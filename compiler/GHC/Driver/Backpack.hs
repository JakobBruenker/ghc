
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE OverloadedStrings #-}


-- | This is the driver for the 'ghc --backpack' mode, which
-- is a reimplementation of the "package manager" bits of
-- Backpack directly in GHC.  The basic method of operation
-- is to compile packages and then directly insert them into
-- GHC's in memory database.
--
-- The compilation products of this mode aren't really suitable
-- for Cabal, because GHC makes up component IDs for the things
-- it builds and doesn't serialize out the database contents.
-- But it's still handy for constructing tests.

module GHC.Driver.Backpack (doBackpack) where

import GHC.Prelude

-- In a separate module because it hooks into the parser.
import GHC.Driver.Backpack.Syntax
import GHC.Driver.Config
import GHC.Driver.Monad
import GHC.Driver.Session
import GHC.Driver.Ppr
import GHC.Driver.Main
import GHC.Driver.Make
import GHC.Driver.Env
import GHC.Driver.Errors
import GHC.Driver.Errors.Types

import GHC.Parser
import GHC.Parser.Header
import GHC.Parser.Lexer
import GHC.Parser.Annotation
import GHC.Parser.Errors.Ppr

import GHC hiding (Failed, Succeeded)
import GHC.Tc.Utils.Monad
import GHC.Iface.Recomp
import GHC.Builtin.Names

import GHC.Types.SrcLoc
import GHC.Types.SourceError
import GHC.Types.SourceText
import GHC.Types.SourceFile
import GHC.Types.Unique.FM
import GHC.Types.Unique.DFM
import GHC.Types.Unique.DSet

import GHC.Utils.Outputable
import GHC.Utils.Misc
import GHC.Utils.Panic
import GHC.Utils.Error
import GHC.Utils.Logger

import GHC.Unit
import GHC.Unit.Env
import GHC.Unit.External
import GHC.Unit.State
import GHC.Unit.Finder
import GHC.Unit.Module.Graph
import GHC.Unit.Module.ModSummary
import GHC.Unit.Home.ModInfo

import GHC.Linker.Types

import qualified GHC.LanguageExtensions as LangExt

import GHC.Data.Maybe
import GHC.Data.StringBuffer
import GHC.Data.FastString
import qualified GHC.Data.EnumSet as EnumSet
import qualified GHC.Data.ShortText as ST

import Data.List ( partition )
import System.Exit
import Control.Monad
import System.FilePath
import Data.Version

-- for the unification
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

-- | Entry point to compile a Backpack file.
doBackpack :: [FilePath] -> Ghc ()
doBackpack [src_filename] = do
    logger <- getLogger

    -- Apply options from file to dflags
    dflags0 <- getDynFlags
    let dflags1 = dflags0
    src_opts <- liftIO $ getOptionsFromFile dflags1 src_filename
    (dflags, unhandled_flags, warns) <- liftIO $ parseDynamicFilePragma dflags1 src_opts
    modifySession (\hsc_env -> hsc_env {hsc_dflags = dflags})
    -- Cribbed from: preprocessFile / GHC.Driver.Pipeline
    liftIO $ checkProcessArgsResult unhandled_flags
    liftIO $ handleFlagWarnings logger dflags warns
    -- TODO: Preprocessing not implemented

    buf <- liftIO $ hGetStringBuffer src_filename
    let loc = mkRealSrcLoc (mkFastString src_filename) 1 1 -- TODO: not great
    case unP parseBackpack (initParserState (initParserOpts dflags) buf loc) of
        PFailed pst -> throwErrors (foldPsMessages mkParserErr (getErrorMessages pst))
        POk _ pkgname_bkp -> do
            -- OK, so we have an LHsUnit PackageName, but we want an
            -- LHsUnit HsComponentId.  So let's rename it.
            hsc_env <- getSession
            let bkp = renameHsUnits (hsc_units hsc_env) (bkpPackageNameMap pkgname_bkp) pkgname_bkp
            initBkpM src_filename bkp $
                forM_ (zip [1..] bkp) $ \(i, lunit) -> do
                    let comp_name = unLoc (hsunitName (unLoc lunit))
                    msgTopPackage (i,length bkp) comp_name
                    innerBkpM $ do
                        let (cid, insts) = computeUnitId lunit
                        if null insts
                            then if cid == Indefinite (UnitId (fsLit "main"))
                                    then compileExe lunit
                                    else compileUnit cid []
                            else typecheckUnit cid insts
doBackpack _ =
    throwGhcException (CmdLineError "--backpack can only process a single file")

computeUnitId :: LHsUnit HsComponentId -> (IndefUnitId, [(ModuleName, Module)])
computeUnitId (L _ unit) = (cid, [ (r, mkHoleModule r) | r <- reqs ])
  where
    cid = hsComponentId (unLoc (hsunitName unit))
    reqs = uniqDSetToList (unionManyUniqDSets (map (get_reqs . unLoc) (hsunitBody unit)))
    get_reqs (DeclD HsigFile (L _ modname) _) = unitUniqDSet modname
    get_reqs (DeclD HsSrcFile _ _) = emptyUniqDSet
    get_reqs (DeclD HsBootFile _ _) = emptyUniqDSet
    get_reqs (IncludeD (IncludeDecl (L _ hsuid) _ _)) =
        unitFreeModuleHoles (convertHsComponentId hsuid)

-- | Tiny enum for all types of Backpack operations we may do.
data SessionType
    -- | A compilation operation which will result in a
    -- runnable executable being produced.
    = ExeSession
    -- | A type-checking operation which produces only
    -- interface files, no object files.
    | TcSession
    -- | A compilation operation which produces both
    -- interface files and object files.
    | CompSession
    deriving (Eq)

-- | Create a temporary Session to do some sort of type checking or
-- compilation.
withBkpSession :: IndefUnitId
               -> [(ModuleName, Module)]
               -> [(Unit, ModRenaming)]
               -> SessionType   -- what kind of session are we doing
               -> BkpM a        -- actual action to run
               -> BkpM a
withBkpSession cid insts deps session_type do_this = do
    dflags <- getDynFlags
    let cid_fs = unitFS (indefUnit cid)
        is_primary = False
        uid_str = unpackFS (mkInstantiatedUnitHash cid insts)
        cid_str = unpackFS cid_fs
        -- There are multiple units in a single Backpack file, so we
        -- need to separate out the results in those cases.  Right now,
        -- we follow this hierarchy:
        --      $outputdir/$compid          --> typecheck results
        --      $outputdir/$compid/$unitid  --> compile results
        key_base p | Just f <- p dflags = f
                   | otherwise          = "."
        sub_comp p | is_primary = p
                   | otherwise = p </> cid_str
        outdir p | CompSession <- session_type
                 -- Special case when package is definite
                 , not (null insts) = sub_comp (key_base p) </> uid_str
                 | otherwise = sub_comp (key_base p)

        mk_temp_env hsc_env = hsc_env
            { hsc_dflags   = mk_temp_dflags (hsc_units hsc_env) (hsc_dflags hsc_env)
            }
        mk_temp_dflags unit_state dflags = dflags
            { backend = case session_type of
                            TcSession -> NoBackend
                            _         -> backend dflags
            , homeUnitInstantiations_ = insts
                                     -- if we don't have any instantiation, don't
                                     -- fill `homeUnitInstanceOfId` as it makes no
                                     -- sense (we're not instantiating anything)
            , homeUnitInstanceOf_   = if null insts then Nothing else Just (indefUnit cid)
            , homeUnitId_ = case session_type of
                TcSession -> newUnitId cid Nothing
                -- No hash passed if no instances
                _ | null insts -> newUnitId cid Nothing
                  | otherwise  -> newUnitId cid (Just (mkInstantiatedUnitHash cid insts))


            -- If we're type-checking an indefinite package, we want to
            -- turn on interface writing.  However, if the user also
            -- explicitly passed in `-fno-code`, we DON'T want to write
            -- interfaces unless the user also asked for `-fwrite-interface`.
            -- See Note [-fno-code mode]
            , generalFlags = case session_type of
                -- Make sure to write interfaces when we are type-checking
                -- indefinite packages.
                TcSession
                  | backend dflags /= NoBackend
                  -> EnumSet.insert Opt_WriteInterface (generalFlags dflags)
                _ -> generalFlags dflags

            -- Setup all of the output directories according to our hierarchy
            , objectDir   = Just (outdir objectDir)
            , hiDir       = Just (outdir hiDir)
            , stubDir     = Just (outdir stubDir)
            -- Unset output-file for non exe builds
            , outputFile_ = case session_type of
                ExeSession -> outputFile_ dflags
                _          -> Nothing
            , dynOutputFile_ = case session_type of
                ExeSession -> dynOutputFile_ dflags
                _          -> Nothing
            -- Clear the import path so we don't accidentally grab anything
            , importPaths = []
            -- Synthesize the flags
            , packageFlags = packageFlags dflags ++ map (\(uid0, rn) ->
              let uid = unwireUnit unit_state
                        $ improveUnit unit_state
                        $ renameHoleUnit unit_state (listToUFM insts) uid0
              in ExposePackage
                (showSDoc dflags
                    (text "-unit-id" <+> ppr uid <+> ppr rn))
                (UnitIdArg uid) rn) deps
            }
    withTempSession mk_temp_env $ do
      dflags <- getSessionDynFlags
      -- pprTrace "flags" (ppr insts <> ppr deps) $ return ()
      setSessionDynFlags dflags -- calls initUnits
      do_this

withBkpExeSession :: [(Unit, ModRenaming)] -> BkpM a -> BkpM a
withBkpExeSession deps do_this =
    withBkpSession (Indefinite (UnitId (fsLit "main"))) [] deps ExeSession do_this

getSource :: IndefUnitId -> BkpM (LHsUnit HsComponentId)
getSource cid = do
    bkp_env <- getBkpEnv
    case Map.lookup cid (bkp_table bkp_env) of
        Nothing -> pprPanic "missing needed dependency" (ppr cid)
        Just lunit -> return lunit

typecheckUnit :: IndefUnitId -> [(ModuleName, Module)] -> BkpM ()
typecheckUnit cid insts = do
    lunit <- getSource cid
    buildUnit TcSession cid insts lunit

compileUnit :: IndefUnitId -> [(ModuleName, Module)] -> BkpM ()
compileUnit cid insts = do
    -- Let everyone know we're building this unit
    msgUnitId (mkVirtUnit cid insts)
    lunit <- getSource cid
    buildUnit CompSession cid insts lunit

-- | Compute the dependencies with instantiations of a syntactic
-- HsUnit; e.g., wherever you see @dependency p[A=<A>]@ in a
-- unit file, return the 'Unit' corresponding to @p[A=<A>]@.
-- The @include_sigs@ parameter controls whether or not we also
-- include @dependency signature@ declarations in this calculation.
--
-- Invariant: this NEVER returns UnitId.
hsunitDeps :: Bool {- include sigs -} -> HsUnit HsComponentId -> [(Unit, ModRenaming)]
hsunitDeps include_sigs unit = concatMap get_dep (hsunitBody unit)
  where
    get_dep (L _ (IncludeD (IncludeDecl (L _ hsuid) mb_lrn is_sig)))
        | include_sigs || not is_sig = [(convertHsComponentId hsuid, go mb_lrn)]
        | otherwise = []
      where
        go Nothing = ModRenaming True []
        go (Just lrns) = ModRenaming False (map convRn lrns)
          where
            convRn (L _ (Renaming (L _ from) Nothing))         = (from, from)
            convRn (L _ (Renaming (L _ from) (Just (L _ to)))) = (from, to)
    get_dep _ = []

buildUnit :: SessionType -> IndefUnitId -> [(ModuleName, Module)] -> LHsUnit HsComponentId -> BkpM ()
buildUnit session cid insts lunit = do
    -- NB: include signature dependencies ONLY when typechecking.
    -- If we're compiling, it's not necessary to recursively
    -- compile a signature since it isn't going to produce
    -- any object files.
    let deps_w_rns = hsunitDeps (session == TcSession) (unLoc lunit)
        raw_deps = map fst deps_w_rns
    hsc_env <- getSession
    -- The compilation dependencies are just the appropriately filled
    -- in unit IDs which must be compiled before we can compile.
    let hsubst = listToUFM insts
        deps0 = map (renameHoleUnit (hsc_units hsc_env) hsubst) raw_deps

    -- Build dependencies OR make sure they make sense. BUT NOTE,
    -- we can only check the ones that are fully filled; the rest
    -- we have to defer until we've typechecked our local signature.
    -- TODO: work this into GHC.Driver.Make!!
    forM_ (zip [1..] deps0) $ \(i, dep) ->
        case session of
            TcSession -> return ()
            _ -> compileInclude (length deps0) (i, dep)

    -- IMPROVE IT
    let deps = map (improveUnit (hsc_units hsc_env)) deps0

    mb_old_eps <- case session of
                    TcSession -> fmap Just getEpsGhc
                    _ -> return Nothing

    conf <- withBkpSession cid insts deps_w_rns session $ do

        dflags <- getDynFlags
        mod_graph <- hsunitModuleGraph (unLoc lunit)

        msg <- mkBackpackMsg
        ok <- load' LoadAllTargets (Just msg) mod_graph
        when (failed ok) (liftIO $ exitWith (ExitFailure 1))

        let hi_dir = expectJust (panic "hiDir Backpack") $ hiDir dflags
            export_mod ms = (ms_mod_name ms, ms_mod ms)
            -- Export everything!
            mods = [ export_mod ms | ms <- mgModSummaries mod_graph
                                   , ms_hsc_src ms == HsSrcFile ]

        -- Compile relevant only
        hsc_env <- getSession
        let home_mod_infos = eltsUDFM (hsc_HPT hsc_env)
            linkables = map (expectJust "bkp link" . hm_linkable)
                      . filter ((==HsSrcFile) . mi_hsc_src . hm_iface)
                      $ home_mod_infos
            getOfiles (LM _ _ us) = map nameOfObject (filter isObject us)
            obj_files = concatMap getOfiles linkables
            state     = hsc_units hsc_env

        let compat_fs = unitIdFS (indefUnit cid)
            compat_pn = PackageName compat_fs
            unit_id   = homeUnitId (hsc_home_unit hsc_env)

        return GenericUnitInfo {
            -- Stub data
            unitAbiHash = "",
            unitPackageId = PackageId compat_fs,
            unitPackageName = compat_pn,
            unitPackageVersion = makeVersion [],
            unitId = unit_id,
            unitComponentName = Nothing,
            unitInstanceOf = cid,
            unitInstantiations = insts,
            -- Slight inefficiency here haha
            unitExposedModules = map (\(m,n) -> (m,Just n)) mods,
            unitHiddenModules = [], -- TODO: doc only
            unitDepends = case session of
                        -- Technically, we should state that we depend
                        -- on all the indefinite libraries we used to
                        -- typecheck this.  However, this field isn't
                        -- really used for anything, so we leave it
                        -- blank for now.
                        TcSession -> []
                        _ -> map (toUnitId . unwireUnit state)
                                $ deps ++ [ moduleUnit mod
                                          | (_, mod) <- insts
                                          , not (isHoleModule mod) ],
            unitAbiDepends = [],
            unitLinkerOptions = case session of
                                 TcSession -> []
                                 _ -> map ST.pack $ obj_files,
            unitImportDirs = [ ST.pack $ hi_dir ],
            unitIsExposed = False,
            unitIsIndefinite = case session of
                                 TcSession -> True
                                 _ -> False,
            -- nope
            unitLibraries = [],
            unitExtDepLibsSys = [],
            unitExtDepLibsGhc = [],
            unitLibraryDynDirs = [],
            unitLibraryDirs = [],
            unitExtDepFrameworks = [],
            unitExtDepFrameworkDirs = [],
            unitCcOptions = [],
            unitIncludes = [],
            unitIncludeDirs = [],
            unitHaddockInterfaces = [],
            unitHaddockHTMLs = [],
            unitIsTrusted = False
            }


    addUnit conf
    case mb_old_eps of
        Just old_eps -> updateEpsGhc_ (const old_eps)
        _ -> return ()

compileExe :: LHsUnit HsComponentId -> BkpM ()
compileExe lunit = do
    msgUnitId mainUnit
    let deps_w_rns = hsunitDeps False (unLoc lunit)
        deps = map fst deps_w_rns
        -- no renaming necessary
    forM_ (zip [1..] deps) $ \(i, dep) ->
        compileInclude (length deps) (i, dep)
    withBkpExeSession deps_w_rns $ do
        mod_graph <- hsunitModuleGraph (unLoc lunit)
        msg <- mkBackpackMsg
        ok <- load' LoadAllTargets (Just msg) mod_graph
        when (failed ok) (liftIO $ exitWith (ExitFailure 1))

-- | Register a new virtual unit database containing a single unit
addUnit :: GhcMonad m => UnitInfo -> m ()
addUnit u = do
    hsc_env <- getSession
    logger <- getLogger
    let dflags0 = hsc_dflags hsc_env
    let old_unit_env = hsc_unit_env hsc_env
    newdbs <- case ue_unit_dbs old_unit_env of
        Nothing  -> panic "addUnit: called too early"
        Just dbs ->
         let newdb = UnitDatabase
               { unitDatabasePath  = "(in memory " ++ showSDoc dflags0 (ppr (unitId u)) ++ ")"
               , unitDatabaseUnits = [u]
               }
         in return (dbs ++ [newdb]) -- added at the end because ordering matters
    (dbs,unit_state,home_unit,mconstants) <- liftIO $ initUnits logger dflags0 (Just newdbs)

    -- update platform constants
    dflags <- liftIO $ updatePlatformConstants dflags0 mconstants

    let unit_env = UnitEnv
          { ue_platform  = targetPlatform dflags
          , ue_namever   = ghcNameVersion dflags
          , ue_home_unit = Just home_unit
          , ue_hpt       = ue_hpt old_unit_env
          , ue_eps       = ue_eps old_unit_env
          , ue_units     = unit_state
          , ue_unit_dbs  = Just dbs
          }
    setSession $ hsc_env
        { hsc_dflags   = dflags
        , hsc_unit_env = unit_env
        }

compileInclude :: Int -> (Int, Unit) -> BkpM ()
compileInclude n (i, uid) = do
    hsc_env <- getSession
    let pkgs = hsc_units hsc_env
    msgInclude (i, n) uid
    -- Check if we've compiled it already
    case uid of
      HoleUnit   -> return ()
      RealUnit _ -> return ()
      VirtUnit i -> case lookupUnit pkgs uid of
        Nothing -> innerBkpM $ compileUnit (instUnitInstanceOf i) (instUnitInsts i)
        Just _  -> return ()

-- ----------------------------------------------------------------------------
-- Backpack monad

-- | Backpack monad is a 'GhcMonad' which also maintains a little extra state
-- beyond the 'Session', c.f. 'BkpEnv'.
type BkpM = IOEnv BkpEnv

-- | Backpack environment.  NB: this has a 'Session' and not an 'HscEnv',
-- because we are going to update the 'HscEnv' as we go.
data BkpEnv
    = BkpEnv {
        -- | The session
        bkp_session :: Session,
        -- | The filename of the bkp file we're compiling
        bkp_filename :: FilePath,
        -- | Table of source units which we know how to compile
        bkp_table :: Map IndefUnitId (LHsUnit HsComponentId),
        -- | When a package we are compiling includes another package
        -- which has not been compiled, we bump the level and compile
        -- that.
        bkp_level :: Int
    }

-- Blah, to get rid of the default instance for IOEnv
-- TODO: just make a proper new monad for BkpM, rather than use IOEnv
instance {-# OVERLAPPING #-} HasDynFlags BkpM where
    getDynFlags = fmap hsc_dflags getSession
instance {-# OVERLAPPING #-} HasLogger BkpM where
    getLogger = fmap hsc_logger getSession


instance GhcMonad BkpM where
    getSession = do
        Session s <- fmap bkp_session getEnv
        readMutVar s
    setSession hsc_env = do
        Session s <- fmap bkp_session getEnv
        writeMutVar s hsc_env

-- | Get the current 'BkpEnv'.
getBkpEnv :: BkpM BkpEnv
getBkpEnv = getEnv

-- | Get the nesting level, when recursively compiling modules.
getBkpLevel :: BkpM Int
getBkpLevel = bkp_level `fmap` getBkpEnv

-- | Run a 'BkpM' computation, with the nesting level bumped one.
innerBkpM :: BkpM a -> BkpM a
innerBkpM do_this =
    -- NB: withTempSession mutates, so we don't have to worry
    -- about bkp_session being stale.
    updEnv (\env -> env { bkp_level = bkp_level env + 1 }) do_this

-- | Update the EPS from a 'GhcMonad'. TODO move to appropriate library spot.
updateEpsGhc_ :: GhcMonad m => (ExternalPackageState -> ExternalPackageState) -> m ()
updateEpsGhc_ f = do
    hsc_env <- getSession
    liftIO $ atomicModifyIORef' (euc_eps (ue_eps (hsc_unit_env hsc_env))) (\x -> (f x, ()))

-- | Get the EPS from a 'GhcMonad'.
getEpsGhc :: GhcMonad m => m ExternalPackageState
getEpsGhc = do
    hsc_env <- getSession
    liftIO $ hscEPS hsc_env

-- | Run 'BkpM' in 'Ghc'.
initBkpM :: FilePath -> [LHsUnit HsComponentId] -> BkpM a -> Ghc a
initBkpM file bkp m =
  reifyGhc $ \session -> do
    let env = BkpEnv {
        bkp_session = session,
        bkp_table = Map.fromList [(hsComponentId (unLoc (hsunitName (unLoc u))), u) | u <- bkp],
        bkp_filename = file,
        bkp_level = 0
      }
    runIOEnv env m

-- ----------------------------------------------------------------------------
-- Messaging

-- | Print a compilation progress message, but with indentation according
-- to @level@ (for nested compilation).
backpackProgressMsg :: Int -> Logger -> DynFlags -> SDoc -> IO ()
backpackProgressMsg level logger dflags msg =
    compilationProgressMsg logger dflags $ text (replicate (level * 2) ' ') -- TODO: use GHC.Utils.Ppr.RStr
                                      <> msg

-- | Creates a 'Messager' for Backpack compilation; this is basically
-- a carbon copy of 'batchMsg' but calling 'backpackProgressMsg', which
-- handles indentation.
mkBackpackMsg :: BkpM Messager
mkBackpackMsg = do
    level <- getBkpLevel
    return $ \hsc_env mod_index recomp node ->
      let dflags = hsc_dflags hsc_env
          logger = hsc_logger hsc_env
          state = hsc_units hsc_env
          showMsg msg reason =
            backpackProgressMsg level logger dflags $ pprWithUnitState state $
                showModuleIndex mod_index <>
                msg <> showModMsg dflags (recompileRequired recomp) node
                    <> reason
      in case node of
        InstantiationNode _ ->
          case recomp of
            MustCompile -> showMsg (text "Instantiating ") empty
            UpToDate
              | verbosity (hsc_dflags hsc_env) >= 2 -> showMsg (text "Skipping  ") empty
              | otherwise -> return ()
            RecompBecause reason -> showMsg (text "Instantiating ") (text " [" <> text reason <> text "]")
        ModuleNode _ ->
          case recomp of
            MustCompile -> showMsg (text "Compiling ") empty
            UpToDate
              | verbosity (hsc_dflags hsc_env) >= 2 -> showMsg (text "Skipping  ") empty
              | otherwise -> return ()
            RecompBecause reason -> showMsg (text "Compiling ") (text " [" <> text reason <> text "]")

-- | 'PprStyle' for Backpack messages; here we usually want the module to
-- be qualified (so we can tell how it was instantiated.) But we try not
-- to qualify packages so we can use simple names for them.
backpackStyle :: PprStyle
backpackStyle =
    mkUserStyle
        (QueryQualify neverQualifyNames
                      alwaysQualifyModules
                      neverQualifyPackages) AllTheWay

-- | Message when we initially process a Backpack unit.
msgTopPackage :: (Int,Int) -> HsComponentId -> BkpM ()
msgTopPackage (i,n) (HsComponentId (PackageName fs_pn) _) = do
    dflags <- getDynFlags
    logger <- getLogger
    level <- getBkpLevel
    liftIO . backpackProgressMsg level logger dflags
        $ showModuleIndex (i, n) <> text "Processing " <> ftext fs_pn

-- | Message when we instantiate a Backpack unit.
msgUnitId :: Unit -> BkpM ()
msgUnitId pk = do
    dflags <- getDynFlags
    logger <- getLogger
    hsc_env <- getSession
    level <- getBkpLevel
    let state = hsc_units hsc_env
    liftIO . backpackProgressMsg level logger dflags
        $ pprWithUnitState state
        $ text "Instantiating "
           <> withPprStyle backpackStyle (ppr pk)

-- | Message when we include a Backpack unit.
msgInclude :: (Int,Int) -> Unit -> BkpM ()
msgInclude (i,n) uid = do
    dflags <- getDynFlags
    logger <- getLogger
    hsc_env <- getSession
    level <- getBkpLevel
    let state = hsc_units hsc_env
    liftIO . backpackProgressMsg level logger dflags
        $ pprWithUnitState state
        $ showModuleIndex (i, n) <> text "Including "
            <> withPprStyle backpackStyle (ppr uid)

-- ----------------------------------------------------------------------------
-- Conversion from PackageName to HsComponentId

type PackageNameMap a = UniqFM PackageName a

-- For now, something really simple, since we're not actually going
-- to use this for anything
unitDefines :: LHsUnit PackageName -> (PackageName, HsComponentId)
unitDefines (L _ HsUnit{ hsunitName = L _ pn@(PackageName fs) })
    = (pn, HsComponentId pn (Indefinite (UnitId fs)))

bkpPackageNameMap :: [LHsUnit PackageName] -> PackageNameMap HsComponentId
bkpPackageNameMap units = listToUFM (map unitDefines units)

renameHsUnits :: UnitState -> PackageNameMap HsComponentId -> [LHsUnit PackageName] -> [LHsUnit HsComponentId]
renameHsUnits pkgstate m units = map (fmap renameHsUnit) units
  where

    renamePackageName :: PackageName -> HsComponentId
    renamePackageName pn =
        case lookupUFM m pn of
            Nothing ->
                case lookupPackageName pkgstate pn of
                    Nothing -> error "no package name"
                    Just cid -> HsComponentId pn cid
            Just hscid -> hscid

    renameHsUnit :: HsUnit PackageName -> HsUnit HsComponentId
    renameHsUnit u =
        HsUnit {
            hsunitName = fmap renamePackageName (hsunitName u),
            hsunitBody = map (fmap renameHsUnitDecl) (hsunitBody u)
        }

    renameHsUnitDecl :: HsUnitDecl PackageName -> HsUnitDecl HsComponentId
    renameHsUnitDecl (DeclD a b c) = DeclD a b c
    renameHsUnitDecl (IncludeD idecl) =
        IncludeD IncludeDecl {
            idUnitId = fmap renameHsUnitId (idUnitId idecl),
            idModRenaming = idModRenaming idecl,
            idSignatureInclude = idSignatureInclude idecl
        }

    renameHsUnitId :: HsUnitId PackageName -> HsUnitId HsComponentId
    renameHsUnitId (HsUnitId ln subst)
        = HsUnitId (fmap renamePackageName ln) (map (fmap renameHsModuleSubst) subst)

    renameHsModuleSubst :: HsModuleSubst PackageName -> HsModuleSubst HsComponentId
    renameHsModuleSubst (lk, lm)
        = (lk, fmap renameHsModuleId lm)

    renameHsModuleId :: HsModuleId PackageName -> HsModuleId HsComponentId
    renameHsModuleId (HsModuleVar lm) = HsModuleVar lm
    renameHsModuleId (HsModuleId luid lm) = HsModuleId (fmap renameHsUnitId luid) lm

convertHsComponentId :: HsUnitId HsComponentId -> Unit
convertHsComponentId (HsUnitId (L _ hscid) subst)
    = mkVirtUnit (hsComponentId hscid) (map (convertHsModuleSubst . unLoc) subst)

convertHsModuleSubst :: HsModuleSubst HsComponentId -> (ModuleName, Module)
convertHsModuleSubst (L _ modname, L _ m) = (modname, convertHsModuleId m)

convertHsModuleId :: HsModuleId HsComponentId -> Module
convertHsModuleId (HsModuleVar (L _ modname)) = mkHoleModule modname
convertHsModuleId (HsModuleId (L _ hsuid) (L _ modname)) = mkModule (convertHsComponentId hsuid) modname



{-
************************************************************************
*                                                                      *
                        Module graph construction
*                                                                      *
************************************************************************
-}

-- | This is our version of GHC.Driver.Make.downsweep, but with a few modifications:
--
--  1. Every module is required to be mentioned, so we don't do any funny
--     business with targets or recursively grabbing dependencies.  (We
--     could support this in principle).
--  2. We support inline modules, whose summary we have to synthesize ourself.
--
-- We don't bother trying to support GHC.Driver.Make for now, it's more trouble
-- than it's worth for inline modules.
hsunitModuleGraph :: HsUnit HsComponentId -> BkpM ModuleGraph
hsunitModuleGraph unit = do
    hsc_env <- getSession

    let decls = hsunitBody unit
        pn = hsPackageName (unLoc (hsunitName unit))
        home_unit = hsc_home_unit hsc_env

    --  1. Create a HsSrcFile/HsigFile summary for every
    --  explicitly mentioned module/signature.
    let get_decl (L _ (DeclD hsc_src lmodname mb_hsmod)) =
          Just `fmap` summariseDecl pn hsc_src lmodname mb_hsmod
        get_decl _ = return Nothing
    nodes <- catMaybes `fmap` mapM get_decl decls

    --  2. For each hole which does not already have an hsig file,
    --  create an "empty" hsig file to induce compilation for the
    --  requirement.
    let hsig_set = Set.fromList
          [ ms_mod_name ms
          | ExtendedModSummary { emsModSummary = ms } <- nodes
          , ms_hsc_src ms == HsigFile
          ]
    req_nodes <- fmap catMaybes . forM (homeUnitInstantiations home_unit) $ \(mod_name, _) ->
        if Set.member mod_name hsig_set
            then return Nothing
            else fmap (Just . extendModSummaryNoDeps) $ summariseRequirement pn mod_name
            -- Using extendModSummaryNoDeps here is okay because we're making a leaf node
            -- representing a signature that can't depend on any other unit.

    -- 3. Return the kaboodle
    return $ mkModuleGraph' $
      (ModuleNode <$> (nodes ++ req_nodes)) ++ instantiationNodes (hsc_units hsc_env)

summariseRequirement :: PackageName -> ModuleName -> BkpM ModSummary
summariseRequirement pn mod_name = do
    hsc_env <- getSession
    let dflags = hsc_dflags hsc_env
    let home_unit = hsc_home_unit hsc_env

    let PackageName pn_fs = pn
    location <- liftIO $ mkHomeModLocation2 dflags mod_name
                 (unpackFS pn_fs </> moduleNameSlashes mod_name) "hsig"

    env <- getBkpEnv
    time <- liftIO $ getModificationUTCTime (bkp_filename env)
    hi_timestamp <- liftIO $ modificationTimeIfExists (ml_hi_file location)
    hie_timestamp <- liftIO $ modificationTimeIfExists (ml_hie_file location)
    let loc = srcLocSpan (mkSrcLoc (mkFastString (bkp_filename env)) 1 1)

    let fc = hsc_FC hsc_env
    mod <- liftIO $ addHomeModuleToFinder fc home_unit mod_name location

    extra_sig_imports <- liftIO $ findExtraSigImports hsc_env HsigFile mod_name

    return ModSummary {
        ms_mod = mod,
        ms_hsc_src = HsigFile,
        ms_location = location,
        ms_hs_date = time,
        ms_obj_date = Nothing,
        ms_iface_date = hi_timestamp,
        ms_hie_date = hie_timestamp,
        ms_srcimps = [],
        ms_textual_imps = extra_sig_imports,
        ms_parsed_mod = Just (HsParsedModule {
                hpm_module = L loc (HsModule {
                        hsmodAnn = noAnn,
                        hsmodLayout = NoLayoutInfo,
                        hsmodName = Just (L loc mod_name),
                        hsmodExports = Nothing,
                        hsmodImports = [],
                        hsmodDecls = [],
                        hsmodDeprecMessage = Nothing,
                        hsmodHaddockModHeader = Nothing
                    }),
                hpm_src_files = []
            }),
        ms_hspp_file = "", -- none, it came inline
        ms_hspp_opts = dflags,
        ms_hspp_buf = Nothing
        }

summariseDecl :: PackageName
              -> HscSource
              -> Located ModuleName
              -> Maybe (Located HsModule)
              -> BkpM ExtendedModSummary
summariseDecl pn hsc_src (L _ modname) (Just hsmod) = hsModuleToModSummary pn hsc_src modname hsmod
summariseDecl _pn hsc_src lmodname@(L loc modname) Nothing
    = do hsc_env <- getSession
         -- TODO: this looks for modules in the wrong place
         r <- liftIO $ summariseModule hsc_env
                         emptyModNodeMap -- GHC API recomp not supported
                         (hscSourceToIsBoot hsc_src)
                         lmodname
                         True -- Target lets you disallow, but not here
                         Nothing -- GHC API buffer support not supported
                         [] -- No exclusions
         case r of
            Nothing -> throwOneError $ fmap GhcDriverMessage
                                     $ mkPlainErrorMsgEnvelope loc (DriverBackpackModuleNotFound modname)
            Just (Left err) -> throwErrors (fmap GhcDriverMessage err)
            Just (Right summary) -> return summary

-- | Up until now, GHC has assumed a single compilation target per source file.
-- Backpack files with inline modules break this model, since a single file
-- may generate multiple output files.  How do we decide to name these files?
-- Should there only be one output file? This function our current heuristic,
-- which is we make a "fake" module and use that.
hsModuleToModSummary :: PackageName
                     -> HscSource
                     -> ModuleName
                     -> Located HsModule
                     -> BkpM ExtendedModSummary
hsModuleToModSummary pn hsc_src modname
                     hsmod = do
    let imps = hsmodImports (unLoc hsmod)
        loc  = getLoc hsmod
    hsc_env <- getSession
    -- Sort of the same deal as in GHC.Driver.Pipeline's getLocation
    -- Use the PACKAGE NAME to find the location
    let PackageName unit_fs = pn
        dflags = hsc_dflags hsc_env
    -- Unfortunately, we have to define a "fake" location in
    -- order to appease the various code which uses the file
    -- name to figure out where to put, e.g. object files.
    -- To add insult to injury, we don't even actually use
    -- these filenames to figure out where the hi files go.
    -- A travesty!
    location0 <- liftIO $ mkHomeModLocation2 dflags modname
                             (unpackFS unit_fs </>
                              moduleNameSlashes modname)
                              (case hsc_src of
                                HsigFile -> "hsig"
                                HsBootFile -> "hs-boot"
                                HsSrcFile -> "hs")
    -- DANGEROUS: bootifying can POISON the module finder cache
    let location = case hsc_src of
                        HsBootFile -> addBootSuffixLocnOut location0
                        _ -> location0
    -- This duplicates a pile of logic in GHC.Driver.Make
    env <- getBkpEnv
    time <- liftIO $ getModificationUTCTime (bkp_filename env)
    hi_timestamp <- liftIO $ modificationTimeIfExists (ml_hi_file location)
    hie_timestamp <- liftIO $ modificationTimeIfExists (ml_hie_file location)

    -- Also copied from 'getImports'
    let (src_idecls, ord_idecls) = partition ((== IsBoot) . ideclSource . unLoc) imps

             -- GHC.Prim doesn't exist physically, so don't go looking for it.
        ordinary_imps = filter ((/= moduleName gHC_PRIM) . unLoc . ideclName . unLoc)
                               ord_idecls

        implicit_prelude = xopt LangExt.ImplicitPrelude dflags
        implicit_imports = mkPrelImports modname loc
                                         implicit_prelude imps
        convImport (L _ i) = (fmap sl_fs (ideclPkgQual i), ideclName i)

    extra_sig_imports <- liftIO $ findExtraSigImports hsc_env hsc_src modname

    let normal_imports = map convImport (implicit_imports ++ ordinary_imps)
    (implicit_sigs, inst_deps) <- liftIO $ implicitRequirementsShallow hsc_env normal_imports

    -- So that Finder can find it, even though it doesn't exist...
    this_mod <- liftIO $ do
      let home_unit = hsc_home_unit hsc_env
      let fc        = hsc_FC hsc_env
      addHomeModuleToFinder fc home_unit modname location
    return $ ExtendedModSummary
      { emsModSummary =
          ModSummary {
            ms_mod = this_mod,
            ms_hsc_src = hsc_src,
            ms_location = location,
            ms_hspp_file = (case hiDir dflags of
                            Nothing -> ""
                            Just d -> d) </> ".." </> moduleNameSlashes modname <.> "hi",
            ms_hspp_opts = dflags,
            ms_hspp_buf = Nothing,
            ms_srcimps = map convImport src_idecls,
            ms_textual_imps = normal_imports
                           -- We have to do something special here:
                           -- due to merging, requirements may end up with
                           -- extra imports
                           ++ extra_sig_imports
                           ++ ((,) Nothing . noLoc <$> implicit_sigs),
            -- This is our hack to get the parse tree to the right spot
            ms_parsed_mod = Just (HsParsedModule {
                    hpm_module = hsmod,
                    hpm_src_files = [] -- TODO if we preprocessed it
                }),
            ms_hs_date = time,
            ms_obj_date = Nothing, -- TODO do this, but problem: hi_timestamp is BOGUS
            ms_iface_date = hi_timestamp,
            ms_hie_date = hie_timestamp
          }
      , emsInstantiatedUnits = inst_deps
      }

-- | Create a new, externally provided hashed unit id from
-- a hash.
newUnitId :: IndefUnitId -> Maybe FastString -> UnitId
newUnitId uid mhash = case mhash of
   Nothing   -> indefUnit uid
   Just hash -> UnitId (unitIdFS (indefUnit uid) `appendFS` mkFastString "+" `appendFS` hash)
