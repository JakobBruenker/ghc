{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}

{-# OPTIONS -fno-warn-name-shadowing #-}

-- | Get information on modules, expressions, and identifiers
module GHCi.UI.Info
    ( ModInfo(..)
    , SpanInfo(..)
    , spanInfoFromRealSrcSpan
    , collectInfo
    , findLoc
    , findNameUses
    , findType
    , getModInfo
    ) where

import           Control.Exception
import           Control.Monad
import           Control.Monad.Catch as MC
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Maybe
import           Data.Data
import           Data.Function
import           Data.List (find, sortBy)
import           Data.Map.Strict   (Map)
import qualified Data.Map.Strict   as M
import           Data.Maybe
import           Data.Time
import           Prelude           hiding (mod,(<>))
import           System.Directory

import qualified GHC.Core.Utils
import           GHC.HsToCore
import           GHC.Driver.Session (HasDynFlags(..))
import           GHC.Data.FastString
import           GHC
import           GHC.Driver.Monad
import           GHC.Driver.Env
import           GHC.Driver.Ppr
import           GHC.Types.Name
import           GHC.Types.Name.Set
import           GHC.Utils.Outputable
import           GHC.Types.SrcLoc
import           GHC.Tc.Utils.Zonk
import           GHC.Types.Var

-- | Info about a module. This information is generated every time a
-- module is loaded.
data ModInfo = ModInfo
    { modinfoSummary    :: !ModSummary
      -- ^ Summary generated by GHC. Can be used to access more
      -- information about the module.
    , modinfoSpans      :: [SpanInfo]
      -- ^ Generated set of information about all spans in the
      -- module that correspond to some kind of identifier for
      -- which there will be type info and/or location info.
    , modinfoInfo       :: !ModuleInfo
      -- ^ Again, useful from GHC for accessing information
      -- (exports, instances, scope) from a module.
    , modinfoLastUpdate :: !UTCTime
      -- ^ The timestamp of the file used to generate this record.
    }

-- | Type of some span of source code. Most of these fields are
-- unboxed but Haddock doesn't show that.
data SpanInfo = SpanInfo
    { spaninfoSrcSpan   :: {-# UNPACK #-} !RealSrcSpan
      -- ^ The span we associate information with
    , spaninfoType      :: !(Maybe Type)
      -- ^ The 'Type' associated with the span
    , spaninfoVar       :: !(Maybe Id)
      -- ^ The actual 'Var' associated with the span, if
      -- any. This can be useful for accessing a variety of
      -- information about the identifier such as module,
      -- locality, definition location, etc.
    }

instance Outputable SpanInfo where
  ppr (SpanInfo s t i) = ppr s <+> ppr t <+> ppr i

-- | Test whether second span is contained in (or equal to) first span.
-- This is basically 'containsSpan' for 'SpanInfo'
containsSpanInfo :: SpanInfo -> SpanInfo -> Bool
containsSpanInfo = containsSpan `on` spaninfoSrcSpan

-- | Filter all 'SpanInfo' which are contained in 'SpanInfo'
spaninfosWithin :: [SpanInfo] -> SpanInfo -> [SpanInfo]
spaninfosWithin spans' si = filter (si `containsSpanInfo`) spans'

-- | Construct a 'SpanInfo' from a 'RealSrcSpan' and optionally a
-- 'Type' and an 'Id' (for 'spaninfoType' and 'spaninfoVar'
-- respectively)
spanInfoFromRealSrcSpan :: RealSrcSpan -> Maybe Type -> Maybe Id -> SpanInfo
spanInfoFromRealSrcSpan spn mty mvar =
    SpanInfo spn mty mvar

-- | Convenience wrapper around 'spanInfoFromRealSrcSpan' which needs
-- only a 'RealSrcSpan'
spanInfoFromRealSrcSpan' :: RealSrcSpan -> SpanInfo
spanInfoFromRealSrcSpan' s = spanInfoFromRealSrcSpan s Nothing Nothing

-- | Convenience wrapper around 'srcSpanFile' which results in a 'FilePath'
srcSpanFilePath :: RealSrcSpan -> FilePath
srcSpanFilePath = unpackFS . srcSpanFile

-- | Try to find the location of the given identifier at the given
-- position in the module.
findLoc :: GhcMonad m
        => Map ModuleName ModInfo
        -> RealSrcSpan
        -> String
        -> ExceptT SDoc m (ModInfo,Name,SrcSpan)
findLoc infos span0 string = do
    name  <- maybeToExceptT "Couldn't guess that module name. Does it exist?" $
             guessModule infos (srcSpanFilePath span0)

    info  <- maybeToExceptT "No module info for current file! Try loading it?" $
             MaybeT $ pure $ M.lookup name infos

    name' <- findName infos span0 info string

    case getSrcSpan name' of
        UnhelpfulSpan{} -> do
            throwE ("Found a name, but no location information." <+>
                    "The module is:" <+>
                    maybe "<unknown>" (ppr . moduleName)
                          (nameModule_maybe name'))

        span' -> return (info,name',span')

-- | Find any uses of the given identifier in the codebase.
findNameUses :: (GhcMonad m)
             => Map ModuleName ModInfo
             -> RealSrcSpan
             -> String
             -> ExceptT SDoc m [SrcSpan]
findNameUses infos span0 string =
    locToSpans <$> findLoc infos span0 string
  where
    locToSpans (modinfo,name',span') =
        stripSurrounding (span' : map toSrcSpan spans)
      where
        toSrcSpan s = RealSrcSpan (spaninfoSrcSpan s) Nothing
        spans = filter ((== Just name') . fmap getName . spaninfoVar)
                       (modinfoSpans modinfo)

-- | Filter out redundant spans which surround/contain other spans.
stripSurrounding :: [SrcSpan] -> [SrcSpan]
stripSurrounding xs = filter (not . isRedundant) xs
  where
    isRedundant x = any (x `strictlyContains`) xs

    (RealSrcSpan s1 _) `strictlyContains` (RealSrcSpan s2 _)
         = s1 /= s2 && s1 `containsSpan` s2
    _                `strictlyContains` _ = False

-- | Try to resolve the name located at the given position, or
-- otherwise resolve based on the current module's scope.
findName :: GhcMonad m
         => Map ModuleName ModInfo
         -> RealSrcSpan
         -> ModInfo
         -> String
         -> ExceptT SDoc m Name
findName infos span0 mi string =
    case resolveName (modinfoSpans mi) (spanInfoFromRealSrcSpan' span0) of
      Nothing -> tryExternalModuleResolution
      Just name ->
        case getSrcSpan name of
          UnhelpfulSpan {} -> tryExternalModuleResolution
          RealSrcSpan   {} -> return (getName name)
  where
    tryExternalModuleResolution =
      case find (matchName $ mkFastString string)
                (fromMaybe [] (modInfoTopLevelScope (modinfoInfo mi))) of
        Nothing -> throwE "Couldn't resolve to any modules."
        Just imported -> resolveNameFromModule infos imported

    matchName :: FastString -> Name -> Bool
    matchName str name =
      str ==
      occNameFS (getOccName name)

-- | Try to resolve the name from another (loaded) module's exports.
resolveNameFromModule :: GhcMonad m
                      => Map ModuleName ModInfo
                      -> Name
                      -> ExceptT SDoc m Name
resolveNameFromModule infos name = do
     modL <- maybe (throwE $ "No module for" <+> ppr name) return $
             nameModule_maybe name

     info <- maybe (throwE (ppr (moduleUnit modL) <> ":" <>
                            ppr modL)) return $
             M.lookup (moduleName modL) infos

     maybe (throwE "No matching export in any local modules.") return $
         find (matchName name) (modInfoExports (modinfoInfo info))
  where
    matchName :: Name -> Name -> Bool
    matchName x y = occNameFS (getOccName x) ==
                    occNameFS (getOccName y)

-- | Try to resolve the type display from the given span.
resolveName :: [SpanInfo] -> SpanInfo -> Maybe Var
resolveName spans' si = listToMaybe $ mapMaybe spaninfoVar $
                        reverse spans' `spaninfosWithin` si

-- | Try to find the type of the given span.
findType :: GhcMonad m
         => Map ModuleName ModInfo
         -> RealSrcSpan
         -> String
         -> ExceptT SDoc m (ModInfo, Type)
findType infos span0 string = do
    name  <- maybeToExceptT "Couldn't guess that module name. Does it exist?" $
             guessModule infos (srcSpanFilePath span0)

    info  <- maybeToExceptT "No module info for current file! Try loading it?" $
             MaybeT $ pure $ M.lookup name infos

    case resolveType (modinfoSpans info) (spanInfoFromRealSrcSpan' span0) of
        Nothing -> (,) info <$> lift (exprType TM_Inst string)
        Just ty -> return (info, ty)
  where
    -- | Try to resolve the type display from the given span.
    resolveType :: [SpanInfo] -> SpanInfo -> Maybe Type
    resolveType spans' si = listToMaybe $ mapMaybe spaninfoType $
                            reverse spans' `spaninfosWithin` si

-- | Guess a module name from a file path.
guessModule :: GhcMonad m
            => Map ModuleName ModInfo -> FilePath -> MaybeT m ModuleName
guessModule infos fp = do
    target <- lift $ guessTarget fp Nothing Nothing
    case targetId target of
        TargetModule mn  -> return mn
        TargetFile fp' _ -> guessModule' fp'
  where
    guessModule' :: GhcMonad m => FilePath -> MaybeT m ModuleName
    guessModule' fp' = case findModByFp fp' of
        Just mn -> return mn
        Nothing -> do
            fp'' <- liftIO (makeRelativeToCurrentDirectory fp')

            target' <- lift $ guessTarget fp'' Nothing Nothing
            case targetId target' of
                TargetModule mn -> return mn
                _               -> MaybeT . pure $ findModByFp fp''

    findModByFp :: FilePath -> Maybe ModuleName
    findModByFp fp' = fst <$> find ((Just fp' ==) . mifp) (M.toList infos)
      where
        mifp :: (ModuleName, ModInfo) -> Maybe FilePath
        mifp = ml_hs_file . ms_location . modinfoSummary . snd


-- | Collect type info data for the loaded modules.
collectInfo :: (GhcMonad m) => Map ModuleName ModInfo -> [ModuleName]
               -> m (Map ModuleName ModInfo)
collectInfo ms loaded = do
    df <- getDynFlags
    unit_state <- hsc_units <$> getSession
    liftIO (filterM cacheInvalid loaded) >>= \case
        [] -> return ms
        invalidated -> do
            liftIO (putStrLn ("Collecting type info for " ++
                              show (length invalidated) ++
                              " module(s) ... "))

            foldM (go df unit_state) ms invalidated
  where
    go df unit_state m name = do { info <- getModInfo name; return (M.insert name info m) }
                   `MC.catch`
                   (\(e :: SomeException) -> do
                         liftIO $ putStrLn
                                $ showSDocForUser df unit_state alwaysQualify
                                $ "Error while getting type info from" <+>
                                  ppr name <> ":" <+> text (show e)
                         return m)

    cacheInvalid name = case M.lookup name ms of
        Nothing -> return True
        Just mi -> do
            let fp = srcFilePath (modinfoSummary mi)
                last' = modinfoLastUpdate mi
            current <- getModificationTime fp
            exists <- doesFileExist fp
            if exists
                then return $ current /= last'
                else return True

-- | Get the source file path from a ModSummary.
-- If the .hs file is missing, and the .o file exists,
-- we return the .o file path.
srcFilePath :: ModSummary -> FilePath
srcFilePath modSum = fromMaybe obj_fp src_fp
    where
        src_fp = ml_hs_file ms_loc
        obj_fp = ml_obj_file ms_loc
        ms_loc = ms_location modSum

-- | Get info about the module: summary, types, etc.
getModInfo :: (GhcMonad m) => ModuleName -> m ModInfo
getModInfo name = do
    m <- getModSummary name
    p <- parseModule m
    typechecked <- typecheckModule p
    allTypes <- processAllTypeCheckedModule typechecked
    let i = tm_checked_module_info typechecked
    ts <- liftIO $ getModificationTime $ srcFilePath m
    return (ModInfo m allTypes i ts)

-- | Get ALL source spans in the module.
processAllTypeCheckedModule :: forall m . GhcMonad m => TypecheckedModule
                            -> m [SpanInfo]
processAllTypeCheckedModule tcm = do
    bts <- mapM (getTypeLHsBind ) $ listifyAllSpans tcs
    ets <- mapM (getTypeLHsExpr ) $ listifyAllSpans tcs
    pts <- mapM (getTypeLPat    ) $ listifyAllSpans tcs
    return $ mapMaybe toSpanInfo
           $ sortBy cmpSpan
           $ catMaybes (bts ++ ets ++ pts)
  where
    tcs = tm_typechecked_source tcm

    -- | Extract 'Id', 'SrcSpan', and 'Type' for 'LHsBind's
    getTypeLHsBind :: LHsBind GhcTc -> m (Maybe (Maybe Id,SrcSpan,Type))
    getTypeLHsBind (L _spn FunBind{fun_id = pid,fun_matches = MG _ _ _})
        = pure $ Just (Just (unLoc pid), getLocA pid,varType (unLoc pid))
    getTypeLHsBind _ = pure Nothing

    -- | Extract 'Id', 'SrcSpan', and 'Type' for 'LHsExpr's
    getTypeLHsExpr :: LHsExpr GhcTc -> m (Maybe (Maybe Id,SrcSpan,Type))
    getTypeLHsExpr e = do
        hs_env  <- getSession
        (_,mbe) <- liftIO $ deSugarExpr hs_env e
        return $ fmap (\expr -> (mid, getLocA e, GHC.Core.Utils.exprType expr)) mbe
      where
        mid :: Maybe Id
        mid | HsVar _ (L _ i) <- unwrapVar (unLoc e) = Just i
            | otherwise                              = Nothing

        unwrapVar (XExpr (WrapExpr (HsWrap _ var))) = var
        unwrapVar e'                                = e'

    -- | Extract 'Id', 'SrcSpan', and 'Type' for 'LPats's
    getTypeLPat :: LPat GhcTc -> m (Maybe (Maybe Id,SrcSpan,Type))
    getTypeLPat (L spn pat) =
        pure (Just (getMaybeId pat,locA spn,hsPatType pat))
      where
        getMaybeId :: Pat GhcTc -> Maybe Id
        getMaybeId (VarPat _ (L _ vid)) = Just vid
        getMaybeId _                        = Nothing

    -- | Get ALL source spans in the source.
    listifyAllSpans :: Typeable a => TypecheckedSource -> [LocatedA a]
    listifyAllSpans = everythingAllSpans (++) [] ([] `mkQ` (\x -> [x | p x]))
      where
        p (L spn _) = isGoodSrcSpan (locA spn)

    -- | Variant of @syb@'s @everything@ (which summarises all nodes
    -- in top-down, left-to-right order) with a stop-condition on 'NameSet's
    everythingAllSpans :: (r -> r -> r) -> r -> GenericQ r -> GenericQ r
    everythingAllSpans k z f x
      | (False `mkQ` (const True :: NameSet -> Bool)) x = z
      | otherwise = foldl k (f x) (gmapQ (everythingAllSpans k z f) x)

    cmpSpan (_,a,_) (_,b,_)
      | a `isSubspanOf` b = LT
      | b `isSubspanOf` a = GT
      | otherwise         = EQ

    -- | Pretty print the types into a 'SpanInfo'.
    toSpanInfo :: (Maybe Id,SrcSpan,Type) -> Maybe SpanInfo
    toSpanInfo (n,RealSrcSpan spn _,typ)
        = Just $ spanInfoFromRealSrcSpan spn (Just typ) n
    toSpanInfo _ = Nothing

-- helper stolen from @syb@ package
type GenericQ r = forall a. Data a => a -> r

mkQ :: (Typeable a, Typeable b) => r -> (b -> r) -> a -> r
(r `mkQ` br) a = maybe r br (cast a)
