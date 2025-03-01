{-
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998

\section[SimplCore]{Driver for simplifying @Core@ programs}
-}

{-# LANGUAGE CPP #-}

module GHC.Core.Opt.Pipeline ( core2core, simplifyExpr ) where

import GHC.Prelude

import GHC.Driver.Session
import GHC.Driver.Ppr
import GHC.Driver.Plugins ( withPlugins, installCoreToDos )
import GHC.Driver.Env
import GHC.Platform.Ways  ( hasWay, Way(WayProf) )

import GHC.Core
import GHC.Core.Opt.CSE  ( cseProgram )
import GHC.Core.Rules   ( mkRuleBase, unionRuleBase,
                          extendRuleBaseList, ruleCheckProgram, addRuleInfo,
                          getRules, initRuleOpts )
import GHC.Core.Ppr     ( pprCoreBindings, pprCoreExpr )
import GHC.Core.Opt.OccurAnal ( occurAnalysePgm, occurAnalyseExpr )
import GHC.Core.Stats   ( coreBindsSize, coreBindsStats, exprSize )
import GHC.Core.Utils   ( mkTicks, stripTicksTop, dumpIdInfoOfProgram )
import GHC.Core.Lint    ( endPass, lintPassResult, dumpPassResult,
                          lintAnnots )
import GHC.Core.Opt.Simplify       ( simplTopBinds, simplExpr, simplRules )
import GHC.Core.Opt.Simplify.Utils ( simplEnvForGHCi, activeRule, activeUnfolding )
import GHC.Core.Opt.Simplify.Env
import GHC.Core.Opt.Simplify.Monad
import GHC.Core.Opt.Monad
import GHC.Core.Opt.FloatIn      ( floatInwards )
import GHC.Core.Opt.FloatOut     ( floatOutwards )
import GHC.Core.Opt.LiberateCase ( liberateCase )
import GHC.Core.Opt.StaticArgs   ( doStaticArgs )
import GHC.Core.Opt.Specialise   ( specProgram)
import GHC.Core.Opt.SpecConstr   ( specConstrProgram)
import GHC.Core.Opt.DmdAnal
import GHC.Core.Opt.CprAnal      ( cprAnalProgram )
import GHC.Core.Opt.CallArity    ( callArityAnalProgram )
import GHC.Core.Opt.Exitify      ( exitifyProgram )
import GHC.Core.Opt.WorkWrap     ( wwTopBinds )
import GHC.Core.Opt.CallerCC     ( addCallerCostCentres )
import GHC.Core.Seq (seqBinds)
import GHC.Core.FamInstEnv

import qualified GHC.Utils.Error as Err
import GHC.Utils.Error  ( withTiming )
import GHC.Utils.Logger as Logger
import GHC.Utils.Outputable
import GHC.Utils.Panic
import GHC.Utils.Constants (debugIsOn)

import GHC.Unit.External
import GHC.Unit.Module.Env
import GHC.Unit.Module.ModGuts
import GHC.Unit.Module.Deps

import GHC.Runtime.Context

import GHC.Types.SrcLoc
import GHC.Types.Id
import GHC.Types.Id.Info
import GHC.Types.Basic
import GHC.Types.Demand ( zapDmdEnvSig )
import GHC.Types.Var.Set
import GHC.Types.Var.Env
import GHC.Types.Tickish
import GHC.Types.Unique.Supply ( UniqSupply )
import GHC.Types.Unique.FM
import GHC.Types.Name.Ppr

import Control.Monad
import qualified GHC.LanguageExtensions as LangExt
{-
************************************************************************
*                                                                      *
\subsection{The driver for the simplifier}
*                                                                      *
************************************************************************
-}

core2core :: HscEnv -> ModGuts -> IO ModGuts
core2core hsc_env guts@(ModGuts { mg_module  = mod
                                , mg_loc     = loc
                                , mg_deps    = deps
                                , mg_rdr_env = rdr_env })
  = do { let builtin_passes = getCoreToDo logger dflags
             orph_mods = mkModuleSet (mod : dep_orphs deps)
             uniq_mask = 's'
       ;
       ; (guts2, stats) <- runCoreM hsc_env hpt_rule_base uniq_mask mod
                                    orph_mods print_unqual loc $
                           do { hsc_env' <- getHscEnv
                              ; all_passes <- withPlugins hsc_env'
                                                installCoreToDos
                                                builtin_passes
                              ; runCorePasses all_passes guts }

       ; Logger.dumpIfSet_dyn logger dflags Opt_D_dump_simpl_stats
             "Grand total simplifier statistics"
             FormatText
             (pprSimplCount stats)

       ; return guts2 }
  where
    logger         = hsc_logger hsc_env
    dflags         = hsc_dflags hsc_env
    home_pkg_rules = hptRules hsc_env (dep_mods deps)
    hpt_rule_base  = mkRuleBase home_pkg_rules
    print_unqual   = mkPrintUnqualified (hsc_unit_env hsc_env) rdr_env
    -- mod: get the module out of the current HscEnv so we can retrieve it from the monad.
    -- This is very convienent for the users of the monad (e.g. plugins do not have to
    -- consume the ModGuts to find the module) but somewhat ugly because mg_module may
    -- _theoretically_ be changed during the Core pipeline (it's part of ModGuts), which
    -- would mean our cached value would go out of date.

{-
************************************************************************
*                                                                      *
           Generating the main optimisation pipeline
*                                                                      *
************************************************************************
-}

getCoreToDo :: Logger -> DynFlags -> [CoreToDo]
getCoreToDo logger dflags
  = flatten_todos core_todo
  where
    opt_level     = optLevel           dflags
    phases        = simplPhases        dflags
    max_iter      = maxSimplIterations dflags
    rule_check    = ruleCheck          dflags
    call_arity    = gopt Opt_CallArity                    dflags
    exitification = gopt Opt_Exitification                dflags
    strictness    = gopt Opt_Strictness                   dflags
    full_laziness = gopt Opt_FullLaziness                 dflags
    do_specialise = gopt Opt_Specialise                   dflags
    do_float_in   = gopt Opt_FloatIn                      dflags
    cse           = gopt Opt_CSE                          dflags
    spec_constr   = gopt Opt_SpecConstr                   dflags
    liberate_case = gopt Opt_LiberateCase                 dflags
    late_dmd_anal = gopt Opt_LateDmdAnal                  dflags
    late_specialise = gopt Opt_LateSpecialise             dflags
    static_args   = gopt Opt_StaticArgumentTransformation dflags
    rules_on      = gopt Opt_EnableRewriteRules           dflags
    eta_expand_on = gopt Opt_DoLambdaEtaExpansion         dflags
    pre_inline_on = gopt Opt_SimplPreInlining             dflags
    ww_on         = gopt Opt_WorkerWrapper                dflags
    static_ptrs   = xopt LangExt.StaticPointers           dflags
    profiling     = ways dflags `hasWay` WayProf

    maybe_rule_check phase = runMaybe rule_check (CoreDoRuleCheck phase)

    maybe_strictness_before (Phase phase)
      | phase `elem` strictnessBefore dflags = CoreDoDemand
    maybe_strictness_before _
      = CoreDoNothing

    base_mode = SimplMode { sm_phase      = panic "base_mode"
                          , sm_names      = []
                          , sm_dflags     = dflags
                          , sm_logger     = logger
                          , sm_uf_opts    = unfoldingOpts dflags
                          , sm_rules      = rules_on
                          , sm_eta_expand = eta_expand_on
                          , sm_inline     = True
                          , sm_case_case  = True
                          , sm_pre_inline = pre_inline_on
                          }

    simpl_phase phase name iter
      = CoreDoPasses
      $   [ maybe_strictness_before phase
          , CoreDoSimplify iter
                (base_mode { sm_phase = phase
                           , sm_names = [name] })

          , maybe_rule_check phase ]

    -- Run GHC's internal simplification phase, after all rules have run.
    -- See Note [Compiler phases] in GHC.Types.Basic
    simplify name = simpl_phase FinalPhase name max_iter

    -- initial simplify: mk specialiser happy: minimum effort please
    simpl_gently = CoreDoSimplify max_iter
                       (base_mode { sm_phase = InitialPhase
                                  , sm_names = ["Gentle"]
                                  , sm_rules = rules_on   -- Note [RULEs enabled in InitialPhase]
                                  , sm_inline = True
                                              -- See Note [Inline in InitialPhase]
                                  , sm_case_case = False })
                          -- Don't do case-of-case transformations.
                          -- This makes full laziness work better

    dmd_cpr_ww = if ww_on then [CoreDoDemand,CoreDoCpr,CoreDoWorkerWrapper]
                          else [CoreDoDemand,CoreDoCpr]


    demand_analyser = (CoreDoPasses (
                           dmd_cpr_ww ++
                           [simplify "post-worker-wrapper"]
                           ))

    -- Static forms are moved to the top level with the FloatOut pass.
    -- See Note [Grand plan for static forms] in GHC.Iface.Tidy.StaticPtrTable.
    static_ptrs_float_outwards =
      runWhen static_ptrs $ CoreDoPasses
        [ simpl_gently -- Float Out can't handle type lets (sometimes created
                       -- by simpleOptPgm via mkParallelBindings)
        , CoreDoFloatOutwards FloatOutSwitches
          { floatOutLambdas   = Just 0
          , floatOutConstants = True
          , floatOutOverSatApps = False
          , floatToTopLevelOnly = True
          }
        ]

    add_caller_ccs =
        runWhen (profiling && not (null $ callerCcFilters dflags)) CoreAddCallerCcs

    core_todo =
     if opt_level == 0 then
       [ static_ptrs_float_outwards,
         CoreDoSimplify max_iter
             (base_mode { sm_phase = FinalPhase
                        , sm_names = ["Non-opt simplification"] })
       , add_caller_ccs
       ]

     else {- opt_level >= 1 -} [

    -- We want to do the static argument transform before full laziness as it
    -- may expose extra opportunities to float things outwards. However, to fix
    -- up the output of the transformation we need at do at least one simplify
    -- after this before anything else
        runWhen static_args (CoreDoPasses [ simpl_gently, CoreDoStaticArgs ]),

        -- initial simplify: mk specialiser happy: minimum effort please
        simpl_gently,

        -- Specialisation is best done before full laziness
        -- so that overloaded functions have all their dictionary lambdas manifest
        runWhen do_specialise CoreDoSpecialising,

        if full_laziness then
           CoreDoFloatOutwards FloatOutSwitches {
                                 floatOutLambdas   = Just 0,
                                 floatOutConstants = True,
                                 floatOutOverSatApps = False,
                                 floatToTopLevelOnly = False }
                -- Was: gentleFloatOutSwitches
                --
                -- I have no idea why, but not floating constants to
                -- top level is very bad in some cases.
                --
                -- Notably: p_ident in spectral/rewrite
                --          Changing from "gentle" to "constantsOnly"
                --          improved rewrite's allocation by 19%, and
                --          made 0.0% difference to any other nofib
                --          benchmark
                --
                -- Not doing floatOutOverSatApps yet, we'll do
                -- that later on when we've had a chance to get more
                -- accurate arity information.  In fact it makes no
                -- difference at all to performance if we do it here,
                -- but maybe we save some unnecessary to-and-fro in
                -- the simplifier.
        else
           -- Even with full laziness turned off, we still need to float static
           -- forms to the top level. See Note [Grand plan for static forms] in
           -- GHC.Iface.Tidy.StaticPtrTable.
           static_ptrs_float_outwards,

        -- Run the simplier phases 2,1,0 to allow rewrite rules to fire
        CoreDoPasses [ simpl_phase (Phase phase) "main" max_iter
                     | phase <- [phases, phases-1 .. 1] ],
        simpl_phase (Phase 0) "main" (max max_iter 3),
                -- Phase 0: allow all Ids to be inlined now
                -- This gets foldr inlined before strictness analysis

                -- At least 3 iterations because otherwise we land up with
                -- huge dead expressions because of an infelicity in the
                -- simplifier.
                --      let k = BIG in foldr k z xs
                -- ==>  let k = BIG in letrec go = \xs -> ...(k x).... in go xs
                -- ==>  let k = BIG in letrec go = \xs -> ...(BIG x).... in go xs
                -- Don't stop now!

        runWhen do_float_in CoreDoFloatInwards,
            -- Run float-inwards immediately before the strictness analyser
            -- Doing so pushes bindings nearer their use site and hence makes
            -- them more likely to be strict. These bindings might only show
            -- up after the inlining from simplification.  Example in fulsom,
            -- Csg.calc, where an arg of timesDouble thereby becomes strict.

        runWhen call_arity $ CoreDoPasses
            [ CoreDoCallArity
            , simplify "post-call-arity"
            ],

        -- Strictness analysis
        runWhen strictness demand_analyser,

        runWhen exitification CoreDoExitify,
            -- See note [Placement of the exitification pass]

        runWhen full_laziness $
           CoreDoFloatOutwards FloatOutSwitches {
                                 floatOutLambdas     = floatLamArgs dflags,
                                 floatOutConstants   = True,
                                 floatOutOverSatApps = True,
                                 floatToTopLevelOnly = False },
                -- nofib/spectral/hartel/wang doubles in speed if you
                -- do full laziness late in the day.  It only happens
                -- after fusion and other stuff, so the early pass doesn't
                -- catch it.  For the record, the redex is
                --        f_el22 (f_el21 r_midblock)


        runWhen cse CoreCSE,
                -- We want CSE to follow the final full-laziness pass, because it may
                -- succeed in commoning up things floated out by full laziness.
                -- CSE used to rely on the no-shadowing invariant, but it doesn't any more

        runWhen do_float_in CoreDoFloatInwards,

        simplify "final",  -- Final tidy-up

        maybe_rule_check FinalPhase,

        --------  After this we have -O2 passes -----------------
        -- None of them run with -O

                -- Case-liberation for -O2.  This should be after
                -- strictness analysis and the simplification which follows it.
        runWhen liberate_case $ CoreDoPasses
           [ CoreLiberateCase, simplify "post-liberate-case" ],
           -- Run the simplifier after LiberateCase to vastly
           -- reduce the possibility of shadowing
           -- Reason: see Note [Shadowing] in GHC.Core.Opt.SpecConstr

        runWhen spec_constr $ CoreDoPasses
           [ CoreDoSpecConstr, simplify "post-spec-constr"],
           -- See Note [Simplify after SpecConstr]

        maybe_rule_check FinalPhase,

        runWhen late_specialise $ CoreDoPasses
           [ CoreDoSpecialising, simplify "post-late-spec"],

        -- LiberateCase can yield new CSE opportunities because it peels
        -- off one layer of a recursive function (concretely, I saw this
        -- in wheel-sieve1), and I'm guessing that SpecConstr can too
        -- And CSE is a very cheap pass. So it seems worth doing here.
        runWhen ((liberate_case || spec_constr) && cse) $ CoreDoPasses
           [ CoreCSE, simplify "post-final-cse" ],

        ---------  End of -O2 passes --------------

        runWhen late_dmd_anal $ CoreDoPasses (
            dmd_cpr_ww ++ [simplify "post-late-ww"]
          ),

        -- Final run of the demand_analyser, ensures that one-shot thunks are
        -- really really one-shot thunks. Only needed if the demand analyser
        -- has run at all. See Note [Final Demand Analyser run] in GHC.Core.Opt.DmdAnal
        -- It is EXTREMELY IMPORTANT to run this pass, otherwise execution
        -- can become /exponentially/ more expensive. See #11731, #12996.
        runWhen (strictness || late_dmd_anal) CoreDoDemand,

        maybe_rule_check FinalPhase,

        add_caller_ccs
     ]

    -- Remove 'CoreDoNothing' and flatten 'CoreDoPasses' for clarity.
    flatten_todos [] = []
    flatten_todos (CoreDoNothing : rest) = flatten_todos rest
    flatten_todos (CoreDoPasses passes : rest) =
      flatten_todos passes ++ flatten_todos rest
    flatten_todos (todo : rest) = todo : flatten_todos rest

{- Note [Inline in InitialPhase]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
In GHC 8 and earlier we did not inline anything in the InitialPhase. But that is
confusing for users because when they say INLINE they expect the function to inline
right away.

So now we do inlining immediately, even in the InitialPhase, assuming that the
Id's Activation allows it.

This is a surprisingly big deal. Compiler performance improved a lot
when I made this change:

   perf/compiler/T5837.run            T5837 [stat too good] (normal)
   perf/compiler/parsing001.run       parsing001 [stat too good] (normal)
   perf/compiler/T12234.run           T12234 [stat too good] (optasm)
   perf/compiler/T9020.run            T9020 [stat too good] (optasm)
   perf/compiler/T3064.run            T3064 [stat too good] (normal)
   perf/compiler/T9961.run            T9961 [stat too good] (normal)
   perf/compiler/T13056.run           T13056 [stat too good] (optasm)
   perf/compiler/T9872d.run           T9872d [stat too good] (normal)
   perf/compiler/T783.run             T783 [stat too good] (normal)
   perf/compiler/T12227.run           T12227 [stat too good] (normal)
   perf/should_run/lazy-bs-alloc.run  lazy-bs-alloc [stat too good] (normal)
   perf/compiler/T1969.run            T1969 [stat too good] (normal)
   perf/compiler/T9872a.run           T9872a [stat too good] (normal)
   perf/compiler/T9872c.run           T9872c [stat too good] (normal)
   perf/compiler/T9872b.run           T9872b [stat too good] (normal)
   perf/compiler/T9872d.run           T9872d [stat too good] (normal)

Note [RULEs enabled in InitialPhase]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
RULES are enabled when doing "gentle" simplification in InitialPhase,
or with -O0.  Two reasons:

  * We really want the class-op cancellation to happen:
        op (df d1 d2) --> $cop3 d1 d2
    because this breaks the mutual recursion between 'op' and 'df'

  * I wanted the RULE
        lift String ===> ...
    to work in Template Haskell when simplifying
    splices, so we get simpler code for literal strings

But watch out: list fusion can prevent floating.  So use phase control
to switch off those rules until after floating.

Note [Simplify after SpecConstr]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We want to run the simplifier after SpecConstr, and before late-Specialise,
for two reasons, both shown up in test perf/compiler/T16473,
with -O2 -flate-specialise

1.  I found that running late-Specialise after SpecConstr, with no
    simplification in between meant that the carefullly constructed
    SpecConstr rule never got to fire.  (It was something like
          lvl = f a   -- Arity 1
          ....g lvl....
    SpecConstr specialised g for argument lvl; but Specialise then
    specialised lvl = f a to lvl = $sf, and inlined. Or something like
    that.)

2.  Specialise relies on unfoldings being available for top-level dictionary
    bindings; but SpecConstr kills them all!  The Simplifer restores them.

This extra run of the simplifier has a cost, but this is only with -O2.


************************************************************************
*                                                                      *
                  The CoreToDo interpreter
*                                                                      *
************************************************************************
-}

runCorePasses :: [CoreToDo] -> ModGuts -> CoreM ModGuts
runCorePasses passes guts
  = foldM do_pass guts passes
  where
    do_pass guts CoreDoNothing = return guts
    do_pass guts (CoreDoPasses ps) = runCorePasses ps guts
    do_pass guts pass = do
      dflags <- getDynFlags
      logger <- getLogger
      withTiming logger dflags (ppr pass <+> brackets (ppr mod))
                   (const ()) $ do
            guts' <- lintAnnots (ppr pass) (doCorePass pass) guts
            endPass pass (mg_binds guts') (mg_rules guts')
            return guts'

    mod = mg_module guts

doCorePass :: CoreToDo -> ModGuts -> CoreM ModGuts
doCorePass pass guts = do
  logger <- getLogger
  case pass of
    CoreDoSimplify {}         -> {-# SCC "Simplify" #-}
                                 simplifyPgm pass guts

    CoreCSE                   -> {-# SCC "CommonSubExpr" #-}
                                 doPass cseProgram guts

    CoreLiberateCase          -> {-# SCC "LiberateCase" #-}
                                 doPassD liberateCase guts

    CoreDoFloatInwards        -> {-# SCC "FloatInwards" #-}
                                 floatInwards guts

    CoreDoFloatOutwards f     -> {-# SCC "FloatOutwards" #-}
                                 doPassDUM (floatOutwards logger f) guts

    CoreDoStaticArgs          -> {-# SCC "StaticArgs" #-}
                                 doPassU doStaticArgs guts

    CoreDoCallArity           -> {-# SCC "CallArity" #-}
                                 doPassD callArityAnalProgram guts

    CoreDoExitify             -> {-# SCC "Exitify" #-}
                                 doPass exitifyProgram guts

    CoreDoDemand              -> {-# SCC "DmdAnal" #-}
                                 doPassDFRM (dmdAnal logger) guts

    CoreDoCpr                 -> {-# SCC "CprAnal" #-}
                                 doPassDFM (cprAnalProgram logger) guts

    CoreDoWorkerWrapper       -> {-# SCC "WorkWrap" #-}
                                 doPassDFU wwTopBinds guts

    CoreDoSpecialising        -> {-# SCC "Specialise" #-}
                                 specProgram guts

    CoreDoSpecConstr          -> {-# SCC "SpecConstr" #-}
                                 specConstrProgram guts

    CoreAddCallerCcs          -> {-# SCC "AddCallerCcs" #-}
                                 addCallerCostCentres guts

    CoreDoPrintCore           -> observe (printCore logger) guts

    CoreDoRuleCheck phase pat -> ruleCheckPass phase pat guts
    CoreDoNothing             -> return guts
    CoreDoPasses passes       -> runCorePasses passes guts

    CoreDoPluginPass _ p      -> {-# SCC "Plugin" #-} p guts

    CoreDesugar               -> pprPanic "doCorePass" (ppr pass)
    CoreDesugarOpt            -> pprPanic "doCorePass" (ppr pass)
    CoreTidy                  -> pprPanic "doCorePass" (ppr pass)
    CorePrep                  -> pprPanic "doCorePass" (ppr pass)
    CoreOccurAnal             -> pprPanic "doCorePass" (ppr pass)

{-
************************************************************************
*                                                                      *
\subsection{Core pass combinators}
*                                                                      *
************************************************************************
-}

printCore :: Logger -> DynFlags -> CoreProgram -> IO ()
printCore logger dflags binds
    = Logger.dumpIfSet logger dflags True "Print Core" (pprCoreBindings binds)

ruleCheckPass :: CompilerPhase -> String -> ModGuts -> CoreM ModGuts
ruleCheckPass current_phase pat guts = do
    dflags <- getDynFlags
    logger <- getLogger
    withTiming logger dflags (text "RuleCheck"<+>brackets (ppr $ mg_module guts))
                (const ()) $ do
        rb <- getRuleBase
        vis_orphs <- getVisibleOrphanMods
        let rule_fn fn = getRules (RuleEnv rb vis_orphs) fn
                          ++ (mg_rules guts)
        let ropts = initRuleOpts dflags
        liftIO $ putLogMsg logger dflags Err.MCDump noSrcSpan
                     $ withPprStyle defaultDumpStyle
                     (ruleCheckProgram ropts current_phase pat
                        rule_fn (mg_binds guts))
        return guts

doPassDUM :: (DynFlags -> UniqSupply -> CoreProgram -> IO CoreProgram) -> ModGuts -> CoreM ModGuts
doPassDUM do_pass = doPassM $ \binds -> do
    dflags <- getDynFlags
    us     <- getUniqueSupplyM
    liftIO $ do_pass dflags us binds

doPassDM :: (DynFlags -> CoreProgram -> IO CoreProgram) -> ModGuts -> CoreM ModGuts
doPassDM do_pass = doPassDUM (\dflags -> const (do_pass dflags))

doPassD :: (DynFlags -> CoreProgram -> CoreProgram) -> ModGuts -> CoreM ModGuts
doPassD do_pass = doPassDM (\dflags -> return . do_pass dflags)

doPassDU :: (DynFlags -> UniqSupply -> CoreProgram -> CoreProgram) -> ModGuts -> CoreM ModGuts
doPassDU do_pass = doPassDUM (\dflags us -> return . do_pass dflags us)

doPassU :: (UniqSupply -> CoreProgram -> CoreProgram) -> ModGuts -> CoreM ModGuts
doPassU do_pass = doPassDU (const do_pass)

doPassDFM :: (DynFlags -> FamInstEnvs -> CoreProgram -> IO CoreProgram) -> ModGuts -> CoreM ModGuts
doPassDFM do_pass guts = do
    dflags <- getDynFlags
    p_fam_env <- getPackageFamInstEnv
    let fam_envs = (p_fam_env, mg_fam_inst_env guts)
    doPassM (liftIO . do_pass dflags fam_envs) guts

doPassDFRM :: (DynFlags -> FamInstEnvs -> [CoreRule] -> CoreProgram -> IO CoreProgram) -> ModGuts -> CoreM ModGuts
doPassDFRM do_pass guts = do
    dflags <- getDynFlags
    p_fam_env <- getPackageFamInstEnv
    let fam_envs = (p_fam_env, mg_fam_inst_env guts)
    doPassM (liftIO . do_pass dflags fam_envs (mg_rules guts)) guts

doPassDFU :: (DynFlags -> FamInstEnvs -> UniqSupply -> CoreProgram -> CoreProgram) -> ModGuts -> CoreM ModGuts
doPassDFU do_pass guts = do
    dflags <- getDynFlags
    us     <- getUniqueSupplyM
    p_fam_env <- getPackageFamInstEnv
    let fam_envs = (p_fam_env, mg_fam_inst_env guts)
    doPass (do_pass dflags fam_envs us) guts

-- Most passes return no stats and don't change rules: these combinators
-- let us lift them to the full blown ModGuts+CoreM world
doPassM :: Monad m => (CoreProgram -> m CoreProgram) -> ModGuts -> m ModGuts
doPassM bind_f guts = do
    binds' <- bind_f (mg_binds guts)
    return (guts { mg_binds = binds' })

doPass :: (CoreProgram -> CoreProgram) -> ModGuts -> CoreM ModGuts
doPass bind_f guts = return $ guts { mg_binds = bind_f (mg_binds guts) }

-- Observer passes just peek; don't modify the bindings at all
observe :: (DynFlags -> CoreProgram -> IO a) -> ModGuts -> CoreM ModGuts
observe do_pass = doPassM $ \binds -> do
    dflags <- getDynFlags
    _ <- liftIO $ do_pass dflags binds
    return binds

{-
************************************************************************
*                                                                      *
        Gentle simplification
*                                                                      *
************************************************************************
-}

simplifyExpr :: HscEnv -- includes spec of what core-to-core passes to do
             -> CoreExpr
             -> IO CoreExpr
-- simplifyExpr is called by the driver to simplify an
-- expression typed in at the interactive prompt
simplifyExpr hsc_env expr
  = withTiming logger dflags (text "Simplify [expr]") (const ()) $
    do  { eps <- hscEPS hsc_env ;
        ; let rule_env  = mkRuleEnv (eps_rule_base eps) []
              fi_env    = ( eps_fam_inst_env eps
                          , extendFamInstEnvList emptyFamInstEnv $
                            snd $ ic_instances $ hsc_IC hsc_env )
              simpl_env = simplEnvForGHCi logger dflags

        ; let sz = exprSize expr

        ; (expr', counts) <- initSmpl logger dflags rule_env fi_env sz $
                             simplExprGently simpl_env expr

        ; Logger.dumpIfSet logger dflags (dopt Opt_D_dump_simpl_stats dflags)
                  "Simplifier statistics" (pprSimplCount counts)

        ; Logger.dumpIfSet_dyn logger dflags Opt_D_dump_simpl "Simplified expression"
                        FormatCore
                        (pprCoreExpr expr')

        ; return expr'
        }
  where
    dflags = hsc_dflags hsc_env
    logger = hsc_logger hsc_env

simplExprGently :: SimplEnv -> CoreExpr -> SimplM CoreExpr
-- Simplifies an expression
--      does occurrence analysis, then simplification
--      and repeats (twice currently) because one pass
--      alone leaves tons of crud.
-- Used (a) for user expressions typed in at the interactive prompt
--      (b) the LHS and RHS of a RULE
--      (c) Template Haskell splices
--
-- The name 'Gently' suggests that the SimplMode is InitialPhase,
-- and in fact that is so.... but the 'Gently' in simplExprGently doesn't
-- enforce that; it just simplifies the expression twice

-- It's important that simplExprGently does eta reduction; see
-- Note [Simplifying the left-hand side of a RULE] above.  The
-- simplifier does indeed do eta reduction (it's in GHC.Core.Opt.Simplify.completeLam)
-- but only if -O is on.

simplExprGently env expr = do
    expr1 <- simplExpr env (occurAnalyseExpr expr)
    simplExpr env (occurAnalyseExpr expr1)

{-
************************************************************************
*                                                                      *
\subsection{The driver for the simplifier}
*                                                                      *
************************************************************************
-}

simplifyPgm :: CoreToDo -> ModGuts -> CoreM ModGuts
simplifyPgm pass guts
  = do { hsc_env <- getHscEnv
       ; rb <- getRuleBase
       ; liftIOWithCount $
         simplifyPgmIO pass hsc_env rb guts }

simplifyPgmIO :: CoreToDo
              -> HscEnv
              -> RuleBase
              -> ModGuts
              -> IO (SimplCount, ModGuts)  -- New bindings

simplifyPgmIO pass@(CoreDoSimplify max_iterations mode)
              hsc_env hpt_rule_base
              guts@(ModGuts { mg_module = this_mod
                            , mg_rdr_env = rdr_env
                            , mg_deps = deps
                            , mg_binds = binds, mg_rules = rules
                            , mg_fam_inst_env = fam_inst_env })
  = do { (termination_msg, it_count, counts_out, guts')
           <- do_iteration 1 [] binds rules

        ; Logger.dumpIfSet logger dflags (dopt Opt_D_verbose_core2core dflags &&
                                dopt Opt_D_dump_simpl_stats  dflags)
                  "Simplifier statistics for following pass"
                  (vcat [text termination_msg <+> text "after" <+> ppr it_count
                                              <+> text "iterations",
                         blankLine,
                         pprSimplCount counts_out])

        ; return (counts_out, guts')
    }
  where
    dflags       = hsc_dflags hsc_env
    logger       = hsc_logger hsc_env
    print_unqual = mkPrintUnqualified (hsc_unit_env hsc_env) rdr_env
    simpl_env    = mkSimplEnv mode
    active_rule  = activeRule mode
    active_unf   = activeUnfolding mode

    do_iteration :: Int --UniqSupply
                --  -> Int          -- Counts iterations
                 -> [SimplCount] -- Counts from earlier iterations, reversed
                 -> CoreProgram  -- Bindings in
                 -> [CoreRule]   -- and orphan rules
                 -> IO (String, Int, SimplCount, ModGuts)

    do_iteration iteration_no counts_so_far binds rules
        -- iteration_no is the number of the iteration we are
        -- about to begin, with '1' for the first
      | iteration_no > max_iterations   -- Stop if we've run out of iterations
      = warnPprTrace (debugIsOn && (max_iterations > 2))
            ( hang (text "Simplifier bailing out after" <+> int max_iterations
                    <+> text "iterations"
                    <+> (brackets $ hsep $ punctuate comma $
                         map (int . simplCountN) (reverse counts_so_far)))
                 2 (text "Size =" <+> ppr (coreBindsStats binds))) $

                -- Subtract 1 from iteration_no to get the
                -- number of iterations we actually completed
        return ( "Simplifier baled out", iteration_no - 1
               , totalise counts_so_far
               , guts { mg_binds = binds, mg_rules = rules } )

      -- Try and force thunks off the binds; significantly reduces
      -- space usage, especially with -O.  JRS, 000620.
      | let sz = coreBindsSize binds
      , () <- sz `seq` ()     -- Force it
      = do {
                -- Occurrence analysis
           let { tagged_binds = {-# SCC "OccAnal" #-}
                     occurAnalysePgm this_mod active_unf active_rule rules
                                     binds
               } ;
           Logger.dumpIfSet_dyn logger dflags Opt_D_dump_occur_anal "Occurrence analysis"
                     FormatCore
                     (pprCoreBindings tagged_binds);

                -- Get any new rules, and extend the rule base
                -- See Note [Overall plumbing for rules] in GHC.Core.Rules
                -- We need to do this regularly, because simplification can
                -- poke on IdInfo thunks, which in turn brings in new rules
                -- behind the scenes.  Otherwise there's a danger we'll simply
                -- miss the rules for Ids hidden inside imported inlinings
           eps <- hscEPS hsc_env ;
           let  { rule_base1 = unionRuleBase hpt_rule_base (eps_rule_base eps)
                ; rule_base2 = extendRuleBaseList rule_base1 rules
                ; fam_envs = (eps_fam_inst_env eps, fam_inst_env)
                ; vis_orphs = this_mod : dep_orphs deps } ;

                -- Simplify the program
           ((binds1, rules1), counts1) <-
             initSmpl logger dflags (mkRuleEnv rule_base2 vis_orphs) fam_envs sz $
               do { (floats, env1) <- {-# SCC "SimplTopBinds" #-}
                                      simplTopBinds simpl_env tagged_binds

                      -- Apply the substitution to rules defined in this module
                      -- for imported Ids.  Eg  RULE map my_f = blah
                      -- If we have a substitution my_f :-> other_f, we'd better
                      -- apply it to the rule to, or it'll never match
                  ; rules1 <- simplRules env1 Nothing rules Nothing

                  ; return (getTopFloatBinds floats, rules1) } ;

                -- Stop if nothing happened; don't dump output
                -- See Note [Which transformations are innocuous] in GHC.Core.Opt.Monad
           if isZeroSimplCount counts1 then
                return ( "Simplifier reached fixed point", iteration_no
                       , totalise (counts1 : counts_so_far)  -- Include "free" ticks
                       , guts { mg_binds = binds1, mg_rules = rules1 } )
           else do {
                -- Short out indirections
                -- We do this *after* at least one run of the simplifier
                -- because indirection-shorting uses the export flag on *occurrences*
                -- and that isn't guaranteed to be ok until after the first run propagates
                -- stuff from the binding site to its occurrences
                --
                -- ToDo: alas, this means that indirection-shorting does not happen at all
                --       if the simplifier does nothing (not common, I know, but unsavoury)
           let { binds2 = {-# SCC "ZapInd" #-} shortOutIndirections binds1 } ;

                -- Dump the result of this iteration
           dump_end_iteration logger dflags print_unqual iteration_no counts1 binds2 rules1 ;
           lintPassResult hsc_env pass binds2 ;

                -- Loop
           do_iteration (iteration_no + 1) (counts1:counts_so_far) binds2 rules1
           } }
#if __GLASGOW_HASKELL__ <= 810
      | otherwise = panic "do_iteration"
#endif
      where
        -- Remember the counts_so_far are reversed
        totalise :: [SimplCount] -> SimplCount
        totalise = foldr (\c acc -> acc `plusSimplCount` c)
                         (zeroSimplCount dflags)

simplifyPgmIO _ _ _ _ = panic "simplifyPgmIO"

-------------------
dump_end_iteration :: Logger -> DynFlags -> PrintUnqualified -> Int
                   -> SimplCount -> CoreProgram -> [CoreRule] -> IO ()
dump_end_iteration logger dflags print_unqual iteration_no counts binds rules
  = dumpPassResult logger dflags print_unqual mb_flag hdr pp_counts binds rules
  where
    mb_flag | dopt Opt_D_dump_simpl_iterations dflags = Just Opt_D_dump_simpl_iterations
            | otherwise                               = Nothing
            -- Show details if Opt_D_dump_simpl_iterations is on

    hdr = text "Simplifier iteration=" <> int iteration_no
    pp_counts = vcat [ text "---- Simplifier counts for" <+> hdr
                     , pprSimplCount counts
                     , text "---- End of simplifier counts for" <+> hdr ]

{-
************************************************************************
*                                                                      *
                Shorting out indirections
*                                                                      *
************************************************************************

If we have this:

        x_local = <expression>
        ...bindings...
        x_exported = x_local

where x_exported is exported, and x_local is not, then we replace it with this:

        x_exported = <expression>
        x_local = x_exported
        ...bindings...

Without this we never get rid of the x_exported = x_local thing.  This
save a gratuitous jump (from \tr{x_exported} to \tr{x_local}), and
makes strictness information propagate better.  This used to happen in
the final phase, but it's tidier to do it here.

Note [Messing up the exported Id's RULES]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We must be careful about discarding (obviously) or even merging the
RULES on the exported Id. The example that went bad on me at one stage
was this one:

    iterate :: (a -> a) -> a -> [a]
        [Exported]
    iterate = iterateList

    iterateFB c f x = x `c` iterateFB c f (f x)
    iterateList f x =  x : iterateList f (f x)
        [Not exported]

    {-# RULES
    "iterate"   forall f x.     iterate f x = build (\c _n -> iterateFB c f x)
    "iterateFB"                 iterateFB (:) = iterateList
     #-}

This got shorted out to:

    iterateList :: (a -> a) -> a -> [a]
    iterateList = iterate

    iterateFB c f x = x `c` iterateFB c f (f x)
    iterate f x =  x : iterate f (f x)

    {-# RULES
    "iterate"   forall f x.     iterate f x = build (\c _n -> iterateFB c f x)
    "iterateFB"                 iterateFB (:) = iterate
     #-}

And now we get an infinite loop in the rule system
        iterate f x -> build (\cn -> iterateFB c f x)
                    -> iterateFB (:) f x
                    -> iterate f x

Old "solution":
        use rule switching-off pragmas to get rid
        of iterateList in the first place

But in principle the user *might* want rules that only apply to the Id
they say.  And inline pragmas are similar
   {-# NOINLINE f #-}
   f = local
   local = <stuff>
Then we do not want to get rid of the NOINLINE.

Hence hasShortableIdinfo.


Note [Rules and indirection-zapping]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Problem: what if x_exported has a RULE that mentions something in ...bindings...?
Then the things mentioned can be out of scope!  Solution
 a) Make sure that in this pass the usage-info from x_exported is
        available for ...bindings...
 b) If there are any such RULES, rec-ify the entire top-level.
    It'll get sorted out next time round

Other remarks
~~~~~~~~~~~~~
If more than one exported thing is equal to a local thing (i.e., the
local thing really is shared), then we do one only:
\begin{verbatim}
        x_local = ....
        x_exported1 = x_local
        x_exported2 = x_local
==>
        x_exported1 = ....

        x_exported2 = x_exported1
\end{verbatim}

We rely on prior eta reduction to simplify things like
\begin{verbatim}
        x_exported = /\ tyvars -> x_local tyvars
==>
        x_exported = x_local
\end{verbatim}
Hence,there's a possibility of leaving unchanged something like this:
\begin{verbatim}
        x_local = ....
        x_exported1 = x_local Int
\end{verbatim}
By the time we've thrown away the types in STG land this
could be eliminated.  But I don't think it's very common
and it's dangerous to do this fiddling in STG land
because we might eliminate a binding that's mentioned in the
unfolding for something.

Note [Indirection zapping and ticks]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Unfortunately this is another place where we need a special case for
ticks. The following happens quite regularly:

        x_local = <expression>
        x_exported = tick<x> x_local

Which we want to become:

        x_exported =  tick<x> <expression>

As it makes no sense to keep the tick and the expression on separate
bindings. Note however that this might increase the ticks scoping
over the execution of x_local, so we can only do this for floatable
ticks. More often than not, other references will be unfoldings of
x_exported, and therefore carry the tick anyway.
-}

type IndEnv = IdEnv (Id, [CoreTickish]) -- Maps local_id -> exported_id, ticks

shortOutIndirections :: CoreProgram -> CoreProgram
shortOutIndirections binds
  | isEmptyVarEnv ind_env = binds
  | no_need_to_flatten    = binds'                      -- See Note [Rules and indirect-zapping]
  | otherwise             = [Rec (flattenBinds binds')] -- for this no_need_to_flatten stuff
  where
    ind_env            = makeIndEnv binds
    -- These exported Ids are the subjects  of the indirection-elimination
    exp_ids            = map fst $ nonDetEltsUFM ind_env
      -- It's OK to use nonDetEltsUFM here because we forget the ordering
      -- by immediately converting to a set or check if all the elements
      -- satisfy a predicate.
    exp_id_set         = mkVarSet exp_ids
    no_need_to_flatten = all (null . ruleInfoRules . idSpecialisation) exp_ids
    binds'             = concatMap zap binds

    zap (NonRec bndr rhs) = [NonRec b r | (b,r) <- zapPair (bndr,rhs)]
    zap (Rec pairs)       = [Rec (concatMap zapPair pairs)]

    zapPair (bndr, rhs)
        | bndr `elemVarSet` exp_id_set
        = []   -- Kill the exported-id binding

        | Just (exp_id, ticks) <- lookupVarEnv ind_env bndr
        , (exp_id', lcl_id') <- transferIdInfo exp_id bndr
        =      -- Turn a local-id binding into two bindings
               --    exp_id = rhs; lcl_id = exp_id
          [ (exp_id', mkTicks ticks rhs),
            (lcl_id', Var exp_id') ]

        | otherwise
        = [(bndr,rhs)]

makeIndEnv :: [CoreBind] -> IndEnv
makeIndEnv binds
  = foldl' add_bind emptyVarEnv binds
  where
    add_bind :: IndEnv -> CoreBind -> IndEnv
    add_bind env (NonRec exported_id rhs) = add_pair env (exported_id, rhs)
    add_bind env (Rec pairs)              = foldl' add_pair env pairs

    add_pair :: IndEnv -> (Id,CoreExpr) -> IndEnv
    add_pair env (exported_id, exported)
        | (ticks, Var local_id) <- stripTicksTop tickishFloatable exported
        , shortMeOut env exported_id local_id
        = extendVarEnv env local_id (exported_id, ticks)
    add_pair env _ = env

-----------------
shortMeOut :: IndEnv -> Id -> Id -> Bool
shortMeOut ind_env exported_id local_id
-- The if-then-else stuff is just so I can get a pprTrace to see
-- how often I don't get shorting out because of IdInfo stuff
  = if isExportedId exported_id &&              -- Only if this is exported

       isLocalId local_id &&                    -- Only if this one is defined in this
                                                --      module, so that we *can* change its
                                                --      binding to be the exported thing!

       not (isExportedId local_id) &&           -- Only if this one is not itself exported,
                                                --      since the transformation will nuke it

       not (local_id `elemVarEnv` ind_env)      -- Only if not already substituted for
    then
        if hasShortableIdInfo exported_id
        then True       -- See Note [Messing up the exported Id's IdInfo]
        else warnPprTrace True (text "Not shorting out:" <+> ppr exported_id) False
    else
        False

-----------------
hasShortableIdInfo :: Id -> Bool
-- True if there is no user-attached IdInfo on exported_id,
-- so we can safely discard it
-- See Note [Messing up the exported Id's IdInfo]
hasShortableIdInfo id
  =  isEmptyRuleInfo (ruleInfo info)
  && isDefaultInlinePragma (inlinePragInfo info)
  && not (isStableUnfolding (unfoldingInfo info))
  where
     info = idInfo id

-----------------
{- Note [Transferring IdInfo]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If we have
     lcl_id = e; exp_id = lcl_id

and lcl_id has useful IdInfo, we don't want to discard it by going
     gbl_id = e; lcl_id = gbl_id

Instead, transfer IdInfo from lcl_id to exp_id, specifically
* (Stable) unfolding
* Strictness
* Rules
* Inline pragma

Overwriting, rather than merging, seems to work ok.

We also zap the InlinePragma on the lcl_id. It might originally
have had a NOINLINE, which we have now transferred; and we really
want the lcl_id to inline now that its RHS is trivial!
-}

transferIdInfo :: Id -> Id -> (Id, Id)
-- See Note [Transferring IdInfo]
transferIdInfo exported_id local_id
  = ( modifyIdInfo transfer exported_id
    , local_id `setInlinePragma` defaultInlinePragma )
  where
    local_info = idInfo local_id
    transfer exp_info = exp_info `setDmdSigInfo`    dmdSigInfo local_info
                                 `setCprSigInfo`           cprSigInfo local_info
                                 `setUnfoldingInfo`     unfoldingInfo local_info
                                 `setInlinePragInfo`    inlinePragInfo local_info
                                 `setRuleInfo`          addRuleInfo (ruleInfo exp_info) new_info
    new_info = setRuleInfoHead (idName exported_id)
                               (ruleInfo local_info)
        -- Remember to set the function-name field of the
        -- rules as we transfer them from one function to another



dmdAnal :: Logger -> DynFlags -> FamInstEnvs -> [CoreRule] -> CoreProgram -> IO CoreProgram
dmdAnal logger dflags fam_envs rules binds = do
  let !opts = DmdAnalOpts
               { dmd_strict_dicts = gopt Opt_DictsStrict dflags
               }
      binds_plus_dmds = dmdAnalProgram opts fam_envs rules binds
  Logger.dumpIfSet_dyn logger dflags Opt_D_dump_str_signatures "Strictness signatures" FormatText $
    dumpIdInfoOfProgram (ppr . zapDmdEnvSig . dmdSigInfo) binds_plus_dmds
  -- See Note [Stamp out space leaks in demand analysis] in GHC.Core.Opt.DmdAnal
  seqBinds binds_plus_dmds `seq` return binds_plus_dmds
