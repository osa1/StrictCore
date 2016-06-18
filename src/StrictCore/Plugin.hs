module StrictCore.Plugin (plugin) where

--------------------------------------------------------------------------------

import CoreLint (displayLintResults)
import GhcPlugins

import StrictCore.Lint
import StrictCore.Simplify (initSimplEnv, simplifyPgm)
import StrictCore.Syntax (initSCVars, translateBind)

--------------------------------------------------------------------------------

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = installPlugin }

installPlugin :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
installPlugin _ todos
  = return ( CoreDoPluginPass "StrictCore" pass : todos )

pass :: ModGuts -> CoreM ModGuts
pass guts@ModGuts{ mg_binds = binds }
  = do us <- getUniqueSupplyM
       let strictcore_binds = initUs_ us (mapM (fmap snd . translateBind initSCVars) binds)
       pprTrace "StrictCore pass" (ppr strictcore_binds) (return ())

       dflags <- getDynFlags

       -- lint the translation
       let (warns0, errs0) = lintCoreProgram dflags [] strictcore_binds
       liftIO $ displayLintResults dflags (CoreDoPluginPass "StrictCore" undefined) warns0 errs0 []

       -- run simplifier
       let simplified_pgm = simplifyPgm initSimplEnv strictcore_binds
       pprTrace "Simplifier pass" (ppr simplified_pgm) (return ())
       -- lint the simplification
       let (warns1, errs1) = lintCoreProgram dflags [] simplified_pgm
       liftIO $ displayLintResults dflags (CoreDoPluginPass "StrictCore" undefined) warns1 errs1 []

       return guts
