module StrictCore.Plugin (plugin) where

--------------------------------------------------------------------------------

import CoreLint (displayLintResults)
import GhcPlugins

import StrictCore.Lint
import StrictCore.Syntax

--------------------------------------------------------------------------------

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = installPlugin }

installPlugin :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
installPlugin _ todos
  = return ( CoreDoPluginPass "StrictCore" pass : todos )

pass :: ModGuts -> CoreM ModGuts
pass guts@ModGuts{ mg_binds = binds }
  = do us <- getUniqueSupplyM
       let strictCoreBinds = initUs_ us (mapM (fmap snd . translateBind initSCVars) binds)
       pprTrace "StrictCore pass" (ppr strictCoreBinds) (return ())
       dflags <- getDynFlags
       let (warns, errs) = lintCoreProgram dflags [] strictCoreBinds
       liftIO $ displayLintResults dflags (CoreDoPluginPass "StrictCore" undefined) warns errs []
       return guts

