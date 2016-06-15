module StrictCore.Plugin (plugin) where

--------------------------------------------------------------------------------

import           GhcPlugins

import           StrictCore.Syntax

--------------------------------------------------------------------------------

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = installPlugin }

installPlugin :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
installPlugin _ todos
  = return ( CoreDoPluginPass "StrictCore" pass : todos )

pass :: ModGuts -> CoreM ModGuts
pass guts@ModGuts{ mg_binds = binds }
  = do let strictCoreBinds = map (translateBind initSCVars) binds
       pprTrace "StrictCore pass" (ppr strictCoreBinds) (return guts)
