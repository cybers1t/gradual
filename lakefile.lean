import Lake
open Lake DSL

package Gradual where
  precompileModules := true

@[default_target]
lean_exe Gradual where
  root := `gradual


require verso from git "https://github.com/leanprover/verso.git"@"main"

-- A demo site that shows how to generate websites with Verso
lean_lib Site where
  roots := #[`Site]

@[default_target]
lean_exe SiteExe where
  root := `SiteMain
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

