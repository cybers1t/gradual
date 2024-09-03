import Lake
open Lake DSL

package Gradual where
  precompileModules := true

@[default_target]
lean_exe Gradual where
  root := `gradual


require verso from git "https://github.com/leanprover/verso.git"@"main"
