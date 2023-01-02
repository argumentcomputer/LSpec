import Lake
open Lake DSL

package LSpec

lean_lib LSpec

@[default_target]
lean_exe lspec where
  root := `Main

lean_exe «lspec-ci» where
  root := `CI
