import Lake
open Lake DSL

package LSpec

lean_lib LSpec

lean_exe lspec where
  root := `Main

lean_exe «lspec-ci» where
  root := `CI
