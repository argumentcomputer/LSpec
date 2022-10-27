import Lake
open Lake DSL

package LSpec

lean_lib LSpec

@[default_target]
lean_exe lspec {
  root := `Main
}
