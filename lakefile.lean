import Lake
open Lake DSL

package LSpec

lean_lib LSpec

@[defaultTarget]
lean_exe lspec {
  root := `Main
}
