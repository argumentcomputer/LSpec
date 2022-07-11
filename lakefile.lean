import Lake
open Lake DSL

package LSpec

@[defaultTarget]
lean_exe lspec {
  root := `Main
}
