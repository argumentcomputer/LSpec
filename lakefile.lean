import Lake
open Lake DSL

package LSpec

lean_lib LSpec

@[default_target]
lean_exe lspec {
  supportInterpreter := true
  root := `Main
}

lean_exe «lspec-ci» {
  root := `CI
}

lean_exe Tests.aa
