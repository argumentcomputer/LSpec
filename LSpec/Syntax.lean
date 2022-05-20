import LSpec.Spec

syntax "it " str " so " term " should be " term : doElem
syntax "it " str " so " term " never equals " term " check " term : doElem

syntax (name := testSuite) withPosition("test_suite" colGt doElem*) : command

set_option hygiene false in
macro_rules
  | `(doElem| it $s so $l should be $r) => 
    `(doElem| results := results.concat (ExampleOf.fromDescrParam (equals $l $r) $s ()).run )
  | `(doElem| it $s so $f never equals $b check $a) => 
    `(doElem| results := results.concat (ExampleOf.fromDescrParam (alwaysEquals $f $b) $s $a).run )
  | `(testSuite| test_suite $ts*) => 
      `(def testName : IO UInt32 := do
          let mut results : List String := []
          $[$ts:doElem]*
          for result in results do
            IO.println result
          return 0)