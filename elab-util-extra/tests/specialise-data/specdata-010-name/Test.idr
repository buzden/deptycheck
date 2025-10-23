module Test

import Shared

%language ElabReflection

%runElab specialiseData' "MyName" Name

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e0' = %runElab verifySpecialisation Name MyName
  [ `(NS (MkNS []) "Test")
  , `(NS (MkNS ["Prelude"]) "Test")
  , `(UN (Basic "a"))
  , `(UN (Field "f"))
  , `(UN Underscore)
  , `(MN "test" 23)
  , `(DN "test" "testname")
  , `(Nested (0,1) "nested")
  , `(CaseBlock "cbcb" 0)
  , `(WithBlock "wbwb" 0)
  ]

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e1' = %runElab verifyFromStrings Name MyName ["Hello", "World", "a.b", ""]
