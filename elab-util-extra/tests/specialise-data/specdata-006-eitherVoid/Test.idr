module Test

import Shared

%language ElabReflection

%runElab specialiseData' (\a => Either Void a) "EitherVoid"

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e0' = %runElab verifySpecialisation (Either Void Nat) (EitherVoid Nat)
  [ `(Right 0)
  , `(Right 1)
  , `(Right 10)
  ]

e0NoLeft : EitherVoid Nat -> Nat
e0NoLeft (Right n) = n

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e1' = %runElab verifySpecialisation (Either Void String) (EitherVoid String)
  [ `(Right "")
  , `(Right "hello")
  , `(Right "world")
  ]

e1NoLeft : EitherVoid String -> String
e1NoLeft (Right n) = n
