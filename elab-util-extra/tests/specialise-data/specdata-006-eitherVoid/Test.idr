module Test

import Shared

%language ElabReflection

%runElab specialiseData' (\a => Either Void a) "EitherVoid"

e0' : Unit
e0' = %runElab verifySpecialisation (Either Void Nat) (EitherVoid Nat) [`(Right 0), `(Right 1), `(Right 10)]

e0NoLeft : EitherVoid Nat -> Nat
e0NoLeft (Right n) = n

e1' : Unit
e1' = %runElab verifySpecialisation (Either Void String) (EitherVoid String) [`(Right ""), `(Right "hello"), `(Right "world")]

e1NoLeft : EitherVoid String -> String
e1NoLeft (Right n) = n
