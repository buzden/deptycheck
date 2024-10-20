module DerivedGen

import public Deriving.DepTyCheck.Util.Fusion
import public Deriving.DepTyCheck.Gen.Core

%default total


deps : List Arg
deps = [MkArg MW ExplicitArg Nothing (var "X" .$ bindVar "a" .$ bindVar "b"), MkArg MW ExplicitArg Nothing (var "Y" .$ bindVar "b" .$ bindVar "c")]


main : IO ()
main = putPretty $ solveDependencies deps
