module DerivedGen

import public Deriving.DepTyCheck.Util.Fusion
import public Deriving.DepTyCheck.Gen.Core

%default total


deps : List Arg
deps = [ MkArg MW ExplicitArg Nothing (var "X" .$ bindVar "a")
       , MkArg MW ExplicitArg Nothing (var "Y" .$ bindVar "a")
       , MkArg MW ExplicitArg Nothing (var "Z" .$ bindVar "b") ]


main : IO ()
main = putPretty $ solveDependencies deps
