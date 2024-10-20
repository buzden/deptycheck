module DerivedGen

import public Deriving.DepTyCheck.Util.Fusion
import public Deriving.DepTyCheck.Gen.Core


%default total

data X : String -> Type where
    MkX : X "0"

data Y : String -> Type where
    MkY : Y "0"

%language ElabReflection

decl : Maybe FusionDecl
decl = %runElab runFusion `{X} [`{n}] `{Y} [`{n}]

main : IO ()
main = putPretty $ getFusion decl
