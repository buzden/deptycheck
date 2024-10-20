module DerivedGen

import public Deriving.DepTyCheck.Util.Fusion
import public Deriving.DepTyCheck.Gen.Core

%default total

data X : Type -> Type where
    MkX : X n

data Y : Type -> Type where
    MkY : Y n

data Z : Type where
  MkZ : (n : Type) -> X n -> Y n -> Z

%language ElabReflection

decl : Maybe FusionDecl
decl = %runElab runFusion `{X} [`{n}] `{Y} [`{n}]

declared : ()
declared = %runElab declare $ getFusion decl

sign : Maybe GenSignature
sign = %runElab createGenSignature `{XY}

main : IO ()
main = case sign of
          Nothing => printLn "no signature generated"
          Just x => printLn "signature generated"
