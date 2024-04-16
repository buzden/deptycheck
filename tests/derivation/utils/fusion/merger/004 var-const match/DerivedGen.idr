module DerivedGen

import public Deriving.DepTyCheck.Util.Fusion
import public Deriving.DepTyCheck.Gen.Core


%default total

data X : Nat -> Type where
    MkX : X n
  
data Y : Nat -> Type where
    MkY : Y 1 -- unexpected behaviour for 0

%language ElabReflection

%runElab runFusion `{X} [`{n}] `{Y} [`{n}]
