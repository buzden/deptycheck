||| The derived generator for `X`, kept in its own module so that only the tests
||| that need it pay for running the derivation.
module XDerived

import public Data.Fuel

import public XGens

import Deriving.DepTyCheck.Gen

%default total

export
genX : Fuel -> (n : Nat) -> Gen MaybeEmpty (X n)
genX = deriveGen
