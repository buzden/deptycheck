||| The length-indexed list of the investigation's section 4.1: the original case
||| study, and the only subject here that actually branches.
module NatListGens

import public Data.Fuel

import public Test.DepTyCheck.Gen

import Deriving.DepTyCheck.Gen

%default total

public export
data NatList : Nat -> Type where
  Nil  : NatList 0
  Cons : Nat -> NatList n -> NatList (S n)

||| Walks the whole value, elements included, so that adding the result forces
||| generation to have really happened.
public export
weighNatList : NatList n -> Nat
weighNatList Nil         = 0
weighNatList (Cons x xs) = S $ x + weighNatList xs

export
genNatList : Fuel -> (l : Nat) -> Gen MaybeEmpty (NatList l)
genNatList = deriveGen

||| Hand-written spine with the element hardcoded, so the derived element
||| generator is never called. Linear, and about five orders of magnitude faster
||| than the derived generator over the measured range --- the reference the
||| whole investigation is built against.
export
genDegenerateLists : (l : Nat) -> Gen MaybeEmpty (NatList l)
genDegenerateLists 0     = pure Nil
genDegenerateLists (S k) = genDegenerateLists k >>= \xs => pure $ Cons Z xs
