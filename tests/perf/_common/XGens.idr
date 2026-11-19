||| The probe type `X` of the investigation's section 4.1, and every hand-written
||| generator for it that the investigation measured.
|||
||| `X n` has exactly one inhabitant, so it has nothing to choose and nothing to
||| branch on. Anything measured on it is the cost of the generator machinery
||| itself, which is what makes it the right subject for a complexity gate: the
||| numbers cannot drift because a distribution changed.
module XGens

import Data.Nat1

import public Test.DepTyCheck.Gen

%default total

public export
data X : Nat -> Type where
  XZ : X 0
  XS : X n -> X (S n)

||| Walks the whole value, so that adding the result forces generation to have
||| really happened.
public export
depth : X n -> Nat
depth XZ     = 0
depth (XS x) = S $ depth x

--- Composition styles: expected to be linear (investigation, section 7.3) ---

||| The baseline. Every bind's continuation returns `pure`, so the chain
||| telescopes into a single `Pure` node and sampling costs one traversal.
export
genXByHand : (n : Nat) -> Gen MaybeEmpty (X n)
genXByHand 0     = pure XZ
genXByHand (S k) = genXByHand k >>= \x => pure $ XS x

export
genXMap : (n : Nat) -> Gen MaybeEmpty (X n)
genXMap 0     = pure XZ
genXMap (S k) = XS <$> genXMap k

export
genXAp : (n : Nat) -> Gen MaybeEmpty (X n)
genXAp 0     = pure XZ
genXAp (S k) = pure XS <*> genXAp k

--- Placement of a single `oneOf` (investigation, section 7.5) ---

||| One `oneOf`, on top of a body that telescopes. Off the recursion edge, so
||| expected to stay linear.
export
genXOneOfOffEdge : (n : Nat) -> Gen MaybeEmpty (X n)
genXOneOfOffEdge 0     = pure XZ
genXOneOfOffEdge (S k) = oneOf [ genXByHand k >>= \x => pure $ XS x ]

||| One `oneOf`, in the base case, so reached exactly once. Expected to stay
||| linear, at a constant factor of about 4.5 --- which is itself worth
||| watching, and is the subject of the second upstream issue the investigation
||| proposes.
export
genXOneOfInBase : (n : Nat) -> Gen MaybeEmpty (X n)
genXOneOfInBase 0     = oneOf [ pure XZ ]
genXOneOfInBase (S k) = genXOneOfInBase k >>= \x => pure $ XS x

--- `oneOf` on the recursion edge, by arity (investigation, section 7.4) ---

||| One always-live alternative --- nothing to choose --- re-created at every
||| level. This is the mechanism the investigation holds responsible for derived
||| generators being super-quadratic, and it reproduces the derived generator's
||| curve almost exactly.
export
genXOneOf1 : (n : Nat) -> Gen MaybeEmpty (X n)
genXOneOf1 0     = pure XZ
genXOneOf1 (S k) = oneOf [ genXOneOf1 k >>= \x => pure $ XS x ]

export
genXOneOf2 : (n : Nat) -> Gen MaybeEmpty (X n)
genXOneOf2 0     = pure XZ
genXOneOf2 (S k) = oneOf [ genXOneOf2 k >>= \x => pure $ XS x
                         , genXOneOf2 k >>= \x => pure $ XS x
                         ]

export
genXOneOf3 : (n : Nat) -> Gen MaybeEmpty (X n)
genXOneOf3 0     = pure XZ
genXOneOf3 (S k) = oneOf [ genXOneOf3 k >>= \x => pure $ XS x
                         , genXOneOf3 k >>= \x => pure $ XS x
                         , genXOneOf3 k >>= \x => pure $ XS x
                         ]

--- `frequency`, with and without the weight recomputation `deriveGen` emits ---

||| Structural weight, linear in its argument, as derivation computes it.
weightOfNat : Nat -> Nat1
weightOfNat Z     = one
weightOfNat (S k) = succ $ weightOfNat k

export
genXFreq1 : (n : Nat) -> Gen MaybeEmpty (X n)
genXFreq1 0     = pure XZ
genXFreq1 (S k) = frequency [ (weightOfNat k, genXFreq1 k >>= \x => pure $ XS x) ]

export
genXFreq2Const : (n : Nat) -> Gen MaybeEmpty (X n)
genXFreq2Const 0     = pure XZ
genXFreq2Const (S k) = frequency [ (one, genXFreq2Const k >>= \x => pure $ XS x)
                                 , (one, genXFreq2Const k >>= \x => pure $ XS x)
                                 ]

export
genXFreq2Weighted : (n : Nat) -> Gen MaybeEmpty (X n)
genXFreq2Weighted 0     = pure XZ
genXFreq2Weighted (S k) = frequency [ (weightOfNat k, genXFreq2Weighted k >>= \x => pure $ XS x)
                                    , (one          , genXFreq2Weighted k >>= \x => pure $ XS x)
                                    ]
