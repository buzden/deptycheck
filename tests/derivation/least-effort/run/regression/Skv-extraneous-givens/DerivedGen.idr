module DerivedGen

import RunDerivedGen

%default total

record FI n where
    constructor MkFI
    v : Nat
    p : LTE v n

namespace VN
    public export
    data VN : Nat -> Type where
        Nil : VN 0
        (::) : Nat -> VN n -> VN (S n)

namespace HVF
    public export
    data HVF : (k : Nat) -> VN k -> Type where
        Nil : HVF 0 []
        (::) : FI n -> HVF k ns -> HVF (S k) (n :: ns)

data X : Nat -> (n : Nat) -> FI n -> Type

namespace HVX
    public export
    data HVX : Nat -> (k : Nat) -> (ns : VN k) -> HVF k ns -> Type where
        Nil : HVX z 0 [] []
        (::) : forall z, n, ns, cs, c.
               X z n c ->
               HVX z k ns cs ->
               HVX z (S k) (n :: ns) (c :: cs)

data X : Nat -> (n : Nat) -> FI n -> Type where
    MkX : forall z, n, kv, ns, cs.
          {0 kp : LTE (S kv) (n * z)} ->
          HVX z kv ns cs ->
          X z n (MkFI n Control.Relation.reflexive)

Show (FI n) where
  show (MkFI v p) = "MkFI \{show v}"

Show (HVX z k ns cs) where
  show Nil = "[]"
  show ((::) (MkX es) xs) = "\{show es} :: \{show xs}"

Show (X z n c) where
  show (MkX es) = "MkX \{show es} prf"

checkedGen : Fuel -> (z : Nat) -> Gen MaybeEmpty (n ** c ** X z n c)
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

main : IO ()
main = runGs
  [
    (G $ \fl => checkedGen fl 16),
    (G $ \fl => checkedGen fl 32),
    (G $ \fl => checkedGen fl 512),
    (G $ \fl => checkedGen fl 1024)
  ]
