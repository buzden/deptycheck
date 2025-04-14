module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

namespace A

  public export
  data FinsList : Nat -> Type where
    Nil  : FinsList n
    (::) : Fin n -> FinsList n -> FinsList n

  public export
  (.length) : FinsList n -> Nat
  (.length) []      = 0
  (.length) (x::xs) = S xs.length

  public export
  fst : (fs : FinsList s) -> Fin fs.length -> Fin s
  fst (f::_ ) _ = f

namespace B

  public export
  data NatsList = Nil | (::) Nat NatsList

  public export
  (.length) : NatsList -> Nat
  (.length) []      = Z
  (.length) (_::ms) = S ms.length

data FindNat : (nats: NatsList) -> Fin (nats.length) -> Type where
  MHere  : FindNat (p::ps) FZ

data Test : (nats: NatsList) -> FinsList (nats.length) -> Type where
  MkT  : FindNat nats (fst fins f) -> Test nats fins

checkedGen : Fuel -> (nats: NatsList) -> (fins: FinsList $ nats.length) -> Gen MaybeEmpty $ Test nats fins
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show (Test ns fs) where
  show _ = "indeed"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl [3, 4, 1] [2, 2, 0]
  , G $ \fl => checkedGen fl [3, 4, 1] [0]
  ]
