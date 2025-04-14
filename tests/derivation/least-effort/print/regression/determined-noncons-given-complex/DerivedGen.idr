module DerivedGen

import Deriving.DepTyCheck.Gen

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

%language ElabReflection

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $
  Fuel -> (nats: NatsList) -> (fins: FinsList $ nats.length) -> Gen MaybeEmpty $ Test nats fins
