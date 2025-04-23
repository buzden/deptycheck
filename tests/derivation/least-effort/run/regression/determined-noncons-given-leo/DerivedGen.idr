module DerivedGen

import RunDerivedGen

import Data.Fin

%default total

namespace FinsList

  public export
  data FinsList : Nat -> Type where
    Nil  : FinsList n
    (::) : Fin n -> FinsList n -> FinsList n

  public export
  (.length) : FinsList n -> Nat
  (.length) []      = 0
  (.length) (x::xs) = S xs.length

namespace NatsList

  public export
  data NatsList : Type where
    Nil  : NatsList
    (::) : Nat -> NatsList -> NatsList

namespace ModuleSig

  public export
  record ModuleSig where
    constructor MkModuleSig
    inputs  : NatsList
    outputs : NatsList

  %name ModuleSig m

  public export
  data ModuleSigsList = Nil | (::) ModuleSig ModuleSigsList

  %name ModuleSigsList ms

  public export
  (.length) : ModuleSigsList -> Nat
  (.length) []      = Z
  (.length) (_::ms) = S $ ms.length

public export
data CtxPorts : (ms : ModuleSigsList) -> (subMs : FinsList ms.length) ->
                (subMFins : FinsList subMs.length) -> ModuleSigsList -> Type where
  CPEmpty : CtxPorts ms [] [] []
  CPCons  : {ms : ModuleSigsList} -> {subMs : FinsList ms.length} ->
            {subMF : Fin subMs.length} -> {restFins : FinsList subMs.length} ->
            CtxPorts ms subMs restFins ps -> CtxPorts ms subMs (subMF::restFins) (p::ps)

public export
data Modules : ModuleSigsList -> Type where
  End : Modules ms
  NewCompositeModule : (subMs : FinsList ms.length) -> (ctxPorts : CtxPorts ms subMs [] ports) -> Modules ms

checkedGen : Fuel -> (ms : ModuleSigsList) -> Gen MaybeEmpty $ Modules ms
checkedGen = deriveGen @{MainCoreDerivator @{LeastEffort}}

Show (Modules sigs) where
  show End = "End"
  show $ NewCompositeModule _ _ = "NewCompositeModule _ _"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl []
  ]
