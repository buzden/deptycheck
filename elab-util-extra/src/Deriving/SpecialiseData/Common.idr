module Deriving.SpecialiseData.Common

import Deriving.Show
import Language.Reflection.Compat

%language ElabReflection

---------------------------------
--- SPECIALISATION ERROR TYPE ---
---------------------------------

||| Specialisation error
public export
data SpecialisationError : Type where
  ||| Failed to extract polymorphic type name from task
  TaskTypeExtractionError   : SpecialisationError
  ||| Unused variable
  UnusedVarError            : SpecialisationError
  ||| Partial specification
  PartialSpecError          : SpecialisationError
  ||| Internal error
  InternalError             : String -> SpecialisationError
  ||| Lambda has unnamed arguments
  UnnamedArgInLambdaError   : SpecialisationError
  ||| Polymorphic type has unnamed arguments
  UnnamedArgInPolyTyError   : Name -> SpecialisationError
  ||| Failed to get TypeInfo
  |||
  ||| Can occur either due to trying to specialise a non-type invocation
  ||| or due to not having the necessary TypeInfo in the NamesInfoInTypes instance
  MissingTypeInfoError      : Name -> SpecialisationError

%hint
export
showSE : Show SpecialisationError
showSE = %runElab derive

-------------------------------
--- SPECIALISATION SETTINGS ---
-------------------------------


public export
record SpecialisationParams where
  [noHints]
  constructor MkSpecParams
  eraseConNames : Bool

public export
%defaulthint
SpecialisationDefaults : SpecialisationParams
SpecialisationDefaults = MkSpecParams
  { eraseConNames = False
  }

public export
interface NamespaceProvider (0 m : Type -> Type) where
  constructor MkNSProvider
  provideNS : m Namespace

export
Monad m => MonadTrans t => NamespaceProvider m => NamespaceProvider (t m) where
  provideNS = lift provideNS

export
inNS : Monad m => Namespace -> NamespaceProvider m
inNS ns = MkNSProvider $ pure ns

export
%defaulthint
NoNS : Monad m => NamespaceProvider m
NoNS = inNS (MkNS [])

