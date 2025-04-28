module Deriving.DepTyCheck.Gen.Signature

import public Data.Fin
import public Data.List.Extra
import public Data.SortedMap
import public Data.SortedMap.Dependent
import public Data.SortedSet

import public Deriving.DepTyCheck.Util.Reflection

%default total

------------------------------------------------------------
--- Simplest `Gen` signature, user for internal requests ---
------------------------------------------------------------

public export
record GenSignature where
  constructor MkGenSignature
  targetType : TypeInfo
  {auto 0 targetTypeCorrect : AllTyArgsNamed targetType}
  givenParams : SortedSet $ Fin targetType.args.length

namespace GenSignature

  export
  characteristics : GenSignature -> (String, List Nat)
  characteristics $ MkGenSignature ty giv = (show ty.name, toNatList giv)

  export
  showGivens : GenSignature -> String
  showGivens sig = joinBy ", " $ do
    let uName : Arg -> Maybe UserName
        uName $ MkArg {name=Just $ UN un, _} = Just un
        uName _ = Nothing
    sig.givenParams.asList <&> \idx => maybe (show idx) (\n => "\{show idx}(\{show n})") $ uName $ index' sig.targetType.args idx

public export %inline
(.generatedParams) : (sig : GenSignature) -> SortedSet $ Fin sig.targetType.args.length
sig.generatedParams = fromList (allFins sig.targetType.args.length) `difference` sig.givenParams

export
SingleLogPosition GenSignature where logPosition sig = "\{logPosition sig.targetType}[\{showGivens sig}]"

public export
Eq GenSignature where (==) = (==) `on` characteristics

public export
Ord GenSignature where compare = comparing characteristics

-----------------------------------------------------
--- Data types for the safe signature formulation ---
-----------------------------------------------------

public export
data ArgExplicitness = ExplicitArg | ImplicitArg

public export
Eq ArgExplicitness where
  ExplicitArg == ExplicitArg = True
  ImplicitArg == ImplicitArg = True
  _ == _ = False

namespace ArgExplicitness

  public export
  (.toTT) : ArgExplicitness -> PiInfo a
  (.toTT) ExplicitArg = ExplicitArg
  (.toTT) ImplicitArg = ImplicitArg

------------------------------------------------------------------
--- Datatypes to describe signatures after checking user input ---
------------------------------------------------------------------

--- `Gen` signature containing info about params explicitness and their names ---

public export
record ExternalGenSignature where
  constructor MkExternalGenSignature
  targetType : TypeInfo
  {auto 0 targetTypeCorrect : AllTyArgsNamed targetType}
  givenParams : SortedMap (Fin targetType.args.length) (ArgExplicitness, Name)
  givensOrder : Vect givenParams.size $ Fin givenParams.size -- must be a permutation
  {gendParamsCnt : _}
  gendOrder   : Vect gendParamsCnt $ Fin gendParamsCnt -- must be a permutation

namespace ExternalGenSignature

  -- characterises external generator signatures ignoring particular order of given/generated arguments
  export
  characteristics : ExternalGenSignature -> (String, List Nat)
  characteristics $ MkExternalGenSignature ty giv _ _ = (show ty.name, toNatList $ keys giv)

-- Compares external generator signatures ignoring particular order of given/generated arguments
public export
Eq ExternalGenSignature where (==) = (==) `on` characteristics

-- Compares external generator signatures ignoring particular order of given/generated arguments
public export
Ord ExternalGenSignature where compare = comparing characteristics

export
internalise : (extSig : ExternalGenSignature) -> Subset GenSignature $ \sig => sig.givenParams.size = extSig.givenParams.size
internalise $ MkExternalGenSignature ty giv _ _ = Element (MkGenSignature ty $ keySet giv) $ keySetSize giv
