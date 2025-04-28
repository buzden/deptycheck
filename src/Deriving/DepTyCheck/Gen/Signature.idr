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

public export %inline
(.generatedParams) : (sig : GenSignature) -> SortedSet $ Fin sig.targetType.args.length
sig.generatedParams = fromList (allFins sig.targetType.args.length) `difference` sig.givenParams

export
showGivens : GenSignature -> String
showGivens sig = joinBy ", " $ do
  let uName : Arg -> Maybe UserName
      uName $ MkArg {name=Just $ UN un, _} = Just un
      uName _ = Nothing
  sig.givenParams.asList <&> \idx => maybe (show idx) (\n => "\{show idx}(\{show n})") $ uName $ index' sig.targetType.args idx

export
SingleLogPosition GenSignature where logPosition sig = "\{logPosition sig.targetType}[\{showGivens sig}]"

public export
Eq GenSignature where (==) = (==) `on` characteristics

public export
Ord GenSignature where compare = comparing characteristics


