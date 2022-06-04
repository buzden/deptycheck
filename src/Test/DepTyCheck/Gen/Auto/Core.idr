||| Main implementation of the derivator core interface
module Test.DepTyCheck.Gen.Auto.Core

import public Language.Reflection.Syntax
import public Language.Reflection.Types

import public Test.DepTyCheck.Gen.Auto.Core.ConsEntry
import public Test.DepTyCheck.Gen.Auto.Util.Reflection

%default total

-----------------------------------------
--- Utility functions and definitions ---
-----------------------------------------

--- Ancillary data structures ---

data Recursiveness = Recursive | NonRecursive

Eq Recursiveness where
  Recursive    == Recursive    = True
  NonRecursive == NonRecursive = True
  Recursive    == NonRecursive = False
  NonRecursive == Recursive    = False

----------------------------
--- Derivation functions ---
----------------------------

export
ConstructorDerivator => DerivatorCore where
  canonicBody sig n = do

    -- check that there is at least one constructor
    when .| null sig.targetType.cons .| fail "No constructors found for the type `\{show sig.targetType.name}`"

    -- check that desired `Gen` is not a generator of `Gen`s
    when .| sig.targetType.name == `{Test.DepTyCheck.Gen.Gen} .| fail "Target type of a derived `Gen` cannot be a `Gen`"

    -- derive bodies, generate claims and acquire additional gens for generators per constructors
    (consAdditions, consClaims, consBodies) <- map unzip3 $ for sig.targetType.cons $ \con => do
      let consName = consGenName con
      (bodyClauses, additionalGens) <- canonicConsBody sig consName con
      pure (additionalGens, export' consName $ canonicSig sig additionalGens, def consName bodyClauses)

    -- compute composite additional gens value fir the whole generator
    let additionalGens = concat consAdditions

    -- calculate which constructors are recursive and which are not
    consRecs <- for (sig.targetType.cons `zip` consAdditions) $ \(con, adds) => consRecursiveness con <&> ((con, adds),)

    -- decide how to name a fuel argument on the LHS
    let fuelArg = "^fuel_arg^" -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend

    -- generate the case expression deciding whether will we go into recursive constructors or not
    let outmostRHS = fuelDecisionExpr fuelArg consRecs

    -- return function definition
    pure $ (, additionalGens) [
      wrapAdditionalGensLHS additionalGens (canonicDefaultLHS sig n fuelArg) .= local (consClaims ++ consBodies) outmostRHS
    ]

  where

    consGenName : Con -> Name
    consGenName con = UN $ Basic $ "<<\{show con.name}>>"
    -- I'm using `UN` but containing chars that cannot be present in the code parsed from the Idris frontend

    fuelDecisionExpr : (fuelArg : String) -> List ((Con, AdditionalGens), Recursiveness) -> TTImp
    fuelDecisionExpr fuelAr consRecs = do

      -- find out non-recursive constructors
      let nonRecCons = fst <$> filter ((== NonRecursive) . snd) consRecs

      -- acquire all constructors
      let allCons = fst <$> consRecs

      -- pattern match on the fuel argument
      iCase .| varStr fuelAr .| var `{Data.Fuel.Fuel} .|

        [ -- if fuel is dry, call all non-recursive constructors on `Dry`
          let dry = var `{Data.Fuel.Dry} in dry       .= callOneOf (nonRecCons <&> callConsGen dry)

        , -- if fuel is `More`, spend one fuel and call all constructors on the rest
          let subFuelArg = "^sub" ++ fuelAr in -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend
          var `{Data.Fuel.More} .$ bindVar subFuelArg .= callOneOf (allCons <&> callConsGen (varStr subFuelArg))
        ]

      where

        callConsGen : (fuel : TTImp) -> (Con, AdditionalGens) -> TTImp
        callConsGen fuel (con, adds) = wrapAdditionalGensRHS adds $ canonicDefaultRHS sig .| consGenName con .| fuel

    consRecursiveness : Con -> m Recursiveness
    consRecursiveness con = map toRec $ any (hasNameInsideDeep sig.targetType.name) $ map type con.args ++ (getExpr <$> snd (unAppAny con.type)) where

      toRec : Bool -> Recursiveness
      toRec True  = Recursive
      toRec False = NonRecursive

      any : (a -> m Bool) -> List a -> m Bool
      any = foldl (||) (pure False) .: map

export
MainCoreDerivator : ConstructorDerivator => DerivatorCore
MainCoreDerivator = %search
