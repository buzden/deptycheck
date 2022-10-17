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

    -- generate claims for generators per constructors
    let consClaims = sig.targetType.cons <&> \con => export' (consGenName con) (canonicSig UnderMaybe sig)

    -- derive bodies for generators per constructors
    consBodies <- for sig.targetType.cons $ \con => logBounds "consBody" [sig, con] $
      canonicConsBody sig (consGenName con) con <&> def (consGenName con)

    -- calculate which constructors are recursive and which are not
    consRecs <- for sig.targetType.cons $ \con => logBounds "consRec" [sig, con] $ do
      let conExprs = map type con.args ++ (getExpr <$> snd (unAppAny con.type))
      r <- any (hasNameInsideDeep sig.targetType.name) conExprs
      pure (con, toRec r)

    -- decide how to name a fuel argument on the LHS
    let fuelArg = "^fuel_arg^" -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend

    -- generate the case expression deciding whether will we go into recursive constructors or not
    let outmostRHS = fuelDecisionExpr fuelArg consRecs

    -- return function definition
    pure [ canonicDefaultLHS sig n fuelArg .= local (consClaims ++ consBodies) outmostRHS ]

  where

    consGenName : Con -> Name
    consGenName con = UN $ Basic $ "<<\{show con.name}>>"
    -- I'm using `UN` but containing chars that cannot be present in the code parsed from the Idris frontend

    fuelDecisionExpr : (fuelArg : String) -> List (Con, Recursiveness) -> TTImp
    fuelDecisionExpr fuelAr consRecs = do

      -- check if there are any recursive constructors
      let True = isJust $ find ((== Recursive) . snd) consRecs
        | False =>
            -- no recursive constructors, thus just call all without spending fuel
            callOneOf UnderMaybe (consRecs <&> callConsGen (varStr fuelAr) . fst)

      -- pattern match on the fuel argument
      iCase .| varStr fuelAr .| var `{Data.Fuel.Fuel} .|

        [ -- if fuel is dry, call all non-recursive constructors on `Dry`
          let nonRecCons = fst <$> filter ((== NonRecursive) . snd) consRecs in
          let dry = var `{Data.Fuel.Dry} in dry       .= callOneOf UnderMaybe (nonRecCons <&> callConsGen dry)

        , do -- if fuel is `More`, spend one fuel and call all constructors on the rest
          let subFuelArg = "^sub" ++ fuelAr -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend
          let selectFuel : Recursiveness -> String
              selectFuel Recursive    = subFuelArg
              selectFuel NonRecursive = fuelAr
          var `{Data.Fuel.More} .$ bindVar subFuelArg .= callOneOf UnderMaybe (consRecs <&> \(con, rec) => callConsGen (varStr $ selectFuel rec) con)
        ]

      where

        callConsGen : (fuel : TTImp) -> Con -> TTImp
        callConsGen fuel con = canonicDefaultRHS sig .| consGenName con .| fuel

    toRec : Bool -> Recursiveness
    toRec True  = Recursive
    toRec False = NonRecursive

export
MainCoreDerivator : ConstructorDerivator => DerivatorCore
MainCoreDerivator = %search
