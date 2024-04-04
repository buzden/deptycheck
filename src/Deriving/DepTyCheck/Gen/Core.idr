||| Main implementation of the derivator core interface
module Deriving.DepTyCheck.Gen.Core

import public Deriving.DepTyCheck.Gen.Core.ConsEntry
import public Deriving.DepTyCheck.Util.Reflection

import public Language.Reflection.Syntax
import public Language.Reflection.Types

%default total

-----------------------------------------
--- Utility functions and definitions ---
-----------------------------------------

--- Ancillary data structures ---

data Recursiveness =
  ||| When constructor refers transitively to the type it belongs
  DirectlyRecursive |
  ||| When constructor does not refer to the type it belongs,
  ||| nor to any recursive constructor in its generated indices
  NonRecursive

||| Checks if the status is anyhow recursive, directly or through index
isRec : Recursiveness -> Bool
isRec DirectlyRecursive  = True
isRec NonRecursive       = False

||| Check if we are able to call for this constructor on a dry fuel
notDirectlyRec : Recursiveness -> Bool
notDirectlyRec NonRecursive       = True
notDirectlyRec DirectlyRecursive  = False

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
    let consClaims = sig.targetType.cons <&> \con => export' (consGenName con) (canonicSig sig)

    -- derive bodies for generators per constructors
    consBodies <- for sig.targetType.cons $ \con => logBounds "consBody" [sig, con] $
      canonicConsBody sig (consGenName con) con <&> def (consGenName con)

    -- calculate which constructors are recursive and which are not
    consRecs <- logBounds "consRec" [sig] $ pure $ sig.targetType.cons <&> \con => do
      let conExprs = map type con.args ++ (getExpr <$> snd (unAppAny con.type))
      let False = any (hasNameInsideDeep sig.targetType.name) conExprs
        | True => (con, DirectlyRecursive)
      (con, NonRecursive)

    -- decide how to name a fuel argument on the LHS
    let fuelArg = "^fuel_arg^" -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend

    -- generate the case expression deciding whether will we go into recursive constructors or not
    let outmostRHS = fuelDecisionExpr fuelArg consRecs

    -- return function definition
    pure [ canonicDefaultLHS' namesWrapper sig n fuelArg .= local (consClaims ++ consBodies) outmostRHS ]

  where

    consGenName : Con -> Name
    consGenName con = UN $ Basic $ "<<\{show con.name}>>"
    -- I'm using `UN` but containing chars that cannot be present in the code parsed from the Idris frontend

    -- this is a workarond for Idris compiler bug #2983
    namesWrapper : String -> String
    namesWrapper s = "inter^<\{s}>"

    fuelDecisionExpr : (fuelArg : String) -> List (Con, Recursiveness) -> TTImp
    fuelDecisionExpr fuelAr consRecs = do

      -- check if there are any non-recursive constructors
      let True = isJust $ find (isRec . snd) consRecs
        | False =>
            -- no recursive constructors, thus just call all without spending fuel
            callOneOf "\{logPosition sig} (non-recursive)".label (consRecs <&> callConsGen (varStr fuelAr) . fst)

      -- pattern match on the fuel argument
      iCase .| varStr fuelAr .| var `{Data.Fuel.Fuel} .|

        [ -- if fuel is dry, call all non-recursive constructors on `Dry`
          let nonRecCons = fst <$> filter (notDirectlyRec . snd) consRecs in
          let dry = var `{Data.Fuel.Dry} in dry       .= callOneOf "\{logPosition sig} (dry fuel)".label (nonRecCons <&> callConsGen dry)

        , do -- if fuel is `More`, spend one fuel and call all constructors on the rest
          let subFuelArg = "^sub" ++ fuelAr -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend
          let selectFuel : Recursiveness -> String
              selectFuel DirectlyRecursive  = subFuelArg
              selectFuel NonRecursive       = fuelAr
          let leftDepthExpr : ?; leftDepthExpr = var `{Deriving.DepTyCheck.Util.Reflection.leftDepth} .$ varStr subFuelArg
          let weight : Recursiveness -> TTImp
              weight DirectlyRecursive  = leftDepthExpr
              weight NonRecursive       = liftWeight1
          var `{Data.Fuel.More} .$ bindVar subFuelArg .= callFrequency "\{logPosition sig} (spend fuel)".label
                                                           (consRecs <&> \(con, rec) => (weight rec, callConsGen (varStr $ selectFuel rec) con))
        ]

      where

        callConsGen : (fuel : TTImp) -> Con -> TTImp
        callConsGen fuel con = canonicDefaultRHS' namesWrapper sig .| consGenName con .| fuel

export
MainCoreDerivator : ConstructorDerivator => DerivatorCore
MainCoreDerivator = %search
