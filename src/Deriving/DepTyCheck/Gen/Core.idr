||| Main implementation of the derivator core interface
module Deriving.DepTyCheck.Gen.Core

import public Deriving.DepTyCheck.Gen.Core.ConsEntry
import public Deriving.DepTyCheck.Util.Reflection

%default total

%hide Text.PrettyPrint.Bernardy.Core.Doc.(>>=)

----------------------------
--- Derivation functions ---
----------------------------

export
ConstructorDerivator => DerivatorCore where
  canonicBody sig n = do

    -- check that there is at least one constructor
    Prelude.when .| null sig.targetType.cons .| fail "No constructors found for the type `\{show sig.targetType.name}`"

    -- check that desired `Gen` is not a generator of `Gen`s
    Prelude.when .| sig.targetType.name == `{Test.DepTyCheck.Gen.Gen} .| fail "Target type of a derived `Gen` cannot be a `Gen`"

    -- generate claims for generators per constructors
    let consClaims = sig.targetType.cons <&> \con => export' (consGenName con) (canonicSig sig)

    -- derive bodies for generators per constructors
    consBodies <- for sig.targetType.cons $ \con => logBounds {level=Info} "consBody" [sig, con] $
      canonicConsBody sig (consGenName con) con <&> def (consGenName con)

    -- calculate which constructors are recursive and spend fuel, and which are not
    let Just consRecs = lookupConsWithWeight sig.targetType
      | Nothing => fail "INTERNAL ERROR: unknown type for consRecs: \{show sig.targetType.name}"
    let givens = mapIn finToNat sig.givenParams
    let consRecs = map @{Compose} (weightExpr . (`apply` givens)) consRecs

    -- decide how to name a fuel argument on the LHS
    let fuelArg = "^fuel_arg^" -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend

    -- generate the case expression deciding whether will we go into recursive constructors or not
    outmostRHS <- fuelDecisionExpr fuelArg consRecs

    -- return function definition
    pure [ canonicDefaultLHS' namesWrapper sig n fuelArg .= local (consClaims ++ consBodies) outmostRHS ]

  where

    consGenName : Con -> Name
    consGenName con = UN $ Basic $ "<<\{show con.name}>>"
    -- I'm using `UN` but containing chars that cannot be present in the code parsed from the Idris frontend

    -- this is a workarond for Idris compiler bug #2983
    namesWrapper : String -> String
    namesWrapper s = "inter^<\{s}>"

    fuelDecisionExpr : (fuelArg : String) -> List (Con, Either TTImp (String -> TTImp)) -> m TTImp
    fuelDecisionExpr fuelAr consRecs = do

      let callConstFreqs : CTLabel -> (fuel : TTImp) -> List (Con, TTImp) -> TTImp
          callConstFreqs l fuel cons = if isJust $ find (((/=) liftWeight1) . snd) cons
            then callFrequency l $ cons <&> map (callConsGen fuel) . swap
            else callOneOf l $ cons <&> callConsGen fuel . fst

      -- check if there are any non-recursive constructors
      let Nothing = for consRecs $ \(con, w) => (con,) <$> getLeft w
          -- only constantly weighted constructors (usually, non-recusrive), thus just call all without spending fuel
        | Just consRecs => pure $ callConstFreqs "\{logPosition sig} (non-spending)".label (varStr fuelAr) consRecs

      -- pattern match on the fuel argument
      map (iCase .| varStr fuelAr .| var `{Data.Fuel.Fuel}) $ Prelude.sequence $

        [ -- if fuel is dry, call all non-recursive constructors on `Dry`
          let nonSpendCons = mapMaybe (\(con, w) => (con,) <$> getLeft w) consRecs in
          pure $ var `{Data.Fuel.Dry}                        .= callConstFreqs "\{logPosition sig} (dry fuel)".label (varStr fuelAr) nonSpendCons

        , do -- if fuel is `More`, call spending constructors on the rest and other on the original fuel
          let subFuelArg = "^sub" ++ fuelAr -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend
          let weightAndFuel = either ((varStr fuelAr,)) (\f => (varStr subFuelArg, f subFuelArg))
          pure $ var `{Data.Fuel.More} .$ bindVar subFuelArg .= callFrequency "\{logPosition sig} (non-dry fuel)".label
            (consRecs <&> \(con, rec) => let (f, w) = weightAndFuel rec in (w, callConsGen f con))
        ]

      where

        callConsGen : (fuel : TTImp) -> Con -> TTImp
        callConsGen fuel con = canonicDefaultRHS' namesWrapper sig .| consGenName con .| fuel

export
MainCoreDerivator : ConstructorDerivator => DerivatorCore
MainCoreDerivator = %search
