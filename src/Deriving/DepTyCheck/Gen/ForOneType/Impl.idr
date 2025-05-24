||| Main implementation of the derivator core interface
module Deriving.DepTyCheck.Gen.ForOneType.Impl

import public Data.Either

import public Deriving.DepTyCheck.Gen.Labels
import public Deriving.DepTyCheck.Gen.ForOneTypeCon.Impl
import public Deriving.DepTyCheck.Gen.ForOneType.Interface

%default total

------------------------------------
--- Expressions generation utils ---
------------------------------------

defArgNames : {sig : GenSignature} -> Vect sig.givenParams.size Name
defArgNames = sig.givenParams.asVect <&> argName . index' sig.targetType.args

export %inline
canonicDefaultLHS' : (namesFun : Name -> Name) -> GenSignature -> Name -> (fuel : Name) -> TTImp
canonicDefaultLHS' nmf sig n fuel = callCanonic sig n .| bindVar fuel .| bindVar . nmf <$> defArgNames

export %inline
canonicDefaultRHS' : (namesFun : Name -> Name) -> GenSignature -> Name -> (fuel : TTImp) -> TTImp
canonicDefaultRHS' nmf sig n fuel = callCanonic sig n fuel .| var . nmf <$> defArgNames

export %inline
canonicDefaultLHS : GenSignature -> Name -> (fuel : Name) -> TTImp
canonicDefaultLHS = canonicDefaultLHS' id

export %inline
canonicDefaultRHS : GenSignature -> Name -> (fuel : TTImp) -> TTImp
canonicDefaultRHS = canonicDefaultRHS' id

----------------------------
--- Derivation functions ---
----------------------------

export
DeriveBodyRhsForCon => DeriveBodyForType where
  canonicBody sig n = do

    -- check that there is at least one constructor
    Prelude.when .| null sig.targetType.cons .| fail "No constructors found for the type `\{show sig.targetType.name}`"

    -- check that desired `Gen` is not a generator of `Gen`s
    Prelude.when .| sig.targetType.name == `{Test.DepTyCheck.Gen.Gen} .| fail "Target type of a derived `Gen` cannot be a `Gen`"

    -- generate claims for generators per constructors
    let consClaims = sig.targetType.cons <&> \con => export' (consGenName con) (canonicSig sig)

    -- derive bodies for generators per constructors
    consBodies <- for sig.targetType.cons $ \con => logBounds {level=Info} "deptycheck.derive.consBody" [sig, con] $
      canonicConsBody sig (consGenName con) con <&> def (consGenName con)

    -- calculate which constructors are recursive and spend fuel, and which are not
    let Just consRecs = lookupConsWithWeight sig
      | Nothing => fail "INTERNAL ERROR: unknown type for consRecs: \{show sig.targetType.name}"

    -- ask to derive all needed weigthing functions, if any
    traverse_ needWeightFun $ mapMaybe (usedWeightFun . snd) consRecs

    -- decide how to name a fuel argument on the LHS
    let fuelArg = "^fuel_arg^" -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend

    -- generate the case expression deciding whether will we go into recursive constructors or not
    let outmostRHS = fuelDecisionExpr fuelArg $ map @{Compose} weightExpr consRecs

    -- return function definition
    pure [ canonicDefaultLHS' interimNamesWrapper sig n fuelArg .= local (consClaims ++ consBodies) outmostRHS ]

  where

    consGenName : Con -> Name
    consGenName con = UN $ Basic $ "<<\{show con.name}>>"
    -- I'm using `UN` but containing chars that cannot be present in the code parsed from the Idris frontend

    fuelDecisionExpr : (fuelArg : Name) -> List (Con, Either TTImp (Name -> TTImp)) -> TTImp
    fuelDecisionExpr fuelAr consRecs = do

      let callConstFreqs : CTLabel -> (fuel : TTImp) -> List (Con, TTImp) -> TTImp
          callConstFreqs l fuel cons = if isJust $ find (not . isWeight1 . snd) cons
            then callFrequency l $ cons <&> map (callConsGen fuel) . swap
            else callOneOf l $ cons <&> callConsGen fuel . fst

      -- check if there are any non-recursive constructors
      let Nothing = for consRecs $ \(con, w) => (con,) <$> getLeft w
          -- only constantly weighted constructors (usually, non-recusrive), thus just call all without spending fuel
        | Just consRecs => callConstFreqs "\{logPosition sig} (non-spending)".label (var fuelAr) consRecs

      -- pattern match on the fuel argument
      iCase .| var fuelAr .| var `{Data.Fuel.Fuel} .|

        [ -- if fuel is dry, call all non-recursive constructors on `Dry`
          let nonSpendCons = mapMaybe (\(con, w) => (con,) <$> getLeft w) consRecs in
          var `{Data.Fuel.Dry}                        .= callConstFreqs "\{logPosition sig} (dry fuel)".label (var fuelAr) nonSpendCons

        , do -- if fuel is `More`, call spending constructors on the rest and other on the original fuel
          -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend
          let subFuelArg = UN $ Basic $ "^sub" ++ show fuelAr
          let weightAndFuel = either ((var fuelAr,)) (\f => (var subFuelArg, f subFuelArg))
          var `{Data.Fuel.More} .$ bindVar subFuelArg .= callFrequency "\{logPosition sig} (non-dry fuel)".label
            (consRecs <&> \(con, rec) => let (f, w) = weightAndFuel rec in (w, callConsGen f con))
        ]

      where

        callConsGen : (fuel : TTImp) -> Con -> TTImp
        callConsGen fuel con = canonicDefaultRHS' interimNamesWrapper sig .| consGenName con .| fuel

export
MainCoreDerivator : DeriveBodyRhsForCon => DeriveBodyForType
MainCoreDerivator = %search
