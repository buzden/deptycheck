||| Main implementation of the derivator core interface
module Deriving.DepTyCheck.Gen.Core

import public Deriving.DepTyCheck.Gen.Core.ConsEntry
import public Deriving.DepTyCheck.Util.Reflection

%default total

-------------------------------
--- Tuning of probabilities ---
-------------------------------

public export
interface ProbabilityTuning (0 n : Name) where
  0 isConstructor : (con : IsConstructor n ** GenuineProof con)
  tuneWeight : Nat1 -> Nat1

-----------------------------------------
--- Utility functions and definitions ---
-----------------------------------------

--- Ancillary data structures ---

record ConWeightInfo where
  constructor MkConWeightInfo
  ||| Either constant (for non-recursive) or an expression (be a lambda taking the left fuel, or some other expression; for recursive)
  weight : Either Nat1 TTImp

%inline
recursive : ConWeightInfo -> Bool
recursive = isRight . weight

----------------------------
--- Derivation functions ---
----------------------------

-- This is a workaround of some bad and not yet understood behaviour, leading to both compile- and runtime errors
removeNamedApps, workaroundFromNat : TTImp -> TTImp
removeNamedApps = mapTTImp $ \case INamedApp _ lhs _ _ => lhs; e => e
workaroundFromNat = mapTTImp $ \e => case fst $ unAppAny e of IVar _ `{Data.Nat1.FromNat} => removeNamedApps e; _ => e

%ambiguity_depth 4

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

    -- calculate which constructors are recursive and which are not
    consRecs <- logBounds {level=Trace} "consRec" [sig] $ Prelude.for sig.targetType.cons $ \con => do
      let rec = isRecursive {containingType=Just sig.targetType} con
      tuneImpl <- search $ ProbabilityTuning $ Con.name con
      let baseForRec = \subFuelArg => var `{Deriving.DepTyCheck.Util.Reflection.leftDepth} .$ varStr subFuelArg
      let someStrangeName = "^some_strange_name^"
      w <- case rec of
        False => pure $ Left $ maybe one (\impl => tuneWeight @{impl} one) tuneImpl
        True  => Right <$> case tuneImpl of
          Nothing   => pure $ lam (lambdaArg $ UN $ Basic someStrangeName) $ baseForRec someStrangeName
          Just impl => quote (tuneWeight @{impl}) <&> \wm =>
            lam (lambdaArg $ UN $ Basic someStrangeName) $ workaroundFromNat $ wm `applySyn` baseForRec someStrangeName
      Prelude.pure (con, MkConWeightInfo w)

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

    fuelDecisionExpr : (fuelArg : String) -> List (Con, ConWeightInfo) -> TTImp
    fuelDecisionExpr fuelAr consRecs = do

      let reflectNat1 : Nat1 -> TTImp
          reflectNat1 $ FromNat 1 = liftWeight1
          reflectNat1 $ FromNat n = `(fromInteger ~(primVal $ BI $ cast n))

      let callConstFreqs : CTLabel -> (fuel : TTImp) -> List (Con, Nat1) -> TTImp
          callConstFreqs l fuel cons = if isJust $ find ((/=) 1 . toNat . snd) cons
            then callFrequency l $ cons <&> bimap reflectNat1 (callConsGen fuel) . swap
            else callOneOf l $ cons <&> callConsGen fuel . fst

      -- check if there are any non-recursive constructors
      let Nothing = for consRecs $ \(con, w) => (con,) <$> getLeft w.weight
          -- only constantly weighted constructors (usually, non-recusrive), thus just call all without spending fuel
        | Just consRecs => callConstFreqs "\{logPosition sig} (non-recursive)".label (varStr fuelAr) consRecs

      -- pattern match on the fuel argument
      iCase .| varStr fuelAr .| var `{Data.Fuel.Fuel} .|

        [ -- if fuel is dry, call all non-recursive constructors on `Dry`
          let nonRecCons = mapMaybe (\(con, w) => (con,) <$> getLeft w.weight) consRecs in
          let dry = var `{Data.Fuel.Dry} in dry       .= callConstFreqs "\{logPosition sig} (dry fuel)".label dry nonRecCons
                                                                       -- TODO to think why not `fuelAr` here ^^^ if we check non-rec here

        , do -- if fuel is `More`, spend one fuel and call all constructors on the rest
          let subFuelArg = "^sub" ++ fuelAr -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend
          let selectFuel = \r => varStr $ if recursive r then subFuelArg else fuelAr
          let weight = either reflectNat1 (`applySyn` varStr subFuelArg) . weight
          var `{Data.Fuel.More} .$ bindVar subFuelArg .= callFrequency "\{logPosition sig} (spend fuel)".label
                                                           (consRecs <&> \(con, rec) => (weight rec, callConsGen (selectFuel rec) con))
        ]

      where

        callConsGen : (fuel : TTImp) -> Con -> TTImp
        callConsGen fuel con = canonicDefaultRHS' namesWrapper sig .| consGenName con .| fuel

export
MainCoreDerivator : ConstructorDerivator => DerivatorCore
MainCoreDerivator = %search
