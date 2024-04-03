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
  ||| When constructor itself does not refer to the type it belongs,
  ||| but its generated index either
  ||| - refers to some constructor that is recursive, or
  ||| - is general enough to be able to refer so some recursive constructor
  IndexedByRecursive |
  ||| When constructor does not refer to the type it belongs,
  ||| nor to any recursive constructor in its generated indices
  NonRecursive

||| Checks if the status is anyhow recursive, directly or through index
isRec : Recursiveness -> Bool
isRec DirectlyRecursive  = True
isRec IndexedByRecursive = True
isRec NonRecursive       = False

||| Check if we are able to call for this constructor on a dry fuel
isDirectlyRec : Recursiveness -> Bool
isDirectlyRec DirectlyRecursive  = True
isDirectlyRec IndexedByRecursive = False
isDirectlyRec NonRecursive       = False

||| Property is implication from the strong property to the weak one
0 recStrengthProp : So (isDirectlyRec r) -> So (isRec r)
recStrengthProp {r=DirectlyRecursive} Oh = Oh

----------------------------
--- Derivation functions ---
----------------------------

[Short] Show TTImp where
  show expr = do
    let (l, rs) = unAppAny expr
    "\{l}\{concatMap (const " (...)") rs}"

printMatrix : Foldable f => Foldable t => Elaboration m => (desc : String) -> f (t TTImp) -> m ()
printMatrix desc xxs = do
  logMsg "debug" 0 desc
  for_ xxs $ \xs => do
    logMsg "debug" 0 "- \{joinBy ", " $ map (show @{Short}) $ toList xs}"

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

    -- prepare information about generated type arguments by constructors
    genConParams <- either (uncurry failAt) pure $ for sig.targetType.cons.asVect $ \con => do
      let conParams = snd $ unAppAny con.type
      let Yes lengthCorrect = decEq conParams.length sig.targetType.args.length
        | No _ => Left (getFC con.type, "INTERNAL ERROR: wrong count of unapp of constructor \{show con.name}")
      let genConParams = sig.generatedParams.asVect <&> \gv => getExpr $ index' conParams $ rewrite lengthCorrect in gv
      Right genConParams
    -- clean up prefixes of potential indices, we kinda depend here on fact that constructor expressions are already normalised
    printMatrix "before" genConParams
    let genConParams = transpose . map (cutAppPrefix {n=sig.targetType.cons.length}) . transpose $ genConParams
    printMatrix "after" genConParams

    -- calculate which constructors are recursive and which are not
    consRecs <- logBounds "consRec" [sig] $ for (sig.targetType.cons `zipV` genConParams) $ \(con, genConIdxs) => do
      let False = isRecursive {containingType=Just sig.targetType} con
        | True => pure (con, DirectlyRecursive)
      -- this constructor is not directly recursive, check if any of generated indices are indexed by a recursive constructor
      let conArgNames = fromList $ name <$> con.args
      let namesInGivenConParams = concatMap allVarNames' genConIdxs
      logMsg "debug" 0 "\{show con.name}: names in givens: \{show namesInGivenConParams.asList}"
      let externalNamesInGivenConParams = SortedSet.toList $ namesInGivenConParams `difference` conArgNames
      logMsg "debug" 0 "\{show con.name}: extrnal names in givens: \{show externalNamesInGivenConParams}"
      -- now we want to check if external names can refer to non-constructors and/or recursive constructors;
      -- if yes, then this constructor is potentially indexed by recursive something
      let rec = if any ((/= Just False) . isRecursiveConstructor) externalNamesInGivenConParams then IndexedByRecursive else NonRecursive
      pure (con, rec)

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
          let nonRecCons = fst <$> filter (not . isDirectlyRec . snd) consRecs in
          let dry = var `{Data.Fuel.Dry} in dry       .= callOneOf "\{logPosition sig} (dry fuel)".label (nonRecCons <&> callConsGen dry)

        , do -- if fuel is `More`, spend one fuel and call all constructors on the rest
          let subFuelArg = "^sub" ++ fuelAr -- I'm using a name containing chars that cannot be present in the code parsed from the Idris frontend
          let selectFuel = \r => varStr $ if isDirectlyRec r then subFuelArg else fuelAr
          let weight = \r => if isRec r then var `{Deriving.DepTyCheck.Util.Reflection.leftDepth} .$ varStr subFuelArg else liftWeight1
          var `{Data.Fuel.More} .$ bindVar subFuelArg .= callFrequency "\{logPosition sig} (spend fuel)".label
                                                           (consRecs <&> \(con, rec) => (weight rec, callConsGen (selectFuel rec) con))
        ]

      where

        callConsGen : (fuel : TTImp) -> Con -> TTImp
        callConsGen fuel con = canonicDefaultRHS' namesWrapper sig .| consGenName con .| fuel

export
MainCoreDerivator : ConstructorDerivator => DerivatorCore
MainCoreDerivator = %search
