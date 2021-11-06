||| Main implementation of the derivator core interface
module Test.DepTyCheck.Gen.Auto.Core

import public Language.Reflection.Syntax
import public Language.Reflection.Types

import public Test.DepTyCheck.Gen.Auto.Derive
import public Test.DepTyCheck.Gen.Auto.Util.Reflection.Syntactic

%default total

-----------------------------------------
--- Utility functions and definitions ---
-----------------------------------------

--- Expressions generation utils ---

defArgNames : {sig : GenSignature} -> Vect sig.givenParams.asList.length String
defArgNames = sig.givenParams.asVect <&> show . name . index' sig.targetType.args

%inline
canonicDefault : (String -> TTImp) -> GenSignature -> Name -> (fuel : String) -> TTImp
canonicDefault varF sig n fuel = callCanonic sig n .| varF fuel .| varF <$> defArgNames

export %inline
canonicDefaultLHS : GenSignature -> Name -> (fuel : String) -> TTImp
canonicDefaultLHS = canonicDefault bindVar

export %inline
canonicDefaultRHS : GenSignature -> Name -> (fuel : String) -> TTImp
canonicDefaultRHS = canonicDefault varStr

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

public export
interface ConstructorDerivator where
  canonicConsBody : CanonicGen m => GenSignature -> Name -> Con -> m $ List Clause

export
ConstructorDerivator => DerivatorCore where
  canonicBody sig n = do

    -- check that there is at least one constructor
    when .| null sig.targetType.cons .| fail "No constructors found for the type `\{show sig.targetType.name}`"

    -- generate claims for generators per constructors
    let consClaims = sig.targetType.cons <&> \con => export' (consGenName con) (canonicSig sig)

    -- derive bodies for generators per constructors
    consBodies <- for sig.targetType.cons $ \con => canonicConsBody sig (consGenName con) con <&> def (consGenName con)

    -- calculate which constructors are recursive and which are not
    let consRecs = sig.targetType.cons <&> \con => (con,) $ consRecursiveness con

    -- decide how to name a fuel argument on the LHS
    let fuelArg = "fuel_arg_86"

    -- generate the case expression decising where will we go into recursive constructors or not
    let outmostRHS = fuelDecisionExpr fuelArg consRecs

    -- return function definition
    pure [ canonicDefaultLHS sig n fuelArg .= local (consClaims ++ consBodies) outmostRHS ]

  where

    consGenName : Con -> Name
    consGenName con = MN "cons_gen_for_\{show con.name}" 7

    fuelDecisionExpr : (fuelArg : String) -> List (Con, Recursiveness) -> TTImp
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
          let subFuelArg = "sub_" ++ fuelAr in
          var `{Data.Fuel.More} .$ bindVar subFuelArg .= callOneOf (allCons <&> callConsGen (varStr subFuelArg))
        ]

      where

        callConsGen : (fuel : TTImp) -> Con -> TTImp
        callConsGen fuel con = callCanonic sig .| consGenName con .| fuel .| varStr <$> defArgNames

        callOneOf : List TTImp -> TTImp
        callOneOf variants = var `{Test.DepTyCheck.Gen.oneOf'} .$ liftList variants

    consRecursiveness : Con -> Recursiveness
    consRecursiveness con =
      if any (hasIVarInside sig.targetType.name) $ map type con.args ++ snd (unApp con.type)
      then Recursive
      else NonRecursive

export
MainCoreDerivator : ConstructorDerivator => DerivatorCore
MainCoreDerivator = %search
