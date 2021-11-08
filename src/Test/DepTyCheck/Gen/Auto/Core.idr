||| Main implementation of the derivator core interface
module Test.DepTyCheck.Gen.Auto.Core

import public Language.Reflection.Syntax
import public Language.Reflection.Types

import public Test.DepTyCheck.Gen.Auto.Core.Cons
import public Test.DepTyCheck.Gen.Auto.Util.Reflection.Syntactic

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

    -- generate claims for generators per constructors
    let consClaims = sig.targetType.cons <&> \con => export' (consGenName con) (canonicSig sig)

    -- derive bodies for generators per constructors
    consBodies <- for sig.targetType.cons $ \con => canonicConsBody sig (consGenName con) con <&> def (consGenName con)

    -- calculate which constructors are recursive and which are not
    consRecs <- for sig.targetType.cons $ \con => consRecursiveness con <&> (con,)

    -- decide how to name a fuel argument on the LHS
    let fuelArg = "fuel_arg_86"

    -- generate the case expression deciding whether will we go into recursive constructors or not
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
        callConsGen fuel con = canonicDefaultRHS sig .| consGenName con .| fuel

    consRecursiveness : Con -> m Recursiveness
    consRecursiveness con = map toRec $ any (hasNameInsideDeep sig.targetType.name) $ map type con.args ++ snd (unApp con.type) where

      toRec : Bool -> Recursiveness
      toRec True  = Recursive
      toRec False = NonRecursive

      any : (a -> m Bool) -> List a -> m Bool
      any = foldl (||) (pure False) .: map

export
MainCoreDerivator : ConstructorDerivator => DerivatorCore
MainCoreDerivator = %search
