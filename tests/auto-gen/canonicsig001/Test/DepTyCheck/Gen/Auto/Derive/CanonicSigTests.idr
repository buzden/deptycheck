module Test.DepTyCheck.Gen.Auto.Derive.CanonicSigTests

import public Data.Fuel

import public Debug.Reflection

import public Test.DepTyCheck.Gen
import public Test.DepTyCheck.Gen.Auto.Checked

import public Language.Reflection.Types

%default total

%language ElabReflection

Eq TTImp where
  -- The following is a non-complete trick, dealing with the fact that unnamed arguments are named after compler's check for being `Type`
  -- It works only for the top-level `Pi` type and only when `Pi` type is on the top level.
  IPi _ MW ExplicitArg Nothing argTy retTy == IPi _ MW ExplicitArg (Just $ MN _ _) argTy' retTy' = argTy == argTy' && retTy == retTy'
  x == y = show x == show y

%inline
TestCaseData : Type
TestCaseData = (TTImp, Type)

%inline
TestCaseDesc : Type
TestCaseDesc = (String, TestCaseData)

chk : (ty : TypeInfo) -> List (Fin ty.args.length) -> Type -> TestCaseData
chk ty giv expr = (canonicSig (MkGenSignature ty $ fromList giv), Fuel -> expr)

namespace Trivial

  data Y = Y0 | Y1

  export
  check : List TestCaseDesc
  check = [ ("trivial type; no givens",) $ chk (getInfo "Y") [] $ Gen Y
          ]

namespace NonDepExplParams_AllNamed

  data Y : (n : Nat) -> (a : Type) -> Type where
    Y0 : Y 0 Int
    Y1 : Y 1 Nat

  YInfo : TypeInfo
  YInfo = getInfo `{Y}

  export
  check : List TestCaseDesc
  check = mapFst ("non-dependent type + expl params; all named; " ++) <$>
            [ ("no givens",) $ chk YInfo [] $ Gen (n : Nat ** a : Type ** Y n a)

            , ("1st given",) $ chk YInfo [0] $ (n : Nat) -> Gen (a : Type ** Y n a)
            , ("2nd given",) $ chk YInfo [1] $ (a : Type) -> Gen (n : Nat ** Y n a)

            , ("both given",) $ chk YInfo [1, 0] $ (n : Nat) -> (a : Type) -> Gen (Y n a)
            ]

namespace NonDepMixedParams_AllNamed

  data Y : {n : Nat} -> (a : Type) -> Type where
    Y0 : Y {n=0} Int
    Y1 : Y {n=1} Nat

  YInfo : TypeInfo
  YInfo = getInfo `{Y}

  export
  check : List TestCaseDesc
  check = mapFst ("non-dependent type + mixed explicitness; all named; " ++) <$>
            [ ("no givens",) $ chk YInfo [] $ Gen (n : Nat ** a : Type ** Y {n} a)

            , ("1st given",) $ chk YInfo [0] $ (n : Nat) -> Gen (a : Type ** Y {n} a)
            , ("2nd given",) $ chk YInfo [1] $ (a : Type) -> Gen (n : Nat ** Y {n} a)

            , ("both given",)  $ chk YInfo [1, 0] $ (n : Nat) -> (a : Type) -> Gen (Y {n} a)
            ]

namespace DepParams_AllNamed

  data Y : (n : Nat) -> (v : Vect n a) -> Type where
    Y0 : Y 0 []
    Y1 : (x : a) -> Y 1 [x]

  YInfo : TypeInfo
  YInfo = getInfo `{Y}

  export
  check : List TestCaseDesc
  check = mapFst ("dependent type + mixed explicitness; all named; " ++) <$>
            [ ("no givens",)  $ chk YInfo [] $ Gen (a : Type ** n : Nat ** v : Vect n a ** Y {a} n v)
            , ("no givens'",) $ chk YInfo [] $ Gen (a : Type ** n : Nat ** v : Vect n a ** Y n v)

            , ("impl `a` given",) $ chk YInfo [0] $ (a : Type) -> Gen (n : Nat ** v : Vect n a ** Y n v)
            , ("expl `n` given",) $ chk YInfo [1] $ (n : Nat) -> Gen (a : Type ** v : Vect n a ** Y n v)

            , ("`a` and `n` given",) $ chk YInfo [0, 1] $ (a : Type) -> (n : Nat) -> Gen (v : Vect n a ** Y n v)

            , ("all given",) $ chk YInfo [0, 1, 2] $ (a : Type) -> (n : Nat) -> (v : Vect n a) -> Gen (Y n v)
            ]

pr : TestCaseDesc -> Elab String
pr (desc, given, expected) = do
  expected <- quote expected
  pure $ if given == expected
    then "\{desc}:\tOKAY"
    else """
         \{desc}:\tFAILED
           - given: \{show given}
           - expected: \{show expected}
         """

logCheck : String -> Elab ()
logCheck = \s => logMsg "gen.auto.canonic.check-sig" 0 s

public export
main : Elab ()
main =
  traverse_ .| logCheck <=< pr .| with Prelude.(::) foldMap Lazy.fromList
    [ Trivial.check
    , NonDepExplParams_AllNamed.check
    , NonDepMixedParams_AllNamed.check
    , DepParams_AllNamed.check
    ]
