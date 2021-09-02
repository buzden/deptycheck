module CanonicSigCheck

import public Debug.Reflection

import public Test.DepTyCheck.Gen
import public Test.DepTyCheck.Gen.Auto.Checked

import public Language.Reflection.Types

%default total

%language ElabReflection

Eq TTImp where
  (==) = (==) `on` show

%inline
TestCaseData : Type
TestCaseData = (TTImp, Type)

%inline
TestCaseDesc : Type
TestCaseDesc = (String, TestCaseData)

chk : (ty : TypeInfo) -> List (Fin ty.args.length, ArgExplicitness) -> Type -> TestCaseData
chk ty giv expr = (canonicSig (MkGenSignature ty $ fromList giv), expr)

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

            , ("1st given expl",) $ chk YInfo [(0, ExplicitArg)] $ (n : Nat) -> Gen (a : Type ** Y n a)
            , ("1st given impl",) $ chk YInfo [(0, ImplicitArg)] $ {n : Nat} -> Gen (a : Type ** Y n a)
            , ("2nd given expl",) $ chk YInfo [(1, ExplicitArg)] $ (a : Type) -> Gen (n : Nat ** Y n a)
            , ("2nd given impl",) $ chk YInfo [(1, ImplicitArg)] $ {a : Type} -> Gen (n : Nat ** Y n a)

            , ("both given, expl+expl",) $ chk YInfo [(1, ExplicitArg), (0, ExplicitArg)] $ (n : Nat) -> (a : Type) -> Gen (Y n a)
            , ("both given, expl+impl",) $ chk YInfo [(1, ImplicitArg), (0, ExplicitArg)] $ (n : Nat) -> {a : Type} -> Gen (Y n a)
            , ("both given, impl+expl",) $ chk YInfo [(1, ExplicitArg), (0, ImplicitArg)] $ {n : Nat} -> (a : Type) -> Gen (Y n a)
            , ("both given, impl+impl",) $ chk YInfo [(1, ImplicitArg), (0, ImplicitArg)] $ {n : Nat} -> {a : Type} -> Gen (Y n a)
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

            , ("1st given expl",) $ chk YInfo [(0, ExplicitArg)] $ (n : Nat) -> Gen (a : Type ** Y {n} a)
            , ("1st given impl",) $ chk YInfo [(0, ImplicitArg)] $ {n : Nat} -> Gen (a : Type ** Y {n} a)
            , ("2nd given expl",) $ chk YInfo [(1, ExplicitArg)] $ (a : Type) -> Gen (n : Nat ** Y {n} a)
            , ("2nd given impl",) $ chk YInfo [(1, ImplicitArg)] $ {a : Type} -> Gen (n : Nat ** Y {n} a)

            , ("both given, expl+expl",)  $ chk YInfo [(1, ExplicitArg), (0, ExplicitArg)] $ (n : Nat) -> (a : Type) -> Gen (Y {n} a)
            , ("both given, expl+impl",)  $ chk YInfo [(1, ImplicitArg), (0, ExplicitArg)] $ (n : Nat) -> {a : Type} -> Gen (Y {n} a)
            , ("both given, impl+expl",)  $ chk YInfo [(1, ExplicitArg), (0, ImplicitArg)] $ {n : Nat} -> (a : Type) -> Gen (Y {n} a)
            , ("both given, impl+impl",)  $ chk YInfo [(1, ImplicitArg), (0, ImplicitArg)] $ {n : Nat} -> {a : Type} -> Gen (Y {n} a)
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

            , ("impl `a` given as expl",)  $ chk YInfo [(0, ExplicitArg)] $ (a : Type) -> Gen (n : Nat ** v : Vect n a ** Y n v)
            , ("impl `a` given as impl",)  $ chk YInfo [(0, ImplicitArg)] $ {a : Type} -> Gen (n : Nat ** v : Vect n a ** Y n v)

            , ("expl `n` given as expl",) $ chk YInfo [(1, ExplicitArg)] $ (n : Nat) -> Gen (a : Type ** v : Vect n a ** Y n v)
            , ("expl `n` given as impl",) $ chk YInfo [(1, ImplicitArg)] $ {n : Nat} -> Gen (a : Type ** v : Vect n a ** Y n v)

            , ("`a` and `n` given, expl+expl",) $ chk YInfo [(0, ExplicitArg), (1, ExplicitArg)]
                                                $ (a : Type) -> (n : Nat) -> Gen (v : Vect n a ** Y n v)
            , ("`a` and `n` given, impl+expl",) $ chk YInfo [(0, ImplicitArg), (1, ExplicitArg)]
                                                $ {a : Type} -> (n : Nat) -> Gen (v : Vect n a ** Y n v)
            , ("`a` and `n` given, expl+impl",) $ chk YInfo [(0, ExplicitArg), (1, ImplicitArg)]
                                                $ (a : Type) -> {n : Nat} -> Gen (v : Vect n a ** Y n v)
            , ("`a` and `n` given, impl+impl",) $ chk YInfo [(0, ImplicitArg), (1, ImplicitArg)]
                                                $ {a : Type} -> {n : Nat} -> Gen (v : Vect n a ** Y n v)

            , ("all given, expl+expl+expl",) $ chk YInfo [(0, ExplicitArg), (1, ExplicitArg), (2, ExplicitArg)]
                                             $ (a : Type) -> (n : Nat) -> (v : Vect n a) -> Gen (Y n v)
            , ("all given, impl+expl+expl",) $ chk YInfo [(0, ImplicitArg), (1, ExplicitArg), (2, ExplicitArg)]
                                             $ {a : Type} -> (n : Nat) -> (v : Vect n a) -> Gen (Y n v)
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

main : Elab ()
main =
  traverse_ .| logCheck <=< pr .| with Prelude.(::) foldMap Lazy.fromList
    [ Trivial.check
    , NonDepExplParams_AllNamed.check
    , NonDepMixedParams_AllNamed.check
    , DepParams_AllNamed.check
    ]

%runElab main
