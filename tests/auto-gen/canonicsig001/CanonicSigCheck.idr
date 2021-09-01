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

chk : (ty : TypeInfo) -> List (Fin ty.args.length, ArgExplicitness, Name) -> Type -> TestCaseData
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

            , ("1st given expl",) $ chk YInfo [(0, ExplicitArg, "x")] $ (x : Nat) -> Gen (a : Type ** Y x a)
            , ("1st given impl",) $ chk YInfo [(0, ImplicitArg, "x")] $ {x : Nat} -> Gen (a : Type ** Y x a)
            , ("2nd given expl",) $ chk YInfo [(1, ExplicitArg, "b")] $ (b : Type) -> Gen (n : Nat ** Y n b)
            , ("2nd given impl",) $ chk YInfo [(1, ImplicitArg, "b")] $ {b : Type} -> Gen (n : Nat ** Y n b)

            , ("both given, expl+expl",)  $ chk YInfo [(1, ExplicitArg, "b"), (0, ExplicitArg, "m")] $ (m : Nat) -> (b : Type) -> Gen (Y m b)
            , ("both given', expl+expl",) $ chk YInfo [(1, ExplicitArg, "a"), (0, ExplicitArg, "n")] $ (n : Nat) -> (a : Type) -> Gen (Y n a)
            , ("both given, expl+impl",)  $ chk YInfo [(1, ImplicitArg, "b"), (0, ExplicitArg, "m")] $ (m : Nat) -> {b : Type} -> Gen (Y m b)
            , ("both given, impl+expl",)  $ chk YInfo [(1, ExplicitArg, "b"), (0, ImplicitArg, "m")] $ {m : Nat} -> (b : Type) -> Gen (Y m b)
            , ("both given, impl+impl",)  $ chk YInfo [(1, ImplicitArg, "b"), (0, ImplicitArg, "m")] $ {m : Nat} -> {b : Type} -> Gen (Y m b)
            ]

namespace NonDepExplParams_AllUnnamed

  data Y : Nat -> Type -> Type where
    Y0 : Y 0 Int
    Y1 : Y 1 Nat

  YInfo : TypeInfo
  YInfo = getInfo `{Y}

  export
  check : List TestCaseDesc
  check = mapFst ("non-dependent type + expl params; all unnamed; " ++) <$>
            [ ("both given, expl+expl",)  $ chk YInfo [(1, ExplicitArg, "b"), (0, ExplicitArg, "m")] $ (m : Nat) -> (b : Type) -> Gen (Y m b)
            , ("both given', expl+expl",) $ chk YInfo [(1, ExplicitArg, "a"), (0, ExplicitArg, "n")] $ (n : Nat) -> (a : Type) -> Gen (Y n a)
            , ("both given, expl+impl",)  $ chk YInfo [(1, ImplicitArg, "b"), (0, ExplicitArg, "m")] $ (m : Nat) -> {b : Type} -> Gen (Y m b)
            , ("both given, impl+expl",)  $ chk YInfo [(1, ExplicitArg, "b"), (0, ImplicitArg, "m")] $ {m : Nat} -> (b : Type) -> Gen (Y m b)
            , ("both given, impl+impl",)  $ chk YInfo [(1, ImplicitArg, "b"), (0, ImplicitArg, "m")] $ {m : Nat} -> {b : Type} -> Gen (Y m b)
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

            , ("1st given expl",) $ chk YInfo [(0, ExplicitArg, "x")] $ (x : Nat) -> Gen (a : Type ** Y {n=x} a)
            , ("1st given impl",) $ chk YInfo [(0, ImplicitArg, "x")] $ {x : Nat} -> Gen (a : Type ** Y {n=x} a)
            , ("2nd given expl",) $ chk YInfo [(1, ExplicitArg, "b")] $ (b : Type) -> Gen (n : Nat ** Y {n} b)
            , ("2nd given impl",) $ chk YInfo [(1, ImplicitArg, "b")] $ {b : Type} -> Gen (n : Nat ** Y {n} b)

            , ("both given, expl+expl",)  $ chk YInfo [(1, ExplicitArg, "b"), (0, ExplicitArg, "m")] $ (m : Nat) -> (b : Type) -> Gen (Y {n=m} b)
            , ("both given', expl+expl",) $ chk YInfo [(1, ExplicitArg, "a"), (0, ExplicitArg, "n")] $ (n : Nat) -> (a : Type) -> Gen (Y {n} a)
            , ("both given, expl+impl",)  $ chk YInfo [(1, ImplicitArg, "b"), (0, ExplicitArg, "m")] $ (m : Nat) -> {b : Type} -> Gen (Y {n=m} b)
            , ("both given, impl+expl",)  $ chk YInfo [(1, ExplicitArg, "b"), (0, ImplicitArg, "m")] $ {m : Nat} -> (b : Type) -> Gen (Y {n=m} b)
            , ("both given, impl+impl",)  $ chk YInfo [(1, ImplicitArg, "b"), (0, ImplicitArg, "m")] $ {m : Nat} -> {b : Type} -> Gen (Y {n=m} b)
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

            , ("impl `a` given as expl",)  $ chk YInfo [(0, ExplicitArg, "u")] $ (u : Type) -> Gen (n : Nat ** v : Vect n u ** Y n v)
            , ("impl `a` given' as expl",) $ chk YInfo [(0, ExplicitArg, "a")] $ (a : Type) -> Gen (n : Nat ** v : Vect n a ** Y n v)
            , ("impl `a` given as impl",)  $ chk YInfo [(0, ImplicitArg, "u")] $ {u : Type} -> Gen (n : Nat ** v : Vect n u ** Y n v)

            , ("expl `n` given as expl",) $ chk YInfo [(1, ExplicitArg, "m")] $ (m : Nat) -> Gen (a : Type ** v : Vect m a ** Y m v)
            , ("expl `n` given as impl",) $ chk YInfo [(1, ImplicitArg, "m")] $ {m : Nat} -> Gen (a : Type ** v : Vect m a ** Y m v)

            , ("`a` and `n` given, expl+expl",) $ chk YInfo [(0, ExplicitArg, "b"), (1, ExplicitArg, "m")]
                                                $ (b : Type) -> (m : Nat) -> Gen (v : Vect m b ** Y m v)
            , ("`a` and `n` given, impl+expl",) $ chk YInfo [(0, ImplicitArg, "b"), (1, ExplicitArg, "m")]
                                                $ {b : Type} -> (m : Nat) -> Gen (v : Vect m b ** Y m v)
            , ("`a` and `n` given, expl+impl",) $ chk YInfo [(0, ExplicitArg, "b"), (1, ImplicitArg, "m")]
                                                $ (b : Type) -> {m : Nat} -> Gen (v : Vect m b ** Y m v)
            , ("`a` and `n` given, impl+impl",) $ chk YInfo [(0, ImplicitArg, "b"), (1, ImplicitArg, "m")]
                                                $ {b : Type} -> {m : Nat} -> Gen (v : Vect m b ** Y m v)

            , ("all given, expl+expl+expl",) $ chk YInfo [(0, ExplicitArg, "b"), (1, ExplicitArg, "m"), (2, ExplicitArg, "w")]
                                             $ (b : Type) -> (m : Nat) -> (w : Vect m b) -> Gen (Y m w)
            , ("all given, impl+expl+expl",) $ chk YInfo [(0, ImplicitArg, "b"), (1, ExplicitArg, "m"), (2, ExplicitArg, "w")]
                                             $ {b : Type} -> (m : Nat) -> (w : Vect m b) -> Gen (Y m w)
            , ("all given', impl+expl+expl",) $ chk YInfo [(0, ImplicitArg, "b"), (1, ExplicitArg, "a"), (2, ExplicitArg, "n")]
                                              $ {b : Type} -> (a : Nat) -> (n : Vect a b) -> Gen (Y a n)
            ]

namespace DepParams_RightmostUnnamed

  data Y : (n : Nat) -> Vect n a -> Type where
    Y0 : Y 0 []
    Y1 : (x : a) -> Y 1 [x]

  YInfo : TypeInfo
  YInfo = getInfo `{Y}

  export
  check : List TestCaseDesc
  check = mapFst ("dependent type + mixed explicitness; rightmost unnamed; " ++) <$>
            [ ("all given, expl+expl+expl",) $ chk YInfo [(0, ExplicitArg, "b"), (1, ExplicitArg, "m"), (2, ExplicitArg, "w")]
                                             $ (b : Type) -> (m : Nat) -> (w : Vect m b) -> Gen (Y m w)
            , ("all given, impl+expl+expl",) $ chk YInfo [(0, ImplicitArg, "b"), (1, ExplicitArg, "m"), (2, ExplicitArg, "w")]
                                             $ {b : Type} -> (m : Nat) -> (w : Vect m b) -> Gen (Y m w)
            , ("all given', impl+expl+expl",) $ chk YInfo [(0, ImplicitArg, "b"), (1, ExplicitArg, "a"), (2, ExplicitArg, "n")]
                                              $ {b : Type} -> (a : Nat) -> (n : Vect a b) -> Gen (Y a n)
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
    , NonDepExplParams_AllUnnamed.check
    , NonDepMixedParams_AllNamed.check
    , DepParams_AllNamed.check
    , DepParams_RightmostUnnamed.check
    ]

%runElab main
