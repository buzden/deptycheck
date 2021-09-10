module CanonicSigCheck

import public Infra

%default total

%language ElabReflection

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

main : Elab ()
main =
  traverse_ .| logCheck <=< pr .| with Prelude.(::) foldMap Lazy.fromList
    [ Trivial.check
    , NonDepExplParams_AllNamed.check
    , NonDepMixedParams_AllNamed.check
    , DepParams_AllNamed.check
    ]

%runElab main
