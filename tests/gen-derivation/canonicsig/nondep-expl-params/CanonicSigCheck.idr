module CanonicSigCheck

import public Infra

%default total

%language ElabReflection

data Y : (n : Nat) -> (a : Type) -> Type where
  Y0 : Y 0 Int
  Y1 : Y 1 Nat

YInfo : TypeInfo
YInfo = getInfo `{Y}

cases : List TestCaseDesc
cases = mapFst ("non-dependent type + expl params; all named; " ++) <$>
          [ ("no givens",) $ chk YInfo [] $ Gen CanBeEmptyStatic (n : Nat ** a : Type ** Y n a)

          , ("1st given",) $ chk YInfo [0] $ (n : Nat) -> Gen CanBeEmptyStatic (a : Type ** Y n a)
          , ("2nd given",) $ chk YInfo [1] $ (a : Type) -> Gen CanBeEmptyStatic (n : Nat ** Y n a)

          , ("both given",) $ chk YInfo [1, 0] $ (n : Nat) -> (a : Type) -> Gen CanBeEmptyStatic (Y n a)
          ]

%runElab for_ cases checkAndLog
