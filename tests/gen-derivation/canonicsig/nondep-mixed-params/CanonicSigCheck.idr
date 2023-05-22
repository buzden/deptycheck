module CanonicSigCheck

import public Infra

%default total

%language ElabReflection

data Y : {n : Nat} -> (a : Type) -> Type where
  Y0 : Y {n=0} Int
  Y1 : Y {n=1} Nat

YInfo : TypeInfo
YInfo = getInfo `{Y}

export
cases : List TestCaseDesc
cases = mapFst ("non-dependent type + mixed explicitness; all named; " ++) <$>
          [ ("no givens",) $ chk YInfo [] $ Gen0 (n : Nat ** a : Type ** Y {n} a)

          , ("1st given",) $ chk YInfo [0] $ (n : Nat) -> Gen0 (a : Type ** Y {n} a)
          , ("2nd given",) $ chk YInfo [1] $ (a : Type) -> Gen0 (n : Nat ** Y {n} a)

          , ("both given",)  $ chk YInfo [1, 0] $ (n : Nat) -> (a : Type) -> Gen0 (Y {n} a)
          ]

%runElab for_ cases checkAndLog
