module CanonicSigCheck

import public Infra

%default total

%language ElabReflection

data Y : (n : Nat) -> (v : Vect n a) -> Type where
  Y0 : Y 0 []
  Y1 : (x : a) -> Y 1 [x]

YInfo : TypeInfo
YInfo = getInfo `{Y}

cases : List TestCaseDesc
cases = mapFst ("dependent type + mixed explicitness; all named; " ++) <$>
          [ ("no givens",)  $ chk YInfo [] $ Gen0 (a : Type ** n : Nat ** v : Vect n a ** Y {a} n v)
          , ("no givens'",) $ chk YInfo [] $ Gen0 (a : Type ** n : Nat ** v : Vect n a ** Y n v)

          , ("impl `a` given",) $ chk YInfo [0] $ (a : Type) -> Gen0 (n : Nat ** v : Vect n a ** Y n v)
          , ("expl `n` given",) $ chk YInfo [1] $ (n : Nat) -> Gen0 (a : Type ** v : Vect n a ** Y n v)

          , ("`a` and `n` given",) $ chk YInfo [0, 1] $ (a : Type) -> (n : Nat) -> Gen0 (v : Vect n a ** Y n v)

          , ("all given",) $ chk YInfo [0, 1, 2] $ (a : Type) -> (n : Nat) -> (v : Vect n a) -> Gen0 (Y n v)
          ]

%runElab for_ cases checkAndLog
