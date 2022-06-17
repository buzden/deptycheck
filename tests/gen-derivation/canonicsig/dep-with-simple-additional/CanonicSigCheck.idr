module CanonicSigCheck

import public Infra

%default total

%language ElabReflection

data Y : (n : Nat) -> (v : Vect n a) -> Type where
  Y0 : Y 0 []
  Y1 : (x : a) -> Y 1 [x]

YInfo : TypeInfo
YInfo = getInfo `{Y}

NatInfo : TypeInfo
NatInfo = getInfo `{Nat}

Na, at : {sig : _} -> IsS (sig.targetType.args.length) => AdditionalGensFor sig -> AdditionalGensFor sig

Na with (sig.targetType.args.length) proof p
  _ | S _ = {additionalGens $= insert (rewrite p in FZ, MkGenSignature NatInfo empty)}
at with (sig.targetType.args.length) proof p
  _ | S _ = {additionalGens $= insert (rewrite p in FZ, MkGenSignature (typeInfoForPolyType `{a} []) empty)}

cases : List TestCaseDesc
cases = mapFst ("dependent type + mixed explicitness; all named; with additional; " ++) <$>
          [ ("no givens; universal",)                   $ chk YInfo [] {additional = un ne}
              $ (Fuel -> Gen (ty : Type ** Fuel -> Gen ty)) => Gen (a : Type ** n : Nat ** v : Vect n a ** Y {a} n v)
          , ("no givens'; universal + additional Nat",) $ chk YInfo [] {additional = un $ Na ne}
              $ (Fuel -> Gen (ty : Type ** Fuel -> Gen ty)) => (Fuel -> Gen Nat) => Gen (a : Type ** n : Nat ** v : Vect n a ** Y n v)

          , ("impl `a` given; additional `a`",)    $ chk YInfo [0]       {additional = at ne}
              $ (a : Type) -> (Fuel -> Gen a) => Gen (n : Nat ** v : Vect n a ** Y n v)
          , ("`a` and `n` given; additional `a`",) $ chk YInfo [0, 1]    {additional = at ne}
              $ (a : Type) -> (n : Nat) -> (Fuel -> Gen a) => Gen (v : Vect n a ** Y n v)
          , ("all given; additional `a`",)         $ chk YInfo [0, 1, 2] {additional = at ne}
              $ (a : Type) -> (n : Nat) -> (v : Vect n a) -> (Fuel -> Gen a) => Gen (Y n v)

          , ("impl `a` given; universal + additional `a`",)    $ chk YInfo [0]       {additional = un $ at ne}
              $ (a : Type) -> (Fuel -> Gen (ty : Type ** Fuel -> Gen ty)) => (Fuel -> Gen a) => Gen (n : Nat ** v : Vect n a ** Y n v)
          , ("`a` and `n` given; universal + additional `a`",) $ chk YInfo [0, 1]    {additional = un $ at ne}
              $ (a : Type) -> (n : Nat) -> (Fuel -> Gen (ty : Type ** Fuel -> Gen ty)) => (Fuel -> Gen a) => Gen (v : Vect n a ** Y n v)
          , ("all given; universal + additional `a`",)         $ chk YInfo [0, 1, 2] {additional = un $ at ne}
              $ (a : Type) -> (n : Nat) -> (v : Vect n a) -> (Fuel -> Gen (ty : Type ** Fuel -> Gen ty)) => (Fuel -> Gen a) => Gen (Y n v)
          ]

%runElab for_ cases checkAndLog
