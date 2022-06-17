module CanonicSigCheck

import public Infra

%default total

%language ElabReflection

hte, htf : {sig : _} -> IsS (sig.targetType.args.length) => AdditionalGensFor sig -> AdditionalGensFor sig

h : TypeInfo
h = typeInfoForPolyType `{h} [MkArg MW ExplicitArg `{p} `(Prelude.Types.Nat)]

data Z : (h : Nat -> Type) -> Nat -> Type where
  Z0 : hh 0 -> Z hh n
  Zn : hh n -> Z hh (S n)

ZInfo : TypeInfo
ZInfo = getInfo `{Z}

hte with (sig.targetType.args.length) proof p
  _ | S _ = {additionalGens $= insert (rewrite p in FZ, MkGenSignature h empty)}
htf with (sig.targetType.args.length) proof p
  _ | S _ = {additionalGens $= insert (rewrite p in FZ, MkGenSignature h $ singleton 0)}

cases : List TestCaseDesc
cases = mapFst ("dependent type with higher-kinded additional; " ++) <$>
          [ ("hkt given; empty hkt givs",)             $ chk ZInfo [0] {additional=hte ne}
              $ (h : Nat -> Type) -> (Fuel -> Gen (p ** h p)) => Gen (n : Nat ** Z h n)
          , ("hkt given; empty hkt givs + universal",) $ chk ZInfo [0] {additional=hte $ un ne}
              $ (h : Nat -> Type) -> (Fuel -> Gen (ty : Type ** Fuel -> Gen ty)) => (Fuel -> Gen (p ** h p)) => Gen (n : Nat ** Z h n)

          , ("hkt given; hkt givs",)             $ chk ZInfo [0] {additional=htf ne}
              $ (h : Nat -> Type) -> (Fuel -> (p : Nat) -> Gen $ h p) => Gen (n : Nat ** Z h n)
          , ("hkt given; hkt givs + universal",) $ chk ZInfo [0] {additional=htf $ un ne}
              $ (h : Nat -> Type) -> (Fuel -> Gen (ty : Type ** Fuel -> Gen ty)) => (Fuel -> (p : Nat) -> Gen $ h p) => Gen (n : Nat ** Z h n)

          , ("all given; empty hkt givs",)             $ chk ZInfo [0, 1] {additional=hte ne}
              $ (h : Nat -> Type) -> (n : Nat) -> (Fuel -> Gen (p ** h p)) => Gen (Z h n)
          , ("all given; empty hkt givs + universal",) $ chk ZInfo [0, 1] {additional=hte $ un ne}
              $ (h : Nat -> Type) -> (n : Nat) -> (Fuel -> Gen (ty : Type ** Fuel -> Gen ty)) => (Fuel -> Gen (p ** h p)) => Gen (Z h n)

          , ("all given; hkt givs",)             $ chk ZInfo [0, 1] {additional=htf ne}
              $ (h : Nat -> Type) -> (n : Nat) -> (Fuel -> (p : Nat) -> Gen $ h p) => Gen (Z h n)
          , ("all given; hkt givs + universal",) $ chk ZInfo [0, 1] {additional=htf $ un ne}
              $ (h : Nat -> Type) -> (n : Nat) -> (Fuel -> Gen (ty : Type ** Fuel -> Gen ty)) => (Fuel -> (p : Nat) -> Gen $ h p) => Gen (Z h n)
          ]

%runElab for_ cases checkAndLog
