module Test

import Shared

%language ElabReflection

%runElab withUnify' ["x" #: `(Nat)] `(x) ["y" #: `(Nat)] `(y) $ \res => do
  assertFV res "y" `(x)

%runElab withUnify' ["x" #: `(Nat)] `(S x) ["y" #: `(Nat)] `(y) $ \res => do
  assertFV res "y" `(Prelude.Types.S x)

failing
  %runElab showUnify' ["x" #: `(Nat)] `(S x) ["y" #: `(Nat)] `(y + 1)

%runElab withUnify' ["x" #: `(Nat)] `(S (S x)) ["y" #: `(Nat)] `(2 + y) $ \res => do
  assertFV res "y" `(x)

%runElab withUnify' ["x" #: `(Nat)] `(S (S x)) ["y" #: `(Nat)] `(1 + y) $ \res => do
  assertFV res "y" `(Prelude.Types.S x)

assert0 : UnificationResult -> Elab ()
assert0 ur = do
  assertFV ur "x" `(Prelude.Types.S Prelude.Types.Z)
  assertFV ur "y" `(String)
  assertOrder ur []

%runElab withUnify' ["x" #: `(Nat), "y" #: `(Type)] `(Vect x y)
                    []                              `(Vect 1 String)
                    assert0

assert1 : UnificationResult -> Elab ()
assert1 ur = do
  assertFV ur "x" `(Prelude.Types.Z)
  assertFV ur "y" `(String)
  assertOrder ur []

%runElab withUnify' ["x" #: `(Nat), "y" #: `(Type)] `(Vect (S x) y)
                    []                              `(Vect 1     String)
                    assert1

failing "Unifier failed with: Compiler couldn't find a unification"
  %runElab showUnify' ["x" #: `(Nat), "y" #: `(Type)] `(Vect (S $ S x) y)
                      []                              `(Vect 1     String)

failing "Unifier failed with: Compiler failed to generate correct unification. Instead generated ?postpone"
  %runElab showUnify' ["x" #: `(Nat), "y" #: `(Type), "z" #: `(Nat)]
                      `(Vect (x + z) y)
                      []                              `(Vect 1 String)

%runElab withUnify' ["x" #: `(Nat), "y" #: `(Type)] `(Vect (1 + x) y)
                    []                              `(Vect 1     String)
                    assert1

failing "Unifier failed with: Compiler failed to generate correct unification. Instead generated ?postpone"
  %runElab showUnify' ["x" #: `(Nat), "y" #: `(Type)] `(Vect (x + 1) y)
                      []                              `(Vect 1     String)

assert2 : UnificationResult -> Elab ()
assert2 ur = do
  assertFV ur "x" `(Prelude.Types.S z)
  assertFV ur "y" `(String)
  assertOrder ur ["z"]

%runElab withUnify' ["x" #: `(Nat), "y" #: `(Type)] `(Vect x y)
                    ["z" #: `(Nat)]                 `(Vect (S z) String)
                    assert2

assert3 : UnificationResult -> Elab ()
assert3 ur = do
  assertFV ur "x"
    `(Prelude.Types.S $ Prelude.Types.S $ Prelude.Types.S $ Prelude.Types.S $ Prelude.Types.S $ Prelude.Types.S $ Prelude.Types.S $
      Prelude.Types.S $ Prelude.Types.S $ Prelude.Types.S $ Prelude.Types.Z)
  assertFV ur "y" `(Prelude.Basics.List z)
  assertOrder ur ["z"]

%runElab withUnify' ["x" #: `(Nat), "y" #: `(Type)] `(Vect x y)
                    ["z" #: `(Type)]                `(Vect 10 (List z))
                    assert3

assert4 : UnificationResult -> Elab ()
assert4 ur = do
  assertFV ur "x" `(Prelude.Types.Z)
  assertFV ur "y" `(Data.Vect.Nil {elem = Prelude.Types.Nat})
  assertOrder ur []

%runElab withUnify' ["x" #: `(Nat), "y" #: `(Vect x Nat)] `(MkPair x y)
                    []
                    `(MkPair (the Nat 0) (the (Vect 0 Nat) []))
                    assert4

assert5 : UnificationResult -> Elab ()
assert5 ur = do
  assertFV ur "x" `(Prelude.Types.S Prelude.Types.Z)
  assertFV ur "y"
    `(Data.Vect.(::) {len = Prelude.Types.Z} {elem = Prelude.Types.Nat}
        (Prelude.Types.S $ Prelude.Types.S $ Prelude.Types.Z)
        $ Data.Vect.Nil {elem = Prelude.Types.Nat})

%runElab withUnify' ["x" #: `(Nat), "y" #: `(Vect x Nat)] `(MkPair x y)
                    []
                    `(MkPair (the Nat 1) (the (Vect 1 Nat) [2]))
                    assert5

assert6 : UnificationResult -> Elab ()
assert6 ur = do
  assertFV ur "x" `(Data.Fin.Fin y)
  assertOrder ur ["y"]

%runElab withUnify' ["x" #: `(Type)] `(Maybe x) ["y" #: `(Nat)] `(Maybe $ Fin y) assert6

assert7 : UnificationResult -> Elab ()
assert7 ur = do
  assertFV ur "a" `(len)
  assertFV ur "elem" `(Data.Vect.Vect b Prelude.Types.Nat)
  assertOrder ur ["len", "b"]

%runElab withUnify' ["len" #: `(Nat), "elem" #: `(Type)] `(Vect len elem)
                    ["a" #: `(Nat), "b" #: `(Nat)] `(Vect a (Vect b Nat))
                    assert7

assert8 : UnificationResult -> Elab ()
assert8 ur = do
  assertFV ur "a" `(Prelude.Types.S $ Prelude.Types.S $ Prelude.Types.Z)
  assertFV ur "b" `(Prelude.Types.Nat)
  assertOrder ur []

%runElab withUnify' ["a" #: `(Nat)] `(Vect a Nat)
                    ["b" #: `(Type)] `(Vect 2 b) assert8

assert9 : UnificationResult -> Elab ()
assert9 ur = do
  assertFV ur "a" !(quote 10)
  assertOrder ur []

failing "Unifier failed with: Compiler couldn't find a unification"
  %runElab withUnify' ["a" #: `(Nat)] `((\x => a))
                      [] `(const 10) assert9
