module Test

import Shared

%language ElabReflection

%runElab withUnify' ["x" #: `(Nat)] `(x) ["y" #: `(Nat)] `(y)
  $ \res => do
    assertFV res "y" `(x)
    assertOrder res ["x"]

%runElab withUnify' ["x" #: `(Nat)] `(S x) ["y" #: `(Nat)] `(y)
  $ \res => do
    assertFV res "y" `(Prelude.Types.S x)
    assertOrder res ["x"]

failing "Compiler failed to generate correct unification. Instead generated ?postpone"
  %runElab showUnify' ["x" #: `(Nat)] `(S x) ["y" #: `(Nat)] `(y + 1)

%runElab withUnify' ["x" #: `(Nat)] `(S (S x)) ["y" #: `(Nat)] `(2 + y)
  $ \res => do
    assertFV res "y" `(x)
    assertOrder res ["x"]

%runElab withUnify' ["x" #: `(Nat)] `(S (S x)) ["y" #: `(Nat)] `(1 + y)
  $ \res => do
    assertFV res "y" `(Prelude.Types.S x)
    assertOrder res ["x"]

%runElab withUnify'
  ["x" #: `(Nat), "y" #: `(Type)] `(Vect x y)
  []                              `(Vect 1 String)
  $ \ur => do
    assertFV' ur "x" Nat `(1)
    assertFV' ur "y" Type `(String)
    assertOrder ur []

%runElab withUnify'
  ["x" #: `(Nat), "y" #: `(Type)] `(Vect (S x) y)
  []                              `(Vect 1     String)
  $ \ur => do
    assertFV' ur "x" Nat `(0)
    assertFV' ur "y" Type `(String)
    assertOrder ur []

failing "Unifier failed with: Compiler couldn't find a unification"
  %runElab showUnify' ["x" #: `(Nat), "y" #: `(Type)] `(Vect (S $ S x) y)
                      []                              `(Vect 1     String)

failing "Unifier failed with: Compiler failed to generate correct unification. Instead generated ?postpone"
  %runElab showUnify' ["x" #: `(Nat), "y" #: `(Type), "z" #: `(Nat)]
                      `(Vect (x + z) y)
                      []                              `(Vect 1 String)

%runElab withUnify'
  ["x" #: `(Nat), "y" #: `(Type)] `(Vect (1 + x) y)
  []                              `(Vect 1     String)
  $ \ur => do
    assertFV' ur "x" Nat `(0)
    assertFV' ur "y" Type `(String)
    assertOrder ur []

failing "Unifier failed with: Compiler failed to generate correct unification. Instead generated ?postpone"
  %runElab showUnify' ["x" #: `(Nat), "y" #: `(Type)] `(Vect (x + 1) y)
                      []                              `(Vect 1     String)


%runElab withUnify'
  ["x" #: `(Nat), "y" #: `(Type)] `(Vect x y)
  ["z" #: `(Nat)]                 `(Vect (S z) String)
  $ \ur => do
    assertFV ur "x" `(Prelude.Types.S z)
    assertFV' ur "y" Type `(String)
    assertOrder ur ["z"]


%runElab withUnify' ["x" #: `(Nat), "y" #: `(Type)] `(Vect x y)
                    ["z" #: `(Type)]                `(Vect 10 (List z))
  $ \ur => do
    assertFV' ur "x" Nat `(10)
    assertFV ur "y" `(Prelude.Basics.List z)
    assertOrder ur ["z"]

%runElab withUnify'
  ["x" #: `(Nat), "y" #: `(Vect x Nat)] `(MkPair x y)
  []
  `(MkPair (the Nat 0) (the (Vect 0 Nat) []))
  $ \ur => do
    assertFV' ur "x" Nat `(0)
    assertFV' ur "y" (Vect 0 Nat) `(Nil {elem = Nat})
    assertOrder ur []

%runElab withUnify'
  ["x" #: `(Nat), "y" #: `(Vect x Nat)] `(MkPair x y)
  []
  `(MkPair (the Nat 1) (the (Vect 1 Nat) [2]))
  $ \ur => do
    assertFV' ur "x" Nat `(1)
    assertFV' ur "y" (Vect 1 Nat) `([2])
    assertOrder ur []

%runElab withUnify'
  ["x" #: `(Type)] `(Maybe x)
  ["y" #: `(Nat)] `(Maybe $ Fin y)
  $ \ur => do
    assertFV ur "x" `(Data.Fin.Fin y)
    assertOrder ur ["y"]


%runElab withUnify'
  ["len" #: `(Nat), "elem" #: `(Type)] `(Vect len elem)
  ["a" #: `(Nat), "b" #: `(Nat)] `(Vect a (Vect b Nat))
  $ \ur => do
    assertFV ur "a" `(len)
    assertFV ur "elem" `(Data.Vect.Vect b Prelude.Types.Nat)
    assertOrder ur ["len", "b"]

%runElab withUnify'
  ["a" #: `(Nat)] `(Vect a Nat)
  ["b" #: `(Type)] `(Vect 2 b)
  $ \ur => do
    assertFV' ur "a" Nat `(2)
    assertFV' ur "b" Type `(Nat)
    assertOrder ur []

failing "Unifier failed with: Compiler couldn't find a unification"
  %runElab withUnify'
    ["a" #: `(Nat)] `((\x => a))
    [] `(const 10)
    $ \ur => do
      assertFV ur "a" !(quote 10)
      assertOrder ur []

