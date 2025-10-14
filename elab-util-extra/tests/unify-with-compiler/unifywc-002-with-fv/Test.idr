module Test

import Shared

%language ElabReflection

%runElab showUnify' ["x" #: `(Nat)] `(x) ["y" #: `(Nat)] `(y)

%runElab showUnify' ["x" #: `(Nat)] `(S x) ["y" #: `(Nat)] `(y)

failing
  %runElab showUnify' ["x" #: `(Nat)] `(S x) ["y" #: `(Nat)] `(y + 1)

%runElab showUnify' ["x" #: `(Nat)] `(S (S x)) ["y" #: `(Nat)] `(2 + y)

%runElab showUnify' ["x" #: `(Nat)] `(S (S x)) ["y" #: `(Nat)] `(1 + y)

%runElab showUnify' ["x" #: `(Nat), "y" #: `(Type)] `(Vect x y)
                    []                              `(Vect 1 String)

%runElab showUnify' ["x" #: `(Nat), "y" #: `(Type)] `(Vect (S x) y)
                    []                              `(Vect 1     String)

failing
  %runElab showUnify' ["x" #: `(Nat), "y" #: `(Type)] `(Vect (S $ S x) y)
                      []                              `(Vect 1     String)

failing
  %runElab showUnify' ["x" #: `(Nat), "y" #: `(Type), "z" #: `(Nat)]
                      `(Vect (x + z) y)
                      []                              `(Vect 1 String)

%runElab showUnify' ["x" #: `(Nat), "y" #: `(Type)] `(Vect (1 + x) y)
                    []                              `(Vect 1     String)

failing
  %runElab showUnify' ["x" #: `(Nat), "y" #: `(Type)] `(Vect (x + 1) y)
                      []                              `(Vect 1     String)

%runElab showUnify' ["x" #: `(Nat), "y" #: `(Type)] `(Vect x y)
                    ["z" #: `(Nat)]                 `(Vect (S z) String)

%runElab showUnify' ["x" #: `(Nat), "y" #: `(Type)] `(Vect x y)
                    ["z" #: `(Type)]                `(Vect 10 (List z))

%runElab showUnify' ["x" #: `(Nat), "y" #: `(Vect x Nat)] `(MkPair x y)
                    []
                    `(MkPair (the Nat 0) (the (Vect 0 Nat) []))

%runElab showUnify' ["x" #: `(Nat), "y" #: `(Vect x Nat)] `(MkPair x y)
                    []
                    `(MkPair (the Nat 1) (the (Vect 1 Nat) [10]))
