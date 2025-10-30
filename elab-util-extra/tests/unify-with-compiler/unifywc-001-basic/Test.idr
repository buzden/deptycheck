module Test

import Shared

%language ElabReflection

%runElab runUnifyWithCompiler' [] `(0) [] `(0)

%runElab runUnifyWithCompiler' [] `(1) [] `(1)

failing "Unifier failed with: Just NoUnificationError"
  %runElab runUnifyWithCompiler' [] `(0) [] `(1)

%runElab runUnifyWithCompiler' [] `(Z) [] `(Z)

%runElab runUnifyWithCompiler' [] `(S Z) [] `(S Z)

%runElab runUnifyWithCompiler' [] `(the Nat 0) [] `(Z)

%runElab runUnifyWithCompiler' [] `(the Nat 1) [] `(S Z)

failing "Unifier failed with: Just NoUnificationError"
  %runElab runUnifyWithCompiler' [] `(0) [] `(Z)

failing "Unifier failed with: Just NoUnificationError"
  %runElab runUnifyWithCompiler' [] `(1) [] `(S Z)

%runElab runUnifyWithCompiler' [] `(the (List Nat) [1,2,3,4,5]) [] `(the (List Nat) [1,2,3,4,5])

failing "TargetTypeError"
  %runElab runUnifyWithCompiler' [] `([1,2,3,4,5]) [] `([1,2,3,4,5])

%runElab runUnifyWithCompiler' [] `(the Nat (1 + 2)) [] `(the Nat 3)

%runElab runUnifyWithCompiler' [] `(the String "Hello world!") [] `("Hello world!")

failing "Unifier failed with: Nothing"
  %runElab runUnifyWithCompiler' [] `("Hello world!") [] `("Hello world!")

hw1 : String
hw1 = "Hello world!"

hw2 : String
hw2 = "Hello world!"

%runElab runUnifyWithCompiler' [] `(hw1) [] `(hw2)

%runElab runUnifyWithCompiler' [] `(runUnifyWithCompiler') [] `(runUnifyWithCompiler')

%runElab runUnifyWithCompiler' [] `(Vect 2 Nat) [] `(Vect (1+1) Nat)

%runElab runUnifyWithCompiler' [] `(0) [] `(_)

%runElab runUnifyWithCompiler' [] `(Nat) [] `(_)

%runElab runUnifyWithCompiler' [] `(0) [] `(?)

%runElab runUnifyWithCompiler' [] `(Nat) [] `(?)

%runElab runUnifyWithCompiler' [] `((\a => a)) [] `((\b => b))

failing "Unifier failed with: Nothing"
  %runElab runUnifyWithCompiler' [] `((\a, b => a + b)) [] `((\b, a => b + a))

%runElab runUnifyWithCompiler'
  [] `((\a : Nat, b : Nat => a + b))
  [] `((\b : Nat, a : Nat => b + a))

%runElab runUnifyWithCompiler'
  [] `((\a : Nat, b : Nat => a + b))
  [] `((+))

failing "Unifier failed with: Nothing"
  %runElab runUnifyWithCompiler' [] `((\a, b => a b)) [] `((\b, a => b a))

%runElab runUnifyWithCompiler'
  [] `((\a : (Nat -> Nat), b : Nat => a b))
  [] `((\b : (Nat -> Nat), a : Nat => b a))

%runElab runUnifyWithCompiler'
  [] `((\x : Type, y : Type, a : (x -> y), b : x => a b))
  [] `((\x : Type, y : Type, b : (x -> y), a : x => b a))

%runElab runUnifyWithCompiler'
  [] `(the ({0 x,y : Type} -> (x -> y) -> x -> y) (\a,b => a b))
  [] `((\b, a => b a))

%runElab runUnifyWithCompiler'
  [] `(the ({0 x,y : Type} -> (x -> y) -> x -> y) (\a,b => a b))
  [] `(Prelude.apply)

%runElab runUnifyWithCompiler' [] `((\a => a)) [] `(id)

%runElab runUnifyWithCompiler' [] `((\a => 0)) [] `(const 0)
