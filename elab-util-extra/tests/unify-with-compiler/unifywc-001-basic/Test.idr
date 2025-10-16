module Test

import Shared

%language ElabReflection

%runElab runUnifyWithCompiler' [] `(0) [] `(0)

%runElab runUnifyWithCompiler' [] `(1) [] `(1)

failing "Unifier failed with: Compiler couldn't find a unification"
  %runElab runUnifyWithCompiler' [] `(0) [] `(1)

%runElab runUnifyWithCompiler' [] `(Z) [] `(Z)

%runElab runUnifyWithCompiler' [] `(S Z) [] `(S Z)

%runElab runUnifyWithCompiler' [] `(the Nat 0) [] `(Z)

%runElab runUnifyWithCompiler' [] `(the Nat 1) [] `(S Z)

failing "Unifier failed with: Compiler couldn't find a unification"
  %runElab runUnifyWithCompiler' [] `(0) [] `(Z)

failing "Unifier failed with: Compiler couldn't find a unification"
  %runElab runUnifyWithCompiler' [] `(1) [] `(S Z)

%runElab runUnifyWithCompiler' [] `(the (List Nat) [1,2,3,4,5]) [] `(the (List Nat) [1,2,3,4,5])

failing "Unifier failed with: Failed to build target type"
  %runElab runUnifyWithCompiler' [] `([1,2,3,4,5]) [] `([1,2,3,4,5])

%runElab runUnifyWithCompiler' [] `(the Nat (1 + 2)) [] `(the Nat 3)

%runElab runUnifyWithCompiler' [] `(the String "Hello world!") [] `("Hello world!")

failing "Unifier failed with: Compiler failed to generate correct unification. Instead generated ?postpone"
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

%runElab runUnifyWithCompiler' [] `((\a => a)) [] `(id)

%runElab runUnifyWithCompiler' [] `((\a => 0)) [] `(const 0)
