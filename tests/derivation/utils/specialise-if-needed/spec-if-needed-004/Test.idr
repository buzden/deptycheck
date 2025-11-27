module Test

import Data.Fin
import Shared

%language ElabReflection

%logging "deptycheck.util.specialisation" 20

data X : (f : Nat -> Type) -> (n : Nat) -> (f n -> Nat) -> Type where

Nt : Nat -> Type
Nt 0 = Nat
Nt _ = List Nat

data Y : (a -> Nat) -> Type -> Type where

Nn : List Nat -> Nat

data Z = MkZ (Y Nn (X Nt 5 Nn))

%runElab runSIN Nothing True (const "X1") `(Y {a=Nat} Nn (X Nt 5 Nn))

Nn' : Fin 5 -> Nat

data Z' = MkZ' (Y Nn' (X Fin 5 Nn'))

%runElab runSIN Nothing True (const "X2") `(Y {a=Nat} Nn' (X Fin 5 Nn'))
