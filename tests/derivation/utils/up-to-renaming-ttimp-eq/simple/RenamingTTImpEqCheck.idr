module RenamingTTImpEqCheck

import public Infra

%default total

%language ElabReflection

%runElab checkEq "unit is unit"                    True  Unit Unit
%runElab checkEq "unit is not its value"           False Unit ()

%runElab checkEq "zero is zero"                    True  Z Z
%runElab checkEq "zero is not one"                 False Z (S Z)

%runElab checkEq "one (cons) is one (nat lit)"     True  (S Z) 1 {expr2=Nat}
%runElab checkEq "nat one is not integer one"      False (S Z) 1

%runElab checkEq "list is list"                    True  List List
%runElab checkEq "list is not vect"                False List Vect

%runElab checkEq "succ is succ"                    True  S S
%runElab checkEq "succ is not zero"                False S Z

%runElab checkEq "unit is unit (ttimp)"            True  Unit $ var `{Builtin.Unit}
%runElab checkEq "unit is not some other `Unit`"   False Unit $ var `{Unit}

%runElab checkEq "nat id is nat id"                True  (\x : Nat => x) (\x : Nat => x)
%runElab checkEq "nat id is not string id"         False (\x : Nat => x) (\x : String => x)

%runElab checkEq "nat fun ty is nat fun ty"        True  (Nat -> Nat) (Nat -> Nat)
%runElab checkEq "nat fun ty is not string fun ty" False (Nat -> Nat) (String -> Nat)

%runElab checkEq "dep ty fun is itself"            True  ({a : _} -> (n : Nat) -> Vect n a) ({a : _} -> (n : Nat) -> Vect n a)
%runElab checkEq "dep ty fun is not another one"   False ({a : _} -> (n : Nat) -> Vect n a) ({a : _} -> (n : Nat) -> Vect (S n) a)
