module Test

import Shared

%language ElabReflection

public export
data Lookup : a -> List (a, b) -> Type where
  Here : {0 type_of_x : Type} -> {0 x : type_of_x} -> {0 b : Type} -> {0 xys : List (type_of_x, b)} -> (y : b) -> Lookup {b} {a = type_of_x} x ((::) {a = (type_of_x, b)} (MkPair {a = type_of_x} {b} x y) xys)
  There : {0 b : Type} -> {0 a : Type} -> {0 x : a} -> {0 y : b} -> {0 z : a} -> {0 xys : List (a, b)} -> Lookup {b} {a} z xys -> Lookup {b} {a} z ((::) {a = (a, b)} (MkPair {a} {b} x y) xys)

public export
data IsReveal : Lookup {a} {b} x xys -> b -> Type where
  IsHere : IsReveal (Here y) y
  IsThere : IsReveal subl y -> IsReveal (There subl) y

export
data Name = MkName String

public export
data Type' = Bool' | Int' | String'

%runElab specialiseDataLam' "IsRevealName" $ \ 0 l0 => \ 0 l1 => \ l2 => \ l3 => Test.IsReveal {a = Test.Name} {x = l0} {b = Type'} {xys = l1} l2 l3
