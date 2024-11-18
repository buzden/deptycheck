module Decls

import Data.Fuel
import Data.Fin

import Decidable.Equality

import Test.DepTyCheck.Gen

%default total

%language ElabReflection

public export
data Ty = I | B

export
DecEq Ty where
  decEq I I = Yes Refl
  decEq B B = Yes Refl
  decEq I B = No $ \Refl impossible
  decEq B I = No $ \Refl impossible

public export
data MaybeTy = Nothing | Just Ty

public export
data Regs : Nat -> Type where
  Nil  : Regs 0
  (::) : MaybeTy -> Regs n -> Regs $ S n

public export
data RegIsType : Fin r -> Ty -> Regs r -> Type where
  Here  : RegIsType FZ t (Just t :: rest)
  There : RegIsType i t rest -> RegIsType (FS i) t (reg :: rest)

public export
data Expr : Regs r -> Ty -> Type where
  Read : (idx : Fin r) -> RegIsType idx t regs => Expr regs t
