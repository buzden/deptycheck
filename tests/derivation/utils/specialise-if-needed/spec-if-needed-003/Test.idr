module Test

import Data.Fin
import Shared

%language ElabReflection

%logging "deptycheck.util.specialisation" 20


data X : (t : Type) -> (t -> Type) -> Type where

data Y = MkY (X Nat Fin)

%runElab runSIN Nothing True (const "SpecX") `(X Nat Fin)
