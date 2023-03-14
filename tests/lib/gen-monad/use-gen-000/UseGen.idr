module UseGen

import Data.Fin

import Test.DepTyCheck.Gen

fin_uni_gen : {rc : Nat} -> Gen0 (Fin rc)
fin_uni_gen {rc=Z}   = empty
fin_uni_gen {rc=S _} = chooseAny
