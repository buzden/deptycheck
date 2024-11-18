module DerivedGen

import Decls
import Deriving.DepTyCheck.Gen

%default total

%language ElabReflection

%runElab deriveGenPrinter @{MainCoreDerivator @{LeastEffort}} $ Fuel -> {r : _} -> (rs : Regs r) -> (t : Ty) -> Gen MaybeEmpty $ Expr rs t
