module DerivedGen

import Decls
import RunDerivedGen

%default total

%language ElabReflection

checkedGen : Fuel -> {r : _} -> (rs : Regs r) -> (t : Ty) -> Gen MaybeEmpty $ Expr rs t
checkedGen = deriveGen

Show (Expr rs t) where
  show $ Read idx = "[\{show idx}]"

main : IO ()
main = runGs
  [ G $ \fl => checkedGen fl [Just B, Nothing, Just I, Just I] I
  ]
