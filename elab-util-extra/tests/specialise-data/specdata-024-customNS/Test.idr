module Test

import public Shared

%language ElabReflection

decls : List Decl
decls = %runElab specialiseData'' {nsProvider = inNS $ MkNS ["Custom", "Test"]} "MyNat" Nat

namespace Custom
  %runElab declare decls

--- The variable assignment is a workaround for https://github.com/idris-lang/Idris2/issues/3651
e0' = %runElab verifySpecialisation Nat MyNat [`(Z), `(S Z)]
