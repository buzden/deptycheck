module AlternativeCore

import public Test.DepTyCheck.Gen.Auto.Derive
import Test.DepTyCheck.Gen.Auto.Core

%default total

export
[Empty] DerivatorCore where
  canonicBody sig n = pure [ callCanonic sig n implicitTrue (replicate _ implicitTrue) .= `(empty) ]

export
[CallSelf] (sup : DerivatorCore) => DerivatorCore where
  canonicBody _ n = ?gen_body_call_self

-- Call an external for the particular type (say, `String), and returns `MkX` applied to derived string. Or `sup` otherwise.
export
[CallTheExt] (sup : DerivatorCore) => DerivatorCore where
  canonicBody _ n = ?gen_body_call_the_ext
