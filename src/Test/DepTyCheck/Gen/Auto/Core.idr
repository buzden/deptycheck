||| Main implementation of the derivator core interface
module Test.DepTyCheck.Gen.Auto.Core

import public Language.Reflection.Syntax
import public Language.Reflection.Types

import public Test.DepTyCheck.Gen.Auto.Derive

%default total

----------------------------
--- Derivation functions ---
----------------------------

export
DerivatorCore where
  canonicBody sig name = do

    -- check that there is at least one constructor
    let (_::_) = sig.targetType.cons
      | [] => fail "No constructors found for the type `\{show sig.targetType.name}`"

    ?canonicBody_rhs
