module Deriving.DepTyCheck.Gen

import public Deriving.DepTyCheck.Gen.Entry

%default total

%defaulthint %inline
public export
DefaultConstructorDerivator : ConstructorDerivator
DefaultConstructorDerivator = LeastEffort
