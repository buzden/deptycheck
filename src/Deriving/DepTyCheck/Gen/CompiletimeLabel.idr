module Deriving.DepTyCheck.Gen.CompiletimeLabel

import public Language.Reflection.Expr
import public Language.Reflection.Syntax
import public Language.Reflection.Syntax.Ops

%default total

public export
data CTLabel = MkCTLabel TTImp

public export
FromString CTLabel where
  fromString = MkCTLabel . primVal . Str

public export
Semigroup CTLabel where
  MkCTLabel l <+> MkCTLabel r = MkCTLabel `(~l ++ ~r)

public export
Monoid CTLabel where
  neutral = ""

namespace FromString
  public export %inline
  (.label) : String -> CTLabel
  (.label) = fromString

namespace FromTTImp
  public export %inline
  (.label) : TTImp -> CTLabel
  (.label) = MkCTLabel

export
labelGen : (desc : CTLabel) -> TTImp -> TTImp
labelGen (MkCTLabel desc) expr = `(Test.DepTyCheck.Gen.label (fromString ~desc) ~expr)

export
callOneOf : (desc : CTLabel) -> List TTImp -> TTImp
callOneOf desc [v]      = labelGen desc v
callOneOf desc variants = labelGen desc $ `(Test.DepTyCheck.Gen.oneOf {em=MaybeEmpty}) .$ liftList variants

-- List of weights and subgenerators
export
callFrequency : (desc : CTLabel) -> List (TTImp, TTImp) -> TTImp
callFrequency _    [(_, v)] = v
callFrequency desc variants = labelGen desc $ var `{Test.DepTyCheck.Gen.frequency} .$
                                liftList (variants <&> \(freq, subgen) => var `{Builtin.MkPair} .$ freq .$ subgen)
