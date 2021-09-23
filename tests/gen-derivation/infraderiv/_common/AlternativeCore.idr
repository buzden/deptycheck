module AlternativeCore

import Test.DepTyCheck.Gen.Auto.Core
import public Test.DepTyCheck.Gen.Auto.Derive
import public Test.DepTyCheck.Gen.Auto.Entry

%default total

export covering
printDerived : DerivatorCore => Type -> Elab Unit
printDerived ty = logMsg "gen.auto.derive.infra" 0 $ "\n" ++ show !(deriveGenExpr !(quote ty))

irrelevantArgs : {n : _} -> Vect n TTImp
irrelevantArgs = replicate _ implicitTrue

numberedArgs : (bind : Bool) -> {n : _} -> Vect n TTImp
numberedArgs bind = Fin.tabulate $ (if bind then bindVar else varStr) . show

export
[Empty] DerivatorCore where
  canonicBody sig n = pure [ callCanonic sig n implicitTrue irrelevantArgs .= `(empty) ]

export
[CallSelf] (sup : DerivatorCore) => DerivatorCore where
  canonicBody sig n = pure
    [ callCanonic sig n (var `{Dry})                    irrelevantArgs      .= `(empty)
    , callCanonic sig n (var `{More} .$ bindVar "fuel") (numberedArgs True) .= !(callGen sig (var "fuel") $ numberedArgs False)
    ]

-- Call an external for the particular type (say, `String), and returns `MkX` applied to derived string. Or `sup` otherwise.
export
[CallTheExt] (sup : DerivatorCore) => DerivatorCore where
  canonicBody _ n = ?gen_body_call_the_ext
