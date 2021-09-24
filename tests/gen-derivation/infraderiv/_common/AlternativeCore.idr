module AlternativeCore

import Test.DepTyCheck.Gen.Auto.Core
import public Test.DepTyCheck.Gen.Auto.Derive
import public Test.DepTyCheck.Gen.Auto.Entry

%default total

%language ElabReflection

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

------------------------------
--- Working with externals ---
------------------------------

callSimpleGen : CanonicGen m => TypeInfo -> (fuel : TTImp) -> m TTImp
callSimpleGen tyi fuel = callGen (MkGenSignature tyi SortedSet.empty) fuel $ believe_me $ Vect.Nil {elem = TTImp}

callStrGen : CanonicGen m => (fuel : TTImp) -> m TTImp
callStrGen = callSimpleGen $ primTypeInfo "String"

callNatGen : CanonicGen m => (fuel : TTImp) -> m TTImp
callNatGen = callSimpleGen $ getInfo "Nat"

--- One (string) argument taken from external ---

public export
data XS = MkXS String

export
Show XS where
  show (MkXS s) = "MkXS \{show s}"

export
[Ext_XS] DerivatorCore where
  canonicBody sig n =
    pure [ callCanonic sig n (bindVar "fuel") irrelevantArgs .= `(MkXS <$> ~(!(callStrGen $ var "fuel"))) ]

--- Two (string) arguments taken from external ---

public export
data XSS = MkXSS String String

export
Show XSS where
  show (MkXSS s1 s2) = "MkXSS \{show s1} \{show s2}"

export
[Ext_XSS] DerivatorCore where
  canonicBody sig n =
    pure [ callCanonic sig n (bindVar "fuel") irrelevantArgs .= `(MkXSS <$> ~(!(callStrGen $ var "fuel")) <*> ~(!(callStrGen $ var "fuel"))) ]

--- Two (string and nat) arguments taken from external ---

public export
data XSN = MkXSN String Nat

export
Show XSN where
  show (MkXSN s n) = "MkXSN \{show s} \{show n}"

export
[Ext_XSN] DerivatorCore where
  canonicBody sig n =
    pure [ callCanonic sig n (bindVar "fuel") irrelevantArgs .= `(MkXSN <$> ~(!(callStrGen $ var "fuel")) <*> ~(!(callNatGen $ var "fuel"))) ]
