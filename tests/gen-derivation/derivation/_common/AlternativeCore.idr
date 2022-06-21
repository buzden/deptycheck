module AlternativeCore

import public Test.DepTyCheck.Gen.Auto.Core

%default total

%language ElabReflection

irrelevantArgs : {n : _} -> Vect n TTImp
irrelevantArgs = replicate _ implicitTrue

numberedArgs : (bind : Bool) -> {n : _} -> Vect n TTImp
numberedArgs bind = Fin.tabulate $ (if bind then bindVar else varStr) . show

export
[EmptyBody] DerivatorCore where
  canonicBody sig n = pure $ (, the (AdditionalGensFor sig) neutral) [ callCanonic sig n implicitTrue irrelevantArgs .= `(empty) ]

export
[CallSelf] DerivatorCore where
  canonicBody sig n = pure $ (, the (AdditionalGensFor sig) neutral)
    [ callCanonic sig n (var `{Dry})                    irrelevantArgs      .= `(empty)
    , callCanonic sig n (var `{More} .$ bindVar "fuel") (numberedArgs True) .= fst !(callGen sig sig (var "fuel") $ numberedArgs False)
    ]

export
[EmptyCons'] ConstructorDerivator where
  consGenExpr sig _ _ _ = pure $ (, the (AdditionalGensFor sig) neutral) `(empty)

export
EmptyCons : DerivatorCore
EmptyCons = MainCoreDerivator @{EmptyCons'}

------------------------------
--- Working with externals ---
------------------------------

callSimpleGen : CanonicGen m => TypeInfo -> (fuel : TTImp) -> m TTImp
callSimpleGen tyi fuel = map fst $ callGen dummySig (MkGenSignature tyi SortedSet.empty) fuel $ believe_me $ Vect.Nil {elem = TTImp}

callStrGen : CanonicGen m => (fuel : TTImp) -> m TTImp
callStrGen = callSimpleGen $ typeInfoForPrimType StringType

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
  canonicBody sig n = pure $ (, the (AdditionalGensFor sig) neutral)
    [ callCanonic sig n (bindVar "fuel") irrelevantArgs .= `(MkXS <$> ~(!(callStrGen $ var "fuel"))) ]

--- Two (string) arguments taken from external ---

public export
data XSS = MkXSS String String

export
Show XSS where
  show (MkXSS s1 s2) = "MkXSS \{show s1} \{show s2}"

export
[Ext_XSS] DerivatorCore where
  canonicBody sig n = pure $ (, the (AdditionalGensFor sig) neutral)
    [ callCanonic sig n (bindVar "fuel") irrelevantArgs .= `(MkXSS <$> ~(!(callStrGen $ var "fuel")) <*> ~(!(callStrGen $ var "fuel"))) ]

--- Two (string and nat) arguments taken from external ---

public export
data XSN = MkXSN String Nat

export
Show XSN where
  show (MkXSN s n) = "MkXSN \{show s} \{show n}"

export
[Ext_XSN] DerivatorCore where
  canonicBody sig n = pure $ (, the (AdditionalGensFor sig) neutral)
    [ callCanonic sig n (bindVar "fuel") irrelevantArgs .= `(MkXSN <$> ~(!(callStrGen $ var "fuel")) <*> ~(!(callNatGen $ var "fuel"))) ]

--- Dependent type's argument + a constructor's argument taken from external ---

public export
data X'S : Nat -> Type where
  MkX'S : String -> X'S n

export
{n : Nat} -> Show (X'S n) where
  show (MkX'S s) = "MkX'S \{show s} : X'S \{show n}"

export
[Ext_X'S] DerivatorCore where
  canonicBody sig n = pure $ (, the (AdditionalGensFor sig) neutral)
    [ callCanonic sig n (bindVar "fuel") irrelevantArgs .= `(MkX'S <$> ~(!(callStrGen $ var "fuel"))) ]
