module AlternativeCore

import public Deriving.DepTyCheck.Gen.ForOneType.Impl

%default total

%language ElabReflection

irrelevantArgs : {n : _} -> Vect n TTImp
irrelevantArgs = replicate _ implicitTrue

numberedArgs : (bind : Bool) -> {n : _} -> Vect n TTImp
numberedArgs bind = Fin.tabulate $ (if bind then bindVar else var) . UN . Basic . show

export
[EmptyBody] DeriveBodyForType where
  canonicBody sig n = pure [ callCanonic sig n implicitTrue irrelevantArgs .= `(empty) ]

export
[CallSelf] DeriveBodyForType where
  canonicBody sig n = pure
    [ callCanonic sig n (var `{Dry})                    irrelevantArgs      .= `(empty)
    , callCanonic sig n (var `{More} .$ bindVar "fuel") (numberedArgs True) .= fst !(callGen sig (var "fuel") $ numberedArgs False)
    ]

export
[EmptyCons'] DeriveBodyRhsForCon where
  consGenExpr _ _ _ _ = pure `(empty)

export
EmptyCons : DeriveBodyForType
EmptyCons = MainCoreDerivator @{EmptyCons'}

------------------------------
--- Working with externals ---
------------------------------

callSimpleGen : DerivationClosure m => TypeInfo -> (fuel : TTImp) -> m TTImp
callSimpleGen tyi fuel = do
  _ <- ensureTyArgsNamed tyi
  map fst $ callGen (MkGenSignature tyi SortedSet.empty) fuel $ believe_me $ Vect.Nil {elem = TTImp}

callStrGen : DerivationClosure m => (fuel : TTImp) -> m TTImp
callStrGen = callSimpleGen $ typeInfoForPrimType StringType

callNatGen : DerivationClosure m => (fuel : TTImp) -> m TTImp
callNatGen = callSimpleGen $ getInfo "Nat"

--- One (string) argument taken from external ---

public export
data XS = MkXS String

export
Show XS where
  show (MkXS s) = "MkXS \{show s}"

export
[Ext_XS] DeriveBodyForType where
  canonicBody sig n =
    pure [ callCanonic sig n (bindVar "fuel") irrelevantArgs .= `(MkXS <$> ~(!(callStrGen $ var "fuel"))) ]

--- Two (string) arguments taken from external ---

public export
data XSS = MkXSS String String

export
Show XSS where
  show (MkXSS s1 s2) = "MkXSS \{show s1} \{show s2}"

export
[Ext_XSS] DeriveBodyForType where
  canonicBody sig n =
    pure [ callCanonic sig n (bindVar "fuel") irrelevantArgs .= `(MkXSS <$> ~(!(callStrGen $ var "fuel")) <*> ~(!(callStrGen $ var "fuel"))) ]

--- Two (string and nat) arguments taken from external ---

public export
data XSN = MkXSN String Nat

export
Show XSN where
  show (MkXSN s n) = "MkXSN \{show s} \{show n}"

export
[Ext_XSN] DeriveBodyForType where
  canonicBody sig n =
    pure [ callCanonic sig n (bindVar "fuel") irrelevantArgs .= `(MkXSN <$> ~(!(callStrGen $ var "fuel")) <*> ~(!(callNatGen $ var "fuel"))) ]

--- Dependent type's argument + a constructor's argument taken from external ---

public export
data X'S : Nat -> Type where
  MkX'S : String -> X'S n

export
{n : Nat} -> Show (X'S n) where
  show (MkX'S s) = "MkX'S \{show s} : X'S \{show n}"

export
[Ext_X'S] DeriveBodyForType where
  canonicBody sig n =
    pure [ callCanonic sig n (bindVar "fuel") irrelevantArgs .= `(MkX'S <$> ~(!(callStrGen $ var "fuel"))) ]
