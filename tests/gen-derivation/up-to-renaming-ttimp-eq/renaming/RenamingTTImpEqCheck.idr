module RenamingTTImpEqCheck

import public Infra

%default total

%language ElabReflection

infixr 3 `lam`

%runElab checkEq "fst, rename, diff names" True (\x : Nat => \y : Nat => x) (\v : Nat => \w : Nat => v)
%runElab checkEq "fst, rename, same names" True (\x : Nat => \y : Nat => x) (\y : Nat => \x : Nat => y)
%runElab checkEq "snd, rename, diff names" True (\x : Nat => \y : Nat => y) (\v : Nat => \w : Nat => w)
%runElab checkEq "snd, rename, same names" True (\x : Nat => \y : Nat => y) (\y : Nat => \x : Nat => x)

%runElab checkEq "flipped lambda"          False (\x : Nat => \y : Nat => x) (\y : Nat => \x : Nat => x)
%runElab checkEq "flipped lambda, `_` q"   False (\x : Nat => \_ : Nat => x) (\_ : Nat => \x : Nat => x)
%runElab checkEq "flipped lambda, `_` e"   False `(\x => \_ => x) `(\_ => \x => x)
%runElab checkEq "flipped lambda, unnamed" False (lambdaArg `{x} `lam` arg implicitFalse `lam` `(x)) (arg implicitFalse `lam` lambdaArg `{x} `lam` `(x))

%runElab checkEq "snd, shadow"         True `(\x => \x => x) `(\y => \x => x)
%runElab checkEq "snd, shadow, rename" True `(\x => \x => x) `(\y => \u => u)

%runElab checkEq "unnamed unused" True (lambdaArg `{x} `lam` arg implicitFalse `lam` `(x)) (lambdaArg `{x} `lam` lambdaArg `{y} `lam` `(x))
%runElab checkEq "_ unused e"     True `(\x => \_ => x) `(\x => \y => x)
%runElab checkEq "_ unused q"     True (\x : Nat => \_ : Nat => x) (\x : Nat => \y : Nat => x)

%runElab checkEq "unnamed unused'" True (arg implicitFalse `lam` lambdaArg `{x} `lam` `(x)) (lambdaArg `{y} `lam` lambdaArg `{x} `lam` `(x))
%runElab checkEq "_ unused' e"     True `(\_ => \x => x) `(\y => \x => x)
%runElab checkEq "_ unused' q"     True (\_ : Nat => \x : Nat => x) (\y : Nat => \x : Nat => x)
