module Example.Pil.GenShow

import Data.List

import Example.Pil.Gen

%default total

%hint
interestingType : Gen Type
interestingType = oneOf $ map pure $ [Int, String, Bool]

DecEq' Type where
  decEq' Int    Int    = Yes Refl
  decEq' String String = Yes Refl
  decEq' Bool   Bool   = Yes Refl
  decEq' _      _      = No

alphaChar : Gen Char
alphaChar = choose ('a', 'z')

%hint
alphaString : Gen String
alphaString = map pack $ sequence $ replicate !(choose (1, 3)) alphaChar

%hint
varName : Gen Name
varName = MkName <$> alphaString

partial
simpleValue : {a : Type} -> Gen a
simpleValue {a=Int}    = chooseAny
simpleValue {a=String} = alphaString
simpleValue {a=Bool}   = chooseAny

partial
uniFunction : {a : Type} -> Gen (a -> a)
uniFunction {a=Int}    = oneOf $ map pure $ [ (+1), (+2), \x => x - 1 ]
uniFunction {a=String} = oneOf $ map pure $ [ ("a"++), (++"z") ]
uniFunction {a=Bool}   = pure not

partial
biFunction : {a : Type} -> Gen (a -> a -> a)
biFunction {a=Int}    = oneOf $ map pure $ [ (+), (*) ]
biFunction {a=String} = pure (++)
biFunction {a=Bool}   = oneOf $ map pure $ [ (\x, y => x && y), (\x, y => x || y) ]

%hint
partial
interestingExpr : {a : Type} -> {ctx : Context} -> Gen (Expression ctx a)
interestingExpr = exprGen 3 simpleValue uniFunction biFunction

partial
someStatementGen : Gen (post ** Statement [] post)
someStatementGen = stmtGen []

partial
someStatement : (post ** Statement [] post)
someStatement = unGen someStatementGen someStdGen
