module Example.Pil.DemoGen

import Data.List
import Data.Strings

import Example.Pil.Gen
import Example.Pil.Lang.ShowC

%default total

%hint
interestingType : Gen Type'
interestingType = oneOf $ map pure $ [Int', String', Bool']

alphaChar : Gen Char
alphaChar = choose ('a', 'z')

%hint
alphaString : Gen String
alphaString = map pack $ sequence $ replicate !(choose (1, 3)) alphaChar

%hint
varName : Gen Name
varName = fromString <$> alphaString

simpleValue : {a : Type'} -> Gen $ idrTypeOf a
simpleValue {a=Int'}    = chooseAny
simpleValue {a=String'} = alphaString
simpleValue {a=Bool'}   = chooseAny

uniFunction : {a : Type'} -> Gen (idrTypeOf a -> idrTypeOf a)
uniFunction {a=Int'}    = oneOf $ map pure $ [ (+1), (+2), \x => x - 1 ]
uniFunction {a=String'} = oneOf $ map pure $ [ ("a"++), (++"z") ]
uniFunction {a=Bool'}   = pure not

biFunction : {a : Type'} -> Gen (idrTypeOf a -> idrTypeOf a -> idrTypeOf a)
biFunction {a=Int'}    = oneOf $ map pure $ [ (+), (*) ]
biFunction {a=String'} = pure (++)
biFunction {a=Bool'}   = oneOf $ map pure $ [ (\x, y => x && y), (\x, y => x || y) ]

%hint
interestingExpr : {a : Type'} -> {ctx : Context} -> Gen (Expression ctx a)
interestingExpr = exprGen 3 simpleValue uniFunction biFunction

export
someStatementGen : Gen (post ** Statement [] post)
someStatementGen = stmtGen 5 []

export
someStatement : Nat -> (post ** Statement [] post)
someStatement n = unGen (variant n $ someStatementGen) someStdGen

export
someStatements : String
someStatements = unlines $ intersperse "----" $ map (\n => show $ snd $ someStatement n) [0 .. 10]
