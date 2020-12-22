module Example.Pil.DemoGen

import Control.Monad.State

import Data.List
import Data.List.Lazy
import Data.Strings

import Example.Pil.Gens
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
simpleValue {a=Int'}    = choose (-100, 100)
simpleValue {a=String'} = alphaString
simpleValue {a=Bool'}   = chooseAny

recExpr : ({x : Type'} -> Gen $ Expression ctx x) -> {a : Type'} -> Gen $ Expression ctx a
recExpr sub {a=Int'}    = oneOf [ U (+1) {opName="inc"} <$> sub {x=Int'}
                                , B (+) {opName="+"} <$> sub {x=Int'} <*> sub {x=Int'}
                                , B (*) {opName="*"} <$> sub {x=Int'} <*> sub {x=Int'}
                                ]
recExpr sub {a=String'} = oneOf [ U show {opName="as_str"} <$> sub {x=Int'}
                                , B (++) {opName="concat"} <$> sub {x=String'} <*> sub {x=String'}
                                ]
recExpr sub {a=Bool'}   = oneOf [ U not {opName="!"} <$> sub {x=Bool'}
                                , B (\x, y => x && y) {opName="&&"} <$> sub {x=Bool'} <*> sub {x=Bool'}
                                , B (\x, y => x || y) {opName="||"} <$> sub {x=Bool'} <*> sub {x=Bool'}
                                , B (<) {opName="<"} <$> sub {x=Int'} <*> sub {x=Int'}
                                , B (<=) {opName="<="} <$> sub {x=Int'} <*> sub {x=Int'}
                                ]

%hint
interestingExpr : {a : Type'} -> {ctx : Context} -> Gen (Expression ctx a)
interestingExpr = exprGen 3 simpleValue recExpr

export
someStatementGen : Gen (post ** Statement [] post)
someStatementGen = stmtGen 6 []

export
someStatement : Nat -> Maybe (post ** Statement [] post)
someStatement n = head' $ evalState someStdGen $ unGen (variant n $ someStatementGen)

export
showSomeStatements : {default 0 variant : Nat} -> (count : Nat) -> IO ()
showSomeStatements count = traverse_ putStrLn $ intersperse "----" $ (concat . map (\p => show $ snd p) . someStatement) <$> [variant .. (variant + count)]

export
main : IO ()
main = showSomeStatements {variant=5003} 10
