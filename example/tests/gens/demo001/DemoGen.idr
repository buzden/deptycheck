module DemoGen

import Control.Monad.State

import Data.Fin
import Data.List
import Data.List.Lazy
import Data.String

import Example.Pil.Gens
import Example.Pil.Lang.ShowC

import System.Random.Pure.StdGen

%default total

%hint
interestingType : Gen0 Type'
interestingType = elements [Int', String', Bool']

alphaChar : Gen0 Char
alphaChar = choose ('a', 'z')

alphaString : Gen0 String
alphaString = map pack $ sequence $ List.replicate !(choose (1, 3)) alphaChar

%hint
varName : Gen0 Name
varName = fromString <$> alphaString

simpleValue : {a : Type'} -> Gen0 $ idrTypeOf a
simpleValue {a=Int'}    = choose (-100, 100)
simpleValue {a=String'} = alphaString
simpleValue {a=Bool'}   = chooseAny

recExpr : ({x : Type'} -> Gen0 $ Expression vars regs x) -> {a : Type'} -> Gen0 $ Expression vars regs a
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
interestingExpr : {a : Type'} -> {vars : Variables} -> {regs : Registers rc} -> Gen0 (Expression vars regs a)
interestingExpr = exprGen (limit 3) simpleValue recExpr

export
someStatementGen : {rc : Nat} -> Gen0 (postV ** postR ** Statement [] (AllUndefined {rc}) postV postR)
someStatementGen = statement_gen (limit 12) [] AllUndefined

export
someStatement : {rc : Nat} -> Nat -> Maybe (postV ** postR ** Statement [] (AllUndefined {rc}) postV postR)
someStatement n = head' $ unGenTryN 100 someStdGen $ variant n $ someStatementGen

showStatement : forall preV, preR. (postV ** postR ** Statement preV preR postV postR) -> String
showStatement (postV ** postR ** stmt) = """
  \{show stmt}
  // regs ty after: \{show postR}
  """

export
showSomeStatements : {default 0 variant : Nat} -> {default 2 regCount : Nat} -> (count : Nat) -> IO ()
showSomeStatements count =
  traverse_ putStrLn $
    intersperse "\n----\n" $
      (concat . map showStatement . someStatement {rc=regCount}) <$> fromList [variant .. (variant + count)]

export
main : IO ()
main = showSomeStatements {variant=5003} 10
