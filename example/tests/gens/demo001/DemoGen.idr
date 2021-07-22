module DemoGen

import Control.Monad.State

import Data.Fin
import Data.List
import Data.List.Lazy
import Data.String

import Example.Pil.Gens
import Example.Pil.Lang.ShowC

%default total

%hint
interestingType : Gen Type'
interestingType = oneOf $ map pure $ [Int', String', Bool']

alphaChar : Gen Char
alphaChar = choose ('a', 'z')

alphaString : Gen String
alphaString = map pack $ sequence $ replicate !(choose (1, 3)) alphaChar

%hint
varName : Gen Name
varName = fromString <$> alphaString

simpleValue : {a : Type'} -> Gen $ idrTypeOf a
simpleValue {a=Int'}    = choose (-100, 100)
simpleValue {a=String'} = alphaString
simpleValue {a=Bool'}   = chooseAny

recExpr : ({x : Type'} -> Gen $ Expression vars regs x) -> {a : Type'} -> Gen $ Expression vars regs a
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
interestingExpr : {a : Type'} -> {vars : Variables} -> {regs : Registers rc} -> Gen (Expression vars regs a)
interestingExpr = exprGen (limit 3) simpleValue recExpr

export
someStatementGen : {rc : Nat} -> Gen (postV ** postR ** Statement [] (AllUndefined {rc}) postV postR)
someStatementGen = statement_gen (limit 6) [] AllUndefined

export
someStatement : {rc : Nat} -> Nat -> Maybe (postV ** postR ** Statement [] (AllUndefined {rc}) postV postR)
someStatement n = evalState someStdGen $ unGen (variant n $ someStatementGen) >>= takeSomeRandomly
  where
    takeSomeRandomly : RandomGen g => LazyList a -> State g $ Maybe a
    takeSomeRandomly xs = pure $ head' $ drop (finToNat {n=1000} !random') xs

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
      (concat . map showStatement . someStatement {rc=regCount}) <$> [variant .. (variant + count)]

export
main : IO ()
main = showSomeStatements {variant=5003} 10
