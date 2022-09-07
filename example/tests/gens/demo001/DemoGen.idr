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
interestingType = elements [Int', String', Bool']

alphaChar : Gen Char
alphaChar = choose ('a', 'z')

alphaString : Gen String
alphaString = map pack $ sequence $ List.replicate !(choose (1, 3)) alphaChar

%hint
varName : Gen Name
varName = fromString <$> alphaString

simpleValue : {a : Type'} -> Gen $ idrTypeOf a
simpleValue {a=Int'}    = choose (-100, 100)
simpleValue {a=String'} = alphaString
simpleValue {a=Bool'}   = chooseAny

recExpr : ({x : Type'} -> Gen $ Expression vars regs x) -> {a : Type'} -> Gen $ Expression vars regs a
recExpr sub {a=Int'}    = oneOf [ U (+1) {opName="inc"} <$> forgetStructure (sub {x=Int'})
                                , B (+) {opName="+"} <$> forgetStructure (sub {x=Int'}) <*> forgetStructure (sub {x=Int'})
                                , B (*) {opName="*"} <$> forgetStructure (sub {x=Int'}) <*> forgetStructure (sub {x=Int'})
                                ]
recExpr sub {a=String'} = oneOf [ U show {opName="as_str"} <$> forgetStructure (sub {x=Int'})
                                , B (++) {opName="concat"} <$> forgetStructure (sub {x=String'}) <*> forgetStructure (sub {x=String'})
                                ]
recExpr sub {a=Bool'}   = oneOf [ U not {opName="!"} <$> sub {x=Bool'}
                                , B (\x, y => x && y) {opName="&&"} <$> forgetStructure (sub {x=Bool'}) <*> forgetStructure (sub {x=Bool'})
                                , B (\x, y => x || y) {opName="||"} <$> forgetStructure (sub {x=Bool'}) <*> forgetStructure (sub {x=Bool'})
                                , B (<) {opName="<"} <$> forgetStructure (sub {x=Int'}) <*> forgetStructure (sub {x=Int'})
                                , B (<=) {opName="<="} <$> forgetStructure (sub {x=Int'}) <*> forgetStructure (sub {x=Int'})
                                ]

%hint
interestingExpr : {a : Type'} -> {vars : Variables} -> {regs : Registers rc} -> Gen (Expression vars regs a)
interestingExpr = exprGen (limit 3) simpleValue recExpr

export
someStatementGen : {rc : Nat} -> Gen (postV ** postR ** Statement [] (AllUndefined {rc}) postV postR)
someStatementGen = statement_gen (limit 6) [] AllUndefined

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
      (concat . map showStatement . someStatement {rc=regCount}) <$> [variant .. (variant + count)]

export
main : IO ()
main = showSomeStatements {variant=5003} 10
