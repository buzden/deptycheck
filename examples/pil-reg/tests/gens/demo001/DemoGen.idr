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

%hint
someInt : Gen0 Int
someInt = choose (-100, 100)

alphaChar : Gen0 Char
alphaChar = choose ('a', 'z')

%hint
alphaString : Gen0 String
alphaString = map pack $ sequence $ List.replicate !(choose (1, 3)) alphaChar

%hint
varName : Gen0 Name
varName = fromString <$> alphaString

export
someStatementGen : {rc : Nat} -> Gen0 (postV ** postR ** Statement SomeOps [] (AllUndefined {rc}) postV postR)
someStatementGen = statement_gen (limit 12) [] AllUndefined

export
someStatement : {rc : Nat} -> Nat -> Maybe (postV ** postR ** Statement SomeOps [] (AllUndefined {rc}) postV postR)
someStatement n = head' $ unGenTryN 100 someStdGen $ variant n $ someStatementGen

showStatement : forall ops, preV, preR. (postV ** postR ** Statement ops preV preR postV postR) -> String
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
