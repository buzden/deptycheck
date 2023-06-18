module CheckDistribution

import Data.Fin

import DistrCheckCommon

%default total

embedInEmpties : Nat -> Gen MaybeEmpty a -> Gen MaybeEmpty a
embedInEmpties Z     x = x
embedInEmpties (S k) x = oneOf
  [ empty
  , empty
  , empty
  , empty
  , empty
  , oneOf [pure (), pure ()] >>= \_ => embedInEmpties k x
  , empty
  , empty
  , empty
  , empty
  , empty
  ]

fins' : (n : Nat) -> Gen MaybeEmpty $ Fin n
fins' n = oneOf $ foldrLazy (\k => (::) $ embedInEmpties (finToNat k) (pure k)) [] $ fromList $ allFins n where

fins : (n : Nat) -> Gen MaybeEmpty $ Fin n
fins n = oneOf [pure n, pure n] >>= believe_me fins'

mainFor : Nat -> IO ()
mainFor Z = pure ()
mainFor n@(S _) = do
  printVerdict (fins n) $ fromList $
    [ coverWith (ratio 1 n) (== n') | n' <- allFins n ]

main : IO ()
main = do
  mainFor 1
  mainFor 2
  mainFor 4
  mainFor 8
