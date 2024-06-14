module Syntax.Monad.Logic

import public Language.Implicits.IfUnsolved

%default total

-- Monadically lazy on the second argument
public export
(&&) : Monad m => m Bool -> m Bool -> m Bool
l && r = do
  True <- l
    | False => pure False
  r

-- Monadically lazy on the second argument
public export
(||) : Monad m => m Bool -> m Bool -> m Bool
l || r = do
  False <- l
    | True => pure True
  r

public export %inline
all : Monad n => Foldable f => Functor f => (0 _ : IfUnsolved f List) =>
      (a -> n Bool) -> f a -> n Bool
all = foldl (&&) (pure True) .: map

public export %inline
any : Monad n => Foldable f => Functor f => (0 _ : IfUnsolved f List) =>
      (a -> n Bool) -> f a -> n Bool
any = foldl (||) (pure False) .: map
