module Test.DepTyCheck.Gen.Labels

import Control.Monad.State.Interface
import public Control.Monad.Trans

import Data.String

%default total

-----------------
--- Labelling ---
-----------------

export
data Label : Type where
  StringLabel : String -> Label

export %inline
FromString Label where
  fromString = StringLabel

export %inline
Show Label where
  show (StringLabel x) = x

export
Eq Label where
  StringLabel x == StringLabel y = x == y

export
Ord Label where
  compare = comparing $ \(StringLabel x) => x

--- Labels management interface ---

public export
interface Monad m => CanManageLabels (0 m : Type -> Type) where
  manageLabel : Label -> m ()

public export
CanManageLabels m => MonadTrans t => Monad (t m) => CanManageLabels (t m) where
  manageLabel = lift . manageLabel

export %defaulthint
IgnoreLabels : Monad m => CanManageLabels m
IgnoreLabels = I where
  [I] CanManageLabels m where
    manageLabel _ = pure ()

export
[PrintAllLabels] HasIO io => CanManageLabels io where
  manageLabel = putStrLn . show
