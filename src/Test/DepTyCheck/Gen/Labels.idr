module Test.DepTyCheck.Gen.Labels

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

public export
interface CanManageLabels (0 m : Type -> Type) where
  manageLabel : Label -> m a -> m a

export %defaulthint
IgnoreLabels : CanManageLabels m
IgnoreLabels = I where
  [I] CanManageLabels m where
    manageLabel _ = id
