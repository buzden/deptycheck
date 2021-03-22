module Example.Pil.Lang.Aspects.Variables

import public Example.Pil.Lang.Aspects.Types

%default total

--- Variable's name datatype ---

export
data Name = MkName String

%name Name n, m

export
FromString Name where
  fromString = MkName

export
Eq Name where
  MkName n == MkName m = n == m

export
Show Name where
  show (MkName n) = n

export
DecEq Name where
  decEq (MkName n) (MkName m) = case decEq n m of
    Yes Refl => Yes Refl
    No co => No \case Refl => co Refl

--- Main description of defined variables ---

public export
Variables : Type
Variables = List (Name, Type')

%name Variables vars
