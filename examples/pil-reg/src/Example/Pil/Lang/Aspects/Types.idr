module Example.Pil.Lang.Aspects.Types

import public Decidable.Equality

%default total

--- Available types in the system ---

public export
data Type' = Bool' | Int' | String'

public export
idrTypeOf : Type' -> Type
idrTypeOf Bool'   = Bool
idrTypeOf Int'    = Int
idrTypeOf String' = String

public export
DecEq Type' where
  decEq Bool'   Bool'   = Yes Refl
  decEq Int'    Int'    = Yes Refl
  decEq String' String' = Yes Refl

  decEq Bool'   Int'    = No $ \case Refl impossible
  decEq Bool'   String' = No $ \case Refl impossible

  decEq Int'    Bool'   = No $ \case Refl impossible
  decEq Int'    String' = No $ \case Refl impossible

  decEq String' Bool'   = No $ \case Refl impossible
  decEq String' Int'    = No $ \case Refl impossible
