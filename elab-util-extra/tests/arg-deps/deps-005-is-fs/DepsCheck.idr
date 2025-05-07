module DepsCheck

import Data.Vect

import Language.Reflection

%macro
typeOf : Elaboration m => Name -> m $ List Type
typeOf n = map (mapMaybe id) $ for !(getType n) $ catch . check {expected=Type} . snd

data IsFS : (n : _) -> Fin n -> Type where
  ItIsFS : IsFS _ (FS i)

export
0 listToCheck : List Type
listToCheck = typeOf `{ItIsFS}
