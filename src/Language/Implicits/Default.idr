module Language.Implicits.Default

%default total

||| Interface for providing default value for an implicit in case of unresolved hole.
|||
||| Once you have an implicit argument `e` that in some contexts can be determined by
||| other arguments and/or return value, and one some contexts cannot, you can add
||| a constraint `Default val e =>` to a function to make `e` be chosen to be `val`
||| *only in cases* when in either way `e` would be an unsolved hole.
|||
||| The `Default val e` works nicely even if this parameter is of quantity `0`.
export
interface Default (0 def, a : ty) where
  constructor MkDefault

export %defaulthint
TheDefault : Default x x
TheDefault = MkDefault

export
Default def x where
