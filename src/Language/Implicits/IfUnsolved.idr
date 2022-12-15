module Language.Implicits.IfUnsolved

%default total

||| Interface for providing default value for an implicit in case of unsolved hole.
|||
||| Once you have an implicit argument `e` that in some contexts can be determined by
||| other arguments and/or return value, and one some contexts cannot, you can add
||| a constraint `IfUnsolved val e =>` to a function to make `e` be chosen to be `val`
||| *only in cases* when in either way `e` would be an unsolved hole.
|||
||| The `IfUnsolved val e` works nicely even if this parameter is of quantity `0`.
export
interface IfUnsolved (0 def, a : ty) where
  constructor MkIfUnsolved

export %defaulthint
TheIfUnsolved : IfUnsolved x x
TheIfUnsolved = MkIfUnsolved

export
IfUnsolved def x where
