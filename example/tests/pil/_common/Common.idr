module Common

import public Data.DPair
import Example.Pil.Lang

%default total

--- Functions lifted to the expression level ---

export %inline
(+) : Expression vars regs Int' -> Expression vars regs Int' -> Expression vars regs Int'
(+) = B (+) {opName="+"}

export %inline
div : Expression vars regs Int' -> Expression vars regs Int' -> Expression vars regs Int'
div = B div {opName="/"}

export %inline
mod : Expression vars regs Int' -> Expression vars regs Int' -> Expression vars regs Int'
mod = B mod {opName="%"}

export %inline
(<) : Expression vars regs Int' -> Expression vars regs Int' -> Expression vars regs Bool'
(<) = B (<) {opName="<"}

export %inline
(>) : Expression vars regs Int' -> Expression vars regs Int' -> Expression vars regs Bool'
(>) = B (>) {opName=">"}

export %inline
(==) : Eq (idrTypeOf a) => Expression vars regs a -> Expression vars regs a -> Expression vars regs Bool'
(==) = B (==) {opName="=="}

export %inline
(/=) : Eq (idrTypeOf a) => Expression vars regs a -> Expression vars regs a -> Expression vars regs Bool'
(/=) = B (/=) {opName="!="}

export %inline
(&&) : Expression vars regs Bool' -> Expression vars regs Bool' -> Expression vars regs Bool'
(&&) = B (\a, b => a && b) {opName="&&"} -- recoded because of laziness

export %inline
(++) : Expression vars regs String' -> Expression vars regs String' -> Expression vars regs String'
(++) = B (++) {opName="??concat??"}

export %inline
show : Show (idrTypeOf ty) => Expression vars regs ty -> Expression vars regs String'
show = U show {opName="toString"}

public export %inline
Exists2 : (a -> b -> Type) -> Type
Exists2 ty = Exists $ \x => Exists $ \y => ty x y

public export %inline
Evidence2 : (0 x : a) -> (0 y : b) -> ty x y -> Exists2 ty
Evidence2 x y v = Evidence x $ Evidence y v
