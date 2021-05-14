module Common

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
