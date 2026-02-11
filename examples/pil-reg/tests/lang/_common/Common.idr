module Common

import public Data.DPair
import Example.Pil.Lang

%default total

public export
TestOps : Ops
TestOps = MkOps
  {unary = [ (String', "show", Int')
           ]}
  {binary = [ (Int', "+", Int', Int')
            , (Int', "/", Int', Int')
            , (Int', "%", Int', Int')
            , (Bool', "<", Int', Int')
            , (Bool', ">", Int', Int')
            , (Bool', "==", Int', Int')
            , (Bool', "/=", Int', Int')
            , (Bool', "&&", Bool', Bool')
            , (String', "concat", String', String')
            ]}

--- Functions lifted to the expression level ---

export %inline
(+) : Expression TestOps vars regs Int' -> Expression TestOps vars regs Int' -> Expression TestOps vars regs Int'
(+) = B @{Here _}

export %inline
div : Expression TestOps vars regs Int' -> Expression TestOps vars regs Int' -> Expression TestOps vars regs Int'
div = B @{There $ Here _}

export %inline
mod : Expression TestOps vars regs Int' -> Expression TestOps vars regs Int' -> Expression TestOps vars regs Int'
mod = B @{There $ There $ Here _}

export %inline
(<) : Expression TestOps vars regs Int' -> Expression TestOps vars regs Int' -> Expression TestOps vars regs Bool'
(<) = B @{There $ There $ There $ Here _}

export %inline
(>) : Expression TestOps vars regs Int' -> Expression TestOps vars regs Int' -> Expression TestOps vars regs Bool'
(>) = B @{There $ There $ There $ There $ Here _}

export %inline
(==) : Expression TestOps vars regs ? -> Expression TestOps vars regs ? -> Expression TestOps vars regs Bool'
(==) = B @{There $ There $ There $ There $ There $ Here _}

export %inline
(/=) : Expression TestOps vars regs ? -> Expression TestOps vars regs ? -> Expression TestOps vars regs Bool'
(/=) = B @{There $ There $ There $ There $ There $ There $ Here _}

export %inline
(&&) : Expression TestOps vars regs Bool' -> Expression TestOps vars regs Bool' -> Expression TestOps vars regs Bool'
(&&) = B @{There $ There $ There $ There $ There $ There $ There $ Here _}

export %inline
(++) : Expression TestOps vars regs String' -> Expression TestOps vars regs String' -> Expression TestOps vars regs String'
(++) = B @{There $ There $ There $ There $ There $ There $ There $ There $ Here _}

export %inline
show : Expression TestOps vars regs Int' -> Expression TestOps vars regs String'
show = U

public export %inline
Exists2 : (a -> b -> Type) -> Type
Exists2 ty = Exists $ \x => Exists $ \y => ty x y

public export %inline
Evidence2 : (0 x : a) -> (0 y : b) -> ty x y -> Exists2 ty
Evidence2 x y v = Evidence x $ Evidence y v
