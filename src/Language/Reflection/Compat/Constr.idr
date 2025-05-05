-- This module should've be called `*.Con`, since it serves the `Con` data type,
-- but due to a need of compatibility with some lame OSes, we named it like this
module Language.Reflection.Compat.Constr

import public Data.Cozippable -- public due to compiler's bug #2439
import public Data.List.Elem
import public Data.So

import public Language.Reflection.Compat
import Language.Reflection.Expr

import public Syntax.IHateParens.List

%default total

--------------------------------------------
--- Compiler-based `Con` transformations ---
--------------------------------------------

-- This is a workaround to not to change `elab-util`'s `getInfo'`
export
normaliseCon : Elaboration m => Con -> m Con
normaliseCon orig@(MkCon n args ty) = do
  let whole = piAll ty args
  Just whole <- catch $ normaliseAsType whole
    | Nothing => pure orig -- didn't manage to normalise, e.g. due to private stuff
  let (args', ty) = unPi whole
  -- `quote` may corrupt names, workaround it:
  let args = comergeWith (\pre => {name := pre.name}) args args'
  pure $ MkCon n args ty

------------------------------------
--- Syntactic analysis of `Con`s ---
------------------------------------

export
conSubexprs : Con -> List TTImp
conSubexprs con = map type con.args ++ (map getExpr $ snd $ unAppAny con.type)

--------------------------------------
--- Compile-time constructors info ---
--------------------------------------

--- Constructor argument with nice literals ---

public export
record ConArg (0 con : Con) where
  constructor MkConArg
  conArgIdx : Fin con.args.length

namespace ConArg

  public export
  fromInteger : (x : Integer) -> (0 _ : So $ integerLessThanNat x con.args.length) => ConArg con
  fromInteger x = MkConArg $ fromInteger x

  elemToFin : Elem e xs -> Fin xs.length
  elemToFin Here      = FZ
  elemToFin (There x) = FS $ elemToFin x

  public export
  fromName : (n : Name) -> Elem (Just n) (map Arg.name con.args) => ConArg con
  fromName _ @{e} = MkConArg $ rewrite sym $ lengthMap con.args in elemToFin e

  -- this function is not exported because it breaks type inference in polymorphic higher-kinded case,
  -- but we still leave this a) in a hope that type inference would be improved; b) to make sure we still can implement it.
  --public export
  fromString : (n : String) -> Elem (Just $ fromString n) (map Arg.name con.args) => ConArg con
  fromString n = fromName $ fromString n

--- Getting full names of a data constructor ---

dataCon : Name -> Elab Name
dataCon n = do
  [n] <- mapMaybe id <$> (traverse isAccessibleDataCon =<< getInfo n)
    | [] => fail "Not found data constructor `\{n}`"
    | ns => fail "Ambiguous data constructors: \{joinBy ", " $ show <$> ns}"
  pure n

  where
    isAccessibleDataCon : (Name, NameInfo) -> Elab $ Maybe Name
    isAccessibleDataCon (n, MkNameInfo $ DataCon {}) = (catch (check {expected=()} `(let x = ~(var n) in ())) $> n) @{Compose}
    isAccessibleDataCon _                            = pure Nothing

export %macro (.dataCon) : Name -> Elab Name; (.dataCon) = dataCon

--- Information about constructors ---

public export
record IsConstructor (0 n : Name) where
  constructor ItIsCon
  typeInfo : TypeInfo
  conInfo  : Con

namespace IsConstructor
  export
  data GenuineProof : IsConstructor n -> Type where
    ItIsGenuine : GenuineProof iscn

export %macro
itIsConstructor : {n : Name} -> Elab (con : IsConstructor n ** GenuineProof con)
itIsConstructor = do
  cn <- dataCon n
  let True = n == cn
    | False => fail "Name `\{show n}` is not a full name, use either `\{show cn}` or macro `.dataCon`"
  con <- getCon cn
  let (IVar _ ty, _) = unAppAny con.type
    | (lhs, _) => fail "Can't get type name: \{show lhs}"
  ty <- getInfo' ty
  pure (ItIsCon ty con ** ItIsGenuine)
