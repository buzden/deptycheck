module Language.Reflection.Unify.Interface

import Control.Monad.Either
import Data.Either
import Data.Fin.Set
import Data.SortedMap
import Data.Vect
import Decidable.Equality
import Derive.Prelude
import Language.Reflection
import Language.Reflection.Expr
import Language.Reflection.TTImp
import Language.Reflection.TT
import Language.Reflection.Syntax

%language ElabReflection

%default total

||| Unification task
public export
record UnificationTask where
  constructor MkUniTask
  ||| Amount of left-hand-side free variables
  {lfv : Nat}
  ||| Left-hand-side free variables
  lhsFreeVars : Vect lfv Arg
  {auto 0 lhsAreNamed : All IsNamedArg lhsFreeVars}
  ||| Left-hand-side expression
  lhsExpr : TTImp
  ||| Amount of right-hand-side free variables
  {rfv : Nat}
  ||| Right-hand-side free variables
  rhsFreeVars : Vect rfv Arg
  {auto 0 rhsAreNamed : All IsNamedArg rhsFreeVars}
  ||| Right-hand-side expression
  rhsExpr : TTImp

%name UnificationTask task

%runElab derive "Count" [Show]
%runElab derive "PiInfo" [Show]
%runElab derive "Syntax.Arg" [Show]

export
Show UnificationTask where
  showPrec p t =
    showCon p "MkUniTask" $
      joinBy "" $
        [ showArg t.lfv
        , showArg t.lhsFreeVars
        , showArg t.lhsExpr
        , showArg t.rfv
        , showArg t.rhsFreeVars
        , showArg t.rhsExpr
        ]

||| Free variable output data
public export
record FVData where
  constructor MkFVData
  ||| Free variable name
  name : Name
  ||| Free variable hole name
  holeName : String
  ||| Free variable count
  rig : Count
  ||| Free variable PiInfo
  piInfo : PiInfo TTImp
  ||| Free variable type
  type : TTImp
  ||| Free variable value
  value : Maybe TTImp

%name FVData fv, fvData

%runElab derive "FVData" [Show, Eq]

export
Interpolation FVData where
  interpolate (MkFVData n h r p t v) = joinBy "" [ showPiInfo p $ showCount r "\{n} \{h} : \{show t}", " = \{show v}" ]

||| Make FVData out of most its components and an argument
export
makeFVData : (String, Arg, Name, TTImp, Maybe TTImp) -> FVData
makeFVData (h, fv, n, t, v) = MkFVData n h fv.count fv.piInfo t v

public export
record FVDeps (freeVars : Nat) where
  constructor MkFVDeps
  typeDeps : FinSet freeVars
  valueDeps : FinSet freeVars
  piInfoDeps : FinSet freeVars

%name FVDeps deps

{freeVars : Nat} -> Show (FVDeps freeVars) where
  showPrec p t =
    showCon p "MkFVDeps" $
      joinBy "" $
        [ showArg t.typeDeps
        , showArg t.valueDeps
        , showArg t.piInfoDeps
        ]

{freeVars : Nat} -> Eq (FVDeps freeVars) where
  (==) a b = a.typeDeps == b.typeDeps && a.valueDeps == b.valueDeps && a.piInfoDeps == b.piInfoDeps

export
mergeDeps : FVDeps fv -> FinSet fv
mergeDeps (MkFVDeps typeDeps valueDeps piInfoDeps) = union typeDeps $ union valueDeps piInfoDeps

export
removeDeps : FinSet fv -> FVDeps fv -> FVDeps fv
removeDeps d =
  { typeDeps $= flip difference d
  , valueDeps $= flip difference d
  , piInfoDeps $= flip difference d
  }

||| Free variable depenfdency graph
public export
record DependencyGraph where
  constructor MkDG
  ||| Free variable amount
  freeVars : Nat
  ||| Free variable data
  fvData : Vect freeVars FVData
  ||| Free variable dependency matrix
  fvDeps : Vect freeVars $ FVDeps freeVars
  ||| The set of all i: (Fin freeVars), where (index i fvData).value = None
  empties : FinSet freeVars
  ||| For all i : (Fin freeVars); (lookup (index i fvData).name nameToId) = i
  nameToId : SortedMap Name $ Fin freeVars
  ||| For all i : (Fin freeVars); (lookup (index i fvData).holeName holeToId) = i
  holeToId : SortedMap String $ Fin freeVars

%name DependencyGraph dg, depGraph

%runElab derive "DependencyGraph" [Show]

export
Eq DependencyGraph where
  (==) (MkDG a b c d e f) (MkDG a' b' c' d' e' f') with (decEq a a')
   (==) (MkDG a b c d e f) (MkDG a b' c' d' e' f') | Yes Refl =
    b == b' && c == c' && d == d' && e == e' && f == f'
   _                                               | No _ = False

||| Unification result
public export
record UnificationResult where
  constructor MkUR
  ||| Task given to the unifier
  task : UnificationTask
  ||| Dependency graph returned by the unifier
  uniDg : DependencyGraph
  ||| LHS free variable (polymorphic constructor argument) values
  lhsResult : SortedMap Name TTImp
  ||| RHS free variable (specialised type argument) values
  rhsResult : SortedMap Name TTImp
  ||| All free variable values
  fullResult : SortedMap Name TTImp
  ||| Order of dependency of free variables without values
  ||| (specialised constructor arguments)
  order : List $ Fin uniDg.freeVars

%runElab derive "UnificationResult" [Show]

public export
data UnificationError : Type where
  CatastrophicError : UnificationError
  InternalError : String -> UnificationError
  TargetTypeError : TTImp -> UnificationError
  ExtractionError : TTImp -> UnificationError
  NoUnificationError : UnificationError

%runElab derive "UnificationError" [Show, Eq]

public export
data UnificationVerdict : Type where
  Success : UnificationResult -> UnificationVerdict
  Undecided : UnificationVerdict
  Fail : UnificationError -> UnificationVerdict

%runElab derive "UnificationVerdict" [Show]

export %inline
isSuccess : UnificationVerdict -> Bool
isSuccess (Success _) = True
isSuccess _ = False

export %inline
isUndecided : UnificationVerdict -> Bool
isUndecided Undecided = True
isUndecided _ = False

export %inline
isFail : UnificationVerdict -> Bool
isFail (Fail _) = True
isFail _ = False

export
Cast (Either (Maybe UnificationError) UnificationResult) UnificationVerdict where
  cast (Right s) = Success s
  cast (Left Nothing) = Undecided
  cast (Left $ Just e) = Fail e

public export
interface CanUnify (0 m : Type -> Type) where
  constructor MkCanUnify
  unify : UnificationTask -> m UnificationVerdict

export
Monad m => MonadTrans t => CanUnify m => CanUnify (t m) where
  unify = lift . unify

||| List all free variables that don't depende on any other free variables
leaves : (dg : DependencyGraph) -> FinSet dg.freeVars
leaves dg =
  foldl
    (\acc,(id, deps) => if null deps then insert id acc else acc)
    empty $
  zip (allFins dg.freeVars) (map mergeDeps dg.fvDeps)

||| List all the free variables without a value that don't depend on any other free variables
emptyLeaves : (dg : DependencyGraph) -> FinSet dg.freeVars
emptyLeaves dg = intersection dg.empties $ leaves dg

||| List all the free variables without a value in order of dependency
flattenEmpties : (dg : DependencyGraph) -> SnocList $ Fin dg.freeVars
flattenEmpties dg = flattenEmpties' dg [<]
  where
    flattenEmpties' : (dg : DependencyGraph) -> SnocList (Fin dg.freeVars) -> SnocList $ Fin dg.freeVars
    flattenEmpties' dg@(MkDG {freeVars, fvData, fvDeps, empties, nameToId, holeToId}) ctx = do
      let els = emptyLeaves dg
      let False = null els
      | _ => ctx
      -- Now els is a non-empty subset of dg.empties
      flattenEmpties'
        -- `assert_smaller dg` is a workaround for a non-working `assert_smaller empties`
        (assert_smaller dg $ MkDG
          freeVars
          fvData
          (removeDeps els <$> fvDeps)
          (assert_smaller empties $ flip difference els empties)
          nameToId
          holeToId)
        (ctx <>< toList els)

||| Find all variables which have no value
filterEmpty : Vect _ FVData -> List (Name, TTImp)
filterEmpty = foldl myfun []
  where
    myfun : List (Name, TTImp) -> FVData -> List (Name, TTImp)
    myfun xs x =
      case x.value of
        Just val => (x.name, val) :: xs
        Nothing => xs

||| Calculate UnificationResult (var-to-value mappings and empty leaf dependency order)
export
finalizeDG : (task : UnificationTask) -> (dg : DependencyGraph) -> UnificationResult
finalizeDG task dg = do
  let fvOrder = flattenEmpties dg
  let urList = filterEmpty dg.fvData
  let (lhsRL, rhsRL) = List.splitAt task.lfv urList
  MkUR
    { task
    , uniDg = dg
    , lhsResult = fromList lhsRL
    , rhsResult = fromList rhsRL
    , fullResult = fromList urList
    , order = toList fvOrder
    }
