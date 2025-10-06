module Language.Reflection.Unifier.Interface

import public Control.Monad.Either
import public Data.Either
import public Data.FinBitSet
import public Data.SortedMap
import public Data.Vect
import public Decidable.Equality
import public Language.Reflection
import public Language.Reflection.TTImp
import public Language.Reflection.TT
import public Language.Reflection.Syntax

public export
record TaskFVData where
  constructor MkTFVD
  name : Name
  rig : Count
  piInfo : PiInfo TTImp
  type : TTImp

Show a => Show (PiInfo a) where
  show ImplicitArg = "ImplicitArg"
  show ExplicitArg = "ExplicitArg"
  show AutoImplicit = "AutoImplicit"
  show (DefImplicit x) = "DefImplicit \{show x}"

public export
tryFromArg : MonadError e m => Lazy e -> Arg -> m TaskFVData
tryFromArg errMsg (MkArg count piInfo Nothing type) = 
  throwError errMsg
tryFromArg errMsg (MkArg count piInfo (Just x) type) = 
  pure $ MkTFVD x count piInfo type

public export
Show TaskFVData where
  show (MkTFVD name rig piInfo type) = 
    showPiInfo piInfo $ showCount rig "\{name} : \{show type}"

public export
record UnificationTask where
  constructor MkUniTask
  lfv : Nat
  lhsFreeVars : Vect lfv TaskFVData
  lhs : TTImp
  rfv : Nat
  rhsFreeVars : Vect rfv TaskFVData
  rhs : TTImp

%name UnificationTask task

public export
Show UnificationTask where
  show (MkUniTask l lfv lhs r rfv rhs) = 
    "MkUniTask \{show l} \{show lfv} \{show lhs} \{show r} \{show rfv} \{show rhs}"

public export
record FVData where
  constructor MkFVData
  name : Name
  holeName : String
  rig : Count
  piInfo : PiInfo TTImp
  type : TTImp
  value : Maybe TTImp

%name FVData fv, fvData

public export
Eq FVData where
  (==) (MkFVData n h r p t v) (MkFVData n' h' r' p' t' v') = 
    n == n' && h == h' && t == t' && v == v' && r == r' && p == p'

public export
Show FVData where
  show (MkFVData n h r p t v) = joinBy "" [ showPiInfo p $ showCount r "\{n} \{h} : \{show t}", " = \{show v}" ]

public export
makeFVData : (String, TaskFVData, Name, TTImp, Maybe TTImp) -> FVData
makeFVData (h, fv, n, t, v) = MkFVData n h fv.rig fv.piInfo t v

public export
record DependencyGraph where
  constructor MkDG
  freeVars : Nat
  fvData : Vect freeVars FVData
  fvDeps : Vect freeVars $ FinBitSet freeVars
  --- The set of all i: (Fin freeVars), where (index i fvData).value = None
  empties : FinBitSet freeVars
  --- For all i : (Fin freeVars); (lookup (index i fvData).name nameToId) = i
  nameToId : SortedMap Name $ Fin freeVars
  --- For all i : (Fin freeVars); (lookup (index i fvData).holeName holeToId) = i
  holeToId : SortedMap String $ Fin freeVars

%name DependencyGraph dg, depGraph

public export
Eq DependencyGraph where
  (==) (MkDG a b c d e f) (MkDG a' b' c' d' e' f') with (decEq a a') 
   (==) (MkDG a b c d e f) (MkDG a' b' c' d' e' f') | Yes p =
    a == a' && b == (rewrite p in b') && c == (rewrite p in c') && 
      d == (rewrite p in d') && e == (rewrite p in e') && f == (rewrite p in f')
   (==) (MkDG a b c d e f) (MkDG a' b' c' d' e' f') | No _ = False

public export
Show DependencyGraph where
  show (MkDG a b c d e f) = 
    "MkDG \{show a} \{show b} \{show c} \{show d} \{show e} \{show f}"

prettyDeps : (dg : DependencyGraph) -> FinBitSet dg.freeVars -> String
prettyDeps dg deps = 
  if deps == empty then
    ""
  else
    " Depends on: \{show $ (name . flip index dg.fvData) <$> toList deps}\n"

prettyFV : (dg : DependencyGraph) -> FVData -> String
prettyFV dg fvd = 
  "\{show fvd.name} : \{show fvd.type}" ++ 
    (case fvd.value of
      Nothing => "\n"
      Just val => " = \{show val}\n") ++
    " n2Id : \{show $ lookup fvd.name dg.nameToId}; " ++
    " h2Id : \{show $ lookup fvd.holeName dg.holeToId}\n"


public export
prettyDG : DependencyGraph -> String
prettyDG dg = joinBy ""
  [ show dg.freeVars
  , " free variables:\n"
  , (joinBy "" $ 
      (\(a,b) => prettyFV dg a ++ prettyDeps dg b) <$> 
        (toList $ zip dg.fvData dg.fvDeps))   
  , "===\n"
  , "Empties: "
  , show $ (name . flip index dg.fvData) <$> toList dg.empties
  , "\n======"
  ]

leaves : (dg : DependencyGraph) -> FinBitSet dg.freeVars
leaves dg = 
  foldl 
    (\acc,(id, deps) => if deps == empty then insert id acc else acc) 
    empty $ 
  zip (allFins dg.freeVars) dg.fvDeps

-- List all the free variables without a value that don't depend on any other free variables
emptyLeaves : (dg : DependencyGraph) -> FinBitSet dg.freeVars
emptyLeaves dg = intersection dg.empties $ leaves dg

updateCtx : List (Fin v) -> SnocList (Fin v) -> SnocList (Fin v)
updateCtx [] acc = acc
updateCtx (x :: xs) acc = updateCtx xs $ acc :< x

-- List all the free variables without a value in order of dependency
flattenEmpties' : (dg : DependencyGraph) -> SnocList (Fin dg.freeVars) -> SnocList $ Fin dg.freeVars
flattenEmpties' dg ctx = do
  let els = emptyLeaves dg
  let False = els == empty
  | _ => ctx
  let newCtx = updateCtx (toList els) ctx
  flattenEmpties' (MkDG dg.freeVars dg.fvData (removeAll els <$> dg.fvDeps) (removeAll els dg.empties) dg.nameToId dg.holeToId) newCtx

public export
flattenEmpties : (dg : DependencyGraph) -> SnocList $ Fin dg.freeVars
flattenEmpties dg = flattenEmpties' dg [<]

public export
Unifier : Type
Unifier = UnificationTask -> Elab $ Either String DependencyGraph

