module Deriving.SpecialiseData

import Control.Monad.Either
import Control.Monad.Trans
import public Data.DPair
import Data.Either
import Data.Fin.Set
import Data.List
import public Data.List.Map -- workaround for compiler bug #2439
import Data.List.Quantifiers
import Data.List1
import Data.Maybe
import Data.SnocList
import Data.SnocList.Quantifiers
import Data.SortedMap
import Data.SortedMap.Dependent
import Data.SortedSet
import Data.Vect
import Data.Vect.Quantifiers
import public Decidable.Decidable
import public Decidable.Equality
import Deriving.Show
import public Deriving.SpecialiseData.Codegen
import public Deriving.SpecialiseData.Codegen.Type
import public Deriving.SpecialiseData.Common
import public Deriving.SpecialiseData.Helpers
import public Deriving.SpecialiseData.QuantifiersExt
import public Deriving.SpecialiseData.Task
import public Deriving.SpecialiseData.TaskFormation
import public Deriving.SpecialiseData.TypeInfoExt
import public Deriving.SpecialiseData.Unification
import public Language.Mk
import Language.Reflection.Compat
import Language.Reflection.Compat.Constr
import public Language.Reflection.Compat.TypeInfo -- workaround for compiler bug #2439
import public Language.Reflection.Expr
import Language.Reflection.Syntax
import Language.Reflection.Logging
import public Language.Reflection.Unify.Interface
import public Language.Reflection.VarSubst -- workaround for compiler bug #2439
import Syntax.IHateParens

%language ElabReflection

%default total

---------------------------
--- DATA SPECIALISATION ---
---------------------------

||| Remove named and auto-implicit applications of holes
cleanupHoleAutoImplicitsImpl : TTImp -> TTImp
cleanupHoleAutoImplicitsImpl (IAutoApp _ x (Implicit _ _)) = x
cleanupHoleAutoImplicitsImpl (INamedApp _ x _ (Implicit _ _)) = x
cleanupHoleAutoImplicitsImpl x = x

||| Perform a specialisation for a given type name, kind and content expressions
|||
||| In order to generate a specialised type declaration equivalent to the following type alias:
||| ```
||| VF : Nat -> Type
||| VF n = Fin n
||| ```
||| ...you may use this function as follows:
||| ```
||| specialiseDataRaw `{VF} `(Nat -> Type) `(\n => Fin n)
||| ```
export
specialiseDataRaw :
  Monad m =>
  (nsProvider : NamespaceProvider m) =>
  (unifier : CanUnify m) =>
  MonadLog m =>
  MonadError SpecialisationError m =>
  (namesInfo : NamesInfoInTypes) =>
  SpecialisationParams =>
  (resultName : Name) ->
  (resultKind : TTImp) ->
  (resultContent : TTImp) ->
  m (TypeInfo, List Decl)
specialiseDataRaw resultName resultKind resultContent = do
  let resultKind = mapTTImp cleanupHoleAutoImplicitsImpl $ cleanupNamedHoles resultKind
  let resultContent = mapTTImp cleanupHoleAutoImplicitsImpl $ cleanupNamedHoles resultContent
  task <- getTask resultName resultKind resultContent
  logPoint DetailedDebug "specialiseData" [task.polyTy] "Specialisation task: \{show task}"
  uniResults <- sequence $ mapCons task $ unifyCon task
  (Element specTy specTyNamed, specMeta) <- mkSpecTy task uniResults
  decls <- specDecls task uniResults specTy specMeta
  pure (specTy, decls)

typeDPair : List Arg -> TTImp
typeDPair [] = `(Type)
typeDPair (x :: xs) = do
  let aName = fromMaybe "" x.name
  let aTyName = fromString "\{aName}^ty"
  let tyArg = MkArg MW ExplicitArg (Just aTyName) `(Type)
  let tyVar = var aTyName
  let valArg = MkArg MW ExplicitArg (Just aName) tyVar
  `(DPair Type ~(lam tyArg `(DPair ~tyVar ~(lam valArg $ typeDPair xs))))

valDPair : SortedMap Name String ->  List Arg -> TTImp -> TTImp
valDPair n2s [] x = x
valDPair n2s (x :: xs) y = do
  let aName = fromMaybe "" x.name
  let aTyName = fromString "\{aName}^ty"
  let tyVar = var aTyName
  let valVar = var aName
  let valHole = fromMaybe `(?) $ hole <$> lookup aName n2s
  `(MkDPair ~(x.type) ~(iLet MW aName x.type valHole `(MkDPair ~valVar ~(valDPair n2s xs y))))

unholeImpl : SortedMap String Name -> TTImp -> TTImp
unholeImpl s2n (IHole fc holeName) =
  case lookup holeName s2n of
      Just vn => var vn
      Nothing => IHole fc holeName
unholeImpl s2n t = t

unhole : SortedMap String Name -> TTImp -> TTImp
unhole s2n = mapTTImp (unholeImpl s2n)

unBadHoleImpl : TTImp -> TTImp
unBadHoleImpl (IHole fc "_") = Implicit fc False
unBadHoleImpl t = t

unBadHole : TTImp -> TTImp
unBadHole = mapTTImp unBadHoleImpl

unMkDPair : TTImp -> List TTImp
unMkDPair (IApp _ (IApp _ (INamedApp _ (INamedApp _ (IVar _ "Builtin.DPair.MkDPair") _ _) _ _) dl) dr) =
  dl :: unMkDPair dr
unMkDPair _ = []

decodeDPair : Elaboration m => List Arg -> List TTImp -> m (List Arg)
decodeDPair [] _ = pure []
decodeDPair (a :: as) (aT :: _ :: ts) = pure $ ({type := aT} a) :: !(decodeDPair as ts)
decodeDPair _ _ = fail "INTERNAL ERROR: Failed during lambda normalisation"

genAliases : Elaboration m => List Arg -> m (SortedMap Name String, SortedMap String Name)
genAliases = foldlM genAImpl (empty, empty)
  where
    genAImpl :
      (SortedMap Name String, SortedMap String Name) ->
      Arg ->
      m (SortedMap Name String, SortedMap String Name)
    genAImpl (n2s, s2n) a = do
      randN <- genSym "lamArg"
      let s = show randN
      let n = fromMaybe "" a.name
      pure (insert n s n2s, insert s n s2n)

export
normaliseTask : Elaboration m => List Arg -> TTImp -> m (TTImp, TTImp)
normaliseTask lamArgs lamRhs = do
  (n2s, s2n) <- genAliases lamArgs
  nT : Type <- check $ unBadHole $ typeDPair lamArgs
  nV : nT <- check $ unBadHole $ valDPair n2s lamArgs lamRhs
  nVQ <- quote nV
  newArgs <- decodeDPair lamArgs $ unMkDPair $ unBadHole $ unhole s2n nVQ
  let newLamTy = piAll `(Type) newArgs
  let newLam = foldr lam lamRhs newArgs
  pure (newLamTy, newLam)

export
specialiseDataArgs :
  Elaboration m =>
  (nsProvider : NamespaceProvider m) =>
  (unifier : CanUnify m) =>
  MonadLog m =>
  MonadError SpecialisationError m =>
  (namesInfo : NamesInfoInTypes) =>
  SpecialisationParams =>
  (resultName : Name) ->
  (lambdaArgs : List Arg) ->
  (lambdaRHS : TTImp) ->
  m (TypeInfo, List Decl)
specialiseDataArgs resultName fvArgs lambdaRHS =
  uncurry (specialiseDataRaw resultName) =<< normaliseTask fvArgs lambdaRHS

||| Perform a specialisation for a given type name and content lambda
|||
||| In order to generate a specialised type declaration equivalent to the following type alias:
||| ```
||| VF : Nat -> Type
||| VF n = Fin n
||| ```
||| ...you may use this function as follows:
||| ```
||| specialiseData `{VF} $ \n => Fin n
||| ```
export
specialiseDataLam :
  -- TaskLambda taskT =>
  Monad m =>
  Elaboration m =>
  (nsProvider : NamespaceProvider m) =>
  (unifier : CanUnify m) =>
  MonadError SpecialisationError m =>
  (namesInfo : NamesInfoInTypes) =>
  SpecialisationParams =>
  (resultName : Name) ->
  (0 task : taskT) ->
  m (TypeInfo, List Decl)
specialiseDataLam resultName task = do
  -- Quote spec lambda type
  resultKind <- quote taskT
  -- Quote spec lambda
  resultContent <- quote task
  specialiseDataRaw resultName resultKind resultContent


||| Perform a specialisation for a given type name and content lambda,
||| returning a list of declarations and failing on error
|||
||| In order to generate a specialised type declaration equivalent to the following type alias:
||| ```
||| VF : Nat -> Type
||| VF n = Fin n
||| ```
||| ...you may use this function as follows:
||| ```
||| specialiseDataLam'' `{VF} $ \n => Fin n
||| ```
export
specialiseDataLam'' :
  Elaboration m =>
  (nsProvider : NamespaceProvider m) =>
  (unifier : CanUnify m) =>
  SpecialisationParams =>
  -- TaskLambda taskT =>
  Name ->
  (0 task: taskT) ->
  m $ List Decl
specialiseDataLam'' resultName task = do
  tq <- quote task
  nit <- getNamesInfoInTypes' tq
  Right (specTy, decls) <-
    runEitherT {m} {e=SpecialisationError} $
      specialiseDataLam resultName task
  | Left err => fail "Specialisation error: \{show err}"
  pure decls

||| Perform a specialisation for a given type name and content lambda,
||| declaring the results and failing on error
|||
||| In order to declare a specialised type declaration equivalent to the following type alias:
||| ```
||| VF : Nat -> Type
||| VF n = Fin n
||| ```
||| ...you may use this function as follows:
||| ```
||| %runElab specialiseDataLam' `{VF} $ \n => Fin n
||| ```
export
specialiseDataLam' :
  Elaboration m =>
  (nsProvider : NamespaceProvider m) =>
  (unifier : CanUnify m) =>
  SpecialisationParams =>
  -- TaskLambda taskT =>
  Name ->
  (0 task: taskT) ->
  m ()
specialiseDataLam' resultName task =
  specialiseDataLam'' resultName task >>= declare
