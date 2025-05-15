module Deriving.DepTyCheck.Util.DeepConsApp

import public Control.Monad.Error.Interface
import public Control.Monad.Writer.Interface

import public Data.Fin.Split
import public Data.List.Ex
import public Data.SortedSet
import public Data.Vect.Extra

import public Language.Reflection.Compat.TypeInfo

%default total

public export
data ConsDetermInfo = DeterminedByType | NotDeterminedByType

export
Cast Bool ConsDetermInfo where
  cast True  = DeterminedByType
  cast False = NotDeterminedByType

export
Cast ConsDetermInfo Bool where
  cast DeterminedByType    = True
  cast NotDeterminedByType = False

export
Semigroup ConsDetermInfo where
  DeterminedByType <+> DeterminedByType = DeterminedByType
  NotDeterminedByType <+> x = x
  x <+> NotDeterminedByType = x

export
Monoid ConsDetermInfo where
  neutral = NotDeterminedByType

public export
BindExprFun : Nat -> Type
BindExprFun n = (bindExpr : Fin n -> TTImp) -> {-bind expression-} TTImp

public export
DeepConsAnalysisRes : (collectConsDetermInfo : Bool) -> Type
DeepConsAnalysisRes False = List Name
DeepConsAnalysisRes True = (appliedFreeNames : List (Name, ConsDetermInfo) ** BindExprFun appliedFreeNames.length)

MaybeConsDetermInfo : Bool -> Type
MaybeConsDetermInfo True  = ConsDetermInfo
MaybeConsDetermInfo False = Unit

||| Analyses whether the given expression can be an expression of free variables applied (maybe deeply) to a number of data constructors.
|||
||| Returns which of given free names are actually used in the given expression, in order of appearance in the expression.
||| Notice that applied free names may repeat as soon as one name is used several times in the given expression.
|||
||| Also, a function returning a bind expression (an expression replacing all free names with bind names (`IBindVar`))
||| is also returned.
||| This function requires bind variable names as input.
||| It returns correct bind expression only when all given bind names are different.
export
analyseDeepConsApp : NamesInfoInTypes =>
                     MonadError String m =>
                     MonadWriter (List (Name, ConsDetermInfo)) m =>
                     (collectConsDetermInfo : Bool) ->
                     (freeNames : SortedSet Name) ->
                     (analysedExpr : TTImp) ->
                     m $ DeepConsAnalysisRes collectConsDetermInfo
analyseDeepConsApp ccdi freeNames = isD where

  isD : TTImp -> m $ DeepConsAnalysisRes ccdi
  isD e = do

    -- Treat given expression as a function application to some name
    let (IVar _ lhsName, args) = unAppAny e
      | (IType {}   , _) => pure $ noFree e
      | (IPrimVal {}, _) => pure $ noFree e
      | _ => throwError "not an application to a variable"

    -- Remember the name and determination for the case of a future failure
    when (null args) $ tell [(lhsName, cast $ not ccdi)]

    -- Check that this is an application to a constructor's name
    let Just con = lookupCon lhsName
      | Nothing => if ccdi then throwError "name `\{lhsName}` is not a constructor" else pure $ noFree implicitTrue

    -- Acquire type-determination info, if needed
    typeDetermInfo <- if ccdi then assert_total {- `ccdi` is `True` here when `False` inside -} $ typeDeterminedArgs con else pure neutral
    let _ : Vect con.args.length (MaybeConsDetermInfo ccdi) := typeDetermInfo

    -- Check if this is a free name. This must go AFTER type determination check, since it should write determination info before we may fail here
    let False = contains lhsName freeNames
      | True => if null args
                  then pure $ if ccdi then ([(lhsName, neutral)] ** \f => f FZ) else [lhsName]
                  else throwError "applying free name to some arguments"

    let Just typeDetermInfo = reorder typeDetermInfo
      | Nothing => throwError "INTERNAL ERROR: cannot reorder formal determ info along with a call to a constructor"

    -- Analyze deeply all the arguments
    deepArgs <- for (args.asVect `zip` typeDetermInfo) $ \(anyApp, typeDetermined) => do
      subResult <- isD $ assert_smaller e $ getExpr anyApp
      let subResult = if ccdi then mapSnd (<+> typeDetermined) `mapLstDPair` subResult else subResult
      pure (anyApp, subResult)

    -- Collect all the applied names and form proper application expression with binding variables
    pure $ foldl (mergeApp _) (noFree $ var lhsName) deepArgs

    where
      noFree : TTImp -> DeepConsAnalysisRes ccdi
      noFree e = if ccdi then ([] ** const e) else []

      mergeApp : (ccdi : _) -> DeepConsAnalysisRes ccdi -> (AnyApp, DeepConsAnalysisRes ccdi) -> DeepConsAnalysisRes ccdi
      mergeApp False namesL (_, namesR) = namesL ++ namesR
      mergeApp True (namesL ** bindL) (anyApp, (namesR ** bindR)) = MkDPair (namesL ++ namesR) $ \bindNames => do
        let bindNames : Fin (namesL.length + namesR.length) -> _ := rewrite sym $ lengthConcat namesL namesR in bindNames
        let lhs = bindL $ bindNames . indexSum . Left
        let rhs = bindR $ bindNames . indexSum . Right
        reAppAny1 lhs $ const rhs `mapExpr` anyApp

      mapLstDPair : (a -> b) -> (x : List a ** BindExprFun x.length) -> (x : List b ** BindExprFun x.length)
      mapLstDPair f (lst ** d) = (map f lst ** rewrite lengthMap {f} lst in d)

      ||| Determines which constructor's arguments would be definitely determined by fully known result type.
      typeDeterminedArgs : (con : Con) -> m $ Vect con.args.length ConsDetermInfo
      typeDeterminedArgs con = do
        let conArgNames = fromList $ mapI con.args $ \idx, arg => (argName arg, idx)
        determined <- analyseDeepConsApp False (SortedSet.keySet conArgNames) con.type
        let determined = mapMaybe (lookup' conArgNames) determined
        pure $ map cast $ presenceVect $ fromList determined

      reorder : {formalArgs : List Arg} -> {apps : List AnyApp} -> Vect formalArgs.length a -> Maybe $ Vect apps.length a
      reorder xs = reorder' (fromList formalArgs `zip` xs) apps where
        reorder' : Vect n (Arg, a) -> (apps : List AnyApp) -> Maybe $ Vect apps.length a
        reorder' xs        []      = if isJust $ find ((== ExplicitArg) . piInfo . fst) xs
                                       then Nothing {- not all explicit parameters are used -} else Just []
        reorder' []        (_::_)  = Nothing
        reorder' xs@(_::_) (a::as) = do
          let searchFun : Arg -> Bool
              searchFun = case a of
                            PosApp _      => (== ExplicitArg) . piInfo
                            NamedApp nm _ => \na => isImplicit na.piInfo && na.name == Just nm
                            AutoApp _     => (== AutoImplicit) . piInfo
                            WithApp _     => const False
          let Just i = findIndex (searchFun . fst) xs
            | Nothing => Nothing
          let restxs = deleteAt i xs
          (snd (index i xs) ::) <$> reorder' restxs as
