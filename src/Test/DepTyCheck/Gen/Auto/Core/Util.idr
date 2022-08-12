module Test.DepTyCheck.Gen.Auto.Core.Util

import public Data.Fin.Extra
import public Data.List.Equalities

import public Test.DepTyCheck.Gen.Auto.Derive

%default total

--- Utilities ---

||| Analyses whether the given expression can be an expression of free variables applies (maybe deeply) to a number of data constructors.
|||
||| Returns which of given free names are actually used in the given expression, in order of appearance in the expression.
||| Notice that applied free names may repeat as soon as one name is used several times in the given expression.
|||
||| Also, a function returning a bind expression (an expression replacing all free names with bind names (`IBindVar`))
||| is also returned.
||| This function requires bind variable names as input.
||| It returns correct bind expression only when all given bind names are different.
export
analyseDeepConsApp : Elaboration m =>
                     (freeNames : SortedSet Name) ->
                     (analysedExpr : TTImp) ->
                     m $ Maybe (appliedFreeNames : List Name ** (bindExpr : Fin appliedFreeNames.length -> TTImp) -> {-bind expression-} TTImp)
analyseDeepConsApp freeNames = catch . isD where

  isD : TTImp -> Elab (appliedFreeNames : List Name ** (Fin appliedFreeNames.length -> TTImp) -> TTImp)
  isD e = do

    -- Treat given expression as a function application to some name
    let (IVar _ lhsName, args) = unAppAny e
      | _ => fail "Not an application for some variable"

    -- Check if this is a free name
    let False = contains lhsName freeNames
      | True => if null args
                  then pure (singleton lhsName ** \f => f FZ)
                  else fail "Applying free name to some arguments"

    -- Check that this is an application to a constructor's name
    _ <- getCon lhsName -- or fail if `lhsName` is not a constructor

    -- Analyze deeply all the arguments
    deepArgs <- for args $ \anyApp => map (anyApp,) $ isD $ assert_smaller e $ getExpr anyApp

    -- Collect all the applied names and form proper application expression with binding variables
    pure $ foldl mergeApp ([] ** const $ var lhsName) deepArgs

    where
      mergeApp : (namesL : List Name ** (Fin namesL.length -> a) -> TTImp) ->
                 (AnyApp, (namesR : List Name ** (Fin namesR.length -> a) -> TTImp)) ->
                 (names : List Name ** (Fin names.length -> a) -> TTImp)
      mergeApp (namesL ** bindL) (anyApp, (namesR ** bindR)) = MkDPair (namesL ++ namesR) $ \bindNames => do
        let bindNames : Fin (namesL.length + namesR.length) -> a := rewrite sym $ lengthDistributesOverAppend namesL namesR in bindNames
        let lhs = bindL $ bindNames . indexSum . Left
        let rhs = bindR $ bindNames . indexSum . Right
        reAppAny1 lhs $ const rhs `mapExpr` anyApp
