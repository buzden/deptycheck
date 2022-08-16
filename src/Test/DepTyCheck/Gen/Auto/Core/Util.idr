module Test.DepTyCheck.Gen.Auto.Core.Util

import public Data.Fin.Extra
import public Data.List.Equalities

import public Decidable.Equality

import public Test.DepTyCheck.Gen.Auto.Derive

%default total

--- Utilities ---

public export
data ConsDetermInfo = DeterminedByType | NotDeterminedByType

export
Semigroup ConsDetermInfo where
  DeterminedByType <+> DeterminedByType = DeterminedByType
  NotDeterminedByType <+> x = x
  x <+> NotDeterminedByType = x

export
Monoid ConsDetermInfo where
  neutral = NotDeterminedByType

||| Determines which constructor's arguments would be definitely determined by fully known result type.
export
typeDeterminedArgs : (con : Con) -> Vect con.args.length ConsDetermInfo

public export
BindExprFun : Nat -> Type
BindExprFun n = (bindExpr : Fin n -> TTImp) -> {-bind expression-} TTImp

public export
DeepConsAnalysisRes : (collectConsDetermInfo : Bool) -> Type
DeepConsAnalysisRes c = (appliedFreeNames : List (FreeName c) ** BindExprFun appliedFreeNames.length)
  where
    FreeName : Bool -> Type
    FreeName False = Name
    FreeName True  = (Name, ConsDetermInfo)

MaybeConsDetermInfo : Bool -> Type
MaybeConsDetermInfo True  = ConsDetermInfo
MaybeConsDetermInfo False = Unit

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
                     (collectConsDetermInfo : Bool) ->
                     (freeNames : SortedSet Name) ->
                     (analysedExpr : TTImp) ->
                     m $ Maybe $ DeepConsAnalysisRes collectConsDetermInfo
analyseDeepConsApp ccdi freeNames = catch . isD where

  isD : TTImp -> Elab $ DeepConsAnalysisRes ccdi
  isD e = do

    -- Treat given expression as a function application to some name
    let (IVar _ lhsName, args) = unAppAny e
      | _ => fail "Not an application for some variable"

    -- Check if this is a free name
    let False = contains lhsName freeNames
      | True => if null args
                  then do
                    let n = if ccdi then (lhsName, neutral) else lhsName
                    pure (singleton n ** \f => f FZ)
                  else fail "Applying free name to some arguments"

    -- Check that this is an application to a constructor's name
    con <- getCon lhsName -- or fail if `lhsName` is not a constructor

    -- Get equality of arguments lengths at definition- and call-site
    let Yes lengthsCorrect = args.length `decEq` con.args.length
      | No _ => fail "INTERNAL ERROR: lengths do not correspond"

    -- Aquire type-determination info, if needed
    let typeDetermInfo : Vect con.args.length (MaybeConsDetermInfo ccdi) := if ccdi then typeDeterminedArgs con else replicate _ ()
    -- TODO to think can the order be incorrect, say, implicit arguments applied not in the same order as defined?

    -- Analyze deeply all the arguments
    deepArgs <- for (Vect.fromList args `zip` rewrite lengthsCorrect in typeDetermInfo) $
      \(anyApp, typeDetermined) => do
        subResult <- isD $ assert_smaller e $ getExpr anyApp
        let subResult = if ccdi then mapSnd (<+> typeDetermined) `mapLstDPair` subResult else subResult
        pure (anyApp, subResult)

    -- Collect all the applied names and form proper application expression with binding variables
    pure $ foldl mergeApp ([] ** const $ var lhsName) deepArgs

    where
      mergeApp : DeepConsAnalysisRes ccdi -> (AnyApp, DeepConsAnalysisRes ccdi) -> DeepConsAnalysisRes ccdi
      mergeApp (namesL ** bindL) (anyApp, (namesR ** bindR)) = MkDPair (namesL ++ namesR) $ \bindNames => do
        let bindNames : Fin (namesL.length + namesR.length) -> _ := rewrite sym $ lengthDistributesOverAppend namesL namesR in bindNames
        let lhs = bindL $ bindNames . indexSum . Left
        let rhs = bindR $ bindNames . indexSum . Right
        reAppAny1 lhs $ const rhs `mapExpr` anyApp

      mapLstDPair : (a -> b) -> (x : List a ** BindExprFun x.length) -> (x : List b ** BindExprFun x.length)
      mapLstDPair f (lst ** d) = (map f lst ** rewrite lengthMap {f} lst in d)
