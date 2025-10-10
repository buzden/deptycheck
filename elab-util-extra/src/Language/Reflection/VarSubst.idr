module Language.Reflection.VarSubst

import public Data.SortedSet
import public Data.SortedMap
import public Data.Maybe
import public Language.Reflection
import public Language.Reflection.Pretty
import public Language.Reflection.TTImp
import public Language.Reflection.TT
import public Language.Reflection.Util
import public Control.Monad.Identity
import public Control.Monad.Reader
import public Control.Monad.Reader.Tuple
import public Control.Monad.State

||| Monadic operation on a TTImp
TTOp : (Type -> Type) -> Type
TTOp m = TTImp -> m TTImp -> m TTImp

||| SortedSet of Names
public export
NameSet : Type
NameSet = SortedSet Name

||| Insert `Maybe Name`'s content into a NameSet
insertM : Maybe Name -> NameSet -> NameSet
insertM Nothing = id
insertM (Just x) = insert x

||| Information about variable shadowing
record ShadowingInfo where
  constructor MkSI
  ||| Set of shadowed names
  shadowedNames : NameSet

||| Check if a variable is shadowed
isShadowed : Name -> ShadowingInfo -> Bool
isShadowed n = contains n . shadowedNames

parameters {auto _ : MonadReader ShadowingInfo m}
           (f: TTOp m)
  mutual
    ||| Provide a ShadowingInfo for an operation on a TTImp over a PiInfo TTImp
    doPiInfo : PiInfo TTImp -> m $ PiInfo TTImp
    doPiInfo (DefImplicit x) = DefImplicit <$> doTTImp x
    doPiInfo x = pure x

    ||| Provide a ShadowingInfo for an operation on a TTImp
    doTTImp : TTImp -> m TTImp
    doTTImp = assert_total mapATTImp' provideSI

    ||| Provide a ShadowingInfo for an operation on a TTImp
    provideSI : TTOp m
    provideSI b@(IPi fc count pinfo mn argTy lamTy) newM = do
      pinfo <- doPiInfo pinfo
      argTy <- doTTImp argTy
      lamTy <- local {shadowedNames $= insertM mn} $ doTTImp lamTy
      f b $ pure $ IPi fc count pinfo mn argTy lamTy
    provideSI b@(ILam fc count pinfo mn argTy lamTy) newM = do
      pinfo <- doPiInfo pinfo
      argTy <- doTTImp argTy
      lamTy <- local {shadowedNames $= insertM mn} $ doTTImp lamTy
      f b $ pure $ ILam fc count pinfo mn argTy lamTy
    provideSI b@(ILet fc lhsFC c n nTy nVal scope) newM = do
      nTy <- doTTImp nTy
      nVal <- doTTImp nVal
      scope <- local {shadowedNames $= insert n} $ doTTImp scope
      f b $ pure $ ILet fc lhsFC c n nTy nVal scope
    provideSI b newM = do
      f b newM

||| Information about quoting
record QuoteInfo where
  constructor MkQI
  ||| Indicator of being in a quote
  isQuote : Bool

||| Provide QuoteInfo for a monadic operation on a TTImp
provideQI : MonadReader QuoteInfo m =>
            (f: TTOp m) ->
            TTOp m
provideQI f b@(IQuote fc t) newM = f b $ local {isQuote := True} newM
provideQI f b@(IQuoteDecl fc decls) newM = f b $ local {isQuote := True} newM
provideQI f b@(IUnquote fc t) newM = f b $ local {isQuote := False} newM
provideQI f b newM = f b newM

||| Provide QuoteInfo and ShadowingInfo for a monadic operation on a TTImp
provideCtx : Monad m =>
             MonadReader QuoteInfo m =>
             MonadReader ShadowingInfo m =>
             TTOp m -> TTOp m
provideCtx = provideSI . provideQI

||| Run a monadic operation requiring ShadowingInfo and QuoteInfo on a TTImp
mapTTOp : Monad m => TTOp (ReaderT (ShadowingInfo, QuoteInfo) m) -> TTImp -> m TTImp
mapTTOp op t = do
  let readerOp = mapATTImp' . provideCtx $ op
  runReaderT (MkSI empty, MkQI False) $ readerOp t

containsVariableImpl : Monad m =>
                       MonadReader QuoteInfo m =>
                       MonadReader ShadowingInfo m =>
                       MonadState Bool m =>
                       Name -> TTOp m
containsVariableImpl n (IVar _ n') m =
  if n == n'
     && not !(asks isQuote)
     && not !(asks $ isShadowed n)
  then put True *> m
  else m
containsVariableImpl n tt m = m

||| Check if a TTImp contains a variable
public export
containsVariable : Name -> TTImp -> Bool
containsVariable n =
  execState False .
    mapTTOp (containsVariableImpl n)

collectVariablesImpl : Monad m =>
                       MonadReader QuoteInfo m =>
                       MonadReader ShadowingInfo m =>
                       MonadState NameSet m =>
                       TTOp m
collectVariablesImpl (IVar _ n) m = do
  if not !(asks isQuote)
     && not !(asks $ isShadowed n)
     then modify (insert n) *> m
     else m
collectVariablesImpl tt m = m

||| Calculate a set of used variables
public export
usesVariables : TTImp -> NameSet
usesVariables =
  execState empty .
    mapTTOp (collectVariablesImpl)

substituteVariablesImpl : Monad m =>
                          MonadReader QuoteInfo m =>
                          MonadReader ShadowingInfo m =>
                          SortedMap Name TTImp -> TTOp m
substituteVariablesImpl vMap (IVar fc n) m =
  if not !(asks isQuote)
     && not !(asks $ isShadowed n)
  then
    fromMaybe m $ pure <$> lookup n vMap
  else m
substituteVariablesImpl _ _ m = m

||| Substitute all occurrences of each variable with the given expression
public export
substituteVariables : SortedMap Name TTImp -> TTImp -> TTImp
substituteVariables vMap =
  runIdentity .
    mapTTOp (substituteVariablesImpl vMap)

||| Substitute all occurrences of given variable with given expression
public export
substituteVariable : Name -> TTImp -> TTImp -> TTImp
substituteVariable n t =
  runIdentity .
    mapTTOp (substituteVariablesImpl $ insert n t empty)


substituteBindImpl : Monad m =>
                     MonadReader QuoteInfo m =>
                     MonadReader ShadowingInfo m =>
                     SortedMap Name TTImp -> TTOp m
substituteBindImpl vMap (IVar fc n) m =
  if not !(asks isQuote)
     && not !(asks $ isShadowed n)
  then
    fromMaybe m $ pure <$> lookup n vMap
  else m
substituteBindImpl vMap (IBindVar fc n) m =
  if not !(asks isQuote)
     && not !(asks $ isShadowed n)
  then
    fromMaybe m $ pure <$> lookup n vMap
  else m
substituteBindImpl _ _ m = m

||| Substitute all variable and BindVar occurrences with given
public export
substituteBind : SortedMap Name TTImp -> TTImp -> TTImp
substituteBind vMap = do
  runIdentity . mapTTOp (substituteBindImpl vMap)
