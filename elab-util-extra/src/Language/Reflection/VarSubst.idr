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

TTOp : (Type -> Type) -> Type
TTOp m = TTImp -> m TTImp -> m TTImp

NameSet : Type
NameSet = SortedSet Name

insertM : Maybe Name -> NameSet -> NameSet
insertM Nothing = id
insertM (Just x) = insert x

data ShadowingInfo : Type where
  MkSI : (shadowedNames : NameSet) -> ShadowingInfo

shadowedNames : ShadowingInfo -> NameSet
shadowedNames (MkSI names) = names

(.shadowedNames) : ShadowingInfo -> NameSet
(.shadowedNames) (MkSI names) = names

isShadowed : Name -> ShadowingInfo -> Bool
isShadowed n = contains n . shadowedNames

parameters {auto _ : MonadReader ShadowingInfo m}
           (f: TTOp m)
  mutual
    doPiInfo : PiInfo TTImp -> m $ PiInfo TTImp
    doPiInfo (DefImplicit x) = DefImplicit <$> doTTImp x
    doPiInfo x = pure x

    doTTImp : TTImp -> m TTImp
    doTTImp = assert_total mapATTImp' provideSI

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

data QuoteInfo : Type where
  MkQI : (isQuote : Bool) -> QuoteInfo

isQuote : QuoteInfo -> Bool
isQuote (MkQI iq) = iq

(.isQuote) : QuoteInfo -> Bool
(.isQuote) (MkQI iq) = iq

provideQI : MonadReader QuoteInfo m =>
            (f: TTOp m) ->
            TTOp m
provideQI f b@(IQuote fc t) newM = f b $ local {isQuote := True} newM
provideQI f b@(IQuoteDecl fc decls) newM = f b $ local {isQuote := True} newM
provideQI f b@(IUnquote fc t) newM = f b $ local {isQuote := False} newM
provideQI f b newM = f b newM

provideCtx : Monad m =>
             MonadReader QuoteInfo m =>
             MonadReader ShadowingInfo m =>
             TTOp m -> TTOp m
provideCtx = provideSI . provideQI

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

public export
containsVariable : Name -> TTImp -> Bool
containsVariable n =
  execState False .
    mapTTOp (containsVariableImpl n)

collectVariablesImpl : Monad m =>
                       MonadReader QuoteInfo m =>
                       MonadReader ShadowingInfo m =>
                       MonadState NameSet m =>
                       Name -> TTOp m
collectVariablesImpl n (IVar _ n') m = do
  if n == n'
     && not !(asks isQuote)
     && not !(asks $ isShadowed n)
     then modify (insert n) *> m
     else m
collectVariablesImpl n tt m = m

public export
usesVariables : Name -> TTImp -> NameSet
usesVariables n =
  execState empty .
    mapTTOp (collectVariablesImpl n)

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

public export
substituteVariables : SortedMap Name TTImp -> TTImp -> TTImp
substituteVariables vMap =
  runIdentity .
    mapTTOp (substituteVariablesImpl vMap)

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

public export
substituteBind : SortedMap Name TTImp -> TTImp -> TTImp
substituteBind vMap = do
  runIdentity . mapTTOp (substituteBindImpl vMap)
