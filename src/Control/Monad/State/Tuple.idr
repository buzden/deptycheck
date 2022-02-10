module Control.Monad.State.Tuple

import public Control.Monad.State

%default total

export
Monad m => MonadState l (StateT (l, r) m) where
  get = Builtin.fst <$> get
  put = modify . mapFst . const

wrapFst : Functor m => StateT r m a -> StateT (l, r) m a
wrapFst act = ST $ \(x, y) => mapFst (x,) <$> runStateT y act

export
MonadState s (StateT r m) => Monad m => MonadState s (StateT (l, r) m) where
  get = wrapFst get
  put = wrapFst . put
