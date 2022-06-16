module Control.Monad.State.Tuple

import public Control.Monad.State
import public Control.Monad.RWS

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

export
Monad m => MonadState sl (RWST r w (sl, sr) m) where
  get = Builtin.fst <$> get
  put = modify . mapFst . const

wrapFst' : Functor m => RWST r w sr m a -> RWST r w (sl, sr) m a
wrapFst' $ MkRWST rwst = MkRWST $ \r, (sx, sy), w => rwst r sy w <&> \(a, sy', w') => (a, (sx, sy'), w')

export
MonadState s (RWST r w sr m) => Monad m => MonadState s (RWST r w (sl, sr) m) where
  get = wrapFst' get
  put = wrapFst' . put
