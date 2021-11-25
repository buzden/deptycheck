module Control.Monad.State.Tuple

import public Control.Monad.State

--- For pairs ---

export
Monad m => MonadState l (StateT (l, _) m) where
  get = Builtin.fst <$> get
  put = modify . mapFst . const

export
Monad m => MonadState r (StateT (_, r) m) where
  get = Builtin.snd <$> get
  put = modify . mapSnd . const

--- For triples ---

export
Monad m => MonadState s (StateT (_, s, _) m) where
  get = Builtin.fst . snd <$> get
  put = modify . mapSnd . mapFst . const

export
Monad m => MonadState s (StateT (_, _, s) m) where
  get = Builtin.snd . snd <$> get
  put = modify . mapSnd . mapSnd . const
