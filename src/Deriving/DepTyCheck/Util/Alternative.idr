module Deriving.DepTyCheck.Util.Alternative

%default total

-------------------------------
--- `Alternative` utilities ---
-------------------------------

public export %inline
atLeast : Alternative f => a -> f a -> f a
atLeast v = (<|> pure v)

public export %inline
optional : Alternative f => f a -> f (Maybe a)
optional = atLeast Nothing . map Just

-- `whenT b x` ~ `guard b $> x`
public export %inline
whenT : Alternative f => Bool -> a -> f a
whenT True  x = pure x
whenT False _ = empty
