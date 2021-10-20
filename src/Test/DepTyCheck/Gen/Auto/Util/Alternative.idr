module Test.DepTyCheck.Gen.Auto.Util.Alternative

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
