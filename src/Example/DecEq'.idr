module Example.DecEq'

public export
data Dec' : Type -> Type where
  Yes : (a : x) -> Dec' x
  No : Dec' x

public export
interface DecEq' t where
  decEq' : (x1 : t) -> (x2 : t) -> Dec' (x1 = x2)
