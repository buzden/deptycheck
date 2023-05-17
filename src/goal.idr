import Test.DepTyCheck.Gen

data X : Type

data Y : Type

data F : Type

fun : Y -> F

data Z : Type

data B : X -> F -> Type

data C : X -> Type

data D : Y -> Type

data D' : Y -> Type

data E : X -> Z -> Type

data T : Type where
  MkA : (x : X) -> (y : Y) -> (z : Z) -> B x (fun y) -> C x -> D y -> D' y -> E x z -> T

genB_f : (f : F) -> Gen (x ** B x f)
genB_xf : (x : X) -> (f : F) -> Gen (B x f)

genC : Gen (x ** C x)
genC_x : (x : _) -> Gen (C x)

genD : Gen (y ** D y)
genD_y : (y : _) -> Gen (D y)

genD' : Gen (y ** D' y)
genD'_y : (y : _) -> Gen (D' y)

genE : Gen (x ** z ** E x z)
genE_x : (x : _) -> Gen (z ** E x z)

genT : Gen T
genT = oneOf

  [ -- (E + D) * (D' + B + C)
    do ((x ** z ** e), (y ** d)) <- (,) <$> genE <*> genD
       (d', b, c) <- (,,) <$> genD'_y y <*> genB_xf x (fun y) <*> genC_x x
       pure $ MkA x y z b c d d' e

  , -- D * (D' + B * (C + E))
    do (y ** d) <- genD
       let l = genD'_y y
       let r : Gen (x ** (B x (fun y), C x, (z ** E x z))) := do
         (x ** b) <- genB_f (fun y)
         (c, (z ** e)) <- (,) <$> genC_x x <*> genE_x x
         pure (x ** (b, c, (z ** e)))
       (d', (x ** (b, c, (z ** e)))) <- (,) <$> l <*> r
       pure $ MkA x y z b c d d' e

  , -- (C + D) * (B + D' + E)
    do ((x ** c), (y ** d)) <- (,) <$> genC <*> genD
       (b, d', (z ** e)) <- (,,) <$> genB_xf x (fun y) <*> genD'_y y <*> genE_x x
       pure $ MkA x y z b c d d' e

  -- ... and other orders, say, D * (D' + C * (B + E)), (E + D') * (D + B + C)
  ]
