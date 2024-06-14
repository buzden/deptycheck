||| Functions for collections of `Fin`s
module Data.Fin.Lists

import public Data.Fin

public export
rangeFrom0To : Fin n -> List (Fin n)
rangeFrom0To FZ     = [FZ]
rangeFrom0To (FS x) = FZ :: (FS <$> rangeFrom0To x)

public export
rangeFromTo : Fin n -> Fin n -> List (Fin n)
rangeFromTo FZ     FZ     = [FZ]
rangeFromTo FZ     r      = rangeFrom0To r
rangeFromTo l      FZ     = reverse $ rangeFrom0To l
rangeFromTo (FS l) (FS r) = FS <$> rangeFromTo l r

export
allGreaterThan : {n : _} -> Fin n -> List (Fin n)
allGreaterThan curr = case strengthen $ FS curr of
                        Nothing => []
                        Just next => next :: allGreaterThan (assert_smaller curr next) -- `next` is closer to the upper bound than `curr`
