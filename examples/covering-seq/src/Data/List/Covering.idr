module Data.List.Covering

import public Data.Fin
import Data.String

%default total

namespace BitMask

  -- BitMask n ~~ Vect n Bool
  public export
  data BitMask : (bits : Nat) -> Type where
    Nil  : BitMask 0
    (::) : Bool -> BitMask n -> BitMask (S n)

  export
  Interpolation (BitMask n) where
    interpolate []          = ""
    interpolate (True ::bs) = "1\{bs}"
    interpolate (False::bs) = "0\{bs}"

  public export
  update : Fin n -> (newValue : Bool) -> BitMask n -> BitMask n
  update FZ     v (_::bs) = v::bs
  update (FS n) v (b::bs) = b :: update n v bs

  namespace Index

    public export
    data AtIndex : (n : Nat) -> Fin n -> BitMask n -> Bool -> Type where
      Here  : AtIndex (S n) FZ (b::bs) b
      There : AtIndex n i bs v -> AtIndex (S n) (FS i) (b::bs) v

    public export
    data AllBitsAre : (n : Nat) -> Bool -> BitMask n -> Type where
      Finish   : AllBitsAre Z b []
      Continue : AllBitsAre n b bs -> AllBitsAre (S n) b (b::bs)

  export
  setBits : BitMask n -> List $ Fin n
  setBits []         = []
  setBits $ True ::bs = FZ :: (FS <$> setBits bs)
  setBits $ False::bs = FS <$> setBits bs

-- Contains all and only mentions (hits) of values enabled in the given bitmask in any order interleaved with some arbitrary numbers (misses).
public export
data CoveringSequence : (n : Nat) -> BitMask n -> Type where
  End  : AllBitsAre n False bs => CoveringSequence n bs
  Miss : Nat -> CoveringSequence n bs -> CoveringSequence n bs
  Hit  : (i : Fin n) -> AtIndex n i bs True => CoveringSequence n (update i False bs) -> CoveringSequence n bs

public export
hits : CoveringSequence n bs -> List $ Fin n
hits End         = []
hits $ Miss k xs = hits xs
hits $ Hit i xs  = i :: hits xs

export
Interpolation (CoveringSequence n bs) where
  interpolate = joinBy " " . asList where
    asList : forall n, bs. CoveringSequence n bs -> List String
    asList End         = []
    asList $ Miss k xs = show k :: asList xs
    asList $ Hit i xs  = "[\{show i}]" :: asList xs
