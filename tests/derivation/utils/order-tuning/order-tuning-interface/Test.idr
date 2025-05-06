module Test

import Deriving.DepTyCheck.Gen.ForOneTypeConRhs.Impl

%default total

data X : Nat -> Type where
  MkX1 : (n : Nat) -> (m : Nat) -> X m
  MkX2 : X 4

namespace OnlyNumbers

  GenOrderTuning "MkX1".dataCon where
    isConstructor = itIsConstructor
    deriveFirst _ _ = [1, 0]

namespace OnlyNames

  GenOrderTuning "MkX1".dataCon where
    isConstructor = itIsConstructor
    deriveFirst _ _ = [`{m}, `{n}]

namespace MixedNumbersAndNames

  GenOrderTuning "MkX1".dataCon where
    isConstructor = itIsConstructor
    deriveFirst _ _ = [`{m}, 0]

namespace OnlyNothing

  GenOrderTuning "MkX2".dataCon where
    isConstructor = itIsConstructor
    deriveFirst _ _ = []

-- Non-existent index
failing "Can't find an implementation"
  GenOrderTuning "MkX2".dataCon where
    isConstructor = itIsConstructor
    deriveFirst _ _ = [0]

-- Non-existent name
failing "Can't find an implementation"
  GenOrderTuning "MkX2".dataCon where
    isConstructor = itIsConstructor
    deriveFirst _ _ = [`{x}]

-- Mix of normal and non-existent index
failing "Can't find an implementation"
  GenOrderTuning "MkX2".dataCon where
    isConstructor = itIsConstructor
    deriveFirst _ _ = [0, 2, 1]

-- Mix of normal index, normal name and non-existent index
failing "Can't find an implementation"
  GenOrderTuning "MkX2".dataCon where
    isConstructor = itIsConstructor
    deriveFirst _ _ = [0, 2, `{n}]

-- Mix of normal and non-existent name
failing "Can't find an implementation"
  GenOrderTuning "MkX2".dataCon where
    isConstructor = itIsConstructor
    deriveFirst _ _ = [`{n}, `{k}]

-- Mix of normal name, normal index and non-existent name
failing "Can't find an implementation"
  GenOrderTuning "MkX2".dataCon where
    isConstructor = itIsConstructor
    deriveFirst _ _ = [`{n}, `{k}, 0]
