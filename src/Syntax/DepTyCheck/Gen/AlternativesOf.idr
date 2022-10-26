module Syntax.DepTyCheck.Gen.AlternativesOf

import Test.DepTyCheck.Gen

%default total

-- Support for idiom brackets and monadic syntax --

export
pure : a -> List (Lazy (Gen a))
pure x = [ pure x ]

export
(<*>) : List (Lazy (Gen $ a -> b)) -> List (Lazy (Gen a)) -> List (Lazy (Gen b))
(<*>) xs ys = with Prelude.(<*>) [| ap xs ys |] where
  ap : Lazy (Gen (a -> b)) -> Lazy (Gen a) -> Lazy (Gen b)
  ap x y = x <*> y

export
(>>=) : List (Lazy (Gen a)) -> (a -> List (Lazy (Gen b))) -> List (Lazy (Gen b))
xs >>= f = with Prelude.(>>=) xs >>= alternativesOf . (>>= oneOf . f) . force

namespace HeterogenousL

--  export %inline
--  (<*>) : Gen (a -> b) -> List (Lazy (Gen a)) -> List (Lazy (Gen b))
--  f <*> b = [ f ] <*> b

  export %inline
  (>>=) : Gen a -> (a -> List (Lazy (Gen b))) -> List (Lazy (Gen b))
  gen >>= f = [ gen ] >>= f

--namespace HeterogenousR
--
--  export %inline
--  (<*>) : List (Lazy (Gen $ a -> b)) -> Gen a -> List (Lazy (Gen b))
--  f <*> b = f <*> [ b ]
