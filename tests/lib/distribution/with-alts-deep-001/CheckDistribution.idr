module CheckDistribution

import Data.Either

import DistrCheckCommon

%default total

g1 : Gen NonEmpty Nat
g1 = oneOf
       [ elements [0, 1, 2, 3]
       , elements [4, 5]
       ]

g2 : Gen NonEmpty Nat
g2 = elements [10, 11, 12, 13, 14, 15]

g12 : Gen NonEmpty Nat
g12 = withDeepAlts 2 g1 g2

main : IO ()
main = printVerdict g12
         [ coverWith 8.3.percent (== 0)
         , coverWith 8.3.percent (== 1)
         , coverWith 8.3.percent (== 2)
         , coverWith 8.3.percent (== 3)
         , coverWith 8.3.percent (== 4)
         , coverWith 8.3.percent (== 5)
         , coverWith 8.3.percent (== 10)
         , coverWith 8.3.percent (== 11)
         , coverWith 8.3.percent (== 12)
         , coverWith 8.3.percent (== 13)
         , coverWith 8.3.percent (== 14)
         , coverWith 8.3.percent (== 15)
         ]
