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
g12 = g1 `withAlts` g2

main : IO ()
main = printVerdict g12
         [ coverWith 3.125.percent (== 0)
         , coverWith 3.125.percent (== 1)
         , coverWith 3.125.percent (== 2)
         , coverWith 3.125.percent (== 3)

         , coverWith 6.25.percent (== 4)
         , coverWith 6.25.percent (== 5)

         , coverWith 12.5.percent (== 10)
         , coverWith 12.5.percent (== 11)
         , coverWith 12.5.percent (== 12)
         , coverWith 12.5.percent (== 13)
         , coverWith 12.5.percent (== 14)
         , coverWith 12.5.percent (== 15)
         ]
