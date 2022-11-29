module CheckDistribution

import Data.Either

import DistrCheckCommon

%default total

eb : Gen $ Either Bool Bool
eb = oneOf
       $  Left  `mapAlternativesOf` frequency [ (1000000, pure True), (4000000, pure False) ]
       ++ Right `mapAlternativesOf` frequency [ (1, pure True), (4, pure False) ]

main : IO ()
main = printVerdict eb
         [ coverWith 100.percent isLeft
         , coverWith 0.percent isRight

         , coverWith 20.percent $ (== True)  . fromEither
         , coverWith 80.percent $ (== False) . fromEither

         , coverWith 20.percent $ (== Left True)
         , coverWith 80.percent $ (== Left False)
         , coverWith 0.percent $ (== Right True)
         , coverWith 0.percent $ (== Right False)
         ]
