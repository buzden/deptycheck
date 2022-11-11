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
         [ coverWith 50.percent isLeft
         , coverWith 50.percent isRight

         , coverWith 20.percent $ (== True)  . fromEither
         , coverWith 80.percent $ (== False) . fromEither

         , coverWith 10.percent $ (== Left True)
         , coverWith 40.percent $ (== Left False)
         , coverWith 10.percent $ (== Right True)
         , coverWith 40.percent $ (== Right False)
         ]
