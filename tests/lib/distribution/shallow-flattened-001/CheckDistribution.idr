module CheckDistribution

import Data.Either

import DistrCheckCommon

%default total

bools : Gen Bool
bools = elements [True, False]

eb : Gen $ Either Bool Bool
eb = oneOf
       $  Left  `mapAlternativesOf` bools
       ++ Right `mapAlternativesOf` bools

main : IO ()
main = printVerdict eb
         [ coverWith 50.percent isLeft
         , coverWith 50.percent isRight

         , coverWith 50.percent $ (== True)  . fromEither
         , coverWith 50.percent $ (== False) . fromEither

         , coverWith 25.percent $ (== Left True)
         , coverWith 25.percent $ (== Left False)
         , coverWith 25.percent $ (== Right True)
         , coverWith 25.percent $ (== Right False)
         ]
