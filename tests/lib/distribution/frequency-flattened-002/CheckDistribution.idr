module CheckDistribution

import Data.Either

import DistrCheckCommon

%default total

eb : Gen CanBeEmptyStatic $ Either Bool Bool
eb = oneOf
       $  Left  `mapAlternativesOf` frequency [ (2, pure True) ]
       ++ Right `mapAlternativesOf` frequency [ (1, pure True), (2, pure False) ]

main : IO ()
main = printVerdict eb
         [ coverWith 40.percent isLeft
         , coverWith 60.percent isRight

         , coverWith 60.percent $ (== True)  . fromEither
         , coverWith 40.percent $ (== False) . fromEither

         , coverWith 40.percent $ (== Left True)
         , coverWith 0.percent  $ (== Left False)
         , coverWith 20.percent $ (== Right True)
         , coverWith 40.percent $ (== Right False)
         ]
