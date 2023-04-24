module CheckDistribution

import Data.Either

import DistrCheckCommon

%default total

eb : Gen CanBeEmptyStatic $ Either Bool Bool
eb = frequency
       [ ( 1, Left  <$> elements [True, False] )
       , ( 2, Right <$> frequency [ (4, pure True), (5, pure False) ] )
       ]

main : IO ()
main = printVerdict eb
         [ coverWith 33.percent isLeft
         , coverWith 66.percent isRight

         , coverWith 46.3.percent $ (== True)  . fromEither
         , coverWith 53.7.percent $ (== False) . fromEither

         , coverWith 16.6.percent $ (== Left True)
         , coverWith 16.6.percent $ (== Left False)
         , coverWith 29.6.percent $ (== Right True)
         , coverWith 37.percent   $ (== Right False)
         ]
