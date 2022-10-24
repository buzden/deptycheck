module CheckDistribution

import Data.Maybe

import DistrCheckCommon

%default total

bools : Gen Bool
bools = elements [True, False]

eb : Gen $ Maybe Bool
eb = oneOf
       [ pure Nothing
       , Just <$> bools
       ]

main : IO ()
main = printVerdict eb
         [ coverWith 50.percent isNothing
         , coverWith 50.percent isJust

         , coverWith 25.percent $ (== Just True)
         , coverWith 25.percent $ (== Just False)
         ]
