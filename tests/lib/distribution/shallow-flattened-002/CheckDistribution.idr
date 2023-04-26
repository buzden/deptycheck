module CheckDistribution

import Data.Maybe

import DistrCheckCommon

%default total

bools : Gen MaybeEmpty Bool
bools = elements [True, False]

eb : Gen MaybeEmpty $ Maybe Bool
eb = oneOf
       $  ( pure Nothing )
       :: ( Just <$> alternativesOf bools )

main : IO ()
main = printVerdict eb
         [ coverWith 33.percent isNothing
         , coverWith 66.percent isJust

         , coverWith 33.percent $ (== Just True)
         , coverWith 33.percent $ (== Just False)
         ]
