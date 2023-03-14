module CheckDistribution

import DistrCheckCommon

%default total

-- Credits for this test to Aleksei Volkov @AlgebraicWolf

bools : Gen0 Bool
bools = oneOf
          [ oneOf
              [ empty
              , pure True
              ]
          , pure False
          ]

main : IO ()
main = printVerdict bools
         [ coverWith 50.percent (== True)
         , coverWith 50.percent (== False)
         ]
