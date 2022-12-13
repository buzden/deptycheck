module CheckDistribution

import DistrCheckCommon

%default total

bools : Gen Bool
bools = oneOf
          [ oneOf
              [ oneOf
                  [ empty
                  , oneOf
                      [ empty
                      , empty
                      , empty
                      ]
                  ]
              , pure True
              ]
          , pure False
          ]

main : IO ()
main = printVerdict bools
         [ coverWith 50.percent (== True)
         , coverWith 50.percent (== False)
         ]
