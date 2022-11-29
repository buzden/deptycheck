module CheckDistribution

import DistrCheckCommon

%default total

bools : Gen Bool
bools = oneOf
        [ frequency
            [ (10000000, pure True)
            , (10000000, pure False)
            ]
        , frequency
            [ (20000000, pure True)
            , (20000000, pure False)
            ]
        ]

main : IO ()
main = printVerdict bools
         [ coverWith 50.percent (== True)
         , coverWith 50.percent (== False)
         ]
