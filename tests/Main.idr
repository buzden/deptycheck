module Main

import Test.Golden

lazierList : TestPool
lazierList = MkTestPool "Lazier list" [] Nothing $ ("lazier/" ++) <$>
  [ "basic001"
  -- TODO to add tests to check that lazier list is really lazy. "laziness001"
  ]

genMonad : TestPool
genMonad = MkTestPool "The `Gen` monad" [] Nothing $ ("gen-monad/" ++) <$>
  [ "basic001"
  ]

autoGen : TestPool
autoGen = MkTestPool "Autogeneration of `Gen`s" [] Nothing $ ("auto-gen/" ++) <$>
  [ "inputvalidation001"
  , "canonicsig001"
  ]

main : IO ()
main = do
  runner
    [ lazierList
    , genMonad
    , autoGen
    ]
