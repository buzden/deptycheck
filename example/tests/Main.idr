module Main

import Test.Golden

pilLanguage : TestPool
pilLanguage = MkTestPool "PIL usage examples" [] Nothing $ ("pil/" ++) <$>
  [ "basic001"
  , "usage001"
  -- TODO to add positive and negative tests for particular language constructions
  ]

pilGenerators : TestPool
pilGenerators = MkTestPool "Generators for PIL" [] Nothing $ ("gens/" ++) <$>
  [ "demo001"
  ]

main : IO ()
main = do
  runner
    [ pilLanguage
    , pilGenerators
    ]
