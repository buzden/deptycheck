module Run

import Data.Fuel
import Data.List.Lazy

import GenForSome

import Test.DepTyCheck.Gen

Show (Stmts preDefs postDefs) where
  show $ Def new = "define `\{new}`"
  show $ Use usd = "use `\{usd}`"
  show $ x >> y  = show x ++ "\n" ++ show y

namespace NoParams

  export
  ShowStmts : Show $ Stmts preDefs postDefs
  ShowStmts = %search

namespace PreOnly

  export
  [ShowStmt] Show (preDefs ** Stmts preDefs postDefs) where
    show (preDefs ** stmt) = "-- pre defs: \{show preDefs}\n\{show stmt}"

namespace PostOnly

  export
  [ShowStmt] Show (postDefs ** Stmts preDefs postDefs) where
    show (postDefs ** stmt) = "\{show stmt}\n-- post defs: \{show postDefs}"

namespace BothPreAndPost

  export
  [ShowStmt] Show (preDefs ** postDefs ** Stmts preDefs postDefs) where
    show (preDefs ** postDefs ** stmt) = "-- pre defs: \{show preDefs}\n\{show stmt}\n-- post defs: \{show postDefs}"

main : IO Unit
main = do
  Lazy.traverse_ ((>> putStrLn "\n----\n") . printLn @{%search} @{ShowStmt}) $ allDetermValues $ genStmtP_ (limit 2) []
