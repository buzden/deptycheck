module UseGen

import Data.Fin
import Data.List.Lazy

import Test.DepTyCheck.Gen

gen : (n : Nat) -> Gen MaybeEmpty $ Fin n
gen Z     = empty
gen (S n) = oneOf [pure FZ, FS <$> gen n]

main : IO Unit
main = Lazy.traverse_ ((>> putStrLn "\n----\n") . printLn) $ allDetermValues $ gen 10
