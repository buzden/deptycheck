module UseLazier

import Data.List.Lazier

foo : LzList Int
foo = [1, 2, 5]

bar : LzList String
bar = ["a", "b"]

foobar : LzList (Int, String)
foobar = [| (foo, bar) |]
