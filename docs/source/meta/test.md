<!-- idris
module Meta.Test

import Test.DepTyCheck.Gen
-->

# Simple test module

This module contains a simple gen example:

```idris
genN : Gen Nat
genN = choiceMap pure [0, 1]
```
