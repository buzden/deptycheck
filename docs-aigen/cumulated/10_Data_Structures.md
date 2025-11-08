# Data Structures Tutorial

## Introduction

Welcome! In this hands-on tutorial, we'll work together to generate test data for complex dependently-typed data structures using DepTyCheck. We'll build practical examples step by step, starting simple and gradually tackling more sophisticated challenges.

**What we'll accomplish together:**
- Generate provably sorted lists of numbers
- Create lists with unique elements  
- Build sorted binary trees
- Generate covering sequences

By the end, you'll have hands-on experience with four different constraint patterns that DepTyCheck can handle automatically.

Let's begin with our first challenge: creating lists that are guaranteed to be sorted.

## Sorted List Generation

### The Problem: Self-Sorting Lists

Imagine you're building a leaderboard system where scores must always be displayed in order. With regular lists, bugs could easily introduce out-of-order elements. What if the type system itself prevented this?

### Defining a Sorted List Type

We'll use a `SortedList` type that encodes the sorting constraint directly in its definition:

```idris
-- From: examples/sorted-list-tl-pred/src/Data/List/Sorted.idr

data SortedList : Type where
  Nil  : SortedList
  (::) : (x : Nat) -> (xs : SortedList) -> FirstGT x xs => SortedList
```

The key constraint is `FirstGT x xs`, which ensures the new element `x` is smaller than the head of the existing list `xs`.

Let's define the `FirstGT` constraint:

```idris
-- From: examples/sorted-list-tl-pred/src/Data/List/Sorted.idr

data FirstGT : Nat -> SortedList -> Type where
  E  : FirstGT n []
  NE : x `GT` n -> FirstGT n $ (x::xs)
```

This gives us two cases:
- `E`: Empty lists always accept new elements
- `NE`: Non-empty lists require proof that the head is greater than the new element

### Exercise: Build a Sorted List Manually

Let's practice building a sorted list by hand:

```idris
-- Start with empty list
l0 : SortedList
l0 = Nil

-- Add 10 to empty list (E rule applies)
l1 : SortedList
l1 = 10 :: l0

-- Add 5 to [10] (NE rule: 10 > 5 is provable)
l2 : SortedList
l2 = 5 :: l1

-- Try adding 8 to [5, 10] - this will fail!
-- l3 : SortedList
-- l3 = 8 :: l2  -- Error: Can't find proof that 5 > 8
```

**Solution:** The type system correctly prevents us from creating `[8, 5, 10]` because 5 is not greater than 8.

### Automatic Generator Derivation for Sorted Lists

Now let's see how `deriveGen` handles this automatically:

```idris
-- From: examples/sorted-list-tl-pred/src/Data/List/Sorted/Gen.idr

import public Data.List.Sorted
import Deriving.DepTyCheck.Gen

export
genSortedList : Fuel -> Gen MaybeEmpty SortedList
genSortedList = deriveGen
```

That's it! One line gives us a generator that only produces valid sorted lists.

### Constraint Resolution Strategy

How does `deriveGen` solve this puzzle? Let's trace through the generation process:

1. **Choose constructor**: Randomly picks `Nil` or `(::)`
2. **If `(::)` chosen**: Needs `x`, `xs`, and `FirstGT x xs` proof
3. **Generate tail first**: Creates `xs` recursively
4. **Use constraint to guide `x`**: If `xs = [20, 30]`, generates `x < 20`
5. **Assemble result**: Combines `x`, `xs`, and proof

The key insight: `deriveGen` analyzes dependencies and generates in the optimal order.

**Exercise**: Try running the generator and observe the patterns:

```idris
-- Generate some sorted lists
main : IO ()
main = do
  Just list1 <- pick1 (genSortedList defaultFuel)
    | Nothing => putStrLn "Out of fuel"
  putStrLn "Generated: {show list1}"
  
  Just list2 <- pick1 (genSortedList defaultFuel)
    | Nothing => putStrLn "Out of fuel"
  putStrLn "Generated: {show list2}"
```

**Expected output patterns**:
- `[]` (empty list)
- `[42]` (single element)
- `[5, 10, 25]` (sorted ascending)
- `[100, 200, 300]` (larger sorted values)

**Notice**: All lists will be properly sorted, never something like `[10, 5]`.

## Unique Element Lists

### The Problem: Lists Without Duplicates

Now let's tackle a different constraint: ensuring all elements in a list are unique. Imagine managing user IDs where duplicates would cause conflicts.

### Defining Unique List Types

We'll create a `UniqStrList` that prevents duplicates at the type level:

```idris
-- From: examples/uniq-list/src/Data/List/Uniq.idr

data UniqStrList : Type where
  Nil  : UniqStrList
  (::) : (s : String) -> (ss : UniqStrList) -> s `NotIn` ss => UniqStrList
```

The `NotIn` constraint ensures each new element isn't already in the list:

```idris
-- From: examples/uniq-list/src/Data/List/Uniq.idr

data NotIn : String -> UniqStrList -> Type where
  N : NotIn x []
  S : So (x /= s) => x `NotIn` ss -> x `NotIn` (s::ss)
```

### Exercise: Build a Unique List Manually

Let's practice building unique lists:

```idris
-- Start with empty list
l0 : UniqStrList
l0 = Nil

-- Add "a" to empty list (N rule applies)
l1 : UniqStrList
l1 = "a" :: l0

-- Add "b" to ["a"] (S rule: "b" != "a")
l2 : UniqStrList
l2 = "b" :: l1

-- Try adding "a" to ["b", "a"] - this will fail!
-- l3 : UniqStrList
-- l3 = "a" :: l2  -- Error: Can't find proof that "a" != "b"
```

**Solution**: The type system correctly prevents `["a", "b", "a"]` because "a" is already in the list.

### Element Generator Integration

To generate unique lists, we need to provide an element generator:

```idris
-- From: examples/uniq-list/src/Data/List/Uniq/Gen.idr

import Deriving.DepTyCheck.Gen
import Data.List.Uniq

genUniqStrList : Fuel -> (Fuel -> Gen MaybeEmpty String) => Gen MaybeEmpty UniqStrList
genUniqStrList = deriveGen
```

Notice the `(Fuel -> Gen MaybeEmpty String)` constraint - this tells `deriveGen` how to generate individual elements.

### Stateful Constraint Handling

How does `deriveGen` avoid duplicates? It uses a clever stateful approach:

1. **Generate tail first**: Creates `ss = ["c", "e"]` recursively
2. **Analyze constraint**: Needs `s` where `s` not in `["c", "e"]`
3. **Filter element generator**: Wraps our generator to reject "c" and "e"
4. **Generate valid head**: Keeps trying until it gets "a" (not "c" or "e")
5. **Assemble result**: `["a", "c", "e"]`

**Exercise**: Create and test a unique list generator:

```idris
-- Simple string generator
simpleStrGen : Gen MaybeEmpty String
simpleStrGen = elements ["x", "y", "z"]

-- Generate unique lists
main : IO ()
main = do
  Just list1 <- pick1 (genUniqStrList {sub=const simpleStrGen} (limit 3))
    | Nothing => putStrLn "Out of fuel"
  putStrLn "Generated: {show list1}"
  
  Just list2 <- pick1 (genUniqStrList {sub=const simpleStrGen} (limit 3))
    | Nothing => putStrLn "Out of fuel"
  putStrLn "Generated: {show list2}"
```

**Expected output patterns**:
- `[]` (empty list)
- `["x"]` (single element)
- `["y", "x", "z"]` (all unique elements)
- `["z", "x"]` (subset of available elements)

**Notice**: Lists will never contain duplicates like `["x", "y", "x"]`.

### Unique Vectors

The same approach works for vectors with length tracking:

```idris
-- From: examples/uniq-list/src/Data/Vect/Uniq.idr

data UniqStrVect : Nat -> Type where
  Nil  : UniqStrVect Z
  (::) : (s : String) -> (ss : UniqStrVect n) -> NotIn s n ss => UniqStrVect $ S n
```

`deriveGen` handles the length constraint automatically while maintaining uniqueness.

## Sorted Binary Trees

### The Problem: Self-Organizing Search Trees

Now let's combine sorting and recursion to build binary search trees. These structures enable fast lookups by maintaining ordering properties.

### Binary Search Tree Properties

A binary search tree ensures that for any node:
- All left subtree values are smaller
- All right subtree values are larger

Here's one way to encode this:

```idris
-- From: examples/sorted-tree-naive/src/Data/SortedBinTree.idr

data SortedBinTree : Type where
  Empty : SortedBinTree
  Node  : (x : Nat) -> (left, right : SortedBinTree) ->
          AllLT x left => AllGT x right => SortedBinTree
```

The constraints `AllLT` and `AllGT` ensure the ordering property:

```idris
-- Simplified definition of AllLT
data AllLT : Nat -> SortedBinTree -> Type where
  EmptyLT : AllLT ref Empty
  NodeLT  : x `LT` ref -> AllLT ref l -> AllLT ref r ->
            AllLT ref (Node x l r)
```

### Exercise: Build a Binary Search Tree Manually

Let's practice building trees:

```idris
-- Start with empty trees
leftTree : SortedBinTree
leftTree = Empty

rightTree : SortedBinTree
rightTree = Empty

-- Create a node with value 5
node5 : SortedBinTree
node5 = Node 5 leftTree rightTree

-- Create left subtree with value 2
leftSub : SortedBinTree
leftSub = Node 2 Empty Empty

-- Create right subtree with value 8
rightSub : SortedBinTree
rightSub = Node 8 Empty Empty

-- Combine into tree: 5 with left=2, right=8
tree : SortedBinTree
tree = Node 5 leftSub rightSub

-- Try creating invalid tree - this will fail!
-- badTree : SortedBinTree
-- badTree = Node 5 (Node 8 Empty Empty) rightSub  -- Error: Can't prove 8 < 5
```

**Solution**: The type system prevents `Node 5 (Node 8 ...) ...` because 8 is not less than 5.

### Alternative Encoding Approaches

Another approach uses indexed trees with bounds:

```idris
-- From: examples/sorted-tree-indexed/src/Data/SortedBinTree.idr

data SortedBinTree1 : (mi, ma : Nat) -> Type where
  Leaf : (x : Nat) -> SortedBinTree1 x x
  Node : (left : SortedBinTree1 lmi lma) ->
         (right : SortedBinTree1 rmi rma) ->
         lma `LT` rmi => SortedBinTree1 lmi rma
```

This encodes the BST property as `lma < rmi` - the max of left subtree must be less than min of right subtree.

### Recursive Constraint Resolution

How does `deriveGen` build valid binary search trees?

```idris
-- From: examples/sorted-tree-naive/src/Data/SortedBinTree/Gen.idr

import Deriving.DepTyCheck.Gen

export
genSortedBinTree : Fuel -> Gen MaybeEmpty SortedBinTree
genSortedBinTree = deriveGen
```

The generation process:
1. **Generate root value**: Picks random `x` (e.g., 10)
2. **Generate left subtree**: Creates tree using only numbers `< 10`
3. **Generate right subtree**: Creates tree using only numbers `> 10`
4. **Assemble node**: Combines root, left, and right subtrees

**Exercise**: Generate and examine binary search trees:

```idris
main : IO ()
main = do
  Just tree <- pick1 (genSortedBinTree (limit 3))
    | Nothing => putStrLn "Out of fuel"
  putStrLn "Generated tree: {show tree}"
  
  -- Try generating more trees
  Just tree2 <- pick1 (genSortedBinTree (limit 3))
    | Nothing => putStrLn "Out of fuel"
  putStrLn "Another tree: {show tree2}"
```

**Expected output patterns**:
- `Empty` (empty tree)
- `Node 5 Empty Empty` (single node)
- `Node 10 (Node 5 Empty Empty) (Node 15 Empty Empty)` (balanced tree)
- `Node 20 (Node 10 Empty Empty) Empty` (left-heavy tree)

**Notice**: All trees maintain the BST property - left values are smaller than root, right values are larger.

### Alternative Indexed Tree Generation

For the indexed version:

```idris
-- From: examples/sorted-tree-indexed/src/Data/SortedBinTree/Gen.idr

genSortedBinTree1 : Fuel -> Gen MaybeEmpty (mi ** ma ** SortedBinTree1 mi ma)
genSortedBinTree1 = deriveGen
```

This generates trees along with their proven bounds.

## Covering Sequences

### The Problem: Scavenger Hunt Checklists

Now let's tackle a different kind of constraint: ensuring a sequence contains specific values, regardless of order. Imagine a scavenger hunt where players must collect certain items.

### BitMask Representation

We represent requirements using a `BitMask`:

```idris
-- From: examples/covering-seq/src/Data/List/Covering.idr

-- A BitMask is just a list of Bools with its length in the type
data BitMask : (bits : Nat) -> Type where
  Nil  : BitMask 0
  (::) : Bool -> BitMask n -> BitMask (S n)
```

For example, `[True, True, False, True]` means we need items 0, 1, and 3.

### State Tracking Across Sequences

The `CoveringSequence` type tracks progress:

```idris
-- From: examples/covering-seq/src/Data/List/Covering.idr

data CoveringSequence : (n : Nat) -> BitMask n -> Type where
  End  : AllBitsAre n False bs => CoveringSequence n bs
  Miss : Nat -> CoveringSequence n bs -> CoveringSequence n bs
  Hit  : (i : Fin n) -> AtIndex n i bs True =>
         CoveringSequence n (update i False bs) -> CoveringSequence n bs
```

- `Hit i`: Records finding required item `i`, updates mask
- `Miss k`: Records finding optional item `k`, mask unchanged
- `End`: Only allowed when all requirements are met

### Exercise: Build a Covering Sequence Manually

Let's practice building sequences:

```idris
-- Start with requirements: need items 0, 1, and 3
mask : BitMask 4
mask = [True, True, False, True]

-- Build sequence: Hit 1, Miss 20, Hit 0, Hit 3
journey : CoveringSequence 4 mask
journey = Hit 1 (Miss 20 (Hit 0 (Hit 3 End)))

-- Try invalid sequence - this will fail!
-- badJourney : CoveringSequence 4 mask
-- badJourney = Hit 2 End  -- Error: Item 2 not required
```

**Solution**: The type system prevents `Hit 2` because item 2 is `False` in the mask.

### Coverage Validation

How does `deriveGen` generate valid sequences?

```idris
-- From: examples/covering-seq/src/Data/List/Covering/Gen.idr

import Deriving.DepTyCheck.Gen

export
genCoveringSequence : Fuel -> {n : Nat} -> (bs : BitMask n) ->
                      Gen MaybeEmpty (CoveringSequence n bs)
genCoveringSequence = deriveGen
```

The generation process:
1. **Analyze mask**: Check which items are required (`True`)
2. **Choose action**: Randomly pick `Hit`, `Miss`, or `End`
3. **If `Hit`**: Pick from required items, update mask recursively
4. **If `Miss`**: Generate random number, keep mask unchanged
5. **If `End`**: Only allowed when mask is all `False`

**Exercise**: Generate covering sequences:

```idris
main : IO ()
main = do
  let checklist = [True, True, False, True]
  Just sequence <- pick1 (genCoveringSequence defaultFuel checklist)
    | Nothing => putStrLn "Out of fuel"
  putStrLn "Generated sequence: {show sequence}"
  
  Just sequence2 <- pick1 (genCoveringSequence defaultFuel checklist)
    | Nothing => putStrLn "Out of fuel"
  putStrLn "Another sequence: {show sequence2}"
```

**Expected output patterns**:
- `Hit 1 (Hit 0 (Hit 3 End))` (direct path)
- `Miss 42 (Hit 3 (Miss 99 (Hit 1 (Hit 0 End))))` (with extras)
- `Hit 0 (Miss 7 (Hit 3 (Hit 1 End)))` (mixed order)

**Notice**: All sequences will contain `Hit` for items 0, 1, and 3 exactly once.

## Conclusion

### Summary of Techniques

Throughout this tutorial, we've seen how `DepTyCheck` handles various constraints:

**Sorted Lists**: Uses dependency analysis to generate tail first, then constrained head
**Unique Lists**: Uses stateful filtering to avoid duplicates
**Binary Trees**: Uses recursive bounds partitioning
**Covering Sequences**: Uses state tracking with bit masks

### Practical Applications

These techniques enable:
- Testing sorting algorithms with provably sorted data
- Validating uniqueness constraints in databases
- Generating test cases for tree-based algorithms
- Creating coverage tests for state machines

### Next Steps

Ready for more complex examples? Try:
- Generating programs for embedded languages
- Testing compiler transformations
- Validating protocol implementations

Each builds on the patterns we've learned here.