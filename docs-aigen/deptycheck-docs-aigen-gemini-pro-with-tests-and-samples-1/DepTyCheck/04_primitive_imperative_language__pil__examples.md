# Chapter 4: Primitive Imperative Language (PIL) Examples

In the last chapter, [Chapter 3: The `Gen` Monad](03_the__gen__monad.md), we learned that `Gen` is a powerful recipe for creating random data and that we can chain these recipes together to build complex values.

Now, we’re going to take that knowledge and apply it to our most ambitious example yet. We will move beyond generating simple data like lists and trees. We are going to ask `DepTyCheck` to do something that sounds like science fiction: **automatically write syntactically and semantically correct computer programs.**

### The Challenge: Teaching a Machine to Code

Imagine a very simple programming language. Even a simple one has complex rules:
1.  You must declare a variable before you can use it. (`x = 5;` is okay, `y = x;` is not if `x` isn't declared).
2.  Types must match. You can't assign a boolean value to an integer variable.
3.  Some variables might be read-only (immutable). You can't change their value after they're created.

A human programmer learns these rules. When you write code, your brain (and the compiler) constantly checks them. Now, what if we wanted to generate random, *valid* programs for testing a compiler? Writing a generator that follows all these rules by hand would be incredibly difficult. You'd essentially be re-implementing a compiler's brain inside your test generator!

This is where `DepTyCheck`'s power truly shines. We can model our programming language's rules directly in the Idris type system and then let `DepTyCheck` do the heavy lifting.

### The Blueprint: A Language Defined by Types

Let's look at a "Primitive Imperative Language" (or PIL), as seen in the `DepTyCheck` examples. We won't look at the whole thing, just a few key pieces that show how the rules are encoded.

**1. The Types of our Language**
First, our simple language only has two types: integers and booleans.

```idris
-- From `examples/pil-fun/src/Language/PilFun.idr`
data Ty = Int' | Bool'
```
This is the easy part. `Int'` represents an integer and `Bool'` represents a boolean.

**2. The Context: Keeping Track of Variables**
To check rules like "variable must be declared," our types need to know what variables exist. We'll use a `Vars` type (which is a list-like structure) to represent the "context" of all variables in scope, along with their types and mutability (`Mutable` or `Immutable`).

**3. The Expressions: Building Blocks with Rules**
An `Expr` is something that evaluates to a value, like a constant (`5`), a variable (`x`), or a function call. The type for `Expr` is the amazing part:

```idris
-- A simplified version of Expr
data Expr : (vars : Vars) -> (ty : Ty) -> Type where
  C : Literal ty -> Expr vars ty
  V : (n : IndexIn vars) ->
      AtIndex n ty mut =>
      Expr vars ty
```

Let's break down this blueprint:
*   `Expr vars ty`: This says, "An `Expr` is defined in the context of some `vars`, and it will produce a value of type `ty`."
*   `C`: The `C`onstant constructor. This lets us create an expression like `5` (which has type `Int'`) or `True` (type `Bool'`).
*   `V`: The `V`ariable constructor. This is where the magic is! To use a variable, you need two things:
    *   `n : IndexIn vars`: A "proof" that the variable exists in our context `vars`.
    *   `AtIndex n ty mut =>`: A "proof" that the variable at that index has a specific `ty`pe and `mut`ability.

The type system itself forbids you from creating an `Expr` that refers to a variable that doesn't exist. If you try, the compiler will say, "You can't give me a proof that this variable exists!"

**4. The Statements: Writing the Program**
A `Stmt` (statement) is an action, like declaring a new variable or assigning a value to an existing one. Look how the rules for assignment are encoded in the type:

```idris
-- A simplified version of Stmts
data Stmts : (vars : Vars) -> Type where
  Assign : (n : IndexIn vars) ->
           AtIndex n ty Mutable =>
           (val : Expr vars ty) ->
           Stmts vars ->
           Stmts vars
```

This `Assign` constructor models an assignment like `x = 5;`.
*   `n : IndexIn vars`: You must prove which variable you are assigning to.
*   `AtIndex n ty Mutable =>`: The type system enforces a critical rule: you can only assign to a variable that is `Mutable`. If you try to assign to an immutable one, you won't be able to provide this proof.
*   `val : Expr vars ty`: The value you're assigning (`val`) must be an expression that has the *exact same type* `ty` as the variable. This prevents you from assigning a `Bool'` to an `Int'`.

We have successfully encoded the rules of our programming language directly into the Idris type system!

### Let `DepTyCheck` Be the Programmer

Now for the payoff. We have this incredibly complex and rule-bound blueprint (`Stmts`). How do we generate valid programs? We just ask `DepTyCheck`.

First, we define the signature for our program generator. It will take some `Fuel` and the initial context (for example, an empty list of variables) and produce a `Gen` for a `Stmts`.

```idris
-- From `examples/pil-fun/src/Main.idr`
genProgram : Fuel -> Gen MaybeEmpty (Stmts Lin Nothing)
```
*   `Stmts Lin Nothing`: This means "generate a sequence of statements, starting with an empty context (`Lin`) and no return value expected (`Nothing`)."

And the implementation is... you guessed it.

```idris
genProgram = deriveGen
```

That's it. We're done. When the compiler sees this, `DepTyCheck` kicks in, reads the blueprints for `Stmts`, `Expr`, `AtIndex`, and all the other related types. It untangles all the rules and constraints and automatically writes a complex generator function that knows how to:
*   Declare new variables.
*   Use only variables that are in scope.
*   Respect type-safety during assignments.
*   Only assign to mutable variables.
*   ...and so on!

The result is a generator that can produce random, but always-correct, programs in our little language.

### Under the Hood: `DepTyCheck`'s Thought Process

How does `deriveGen` figure this out? You can think of it as a logical reasoner.

```mermaid
sequenceDiagram
    participant You as Developer
    participant DTC as DepTyCheck (deriveGen)
    participant StmtsBP as Stmts Blueprint
    participant ExprBP as Expr Blueprint
    participant ProgGen as Generated Program Generator

    You->>DTC: Please create a generator for `Stmts`.
    DTC->>StmtsBP: I need to build `Stmts`. What are my options?
    StmtsBP-->>DTC: You can use `Assign`. But to do so, you need a mutable variable and a matching expression.
    DTC->>DTC: Okay, to use `Assign`, I first need to find a `Mutable` variable in the current context. Let's say I find `x` of type `Int'`.
    DTC->>DTC: Now I need an `Expr` of type `Int'`. How do I make one?
    DTC->>ExprBP: I need to build an `Expr` of type `Int'`. What are my options?
    ExprBP-->>DTC: You could make a constant like `5` (`C`), or you could use another variable (`V`) that is also of type `Int'`.
    DTC->>DTC: I'll make a plan: I will choose randomly. Maybe I'll pick a constant `5`.
    DTC->>ProgGen: I'm writing your logic. One possible step for you is: "Find a mutable integer variable `x`. If you find one, generate an assignment statement `x = 5;`."
```

`DepTyCheck` performs this reasoning for *every constructor* of *every data type* involved. It builds a complete "decision tree" that respects all the rules defined in the types, resulting in a smart generator that can navigate the complex state space of a well-typed program.

### Why Is This a Big Deal?

This example is a major leap because it demonstrates `DepTyCheck`'s potential in highly complex domains.

**It's like an AI that writes code snippets.** By giving it a formal grammar (the Idris types), `DepTyCheck` can generate syntactically and semantically correct examples from that grammar.

The most powerful application of this is **compiler fuzz testing**. A "fuzzer" is a tool that bombards a program with random inputs to find bugs.
*   **Bad Fuzzing:** Generating random text (`"int x = ; y z 5 &&&"`) and feeding it to a compiler. Most inputs are rejected by the parser, so only the earliest parts of the compiler are tested.
*   **Good Fuzzing with `DepTyCheck`:** Using `DepTyCheck` to generate thousands of *valid, well-typed* programs. These programs pass the parser and type-checker, allowing the fuzzer to find much deeper bugs in the compiler's optimization, analysis, or code generation phases.

### Conclusion

In this chapter, we saw how `DepTyCheck` can tackle a problem far more complex than generating a sorted list. By modeling the rules of a simple programming language within the Idris type system, we transformed `DepTyCheck` into an engine capable of automatically writing correct programs.

This illustrates a profound concept: if you can describe the rules of your system in its types, `DepTyCheck` can serve as a powerful tool to generate valid instances of that system. This opens the door to advanced testing strategies like compiler fuzzing and model-based testing.

So far, we have treated `deriveGen` as a magical black box. But what if we want to understand how it makes its decisions, or even influence them? In the next chapter, we'll start opening that box.

Next up: [Chapter 5: Derivation Core & Strategy](05_derivation_core___strategy.md).

---

Generated by [AI Codebase Knowledge Builder](https://github.com/The-Pocket/Tutorial-Codebase-Knowledge)