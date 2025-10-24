# Installation and First Steps

Welcome to DepTyCheck! This tutorial will guide you through installing Idris 2 and DepTyCheck, creating your first project, and running a simple
generator.

## Our Goal

In this tutorial, you will:

1. Install Idris 2 and the DepTyCheck library
2. Create a project configured with DepTyCheck
3. Write and run a generator that produces random `TrafficLight` values

By the end, you will see output like:

```text
Red : TrafficLight
```

---

## Step 1: Install Idris 2

First, you need to install Idris 2. We recommend using [`pack`](https://github.com/stefan-hoeck/idris2-pack/), which manages both the compiler
and library dependencies.

Follow its [installation script](https://github.com/stefan-hoeck/idris2-pack/?tab=readme-ov-file#quick-installation).

**Verify your installation:**

```bash
idris2 --version
```

Sample output:

```text
Idris 2, version 0.8.0-80fd5e4d7
```

```{note}
You need Idris 2 version **0.8.0 or newer** for DepTyCheck to work.
```

---

## Step 2: Create Your First Project

### Create a project directory

```bash
mkdir deptycheck-tutorial
cd deptycheck-tutorial
```

### Create a project file named `tutorial.ipkg`

```text
package tutorial

version = 0.0.1
langversion >= 0.8.0

sourcedir = "."
builddir = ".build"

modules = Main
main = Main
executable = tutorial

depends = deptycheck
```

```{note}
The `depends = deptycheck` line tells Idris to use the DepTyCheck library.
```

---

## Step 3: Write Your First Generator

### Create a file `Main.idr` with the following code

```idris
import Deriving.DepTyCheck.Gen
import System.Random.Pure.StdGen

data TrafficLight = Red | Yellow | Green

Show TrafficLight where
  show Red = "Red"
  show Yellow = "Yellow"
  show Green = "Green"

genTrafficLight : Fuel -> Gen MaybeEmpty TrafficLight
genTrafficLight = deriveGen

main : IO ()
main = do
  Just light <- pick (genTrafficLight (limit 0))
    | Nothing => putStrLn "Generation failed"
  printLn light
```

```{note}
- `%language ElabReflection` enables the metaprogramming features needed for `deriveGen`
- `deriveGen` automatically creates a generator for `TrafficLight`
- `pick` runs the generator and extracts one value
```

---

## Step 4: Build and Run

### Build the project

```bash
pack build
```

`pack` will download and build all dependencies automatically along with source code of the module.

### Run the executable

```bash
pack run tutorial.ipkg
```

Expected output (your result will vary):

```text
Yellow
```

```{note}
Run the command multiple times to see different results (Yellow, Green, Red).
```

---

## Step 4: Try It in the REPL (Optional)

You can also test your generator interactively.

### Start the REPL

Pass the Main module name to preload it:

```bash
rlwrap pack repl ./Main.idr
```

```{note}
- `%language ElabReflection` enables the metaprogramming features needed for `deriveGen`
- `deriveGen` automatically creates a generator for `TrafficLight`
- `pick` runs the generator and extracts one value
```

### Run the generator

```text
:exec printLn =<< pick (genTrafficLight (limit 0))
```

Expected output:

```text
Just Green
```

### Run it multiple times to see different colors

### Exit the REPL

```text
:quit
```

---

## Next Steps

Now that you have a working setup, you are ready to learn the fundamentals of generator creation:

- **Continue to Tutorial 1:** [The Generator Monad](t01-generator-monad.md) to learn how to create generators manually using `pure`, `elements`,
  `choose`, and other combinators.
