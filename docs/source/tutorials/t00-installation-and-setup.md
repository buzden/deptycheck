# Installation and First Steps

Welcome to DepTyCheck! This tutorial will guide you through installing Idris 2 and DepTyCheck, creating your first project, and running a simple generator.

## Our Goal

In this tutorial, you will:
1.  Install Idris 2 and the DepTyCheck library
2.  Create a project configured with DepTyCheck
3.  Write and run a generator that produces random `TrafficLight` values

By the end, you will see output like:
```
Red : TrafficLight
```

**Expected time:** 15-20 minutes

---

## Step 1: Install Idris 2

First, you need to install Idris 2. We recommend using [`pack`](https://github.com/stefan-hoeck/idris2-pack/), which manages both the compiler and library dependencies.

**Option A: Using a pre-built distribution** (recommended for beginners)

Download a pre-built distribution from the [Idris 2 releases page](https://github.com/idris-lang/Idris2/releases) and add it to your PATH.

**Option B: Build from source**

```bash
git clone https://github.com/idris-lang/Idris2.git
cd Idris2
make
sudo make install
```

**Verify your installation:**
```bash
idris2 --version
```

Expected output:
```
0.6.x
```

🔍 **Notice:** You need Idris 2 version **0.6.0 or newer** for DepTyCheck to work.

---

## Step 2: Install DepTyCheck

Now that Idris 2 is installed, let's add the DepTyCheck library.

1.  **Update the package database:**
```bash
pack update-db
```

2.  **Install DepTyCheck:**
```bash
pack install deptycheck
```

Expected output:
```
Installing deptycheck...
Successfully installed deptycheck
```

🔍 **Notice:** This command downloads and builds DepTyCheck. It may take a few minutes the first time.

---

## Step 3: Create Your First Project

1.  **Create a project directory:**
```bash
mkdir deptycheck-tutorial
cd deptycheck-tutorial
```

2.  **Create a project file** named `tutorial.ipkg`:
```
package tutorial

version = 0.0.1

sourcedir = src
builddir = .build

modules = Main

depends = deptycheck
```

🔍 **Notice:** The `depends = deptycheck` line tells Idris to use the DepTyCheck library.

---

## Step 4: Write Your First Generator

1.  **Create the source directory:**
```bash
mkdir src
```

2.  **Create a file** `src/Main.idr` with the following code:

```idris
module Main

%language ElabReflection

import Data.Fuel
import Deriving.DepTyCheck.Gen
import Test.DepTyCheck.Runner

data TrafficLight = Red | Yellow | Green

genTrafficLight : Fuel -> Gen MaybeEmpty TrafficLight
genTrafficLight = deriveGen

main : IO ()
main = do
  Just light <- pick1 (genTrafficLight (limit 10))
    | Nothing => putStrLn "Generation failed"
  putStrLn $ show light ++ " : TrafficLight"
```

🔍 **Notice:**
-   `%language ElabReflection` enables the metaprogramming features needed for `deriveGen`
-   `deriveGen` automatically creates a generator for `TrafficLight`
-   `pick1` runs the generator and extracts one value

---

## Step 5: Build and Run

1.  **Build the project:**
```bash
pack build tutorial
```

Expected output:
```
Building tutorial...
Build succeeded
```

2.  **Run the executable:**
```bash
pack exec tutorial
```

Expected output (your result will vary):
```
Red : TrafficLight
```

🔍 **Notice:** Run the command multiple times to see different results (Yellow, Green, Red).

---

## Step 6: Try It in the REPL (Optional)

You can also test your generator interactively:

1.  **Start the REPL:**
```bash
pack repl tutorial
```

2.  **Run the generator:**
```idris
:exec pick1 (genTrafficLight (limit 10))
```

Expected output:
```
Green : TrafficLight
```

3.  **Run it multiple times** to see different colors.

4.  **Exit the REPL:**
```idris
:quit
```

---

## Next Steps

Now that you have a working setup, you are ready to learn the fundamentals of generator creation:

*   **Continue to Tutorial 1:** [The Generator Monad](t01-generator-monad.md) to learn how to create generators manually using `pure`, `elements`, `choose`, and other combinators.
