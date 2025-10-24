# Chapter 8: Project Tooling & Configuration

Welcome to the final chapter of our tutorial! Over the last seven chapters, we've journeyed deep into the heart of `DepTyCheck`. We started with the basic ingredients in [Test Data Generator (`Gen`)](01_test_data_generator___gen___.md), saw the magic of our robot chef `deriveGen`, and just finished dissecting how it reads its orders in [Generator Signature Analysis](07_generator_signature_analysis_.md).

You now understand the *concepts*, the "recipes" of `DepTyCheck`. In this last chapter, we're going to take a tour of the kitchen itself. We'll explore the project's infrastructure—the tools, configurations, and hidden helpers that keep development running smoothly. For a new developer, understanding this is like a new chef learning where the knives are kept and how the oven works.

### The `pack` Package Manager: Our Kitchen's Pantry

Every good kitchen needs a well-stocked pantry. You need to know where to find flour, sugar, and spices. In an Idris project, our "pantry" is managed by a tool called `pack`. It makes sure we have all the code libraries (dependencies) we need to build `DepTyCheck`.

The two most important files for `pack` are `pack.toml` and `.ipkg` files.

#### `pack.toml`: The Master Shopping List

The `pack.toml` file at the root of the project is the master shopping list. It tells `pack` where to find every single component of the project, including external libraries from the internet and all the local example projects we've discussed.

```toml
# In pack.toml

[custom.all.deptycheck]
type = "local"
path = "."
ipkg = "deptycheck.ipkg"

[custom.all.pil-reg]
type = "local"
path = "examples/pil-reg"
ipkg = "pil-reg.ipkg"
test = "tests/tests.ipkg"
```

Let's look at this shopping list entry for `pil-reg`, our [Primitive Imperative Language (PIL) Examples](04_primitive_imperative_language__pil__examples_.md):
*   `type = "local"`: This tells `pack` that the code is right here in our repository, not somewhere on the internet.
*   `path = "examples/pil-reg"`: This is the folder where the `pil-reg` sub-project lives.
*   `ipkg = "pil-reg.ipkg"`: This points to the specific "recipe card" for building this sub-project.

With this file, building the entire project and all its examples is as simple as running one command in your terminal:

```sh
pack build
```
`pack` will read the `pack.toml` file, find all the pieces, and build them in the correct order.

#### `.ipkg` Files: The Recipe Cards

If `pack.toml` is the shopping list, then `.ipkg` files are the individual recipe cards. Each sub-project has one. It lists the modules that are part of that project and the ingredients (dependencies) it needs.

Here's a simplified look at the main recipe card for `DepTyCheck` itself, `deptycheck.ipkg`:

```idris
-- In deptycheck.ipkg
package deptycheck

sourcedir = "src"
modules = Deriving.DepTyCheck.Gen
        , Test.DepTyCheck.Gen
        -- ... and many other modules

depends = ansi
        , elab-util-extra
        , random-pure
```

This tells the Idris compiler:
*   `sourcedir = "src"`: All the source code for this part is in the `src` folder.
*   `modules = ...`: Here is a list of all the code modules that make up the `DepTyCheck` library.
*   `depends = ...`: To build `DepTyCheck`, you first need these other libraries (like `ansi` for terminal colors and `random-pure` for random number generation).

### `.editorconfig`: The Kitchen Rules

A busy kitchen can get messy fast if everyone has their own way of working. `.editorconfig` is a file that sets the "kitchen rules" for our code. It ensures that everyone's code looks the same, no matter what text editor they use.

```ini
# In .editorconfig
root = true

[*]
end_of_line = lf
trim_trailing_whitespace = true
max_line_length = 152

[*.{idr,ipkg}]
indent_style = space
indent_size = 2
```

These rules are simple but effective:
*   `indent_size = 2`: Use 2 spaces for indentation in Idris files.
*   `trim_trailing_whitespace = true`: Automatically clean up any extra spaces at the end of lines.
*   `max_line_length = 152`: Try to keep lines of code from getting too long.

Most modern code editors automatically detect and apply these rules, so the codebase stays clean and consistent without any extra effort.

### Utility Scripts: The Special-Purpose Gadgets

Every kitchen has a few strange-looking gadgets for very specific jobs, like an avocado slicer or a garlic press. Our project has a few of these too, in the form of shell scripts.

#### `.rename`: The Smart Relabeler

Renaming a file in a programming project can be a pain. You also have to find every other file that used the old name and update it. The `.rename` script automates this.

If you wanted to rename a module, you could run:

```sh
./.rename src/Old/Module.idr src/New/Location.idr
```

This script will not only move the file but will also search the entire project for any code that imported `Old.Module` and automatically change it to import `New.Location`. It's a huge time-saver!

#### `.patch-chez-gc-handler`: The Engine Tuner

This is a very advanced tool, like a mechanic's wrench for tuning an engine. `DepTyCheck`'s `deriveGen` does a lot of heavy lifting at compile-time. This can sometimes use a lot of memory. The Idris compiler runs on a system called "Chez Scheme," which has a garbage collector (GC) to manage memory.

The `.patch-chez-gc-handler` script applies a custom patch to this GC, tuning it to be more efficient for the specific, memory-intensive work that `DepTyCheck` does. You won't need to use this unless you are doing very deep work on the derivation engine itself, but it's a vital tool for ensuring the project can compile its most complex examples without running out of memory.

### CI and Docs: Quality Control and Publishing Cookbooks

Finally, how do we make sure our project stays high-quality and easy for others to use?

*   **Continuous Integration (CI):** This is our automated "head chef" who inspects every change. Our CI is set up using GitHub Actions. Whenever a developer suggests a change, a series of automated checks are run on GitHub's servers. These checks build the entire project, run all tests, and try to derive generators for all the [Example Data Structures](03_example_data_structures_.md). If any of these fail, the change is blocked, preventing bugs from entering the main codebase.

*   **Documentation (`.readthedocs.yaml`):** How do we publish our recipes for the world to see? The very tutorial you are reading is built and hosted by a service called "Read the Docs." The `.readthedocs.yaml` file tells this service how to do it.

```yaml
# In .readthedocs.yaml
version: 2

build:
  os: ubuntu-22.04
  tools:
    python: "3.10"

sphinx:
  configuration: docs/source/conf.py
```
This simple file tells Read the Docs: "Use an Ubuntu computer with Python 3.10, and find the main configuration for building the documentation website at `docs/source/conf.py`." This makes publishing beautiful, up-to-date documentation an automatic process.

### Conclusion: You're Ready to Cook!

Congratulations on finishing the `DepTyCheck` tutorial!

We've covered a lot of ground. You started as an apprentice, learning about the most basic ingredient, the [Test Data Generator (`Gen`)](01_test_data_generator___gen___.md). You met the master robot chef, `deriveGen`, and saw it prepare incredibly complex dishes like sorted lists and even entire programs. You peeked inside the derivation factory and saw the assembly line that makes it all possible. And now, you've had a full tour of the kitchen.

You know how the code works, and you know how the project is organized. You are now fully equipped to start exploring, experimenting, and "cooking" up your own powerful, dependently-typed property tests. Happy testing

---

Generated by [AI Codebase Knowledge Builder](https://github.com/The-Pocket/Tutorial-Codebase-Knowledge)