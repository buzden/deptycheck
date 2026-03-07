# DepTyCheck Tutorials

Welcome to the DepTyCheck tutorial series! These tutorials follow the **Diataxis framework** — each lesson is designed to teach you through hands-on experience with concrete, achievable goals.

## How to Use These Tutorials

- **Start from the beginning** if you're new to DepTyCheck or property-based testing
- **Jump to specific topics** if you need to learn a particular skill
- **Complete the exercises** in each tutorial to reinforce learning

---

## Core Track — Essential Skills

Everyone should complete this track to master DepTyCheck fundamentals.

| # | Tutorial |
| - | ---------- |
| 0 | [Installation and First Steps](t00-installation-and-setup.md) |
| 1 | [The Generator Monad](t01-generator-monad.md) |
| 2 | [Handling Emptiness](t02-handling-emptiness.md) |
| 3 | [Measuring Coverage](t03-measuring-test-coverage.md) |
| 4 | [Automatic Derivation](t04-automatic-generator-derivation.md) |
| 5 | [DeriveGen Signatures](t05-derivegen-signatures.md) |
| 6 | [Mixing Manual and Automatic](t06-mixing-manual-and-automatic.md) |
| 7 | [Beyond Fuel](t07-beyond-fuel.md) |
| 8 | [Generating GADTs with Proofs](t08-generating-gadts-with-proofs.md) |
| 9 | [Toy Example: DSL ASTs](t09-toy-example.md) |

**Prerequisites:** Basic Idris 2 knowledge (data types, functions, REPL)

---

## Advanced Track — Deep Mastery

Continue here after completing the Core Track.

| # | Tutorial |
| -- | ---------- |
| 10 | [Derivation Tuning](t10-derivation-tuning.md) |
| 11 | [Under the Hood](t11-under-the-hood-a-derivegen-like-macro.md) |

**Prerequisites:** Core Track completion

---

## Quick Reference — Find What You Need

### "I want to..."

| | |
| ------ | ------------ |
| Install DepTyCheck | [Tutorial 0](t00-installation-and-setup.md) |
| Generate simple data types | [Tutorial 1](t01-generator-monad.md) |
| Handle types that might be empty | [Tutorial 2](t02-handling-emptiness.md) |
| Check if my generators are biased | [Tutorial 3](t03-measuring-test-coverage.md) |
| Stop writing generators by hand | [Tutorial 4](t04-automatic-generator-derivation.md) |
| Control what deriveGen generates | [Tutorial 5](t05-derivegen-signatures.md) |
| Use my custom generators with deriveGen | [Tutorial 6](t06-mixing-manual-and-automatic.md) |
| Understand recursion performance | [Tutorial 7](t07-beyond-fuel.md) |
| Generate types with proof arguments | [Tutorial 8](t08-generating-gadts-with-proofs.md) |
| Generate complete programs for a DSL | [Tutorial 9](t09-toy-example.md) |
| Fix biased automatic generators | [Tutorial 10](t10-derivation-tuning.md) |
| Build custom derivation strategies | [Tutorial 11](t11-under-the-hood-a-derivegen-like-macro.md) |

---

## Tutorial Conventions

Throughout these tutorials, you will see:

> [!NOTE]\
>
> — Important callouts highlighting key concepts

- ```idris``` — Idris code blocks (copypaste ready)
- ```bash``` — Terminal commands
- **Expected output:** — What you should see when running code
- ✅ **Checklist items** — Skills you will acquire

### Code Examples

All code examples are tested and should work as written. If you encounter issues:

1. Check your Idris version (`idris2 --version` should be 0.8.0+)
2. Ensure DepTyCheck is installed (`pack list | grep deptycheck`)
3. [Open an issue](https://github.com/buzden/deptycheck/issues) if problems persist

---

## After Completing the Tutorials

Congratulations! You've mastered DepTyCheck. What's next?

### Apply Your Skills

- **Test your own projects:** Start using DepTyCheck for property-based testing
- **Explore examples:** Browse the [examples/](https://github.com/buzden/deptycheck/tree/master/examples) directory in the repository
- **Read the documentation:** Deepen your understanding with the Explanation and Reference sections

### Contribute

- **Share your generators:** Contribute examples back to the project
- **Report issues:** Help improve the library by reporting bugs
- **Extend the library:** Consider contributing new features

### Continue Learning

- **Property-based testing patterns:** Learn about shrinking, statistical testing
- **Idris metaprogramming:** Explore elaborator reflection in depth
- **Type-driven development:** Apply DepTyCheck skills to larger projects
