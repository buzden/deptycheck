# DepTyCheck Documentation Files Grouped by Subject

## Core Generator Infrastructure

### Generator Monad (`Gen`)
- **Files**:
  - `deptycheck-docs-aigen-gemini-f-5/DepTyCheck/07_test_generator_core_.md` - Core `Gen` data type implementation
- **Subjects**: Generator monad, composable test data generation, `Empty`/`Pure`/`Raw`/`OneOf`/`Bind` constructors

### Type-Level Assembly
- **Files**:
  - `deptycheck-docs-aigen-gemini-pro-4/DepTyCheck/05_type_level_generator_assembly_.md` - Fuel-based generator assembly
- **Subjects**: Type-level programming, fuel-based control flow, constructor combination

## Derivation Pipeline Architecture

### Pipeline Interfaces
- **Files**:
  - `deptycheck-docs-aigen-gemini-pro-with-tests-1/DepTyCheck/04_derivation_pipeline_interfaces_.md` - Modular interface-based pipeline
  - `deptycheck-docs-aigen-gemini-pro-with-tests-and-samples-4/DepTyCheck/04_derivation_pipeline_.md` - Multi-stage assembly-line pipeline
- **Subjects**: `DeriveBodyForType`, `DeriveBodyRhsForCon`, `ForAllNeededTypes`, `ForOneType`, `ForOneTypeCon`

### Derivation Strategies
- **Files**:
  - `deptycheck-docs-aigen-gemini-pro-with-tests-and-samples-1/DepTyCheck/05_derivation_core___strategy.md` - Core `LeastEffort` strategy
  - `deptycheck-docs-aigen-gemini-pro-with-tests-1/DepTyCheck/05__leasteffort__derivation_strategy_.md` - Least-effort algorithm details
- **Subjects**: Dependency analysis, automatic ordering, `searchOrder` function

## Code Analysis Utilities

### Metaprogramming Tools
- **Files**:
  - `deptycheck-docs-aigen-gemini-pro-4/DepTyCheck/11_metaprogramming_utilities_.md` - Metaprogramming utilities
  - `deptycheck-docs-aigen-gemini-pro-3/DepTyCheck/05_derivation_code_analysis_utilities_.md` - Code analysis utilities
- **Subjects**: `DeepConsApp`, `Primitives`, `ArgsPerm`, expression analysis, argument reordering

### Type and Signature Analysis
- **Files**:
  - `deptycheck-docs-aigen-gemini-pro-with-tests-2/DepTyCheck/05_type_and_signature_analysis_utilities_.md` - Type/signature analysis tools
- **Subjects**: `GenSignature`, `ConsRecs`, blueprint scanning, recursion analysis

## Quality Assurance

### Generator Tuning
- **Files**:
  - `deptycheck-docs-aigen-gemini-f-5/DepTyCheck/10_generator_tuning_interface_.md` - Tuning interfaces
- **Subjects**: `GenOrderTuning`, `ProbabilityTuning`, argument generation order, constructor probabilities

### Distribution Checking
- **Files**:
  - `deptycheck-docs-aigen-gemini-pro-with-samples-5/DepTyCheck/06_distribution_checking_utilities_.md` - Statistical validation tools
- **Subjects**: `CoverageTest`, `printVerdict`, statistical analysis, generator quality validation
