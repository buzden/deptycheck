# Precise Index for Various DepTyCheck Documentation Files

## Core Generator Infrastructure

### Generator Monad (`Gen`)
- **File**: `deptycheck-docs-aigen-gemini-f-5/DepTyCheck/07_test_generator_core_.md`
- **Content**: Core `Gen` data type implementation - the test data generator monad
- **Key Components**: `Empty`, `Pure`, `Raw`, `OneOf`, `Bind` constructors; `Functor`/`Applicative`/`Monad` interfaces
- **Purpose**: Fundamental building blocks for composable test data generation

### Type-Level Generator Assembly
- **File**: `deptycheck-docs-aigen-gemini-pro-4/DepTyCheck/05_type_level_generator_assembly_.md`
- **Content**: Final assembly of generators at the type level with fuel-based control
- **Key Components**: Fuel-based control flow (`Dry`/`More` branches), `case` expressions, `fuelDecisionExpr`
- **Purpose**: Safely combine constructor generators into cohesive type generators

## Derivation Pipeline Architecture

### Interface-Based Pipeline
- **File**: `deptycheck-docs-aigen-gemini-pro-with-tests-1/DepTyCheck/04_derivation_pipeline_interfaces_.md`
- **Content**: Modular derivation pipeline with pluggable interfaces
- **Key Components**: `DeriveBodyForType` (dispatcher), `DeriveBodyRhsForCon` (parts assembler), `DerivationClosure` (toolbox)
- **Purpose**: Flexible architecture allowing custom derivation strategies

### Multi-Stage Pipeline
- **File**: `deptycheck-docs-aigen-gemini-pro-with-tests-and-samples-4/DepTyCheck/04_derivation_pipeline_.md`
- **Content**: Assembly-line approach to generator derivation
- **Key Components**: `ForAllNeededTypes` (master planner), `ForOneType` (recipe strategist), `ForOneTypeCon` (dependency analyst)
- **Purpose**: Systematic, multi-phase generator construction

### Core Derivation Strategy
- **File**: `deptycheck-docs-aigen-gemini-pro-with-tests-and-samples-1/DepTyCheck/05_derivation_core___strategy.md`
- **Content**: Default `LeastEffort` strategy and core derivation components
- **Key Components**: `ForAllNeededTypes`, `ForOneType`, `ForOneTypeCon`, dependency analysis
- **Purpose**: Automatic resolution of generation order dependencies

### Least-Effort Strategy Details
- **File**: `deptycheck-docs-aigen-gemini-pro-with-tests-1/DepTyCheck/05__leasteffort__derivation_strategy_.md`
- **Content**: In-depth explanation of the default derivation algorithm
- **Key Components**: Dependency analysis, argument ordering, `searchOrder` function
- **Purpose**: Automatic dependency resolution for generation order

## Analysis and Utility Tools

### Metaprogramming Utilities
- **File**: `deptycheck-docs-aigen-gemini-pro-4/DepTyCheck/11_metaprogramming_utilities_.md`
- **Content**: Low-level metaprogramming tools for code analysis and manipulation
- **Key Components**: `DeepConsApp` (expression analysis), `Primitives` (built-in types), `ArgsPerm` (argument reordering)
- **Purpose**: Enable high-level derivation pipeline functionality

### Derivation Code Analysis
- **File**: `deptycheck-docs-aigen-gemini-pro-3/DepTyCheck/05_derivation_code_analysis_utilities_.md`
- **Content**: Code analysis utilities used during derivation process
- **Key Components**: `DeepConsApp`, `Primitives`, `ArgsPerm` utilities
- **Purpose**: Help derivation engine understand and manipulate Idris code

### Type and Signature Analysis
- **File**: `deptycheck-docs-aigen-gemini-pro-with-tests-2/DepTyCheck/05_type_and_signature_analysis_utilities_.md`
- **Content**: Tools for analyzing data structure types and signatures
- **Key Components**: `GenSignature` (work orders), `DeepConsApp` (blueprint scanner), `ConsRecs` (recursion analysis)
- **Purpose**: Provide structural information about types to derivation engine

## Quality Assurance and Tuning

### Generator Tuning Interface
- **File**: `deptycheck-docs-aigen-gemini-f-5/DepTyCheck/10_generator_tuning_interface_.md`
- **Content**: Interfaces for customizing automatic generator derivation
- **Key Components**: `GenOrderTuning` (argument generation order), `ProbabilityTuning` (constructor selection)
- **Purpose**: Fine-tune how `deriveGen` builds generators

### Distribution Checking Utilities
- **File**: `deptycheck-docs-aigen-gemini-pro-with-samples-5/DepTyCheck/06_distribution_checking_utilities_.md`
- **Content**: Tools for validating generator quality through statistical analysis
- **Key Components**: `CoverageTest` records, `printVerdict` function, statistical validation
- **Purpose**: Ensure generated test data has good variety and coverage
