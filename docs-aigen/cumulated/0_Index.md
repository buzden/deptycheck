# DepTyCheck Tutorial Index

## Learning Progression

### Level 1: Foundation
**Core Concepts: Basic Generator Creation and Automation**

#### 1. Generator Monad (`1_Generator_Monad.md`)
- **Main Topic**: Creating test data generators manually using the Gen monad
- **Key Concepts**: `Gen1`/`NonEmpty` vs `Gen0`/`MaybeEmpty` generators, basic generators (`pure`, `choose`, `elements`), combinators (`map`, `oneOf`, `frequency`, `suchThat`), monadic generation
- **Purpose**: Learn manual generator creation before automation
- **Prerequisites**: Basic Idris knowledge

#### 2. Automatic Derivation (`2_Automatic_Derivation.md`)
- **Main Topic**: Using `deriveGen` to automatically create generators
- **Key Concepts**: `deriveGen` macro, fuel parameter for recursion control, handling simple types, sum types, recursive types, dependent types, external generator dependencies
- **Purpose**: Automate generator creation for complex data types
- **Prerequisites**: Understanding of Gen monad from File 1

### Level 2: Core Engine
**Advanced Topics: Derivation Engine Internals**

#### 3. Recursion Analysis (`3_Recursion_Analysis.md`)
- **Main Topic**: How DepTyCheck handles recursive data types safely
- **Key Concepts**: Fuel-based recursion control, constructor recursiveness analysis (`ConsRecs`), `SpendingFuel` vs `StructurallyDecreasing` recursion, constructor weighting
- **Purpose**: Understand safe generation of recursive types
- **Prerequisites**: Basic generator derivation knowledge

#### 4. Deep Constructor Analysis (`4_Deep_Constructor_Analysis.md`)
- **Main Topic**: Analyzing complex type expressions and dependencies
- **Key Concepts**: `analyseDeepConsApp` function, dependency resolution for GADTs, `BindExprFun` for expression reconstruction, type determination analysis
- **Purpose**: Handle complex dependent type generation
- **Prerequisites**: Understanding of dependent types

#### 5. Signature Analysis (`5_Signature_Analysis.md`)
- **Main Topic**: How DepTyCheck parses and understands generator signatures
- **Key Concepts**: `GenSignature` record structure, given vs generated parameters, external generator signatures, dependent pair analysis
- **Purpose**: Understand signature parsing for code generation
- **Prerequisites**: Basic type system knowledge

#### 6. Derivation Core Engine (`6_Derivation_Core_Engine.md`)
- **Main Topic**: The complete pipeline architecture for generator derivation
- **Key Concepts**: Four-stage pipeline architecture, dependency management and orchestration, state management with `ClosuringContext`, recursive derivation handling
- **Purpose**: Understand the complete derivation process
- **Prerequisites**: Knowledge from Files 3-5

#### 7. Single Type Derivation (`7_Single_Type_Derivation.md`)
- **Main Topic**: Generating complete generators for individual data types
- **Key Concepts**: `DeriveBodyForType` interface, constructor-specific derivation, fuel-based decision logic, GADT index checking
- **Purpose**: Focus on single-type derivation process
- **Prerequisites**: Understanding of derivation pipeline

### Level 3: Quality Assurance
**Testing and Validation**

#### 8. Coverage Tracking (`8_Coverage_Tracking.md`)
- **Main Topic**: Tracking which code paths are exercised by generators
- **Key Concepts**: `withCoverage` macro, `ModelCoverage` and `CoverageGenInfo` structures, label-based coverage collection, coverage analysis
- **Purpose**: Ensure comprehensive test coverage
- **Prerequisites**: Basic generator usage

#### 9. Model Coverage (`9_Model_Coverage.md`)
- **Main Topic**: Advanced coverage analysis techniques
- **Key Concepts**: Coverage report interpretation, blind spot detection, multi-run aggregation, coverage quality gates
- **Purpose**: Advanced coverage analysis and quality assurance
- **Prerequisites**: Basic coverage tracking knowledge

### Level 4: Advanced Applications
**Real-World Use Cases**

#### 10. Data Structures (`10_Data_Structures.md`)
- **Main Topic**: Generating constrained data structures
- **Key Concepts**: Sorted lists with ordering constraints, unique element lists, sorted binary trees, covering sequences with bitmask constraints
- **Purpose**: Practical examples of constrained type generation
- **Prerequisites**: Advanced derivation knowledge

#### 11. Primitive Imperative Language (`11_Primitive_Imperative_Language.md`)
- **Main Topic**: Generating complete, valid computer programs
- **Key Concepts**: PIL-Reg (imperative language with registers), PIL-Fun (functional language with multiple backends), PIL-Dyn (dynamic register management), multi-language transpilation
- **Purpose**: Demonstrate DepTyCheck's most advanced capabilities
- **Prerequisites**: Comprehensive DepTyCheck knowledge

### Level 5: Customization and Optimization
**Fine-Tuning and Advanced Features**

#### 12. Derivation Tuning (`12_Derivation_Tuning.md`)
- **Main Topic**: Customizing automatic derivation behavior
- **Key Concepts**: `GenOrderTuning` for generation sequence control, `ProbabilityTuning` for data distribution adjustment, integration with derivation strategies, performance optimization
- **Purpose**: Fine-tune automatic derivation for specific needs
- **Prerequisites**: Understanding of derivation pipeline

#### 13. Label Management (`13_Label_Management.md`)
- **Main Topic**: Debugging and tracking generator origins
- **Key Concepts**: `Label` type and `CanManageLabels` interface, runtime label processing, external generator coordination, debugging applications
- **Purpose**: Debug complex generator chains
- **Prerequisites**: Basic generator usage

#### 14. Emptiness Tracking (`14_Emptiness_Tracking.md`)
- **Main Topic**: Handling generators that might not produce values
- **Key Concepts**: `NonEmpty` vs `MaybeEmpty` guarantees, emptiness propagation rules, handling impossible types (`Fin 0`), `NoWeaker` relation
- **Purpose**: Safe handling of potentially empty generators
- **Prerequisites**: Basic generator concepts

## Thematic Groupings

### Core Concepts Group
- **Files**: 1, 2, 14
- **Focus**: Fundamental generator creation and safety

### Derivation Engine Group
- **Files**: 3, 4, 5, 6, 7
- **Focus**: Internal mechanics of automatic derivation

### Quality Assurance Group
- **Files**: 8, 9
- **Focus**: Testing and validation of generators

### Advanced Applications Group
- **Files**: 10, 11
- **Focus**: Real-world use cases and complex scenarios

### Customization Group
- **Files**: 12, 13
- **Focus**: Fine-tuning and debugging

## Learning Pathways

### Beginner Path
1. Start with **File 1** (Generator Monad) to understand manual creation
2. Move to **File 2** (Automatic Derivation) for automation
3. Learn **File 14** (Emptiness Tracking) for safety
4. Practice with **File 8** (Coverage Tracking) for testing

### Intermediate Path
1. Study **Files 3-7** to understand the derivation engine
2. Apply knowledge with **File 10** (Data Structures)
3. Learn tuning with **File 12** (Derivation Tuning)

### Advanced Path
1. Master **File 11** (PIL Examples) for program generation
2. Deepen with **File 4** (Deep Constructor Analysis)
3. Optimize with **File 12** (Derivation Tuning)

## Key Cross-References

- **Fuel parameter**: Introduced in File 2, used throughout Files 3-7
- **deriveGen macro**: Core concept in File 2, detailed in Files 5-7
- **Coverage tracking**: Files 8-9 complement each other
- **Label system**: File 13 builds on labeling concepts from File 8
- **Emptiness concept**: File 14 provides foundation for safety in all files

## Diátaxis Framework Assessment

### Diátaxis Alignment Scores (0-10)

**Excellent Alignment (8-10):**
- **10_Data_Structures.md** - 9/10 - Strong hands-on approach with practical exercises
- **14_Emptiness_Tracking.md** - 9/10 - Superb tutorial structure with clear learning objectives
- **8_Coverage_Tracking.md** - 8/10 - Good practical workflow with step-by-step guidance
- **12_Derivation_Tuning.md** - 8/10 - Clear practical applications and tuning examples

**Good Alignment (6-7):**
- **1_Generator_Monad.md** - 7/10 - Solid foundational tutorial with practical examples
- **9_Model_Coverage.md** - 7/10 - Clear learning objectives and three-step process
- **13_Label_Management.md** - 7/10 - Practical debugging focus with hands-on examples

**Fair Alignment (4-5):**
- **2_Automatic_Derivation.md** - 6/10 - Some technical over-explanation but good progression
- **11_Primitive_Imperative_Language.md** - 6/10 - Real-world examples but could use more hands-on
- **5_Signature_Analysis.md** - 5/10 - Mixed practical/theoretical approach

**Poor Alignment (2-4):**
- **3_Recursion_Analysis.md** - 4/10 - Overly technical with internal implementation focus
- **7_Single_Type_Derivation.md** - 4/10 - Internal interface focus without clear learning objectives
- **4_Deep_Constructor_Analysis.md** - 3/10 - Abstract implementation details dominate
- **6_Derivation_Core_Engine.md** - 2/10 - No practical learning activities, reads like internal docs

### Diátaxis Principles Assessment

**Strongest Diátaxis Alignment:**
- Files that focus on practical, hands-on activities with clear learning goals
- Tutorials with immediate practice opportunities and concrete examples
- Documents that maintain clear teacher-pupil relationship throughout

**Areas for Improvement:**
- Reduce internal implementation details in favor of user-facing concepts
- Strengthen learning narratives and "feeling of doing" exercises
- Increase consistency in applying Diátaxis principles across all tutorials

**Recommended Learning Order (Diátaxis-Optimized):**
1. **Start with high-scoring tutorials**: 1, 10, 14, 8, 12
2. **Progress to intermediate**: 9, 13, 2, 11
3. **Reference technical details**: 5, 3, 7, 4, 6 (as needed)

This assessment helps identify which tutorials provide the best learning experience according to Diátaxis pedagogical principles.