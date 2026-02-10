# OSLF: Operational Semantics in Logical Form (WIP)

Lean 4 formalization deriving modal operators ◇/□ from reduction relations with proven Galois connection ◇ ⊣ □.

## What's Formalized

**Structures** (Framework/RewriteSystem.lean):
- `RewriteSystem`: sorts, terms, reduction relation
- `OSLFTypeSystem`: predicates (as Frames), modal operators ◇/□, Galois connection specification
- `NativeTypeOf`: (sort, predicate) pairs
- `Substitutability`: bisimilarity ↔ logical equivalence

**Main results**:
1. **Four concrete `OSLFTypeSystem` instances** with proven Galois connections:
   - ρ-calculus (RhoCalculus/Soundness.lean)
   - λ-calculus (Framework/LambdaInstance.lean)
   - Petri nets (Framework/PetriNetInstance.lean)
   - TinyML (Framework/TinyMLInstance.lean)

2. **Type preservation** for ρ-calculus: `Γ ⊢ P : τ  ∧  P ~> Q  ⟹  Γ ⊢ Q : τ`

3. **Executable reduction engines** with soundness proofs (RhoCalculus/Engine.lean, MeTTaIL/Engine.lean)

4. **Some categorical structure**:
   - Galois connection → Mathlib `Adjunction` (Framework/CategoryBridge.lean)
   - Constructor categories (Framework/ConstructorCategory.lean)
   - Beck-Chevalley analysis with proven counterexample (Framework/BeckChevalleyOSLF.lean)

**What this corresponds to in OSLF papers**:
- Section 4: Predicates as frames (complete Heyting algebras) ✓
- Section 6: Modal operators ◇/□ from reduction ✓
- Section 11: Substitutability theorem ✓

## Relation to Full OSLF/GSLT

**Not yet formalized** (Williams & Stay 2021):
- **§2 Structured λ-theories**: λ-theories with behavior (Definition 1-3, Theorem 4)
- **§3 Presheaf construction P**: Embedding λ-theory into topos (Definition 6)
- **§4 Native type theory**: Composite 2-functor λ-theory →^P Topos →^L HDTΣ
- **§5 Applications**: Structure/behavior reasoning, encoding between languages

**Not yet formalized** (Meredith & Stay 2014):
- **§3 Full second-order signatures**: We use simplified RewriteSystem
- **§5 GSLT category**: Full 2-categorical treatment
- **§8-9 Behavioral equivalence**: Full bisimulation theory
- **§10 Internalization**: Types as objects in the theory

**What corresponds to our formalization**:
- §4 (predicates as frames), §6 (modal operators), §11 (substitutability)

## Scope of This Formalization

**What's proven (0 sorries)**:
- Basic OSLF algorithm: RewriteSystem → modal operators ◇/□
- Galois connection ◇ ⊣ □ for 4 languages (ρ-calc, λ-calc, Petri nets, TinyML)
- Executable reduction engines with soundness proofs
- Type preservation for ρ-calculus
- Some categorical structure (constructor categories, basic fibrations)

**What's NOT formalized**:
- Presheaf construction (λ-theory → Topos)
- Native type theory (full HDTΣ with structure+behavior)
- Structured λ-theories with internal operational semantics
- Full GSLT 2-categorical framework
- Behavior-respecting morphisms between theories

**Statistics**:
- 22,320 lines across 58 Lean 4 files
- 0 sorries in core (29 sorries in π→ρ encoding, separate project)

## Quick Start

**Core algorithm definition:**
- [`Framework/RewriteSystem.lean`](Framework/RewriteSystem.lean) — Input/output structures (196 lines)

**Working example with full proofs:**
- [`RhoCalculus/Soundness.lean`](RhoCalculus/Soundness.lean) — ρ-calculus with proven Galois connection

**Pipeline implementation:**
- [`Framework/TypeSynthesis.lean`](Framework/TypeSynthesis.lean) — `langOSLF` function (201 lines)

## Directory Structure

```
OSLF/
├── Framework/              # Abstract OSLF algorithm (4,400 lines, 0 sorries)
│   ├── RewriteSystem.lean      # Core input/output structures ⭐
│   ├── TypeSynthesis.lean      # langOSLF pipeline ⭐
│   ├── ConstructorCategory.lean # Categorical foundations
│   ├── ConstructorFibration.lean # Fibered structure
│   ├── DerivedTyping.lean       # Auto-generated typing rules
│   ├── LambdaInstance.lean      # λ-calculus example
│   ├── PetriNetInstance.lean    # Petri net example
│   ├── TinyMLInstance.lean      # CBV λ-calc with booleans/pairs
│   └── ...
│
├── RhoCalculus/           # ρ-calculus instance (3,893 lines, 0 sorries)
│   ├── Syntax.lean             # Process syntax
│   ├── Reduction.lean          # COMM, DROP rules
│   ├── StructuralCongruence.lean # 11 SC rules
│   ├── Soundness.lean          # Proven Galois connection ⭐
│   ├── Engine.lean             # Executable reduction
│   └── ...
│
├── MeTTaIL/               # Meta-language for calculi (2,929 lines, 0 sorries)
│   ├── Syntax.lean             # Pattern AST
│   ├── Substitution.lean       # Capture-avoiding substitution
│   ├── Match.lean              # Pattern matcher
│   ├── Engine.lean             # Generic reduction engine
│   └── ...
│
├── PiCalculus/            # π-calculus (6,582 lines, 29 sorries)
│   ├── Syntax.lean             # π-calculus syntax
│   ├── Reduction.lean          # π-calculus reduction
│   ├── RhoEncoding.lean        # π → ρ encoding
│   ├── ForwardSimulation.lean  # RF fragment forward sim (0 sorries)
│   └── ...
│
├── Formula.lean           # Verified bounded model checker (582 lines)
└── Main.lean              # Re-exports
```

## Key Results

### 1. Abstract Framework (0 sorries)

**Theorem** (`Framework/RewriteSystem.lean`): For any `RewriteSystem`, the OSLF algorithm produces an `OSLFTypeSystem` with:
- Modal operators ◇ (diamond) and □ (box) derived from the reduction relation
- Galois connection: `◇ ⊣ □`

### 2. Concrete Instance: ρ-Calculus (0 sorries)

**Theorem** (`RhoCalculus/Soundness.lean`): The ρ-calculus type system satisfies:
- **Type preservation**: `Γ ⊢ P : τ  ∧  P ~> Q  ⟹  Γ ⊢ Q : τ`
- **Galois connection**: `◇ ⊣ □` proven directly
- **Substitutability**: Bisimilar processes have the same types

Reduction rules:
```
COMM: {n!(q) | for(x←n){P} | rest} ~> {P[@q/x] | rest}
DROP: *(@P) ~> P
```

### 3. Four Language Instances (0 sorries)

Each language gets a full `OSLFTypeSystem` with proven Galois connection:

1. **ρ-calculus**: Reflective higher-order process calculus
2. **λ-calculus**: Pure untyped lambda calculus
3. **Petri nets**: Simple marking transitions (no binders)
4. **TinyML**: CBV λ-calc with booleans, pairs, thunks

### 4. Categorical Bridge (0 sorries)

- Constructor category built from sort-crossing constructors
- Subobject fibration with change-of-base
- Derived typing rules: modal operator (◇/□/id) assigned automatically
- Beck-Chevalley analysis (proven counterexample for strong condition)

## Example: Petri Net

```lean
-- Define transitions
T1: {A, B, rest} ~> {C, D, rest}  -- consume A+B, produce C+D
T2: {C, rest} ~> {A, rest}        -- consume C, produce A

-- OSLF automatically derives:
petriOSLF : OSLFTypeSystem petriRS

-- With modal operators:
◇{A, D} = "markings that can reach {A, D}"
□{B, C} = "markings whose predecessors are all in {B, C}"

-- And proven Galois connection:
theorem petri_galois : ◇ ⊣ □  -- proven automatically
```

## Building

```bash
cd lean-projects/mettapedia
lake build Mettapedia.OSLF
```

Individual modules:
```bash
lake build Mettapedia.OSLF.Framework.RewriteSystem
lake build Mettapedia.OSLF.RhoCalculus.Soundness
```

## References

**The full OSLF/GSLT framework (NOT fully formalized here)**:
- Meredith & Stay, ["Operational Semantics in Logical Form"](https://arxiv.org/abs/1406.4888) (2014) — Full framework with presheaf construction, topos, GSLT
- Williams & Stay, ["Native Type Theory"](https://www.cl.cam.ac.uk/events/act2021/papers/ACT_2021_paper_23.pdf) (ACT 2021) — Structured λ-theories, 2-functor λ-theory →^P Topos →^L HDTΣ

**This partial formalization**:
- `papers/leanOSLF.pdf` (2026 draft, 17 pages) — Documents what we actually formalized (basic algorithm only)

**What to read to understand the gap**: Williams & Stay §2-3 explain structured λ-theories with behavior and the presheaf construction. We only formalized the modal operators ◇/□, not the full categorical machinery.

## Status

| Component | Lines | Sorries | Status |
|-----------|-------|---------|--------|
| Framework | 4,400 | 0 | ✅ Proven |
| RhoCalculus | 3,893 | 0 | ✅ Proven |
| MeTTaIL | 2,929 | 0 | ✅ Proven |
| Formula | 582 | 0 | ✅ Proven |
| PiCalculus | 6,582 | 29 | ⚠️ Partial |
| **Total** | **22,320** | **29** | |

The 29 sorries are in π→ρ encoding correctness (separate project). Core OSLF formalization has 0 sorries.

## Contributing

The formalization uses Lean 4.27.0 with Mathlib. See `../../CLAUDE.md` for development guidelines.

---

Machine-checked formalization of OSLF modal logic (◇ ⊣ □) for 4 languages. Full categorical framework (presheaf topos, structured λ-theories) not yet formalized.
