# Meredith GSLT Framework — MeTTapedia Formalization Plan

## Source Papers

1. **Computation, Causality, and Consciousness** (Meredith, 2026-03-15 draft)
   - Part I: Towards a Theory of Causality (§§1–11)
   - Part II: Emergent Ontology in Massive Agent Populations (§§12–21)
   - Part III: Life as Computational Replication (§§22–27)
   - Part IV: The Hypercomputational Tower (§§28–35)

2. **Generating Hypercubes of Type Systems** (Stay, Meredith, Wells, 2026-03)
   - Lambda theories → operational theories → hypercube of type systems

## Existing Formalization (5,270 lines)

### Core/ (771 lines, 0 sorries)
- `LambdaTheoryCategory.lean` — λ-theories with equality as CCCs + finite limits + fibration ✅
- `Web.lean` — Webs, coding functions, graph models (3 sorries: theory, sensible, semisensible)
- `ChangeOfBase.lean` — f*, ∃f, ∀f with adjunctions + Beck-Chevalley ✅

### GraphTheory/ (3,438 lines)
- `Basic.lean` — De Bruijn λ-terms, substitution lemmas, parallel reduction (3 sorries)
- `Approximants.lean` — Approximation orders on terms (2 sorries)
- `Substitution.lean` — Böhm tree substitution (3 sorries)
- `BohmTree.lean` — Böhm tree construction (7 sorries)
- `ParallelReduction.lean` — Church-Rosser via parallel reduction ✅
- `WeakProduct.lean` — Weak products of graph models (5 sorries)

### Topos/ (1,061 lines)
- `PredicateFibration.lean` — Predicate fibration over a topos
- `Yoneda.lean` — Yoneda embedding
- `SubobjectClassifier.lean` — Subobject classifier Ω

## Gap Analysis: Paper vs Formalization

### ✅ Already formalized (Part I foundations):
- GSLT as categorical object (Def 2.1 — partially via LambdaTheoryWithEquality)
- Morphisms of GSLTs (Def 2.2 — via LambdaTheoryMorphism)
- Graph models, webs, coding functions (Defs from Bucciarelli-Salibra)
- Subobject fibration with Frame-valued fibers
- Change-of-base functors with adjunctions
- Beck-Chevalley condition
- Modal operators F!, F* (step-forward)
- De Bruijn λ-terms with substitution
- Parallel reduction and Church-Rosser
- Böhm trees (partial)

### 🔲 Not yet formalized (Part I — highest priority):

#### Tier 1: Core GSLT definition (clean, no hacks)
- [x] **GSLT as triple (T, E, R)** — grammar + equations + rewrite rules
  - Formalized abstractly in `Core/GSLT.lean`
  - Paper Def 2.1: grammar T, equations E (≡), rules R (→)
- [x] **Traces** (Def 3.1) — finite sequences of rule applications
  - Formalized in `Causality/Trace.lean`
- [x] **Reversible Envelope S†** (Defs 3.2–3.4) — extended terms ⟨P, τ⟩, forward/backward rules
  - Current status: reversible-step kernel on `⟨P, τ⟩` states formalized in `Causality/Trace.lean`
- [x] **Proposition 3.1** — η : S → S†, π : S† → S, π ∘ η = id
  - Current status: embedding/projection kernel and roundtrip theorem formalized in `Causality/Trace.lean`

#### Tier 2: Causal structure
- [x] **Synchronization trees** — closed (Def 4.1) and open (Def 4.2)
  - Formalized in `Causality/SyncTree.lean`
- [ ] **Causal graphs** (Def 4.3) — sync trees as causal sets
  - Current status: preorder kernel formalized in `Causality/SyncTree.lean`; antisymmetry/local-finiteness causal-set claims remain open
- [ ] **Causal distance** (Def 4.4) — d_min, d_max in both closed and open trees
  - Current status: explicit path objects and path lengths are formalized in `Causality/SyncTree.lean`; min/max distance operators are not yet extracted

#### Tier 3: Logic layer
- [x] **Minimal contexts** (Def 5.1) — Milner-Sewell-Leifer construction
  - Current status: faithful abstract interface via `Logic/MinimalContext.lean`; the rho-calculus evaluation-context instance is now packaged concretely in `Meredith/RhoMinimalContext.lean`
- [x] **Context-decorated HML** (Def 5.2) — modal logic with context labels
  - Formalized over `MinimalContext` in `Logic/ContextHML.lean`
- [ ] **Adequacy theorem** (Thm 5.1) — bisimilarity ↔ HML equivalence
- [ ] **Logical metric** (Def 5.3) — ultrametric d_HML on T(S)/∼
  - Current status: modal depth, depth-bounded HML agreement, distinguishing witnesses, and a 0/1 pseudoultrametric approximation are formalized in `Logic/LogicalMetric.lean`; `Meredith/WeaknessBridge.lean` now proves that such finite-depth witnesses certify genuine quotient-level distinction under adequacy soundness; the full quotient-level ultrametric remains open

#### Tier 4: Dynamics
- [x] **Weight map** (Def 6.1) — w_r^+ : HML(K) → ℂ
  - Current status: abstract weight structures and weighted GSLTs formalized in `Dynamics/WeightCost.lean`
- [ ] **Path amplitude** (Def 6.3) — product of weights along path
  - Current status: finite-support amplitude kernel formalized in `Dynamics/PathIntegral.lean`
- [ ] **Action functional** (Def 6.4) — S[γ] = Σ log w_r^+(ϕ_i)
- [x] **Resource algebra** (Def 7.1) — commutative ordered monoid
  - Current status: vector-account and debit/solvency kernel formalized in `Dynamics/WeightCost.lean`; stronger algebraic axioms can still be sharpened
- [x] **Cost map** (Def 7.2) — c_r : HML(K) → A^k
  - Formalized abstractly in `Dynamics/WeightCost.lean`
- [x] **Conservation theorem** (Thm 7.1) — net account change = 0 on closed resource-aware cycles in `Synthesis/MainConservation.lean`
- [ ] **Extended modal operator** (Def 8.1) — ⟨K, w+, w−, c, A⟩ϕ
  - Current status: minimal-context weighted/resource-trace HML kernel formalized in `Dynamics/ExtendedHML.lean`; full paper-faithful state semantics remains to tighten

#### Tier 5: Quantum structure
- [x] **Amplitude-weighted GSLT** (Def 9.1) — complex-weight specialization captured by `Dynamics/PathIntegral.lean`
- [x] **Transition amplitude** (Def 9.2) — finite-support version over explicit path families in `Dynamics/PathIntegral.lean`
- [x] **Quantum-weighted reversible GSLT** (Constr. 10.1) — `⟨P, τ, A⟩` states and reversible debit/credit dynamics in `Synthesis/MainConservation.lean`
- [x] **Main Conservation Theorem** (Thm 10.1(i)) — resource part proved in `Synthesis/MainConservation.lean`
- [ ] **Main Conservation Theorem** (Thm 10.1(ii)) — full global probability conservation from local unitarity
  - Current status: one-step finite witness proved, global finite-support normalization exposed as an explicit interface in `Synthesis/MainConservation.lean`
- [ ] **Main Conservation Theorem** (Thm 10.1(iii)) — full CPT automorphism proof
  - Current status: candidate CPT transform and symmetry interface formalized in `Synthesis/MainConservation.lean`

### 🔲 Part II: Emergent Ontology (lower priority, speculative)
- [ ] Ontological isolation (Def 13.1)
- [ ] Agents and scientific method (Def 14.1)
- [ ] Interactive GSLTs and behavioral primes (Defs 15.1–15.3)
- [ ] Communication degradation (Defs 16.1–16.2)
- [ ] Logical topology (Def 17.1)
- [ ] Coherence clusters and nerve (Defs 18.1–18.4)

### 🔲 Part III: Life (lower priority, speculative)
- [x] Assembly theory kernel (Defs 23.1–23.4) — elementary terms, minimum causal depth, and namespace copy number in `Life/AssemblyTheory.lean`
- [ ] Replication as fixed point (§24)
  Current status: derived rho fixed-point kernel `!P ⇝ᵈ* P | !P` and arbitrary finite unfoldings in `Life/ReplicationFixedPoint.lean`; pure quote/COMM-only concurrent `Y` remains open.
- [ ] Phase transitions (§25)

### 🔲 Part IV: Hypercomputational Tower (lower priority, exploratory)
- [ ] Turing-complete GSLT (Def 29.1)
- [ ] Oracle terms and extensions (Defs 29.2–29.3)
- [ ] Hypercomputational fibration (Def 29.4)
- [ ] Sentience (Defs 31.1–31.4)
- [ ] Consciousness at level α (Def 32.1)

### 🔲 Hypercube Paper:
- [ ] Lambda theory (Def 4.1) — operational theory with term formers, equations, rewrites
- [ ] Equationally admissible sort assignments (Def 5.1)
- [ ] Generated modalities from rewrite rules
- [ ] Hypercube construction from sort slot assignments

## Implementation Principles (NO HACKS)

1. **Use Mathlib types** — don't reinvent Category, Functor, Frame, etc.
2. **Abstract over the term grammar** — use a typeclass/structure for GSLT terms, not hardcoded λ-terms
3. **Keep sorry count bounded** — each sorry must have a clear mathematical statement of what's needed
4. **Separate axioms from theorems** — if a result is axiomatized (assumed), mark it explicitly
5. **Build bottom-up** — each file should compile with all its imports
6. **Document paper references** — every definition cites the paper definition number

## Proposed File Structure

```
GSLT/
├── Core/
│   ├── LambdaTheoryCategory.lean     ✅ (existing)
│   ├── Web.lean                       ✅ (existing, 3 sorries)
│   ├── ChangeOfBase.lean              ✅ (existing)
│   ├── GSLT.lean                      🆕 Abstract GSLT (T, E, R)
│   └── Morphism.lean                  🆕 Category of GSLTs
├── Causality/
│   ├── Trace.lean                     🆕 Traces (Def 3.1)
│   ├── ReversibleEnvelope.lean        🆕 S† construction (Defs 3.2–3.4)
│   ├── SyncTree.lean                  🆕 Closed/open sync trees (Defs 4.1–4.2)
│   └── CausalDistance.lean            🆕 Causal metrics (Def 4.4)
├── Logic/
│   ├── MinimalContext.lean            🆕 MSL construction (Def 5.1)
│   ├── ContextHML.lean               🆕 Context-decorated HML (Def 5.2)
│   ├── Adequacy.lean                  🆕 Bisim ↔ HML (Thm 5.1)
│   └── LogicalMetric.lean            🆕 Ultrametric d_HML (Def 5.3)
├── Dynamics/
│   ├── WeightMap.lean                 🆕 Weight map, path amplitude (Defs 6.1–6.4)
│   ├── ResourceAlgebra.lean           🆕 Resource algebras (Def 7.1)
│   ├── CostMap.lean                   🆕 Cost map, conservation (Defs 7.2–7.5, Thm 7.1)
│   ├── ExtendedHML.lean              🆕 Extended modal operators (Def 8.1)
│   └── QuantumAmplitude.lean          🆕 Complex amplitudes, path integral (Defs 9.1–9.3)
├── Synthesis/
│   └── MainConservation.lean          🆕 Construction 10.1, Theorem 10.1 kernel
├── GraphTheory/                       ✅ (existing, supports Core)
│   ├── Basic.lean
│   ├── Approximants.lean
│   ├── Substitution.lean
│   ├── BohmTree.lean
│   ├── ParallelReduction.lean
│   └── WeakProduct.lean
├── Topos/                             ✅ (existing, supports Core)
│   ├── PredicateFibration.lean
│   ├── Yoneda.lean
│   └── SubobjectClassifier.lean
└── Hypercube/                         🆕 (from Hypercube paper)
    ├── OperationalTheory.lean         🆕 Abstract operational theory
    ├── SortAssignment.lean            🆕 Sort slots and assignments
    └── HypercubeConstruction.lean     🆕 The hypercube of type systems
```

## Session 1 Plan: Core GSLT Definition

Start with `GSLT/Core/GSLT.lean` — the abstract GSLT triple (T, E, R).
This is the foundation everything else builds on.

Key design decision: How abstract should the term grammar be?
- Option A: Fully abstract (Type with operations) — most general but hard to prove things
- Option B: Parameterized by a signature — middle ground
- Option C: Inductive type with explicit constructors — concrete but less general

**Recommendation**: Option B — a GSLT is parameterized by a `Signature` that specifies
term constructors, and the grammar is the free term algebra over the signature.
This matches the paper's intent (GSLTs include λ-calculus, π-calculus, ρ-calculus, etc.)
while being concrete enough to prove structural results.
