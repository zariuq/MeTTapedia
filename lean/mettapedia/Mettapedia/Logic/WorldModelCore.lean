import Mettapedia.Logic.PLNWorldModelGeneric
import Mettapedia.Logic.PLNWorldModelProfiles
import Mettapedia.OSLF.Framework.GSLTEvidence
import Mathlib.Analysis.Complex.Basic

/-!
# World Model Core: The Abstraction Hierarchy

This file connects the existing world-model abstractions into a coherent
hierarchy.  No new abstractions are invented — the pieces already exist.

## The Hierarchy (bottom to top)

```
AdditiveWorldModel State Query Ev    ← state-add, any Ev, no zero law
        │
        │  + evidence_zero          = GSLTEvidenceAssignment (≃ AddMonoidHom)
        │
        │  + Ev = BinaryEvidence          = BinaryWorldModel (binary, current PLN core)
        │
        │  + typed queries          = WorldModelSigma
        │
        ▼  (extra layers on top)
ForgettingLayer                     ← forgetting, exact inverse
ProvenanceLayer                     ← source labels, trust gates
ConservationPack                    ← anti-hallucination, Noether
```

## Key Results in This File

1. **Structural equivalence** (kernel-checked):
   `GSLTEvidenceAssignment ≃ AddMonoidHom(State, Query → V)`
   via `equivGSLTProfileHom` — both directions are definitional (rfl).

2. **Bridges** (kernel-checked):
   - `gsltOfZPGWM` : ZeroPreservingGWM → GSLTEvidenceAssignment
   - `zpgwmOfGSLT` : GSLTEvidenceAssignment → ZeroPreservingGWM
   - `instZPGWMOfWorldModel` : BinaryWorldModel → ZeroPreservingGWM

3. **Non-additive views** (structural no-go, kernel-checked):
   - `strength_not_additive` : toStrength is NOT an AddMonoidHom
   - `total_additive` : total evidence IS additive (positive contrast)

## Design Principle

The additive extraction `State →+ (Query → Ev)` is the algebraic core
shared by:
- Binary evidence WM-PLN (Ev = BinaryEvidence)
- Dirichlet/Normal-Gamma carriers (Ev = count vectors / sufficient stats)
- Quantum amplitudes à la Meredith (Ev = ℂ)
- Classical probability à la Knuth-Skilling (Ev = ℝ≥0∞)

Everything else (forgetting, provenance, views, compiled inference, typed
realization) is structure ON TOP of this core.
-/

namespace Mettapedia.Logic.WorldModelCore

open scoped ENNReal
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelGeneric
open Mettapedia.Logic.PLNWorldModelProfiles
open Mettapedia.OSLF.Framework.GSLTEvidence

/-! ## 1. WorldModel with zero law = AddMonoidHom

The existing `WorldModel` has `evidence_add` but not `evidence_zero`.
The existing `BinaryWorldModel` (binary) has both.
The existing `GSLTEvidenceAssignment` also has both.

We define a zero-preserving generic world model predicate and show it
is equivalent to an `AddMonoidHom` into profiles. -/

/-- A `WorldModel` that also preserves zero.
This is the full additive core: `extract : State →+ (Query → Ev)`. -/
class ZeroPreservingGWM (State Query Ev : Type*)
    [EvidenceType State] [AddCommMonoid Ev]
    extends AdditiveWorldModel State Query Ev where
  /-- Zero state extracts zero evidence. -/
  evidence_zero : ∀ q, evidence (0 : State) q = (0 : Ev)

/-- Bundle a zero-preserving generic world model into an AddMonoidHom. -/
noncomputable def zpgwmProfileHom
    {State Query Ev : Type*} [EvidenceType State] [AddCommMonoid Ev]
    [inst : ZeroPreservingGWM State Query Ev] :
    AddMonoidHom State (Query → Ev) where
  toFun W q := inst.evidence W q
  map_zero' := funext inst.evidence_zero
  map_add' W₁ W₂ := funext (inst.evidence_add W₁ W₂)

/-- Recover a zero-preserving GWM from an AddMonoidHom. -/
def zpgwmOfProfileHom
    {State Query Ev : Type*} [EvidenceType State] [AddCommMonoid Ev]
    (F : AddMonoidHom State (Query → Ev)) :
    ZeroPreservingGWM State Query Ev where
  evidence W q := F W q
  evidence_add W₁ W₂ q := by
    exact congrArg (fun f => f q) (F.map_add W₁ W₂)
  evidence_zero q := by
    exact congrArg (fun f => f q) F.map_zero

-- The real structural equivalence is `equivGSLTProfileHom` below
-- (GSLTEvidenceAssignment ≃ AddMonoidHom, with rfl both directions).

/-! ## 2. Bridge: GSLTEvidenceAssignment ↔ ZeroPreservingGWM

They are the same algebraic object, just with different packaging. -/

-- GSLTEvidenceAssignment and ZeroPreservingGWM are the same
-- algebraic object with different packaging:
-- GSLTEvidenceAssignment uses [AddCommMonoid State]
-- ZeroPreservingGWM uses [EvidenceType State] (which extends AddCommMonoid)
-- Every ZeroPreservingGWM gives a GSLTEvidenceAssignment.

/-- Convert a ZeroPreservingGWM to a GSLTEvidenceAssignment. -/
def gsltOfZPGWM
    {State Query V : Type*}
    [EvidenceType State] [AddCommMonoid V]
    [inst : ZeroPreservingGWM State Query V] :
    GSLTEvidenceAssignment State Query V where
  extract := inst.evidence
  extract_add := inst.evidence_add
  extract_zero := inst.evidence_zero

/-- Convert a GSLTEvidenceAssignment to a ZeroPreservingGWM (reverse bridge). -/
def zpgwmOfGSLT
    {State Query V : Type*}
    [EvidenceType State] [AddCommMonoid V]
    (ea : GSLTEvidenceAssignment State Query V) :
    ZeroPreservingGWM State Query V where
  evidence := ea.extract
  evidence_add := ea.extract_add
  evidence_zero := ea.extract_zero

/-! ## 3. The Structural Equivalence

`GSLTEvidenceAssignment` and `AddMonoidHom(State, Query → V)` are
equivalent as data.  This is the real content — not just existence
(`Nonempty ↔ Nonempty`) but actual structure-preserving bijection.
Proved in `GSLTEvidence.lean` via `toProfileHom` + `ofProfileHom`;
the roundtrips are both definitional (`rfl`). -/

/-- The structural equivalence between GSLTEvidenceAssignment and
    AddMonoidHom into profiles.  Both directions are definitional. -/
def equivGSLTProfileHom
    {State Query V : Type*}
    [AddCommMonoid State] [AddCommMonoid V] :
    GSLTEvidenceAssignment State Query V ≃ (State →+ (Query → V)) where
  toFun := GSLTEvidenceAssignment.toProfileHom
  invFun := GSLTEvidenceAssignment.ofProfileHom
  left_inv ea := by cases ea; rfl
  right_inv f := by rfl

/-! ## 4. The existing BinaryWorldModel is a ZeroPreservingGWM

Every binary BinaryWorldModel instance automatically gives a ZeroPreservingGWM. -/

noncomputable instance instZPGWMOfWorldModel
    {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query] :
    ZeroPreservingGWM State Query BinaryEvidence where
  evidence := BinaryWorldModel.evidence
  evidence_add := BinaryWorldModel.evidence_add
  evidence_zero := BinaryWorldModel.evidence_zero

/-! ## 4. Non-Additive Views (Structural No-Go Theorems)

Views (strength, confidence, Born rule) are NOT additive shadows.
They are lossy projections that do not commute with addition.
These theorems DETERMINE the architecture: you cannot chain on views
and expect correct results. -/

/-- **Strength is not additive**: there exist evidence values where
`strength(e₁ + e₂) ≠ strength(e₁) + strength(e₂)`.

Counterexample: e₁ = ⟨1, 0⟩, e₂ = ⟨0, 1⟩.
strength(e₁ + e₂) = strength(1, 1) = 1/2.
strength(e₁) + strength(e₂) = 1 + 0 = 1.

This is a VIEW, not an additive shadow.  It determines the entire
inference architecture: carry evidence, extract views only at the end. -/
theorem strength_not_additive :
    ∃ e₁ e₂ : BinaryEvidence,
      BinaryEvidence.toStrength (e₁ + e₂) ≠ BinaryEvidence.toStrength e₁ + BinaryEvidence.toStrength e₂ := by
  use ⟨1, 0⟩, ⟨0, 1⟩
  simp [BinaryEvidence.toStrength, BinaryEvidence.total, BinaryEvidence.hplus_def]

/-- **Total evidence is additive but confidence is NOT linear**:
confidence is `n/(n+k)`, which is concave.  So `conf(e₁+e₂) < conf(e₁) + conf(e₂)`
for nonzero inputs.

More precisely: total evidence IS additive (`(e₁+e₂).total = e₁.total + e₂.total`),
but confidence `total/(total+k)` is a nonlinear function of total, so it is NOT
an additive morphism.  This is why views are lossy projections. -/
theorem total_additive (e₁ e₂ : BinaryEvidence) :
    (e₁ + e₂).total = e₁.total + e₂.total := by
  simp [BinaryEvidence.total, BinaryEvidence.hplus_def]; ring

/-- **The Born rule is not additive**: `|z₁ + z₂|² ≠ |z₁|² + |z₂|²`
in general.  The cross-term `2·Re(z₁·z̄₂)` is quantum interference.

Counterexample: z₁ = 1, z₂ = 1.
|1 + 1|² = |2|² = 4.
|1|² + |1|² = 1 + 1 = 2.

This is the mathematical content of quantum mechanics: the passage
from amplitudes to probabilities (the Born rule) destroys the additive
structure.  L. Gregory Meredith's weight map is additive; its Born-rule
shadow is not.

Reference: `Complex.normSq_add` in Mathlib. -/
theorem born_not_additive :
    ∃ z₁ z₂ : ℂ,
      Complex.normSq (z₁ + z₂) ≠ Complex.normSq z₁ + Complex.normSq z₂ := by
  use 1, 1
  simp [Complex.normSq_add, Complex.normSq_one, Complex.mul_conj]

/-! ## 6. Summary: The Abstraction Hierarchy

```
ZeroPreservingGWM State Query Ev   ← THE ALGEBRAIC CORE
  ≃ GSLTEvidenceAssignment          (bridges: gsltOfZPGWM, zpgwmOfGSLT)
  ≃ AddMonoidHom(State, Query → Ev) (equiv: equivGSLTProfileHom, rfl both dirs)
  │
  │ specializations by Ev:
  ├─ Ev = BinaryEvidence         → BinaryWorldModel (binary PLN)
  ├─ Ev = DirichletEvidence → Dirichlet carrier
  ├─ Ev = NGEvidence       → Normal-Gamma carrier
  ├─ Ev = ℂ                → Meredith weight map (future)
  └─ Ev = ℝ≥0∞             → KS probability (future)
  │
  │ extra layers (ON TOP):
  ├─ ForgettingLayer       → exact retraction
  ├─ ScopedTrackedWhichState → provenance
  ├─ EvidenceConservationPack → Noether conservation
  ├─ WMFullVertex          → 13-axis typed realization
  └─ Σ-guarded rewrites    → compiled BN inference
  │
  │ non-additive projections (VIEWS):
  ├─ toStrength            → NOT additive (proved: strength_not_additive)
  ├─ toConfidence          → NOT additive (concavity argument)
  └─ Born |·|²             → NOT additive (proved: born_not_additive)
```

The core insight: everything below the line is structure on TOP of the
additive extraction.  Everything above is a specialization by choosing V.
Views are PROJECTIONS that are provably non-additive.
-/

end Mettapedia.Logic.WorldModelCore
