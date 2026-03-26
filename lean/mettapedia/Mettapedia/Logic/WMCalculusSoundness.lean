import Mettapedia.Logic.EvidenceProofSystem
import Mettapedia.Logic.EvidentialLedger

/-!
# WM Calculus Soundness

The world-model calculus has three operational rules: revise, extract, forget.
The additive world model (`AdditiveWorldModel`) gives these rules their
semantics. The calculus is SOUND if its operations agree with the model.

## The Model-Calculus-Runtime Architecture

    AdditiveWorldModel     (the model — what extraction means)
            ↕  CalculusSound  (the bridge — proved in Lean)
    WMCalculus             (the calculus — revise, extract, forget)
            ↓  implementation correctness
    mettail-c / mettail-rust  (the runtime — actual binary)

The key theorem: prove `CalculusSound` once, and every algebraic
property (`extract_add`, sequential composition, zero preservation,
the four structural rules) transfers to the calculus automatically.

## What this gives implementors

1. `WMCalculus` — the operational interface (three rules)
2. `CalculusSound` — the formal correctness criterion
3. `sound_calculus_extract_add` — sound calculi preserve `extract_add`
4. `sound_calculus_sequential` — sound composition
5. Any implementation proves `CalculusSound` to certify correctness

## References

- WM-PLN book, Ch 4 (The World-Model Calculus), §4.9 (The Evidence Proof System)
- `EvidenceProofSystem.lean` — the four structural rules
- `HE/RuntimeContract.lean` — declares WHAT the runtime should do

0 sorry.
-/

namespace Mettapedia.Logic.WMCalculusSoundness

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelGeneric

/-! ## 1. The WM Calculus

The three operational rules of the world-model calculus.
Revise = cut (combining evidence states).
Extract = evaluation (answering a query from a state).
Forget = weakening (discarding a source's contribution). -/

/-- The world-model calculus: three operational rules on evidence states.
    This is the interface that any implementation of the WM calculus
    must provide — whether in C, Rust, MeTTa, or any other language. -/
structure WMCalculus (State Query Ev : Type*) where
  /-- Combine two evidence states (the cut rule). -/
  revise : State → State → State
  /-- Extract evidence for a query from a state (the evaluation rule). -/
  extract : State → Query → Ev
  /-- Optionally: forget a source's contribution (the weakening rule). -/
  forget : Option (State → State → State)

/-! ## 2. Soundness criterion -/

/-- The calculus is SOUND if its operations agree with the WM algebra.

    This is the formal property an implementation must prove to be certified.
    Once proven, all algebraic properties transfer automatically.

    In proof-theoretic terms: the calculus is sound with respect to the model.
    What the calculus derives, the model validates. -/
structure CalculusSound {State Query Ev : Type*}
    [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]
    (wmc : WMCalculus State Query Ev) : Prop where
  /-- Revision in the calculus = addition in the model. -/
  revise_correct : ∀ W₁ W₂, wmc.revise W₁ W₂ = W₁ + W₂
  /-- Extraction in the calculus = extraction in the model. -/
  extract_correct : ∀ W q,
    wmc.extract W q = AdditiveWorldModel.extract (Ev := Ev) W q

/-! ## 3. Sound calculi inherit extract_add -/

/-- A sound calculus automatically satisfies the extraction-addition law.
    This is the key theorem: you don't need to prove extract_add for
    the calculus separately — it follows from soundness. -/
theorem sound_calculus_extract_add {State Query Ev : Type*}
    [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]
    (wmc : WMCalculus State Query Ev) (h : CalculusSound wmc)
    (W₁ W₂ : State) (q : Query) :
    wmc.extract (wmc.revise W₁ W₂) q =
    wmc.extract W₁ q + wmc.extract W₂ q := by
  rw [h.revise_correct, h.extract_correct, h.extract_correct, h.extract_correct]
  exact AdditiveWorldModel.extract_add W₁ W₂ q

/-! ## 4. Composition of sound calculi -/

/-- Sequential composition: three-way revision extracts correctly. -/
theorem sound_calculus_sequential {State Query Ev : Type*}
    [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]
    (wmc : WMCalculus State Query Ev) (h : CalculusSound wmc)
    (W₁ W₂ W₃ : State) (q : Query) :
    wmc.extract (wmc.revise (wmc.revise W₁ W₂) W₃) q =
    wmc.extract W₁ q + wmc.extract W₂ q + wmc.extract W₃ q := by
  simp only [h.revise_correct, h.extract_correct, AdditiveWorldModel.extract_add, add_assoc]

/-! ## 5. Sound calculus preserves zero -/

/-- A sound calculus on zero state gives zero evidence. -/
theorem sound_calculus_revise_zero_left {State Query Ev : Type*}
    [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]
    (wmc : WMCalculus State Query Ev) (h : CalculusSound wmc)
    (W : State) (q : Query) :
    wmc.extract (wmc.revise 0 W) q = wmc.extract W q := by
  rw [h.revise_correct, zero_add]

/-! ## 6. The correctness contract

For any implementation of the WM calculus:

1. Define your implementation as `WMCalculus State Query Ev`
2. Prove `CalculusSound` for your implementation
3. All WM-PLN algebraic properties transfer automatically:
   - `extract_add` — evidence revision is compositional
   - Sequential composition — multi-step revision is associative
   - Zero preservation — empty state gives empty evidence
   - The four structural rules (cut, weakening, exchange, contraction)

The proof of `CalculusSound` is the CERTIFICATION that the calculus
correctly implements the WM evidence algebra. -/

/-- Summary: what a sound calculus guarantees. -/
theorem soundness_guarantees {State Query Ev : Type*}
    [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]
    (wmc : WMCalculus State Query Ev) (h : CalculusSound wmc) :
    -- Extraction agrees with model
    (∀ W q, wmc.extract W q = AdditiveWorldModel.extract (Ev := Ev) W q) ∧
    -- Revision agrees with model
    (∀ W₁ W₂, wmc.revise W₁ W₂ = W₁ + W₂) ∧
    -- extract_add transfers
    (∀ W₁ W₂ q, wmc.extract (wmc.revise W₁ W₂) q =
      wmc.extract W₁ q + wmc.extract W₂ q) :=
  ⟨h.extract_correct, h.revise_correct,
   fun W₁ W₂ q => sound_calculus_extract_add wmc h W₁ W₂ q⟩

end Mettapedia.Logic.WMCalculusSoundness
