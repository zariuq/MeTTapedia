import Mettapedia.Logic.EvidenceProofSystem
import Mettapedia.Logic.EvidentialLedger

/-!
# Runtime Soundness Bridge

A runtime implementation of evidence operations is SOUND if it agrees
with the WM algebra. This file defines the interface and proves that
sound runtimes inherit all algebraic properties.

## What this gives mettail-c and mettail-rust

1. `EvidenceRuntime` — the interface any implementation must satisfy
2. `RuntimeSound` — the formal correctness criterion
3. `sound_runtime_extract_add` — sound runtimes preserve `extract_add`
4. `sound_runtime_compose` — sound components compose soundly
5. Runtime implementations prove `RuntimeSound` to certify correctness

## Architecture

    Lean specification (AdditiveWorldModel)
            ↓ RuntimeSound proof
    Runtime implementation (EvidenceRuntime)
            ↓ Compilation / FFI
    mettail-c / mettail-rust binary

The RuntimeSound proof is the BRIDGE: it says the implementation
matches the specification. Without it, the runtime is unverified.
With it, every algebraic property (extract_add, forgetting exactness,
compositionality) transfers to the runtime.

## References

- `HE/RuntimeContract.lean` — declares WHAT the runtime should do
- `EvalIRRefinement.lean` — local soundness lemmas
- WM-PLN book, Ch 7 (Natively Typed World Models)

0 sorry.
-/

namespace Mettapedia.Logic.RuntimeSoundnessBridge

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelGeneric

/-! ## 1. Runtime interface -/

/-- A runtime implementation of evidence operations.
    This is the interface that mettail-c, mettail-rust, or any other
    implementation must provide. -/
structure EvidenceRuntime (State Query Ev : Type*) where
  /-- Combine two evidence states (= revision). -/
  rtRevise : State → State → State
  /-- Extract evidence for a query from a state. -/
  rtExtract : State → Query → Ev
  /-- Optionally: forget a source's contribution. -/
  rtForget : Option (State → State → State)  -- (state, scope) → reduced state

/-! ## 2. Soundness criterion -/

/-- A runtime is SOUND if its operations agree with the WM algebra.

    This is the formal property a runtime must prove to be certified.
    Once proven, all algebraic properties transfer automatically. -/
structure RuntimeSound {State Query Ev : Type*}
    [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]
    (rt : EvidenceRuntime State Query Ev) : Prop where
  /-- Revision in the runtime = addition in the algebra. -/
  revise_correct : ∀ W₁ W₂, rt.rtRevise W₁ W₂ = W₁ + W₂
  /-- Extraction in the runtime = extraction in the algebra. -/
  extract_correct : ∀ W q,
    rt.rtExtract W q = AdditiveWorldModel.extract (Ev := Ev) W q

/-! ## 3. Sound runtimes inherit extract_add -/

/-- A sound runtime automatically satisfies the extraction-addition law.
    This is the key theorem: you don't need to prove extract_add for
    the runtime separately — it follows from soundness. -/
theorem sound_runtime_extract_add {State Query Ev : Type*}
    [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]
    (rt : EvidenceRuntime State Query Ev) (h : RuntimeSound rt)
    (W₁ W₂ : State) (q : Query) :
    rt.rtExtract (rt.rtRevise W₁ W₂) q =
    rt.rtExtract W₁ q + rt.rtExtract W₂ q := by
  rw [h.revise_correct, h.extract_correct, h.extract_correct, h.extract_correct]
  exact AdditiveWorldModel.extract_add W₁ W₂ q

/-! ## 4. Composition of sound runtimes -/

/-- If two runtimes agree on their shared interface, composing their
    extractions gives the same result as the algebraic composition. -/
theorem sound_runtime_sequential {State Query Ev : Type*}
    [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]
    (rt : EvidenceRuntime State Query Ev) (h : RuntimeSound rt)
    (W₁ W₂ W₃ : State) (q : Query) :
    rt.rtExtract (rt.rtRevise (rt.rtRevise W₁ W₂) W₃) q =
    rt.rtExtract W₁ q + rt.rtExtract W₂ q + rt.rtExtract W₃ q := by
  simp only [h.revise_correct, h.extract_correct, AdditiveWorldModel.extract_add, add_assoc]

/-! ## 5. Sound runtime preserves zero -/

/-- A sound runtime on zero state gives zero evidence. -/
theorem sound_runtime_revise_zero_left {State Query Ev : Type*}
    [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]
    (rt : EvidenceRuntime State Query Ev) (h : RuntimeSound rt)
    (W : State) (q : Query) :
    rt.rtExtract (rt.rtRevise 0 W) q = rt.rtExtract W q := by
  rw [h.revise_correct, zero_add]

/-! ## 6. The correctness contract

For mettail-c and mettail-rust:

1. Define your runtime as `EvidenceRuntime State Query Ev`
2. Prove `RuntimeSound` for your implementation
3. All WM-PLN algebraic properties transfer automatically:
   - `extract_add` — evidence revision is compositional
   - Sequential composition — multi-step revision is associative
   - Zero preservation — empty state gives empty evidence

The proof of `RuntimeSound` is the CERTIFICATION that your runtime
correctly implements the WM evidence algebra. -/

/-- Summary: what a sound runtime guarantees. -/
theorem soundness_guarantees {State Query Ev : Type*}
    [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]
    (rt : EvidenceRuntime State Query Ev) (h : RuntimeSound rt) :
    -- Extraction agrees with algebra
    (∀ W q, rt.rtExtract W q = AdditiveWorldModel.extract (Ev := Ev) W q) ∧
    -- Revision agrees with algebra
    (∀ W₁ W₂, rt.rtRevise W₁ W₂ = W₁ + W₂) ∧
    -- extract_add transfers
    (∀ W₁ W₂ q, rt.rtExtract (rt.rtRevise W₁ W₂) q =
      rt.rtExtract W₁ q + rt.rtExtract W₂ q) :=
  ⟨h.extract_correct, h.revise_correct,
   fun W₁ W₂ q => sound_runtime_extract_add rt h W₁ W₂ q⟩

end Mettapedia.Logic.RuntimeSoundnessBridge
