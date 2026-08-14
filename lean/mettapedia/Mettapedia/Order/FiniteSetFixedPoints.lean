import Mathlib.Data.Set.Card
import Mathlib.Order.FixedPoints
import Mathlib.Order.Iterate

/-!
# Fixed points of monotone maps on finite powersets

A monotone self-map of `Set S` reaches its least fixed point by iterating from
`∅`, and its greatest fixed point by iterating from `Set.univ`.  When `S` is
finite, at most `Nat.card S` iterations are needed.  The proof combines
Mathlib's monotone-iterate, finite-cardinality, and bounded-stabilization
lemmas.
-/

namespace Mettapedia.Order.FiniteSetFixedPoints

/-- An increasing chain of subsets of a finite carrier that stays constant
after its first repeated step has stabilized by `Nat.card S`. -/
theorem monotone_chain_stabilizes_at_card {S : Type*} [Finite S]
    (chain : Nat → Set S) (monotone : Monotone chain)
    (stable : ∀ index,
      chain index = chain (index + 1) →
        chain (index + 1) = chain (index + 2)) :
    chain (Nat.card S) = chain (Nat.card S + 1) := by
  have cardinalityMonotone : Monotone fun index => (chain index).ncard := by
    intro left right ordered
    exact Set.ncard_le_ncard (monotone ordered) (Set.toFinite _)
  have cardinalityBound : ∀ index, (chain index).ncard ≤ Nat.card S := by
    intro index
    rw [← Set.ncard_univ]
    exact Set.ncard_le_ncard (by intro _ _; trivial) (Set.toFinite _)
  have cardinalityStable : ∀ index,
      (chain index).ncard = (chain (index + 1)).ncard →
        (chain (index + 1)).ncard = (chain (index + 2)).ncard := by
    intro index equalCardinality
    have equalSets : chain index = chain (index + 1) :=
      Set.eq_of_subset_of_ncard_le (monotone (by omega))
        (by omega) (Set.toFinite _)
    exact congrArg Set.ncard (stable index equalSets)
  have equalCardinality := Nat.stabilises_of_monotone
    cardinalityMonotone cardinalityBound cardinalityStable
    (show Nat.card S ≤ Nat.card S + 1 by omega)
  exact Set.eq_of_subset_of_ncard_le (monotone (by omega))
    (by omega) (Set.toFinite _)

/-- A decreasing chain obeying the same stability condition has also
stabilized by `Nat.card S`. -/
theorem antitone_chain_stabilizes_at_card {S : Type*} [Finite S]
    (chain : Nat → Set S) (antitone : Antitone chain)
    (stable : ∀ index,
      chain index = chain (index + 1) →
        chain (index + 1) = chain (index + 2)) :
    chain (Nat.card S) = chain (Nat.card S + 1) := by
  let complementChain : Nat → Set S := fun index => (chain index)ᶜ
  have complementMonotone : Monotone complementChain := by
    intro left right ordered
    exact Set.compl_subset_compl.mpr (antitone ordered)
  have complementStable : ∀ index,
      complementChain index = complementChain (index + 1) →
        complementChain (index + 1) = complementChain (index + 2) := by
    intro index equalComplements
    exact congrArg (fun states : Set S => statesᶜ)
      (stable index (compl_inj_iff.mp equalComplements))
  exact compl_inj_iff.mp (monotone_chain_stabilizes_at_card
    complementChain complementMonotone complementStable)

/-- The least fixed point of a monotone map on a finite powerset is its
`Nat.card S`-th iterate from `∅`. -/
theorem lfp_eq_iterate_empty {S : Type*} [Finite S]
    (transformer : Set S →o Set S) :
    transformer.lfp =
      (transformer : Set S → Set S)^[Nat.card S] (∅ : Set S) := by
  let approximation : Nat → Set S := fun index =>
    (transformer : Set S → Set S)^[index] (∅ : Set S)
  have approximationMonotone : Monotone approximation :=
    transformer.monotone.monotone_iterate_of_le_map bot_le
  have approximationStable : ∀ index,
      approximation index = approximation (index + 1) →
        approximation (index + 1) = approximation (index + 2) := by
    intro index equal
    simpa [approximation, Function.iterate_succ_apply'] using
      congrArg transformer equal
  have stabilized := monotone_chain_stabilizes_at_card
    approximation approximationMonotone approximationStable
  have fixed : transformer (approximation (Nat.card S)) =
      approximation (Nat.card S) := by
    simpa [approximation, Function.iterate_succ_apply'] using stabilized.symm
  have approximationLe : ∀ index, approximation index ≤ transformer.lfp := by
    intro index
    induction index with
    | zero => exact bot_le
    | succ index inductionHypothesis =>
        simpa only [approximation, Function.iterate_succ_apply'] using
          (transformer.monotone inductionHypothesis).trans_eq
            transformer.map_lfp
  exact le_antisymm (transformer.lfp_le_fixed fixed)
    (by simpa [approximation] using approximationLe (Nat.card S))

/-- The greatest fixed point of a monotone map on a finite powerset is its
`Nat.card S`-th iterate from `Set.univ`. -/
theorem gfp_eq_iterate_univ {S : Type*} [Finite S]
    (transformer : Set S →o Set S) :
    transformer.gfp =
      (transformer : Set S → Set S)^[Nat.card S] (Set.univ : Set S) := by
  let approximation : Nat → Set S := fun index =>
    (transformer : Set S → Set S)^[index] (Set.univ : Set S)
  have approximationAntitone : Antitone approximation :=
    transformer.monotone.antitone_iterate_of_map_le le_top
  have approximationStable : ∀ index,
      approximation index = approximation (index + 1) →
        approximation (index + 1) = approximation (index + 2) := by
    intro index equal
    simpa [approximation, Function.iterate_succ_apply'] using
      congrArg transformer equal
  have stabilized := antitone_chain_stabilizes_at_card
    approximation approximationAntitone approximationStable
  have fixed : transformer (approximation (Nat.card S)) =
      approximation (Nat.card S) := by
    simpa [approximation, Function.iterate_succ_apply'] using stabilized.symm
  have approximationGe : ∀ index, transformer.gfp ≤ approximation index := by
    intro index
    induction index with
    | zero => exact le_top
    | succ index inductionHypothesis =>
        simpa only [approximation, Function.iterate_succ_apply'] using
          transformer.map_gfp.symm.le.trans
            (transformer.monotone inductionHypothesis)
  exact le_antisymm
    (by simpa [approximation] using approximationGe (Nat.card S))
    (transformer.le_gfp fixed.ge)

/-! ## Canonical finite semantic ranks -/

/-- The increasing approximation sequence for a least fixed point. -/
def lowerApproximation {S : Type*} (transformer : Set S →o Set S)
    (index : Nat) : Set S :=
  (transformer : Set S → Set S)^[index] (∅ : Set S)

/-- The decreasing approximation sequence for a greatest fixed point. -/
def upperApproximation {S : Type*} (transformer : Set S →o Set S)
    (index : Nat) : Set S :=
  (transformer : Set S → Set S)^[index] (Set.univ : Set S)

@[simp] theorem lowerApproximation_zero {S : Type*}
    (transformer : Set S →o Set S) :
    lowerApproximation transformer 0 = ∅ := rfl

@[simp] theorem lowerApproximation_succ {S : Type*}
    (transformer : Set S →o Set S) (index : Nat) :
    lowerApproximation transformer (index + 1) =
      transformer (lowerApproximation transformer index) := by
  simp [lowerApproximation, Function.iterate_succ_apply']

@[simp] theorem upperApproximation_zero {S : Type*}
    (transformer : Set S →o Set S) :
    upperApproximation transformer 0 = Set.univ := rfl

@[simp] theorem upperApproximation_succ {S : Type*}
    (transformer : Set S →o Set S) (index : Nat) :
    upperApproximation transformer (index + 1) =
      transformer (upperApproximation transformer index) := by
  simp [upperApproximation, Function.iterate_succ_apply']

theorem lowerApproximation_mono {S : Type*}
    (transformer : Set S →o Set S) :
    Monotone (lowerApproximation transformer) :=
  transformer.monotone.monotone_iterate_of_le_map bot_le

theorem upperApproximation_antitone {S : Type*}
    (transformer : Set S →o Set S) :
    Antitone (upperApproximation transformer) :=
  transformer.monotone.antitone_iterate_of_map_le le_top

/-- Every lower approximation lies below the least fixed point. -/
theorem lowerApproximation_le_lfp {S : Type*}
    (transformer : Set S →o Set S) (index : Nat) :
    lowerApproximation transformer index ≤ transformer.lfp := by
  induction index with
  | zero => exact bot_le
  | succ index inductionHypothesis =>
      rw [show index + 1 = Nat.succ index by omega, lowerApproximation_succ]
      exact (transformer.monotone inductionHypothesis).trans_eq transformer.map_lfp

/-- The greatest fixed point lies below every upper approximation. -/
theorem gfp_le_upperApproximation {S : Type*}
    (transformer : Set S →o Set S) (index : Nat) :
    transformer.gfp ≤ upperApproximation transformer index := by
  induction index with
  | zero => exact le_top
  | succ index inductionHypothesis =>
      rw [show index + 1 = Nat.succ index by omega, upperApproximation_succ]
      exact transformer.map_gfp.symm.le.trans
        (transformer.monotone inductionHypothesis)

/-- Every member of a finite least fixed point enters its approximation
sequence by the carrier-cardinality bound. -/
theorem exists_lowerApproximation_of_mem_lfp {S : Type*} [Finite S]
    (transformer : Set S →o Set S) (state : S)
    (member : state ∈ transformer.lfp) :
    ∃ index, state ∈ lowerApproximation transformer index := by
  refine ⟨Nat.card S, ?_⟩
  simpa [lowerApproximation, ← lfp_eq_iterate_empty transformer] using member

/-- Canonical rank of a state in a finite least fixed point: its first
approximation stage. -/
noncomputable def lfpEntryRank {S : Type*} [Finite S]
    (transformer : Set S →o Set S) (state : S)
    (member : state ∈ transformer.lfp) : Nat :=
  by
    classical
    exact Nat.find
      (exists_lowerApproximation_of_mem_lfp transformer state member)

theorem lfpEntryRank_mem {S : Type*} [Finite S]
    (transformer : Set S →o Set S) (state : S)
    (member : state ∈ transformer.lfp) :
    state ∈ lowerApproximation transformer
      (lfpEntryRank transformer state member) :=
  by
    classical
    exact Nat.find_spec
      (exists_lowerApproximation_of_mem_lfp transformer state member)

theorem lfpEntryRank_min {S : Type*} [Finite S]
    (transformer : Set S →o Set S) (state : S)
    (member : state ∈ transformer.lfp) {index : Nat}
    (atIndex : state ∈ lowerApproximation transformer index) :
    lfpEntryRank transformer state member ≤ index :=
  by
    classical
    exact Nat.find_min'
      (exists_lowerApproximation_of_mem_lfp transformer state member) atIndex

theorem lfpEntryRank_le_card {S : Type*} [Finite S]
    (transformer : Set S →o Set S) (state : S)
    (member : state ∈ transformer.lfp) :
    lfpEntryRank transformer state member ≤ Nat.card S := by
  apply lfpEntryRank_min
  simpa [lowerApproximation, ← lfp_eq_iterate_empty transformer] using member

theorem lfpEntryRank_pos {S : Type*} [Finite S]
    (transformer : Set S →o Set S) (state : S)
    (member : state ∈ transformer.lfp) :
    0 < lfpEntryRank transformer state member := by
  apply Nat.pos_of_ne_zero
  intro zero
  have enters := lfpEntryRank_mem transformer state member
  simp [zero] at enters

/-- Every state outside a finite greatest fixed point leaves its decreasing
approximation sequence by the carrier-cardinality bound. -/
theorem exists_not_mem_upperApproximation_of_not_mem_gfp
    {S : Type*} [Finite S] (transformer : Set S →o Set S) (state : S)
    (missing : state ∉ transformer.gfp) :
    ∃ index, state ∉ upperApproximation transformer index := by
  refine ⟨Nat.card S, ?_⟩
  simpa [upperApproximation, ← gfp_eq_iterate_univ transformer] using missing

/-- Canonical rank of a state outside a finite greatest fixed point: its first
elimination stage. -/
noncomputable def gfpExitRank {S : Type*} [Finite S]
    (transformer : Set S →o Set S) (state : S)
    (missing : state ∉ transformer.gfp) : Nat :=
  by
    classical
    exact Nat.find
      (exists_not_mem_upperApproximation_of_not_mem_gfp transformer state missing)

theorem gfpExitRank_not_mem {S : Type*} [Finite S]
    (transformer : Set S →o Set S) (state : S)
    (missing : state ∉ transformer.gfp) :
    state ∉ upperApproximation transformer
      (gfpExitRank transformer state missing) :=
  by
    classical
    exact Nat.find_spec
      (exists_not_mem_upperApproximation_of_not_mem_gfp transformer state missing)

theorem gfpExitRank_min {S : Type*} [Finite S]
    (transformer : Set S →o Set S) (state : S)
    (missing : state ∉ transformer.gfp) {index : Nat}
    (notAtIndex : state ∉ upperApproximation transformer index) :
    gfpExitRank transformer state missing ≤ index :=
  by
    classical
    exact Nat.find_min'
      (exists_not_mem_upperApproximation_of_not_mem_gfp transformer state missing)
      notAtIndex

theorem gfpExitRank_le_card {S : Type*} [Finite S]
    (transformer : Set S →o Set S) (state : S)
    (missing : state ∉ transformer.gfp) :
    gfpExitRank transformer state missing ≤ Nat.card S := by
  apply gfpExitRank_min
  simpa [upperApproximation, ← gfp_eq_iterate_univ transformer] using missing

theorem gfpExitRank_pos {S : Type*} [Finite S]
    (transformer : Set S →o Set S) (state : S)
    (missing : state ∉ transformer.gfp) :
    0 < gfpExitRank transformer state missing := by
  apply Nat.pos_of_ne_zero
  intro zero
  have exits := gfpExitRank_not_mem transformer state missing
  simp [zero] at exits

/-- Iteration commutes with De Morgan duality.  The empty/universal fixed-point
approximations are the two boundary instances of this generic semiconjugacy
fact. -/
theorem iterate_dual {S : Type*}
    (original dual : Set S → Set S)
    (dualEq : ∀ states, dual states = (original statesᶜ)ᶜ)
    (index : Nat) (states : Set S) :
    dual^[index] statesᶜ = (original^[index] states)ᶜ := by
  have semiconjugate : Function.Semiconj (fun states : Set S => statesᶜ)
      original dual := by
    intro states
    rw [dualEq]
    simp
  exact (semiconjugate.iterate_right index states).symm

/-! ## Executable boundary examples -/

namespace Canary

def forceUnit : Set Unit →o Set Unit where
  toFun _ := Set.univ
  monotone' := by
    intro _ _ _
    exact Set.Subset.rfl

def eraseUnit : Set Unit →o Set Unit where
  toFun _ := ∅
  monotone' := by
    intro _ _ _
    exact Set.Subset.rfl

theorem forceUnit_lfp : forceUnit.lfp = Set.univ := by
  rw [lfp_eq_iterate_empty]
  simp [forceUnit]

theorem eraseUnit_gfp : eraseUnit.gfp = ∅ := by
  rw [gfp_eq_iterate_univ]
  simp [eraseUnit]

theorem forceUnit_entryRank :
    lfpEntryRank forceUnit () (by simp [forceUnit_lfp]) = 1 := by
  apply Nat.le_antisymm
  · simpa only [Nat.card_unique] using
      lfpEntryRank_le_card forceUnit () (by simp [forceUnit_lfp])
  · exact lfpEntryRank_pos forceUnit () (by simp [forceUnit_lfp])

theorem eraseUnit_exitRank :
    gfpExitRank eraseUnit () (by simp [eraseUnit_gfp]) = 1 := by
  apply Nat.le_antisymm
  · simpa only [Nat.card_unique] using
      gfpExitRank_le_card eraseUnit () (by simp [eraseUnit_gfp])
  · exact gfpExitRank_pos eraseUnit () (by simp [eraseUnit_gfp])

end Canary

end Mettapedia.Order.FiniteSetFixedPoints
