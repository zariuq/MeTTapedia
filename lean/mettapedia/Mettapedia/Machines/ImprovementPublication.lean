import Mettapedia.Machines.ImprovementInformation
import Mettapedia.Machines.RevisionedOccurrenceStore

/-!
# Keyed publication with revision-scoped references

An atomic slot update stores a value and a generation. Its payload projection
refines keyed improvement, but reference resolution additionally observes the
generation. Successful updates invalidate old live references; independent
keys and captured immutable views retain their meaning.

This is a logical publication and lifetime model. Generations are unbounded
naturals. Native allocation, reclamation, counter wraparound and concurrent
linearization are not supplied by the payload refinement theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.KeyedImprovement.Publication

structure Slot where
  value : Option Nat
  generation : Nat
  deriving DecidableEq

def Slot.view {Key : Type} (slot : Slot) (key : Key) : RevisionedStoreView Key Nat Nat :=
  ⟨key, slot.generation, slot.value.toList⟩

abbrev State (Key : Type) := Key → Slot

def project {Key : Type} (state : State Key) : Store Key Nat := fun key => (state key).value

variable {Key : Type} [DecidableEq Key]

/-- A successful publication advances only this key's generation. -/
def publish (state : State Key) (key : Key) (candidate : Nat) : State Key × Bool :=
  let replacement : Slot := ⟨some candidate, (state key).generation + 1⟩
  match (state key).value with
  | none => (Function.update state key replacement, true)
  | some old => if candidate < old then (Function.update state key replacement, true) else (state, false)

theorem project_update (state : State Key) (key : Key) (replacement : Slot) :
    project (Function.update state key replacement) = Function.update (project state) key replacement.value := by
  funext observed
  by_cases same : observed = key
  · subst observed; simp [project]
  · simp [project, same]

theorem publish_refines (state : State Key) (key : Key) (candidate : Nat) :
    (project (publish state key candidate).1, (publish state key candidate).2) =
      improve (project state) key candidate := by
  cases old : (state key).value with
  | none =>
    simp only [publish, improve, project, old, Prod.mk.injEq, and_true]
    exact project_update state key _
  | some previous =>
    by_cases better : candidate < previous <;>
      simp only [publish, old, improve, project, better, ↓reduceIte]
    all_goals exact Prod.ext (project_update state key _) rfl

/-- The old generation need not be cached: it is read at publication. -/
def executeDecision (state : State Key) (key : Key) (candidate : Nat) (bit : Bool) : State Key × Bool :=
  if bit then (Function.update state key ⟨some candidate, (state key).generation + 1⟩, true)
  else (state, false)

theorem planned_publication_exact (state : State Key) (key : Key) (candidate : Nat) :
    executeDecision state key candidate (Transactions.branch (state key).value candidate) =
      publish state key candidate := by
  cases old : (state key).value with
  | none => simp [executeDecision, publish, Transactions.branch, old]
  | some previous => by_cases better : candidate < previous <;>
      simp [executeDecision, publish, Transactions.branch, old, better]

/-- The same comparison region preserves the full generation-bearing state,
not only its payload projection, when generation is obtained from live state. -/
theorem publication_plan_exact_iff (state : State Key) (key : Key) (candidate : Nat) (bit : Bool) :
    executeDecision state key candidate bit = publish state key candidate ↔
      bit = Transactions.branch (state key).value candidate := by
  rw [← planned_publication_exact]
  constructor
  · intro same
    have flags := congrArg Prod.snd same
    cases bit <;> cases h : Transactions.branch (state key).value candidate <;>
      simp_all [executeDecision]
  · rintro rfl
    rfl

theorem changed_slot (state : State Key) (key : Key) (candidate : Nat)
    (changed : (publish state key candidate).2 = true) :
    (publish state key candidate).1 key = ⟨some candidate, (state key).generation + 1⟩ := by
  cases old : (state key).value with
  | none => simp [publish, old]
  | some previous =>
    by_cases better : candidate < previous
    · simp [publish, old, better]
    · simp [publish, old, better] at changed

theorem unchanged_state (state : State Key) (key : Key) (candidate : Nat)
    (unchanged : (publish state key candidate).2 = false) : (publish state key candidate).1 = state := by
  cases old : (state key).value with
  | none => simp [publish, old] at unchanged
  | some previous =>
    by_cases better : candidate < previous
    · simp [publish, old, better] at unchanged
    · simp [publish, old, better]

theorem other_slot (state : State Key) (key other : Key) (candidate : Nat) (apart : other ≠ key) :
    (publish state key candidate).1 other = state other := by
  cases old : (state key).value with
  | none => simp [publish, old, apart]
  | some previous => by_cases better : candidate < previous <;> simp [publish, old, better, apart]

theorem old_live_reference_rejected (state : State Key) (key : Key) (candidate : Nat)
    (changed : (publish state key candidate).2 = true) :
    (((publish state key candidate).1 key).view key).resolve ((state key).view key |>.occurrenceId 0) = none := by
  rw [changed_slot state key candidate changed]
  simp [Slot.view, RevisionedStoreView.resolve, RevisionedStoreView.occurrenceId, RevisionedStoreView.readToken]

theorem new_live_reference_resolves (state : State Key) (key : Key) (candidate : Nat)
    (changed : (publish state key candidate).2 = true) :
    let live := ((publish state key candidate).1 key).view key
    live.resolve (live.occurrenceId 0) = some candidate := by
  dsimp only
  rw [RevisionedStoreView.resolve_current, changed_slot state key candidate changed]
  rfl

theorem other_reference_unchanged (state : State Key) (key other : Key) (candidate : Nat)
    (apart : other ≠ key) (reference : StoreOccurrenceId Key Nat) :
    (((publish state key candidate).1 other).view other).resolve reference =
      ((state other).view other).resolve reference := by
  rw [other_slot state key other candidate apart]

omit [DecidableEq Key] in
theorem captured_value (slot : Slot) (key : Key) [DecidableEq Key] :
    (slot.view key).resolve ((slot.view key).occurrenceId 0) = slot.value := by
  rw [RevisionedStoreView.resolve_current]
  cases value : slot.value <;> simp [Slot.view, value]

/-- A captured view remains usable even though its old name is no longer live.
Implementations must retain its backing storage until these readers release it. -/
theorem live_and_captured_distinct (state : State Key) (key : Key) (candidate : Nat)
    (changed : (publish state key candidate).2 = true) :
    (((publish state key candidate).1 key).view key).resolve ((state key).view key |>.occurrenceId 0) = none ∧
    ((state key).view key).resolve ((state key).view key |>.occurrenceId 0) = (state key).value :=
  ⟨old_live_reference_rejected state key candidate changed, captured_value (state key) key⟩

/-! ## Information required by a reference observer -/

def revisionAnswers (value generation : Nat) : StoreOccurrenceId Unit Nat → Option Nat :=
  (Slot.view ⟨some value, generation⟩ ()).resolve

theorem revisionAnswers_injective (value : Nat) : Function.Injective (revisionAnswers value) := by
  intro a b same
  have answer := congrFun same (⟨⟨(), a⟩, 0⟩ : StoreOccurrenceId Unit Nat)
  simp only [revisionAnswers, Slot.view, RevisionedStoreView.resolve, Option.toList_some,
    List.getElem?_cons_zero, and_self, ↓reduceIte, true_and] at answer
  by_contra different
  simp [different] at answer

/-- With `n` simultaneously distinguishable generations, sufficient reference
metadata has at least `n` codes, even though every payload is identical. -/
theorem reference_requires_codes {Code : Type} [Fintype Code] (value n : Nat)
    (encode : Fin n → Code) (decode : Code → StoreOccurrenceId Unit Nat → Option Nat)
    (correct : ∀ generation, decode (encode generation) = revisionAnswers value generation.val) :
    n ≤ Fintype.card Code := by
  have injective : Function.Injective encode := by
    intro a b same
    apply Fin.ext
    apply revisionAnswers_injective value
    exact (correct a).symm.trans ((congrArg decode same).trans (correct b))
  simpa using Fintype.card_le_of_injective encode injective

/-- Payload equality alone cannot recover the reference interface. -/
theorem payload_cannot_recover_references (value : Nat) :
    ¬ Mettapedia.GSLT.Core.NonFactorization.Factors
      (fun _generation : Nat => value) (revisionAnswers value) := by
  intro factors
  have same := factors.constantOnFibers 0 1 rfl
  have impossible := revisionAnswers_injective value same
  omega

namespace Controls

def initial : State Bool := fun _ => ⟨some 10, 0⟩

theorem successful_local_publication :
    (publish initial false 7).1 false = ⟨some 7, 1⟩ ∧
    (publish initial false 7).1 true = ⟨some 10, 0⟩ := by decide

theorem equal_payload_different_reference :
    revisionAnswers 7 0 ⟨⟨(), 0⟩, 0⟩ = some 7 ∧
    revisionAnswers 7 1 ⟨⟨(), 0⟩, 0⟩ = none := by decide

/-- Reusing a generation would make an obsolete name live again. -/
theorem generation_reuse_resurrects :
    revisionAnswers 9 0 ⟨⟨(), 0⟩, 0⟩ = some 9 := by decide

end Controls
end Mettapedia.Machines.KeyedImprovement.Publication
