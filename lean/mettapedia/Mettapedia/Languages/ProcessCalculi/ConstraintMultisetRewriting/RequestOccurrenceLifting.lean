import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RequestActivation

/-!
# Lifting source request steps to physical constraint firings

Distinct consumption occurrences are recovered from the actual source bag.
Premise reads are recovered from its remaining occurrences and may reuse one
occurrence. The output receives a fresh occurrence from the supplied label
fiber. Data-only source checks keep their exact computation.

No source matcher is assumed complete, and no search interpreter is added.
The result constructs an ordinary constraint step with the original source
assignment and exactly the source destination bag.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RequestOccurrenceLifting

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open RequestActivation

variable {V Head P : Type} {O : Type*} [DecidableEq O]

theorem receipt_of_step (layer : TermLayer V (Term Head) P) (recipe : Recipe V Head P)
    (label : O → Term Head) (world : Finset O)
    (supply : ∀ value : Term Head, ∃ occurrence, occurrence ∉ world ∧ label occurrence = value)
    {after : Multiset (Term Head)}
    (stepped : GuardedMultisetRewriting.Step layer recipe.matchingRule (labels label world) after) :
    ∃ receipt : GuardedMultisetRewriting.FiringReceipt O V (Term Head),
      receipt.ValidAt layer recipe.matchingRule label world ∧
      labels label (fire world (receipt.commit layer recipe.matchingRule)) = after := by
  classical
  obtain ⟨assignment, frame, _, kept, made, bindings,
    ⟨takeValues, takeMatch, rfl⟩, ⟨readValues, readMatch, _, readSupport⟩,
    source, checks, outputInstances, destination⟩ := stepped
  have takeSubbag : (takeValues : Multiset (Term Head)) ≤ labels label world := by
    rw [source]
    exact (Multiset.le_add_left _ _).trans (Multiset.le_add_right _ _)
  obtain ⟨takeIds, distinctTakes, takePresent, rfl⟩ :=
    GuardedMultisetRewriting.exists_occurrences label takeValues world takeSubbag
  have takeSubset : takeIds.toFinset ⊆ world := fun occurrence member =>
    takePresent occurrence (by simpa using member)
  have remainder : labels label (world \ takeIds.toFinset) = frame + kept := by
    have split : labels label world = labels label (world \ takeIds.toFinset) + labels label takeIds.toFinset := by
      rw [← labels_union_of_disjoint label Finset.sdiff_disjoint,
        Finset.sdiff_union_of_subset takeSubset]
    rw [GuardedMultisetRewriting.labels_toFinset label distinctTakes, source, add_right_comm] at split
    exact (add_right_cancel split).symm
  obtain ⟨readIds, readsRemaining, rfl⟩ := GuardedMultisetRewriting.exists_list_of_mem label
    (world \ takeIds.toFinset) readValues (fun value member => by
      have present : value ∈ labels label (world \ takeIds.toFinset) := by
        rw [remainder]
        exact Multiset.mem_add.mpr (Or.inr (readSupport value member))
      obtain ⟨occurrence, inWorld, rfl⟩ := Multiset.mem_map.mp present
      exact ⟨occurrence, Finset.mem_val.mp inWorld, rfl⟩)
  have output : ∃ value, layer.inst assignment recipe.conclusion = some value ∧ made = [value] := by
    change instTemplate layer assignment [recipe.conclusion] = some made at outputInstances
    cases result : layer.inst assignment recipe.conclusion with
    | none => simp [instTemplate, result] at outputInstances
    | some value =>
        refine ⟨value, rfl, ?_⟩
        simpa [instTemplate, result] using outputInstances.symm
  obtain ⟨value, instantiated, rfl⟩ := output
  obtain ⟨outputId, freshOutput, outputLabel⟩ := supply value
  let receipt : GuardedMultisetRewriting.FiringReceipt O V (Term Head) :=
    ⟨assignment, takeIds, readIds, [outputId],
      [regionOf label world (semRegion layer assignment recipe.request)]⟩
  have valid : receipt.ValidAt layer recipe.matchingRule label world := by
    refine ⟨distinctTakes, by simp [receipt], takeSubset, ?_, ?_, ?_, bindings,
      takeMatch, readMatch, ?_, ?_⟩
    · intro occurrence member
      exact (Finset.mem_sdiff.mp (readsRemaining occurrence (by simpa [receipt] using member))).1
    · apply Finset.disjoint_left.mpr
      intro occurrence taken read
      exact (Finset.mem_sdiff.mp (readsRemaining occurrence (by simpa [receipt] using read))).2 taken
    · simpa [receipt, Finset.disjoint_left] using freshOutput
    · change instTemplate layer assignment [recipe.conclusion] = some [label outputId]
      simp [instTemplate, instantiated, outputLabel]
    · refine .cons ⟨rfl, ?_⟩ .nil
      exact checks ⟨recipe.request, fun supplied _ => recipe.dataCondition supplied = true⟩
        (by simp [Recipe.matchingRule, GuardedMultisetRewriting.requestRule])
  refine ⟨receipt, valid, ?_⟩
  rw [labels_fire valid.enabled]
  change labels label world - labels label takeIds.toFinset + labels label ({outputId} : Finset O) = after
  rw [GuardedMultisetRewriting.labels_toFinset label distinctTakes, source, add_right_comm,
    add_tsub_cancel_right, destination]
  simp [labels, outputLabel]

theorem constraint_step_of_source_step (layer : TermLayer V (Term Head) P) (structural : layer.E = Eq)
    (falseHead trueHead : Head) (distinct : falseHead ≠ trueHead) (width : Nat)
    (recipe : Recipe V Head P) (label : O → Term Head) (before : Configuration (Term Head) O)
    (supply : ∀ value : Term Head, ∃ occurrence, occurrence ∉ before.present ∧ label occurrence = value)
    (background : (ABTProtectedParameters.action width).Consistent before.equations)
    {after : Multiset (Term Head)}
    (stepped : GuardedMultisetRewriting.Step layer recipe.matchingRule (labels label before.present) after) :
    ∃ receipt rule, activate layer falseHead trueHead recipe receipt.assignment = some rule ∧
      Step (ABTProtectedParameters.action width) label rule before
        ((physicalSelection receipt).result label rule before) ∧
      labels label ((physicalSelection receipt).result label rule before).present = after := by
  obtain ⟨receipt, valid, destination⟩ := receipt_of_step layer recipe label before.present supply stepped
  obtain ⟨rule, computed, fired⟩ := step_of_matching_receipt layer structural falseHead trueHead distinct width
    recipe label before receipt valid background
  exact ⟨receipt, rule, computed, fired, by
    simpa only [Selection.result, physicalSelection, Selection.commit,
      GuardedMultisetRewriting.FiringReceipt.commit, fire] using destination⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RequestOccurrenceLifting
