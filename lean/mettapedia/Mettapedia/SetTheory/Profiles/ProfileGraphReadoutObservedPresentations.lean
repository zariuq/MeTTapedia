import Mettapedia.SetTheory.Profiles.ProfileGraphReadoutPresentations

/-!
# Declared outcomes and origins in finite material observations

An unlabelled member graph does not encode a result or fault. The
observed reading keeps its declared outcome, scope and origin ledger in
addition to material behaviour. Its exact Boolean kernel makes those
commitments inspectable. Origin-index fibres are a dependent consumer
that cannot use unlabelled material equality alone.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileGraphReadout.Presentations.Observed

open Mettapedia.TypeTheory.MaterialSets.Hypersets

inductive Outcome
  | returned (value : Nat)
  | faulted (code : Nat)
  deriving DecidableEq

structure Source where
  graph : Checked
  outcome : Outcome
  scope : Nat
  origins : List Nat

abbrev Reading := Outcome × Nat × List Nat × HSet

def reading (source : Source) : Reading :=
  (source.outcome, source.scope, source.origins, material source.graph)

def equal (first second : Source) : Bool :=
  decide (first.outcome = second.outcome) &&
    decide (first.scope = second.scope) &&
    decide (first.origins = second.origins) && equality first.graph second.graph

theorem equal_eq_true (first second : Source) :
    equal first second = true ↔ reading first = reading second := by
  simp [equal, reading, Prod.mk.injEq, equality_eq_true, and_assoc]

/-- Consumers can request an index in the retained origin ledger. -/
def originIndices (source : Source) := Fin source.origins.length

def readingOriginIndices (view : Reading) := Fin view.2.2.1.length

def readingOrigin (view : Reading) (index : readingOriginIndices view) : Nat :=
  view.2.2.1[index.val]

theorem origin_fibre_computes (source : Source) :
    readingOriginIndices (reading source) = originIndices source := rfl

structure OriginReceipt (source : Source) where
  index : originIndices source
  origin : Nat
  agrees : source.origins[index.val] = origin

theorem originReceipt_ext (source : Source) (first second : OriginReceipt source)
    (same : first.index = second.index) : first = second := by
  rcases first with ⟨firstIndex, firstOrigin, firstAgrees⟩
  rcases second with ⟨secondIndex, secondOrigin, secondAgrees⟩
  cases same
  have origins : firstOrigin = secondOrigin := firstAgrees.symm.trans secondAgrees
  cases origins
  rfl

def originReceipt (source : Source) (index : originIndices source) : OriginReceipt source :=
  ⟨index, source.origins[index.val], rfl⟩

theorem observed_origin_consumer_computes (source : Source) (index : originIndices source) :
    readingOrigin (reading source) index = (originReceipt source index).origin := rfl

def originReceiptEquiv (source : Source) : originIndices source ≃ OriginReceipt source where
  toFun := originReceipt source
  invFun := OriginReceipt.index
  left_inv _ := rfl
  right_inv receipt := originReceipt_ext source _ receipt rfl

def originAt (source : Source) (index : Nat) : Option (OriginReceipt source) :=
  if available : index < source.origins.length then
    some (originReceipt source ⟨index, available⟩)
  else none

theorem originAt_none (source : Source) (index : Nat) :
    originAt source index = none ↔ source.origins.length ≤ index := by
  simp [originAt]

theorem originAt_receipt (source : Source) (index : originIndices source) :
    originAt source index.val = some (originReceipt source index) := by
  simp [originAt, index.isLt]
  exact originReceipt_ext source _ _ (Fin.ext rfl)

theorem originAt_index (source : Source) (index : Nat) (receipt : OriginReceipt source)
    (computes : originAt source index = some receipt) : receipt.index.val = index := by
  unfold originAt at computes
  split at computes
  · exact (congrArg (fun receipt : OriginReceipt source => receipt.index.val)
      (Option.some.inj computes)).symm
  · cases computes

theorem originAt_lookup_roundtrip (source : Source) (receipt : OriginReceipt source) :
    originAt source receipt.index.val = some receipt :=
  (originAt_receipt source receipt.index).trans
    (congrArg some (originReceipt_ext source _ receipt rfl))

theorem originAt_available (source : Source) (index : Nat) :
    (∃ receipt, originAt source index = some receipt) ↔ index < source.origins.length := by
  constructor
  · rintro ⟨receipt, computes⟩
    exact (originAt_index source index receipt computes) ▸ receipt.index.isLt
  · intro available
    exact ⟨originReceipt source ⟨index, available⟩, originAt_receipt source ⟨index, available⟩⟩

namespace Controls

open Presentations.Controls

def returnZero : Source := ⟨empty, .returned 0, 0, [7]⟩
def returnOne : Source := ⟨empty, .returned 1, 0, [7]⟩
def fault : Source := ⟨empty, .faulted 0, 0, [7]⟩
def twoOrigins : Source := ⟨empty, .returned 0, 0, [7, 8]⟩
def repeatedOrigin : Source := ⟨empty, .returned 0, 0, [7, 7]⟩

theorem result_zero_one_unlabelled_agree :
    material returnZero.graph = material returnOne.graph := rfl

theorem result_fault_unlabelled_agree : material returnZero.graph = material fault.graph := rfl

theorem declared_results_distinct : equal returnZero returnOne = false := by decide +kernel

theorem declared_fault_distinct : equal returnZero fault = false := by decide +kernel

theorem retained_origins_distinct : equal returnZero twoOrigins = false := by decide +kernel

theorem origin_indices_not_equivalent :
    ¬ Nonempty (originIndices returnZero ≃ originIndices twoOrigins) := by
  rintro ⟨comparison⟩
  change Fin 1 ≃ Fin 2 at comparison
  have same : comparison.symm 0 = comparison.symm 1 := Subsingleton.elim _ _
  exact Nat.zero_ne_one (congrArg Fin.val (comparison.symm.injective same))

theorem origin_family_does_not_descend :
    ¬ ∃ family : HSet → Type,
      ∀ source : Source, Nonempty (originIndices source ≃ family (material source.graph)) := by
  rintro ⟨family, compares⟩
  obtain ⟨first⟩ := compares returnZero
  obtain ⟨second⟩ := compares twoOrigins
  exact origin_indices_not_equivalent ⟨first.trans second.symm⟩

theorem declared_result_does_not_descend :
    ¬ ∃ consumer : HSet → Outcome,
      ∀ source : Source, consumer (material source.graph) = source.outcome := by
  rintro ⟨consumer, computes⟩
  have first := computes returnZero
  have second := computes returnOne
  have same : Outcome.returned 0 = Outcome.returned 1 := first.symm.trans second
  cases same

def firstOrigin : OriginReceipt repeatedOrigin := originReceipt repeatedOrigin ⟨0, by decide⟩
def secondOrigin : OriginReceipt repeatedOrigin := originReceipt repeatedOrigin ⟨1, by decide⟩

theorem repeated_origin_values_agree : firstOrigin.origin = secondOrigin.origin := rfl

theorem repeated_origin_occurrences_distinct : firstOrigin ≠ secondOrigin := by
  intro same
  exact Nat.zero_ne_one (congrArg (fun receipt : OriginReceipt repeatedOrigin => receipt.index.val) same)

theorem first_origin_lookup : originAt repeatedOrigin 0 = some firstOrigin :=
  originAt_receipt repeatedOrigin ⟨0, by decide⟩

theorem second_origin_lookup : originAt repeatedOrigin 1 = some secondOrigin :=
  originAt_receipt repeatedOrigin ⟨1, by decide⟩

theorem one_origin_rejects_second : originAt returnZero 1 = none :=
  (originAt_none returnZero 1).mpr (by decide)

theorem two_origins_admit_second : ∃ receipt, originAt twoOrigins 1 = some receipt :=
  (originAt_available twoOrigins 1).mpr (by decide)

theorem receipt_family_does_not_descend :
    ¬ ∃ family : HSet → Type,
      ∀ source : Source, Nonempty (OriginReceipt source ≃ family (material source.graph)) := by
  rintro ⟨family, compares⟩
  apply origin_family_does_not_descend
  refine ⟨family, fun source => ?_⟩
  obtain ⟨comparison⟩ := compares source
  exact ⟨(originReceiptEquiv source).trans comparison⟩

end Controls

end Mettapedia.SetTheory.Profiles.ProfileGraphReadout.Presentations.Observed
