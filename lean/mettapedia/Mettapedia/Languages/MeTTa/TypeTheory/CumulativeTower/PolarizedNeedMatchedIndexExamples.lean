import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.PolarizedNeedMatchedIndexService

/-!
# Selected occurrence, bounded element and raw-receipt controls

The canonical family is arbitrary in its vector and valid index. A duplicated
bag selection then keeps two distinct occurrence requests even though their
bindings, vectors and outputs coincide. Cross-occurrence reuse is rejected
by the actual executed consumer at every fuel. Out-of-range and forged-output
controls concern admission, not mathematical negation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace PolarizedNeedMatchedIndex.Examples

open Presentation PrimeNeedReference
open Presentation.PolarizedNeedMachine
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef

def emptyWorld : NeedWorld Tower.Head Operation Nat Empty Empty 0 :=
  ⟨0, [], .empty, .empty, 0, 0⟩

theorem emptyWorld_bounded : PrimeNeedAllocationBound.SlotBound emptyWorld := by
  intro cell record lookup
  cases lookup

def vectorRequest (values : List Pattern) (index : Nat) : Request :=
  ⟨.fvar "items", .collection .vec values none, 0, index⟩

def vectorReceipt (values : List Pattern) (index : Fin values.length) : Receipt :=
  ⟨vectorRequest values index.val, [("items", .collection .vec values none)], values, values.get index⟩

theorem vector_selected (values : List Pattern) (index : Fin values.length) :
    select? (vectorRequest values index.val) = some (vectorReceipt values index) := by
  have read : getElem? values index.val = some (values.get index) :=
    List.getElem?_eq_some_iff.mpr ⟨index.isLt, rfl⟩
  simp [select?, vectorRequest, vectorReceipt, matchPattern, Bindings.lookup,
    MatchedIndexJudgment.checkIndex, read]

theorem vector_eventually_admitted (values : List Pattern) (index : Fin values.length) :
    ∃ fuel, replyOutcome (admittedWire (vectorReceipt values index)) ∈
      answers (vectorRequest values index.val) (vectorRequest values index.val) emptyWorld {} fuel :=
  selected_eventually_admitted _ _ (vector_selected values index) emptyWorld emptyWorld_bounded {}

theorem outside_vector_not_selected (values : List Pattern) (index : Nat)
    (outside : values.length ≤ index) : select? (vectorRequest values index) = none := by
  have read : getElem? values index = none := List.getElem?_eq_none_iff.mpr outside
  simp [select?, vectorRequest, matchPattern, Bindings.lookup, MatchedIndexJudgment.checkIndex, read]

theorem outside_vector_never_admitted (values : List Pattern) (index : Nat)
    (outside : values.length ≤ index) (receipt : Receipt) (fuel : Nat) :
    replyOutcome (admittedWire receipt) ∉
      answers (vectorRequest values index) (vectorRequest values index) emptyWorld {} fuel := by
  intro observed
  have selected := (observed_evidence _ _ receipt emptyWorld emptyWorld_bounded {} observed).1
  rw [outside_vector_not_selected values index outside] at selected
  cases selected

def a : Pattern := .apply "a" []
def b : Pattern := .apply "b" []

def canonical : Receipt := vectorReceipt [a, b] ⟨1, by decide⟩

theorem canonical_output : canonical.output = b := rfl

theorem canonical_checked : validate canonical.request canonical = true :=
  select_validates (vector_selected [a, b] ⟨1, by decide⟩)

theorem canonical_run :
    ∃ fuel, replyOutcome (admittedWire canonical) ∈ answers canonical.request canonical.request emptyWorld {} fuel :=
  vector_eventually_admitted [a, b] ⟨1, by decide⟩

/-- Changing only the proposed result cannot reuse valid bounds as authority. -/
def changedOutput : Receipt := { canonical with output := a }

theorem changed_output_rejected : validate canonical.request changedOutput = false := by
  simp [validate, canonical, changedOutput, vectorReceipt, vectorRequest,
    matchPattern, Bindings.lookup, MatchedIndexJudgment.checkIndex, a, b]

theorem forged_receipt_not_admitted :
    consumeWire canonical.request (encodeReceipt changedOutput) = refusedWire := by
  rw [consumeWire_receipt, changed_output_rejected]
  rfl

def duplicateVector : Pattern := .collection .vec [a] none

def duplicateBindings : Bindings :=
  [("items", duplicateVector), ("rest", .collection .hashBag [duplicateVector] none)]

def duplicateRequest (occurrence : Nat) : Request :=
  ⟨.collection .hashBag [.fvar "items"] (some "rest"),
    .collection .hashBag [duplicateVector, duplicateVector] none, occurrence, 0⟩

def duplicateReceipt (occurrence : Nat) : Receipt :=
  ⟨duplicateRequest occurrence, duplicateBindings, [a], a⟩

theorem duplicate_matches :
    matchPattern (duplicateRequest 0).pattern (duplicateRequest 0).subject =
      [duplicateBindings, duplicateBindings] := by
  simp [duplicateRequest, duplicateBindings, duplicateVector,
    matchPattern, matchBag, mergeBindings]

theorem duplicate_first_selected : select? (duplicateRequest 0) = some (duplicateReceipt 0) := by
  simp only [select?, duplicate_matches]
  simp [duplicateReceipt, duplicateBindings, duplicateVector, duplicateRequest,
    MatchedIndexJudgment.checkIndex, Bindings.lookup]

theorem duplicate_second_selected : select? (duplicateRequest 1) = some (duplicateReceipt 1) := by
  have matched : matchPattern (duplicateRequest 1).pattern (duplicateRequest 1).subject =
      [duplicateBindings, duplicateBindings] := duplicate_matches
  simp only [select?, matched]
  simp [duplicateReceipt, duplicateBindings, duplicateVector, duplicateRequest,
    MatchedIndexJudgment.checkIndex, Bindings.lookup]

theorem duplicate_data_agree_but_receipts_distinct :
    (duplicateReceipt 0).bindings = (duplicateReceipt 1).bindings ∧
      (duplicateReceipt 0).values = (duplicateReceipt 1).values ∧
      (duplicateReceipt 0).output = (duplicateReceipt 1).output ∧
      duplicateReceipt 0 ≠ duplicateReceipt 1 := by decide

theorem duplicate_receipt_codes_distinct :
    encodeReceipt (duplicateReceipt 0) ≠ encodeReceipt (duplicateReceipt 1) :=
  fun same => duplicate_data_agree_but_receipts_distinct.2.2.2 (encodeReceipt_injective same)

theorem both_duplicate_occurrences_run :
    (∃ fuel, replyOutcome (admittedWire (duplicateReceipt 0)) ∈
      answers (duplicateRequest 0) (duplicateRequest 0) emptyWorld {} fuel) ∧
    (∃ fuel, replyOutcome (admittedWire (duplicateReceipt 1)) ∈
      answers (duplicateRequest 1) (duplicateRequest 1) emptyWorld {} fuel) :=
  ⟨selected_eventually_admitted _ _ duplicate_first_selected emptyWorld emptyWorld_bounded {},
   selected_eventually_admitted _ _ duplicate_second_selected emptyWorld emptyWorld_bounded {}⟩

/-- Equal payload and output do not authorize changing the selected position. -/
theorem cross_occurrence_never_admitted (receipt : Receipt) (fuel : Nat) :
    replyOutcome (admittedWire receipt) ∉
      answers (duplicateRequest 0) (duplicateRequest 1) emptyWorld {} fuel :=
  wrong_selection_never_admitted _ _ (by decide) receipt emptyWorld emptyWorld_bounded {} fuel

theorem duplicate_third_not_selected : select? (duplicateRequest 2) = none := by
  have matched : matchPattern (duplicateRequest 2).pattern (duplicateRequest 2).subject =
      [duplicateBindings, duplicateBindings] := duplicate_matches
  simp only [select?, matched]
  rfl

theorem malformed_distinct_from_missing_index :
    selectWire (.symbol "not-a-request") ≠
      selectedWire (vectorRequest [a] 1) := by
  simp [selectWire, decodeRequest, selectedWire,
    outside_vector_not_selected [a] 1 (by decide)]

/-- Using the dependent evidence proves membership of the actual admitted
output, not merely membership of a separately selected value. -/
theorem admitted_output_belongs (expected actual : Request) (receipt : Receipt) {fuel : Nat}
    (observed : replyOutcome (admittedWire receipt) ∈ answers expected actual emptyWorld {} fuel) :
    receipt.output ∈ receipt.values := by
  obtain ⟨_, ⟨evidence⟩⟩ := observed_evidence expected actual receipt emptyWorld emptyWorld_bounded {} observed
  exact List.mem_iff_get.mpr ⟨evidence.index, evidence.element⟩

-- Compiled source execution checks supplement the kernel-checked general laws.
#eval (answers canonical.request canonical.request emptyWorld {} 24).any
  (fun result => decide (result = replyOutcome (admittedWire canonical)))
#eval (answers (duplicateRequest 0) (duplicateRequest 1) emptyWorld {} 24).any
  (fun result => decide (result = replyOutcome refusedWire))

#print axioms vector_selected
#print axioms vector_eventually_admitted
#print axioms outside_vector_never_admitted
#print axioms canonical_run
#print axioms changed_output_rejected
#print axioms forged_receipt_not_admitted
#print axioms duplicate_matches
#print axioms duplicate_data_agree_but_receipts_distinct
#print axioms duplicate_receipt_codes_distinct
#print axioms both_duplicate_occurrences_run
#print axioms cross_occurrence_never_admitted
#print axioms duplicate_third_not_selected
#print axioms malformed_distinct_from_missing_index
#print axioms admitted_output_belongs

end PolarizedNeedMatchedIndex.Examples
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
