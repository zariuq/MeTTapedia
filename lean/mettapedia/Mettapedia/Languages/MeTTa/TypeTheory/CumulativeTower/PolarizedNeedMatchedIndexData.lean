import Mettapedia.GSLT.LanguageDef.MatchedIndexJudgment
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RawInferenceService

/-!
# Raw selected-match requests and independently checked dependent receipts

Requests retain the pattern, subject, matcher-list occurrence and element
index. Receipts are ordinary data: they contain no proof or trusted verdict.
The consumer rechecks the selected occurrence and the existing bounded-index
checker. Its soundness reconstructs two actual finite indices. Equal binding
values at distinct matcher positions are not interchangeable requests.

The wire representation reuses the existing exact Pattern/list codecs.
This boundary does not add native Fin syntax or a general dependent checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace PolarizedNeedMatchedIndex

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceCettaWire

abbrev Wire := RawInferenceService.Wire

structure Request where
  pattern : Pattern
  subject : Pattern
  occurrence : Nat
  index : Nat
  deriving DecidableEq, Repr

structure Receipt where
  request : Request
  bindings : Bindings
  values : List Pattern
  output : Pattern
  deriving DecidableEq, Repr

/-- The producer computes only raw data using the existing matcher/checker. -/
def select? (request : Request) : Option Receipt :=
  match getElem? (matchPattern request.pattern request.subject) request.occurrence with
  | none => none
  | some bindings =>
      match bindings.lookup "items" with
      | some (.collection .vec values none) =>
          (MatchedIndexJudgment.checkIndex request.index bindings).map
            (fun output => ⟨request, bindings, values, output⟩)
      | _ => none

/-- All retained fields are checked independently of producer provenance. -/
def validate (expected : Request) (receipt : Receipt) : Bool :=
  decide (receipt.request = expected) &&
  decide (getElem? (matchPattern expected.pattern expected.subject) expected.occurrence =
    some receipt.bindings) &&
  decide (receipt.bindings.lookup "items" = some (.collection .vec receipt.values none)) &&
  decide (MatchedIndexJudgment.checkIndex expected.index receipt.bindings = some receipt.output)

theorem validate_iff (expected : Request) (receipt : Receipt) :
    validate expected receipt = true ↔
      receipt.request = expected ∧
      getElem? (matchPattern expected.pattern expected.subject) expected.occurrence = some receipt.bindings ∧
      receipt.bindings.lookup "items" = some (.collection .vec receipt.values none) ∧
      MatchedIndexJudgment.checkIndex expected.index receipt.bindings = some receipt.output := by
  simp only [validate, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-- Both the match occurrence and bounded element belong to the exact reply. -/
structure Evidence (expected : Request) (receipt : Receipt) where
  request_eq : receipt.request = expected
  position : Fin (matchPattern expected.pattern expected.subject).length
  position_eq : position.val = expected.occurrence
  selected : (matchPattern expected.pattern expected.subject).get position = receipt.bindings
  vector : receipt.bindings.lookup "items" = some (.collection .vec receipt.values none)
  index : Fin receipt.values.length
  index_eq : index.val = expected.index
  element : receipt.values.get index = receipt.output

theorem validate_evidence_iff (expected : Request) (receipt : Receipt) :
    validate expected receipt = true ↔ Nonempty (Evidence expected receipt) := by
  rw [validate_iff]
  constructor
  · rintro ⟨same, selected, vector, checked⟩
    obtain ⟨positionBound, selected⟩ := List.getElem?_eq_some_iff.mp selected
    simp only [MatchedIndexJudgment.checkIndex, vector] at checked
    obtain ⟨indexBound, element⟩ := List.getElem?_eq_some_iff.mp checked
    exact ⟨⟨same, ⟨expected.occurrence, positionBound⟩, rfl, selected,
      vector, ⟨expected.index, indexBound⟩, rfl, element⟩⟩
  · rintro ⟨evidence⟩
    refine ⟨evidence.request_eq, ?_, evidence.vector, ?_⟩
    · rw [← evidence.position_eq]
      exact List.getElem?_eq_some_iff.mpr ⟨evidence.position.isLt, evidence.selected⟩
    · simp only [MatchedIndexJudgment.checkIndex, evidence.vector]
      rw [← evidence.index_eq]
      exact List.getElem?_eq_some_iff.mpr ⟨evidence.index.isLt, evidence.element⟩

/-- Successful production satisfies the independent complete-request check. -/
theorem select_validates {request : Request} {receipt : Receipt}
    (produced : select? request = some receipt) : validate request receipt = true := by
  unfold select? at produced
  cases selected : getElem? (matchPattern request.pattern request.subject) request.occurrence with
  | none => simp only [selected, reduceCtorEq] at produced
  | some bindings =>
      simp only [selected] at produced
      split at produced
      next values vector =>
        cases checked : MatchedIndexJudgment.checkIndex request.index bindings with
        | none => simp only [checked, Option.map_none, reduceCtorEq] at produced
        | some output =>
            simp only [checked, Option.map_some, Option.some.injEq] at produced
            cases produced
            exact (validate_iff _ _).mpr ⟨rfl, selected, vector, checked⟩
      next => cases produced

theorem valid_selected {request : Request} {receipt : Receipt}
    (checked : validate request receipt = true) : select? request = some receipt := by
  obtain ⟨same, selected, vector, output⟩ := (validate_iff _ _).mp checked
  cases receipt with
  | mk actual bindings values value =>
      dsimp at same selected vector output
      cases same
      simp only [select?, selected, vector, output, Option.map_some]

theorem wrong_request_rejected {expected : Request} {receipt : Receipt}
    (different : receipt.request ≠ expected) : validate expected receipt = false := by
  simp [validate, different]

theorem outside_index_rejected {expected : Request} {receipt : Receipt}
    (outside : receipt.values.length ≤ expected.index) : validate expected receipt = false := by
  cases checked : validate expected receipt with
  | false => rfl
  | true =>
      obtain ⟨evidence⟩ := (validate_evidence_iff _ _).mp checked
      have bound := evidence.index.isLt
      rw [evidence.index_eq] at bound
      exact False.elim (Nat.not_lt_of_ge outside bound)

def encodeBinding (binding : String × Pattern) : Wire :=
  .application "PrimeMatchBinding" [.string binding.1, encodePattern binding.2]

def decodeBinding : Wire → Option (String × Pattern)
  | .application "PrimeMatchBinding" [.string name, value] => do
      return (name, ← decodePattern value)
  | _ => none

@[simp] theorem decode_encode_binding (binding : String × Pattern) :
    decodeBinding (encodeBinding binding) = some binding := by
  cases binding
  simp [decodeBinding, encodeBinding]

def encodeRequest (request : Request) : Wire :=
  .application "PrimeMatchedIndexRequest"
    [encodePattern request.pattern, encodePattern request.subject,
      .natural request.occurrence, .natural request.index]

def decodeRequest : Wire → Option Request
  | .application "PrimeMatchedIndexRequest" [pattern, subject, .natural occurrence, .natural index] => do
      return ⟨← decodePattern pattern, ← decodePattern subject, occurrence, index⟩
  | _ => none

def encodeReceipt (receipt : Receipt) : Wire :=
  .application "PrimeMatchedIndexReceipt"
    [encodeRequest receipt.request, encodeList encodeBinding receipt.bindings,
      encodePatterns receipt.values, encodePattern receipt.output]

def decodeReceipt : Wire → Option Receipt
  | .application "PrimeMatchedIndexReceipt" [request, bindings, values, output] => do
      return ⟨← decodeRequest request, ← decodeList decodeBinding bindings,
        ← decodePatterns values, ← decodePattern output⟩
  | _ => none

@[simp] theorem decode_encode_request (request : Request) :
    decodeRequest (encodeRequest request) = some request := by
  cases request
  simp [decodeRequest, encodeRequest]

@[simp] theorem decode_encode_receipt (receipt : Receipt) :
    decodeReceipt (encodeReceipt receipt) = some receipt := by
  cases receipt
  simp [decodeReceipt, encodeReceipt, decodeList_encodeList decodeBinding encodeBinding decode_encode_binding]

theorem encodeReceipt_injective : Function.Injective encodeReceipt := by
  intro first second same
  have decoded := congrArg decodeReceipt same
  simpa only [decode_encode_receipt, Option.some.injEq] using decoded

/-- Rejection of a query is data and does not assert its logical negation. -/
def selectedWire (request : Request) : Wire :=
  ((select? request).map encodeReceipt).getD (.symbol "PrimeMatchedIndexNotSelected")

def selectWire (input : Wire) : Wire :=
  ((decodeRequest input).map selectedWire).getD (.symbol "PrimeMatchedIndexMalformedRequest")

def admittedWire (receipt : Receipt) : Wire :=
  .application "PrimeMatchedIndexAdmitted" [encodeReceipt receipt]

def refusedWire : Wire := .symbol "PrimeMatchedIndexNotAdmitted"

/-- The complete raw receipt is returned only after independent checking. -/
def consumeWire (expected : Request) (input : Wire) : Wire :=
  match decodeReceipt input with
  | some receipt => if validate expected receipt then admittedWire receipt else refusedWire
  | none => refusedWire

@[simp] theorem selectWire_request (request : Request) :
    selectWire (encodeRequest request) = selectedWire request := by
  simp [selectWire]

@[simp] theorem consumeWire_receipt (expected : Request) (receipt : Receipt) :
    consumeWire expected (encodeReceipt receipt) =
      if validate expected receipt then admittedWire receipt else refusedWire := by
  simp only [consumeWire, decode_encode_receipt]

theorem consumeWire_admitted_iff (expected : Request) (input : Wire) (receipt : Receipt) :
    consumeWire expected input = admittedWire receipt ↔
      decodeReceipt input = some receipt ∧ validate expected receipt = true := by
  unfold consumeWire
  cases decoded : decodeReceipt input with
  | none => simp [refusedWire, admittedWire]
  | some actual =>
      by_cases checked : validate expected actual = true
      · simp only [checked, if_true, admittedWire, CettaWire.Term.application.injEq,
          List.cons.injEq, and_true, true_and, Option.some.injEq]
        rw [encodeReceipt_injective.eq_iff]
        constructor
        · intro same; cases same; exact ⟨rfl, checked⟩
        · exact And.left
      · simp only [checked, if_false, refusedWire, admittedWire, reduceCtorEq, Option.some.injEq]
        constructor
        · intro impossible; cases impossible
        · rintro ⟨rfl, accepted⟩
          exact False.elim (checked accepted)

theorem consume_selected_iff (expected actual : Request) (receipt : Receipt) :
    consumeWire expected (selectedWire actual) = admittedWire receipt ↔
      select? actual = some receipt ∧ validate expected receipt = true := by
  rw [consumeWire_admitted_iff]
  cases selected : select? actual with
  | none => simp [selectedWire, selected, decodeReceipt]
  | some result => simp only [selectedWire, selected, Option.map_some, Option.getD_some,
      decode_encode_receipt]

theorem evidence_compiled_match {expected : Request} {receipt : Receipt}
    (evidence : Evidence expected receipt) (plan : PatternPlanBindingDecisionCompilation.FirstOrder.PatternPlan)
    (pattern : expected.pattern = plan.erase) :
    BindingDecisionLanguage.LanguageReaches
      (BindingDecisionLanguage.encodeState (.run
        (PatternPlanBindingDecisionCompilation.compile plan) expected.subject []))
      (BindingDecisionLanguage.encodeState (.done receipt.bindings)) ∧
      MatchedIndexJudgment.checkIndex expected.index receipt.bindings = some receipt.output := by
  have member : receipt.bindings ∈ matchPattern expected.pattern expected.subject :=
    List.mem_iff_get.mpr ⟨evidence.position, evidence.selected⟩
  rw [pattern] at member
  exact ⟨(BindingDecisionLanguage.languageReaches_compile_iff_mem_matchPattern plan _ _).mpr member,
    ((validate_iff _ _).mp ((validate_evidence_iff _ _).mpr ⟨evidence⟩)).2.2.2⟩

#print axioms validate_evidence_iff
#print axioms select_validates
#print axioms valid_selected
#print axioms decode_encode_receipt
#print axioms consumeWire_admitted_iff
#print axioms consume_selected_iff
#print axioms evidence_compiled_match
#print axioms outside_index_rejected

end PolarizedNeedMatchedIndex
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
