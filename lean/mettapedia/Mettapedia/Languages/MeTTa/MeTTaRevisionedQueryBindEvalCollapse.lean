import Mettapedia.GSLT.Dynamics.CollapseObservationContract
import Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval

/-!
# Collapse folds for revisioned MeTTa queries

This module connects the revisioned query semantics to the generic collapse
contract without choosing an evaluator representation.  A frontend supplies
an answer enumeration and proves that its nonemptiness is exactly the
proof-relevant `Match` relation.  The physical backend may then replace full
answer construction by exact candidate-frontier membership, provided it
supplies the independently proved completeness, exactness, and template
totality certificates.

The resulting `DirectFold` is phrased over the semantic producer interface.
It can therefore be pulled back along a new evaluator presentation without
changing the fold or its proof.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval

open Mettapedia.GSLT.Dynamics.Collapse
open Mettapedia.GSLT.Dynamics.CollapseObservationContract
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Syntax

universe uSpace

namespace ExistenceObserver

/-- A finite evaluator presentation of all visible answers to one match
query.  `nonempty_iff` is the representation-independent adequacy boundary:
the list may come from an abstract machine, a cursor, or a compiled region. -/
structure AnswerEnumeration (model : Model)
    {SpaceName : Type uSpace} (world : RevisionedSpaces SpaceName)
    (space : SpaceName) (pattern template : Pattern) where
  answers : List Pattern
  nonempty_iff : answers ≠ [] ↔
    HasMatchAnswer model world space pattern template

/-- Interpret an adequate answer enumeration as its unit-multiplicity
observation stream. -/
def answerProducer (model : Model)
    {SpaceName : Type uSpace} (world : RevisionedSpaces SpaceName)
    (space : SpaceName) (pattern template : Pattern)
    {Receipt : Type} (receipt : Receipt) :
    Producer (AnswerEnumeration model world space pattern template)
      (Obs Pattern Receipt) where
  materialize enumeration := unitObservations receipt enumeration.answers

/-- Exact candidate-frontier membership and an adequate answer enumeration
have the same nonemptiness observation. -/
theorem frontierContainsPattern_iff_enumeration_nonempty
    (model : Model)
    {SpaceName : Type uSpace} {world : RevisionedSpaces SpaceName}
    {space : SpaceName} {pattern template : Pattern}
    {selector : CandidateSelector world space}
    (complete : CandidateComplete model (pattern := pattern) selector)
    (exact : CandidateExact model (pattern := pattern) selector)
    (total : TemplateTotalOnMatches model world space pattern template)
    (enumeration : AnswerEnumeration model world space pattern template) :
    FrontierContainsPattern pattern selector ↔ enumeration.answers ≠ [] := by
  rw [enumeration.nonempty_iff,
    hasMatchAnswer_iff_hasMatch model total,
    hasMatch_iff_frontierContainsPattern model complete exact]

/-- A decidable exact frontier directly implements the `AnyAlg` fold over
the reference answer producer.  No answer term is inspected or constructed
by `run`; all language-specific obligations occur in the three certificates
above. -/
def exactFrontierAnyFold
    (model : Model)
    {SpaceName : Type uSpace} {world : RevisionedSpaces SpaceName}
    {space : SpaceName} {pattern template : Pattern}
    {selector : CandidateSelector world space}
    [Decidable (FrontierContainsPattern pattern selector)]
    (complete : CandidateComplete model (pattern := pattern) selector)
    (exact : CandidateExact model (pattern := pattern) selector)
    (total : TemplateTotalOnMatches model world space pattern template)
    {Receipt : Type} (receipt : Receipt) :
    DirectFold
      (answerProducer model world space pattern template receipt)
      (AnyAlg Pattern Receipt) where
  run _ := decide (FrontierContainsPattern pattern selector)
  refines enumeration := by
    have frontier_iff := frontierContainsPattern_iff_enumeration_nonempty
      model complete exact total enumeration
    cases answers_eq : enumeration.answers with
    | nil =>
        have frontier_absent : ¬ FrontierContainsPattern pattern selector := by
          intro frontier
          exact (frontier_iff.mp frontier) answers_eq
        simp [frontier_absent, answerProducer, unitObservations, answers_eq,
          collapseWith, foldStream, AnyAlg]
    | cons answer rest =>
        have frontier_present : FrontierContainsPattern pattern selector :=
          frontier_iff.mpr (by simp [answers_eq])
        simp [frontier_present, answerProducer, unitObservations, answers_eq,
          collapseWith, foldStream, AnyAlg]

/-! ## Discriminating canaries -/

namespace Canary

/-- Changing an adequate evaluator's answer representation cannot change the
existence result when both representations describe the same nonemptiness. -/
theorem enumeration_representation_irrelevant
    (model : Model)
    {SpaceName : Type uSpace} {world : RevisionedSpaces SpaceName}
    {space : SpaceName} {pattern template : Pattern}
    (left right : AnswerEnumeration model world space pattern template) :
    (left.answers ≠ []) ↔ (right.answers ≠ []) := by
  rw [left.nonempty_iff, right.nonempty_iff]

/-- Completeness alone cannot admit the exact-membership fold for an open
pattern: the concrete singleton selector is complete but fails exactness. -/
theorem complete_frontier_need_not_be_exact :
    Nonempty (CandidateComplete
      (structuralModel fun _ => 0)
      (pattern :=
        Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.Canary.anyPattern)
      Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.Canary.selectAllCandidates) ∧
    ¬ CandidateExact
      (structuralModel fun _ => 0)
      (pattern :=
        Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.Canary.anyPattern)
      Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.Canary.selectAllCandidates :=
  ⟨⟨Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.Canary.selectAllCandidates_complete⟩,
    Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval.Canary.selectAllCandidates_not_exactForOpenPattern⟩

end Canary

/-! ## Axiom audit -/

#print axioms frontierContainsPattern_iff_enumeration_nonempty
#print axioms exactFrontierAnyFold
#print axioms Canary.enumeration_representation_irrelevant
#print axioms Canary.complete_frontier_need_not_be_exact

end ExistenceObserver

/-! ## Exact cardinality without answer materialization -/

namespace CardinalityObserver

/-- The semantic answer bag of one revisioned match.  The outer bind retains
stored-atom multiplicity, the inner `filterMap` retains matcher multiplicity
and exactly the successful checked template instantiations.  No evaluation
order or physical candidate representation occurs in this definition. -/
def answerBag (model : Model)
    {SpaceName : Type uSpace} (world : RevisionedSpaces SpaceName)
    (space : SpaceName) (pattern template : Pattern) : Multiset Pattern :=
  (world.contents space).bind fun candidate =>
    Multiset.filterMap
      (fun bindings => applyBindingsGround? bindings template)
      (model.matchAtoms pattern candidate)

/-- A frontend enumeration is adequate for cardinality when it presents the
semantic answer bag exactly.  Its list order is deliberately unconstrained. -/
structure AnswerEnumeration (model : Model)
    {SpaceName : Type uSpace} (world : RevisionedSpaces SpaceName)
    (space : SpaceName) (pattern template : Pattern) where
  answers : List Pattern
  exact : (answers : Multiset Pattern) =
    answerBag model world space pattern template

/-- Interpret an exact bag enumeration as a unit-multiplicity stream. -/
def answerProducer (model : Model)
    {SpaceName : Type uSpace} (world : RevisionedSpaces SpaceName)
    (space : SpaceName) (pattern template : Pattern)
    {Receipt : Type} (receipt : Receipt) :
    Producer (AnswerEnumeration model world space pattern template)
      (Obs Pattern Receipt) where
  materialize enumeration :=
    ExistenceObserver.unitObservations receipt enumeration.answers

/-- A physical counter is admitted only by equality with the semantic answer
bag cardinality.  A trie scan, relational join, abstract machine, or future
Prime presentation may establish this same interface independently. -/
structure ExactBackendCount (model : Model)
    {SpaceName : Type uSpace} (world : RevisionedSpaces SpaceName)
    (space : SpaceName) (pattern template : Pattern) where
  count : Nat
  exact : count = (answerBag model world space pattern template).card

/-- Counting unit-multiplicity answer occurrences is list length. -/
theorem collapse_count_unitObservations
    {Answer Receipt : Type} (receipt : Receipt) (answers : List Answer) :
    collapseWith (CountAlg Answer Receipt)
        (ExistenceObserver.unitObservations receipt answers) =
      answers.length := by
  induction answers with
  | nil => rfl
  | cons answer rest ih =>
      change 1 +
          collapseWith (CountAlg Answer Receipt)
            (ExistenceObserver.unitObservations receipt rest) =
        rest.length + 1
      rw [ih, Nat.add_comm]

/-- An exact physical count directly refines materialize-then-count for every
adequate answer enumeration.  `run` neither chooses a schedule nor constructs
an answer term. -/
def exactCountFold
    (model : Model)
    {SpaceName : Type uSpace} {world : RevisionedSpaces SpaceName}
    {space : SpaceName} {pattern template : Pattern}
    (backend : ExactBackendCount model world space pattern template)
    {Receipt : Type} (receipt : Receipt) :
    DirectFold
      (answerProducer model world space pattern template receipt)
      (CountAlg Pattern Receipt) where
  run _ := backend.count
  refines enumeration := by
    change backend.count =
      collapseWith (CountAlg Pattern Receipt)
        (ExistenceObserver.unitObservations receipt enumeration.answers)
    rw [collapse_count_unitObservations]
    calc
      backend.count =
          (answerBag model world space pattern template).card :=
        backend.exact
      _ = (enumeration.answers : Multiset Pattern).card := by
        rw [enumeration.exact]
      _ = enumeration.answers.length := by simp

/-! ### Ground guards as scalar action on a continuation -/

/-- The reference meaning of a ground match followed by a continuation: every
semantic occurrence of the ground pattern runs the same continuation once.
This definition is independent of the backend's candidate representation and
of the strategy used to enumerate the occurrences. -/
def groundGuardThen
    (model : Model)
    {SpaceName : Type uSpace} (world : RevisionedSpaces SpaceName)
    (space : SpaceName) (pattern template : Pattern)
    {Answer Receipt : Type}
    (continuation : List (Obs Answer Receipt)) :
    List (Obs Answer Receipt) :=
  repeatObservations
    (answerBag model world space pattern template).card
    continuation

/-- An exact backend count acts on a count-observed continuation by scalar
multiplication.  This is the representation-independent law used when a
ground conjunction leg is replaced by an exact index count. -/
theorem exactBackendCount_groundGuardThen
    (model : Model)
    {SpaceName : Type uSpace} {world : RevisionedSpaces SpaceName}
    {space : SpaceName} {pattern template : Pattern}
    (backend : ExactBackendCount model world space pattern template)
    {Answer Receipt : Type}
    (continuation : List (Obs Answer Receipt)) :
    collapseWith (CountAlg Answer Receipt)
        (groundGuardThen model world space pattern template continuation) =
      backend.count *
        collapseWith (CountAlg Answer Receipt) continuation := by
  rw [groundGuardThen, collapse_count_repeatObservations, backend.exact]

/-- Because counting forgets answer identity, the scaled continuation may be
published as one weighted witness.  The witness is a physical presentation of
the count result, not a claim that the answer bag has one element. -/
theorem exactBackendCount_groundGuardThen_as_weight
    (model : Model)
    {SpaceName : Type uSpace} {world : RevisionedSpaces SpaceName}
    {space : SpaceName} {pattern template : Pattern}
    (backend : ExactBackendCount model world space pattern template)
    {Answer Receipt : Type} (answer : Answer) (receipt : Receipt)
    (continuation : List (Obs Answer Receipt)) :
    collapseWith (CountAlg Answer Receipt)
        (groundGuardThen model world space pattern template continuation) =
      collapseWith (CountAlg Answer Receipt)
        [⟨answer,
          backend.count *
            collapseWith (CountAlg Answer Receipt) continuation,
          receipt⟩] := by
  rw [exactBackendCount_groundGuardThen model backend continuation]
  simp [collapseWith, foldStream, CountAlg]

/-! ### Provenance-classified observation

An answer's payload does not determine how the evaluator produced it.  In
particular, an `Error`-headed term may be ordinary quoted or matched data.
The evaluator presentation supplies the origin class; the observer algebra
consumes only that interface. -/

inductive AnswerOrigin where
  | ordinaryData
  | controlFallback
deriving DecidableEq, Repr

structure ClassifiedAnswer where
  value : Pattern
  origin : AnswerOrigin
deriving DecidableEq, Repr

def ClassifiedAnswer.isControlFallback
    (answer : ClassifiedAnswer) : Bool :=
  answer.origin == .controlFallback

def classifiedProducer {Receipt : Type} (receipt : Receipt) :
    Producer (List ClassifiedAnswer) (Obs ClassifiedAnswer Receipt) where
  materialize answers :=
    ExistenceObserver.unitObservations receipt answers

/-- A terminal match whose template is instantiated as data presents each
semantic match answer as ordinary data.  This is the producer-level contract
implemented by a frontend's value/data plan certificate; it does not mention
the frontend's plan representation. -/
def ordinaryMatchProducer
    (model : Model)
    {SpaceName : Type uSpace} (world : RevisionedSpaces SpaceName)
    (space : SpaceName) (pattern template : Pattern)
    {Receipt : Type} (receipt : Receipt) :
    Producer (AnswerEnumeration model world space pattern template)
      (Obs ClassifiedAnswer Receipt) where
  materialize enumeration :=
    ExistenceObserver.unitObservations receipt
      (enumeration.answers.map fun answer =>
        ⟨answer, .ordinaryData⟩)

/-- The semantic producer for a data-instantiating terminal match excludes
control fallback by construction.  A BN machine, CBPV machine, cursor, or trie
backend may reuse this certificate after proving that it presents this
producer. -/
theorem ordinaryMatchProducer_excludes_controlFallback
    (model : Model)
    {SpaceName : Type uSpace} (world : RevisionedSpaces SpaceName)
    (space : SpaceName) (pattern template : Pattern)
    {Receipt : Type} (receipt : Receipt) :
    Producer.ExcludesFallback
      (ordinaryMatchProducer model world space pattern template receipt)
      ClassifiedAnswer.isControlFallback := by
  intro enumeration observation member
  simp [ordinaryMatchProducer, ExistenceObserver.unitObservations] at member
  rcases member with ⟨answer, answerMember, rfl⟩
  rfl

/-- An exact backend cardinality is also an exact plain count over the
ordinary-data presentation. -/
def exactOrdinaryMatchCountFold
    (model : Model)
    {SpaceName : Type uSpace} {world : RevisionedSpaces SpaceName}
    {space : SpaceName} {pattern template : Pattern}
    (backend : ExactBackendCount model world space pattern template)
    {Receipt : Type} (receipt : Receipt) :
    DirectFold
      (ordinaryMatchProducer model world space pattern template receipt)
      (CountAlg ClassifiedAnswer Receipt) where
  run _ := backend.count
  refines enumeration := by
    change backend.count =
      collapseWith (CountAlg ClassifiedAnswer Receipt)
        (ExistenceObserver.unitObservations receipt
          (enumeration.answers.map fun answer =>
            (⟨answer, .ordinaryData⟩ : ClassifiedAnswer)))
    rw [collapse_count_unitObservations]
    simp only [List.length_map]
    calc
      backend.count =
          (answerBag model world space pattern template).card :=
        backend.exact
      _ = (enumeration.answers : Multiset Pattern).card := by
        rw [enumeration.exact]
      _ = enumeration.answers.length := by simp

/-- The live optimization theorem: a direct backend count implements the
preferred/fallback observation for a terminal data match because the producer
certificate excludes control fallback.  The implementation remains the same
plain counter. -/
def exactOrdinaryMatchPreferredCountFold
    (model : Model)
    {SpaceName : Type uSpace} {world : RevisionedSpaces SpaceName}
    {space : SpaceName} {pattern template : Pattern}
    (backend : ExactBackendCount model world space pattern template)
    {Receipt : Type} (receipt : Receipt) :
    DirectFold
      (ordinaryMatchProducer model world space pattern template receipt)
      (PreferCountAlg ClassifiedAnswer.isControlFallback) :=
  DirectFold.preferCountOfExcludesFallback
    ClassifiedAnswer.isControlFallback
    (exactOrdinaryMatchCountFold model backend receipt)
    (ordinaryMatchProducer_excludes_controlFallback
      model world space pattern template receipt)

/-- A physical two-bin summary is admitted only with an equality proof to the
provenance-classified reference observation.  A trie, cursor, BN machine, or
CBPV machine may establish the same interface without sharing a runtime
representation. -/
structure ExactClassifiedPreferredCount
    (answers : List ClassifiedAnswer)
    {Receipt : Type} (receipt : Receipt) where
  summary : PreferredFallbackCount
  exact : summary =
    foldStream
      (PreferCountAlg (Receipt := Receipt)
        ClassifiedAnswer.isControlFallback)
      ((classifiedProducer receipt).materialize answers)

/-- Finalize an exact ordinary/fallback summary. -/
def exactPreferredCount
    {answers : List ClassifiedAnswer}
    {Receipt : Type} {receipt : Receipt}
    (backend : ExactClassifiedPreferredCount answers receipt) : Nat :=
  backend.summary.observe

/-- Direct two-bin counting refines materialize-then-observe without inspecting
payload syntax or constraining the evaluator presentation. -/
theorem exactPreferredCount_refines
    (answers : List ClassifiedAnswer)
    {Receipt : Type} (receipt : Receipt)
    (backend : ExactClassifiedPreferredCount answers receipt) :
    exactPreferredCount backend =
      collapseWith
        (PreferCountAlg (Receipt := Receipt)
          ClassifiedAnswer.isControlFallback)
        ((classifiedProducer receipt).materialize answers) := by
  change backend.summary.observe = _
  rw [backend.exact]
  rfl

/-! ### Discriminating canaries -/

namespace Canary

/-- A datum whose spelling is `Empty` is still one produced occurrence.  A
zero-outcome computation is represented by no row, not by inspecting this
payload spelling. -/
def emptySpelledData : Pattern := .apply "Empty" []

def errorPayload : Pattern := .apply "Error" [.apply "source" []]

def ordinaryPayload : Pattern := .apply "ordinary" []

def errorSpelledData : ClassifiedAnswer :=
  ⟨errorPayload, .ordinaryData⟩

def raisedError : ClassifiedAnswer :=
  ⟨errorPayload, .controlFallback⟩

def ordinaryData : ClassifiedAnswer :=
  ⟨ordinaryPayload, .ordinaryData⟩

/-- Equal payloads may have different observation provenance. -/
theorem equal_payload_does_not_fix_origin :
    errorSpelledData.value = raisedError.value ∧
    errorSpelledData.origin ≠ raisedError.origin := by
  decide

/-- An Error-headed value occurrence remains ordinary data. -/
theorem errorSpelledData_is_ordinary :
    errorSpelledData.isControlFallback = false := by
  rfl

/-- A control fallback is classified by its origin, even when its payload is
textually identical to ordinary data. -/
theorem raisedError_is_control_fallback :
    raisedError.isControlFallback = true := by
  rfl

theorem emptySpelledData_counts_one {Receipt : Type} (receipt : Receipt) :
    collapseWith (CountAlg Pattern Receipt)
        (ExistenceObserver.unitObservations receipt [emptySpelledData]) = 1 := by
  simp [ExistenceObserver.unitObservations, collapseWith, foldStream,
    CountAlg]

theorem zeroOutcomes_count_zero {Receipt : Type} (receipt : Receipt) :
    collapseWith (CountAlg Pattern Receipt)
        (ExistenceObserver.unitObservations receipt []) = 0 := by
  rfl

/-- An all-fallback answer bag retains every occurrence. -/
theorem preferredCount_all_fallbacks_remain_visible {Receipt : Type}
    (receipt : Receipt) :
    collapseWith
      (PreferCountAlg (Receipt := Receipt)
        ClassifiedAnswer.isControlFallback)
      [⟨raisedError, 2, receipt⟩] = 2 := by
  rfl

/-- One ordinary answer suppresses control-fallback occurrences. -/
theorem preferredCount_mixed_suppresses_control_fallbacks {Receipt : Type}
    (receipt : Receipt) :
    collapseWith
      (PreferCountAlg (Receipt := Receipt)
        ClassifiedAnswer.isControlFallback)
      [⟨raisedError, 2, receipt⟩, ⟨ordinaryData, 3, receipt⟩] = 3 := by
  rfl

/-- Payload spelling cannot cause ordinary matched data to disappear. -/
theorem preferredCount_error_spelling_remains_ordinary {Receipt : Type}
    (receipt : Receipt) :
    collapseWith
      (PreferCountAlg (Receipt := Receipt)
        ClassifiedAnswer.isControlFallback)
      [⟨errorSpelledData, 2, receipt⟩, ⟨ordinaryData, 3, receipt⟩] = 5 := by
  rfl

/-- Two exact frontend orderings of one answer bag have the same count. -/
theorem enumeration_order_irrelevant
    (model : Model)
    {SpaceName : Type uSpace} {world : RevisionedSpaces SpaceName}
    {space : SpaceName} {pattern template : Pattern}
    (left right : AnswerEnumeration model world space pattern template) :
    left.answers.length = right.answers.length := by
  have sameBag : (left.answers : Multiset Pattern) =
      (right.answers : Multiset Pattern) :=
    left.exact.trans right.exact.symm
  exact Multiset.coe_eq_coe.mp sameBag |>.length_eq

end Canary

/-! ## Cardinality axiom audit -/

#print axioms collapse_count_unitObservations
#print axioms exactCountFold
#print axioms exactBackendCount_groundGuardThen
#print axioms exactBackendCount_groundGuardThen_as_weight
#print axioms exactPreferredCount_refines
#print axioms ordinaryMatchProducer_excludes_controlFallback
#print axioms exactOrdinaryMatchCountFold
#print axioms exactOrdinaryMatchPreferredCountFold
#print axioms Canary.emptySpelledData_counts_one
#print axioms Canary.equal_payload_does_not_fix_origin
#print axioms Canary.errorSpelledData_is_ordinary
#print axioms Canary.raisedError_is_control_fallback
#print axioms Canary.zeroOutcomes_count_zero
#print axioms Canary.preferredCount_all_fallbacks_remain_visible
#print axioms Canary.preferredCount_mixed_suppresses_control_fallbacks
#print axioms Canary.preferredCount_error_spelling_remains_ordinary
#print axioms Canary.enumeration_order_irrelevant

end CardinalityObserver

end Mettapedia.Languages.MeTTa.MeTTaRevisionedQueryBindEval
