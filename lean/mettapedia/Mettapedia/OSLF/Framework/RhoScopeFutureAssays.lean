import Mettapedia.OSLF.Framework.RhoScopeOperationalFutures
import Mettapedia.OSLF.Framework.RhoScopeProbeLearner

/-!
# Scope verdicts, declared grade prices and revision through permitted futures

The independently selected minimum grade and the actual bounded scope guard
are preserved by syntactic substitutions with a section. The complete paid
receiver is executed on each side. Its public responses agree after mapping
the offered name, and hypothesis retention commutes with that comparison.

The price here is an explicit base schedule plus the minimum successful
scope grade, with zero added on rejection. This schedule is distinct from a
claim about the work required to compute a scope guard or an implementation.
Each actual occurrence history remains in its supplied paid round; agreement
of public verdicts does not identify those histories or native witnesses.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopeFutureAssays

open _root_.CategoryTheory Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoScopedNativeAbsence SyntacticRetractionContexts
open RhoScopedParallelEvents
open RhoScopeOperationalFutures RhoEquationGeneratedScope RhoGeneratedScopeDecision
open RhoScopeMinimumReceipts RhoGeneratedScopeMinimum
open Mettapedia.GSLT.Causality ProbeCampaign ComplementaryAssay

universe q p c
variable {Questions : Type q} {Providers : Type p} {Clients : Type c}
variable [DecidableEq Providers] [DecidableEq Clients]
local instance (context : Ctx sig) : DecidableEq (Name context) := Classical.decEq _
local instance (admitted : SourceRule → Prop) (context : Ctx sig) :
    DecidablePred (Enabled (context := context) admitted) := Classical.decPred _

def minimumGrade {context : Ctx sig} (left right : SourceRule → Prop) (name : Name context) : Option Nat :=
  (minimumReceipt? (Enabled left) (Enabled right) name).map Certificate.depth

theorem minimum_grade_preserved {source target : Object sig} (change : source ⟶ target)
    (left right : SourceRule → Prop) (name : Name target.context.vars) :
    minimumGrade left right (bindQ change.val name) = minimumGrade left right name := by
  unfold minimumGrade
  cases earlier : minimumReceipt? (Enabled left) (Enabled right) name with
  | none =>
      have absent := (minimumReceipt?_none_iff (Enabled left) (Enabled right) name).mp earlier
      have futureAbsent : ¬ generated (Enabled left) (Enabled right) (bindQ change.val name) :=
        fun admitted => absent ((permitted_membership_iff change left right name).mp admitted)
      rw [(minimumReceipt?_none_iff (Enabled left) (Enabled right) _).mpr futureAbsent]
      rfl
  | some first =>
      cases later : minimumReceipt? (Enabled left) (Enabled right) (bindQ change.val name) with
      | none =>
          have present := (minimumReceipt?_presence (Enabled left) (Enabled right) name).mp
            (by rw [earlier]; rfl)
          have futurePresent := (permitted_membership_iff change left right name).mpr present
          exact False.elim ((minimumReceipt?_none_iff (Enabled left) (Enabled right) _).mp later futurePresent)
      | some second =>
          simp only [Option.map_some]
          exact congrArg some (permitted_minimum_depths change left right earlier later).symm

theorem guard_preserved {source target : Object sig} (change : source ⟶ target)
    (left right : SourceRule → Prop) (name : Name target.context.vars) :
    guard (Enabled left) (Enabled right) (bindQ change.val name) =
      guard (Enabled left) (Enabled right) name := by
  apply Bool.eq_iff_iff.mpr
  rw [guard_true_iff, guard_true_iff]
  exact permitted_membership_iff change left right name

def gradePrice {context : Ctx sig} (left right : SourceRule → Prop) (base : Nat)
    (name : Name context) : Nat := base + (minimumGrade left right name).getD 0

theorem grade_price_preserved {source target : Object sig} (change : source ⟶ target)
    (left right : SourceRule → Prop) (base : Nat) (name : Name target.context.vars) :
    gradePrice left right base (bindQ change.val name) = gradePrice left right base name := by
  unfold gradePrice
  rw [minimum_grade_preserved]

def protocol (context : Ctx sig) (left right : Questions → SourceRule → Prop)
    (delivery base : Questions → Nat) : Protocol Questions (Name context) where
  test question := guard (Enabled (left question)) (Enabled (right question))
  deliveryCost question _name := delivery question
  inspectionCost question := gradePrice (left question) (right question) (base question)

def requestMap {source target : Object sig} (change : source ⟶ target)
    (request : Request Questions (Name target.context.vars) Providers Clients) :
    Request Questions (Name source.context.vars) Providers Clients where
  question := request.question
  session := request.session
  provider := request.provider
  client := request.client
  arrival := request.arrival.map (bindQ change.val)

def responseMap {source target : Object sig} (change : source ⟶ target)
    (response : Response (Name target.context.vars) Clients) :
    Response (Name source.context.vars) Clients :=
  (response.1, response.2.1, response.2.2.1, bindQ change.val response.2.2.2)

theorem completed_responses_preserved {source target : Object sig} (change : source ⟶ target)
    (left right : Questions → SourceRule → Prop) (delivery base : Questions → Nat)
    (request : Request Questions (Name target.context.vars) Providers Clients) (budget : Nat) :
    (completedRound (protocol source.context.vars left right delivery base)
      (requestMap change request) budget).responses =
    (completedRound (protocol target.context.vars left right delivery base) request budget).responses.map
      (responseMap change) := by
  rw [completedRound_responses, completedRound_responses]
  cases offered : request.arrival with
  | none =>
      have absent : (requestMap change request).arrival = none := by simp [requestMap, offered]
      rw [absent, AssayProbeDelivery.observed_none, AssayProbeDelivery.observed_none]
      rfl
  | some name =>
      have futureOffer : (requestMap change request).arrival = some (bindQ change.val name) := by
        simp [requestMap, offered]
      rw [futureOffer, AssayProbeDelivery.observed_some, AssayProbeDelivery.observed_some]
      change (if delivery request.question + gradePrice (left request.question)
          (right request.question) (base request.question) (bindQ change.val name) ≤ budget then
        {(request.session, verdictOf (guard (Enabled (left request.question))
          (Enabled (right request.question)) (bindQ change.val name)), request.client, bindQ change.val name)}
        else 0) = (if delivery request.question + gradePrice (left request.question)
          (right request.question) (base request.question) name ≤ budget then
        {(request.session, verdictOf (guard (Enabled (left request.question))
          (Enabled (right request.question)) name), request.client, name)}
        else (0 : Multiset (Response (Name target.context.vars) Clients))).map (responseMap change)
      rw [grade_price_preserved, guard_preserved]
      split_ifs <;> simp only [Multiset.map_singleton, Multiset.map_zero, responseMap]

def prediction {context : Ctx sig} (left right : Questions → SourceRule → Prop)
    (name : Name context) (question : Questions) : Bool :=
  guard (Enabled (left question)) (Enabled (right question)) name

omit [DecidableEq Clients] in
theorem candidate_retention_preserved {source target : Object sig} (change : source ⟶ target)
    (left right : Questions → SourceRule → Prop)
    (candidates : Finset (Name target.context.vars)) (name : Name target.context.vars)
    (question : Questions) (responses : Multiset (Response (Name target.context.vars) Clients)) :
    bindQ change.val name ∈ FiniteAssayLearner.revise (prediction left right)
      (candidates.map ⟨bindQ change.val, substitution_injective change .nm⟩) question
      (responses.map (responseMap change)) ↔
    name ∈ FiniteAssayLearner.revise (prediction left right) candidates question responses := by
  rw [FiniteAssayLearner.revise_mem, FiniteAssayLearner.revise_mem,
    Finset.mem_map_mk]
  constructor
  · rintro ⟨initial, compatible⟩
    refine ⟨initial, ?_⟩
    intro response present
    have future := compatible (responseMap change response) (Multiset.mem_map.mpr ⟨response, present, rfl⟩)
    simpa only [prediction, guard_preserved, responseMap] using future
  · rintro ⟨initial, compatible⟩
    refine ⟨initial, ?_⟩
    intro response present
    obtain ⟨earlier, listed, rfl⟩ := Multiset.mem_map.mp present
    simpa only [prediction, guard_preserved, responseMap] using compatible earlier listed

end Mettapedia.OSLF.Framework.RhoScopeFutureAssays
