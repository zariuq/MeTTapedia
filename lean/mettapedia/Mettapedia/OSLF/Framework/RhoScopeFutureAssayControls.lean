import Mettapedia.OSLF.Framework.RhoScopeFutureAssays
import Mettapedia.OSLF.Framework.RhoScopeOperationalFutureControls

/-!
# Actual original scopes with fresh-context paid verdicts

The positive scope retains two original communication premises and has
minimum grade zero. Its configured delivery and base-grade price produce a
confirmation at five tokens, on both sides of fresh-name extension. A smaller
budget emits no verdict. The empty-rule profile supplies an actual paid
refutation, rather than a fabricated scope certificate.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopeFutureAssayControls

open _root_.CategoryTheory Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoScopedParallelEvents RhoScopedNativeAbsence
open RhoScopeFutureAssays RhoScopeOperationalFutureControls
open RhoScopeMinimumReceipts RhoEquationGeneratedScope RhoGeneratedScopeDecision
open Mettapedia.GSLT.Causality ProbeCampaign ComplementaryAssay

local instance (context : Ctx sig) : DecidableEq (Name context) := Classical.decEq _
local instance (admitted : SourceRule → Prop) (context : Ctx sig) :
    DecidablePred (Enabled (context := context) admitted) := Classical.decPred _

def left (question : Bool) : SourceRule → Prop := if question then core else fun _ => False
def right (_question : Bool) : SourceRule → Prop := core
def delivery (_question : Bool) : Nat := 2
def base (_question : Bool) : Nat := 3

def request (question : Bool) : Request Bool (Name []) Nat Nat where
  question := question
  session := 32
  provider := 7
  client := 18
  arrival := some productiveName

def round (question : Bool) (budget : Nat) :=
  completedRound (protocol [] left right delivery base) (request question) budget

theorem actual_minimum_grade_zero : minimumGrade core core productiveName = some 0 := by
  rw [minimumGrade, minimumReceipt?_depth_readout]
  exact productive_minimum_zero

theorem actual_positive_guard : guard (Enabled core) (Enabled core) productiveName = true :=
  (guard_true_iff _ _ _).mpr (certificate_sound productiveCertificate)

theorem complete_scope_price_confirms :
    (round true 5).responses = {(32, Verdict.confirm, 18, productiveName)} := by
  rw [round, completedRound_responses]
  change AssayProbeDelivery.observed _ _ _ 32 7 18 (some productiveName) 5 = _
  rw [AssayProbeDelivery.observed_some]
  change (if 2 + gradePrice core core 3 productiveName ≤ 5 then
    {(32, verdictOf (guard (Enabled core) (Enabled core) productiveName), 18, productiveName)} else 0) = _
  rw [gradePrice, actual_minimum_grade_zero, actual_positive_guard]
  rfl

theorem short_scope_price_is_quiet : (round true 4).responses = 0 := by
  rw [round, completedRound_responses]
  change AssayProbeDelivery.observed _ _ _ 32 7 18 (some productiveName) 4 = _
  rw [AssayProbeDelivery.observed_some]
  change (if 2 + gradePrice core core 3 productiveName ≤ 4 then _ else 0) = 0
  rw [gradePrice, actual_minimum_grade_zero]
  rfl

theorem empty_rule_scope_is_refuted :
    (round false 5).responses = {(32, Verdict.refute, 18, productiveName)} := by
  have rejected := no_scope_from_unavailable_atoms productiveName
  have absent := (minimumReceipt?_none_iff (Enabled (fun _ => False)) (Enabled core) productiveName).mpr rejected
  have guardFalse := (guard_false_iff (Enabled (fun _ => False)) (Enabled core) productiveName).mpr rejected
  rw [round, completedRound_responses]
  change AssayProbeDelivery.observed _ _ _ 32 7 18 (some productiveName) 5 = _
  rw [AssayProbeDelivery.observed_some]
  change (if 2 + gradePrice (fun _ => False) core 3 productiveName ≤ 5 then
    {(32, verdictOf (guard (Enabled (fun _ => False)) (Enabled core) productiveName), 18, productiveName)} else 0) = _
  rw [gradePrice, minimumGrade, absent, guardFalse]
  rfl

theorem actual_confirmation_survives_fresh_context :
    (completedRound (protocol [Srt.nm] left right delivery base)
      (requestMap freshName (request true)) 5).responses =
    {(32, Verdict.confirm, 18, bindQ freshSubstitution productiveName)} := by
  have comparison := completed_responses_preserved freshName left right delivery base (request true) 5
  change (completedRound (protocol [Srt.nm] left right delivery base)
    (requestMap freshName (request true)) 5).responses =
    (round true 5).responses.map (responseMap freshName) at comparison
  have mapped := congrArg (fun responses => responses.map (responseMap freshName))
    complete_scope_price_confirms
  exact comparison.trans (mapped.trans (Multiset.map_singleton _ _))

theorem short_budget_stays_quiet_after_extension :
    (completedRound (protocol [Srt.nm] left right delivery base)
      (requestMap freshName (request true)) 4).responses = 0 := by
  have comparison := completed_responses_preserved freshName left right delivery base (request true) 4
  change (completedRound (protocol [Srt.nm] left right delivery base)
    (requestMap freshName (request true)) 4).responses =
    (round true 4).responses.map (responseMap freshName) at comparison
  have mapped := congrArg (fun responses => responses.map (responseMap freshName))
    short_scope_price_is_quiet
  exact comparison.trans (mapped.trans (Multiset.map_zero _))

def freshEmbedding : Name [] ↪ Name [Srt.nm] :=
  ⟨bindQ freshSubstitution, RhoScopeOperationalFutures.substitution_injective freshName .nm⟩

theorem scope_revision_survives_fresh_context
    (candidates : Finset (Name [])) (name : Name []) :
    bindQ freshSubstitution name ∈ FiniteAssayLearner.revise (prediction left right)
      (candidates.map freshEmbedding)
      true (completedRound (protocol [Srt.nm] left right delivery base)
        (requestMap freshName (request true)) 5).responses ↔
    name ∈ FiniteAssayLearner.revise (prediction left right) candidates true (round true 5).responses := by
  have comparison := completed_responses_preserved freshName left right delivery base (request true) 5
  change (completedRound (protocol [Srt.nm] left right delivery base)
    (requestMap freshName (request true)) 5).responses =
    (round true 5).responses.map (responseMap freshName) at comparison
  rw [comparison]
  exact candidate_retention_preserved freshName left right candidates name true (round true 5).responses

end Mettapedia.OSLF.Framework.RhoScopeFutureAssayControls
