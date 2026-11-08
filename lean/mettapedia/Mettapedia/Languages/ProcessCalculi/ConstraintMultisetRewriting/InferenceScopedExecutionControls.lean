import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedExecution
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenApplicationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceProjectionControls

/-! # A concrete returned scoped inference with retained off-query roots -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedExecutionControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenApplicationControls (a b ab definition)
open InferenceSchemaActivation (judgment request)
open InferenceSchemaKernel (Space Value)
open InferenceRequestExecution (Occurrence label location)
open ScopedInferenceValues (Ready base encode)
open ContextualScopeSupport
open ContextualWorldScopeLedger

local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq (ScopedInferenceValues.Head × List Nat))

def locals : Empty → MetaArity base := fun impossible => nomatch impossible
def captures (_ : Unit) : MetaArity base := ([], ())
abbrev active := ContextualActivatedStep.target locals captures

def readyRequest : Ready := ⟨(.requests, request ⟨"ab"⟩ ab []), rfl⟩
def readyA : Ready := ⟨(.judgments, judgment a), rfl⟩
def readyB : Ready := ⟨(.judgments, judgment b), rfl⟩
def readyRule : RuleInstance Ready := ⟨[readyRequest], [readyA], [], [], [readyB]⟩

theorem actual_source_activates :
    InferenceScopedActivation.activate definition ⟨"ab"⟩ [] = some readyRule := by
  obtain ⟨source, lookup, activated⟩ := InferenceSchemaActivation.activate_of_application
    InferenceProjectionControls.BoardControls.first_application
  have lookupAb : definition.1.lookupRule? ⟨"ab"⟩ = some ab := by
    simp [definition, CertificateGSLT.OpenApplicationControls.presentation,
      CalculusLanguageDef.extend, CalculusLanguageDef.lookupRule?, ab]
  have same : source = ab := Option.some.inj (lookup.symm.trans lookupAb)
  subst source
  unfold InferenceScopedActivation.activate
  rw [activated]
  rfl

def requestOccurrence : Occurrence := (0, readyRequest.val)
def premiseOccurrence : Occurrence := (1, readyA.val)
def outputOccurrence : Occurrence := (2, readyB.val)

def readyLabel (occurrence : Occurrence) : Ready :=
  if occurrence.1 = 0 then readyRequest else if occurrence.1 = 1 then readyA else readyB

def state : Configuration Ready Occurrence := ⟨[], {requestOccurrence, premiseOccurrence}⟩
def selection : Selection Occurrence := ⟨[requestOccurrence], [premiseOccurrence], [outputOccurrence]⟩
def scopes (_ : Unit) : Finset Nat := {37}
def retained : List (Observation base captures) := [observe (generator captures ())]
def templates : List (Observation base (ContextualActivatedStep.source locals captures)) :=
  [observe (generator (ContextualActivatedStep.source locals captures) (.inr ()))]
def occupied : Finset Nat :=
  InferenceScopedInventory.reserve locals captures scopes ∅ readyLabel state retained templates

def nativeRule := ContextualRigidActivation.rule locals captures encode readyRule
def nativeRows := ContextualRigidActivation.rows locals captures encode readyLabel
def nativeBefore := ContextualRigidActivation.before captures encode state
def nativeOutputs := ContextualRigidActivation.outputs locals captures encode readyLabel
def problem := ContextualActivatedStep.problem locals captures occupied selection nativeRule nativeRows nativeBefore

theorem actual_problem_has_both_ordered_equations : problem = [
    (ContextualRigidActivation.into encode active readyRequest, ContextualRigidActivation.into encode active readyRequest),
    (ContextualRigidActivation.into encode active readyA, ContextualRigidActivation.into encode active readyA)] := by
  unfold problem nativeRule nativeRows nativeBefore
  rw [ContextualRigidActivation.problem]
  rfl

theorem independent_model : ContextualResidual.Models (generator active)
    (ContextualResidual.observeProblem problem) := by
  apply (ContextualResidual.models_observeProblem (generator active) problem).mpr
  intro equation member
  rw [actual_problem_has_both_ordered_equations] at member
  rcases List.mem_cons.mp member with same | rest
  · subst equation
    rfl
  · have same := List.mem_singleton.mp rest
    subst equation
    rfl

def pending {equations : ContextualResidual.Problem active} :
    ContextualFrameWorklist.Result equations → Option Nat
  | .refuted _ => none
  | .residual update => some update.remaining.length

theorem actual_worklist_returns_closed :
    pending (ContextualFrameWorklist.run 2 active (ContextualResidual.observeProblem problem)) = some 0 := by
  rw [ContextualFrameWorklist.run_eq_local_on_model 2 (ContextualResidual.observeProblem problem)
    active (generator active) independent_model]
  decide +kernel

theorem physical_admission : ContextualGuardedStep.Requirements locals captures
    occupied selection nativeRule nativeRows nativeBefore nativeOutputs := by
  refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_⟩
  · unfold nativeRule nativeRows
    rw [ContextualRigidActivation.prepared_rule]
    rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [nativeBefore, ContextualRigidActivation.before, OccurrenceRelabeling.configuration,
        state, selection, Selection.commit]
    · simp [nativeBefore, ContextualRigidActivation.before, OccurrenceRelabeling.configuration,
        state, selection, Selection.commit]
    · simp [selection, Selection.commit, requestOccurrence, premiseOccurrence]
    · simp [nativeBefore, ContextualRigidActivation.before, OccurrenceRelabeling.configuration,
        state, selection, Selection.commit, requestOccurrence, premiseOccurrence, outputOccurrence]
    · intro query member
      cases member
  · intro check member
    unfold nativeRule nativeRows at member
    rw [ContextualRigidActivation.prepared_rule] at member
    cases member

theorem canonical_readback (occurrence : Occurrence)
    (member : occurrence ∈ state.present ∨ occurrence ∈ selection.made) :
    (readyLabel occurrence).val = label occurrence := by
  simp only [state, Finset.mem_insert, Finset.mem_singleton, selection, List.mem_singleton] at member
  rcases member with (rfl | rfl) | rfl <;> rfl

/-- The concrete driver result, original source activation and complete
off-query root inventory form one actual execution receipt. -/
theorem actual_receipt : Nonempty (InferenceScopedExecution.Receipt definition locals captures) := by
  have closed := actual_worklist_returns_closed
  cases computed : ContextualFrameWorklist.run 2 active (ContextualResidual.observeProblem problem) with
  | refuted impossible => simp only [computed, pending, reduceCtorEq] at closed
  | residual update =>
      have empty : update.remaining = [] := by
        simpa only [computed, pending, Option.some.injEq, List.length_eq_zero_iff] using closed
      exact ⟨{
        id := ⟨"ab"⟩
        arguments := []
        readyRule := readyRule
        activated := actual_source_activates
        readyLabel := readyLabel
        state := state
        scopes := scopes
        oldLedger := ∅
        retained := retained
        templates := templates
        selection := selection
        fuel := 2
        update := update
        returned := ContextualTransportedActivation.from_run locals captures physical_admission update computed empty
        readback := canonical_readback }⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceScopedExecutionControls
