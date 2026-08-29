import Mettapedia.GSLT.Core.ProofRelevantGSLT
import Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem

/-!
# The proof-relevant source-state GSLT for Metamath

This module composes the existing source-owned local, normal-proof, and
compressed-proof relations into one operational GSLT.  It does not replace
them with a new verifier: every transition constructor contains the exact
authored evidence from those relations.

Include resolution is intentionally not a database-state transition.  It is
the preceding source-expansion stage and composes with this state GSLT at the
source boundary.  Keeping that stage separate prevents filesystem traversal
from being confused with a Metamath declaration or proof step.
-/

namespace Mettapedia.Languages.Metamath.SourceStateGSLT

open Mettapedia.GSLT
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.SourceGSLTOperations
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceGSLTNormalTheorem
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem

/-! ## Authored action and evidence fibres -/

/-- The source-owned actions that change Metamath database state.  Every
payload remains inspectable input to a compiler; no filename or source digest
selects a fixed callback. -/
inductive StateAction where
  | localAction (payload : LocalPayload)
  | theoremNormal
      (label : String)
      (formula : ConstantHeadedFormula)
      (proofLabels : List String)
  | theoremCompressed
      (label : String)
      (formula : ConstantHeadedFormula)
      (explicitHeaderLabels : List String)
      (bodyWords : List (List UInt8))

namespace StateAction

/-- Recover the grammar-owned operation identity of an action. -/
def operation : StateAction → SourceOperation
  | .localAction payload => payload.operation
  | .theoremNormal _ _ _ => .checkTheoremNormal
  | .theoremCompressed _ _ _ _ => .checkTheoremCompressed

end StateAction

/-- Proof-relevant semantics of one state action.  The normal constructor
retains its exact label sequence and proof tree; the compressed constructor
retains its decoder, machine execution, node identities, and heap evidence. -/
inductive Transition : StateAction → SourceState → SourceState → Type
  | localTransition
      {payload : LocalPayload} {before after : SourceState}
      (applied : applyLocalPayload? payload before = some after) :
      Transition (.localAction payload) before after
  | theoremNormal
      {before after : SourceState}
      {label : String} {formula : ConstantHeadedFormula}
      {proofLabels : List String}
      (step : NormalTheoremStep before after label formula proofLabels) :
      Transition (.theoremNormal label formula proofLabels) before after
  | theoremCompressed
      {before after : SourceState}
      {label : String} {formula : ConstantHeadedFormula}
      {explicitHeaderLabels : List String}
      {bodyWords : List (List UInt8)}
      (step : CompressedTheoremStep before after label formula
        explicitHeaderLabels bodyWords) :
      Transition
        (.theoremCompressed label formula explicitHeaderLabels bodyWords)
        before after

/-- The complete occurrence fibre of one source-state reduction includes the
selected action and its exact transition evidence. -/
abbrev TransitionEvidence (before after : SourceState) :=
  Sigma fun action => Transition action before after

/-! ## Extensional GSLT and exact step evidence -/

/-- The extensional state GSLT is the propositional shadow of the authored
occurrence relation. -/
def theory : GSLT where
  Term := SourceState
  equations :=
    { r := Eq
      iseqv :=
        { refl := fun _ => rfl
          symm := fun equality => equality.symm
          trans := fun first second => first.trans second } }
  rewrites := fun before after => Nonempty (TransitionEvidence before after)
  rewrites_resp_left := by
    intro before before' after before_eq step
    subst before_eq
    exact ⟨after, step, rfl⟩
  rewrites_resp_right := by
    intro before after after' step after_eq
    subst after_eq
    exact step

/-- Authored occurrences cover exactly the state GSLT's semantic steps. -/
def stepEvidence : Mettapedia.GSLT.ProofRelevant.StepEvidence theory where
  Evidence := TransitionEvidence
  erases_iff := by
    intros
    rfl

/-- The compiler-facing source object: semantic GSLT plus retained transition
occurrences. -/
def system : ProofRelevantGSLT :=
  { theory := theory
    steps := stepEvidence }

/-! ## Operation coverage and boundaries -/

/-- These are exactly the grammar operations whose semantics changes source
database state.  Include resolution belongs to the preceding source-expansion
stage. -/
def stateOperations : List SourceOperation :=
  [.openScope, .closeScope, .declareConstants, .declareVariables,
   .declareDisjoint, .declareFloating, .declareEssential, .declareAxiom,
   .checkTheoremNormal, .checkTheoremCompressed, .completeBlock]

theorem stateOperation_count : stateOperations.length = 11 := by
  decide

theorem stateOperations_eq_source_without_include :
    stateOperations =
      allSourceOperations.filter (fun operation =>
        operation != .resolveInclude) := by
  decide

theorem action_operation_mem_stateOperations (action : StateAction) :
    action.operation ∈ stateOperations := by
  cases action with
  | localAction payload =>
      cases payload <;> simp [StateAction.operation, LocalPayload.operation,
        stateOperations]
  | theoremNormal label formula proofLabels =>
      simp [StateAction.operation, stateOperations]
  | theoremCompressed label formula explicitHeaderLabels bodyWords =>
      simp [StateAction.operation, stateOperations]

theorem action_operation_ne_include (action : StateAction) :
    action.operation ≠ .resolveInclude := by
  intro operation_eq
  have member := action_operation_mem_stateOperations action
  rw [operation_eq] at member
  simp [stateOperations] at member

/-! ## Positive and negative executable controls -/

def oneConstantState : SourceState :=
  { initialState with declaredConstants := ["wff"] }

theorem declare_constant_applies :
    applyLocalPayload? (.declareConstants ["wff"]) initialState =
      some oneConstantState := by
  decide

theorem declare_constant_transition :
    Nonempty
      (Transition (.localAction (.declareConstants ["wff"]))
        initialState oneConstantState) :=
  ⟨.localTransition declare_constant_applies⟩

def oneActiveVariableState : SourceState :=
  { initialState with
    declaredConstants := ["wff"]
    declaredVariables := ["x"]
    activeVariables := ["x"] }

theorem redeclare_active_variable_rejected :
    applyLocalPayload? (.declareVariables ["x"])
      oneActiveVariableState = none := by
  decide

/-- A rejected authored operation has no transition to any successor. -/
theorem no_transition_of_apply_eq_none
    (payload : LocalPayload) (before : SourceState)
    (rejected : applyLocalPayload? payload before = none) :
    forall after, IsEmpty (Transition (.localAction payload) before after) := by
  intro after
  constructor
  intro transition
  cases transition with
  | localTransition applied =>
      rw [rejected] at applied
      contradiction

theorem no_active_variable_redeclaration (after : SourceState) :
    IsEmpty
      (Transition (.localAction (.declareVariables ["x"]))
        oneActiveVariableState after) :=
  no_transition_of_apply_eq_none _ _ redeclare_active_variable_rejected after

#print axioms stateOperations_eq_source_without_include
#print axioms action_operation_ne_include
#print axioms declare_constant_transition
#print axioms no_active_variable_redeclaration

end Mettapedia.Languages.Metamath.SourceStateGSLT
