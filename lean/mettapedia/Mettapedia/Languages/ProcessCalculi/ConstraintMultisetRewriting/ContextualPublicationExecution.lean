import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublicationScope
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionEndpoints

/-!
# Reusable and shared output metadata in the same actual firing result

The actual worklist return supplies the solved value for reusable storage.
Live outputs retain the existing source inclusion, preserving their original
shared reference identities. Only the output metadata differs from the shared
profile: the original admission, occurrence commit, equations, retained
roots and fresh-scope ledger remain those of the existing execution owner.
No intermediate publication transition is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublication

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualScopeSupport ContextualWorldScopeLedger ContextualFrameUpdate

variable {S : Signature} {Local : Type} {O : Type} [DecidableEq O] [DecidableEq Local]
    (locals : Local → MetaArity S) {Γ : Ctx S} {sort : S.Srt}

def replaceOutputs {V Shared : Type} (declaration : V → MetaArity S)
    (captures : Shared → MetaArity S) (selection : Selection O) (reusable : O → Bool)
    (values : O → Term (signature S declaration) Γ sort)
    (inventory : Inventory locals captures (O := O) Γ sort) :
    Inventory (privateFamily locals declaration) captures (O := O) Γ sort :=
  { extendInventory locals declaration captures inventory with
    rows := fun occurrence => if occurrence ∈ selection.made ∧ reusable occurrence = true
      then ordinary locals declaration (values occurrence)
      else extendPrivate locals declaration (inventory.rows occurrence) }

omit [DecidableEq Local] in
theorem replaceOutputs_covered {V Shared : Type} (declaration : V → MetaArity S)
    (captures : Shared → MetaArity S) (selection : Selection O) (reusable : O → Bool)
    (values : O → Term (signature S declaration) Γ sort)
    (scopes : Shared → Finset Nat) (occupied : Finset Nat)
    (inventory : Inventory locals captures (O := O) Γ sort)
    (covered : CoveredWorld locals captures scopes occupied inventory) :
    CoveredWorld (privateFamily locals declaration) captures scopes occupied
      (replaceOutputs locals declaration captures selection reusable values inventory) := by
  have extended := extendInventory_covered locals declaration captures scopes inventory covered
  refine ⟨extended.equations,?_,extended.retained,extended.templates⟩
  intro occurrence present
  dsimp only [replaceOutputs]
  split
  · exact Finset.Subset.trans (ordinary_covered locals declaration captures scopes (values occurrence))
      (Finset.empty_subset _)
  · exact extended.rows occurrence present

def completedTarget (before : ContextualExecution.Endpoint locals O Γ sort)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort))
    (selection : Selection O)
    (outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort)
    (reusable : O → Bool)
    (ruleCovered : RuleCovered (privateScopes before.scopes) before.occupied rule)
    (admitted : ContextualGuardedStep.Requirements locals before.declarations before.occupied
      selection rule before.inventory.rows before.inventory.configuration outputs)
    (update : Update (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals before.declarations before.occupied selection rule
        before.inventory.rows before.inventory.configuration))) :
    ContextualExecution.Endpoint (privateFamily locals update.declaration) O Γ sort :=
  let sharedTarget := ContextualExecution.computedTarget locals before rule selection outputs ruleCovered admitted update
  { Names := sharedTarget.Names
    equality := sharedTarget.equality
    declarations := sharedTarget.declarations
    scopes := sharedTarget.scopes
    occupied := sharedTarget.occupied
    inventory := replaceOutputs locals update.declaration sharedTarget.declarations selection reusable
      (fun occurrence => instantiate update.answer (outputs occurrence)) sharedTarget.inventory
    covered := replaceOutputs_covered locals update.declaration sharedTarget.declarations selection reusable
      (fun occurrence => instantiate update.answer (outputs occurrence)) sharedTarget.scopes sharedTarget.occupied
      sharedTarget.inventory sharedTarget.covered }

variable {locals} {before : ContextualExecution.Endpoint locals O Γ sort}
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

structure Firing where
  sourceTarget : ContextualExecution.Endpoint locals O Γ sort
  execution : ContextualExecution.Firing locals before sourceTarget
  reusable : O → Bool

namespace Firing

abbrev rule (firing : Firing (before := before)) := firing.execution.rule
abbrev ruleCovered (firing : Firing (before := before)) := firing.execution.ruleCovered
abbrev selection (firing : Firing (before := before)) := firing.execution.selection
abbrev outputs (firing : Firing (before := before)) := firing.execution.outputs
abbrev update (firing : Firing (before := before)) := firing.execution.update
abbrev admitted (firing : Firing (before := before)) := firing.execution.admitted

def target (firing : Firing (before := before)) :=
  completedTarget locals before firing.rule firing.selection firing.outputs firing.reusable
    firing.ruleCovered firing.admitted firing.update

theorem physical_result (firing : Firing (before := before)) :
    firing.target.inventory.configuration.present =
      MeTTaCalculus.OccurrenceCommits.fire before.inventory.configuration.present
        (firing.selection.commit (T := Unit)) := rfl

theorem native_equations (firing : Firing (before := before)) :
    firing.target.inventory.configuration.equations =
      (ContextualTransportedActivation.result locals before.declarations
        (ContextualComputedFreshFrame.includeSource firing.update) before.occupied firing.selection firing.rule
        before.inventory.rows before.inventory.configuration).equations := rfl

theorem ordinary_row (firing : Firing (before := before)) {occurrence : O}
    (made : occurrence ∈ firing.selection.made) (reusable : firing.reusable occurrence = true) :
    firing.target.inventory.rows occurrence =
      ordinary locals firing.update.declaration (instantiate firing.update.answer (firing.outputs occurrence)) := by
  dsimp only [target,completedTarget,replaceOutputs]
  rw [if_pos ⟨made,reusable⟩]

theorem retained_row (firing : Firing (before := before)) {occurrence : O}
    (notMade : occurrence ∉ firing.selection.made) :
    firing.target.inventory.rows occurrence = extendPrivate locals firing.update.declaration
      ((ContextualExecution.computedTarget locals before firing.rule firing.selection firing.outputs
        firing.ruleCovered firing.admitted firing.update).inventory.rows occurrence) := by
  dsimp only [target,completedTarget,replaceOutputs]
  rw [if_neg (fun both => notMade both.1)]

theorem shared_row (firing : Firing (before := before)) {occurrence : O}
    (made : occurrence ∈ firing.selection.made) (isShared : firing.reusable occurrence = false) :
    firing.target.inventory.rows occurrence = ContextualStoredRows.Row.shared
      (instantiate (ContextualComputedFreshFrame.includeSource firing.update) (firing.outputs occurrence)) := by
  dsimp only [target,completedTarget,replaceOutputs]
  rw [if_neg (by simp [isShared])]
  change extendPrivate locals firing.update.declaration
    (ContextualTransportedActivation.resultRows locals before.declarations
      (ContextualComputedFreshFrame.includeSource firing.update) firing.selection firing.outputs
      before.inventory.rows occurrence) = _
  simp only [ContextualTransportedActivation.resultRows,ContextualActivatedStep.resultRows,made,ite_true,
    ContextualStoredRows.Row.map,extendPrivate]

theorem ordinary_matches_source (firing : Firing (before := before)) {occurrence : O}
    (made : occurrence ∈ firing.selection.made) (reusable : firing.reusable occurrence = true)
    {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    ContextualGuardMatching.Matches (privateFamily locals firing.update.declaration) candidate pattern
        (firing.target.inventory.rows occurrence) ↔
      SourceInstances (ContextualResidual.observeProblem
        (ContextualActivatedStep.problem locals before.declarations before.occupied firing.selection firing.rule
          before.inventory.rows before.inventory.configuration)) (firing.outputs occurrence) next pattern := by
  rw [firing.ordinary_row made reusable]
  exact completed_ordinary_matches_iff locals firing.update firing.execution.empty candidate _ pattern

end Firing

variable (locals)

/-- The same admitted solver execution constructs the publication result;
there is no public shared-output state followed by a metadata rewrite. -/
theorem realize_publication
    (before : ContextualExecution.Endpoint locals O Γ sort)
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort))
    (selection : Selection O)
    (outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort)
    (reusable : O → Bool)
    (ruleCovered : RuleCovered (privateScopes before.scopes) before.occupied rule)
    (admitted : ContextualGuardedStep.Valid locals before.declarations before.occupied
      selection rule before.inventory.rows before.inventory.configuration outputs)
    (patterned : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals before.declarations before.occupied selection rule
        before.inventory.rows before.inventory.configuration))) :
    ∃ firing : Firing (before := before), firing.rule = rule ∧ firing.selection = selection ∧
      firing.outputs = outputs ∧ firing.reusable = reusable := by
  obtain ⟨after,execution,ruleEq,selectionEq,outputsEq⟩ :=
    ContextualExecution.realize_semantic_admission locals before rule selection outputs ruleCovered admitted patterned
  exact ⟨⟨after,execution,reusable⟩,ruleEq,selectionEq,outputsEq,rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublication
