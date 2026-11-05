import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalNaturality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalScopes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseAdmission

/-!
# Independent source clauses retain conditions from earlier publications

Source query variables and each row use have separate identities before
native allocation. The joint source problem contains incoming heterogeneous
equations, the existing source pattern/body equations and each selected
row's latent conditions. Compilation embeds that complete problem into the
actual native activation; no stored-row conditions are replaced by a flag.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalSourceProblem

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualClauseFrames ContextualGuardMatching
open ContextualConditionalRows ContextualConditionalNaturality

variable {S : Signature} {Query Local Shared O : Type}
    (queries : Query → MetaArity S) (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    {Γ : Ctx S} {sort : S.Srt}

def nativeRows (rows : O → Row locals captures Γ sort) :=
  fun occurrence => ContextualConditionalPublication.extendPrivate locals queries captures (rows occurrence)

theorem native_values (rows : O → Row locals captures Γ sort) :
    (fun occurrence => (nativeRows queries locals captures rows occurrence).value) =
      ContextualClauseProblem.nativeRows queries locals captures (fun occurrence => (rows occurrence).value) := rfl

def prepareState (before : ContextualConditionalExecution.State locals O Γ sort) :
    ContextualConditionalExecution.State (bank queries locals) O Γ sort where
  Names := before.Names
  equality := before.equality
  declarations := before.declarations
  occupied := before.occupied
  equations := before.equations
  present := before.present
  rows := nativeRows queries locals before.declarations before.rows

theorem prepare_formed (before : ContextualConditionalExecution.State locals O Γ sort)
    (scopes : before.Names → Finset Nat) (formed : ContextualConditionalScopes.Formed locals before scopes) :
    ContextualConditionalScopes.Formed (bank queries locals) (prepareState queries locals before) scopes := by
  refine ⟨formed.equations, ?_⟩
  intro occurrence present
  exact ContextualConditionalScopes.row_extendPrivate locals before.declarations queries scopes before.occupied
    (formed.rows occurrence present)

def bindingEquations (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) :=
  ContextualClauseProblem.problem queries locals captures selection code
    (fun occurrence => (rows occurrence).value) ⟨[], ∅⟩

def latent (selection : Selection O) (rows : O → Row locals captures Γ sort) :
    ContextualResidual.Problem (family queries locals captures) :=
  (List.ofFn fun port : Fin selection.taken.length =>
    ContextualResidual.mapProblem (rowEmbedding queries locals captures)
      ((rows (selection.taken.get port)).obligationsAt locals captures (port.val + 2))).flatten ++
  (List.ofFn fun port : Fin selection.read.length =>
    ContextualResidual.mapProblem (rowEmbedding queries locals captures)
      ((rows (selection.read.get port)).obligationsAt locals captures (selection.taken.length + port.val + 2))).flatten

def problem (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) (before : ContextualResidual.Problem captures) :
    ContextualResidual.Problem (family queries locals captures) :=
  ContextualResidual.mapProblem (captureEmbedding queries locals captures) before ++
    ContextualResidual.observeProblem (bindingEquations queries locals captures selection code rows) ++
    latent queries locals captures selection rows

theorem row_conditions (occupied : Finset Nat) (scope : Nat) (row : Row locals captures Γ sort) :
    ContextualResidual.mapProblem (frame queries locals captures occupied).assignment
      (ContextualResidual.mapProblem (rowEmbedding queries locals captures)
        (row.obligationsAt locals captures scope)) =
    (ContextualConditionalPublication.extendPrivate locals queries captures row).obligationsAt
      (bank queries locals) captures (occupied.sup id + scope) := by
  change ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _
    (ContextualResidual.mapProblem _ row.obligations)) =
      ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ row.obligations)
  simp only [map_problem_compose]
  rw [row_square]

theorem latent_embeds (occupied : Finset Nat) (selection : Selection O) (rows : O → Row locals captures Γ sort) :
    ContextualResidual.mapProblem (frame queries locals captures occupied).assignment
      (latent queries locals captures selection rows) =
    ContextualConditionalExecution.latent (bank queries locals) captures occupied selection
      (nativeRows queries locals captures rows) := by
  simp only [latent, ContextualConditionalExecution.latent, ContextualResidual.mapProblem, List.map_append,
    List.map_flatten, List.map_ofFn]
  congr 1
  · apply congrArg List.flatten
    apply congrArg List.ofFn
    funext port
    have shifted : occupied.sup id + (port.val + 2) =
        ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.takePort selection port) := by
      simp only [ContextualActivationScopes.scopeAt, ContextualActivationScopes.start, ContextualActivationScopes.takePort]
      omega
    exact (row_conditions queries locals captures occupied (port.val + 2) (rows (selection.taken.get port))).trans
      (congrArg (fun scope => (nativeRows queries locals captures rows (selection.taken.get port)).obligationsAt
        (bank queries locals) captures scope) shifted)
  · apply congrArg List.flatten
    apply congrArg List.ofFn
    funext port
    have shifted : occupied.sup id + (selection.taken.length + port.val + 2) =
        ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.readPort selection port) := by
      simp only [ContextualActivationScopes.scopeAt, ContextualActivationScopes.start, ContextualActivationScopes.readPort]
      omega
    exact (row_conditions queries locals captures occupied (selection.taken.length + port.val + 2)
      (rows (selection.read.get port))).trans
      (congrArg (fun scope => (nativeRows queries locals captures rows (selection.read.get port)).obligationsAt
        (bank queries locals) captures scope) shifted)

/-- The independently indexed source problem maps to the actual complete
native information problem, including constraints from earlier results. -/
theorem actual_information (occupied : Finset Nat) (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) (before : ContextualResidual.Problem captures) :
    ContextualConditionalExecution.information (bank queries locals) captures occupied selection
      (ContextualClauseProblem.nativeRule queries locals captures code) (nativeRows queries locals captures rows) before =
    ContextualResidual.mapProblem (frame queries locals captures occupied).assignment
      (problem queries locals captures selection code rows before) := by
  have binding := ContextualClauseProblem.actual_problem queries locals captures occupied selection code
    (fun occurrence => (rows occurrence).value) (⟨[], ∅⟩ : Configuration (Term (signature S captures) Γ sort) O)
  rw [ContextualActivatedStep.problem_eq_frame_append] at binding
  have added : ContextualActivatedStep.addedEquations (bank queries locals) captures occupied selection
      (ContextualClauseProblem.nativeRule queries locals captures code)
      (fun occurrence => (nativeRows queries locals captures rows occurrence).value) =
    ContextualFrameUnifier.mapProblem (frame queries locals captures occupied).assignment
      (bindingEquations queries locals captures selection code rows) := by
    rw [native_values]
    simpa only [ContextualActivatedStep.frame, ContextualFrameUnifier.mapProblem, List.map_nil, List.nil_append,
      bindingEquations] using binding
  rw [ContextualConditionalExecution.information, added, problem]
  simp only [ContextualResidual.mapProblem, List.map_append]
  change _ ++ _ ++ _ = ContextualResidual.mapProblem _ (ContextualResidual.mapProblem _ before) ++
    ContextualResidual.mapProblem _ (ContextualResidual.observeProblem (bindingEquations queries locals captures selection code rows)) ++
    ContextualResidual.mapProblem _ (latent queries locals captures selection rows)
  rw [map_problem_compose, captures_square, ← ContextualResidual.observeProblem_mapProblem, latent_embeds]
  rfl

theorem problem_ofStored (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    problem queries locals captures selection code (fun occurrence => ofStored locals captures (rows occurrence))
      (ContextualResidual.observeProblem before.equations) =
    ContextualResidual.observeProblem (ContextualClauseProblem.problem queries locals captures selection code rows before) := by
  simp only [problem, latent, Row.obligationsAt, ofStored, ContextualResidual.mapProblem, List.map_nil,
    List.ofFn_const, List.flatten_replicate_nil, List.append_nil]
  change ContextualResidual.mapProblem (captureEmbedding queries locals captures)
    (ContextualResidual.observeProblem before.equations) ++
      ContextualResidual.observeProblem (bindingEquations queries locals captures selection code
        (fun occurrence => ofStored locals captures (rows occurrence))) = _
  rw [← ContextualResidual.observeProblem_mapProblem]
  unfold ContextualResidual.observeProblem
  rw [← List.map_append]
  congr 1
  simp [bindingEquations, ContextualClauseProblem.problem, ContextualFrameUnifier.mapProblem, List.append_assoc]
  rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalSourceProblem
