import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseFrames

/-!
# A resolved clause's joint source problem is the actual firing problem

Takes and reads open each stored occurrence independently, while all ports
and body equations retain one query assignment. Source row-use names and
actor variables are distinct before compilation. Native preparation embeds
the complete source problem into the current allocated declaration frame.
This includes body equations and preserves the original caller equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseProblem

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualClauseFrames

variable {S : Signature} {Query Local Shared O : Type}
    (queries : Query → MetaArity S) (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    {Γ : Ctx S} {sort : S.Srt}

def nativeRule (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort)) :=
  code.map (instantiate (actor queries locals captures))

def nativeRows (rows : O → ContextualStoredRows.Row locals captures Γ sort) :=
  fun occurrence => ContextualPublication.extendPrivate locals queries (rows occurrence)

def takeViews (selection : Selection O) (rows : O → ContextualStoredRows.Row locals captures Γ sort) :=
  List.ofFn fun port : Fin selection.taken.length =>
    instantiate (rowEmbedding queries locals captures)
      (ContextualStoredRows.viewAt locals captures (port.val + 2) (rows (selection.taken.get port)))

def readViews (selection : Selection O) (rows : O → ContextualStoredRows.Row locals captures Γ sort) :=
  List.ofFn fun port : Fin selection.read.length =>
    instantiate (rowEmbedding queries locals captures)
      (ContextualStoredRows.viewAt locals captures (selection.taken.length + port.val + 2)
        (rows (selection.read.get port)))

def problem (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) :=
  ContextualFrameUnifier.mapProblem (captureEmbedding queries locals captures) before.equations ++
    ContextualActivatedStep.useEquations (code.take.map (queryView queries locals captures)) (takeViews queries locals captures selection rows) ++
    ContextualActivatedStep.useEquations (code.read.map (queryView queries locals captures)) (readViews queries locals captures selection rows) ++
    ContextualFrameUnifier.mapProblem (queryEmbedding queries locals captures) code.tell

private theorem rule_map_comp {T U V : Type} (first : T → U) (second : U → V) (rule : RuleInstance T) :
    (rule.map first).map second = rule.map (second ∘ first) := by
  cases rule
  simp only [RuleInstance.map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro check _
  cases check <;> rfl

theorem prepared_rule (occupied : Finset Nat) (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) :
    (ContextualActivatedStep.prepared (bank queries locals) captures occupied selection
      (nativeRule queries locals captures code) (nativeRows queries locals captures rows)).rule =
    (code.map (queryView queries locals captures)).map (instantiate (frame queries locals captures occupied).assignment) := by
  change ((code.map (instantiate (actor queries locals captures))).map
      (ContextualFreshening.termAt (bank queries locals) captures
        (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort selection)))) = _
  rw [rule_map_comp, rule_map_comp]
  apply congrArg (fun operation => code.map operation)
  funext value
  exact (query_term queries locals captures occupied value).symm

theorem prepared_takes (occupied : Finset Nat) (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) :
    List.ofFn (ContextualActivatedStep.prepared (bank queries locals) captures occupied selection
      (nativeRule queries locals captures code) (nativeRows queries locals captures rows)).taken =
    (takeViews queries locals captures selection rows).map (instantiate (frame queries locals captures occupied).assignment) := by
  unfold takeViews
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext port
  rw [ContextualActivatedStep.prepared_taken_view]
  have shifted : occupied.sup id + (port.val + 2) = ContextualActivationScopes.scopeAt occupied
      (ContextualActivationScopes.takePort selection port) := by
    simp only [ContextualActivationScopes.scopeAt, ContextualActivationScopes.start, ContextualActivationScopes.takePort]
    omega
  exact (row_term queries locals captures occupied (port.val + 2) (rows (selection.taken.get port))).trans
    (congrArg (fun scope => ContextualStoredRows.viewAt (bank queries locals) captures scope
      (ContextualPublication.extendPrivate locals queries (rows (selection.taken.get port)))) shifted) |>.symm

theorem prepared_reads (occupied : Finset Nat) (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) :
    List.ofFn (ContextualActivatedStep.prepared (bank queries locals) captures occupied selection
      (nativeRule queries locals captures code) (nativeRows queries locals captures rows)).read =
    (readViews queries locals captures selection rows).map (instantiate (frame queries locals captures occupied).assignment) := by
  unfold readViews
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext port
  rw [ContextualActivatedStep.prepared_read_view]
  have shifted : occupied.sup id + (selection.taken.length + port.val + 2) = ContextualActivationScopes.scopeAt occupied
      (ContextualActivationScopes.readPort selection port) := by
    simp only [ContextualActivationScopes.scopeAt, ContextualActivationScopes.start, ContextualActivationScopes.readPort]
    omega
  exact (row_term queries locals captures occupied (selection.taken.length + port.val + 2)
    (rows (selection.read.get port))).trans
    (congrArg (fun scope => ContextualStoredRows.viewAt (bank queries locals) captures scope
      (ContextualPublication.extendPrivate locals queries (rows (selection.read.get port)))) shifted) |>.symm

/-- The independently scoped source problem, including its body equations,
is retained whole in the actual native activation. -/
theorem actual_problem (occupied : Finset Nat) (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    ContextualActivatedStep.problem (bank queries locals) captures occupied selection (nativeRule queries locals captures code)
      (nativeRows queries locals captures rows) before =
    ContextualFrameUnifier.mapProblem (frame queries locals captures occupied).assignment
      (problem queries locals captures selection code rows before) := by
  rw [ContextualActivatedStep.problem, prepared_rule, prepared_takes, prepared_reads]
  simp only [RuleInstance.map]
  unfold problem
  rw [ContextualTransportedActivation.map_append, ContextualTransportedActivation.map_append,
    ContextualTransportedActivation.map_append, ContextualComputedFreshFrame.map_compose, captures_square,
    ContextualTransportedActivation.map_useEquations, ContextualTransportedActivation.map_useEquations]
  rfl

theorem solvable_iff (occupied : Finset Nat) (selection : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    ContextualFrameUnifier.Solvable (ContextualActivatedStep.problem (bank queries locals) captures occupied selection
      (nativeRule queries locals captures code) (nativeRows queries locals captures rows) before) ↔
    ContextualFrameUnifier.Solvable (problem queries locals captures selection code rows before) := by
  rw [actual_problem]
  exact (frame queries locals captures occupied).exists_model_iff _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseProblem
