import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternTermination

/-!
# Complete symbolic answers of a finite contextual source query

Every physical read tuple is constructed from the observed domain. Each tuple
opens its stored schemas in separate port scopes and has its own actual
solver run. A complete return contains either a certified refusal or an
empty-queue principal answer. The answers are not conjoined: incompatible
alternatives retain their separate substitutions and caller constraints.

The table is finite in occurrence tuples, not in ground instances. A single
schematic answer can represent infinitely many later instances. Its exact
factorization preserves every contextual variable, including caller captures
and variables in object-binder spines. No finiteness of all higher-order
solutions or arbitrary higher-order solver completeness is assumed.

The accepting check examines every constructed candidate. Insufficient fuel
and unresolved equations leave it incomplete. On structural-pattern inputs,
the existing driver proves that finite per-tuple budgets suffice. This is a
query observation at the specified problem and row cut; promoting it to a
different cut requires retaining that dependency.

This is a finite reference census. Its exact source-match characterization
is the refinement contract for indexed or factored enumerators; the theorem
does not prescribe materializing a Cartesian product in a native runtime.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualQueryAnswers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualGuardMatching
open ContextualConjunctiveQueries
open ContextualConjunctiveModels (caller joint_model_gives_caller_and_match)

universe u
variable {S : Signature} {Query Local Shared : Type} {O : Type u}
  (queries : Query → MetaArity S) (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

def problemAt {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (chosen : Fin patterns.length → O) :=
  ContextualResidual.observeProblem (joint queries locals captures problem patterns rows chosen)

def closed {V : Type} {source : V → MetaArity S} {problem : ContextualResidual.Problem source} :
    ContextualFrameWorklist.Result problem → Bool
  | .refuted _ => true
  | .residual update => update.remaining.isEmpty

def successful {V : Type} {source : V → MetaArity S} {problem : ContextualResidual.Problem source} :
    ContextualFrameWorklist.Result problem → Bool
  | .refuted _ => false
  | .residual update => update.remaining.isEmpty

variable [DecidableEq Query] [DecidableEq Local] [DecidableEq Shared] [DecidableEq S.Srt]
  [∀ sort, DecidableEq (S.Op sort)]

def scan {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (budget : (Fin patterns.length → O) → Nat) (chosen : Fin patterns.length → O) :=
  ContextualFrameWorklist.run (budget chosen) (family queries locals captures)
    (problemAt queries locals captures problem patterns rows chosen)

def certifies [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (budget : (Fin patterns.length → O) → Nat) : Bool :=
  decide (∀ chosen ∈ ContextualConjunctiveAbsence.candidates world patterns.length,
    closed (scan queries locals captures problem patterns rows budget chosen) = true)

def answers [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (budget : (Fin patterns.length → O) → Nat) : Finset (Fin patterns.length → O) :=
  (ContextualConjunctiveAbsence.candidates world patterns.length).filter fun chosen =>
    successful (scan queries locals captures problem patterns rows budget chosen) = true

theorem actual_answer_iff [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (budget : (Fin patterns.length → O) → Nat)
    (accepted : certifies queries locals captures problem patterns rows world budget = true)
    (chosen : Fin patterns.length → O) :
    chosen ∈ answers queries locals captures problem patterns rows world budget ↔
      (∀ port, chosen port ∈ world) ∧
        ∃ (Next : Type) (next : Next → MetaArity S)
          (candidate : Assignment captures next),
          ContextualFrameUnifier.Models candidate problem ∧
            ContextualConjunctiveQueries.Matches queries locals captures candidate patterns rows chosen := by
  have finished := of_decide_eq_true accepted
  simp only [answers, Finset.mem_filter, ContextualConjunctiveAbsence.mem_candidates]
  constructor
  · rintro ⟨present, success⟩
    cases computed : scan queries locals captures problem patterns rows budget chosen with
    | refuted impossible => simp only [computed, successful, Bool.false_eq_true] at success
    | residual update =>
        have empty : update.remaining = [] := List.isEmpty_iff.mp (by simpa only [computed, successful] using success)
        have solved := (ContextualResidual.models_observeProblem update.answer _).mp (update.completed empty)
        obtain ⟨old, matched⟩ := joint_model_gives_caller_and_match queries locals captures update.answer problem patterns rows chosen solved
        exact ⟨present, update.Variables, update.declaration,
          caller queries locals captures update.answer, old, matched⟩
  · rintro ⟨present, Next, next, candidate, solved, matched⟩
    refine ⟨present, ?_⟩
    obtain ⟨Later, later, combined, jointModel⟩ :=
      match_gives_joint_model queries locals captures candidate problem patterns rows chosen solved matched
    have model := (ContextualResidual.models_observeProblem combined _).mpr jointModel
    have complete := finished chosen ((ContextualConjunctiveAbsence.mem_candidates world chosen).mpr present)
    cases computed : scan queries locals captures problem patterns rows budget chosen with
    | refuted impossible => exact False.elim (impossible later combined model)
    | residual update => simpa only [computed, closed, successful] using complete

/-- Every original future-family solution of a recorded tuple factors
through its actual returned answer. No query alternative or caller binding
is discarded by selecting one ground model. -/
theorem answer_factors [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (budget : (Fin patterns.length → O) → Nat) (chosen : Fin patterns.length → O)
    (recorded : chosen ∈ answers queries locals captures problem patterns rows world budget) :
    ∃ update : ContextualFrameUpdate.Update (problemAt queries locals captures problem patterns rows chosen),
      scan queries locals captures problem patterns rows budget chosen = .residual update ∧
      update.remaining = [] ∧
      ∀ (Next : Type) (next : Next → MetaArity S)
        (candidate : Assignment (family queries locals captures) next),
        ContextualResidual.Models candidate (problemAt queries locals captures problem patterns rows chosen) ↔
          ∃ residual : Assignment update.declaration next,
            ∀ identity, candidate identity = instantiate residual (update.answer identity) := by
  have success := (Finset.mem_filter.mp recorded).2
  cases computed : scan queries locals captures problem patterns rows budget chosen with
  | refuted impossible => simp only [computed, successful, Bool.false_eq_true] at success
  | residual update =>
      have empty : update.remaining = [] := List.isEmpty_iff.mp (by simpa only [computed, successful] using success)
      exact ⟨update, rfl, empty, fun _ next candidate => update.completed_models_iff empty next candidate⟩

/-- Structural-pattern queries have a complete finite table without a
supplied model or successful solver return. Each job can have its own budget. -/
theorem complete_budgets_exist [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (patterned : ∀ chosen ∈ ContextualConjunctiveAbsence.candidates world patterns.length,
      ContextualPatternFragment.ProblemPattern (problemAt queries locals captures problem patterns rows chosen)) :
    ∃ budget, certifies queries locals captures problem patterns rows world budget = true := by
  classical
  have each : ∀ chosen ∈ ContextualConjunctiveAbsence.candidates world patterns.length,
      ∃ fuel, closed (ContextualFrameWorklist.run fuel (family queries locals captures)
        (problemAt queries locals captures problem patterns rows chosen)) = true := by
    intro chosen present
    obtain ⟨fuel, finished⟩ := ContextualPatternTermination.finishes
      (problemAt queries locals captures problem patterns rows chosen) (patterned chosen present)
    refine ⟨fuel, ?_⟩
    generalize computed : ContextualFrameWorklist.run fuel (family queries locals captures)
      (problemAt queries locals captures problem patterns rows chosen) = result at finished ⊢
    cases finished with
    | refuted impossible => rfl
    | solved update empty => simp only [closed, empty, List.isEmpty_nil]
  let budget := fun chosen => if present : chosen ∈ ContextualConjunctiveAbsence.candidates world patterns.length
    then Classical.choose (each chosen present) else 0
  refine ⟨budget, ?_⟩
  apply decide_eq_true
  intro chosen present
  simpa only [scan, budget, dif_pos present] using Classical.choose_spec (each chosen present)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualQueryAnswers
