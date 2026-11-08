import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixPublicationControls

/-!
# Later equations cannot discharge an earlier nonbinding check

The caller is initially free. A check that it already equals 1 is not
entailed at that cut. A later binding to 1 makes the naive final-cut check
true, whereas the isolated prefix check retains the original countermodel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixGuardControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows
open ContextualPrefixPublicationControls

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq DataOperator)

def rows (_ : Nat) : Row none captures [] () := ofStored none captures (.shared (symbol 0))
def savedCheck : Check (Term (signature base captures) [] ()) := .equal (generator captures ()) (symbol 1)

theorem the_original_check_has_a_countermodel :
    ¬ ContextualConditionalGuards.Ask none [] rows ∅ savedCheck := by
  intro asked
  have same := asked Empty none (fun _ => symbol 2) (by intro equation member; cases member)
  change symbol (decl := none) 2 = symbol 1 at same
  have impossible : (2 : Nat) = 1 := DataOperator.symbol.inj (Sum.inl.inj (Term.op.inj same).1)
  omega

theorem the_later_binding_entails_the_naive_check :
    ContextualConditionalGuards.Ask none ambientProblem rows ∅ savedCheck := by
  intro Future future candidate model
  change ContextualResidual.Models candidate [(observe (generator captures ()), observe (symbol 1))] at model
  rw [ContextualResidual.models_observed_iff] at model
  exact model

theorem isolation_retains_the_original_countermodel :
    ¬ ContextualConditionalGuards.Ask none
      (ContextualPrefixIsolation.problem captures captures [] ambientProblem)
      (fun occurrence => (rows occurrence).map none captures (ContextualStoredRows.privateSource captures captures)) ∅
      (savedCheck.map (instantiate (ContextualStoredRows.privateSource captures captures))) := by
  intro asked
  exact the_original_check_has_a_countermodel
    ((ContextualPrefixIsolation.asks_iff captures captures none [] ambientProblem ambient_consistent rows ∅ savedCheck).mp asked)

def naiveCode : RuleInstance (Term (signature base actor) [] ()) :=
  { ContextualPrefixPublicationControls.naiveCode with checks := [.equal callerX (symbol 1)] }
def naivePlan : ContextualPublication.Plan (Term (signature base actor) [] ()) := ⟨naiveCode, [true], rfl⟩

theorem naive_final_cut_accepts : ContextualClauseSourceState.Admitted none none initial naivePlan firstSelection := by
  refine ⟨naive_admitted.take_distinct, naive_admitted.output_distinct, naive_admitted.take_shape,
    naive_admitted.read_shape, naive_admitted.output_shape, naive_admitted.taken_present,
    naive_admitted.read_present, naive_admitted.apart, naive_admitted.fresh, naive_admitted.solvable, ?_⟩
  intro check member
  have only := List.mem_singleton.mp member
  subst check
  intro Future future candidate model
  change ContextualResidual.Models candidate
    (ContextualClauseSourceState.information none none initial ContextualPrefixPublicationControls.naivePlan firstSelection) at model
  erw [naive_information, ContextualResidual.models_observed_iff] at model
  exact model

def isolatedCode : RuleInstance (Term (signature base copiedActor) [] ()) :=
  { copiedCode with checks := [.equal savedX (symbol 1)] }
def isolatedPlan : ContextualPublication.Plan (Term (signature base copiedActor) [] ()) := ⟨isolatedCode, [true], rfl⟩

theorem an_isolated_earlier_check_is_not_repaired_by_the_later_binding :
    ¬ ContextualClauseSourceState.Admitted copiedQueries none initial isolatedPlan firstSelection := by
  intro admitted
  have asked := admitted.checks (.equal savedX (symbol 1)) (List.mem_singleton_self _)
  have same := asked Empty none (copiedModel none 2) (copied_model_valid none 2)
  change symbol (decl := none) 2 = symbol 1 at same
  have impossible : (2 : Nat) = 1 := DataOperator.symbol.inj (Sum.inl.inj (Term.op.inj same).1)
  omega

theorem an_actual_firing_cannot_discard_that_countermodel :
    ¬ Nonempty (ContextualConditionalClauses.Compiled copiedQueries none (before := initial.native ∅)
      isolatedPlan firstSelection) := by
  rintro ⟨compiled⟩
  exact an_isolated_earlier_check_is_not_repaired_by_the_later_binding compiled.source_admitted

theorem the_naive_final_cut_has_an_actual_firing (fuel : Nat) :
    ∃ compiled : ContextualConditionalClauses.Compiled none none (before := initial.native ∅)
      naivePlan firstSelection, compiled.firing.fuel = fuel :=
  ContextualConditionalClauses.realize none none (before := initial.native ∅) naivePlan firstSelection naive_final_cut_accepts fuel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixGuardControls
