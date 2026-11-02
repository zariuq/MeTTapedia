import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexive
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveSupport

/-!
# Reflexivity reduces the queue while preserving its remaining model

An identical equation contributes no constraint on an assignment. Dropping
it preserves the candidate itself, cannot enlarge active-image potential,
and strictly decreases the equation count. No fresh interface is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveProgress

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport

variable {S : Signature} {V Next : Type} [DecidableEq V]
  {source : V → MetaArity S} {next : Next → MetaArity S}

omit [DecidableEq V] in
theorem map_identity (problem : Problem source) : mapProblem (generator source) problem = problem := by
  induction problem with
  | nil => rfl
  | cons equation rest smaller =>
      simpa only [mapProblem, List.map_cons, instantiateObservation_identity] using
        congrArg (List.cons equation) smaller

theorem remaining_is_the_original_tail {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S source) Γ sort) (rest : Problem source) :
    ((ContextualReflexive.discharge term).keep_right rest).remaining = rest := by
  dsimp only [ContextualFrameUpdate.Update.keep_right, ContextualReflexive.discharge, List.nil_append]
  exact map_identity rest

theorem equation_count_decreases {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S source) Γ sort) (rest : Problem source) :
    ((ContextualReflexive.discharge term).keep_right rest).remaining.length <
      ((observe term, observe term) :: rest).length := by
  rw [remaining_is_the_original_tail (S := S) (source := source) term rest]
  exact Nat.lt_succ_self rest.length

theorem model_progress {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S source) Γ sort) (rest : Problem source)
    (candidate : Assignment source next)
    (solved : Models candidate ((observe term, observe term) :: rest)) :
    Models candidate ((ContextualReflexive.discharge term).keep_right rest).remaining ∧
      potential candidate (active ((ContextualReflexive.discharge term).keep_right rest).remaining) ≤
        potential candidate (active ((observe term, observe term) :: rest)) ∧
      ((ContextualReflexive.discharge term).keep_right rest).remaining.length <
        ((observe term, observe term) :: rest).length := by
  refine ⟨?_, ?_, equation_count_decreases term rest⟩
  · rw [remaining_is_the_original_tail]
    exact fun equation member => solved equation (List.mem_cons_of_mem _ member)
  · rw [remaining_is_the_original_tail]
    exact potential_monotone candidate (active_tail_subset _ rest)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveProgress
