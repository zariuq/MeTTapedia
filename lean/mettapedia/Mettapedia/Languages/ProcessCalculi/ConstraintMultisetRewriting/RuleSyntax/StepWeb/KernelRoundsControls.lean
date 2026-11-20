import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRoundsDepth
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRoundsFinite
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStorePathControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreGrowthControls

/-!
# Round-depth controls on an actual six-rule ground program

The finite presentation below covers all ground instances of the existing
three-edge path program. Thus its computed stages test the actual consequence
adapter, not a separate toy transition system. The constructor-growth control
records why finite input and a finite program do not suffice for termination.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRounds.Examples

open Mettapedia.Logic.LP
open OneFrame (Terms)
open SetStoreSyntax
open SetStorePathControls
open SetStoreOpenControls (c)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms)

def finiteConsequences (i : Fin 6) : SetStoreClosure.Instance (Term atoms) := consequence (matchAt i)

theorem all_ground_instances_covered (match_ : GroundMatch program) :
    ∃ i, consequence match_ = finiteConsequences i := by
  obtain ⟨i, same⟩ := match_.member
  refine ⟨i, ?_⟩
  unfold consequence finiteConsequences
  rw [← same]
  fin_cases i <;> simp [consequence, matchAt, ruleAt, ports, c, Subst.applyTerm]

theorem actual_stages_are_finite (n : Nat) :
    stage (consequence (P := program)) (seed : Set (Term atoms)) n =
      (finiteStage finiteConsequences seed n : Set (Term atoms)) :=
  (stage_eq_of_instance_cover _ finiteConsequences all_ground_instances_covered
    (fun i => ⟨matchAt i, rfl⟩) (seed : Set (Term atoms)) n).trans
      (coe_finiteStage finiteConsequences seed n).symm

theorem path_stage_trace : (List.range 4).map (finiteStage finiteConsequences seed) =
    [rows {0, 1, 2}, rows {0, 1, 2, 3, 4, 5}, rows {0, 1, 2, 3, 4, 5, 6, 7}, paths] := by
  decide +kernel

theorem path_stage_three : stage (consequence (P := program)) (seed : Set (Term atoms)) 3 =
    (paths : Set (Term atoms)) := by
  rw [actual_stages_are_finite]
  exact congrArg (fun rs : Finset (Term atoms) => (rs : Set (Term atoms))) (by decide +kernel)

theorem final_path_not_at_stage_two :
    c 8 ∉ stage (consequence (P := program)) (seed : Set (Term atoms)) 2 := by
  rw [actual_stages_are_finite]
  decide +kernel

theorem path_closure_finite : (SetStoreClosure.closure (consequence (P := program)) seed).Finite := by
  rw [← paths_least]
  exact Finset.finite_toSet _

theorem path_depth_three : closureDepth (consequence (P := program)) seed path_closure_finite = 3 := by
  have upper := (closureDepth_le_iff _ _ path_closure_finite 3).mpr (path_stage_three.trans paths_least)
  have notEarlier : ¬ closureDepth (consequence (P := program)) seed path_closure_finite ≤ 2 := by
    intro early
    have full := (closureDepth_le_iff _ _ path_closure_finite 2).mp early
    have member : c 8 ∈ SetStoreClosure.closure (consequence (P := program)) seed := by
      rw [← paths_least]
      decide +kernel
    exact final_path_not_at_stage_two (full.symm ▸ member)
  omega

theorem finite_input_does_not_imply_finite_closure :
    ¬ ∃ carrier : Finset (Term SetStoreGrowthControls.signature),
      SetStoreGrowthControls.tower 0 ∈ carrier ∧
        SetStoreClosure.Closed (consequence (P := SetStoreGrowthControls.program)) carrier := by
  rintro ⟨carrier, seedInside, closed⟩
  exact SetStoreGrowthControls.finite_input_no_closed_carrier carrier seedInside closed

#print axioms all_ground_instances_covered
#print axioms path_stage_trace
#print axioms path_depth_three
#print axioms finite_input_does_not_imply_finite_closure

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRounds.Examples
