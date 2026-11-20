import Mettapedia.GSLT.Core.OperationalColimitEquationSupport

/-!
# Common-stage witnesses for ambient reductions

The two equational ends of an ambient reduction and its authored step may
originate in different stages. The shared relation-witness construction
aligns them. The actual stage GSLT's equation-respect laws then give one
stage step with exactly the represented endpoints.

The witness may lie later than either endpoint's original stage. No step
reflection to an earlier stage or persistence of terminality is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational.OperationalColimits

open CategoryTheory

universe u

variable {J : Type u} [SmallCategory J]

abbrev HasStageReduction (diagram : J ⥤ OperationalTheory.{u})
    (left right : Term diagram) : Prop :=
  HasStageRelation diagram (fun stage => (diagram.obj stage).theory.Step) left right

private theorem step_of_equivalent_left (source : Mettapedia.GSLT.GSLT.{u})
    {left middle right : source.Term} (equivalent : source.Equiv left middle)
    (step : source.Step middle right) : source.Step left right := by
  obtain ⟨next, nextStep, nextEquation⟩ :=
    source.rewrites_resp_left (source.equations.iseqv.symm equivalent) step
  exact source.rewrites_resp_right nextStep (source.equations.iseqv.symm nextEquation)

variable [IsFilteredOrEmpty J]

private theorem stageReduction_equivalent_left (diagram : J ⥤ OperationalTheory.{u})
    {left middle right : Term diagram}
    (equivalent : HasStageEquation diagram left middle)
    (step : HasStageReduction diagram middle right) : HasStageReduction diagram left right :=
  stage_relations_compose diagram _ _ _
    (fun {_ _} route {_ _} equation => (diagram.map route).mapEquiv equation)
    (fun {_ _} route {_ _} step => (diagram.map route).mapStep step)
    (fun stage {_ _ _} equation step => step_of_equivalent_left (diagram.obj stage).theory equation step)
    equivalent step

private theorem stageReduction_equivalent_right (diagram : J ⥤ OperationalTheory.{u})
    {left middle right : Term diagram}
    (step : HasStageReduction diagram left middle)
    (equivalent : HasStageEquation diagram middle right) : HasStageReduction diagram left right :=
  stage_relations_compose diagram _ _ _
    (fun {_ _} route {_ _} step => (diagram.map route).mapStep step)
    (fun {_ _} route {_ _} equation => (diagram.map route).mapEquiv equation)
    (fun stage {_ _ _} step equation => (diagram.obj stage).theory.rewrites_resp_right step equation)
    step equivalent

theorem reduction_iff_has_stage_reduction (diagram : J ⥤ OperationalTheory.{u})
    {left right : Term diagram} :
    Reduction diagram left right ↔ HasStageReduction diagram left right := by
  constructor
  · rintro ⟨before, after, first, authored, last⟩
    have step : HasStageReduction diagram before after := by
      cases authored with
      | stage stage step => exact ⟨stage, _, _, rfl, rfl, step⟩
    exact stageReduction_equivalent_right diagram
      (stageReduction_equivalent_left diagram
        ((equivalent_iff_has_stage_equation diagram).mp first) step)
      ((equivalent_iff_has_stage_equation diagram).mp last)
  · rintro ⟨stage, before, after, first, last, step⟩
    rw [← first, ← last]
    exact ⟨_, _, .refl _, .stage stage step, .refl _⟩

#print axioms reduction_iff_has_stage_reduction

end Mettapedia.GSLT.IndexedOperational.OperationalColimits
