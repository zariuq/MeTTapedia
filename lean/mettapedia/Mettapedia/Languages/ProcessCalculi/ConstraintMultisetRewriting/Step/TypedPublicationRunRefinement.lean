import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationExecution

/-!
# Whole-run refinement maps for source publication

The source independently composes each solver answer with its helper
weakening. The resulting context map is exactly the actual step run's map,
not merely a matching endpoint or store projection. Final solutions pull
back along this map to solutions of the initial knowledge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull

variable {Head : Type} {rules : Rules Head}
variable {L : Type} [UniverseLevel.LevelOrder L] {levels : LevelModel rules L}
  {O : Type} [DecidableEq O] {program : Program levels O}
  {permission : {state : State rules O} → Candidate program state → Prop}

namespace Program.Execution

def refinement : {state : State rules O} → (execution : program.Execution permission state) →
    execution.last.frame ⟶ state.frame
  | _, .nil state => 𝟙 state.frame
  | _, .cons candidate _ _ rest =>
      rest.refinement ≫ (candidate.answer ≫ candidate.schema.helpers.weaken)

def refinementData {state : State rules O} (execution : program.Execution permission state) :
    Σ frame : Context rules, frame ⟶ state.frame := ⟨execution.last.frame, execution.refinement⟩

def nativeRefinementData {state : State rules O} (run : (program.toStep permission).Run state) :
    Σ frame : Context rules, frame ⟶ state.frame := ⟨run.last.frame, run.toLast⟩

theorem nativeRefinementData_cast {source target : State rules O} (same : source = target)
    (run : (program.toStep permission).Run source) :
    HEq (nativeRefinementData (same ▸ run)) (nativeRefinementData run) := by
  cases same
  rfl

theorem toRun_refinementData : {state : State rules O} →
    (execution : program.Execution permission state) → nativeRefinementData execution.toRun = execution.refinementData
  | _, .nil _ => rfl
  | _, .cons candidate admitted allowed rest => by
      let carried := ((program.result_eq permission candidate admitted allowed).symm ▸ rest.toRun)
      let postcompose : (Σ frame : Context rules, frame ⟶ candidate.target) →
          (Σ frame : Context rules, frame ⟶ _) := fun arrow =>
        ⟨arrow.1, arrow.2 ≫ (candidate.answer ≫ candidate.schema.helpers.weaken)⟩
      have carriedData : nativeRefinementData carried = nativeRefinementData rest.toRun :=
        eq_of_heq (nativeRefinementData_cast
          (program.result_eq permission candidate admitted allowed).symm rest.toRun)
      calc
        nativeRefinementData (.cons candidate ((program.admits_iff permission candidate).mpr
            ⟨admitted, allowed⟩) carried) = postcompose (nativeRefinementData carried) := rfl
        _ = postcompose (nativeRefinementData rest.toRun) := congrArg postcompose carriedData
        _ = postcompose rest.refinementData := congrArg postcompose (toRun_refinementData rest)
        _ = (Program.Execution.cons candidate admitted allowed rest).refinementData := rfl

/-- Source solutions are transported through the independently constructed
map, using the actual residual knowledge at every publication. -/
theorem models_start : {state : State rules O} → (execution : program.Execution permission state) →
    {observer : Context rules} → (solution : observer ⟶ execution.last.frame) →
    (frames levels).Models solution execution.last.knowledge →
      (frames levels).Models (solution ≫ execution.refinement) state.knowledge
  | _, .nil state, observer, solution, solved => by
      exact Eq.mpr (congrArg (fun substitution : observer ⟶ state.frame =>
        (frames levels).Models substitution state.knowledge) (Category.comp_id solution)) solved
  | state, .cons candidate admitted allowed rest, observer, solution, solved => by
      have later := models_start rest solution solved
      have information := candidate.basis.sound (solution ≫ rest.refinement) later
      have before := (DependentFull.step levels O).information_refines candidate.application.compile
        ((solution ≫ rest.refinement) ≫ candidate.answer) information
      change (frames levels).Models
        (((solution ≫ rest.refinement) ≫ candidate.answer) ≫ candidate.schema.helpers.weaken)
        state.knowledge at before
      have associated : ((solution ≫ rest.refinement) ≫ candidate.answer) ≫ candidate.schema.helpers.weaken =
          solution ≫ (rest.refinement ≫ (candidate.answer ≫ candidate.schema.helpers.weaken)) :=
        (Category.assoc (solution ≫ rest.refinement) candidate.answer candidate.schema.helpers.weaken).trans
          (Category.assoc solution rest.refinement (candidate.answer ≫ candidate.schema.helpers.weaken))
      exact Eq.mp (congrArg (fun substitution : observer ⟶ state.frame =>
        (frames levels).Models substitution state.knowledge) associated) before

end Program.Execution

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Program.Execution.toRun_refinementData
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Program.Execution.models_start
