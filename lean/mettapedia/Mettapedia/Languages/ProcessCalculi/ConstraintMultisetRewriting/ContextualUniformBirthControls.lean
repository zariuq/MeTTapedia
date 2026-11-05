import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformBirthProblem
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixPublicationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRowPacking

/-!
# Two creation-time schemas use the unchanged common-update publication form

The first output is created before a caller binding; the second after it.
One actual solver update must retain the first output's freedom and the
second output's condition. A separate captured-row control keeps shared
conditions conditional instead of treating them as independent private data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformBirthControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualSourceSchedules ContextualConditionalRows ContextualConjunctiveQueries

namespace TwoOutputs

open ContextualPrefixPublicationControls

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (result : base.Srt) : DecidableEq (base.Op result) := inferInstanceAs (DecidableEq DataOperator)

def laterCode : RuleInstance (Term (signature base (queryFamily none firstFamily)) [] ()) :=
  { secondCode with produce := [box secondActorX] }
def laterPlan : ContextualPublication.Plan (Term (signature base (queryFamily none firstFamily)) [] ()) :=
  ⟨laterCode, [true], rfl⟩
def laterSelection : Selection Nat := ⟨[], [], [1]⟩
abbrev final := ContextualClauseSourceState.target none firstLocals afterFirst laterPlan laterSelection

theorem later_admitted : ContextualClauseSourceState.Admitted none firstLocals afterFirst laterPlan laterSelection := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · with_unfolding_all exact second_admitted.solvable
  · intro check member
    cases member

def body : Schedule base Nat [] () initial final :=
  .snoc (.snoc (.nil initial) none firstPlan firstSelection) none laterPlan laterSelection

theorem admitted : body.Admitted := by
  have firstConsistent := (Schedule.snoc (Schedule.nil initial) none firstPlan firstSelection).source_solvable first_admitted.solvable
  exact ⟨⟨firstConsistent, first_admitted⟩, later_admitted⟩

def firstIndex : body.BirthIndex := ⟨0, by decide +kernel⟩
def secondIndex : body.BirthIndex := ⟨1, by decide +kernel⟩

theorem the_same_update_preserves_both_outputs (fuel : Nat) :
    ∃ result : UniformComputed body fuel, ∀ (Next : Type) (next : Next → MetaArity base)
      (candidate : Assignment result.family next),
      Matches (ContextualPublication.privateFamily none result.update.declaration) result.family candidate
        (box (symbol 2)) (result.birthRow none firstIndex) ∧
      Matches (ContextualPublication.privateFamily none result.update.declaration) result.family candidate
        (box (symbol 1)) (result.birthRow none secondIndex) ∧
      ¬ Matches (ContextualPublication.privateFamily none result.update.declaration) result.family candidate
        (box (symbol 2)) (result.birthRow none secondIndex) := by
  obtain ⟨result⟩ := compute_uniform body admitted fuel
  refine ⟨result, ?_⟩
  intro Next next candidate
  refine ⟨(result.birth_row_instances none firstIndex next candidate _).mpr ?_,
    (result.birth_row_instances none secondIndex next candidate _).mpr ?_, ?_⟩
  · change ContextualPublication.SourceInstances [] (box firstX) next (box (symbol 2))
    exact ⟨ContextualGuardMatching.Extension.identity next, firstModel next 2,
      (by intro equation member; cases member), rfl⟩
  · change ContextualPublication.SourceInstances [(observe secondX, observe (symbol 1))]
      (box secondX) next (box (symbol 1))
    refine ⟨ContextualGuardMatching.Extension.identity next, secondModel next, ?_, rfl⟩
    erw [ContextualResidual.models_observed_iff]
    rfl
  · intro matched
    obtain ⟨extension, images, model, same⟩ :=
      (result.birth_row_instances none secondIndex next candidate _).mp matched
    change ContextualResidual.Models images [(observe secondX, observe (symbol 1))] at model
    erw [ContextualResidual.models_observed_iff] at model
    change box (instantiate images secondX) = box (symbol 2) at same
    rw [model] at same
    have arguments := (Args.cons.inj (eq_of_heq (Term.op.inj same).2)).1
    have impossible : (1 : Nat) = 2 := DataOperator.symbol.inj (Sum.inl.inj (Term.op.inj arguments).1)
    omega

end TwoOutputs

namespace ActualFiring

open ContextualPrefixPublicationControls

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (result : base.Srt) : DecidableEq (base.Op result) := inferInstanceAs (DecidableEq DataOperator)

def code : RuleInstance (Term (signature base copiedActor) [] ()) :=
  { copiedCode with produce := [box savedX, box mainX] }
def plan : ContextualPublication.Plan (Term (signature base copiedActor) [] ()) := ⟨code, [true, true], rfl⟩
def selected : Selection Nat := ⟨[], [], [0, 1]⟩

theorem information : ContextualClauseSourceState.information copiedQueries none initial plan selected =
    [(observe (generator copiedFamily (.inr (.inr ()))), observe (symbol 1))] := by
  with_unfolding_all rfl

theorem admitted : ContextualClauseSourceState.Admitted copiedQueries none initial plan selected := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · with_unfolding_all exact copied_admitted.solvable
  · intro check member
    cases member

/-- One unchanged native firing publishes both ordinary outputs with their different freedoms. -/
theorem an_actual_two_output_firing (fuel : Nat) :
    ∃ compiled : ContextualConditionalClauses.Compiled copiedQueries none (before := initial.native ∅) plan selected,
      compiled.firing.fuel = fuel ∧ compiled.firing.target.present = {0, 1} ∧
      ∀ (Next : Type) (next : Next → MetaArity base) (candidate : Assignment compiled.firing.target.declarations next),
        Matches (ContextualPublication.privateFamily (ContextualClauseFrames.bank copiedQueries none) compiled.firing.update.declaration)
          compiled.firing.target.declarations candidate (box (symbol 2)) (compiled.firing.target.rows 0) ∧
        Matches (ContextualPublication.privateFamily (ContextualClauseFrames.bank copiedQueries none) compiled.firing.update.declaration)
          compiled.firing.target.declarations candidate (box (symbol 1)) (compiled.firing.target.rows 1) ∧
        ¬ Matches (ContextualPublication.privateFamily (ContextualClauseFrames.bank copiedQueries none) compiled.firing.update.declaration)
          compiled.firing.target.declarations candidate (box (symbol 2)) (compiled.firing.target.rows 1) := by
  obtain ⟨compiled, budget⟩ := ContextualConditionalClauses.realize copiedQueries none (before := initial.native ∅)
    plan selected admitted fuel
  refine ⟨compiled, budget, ?_, ?_⟩
  · rw [compiled.physical_result]
    decide +kernel
  · intro Next next candidate
    have kinds := compiled.intents
    change [compiled.firing.reusable 0, compiled.firing.reusable 1] = [true, true] at kinds
    have firstKind := (List.cons.inj kinds).1
    have secondKind := (List.cons.inj (List.cons.inj kinds).2).1
    refine ⟨(compiled.ordinary_body_instances ⟨0, by decide +kernel⟩ firstKind next candidate _).mpr ?_,
      (compiled.ordinary_body_instances ⟨1, by decide +kernel⟩ secondKind next candidate _).mpr ?_, ?_⟩
    · refine ⟨ContextualGuardMatching.Extension.identity next, copiedModel next 2, ?_, rfl⟩
      with_unfolding_all exact copied_model_valid next 2
    · refine ⟨ContextualGuardMatching.Extension.identity next, copiedModel next 0, ?_, rfl⟩
      with_unfolding_all exact copied_model_valid next 0
    · intro matched
      obtain ⟨extension, images, model, same⟩ :=
        (compiled.ordinary_body_instances ⟨1, by decide +kernel⟩ secondKind next candidate _).mp matched
      change ContextualResidual.Models images
        (ContextualClauseSourceState.information copiedQueries none initial plan selected) at model
      erw [information, ContextualResidual.models_observed_iff] at model
      change box (instantiate images (generator copiedFamily (.inr (.inr ())))) = box (symbol 2) at same
      rw [model] at same
      have arguments := (Args.cons.inj (eq_of_heq (Term.op.inj same).2)).1
      have impossible : (1 : Nat) = 2 := DataOperator.symbol.inj (Sum.inl.inj (Term.op.inj arguments).1)
      omega

end ActualFiring

namespace SharedConditions

open ContextualPrefixPublicationControls (DataOperator base captures none symbol box)

abbrev locals (_ : Bool) : MetaArity base := ([], ())
abbrev declarations := ContextualSelectionViews.source locals captures
def privateValue (index : Bool) : Term (signature base declarations) [] () := generator declarations (.inl index)
def sharedValue : Term (signature base declarations) [] () := generator declarations (.inr ())
def first : Row locals captures [] () :=
  ⟨.schema (box (privateValue false)), [(observe (privateValue false), observe sharedValue)]⟩
def second : Row locals captures [] () :=
  ⟨.schema (box (privateValue true)), [(observe (privateValue true), observe sharedValue), (observe sharedValue, observe (symbol 9))]⟩
def combined : Row locals captures [] () :=
  ⟨first.value, first.obligations ++ second.obligations⟩
def caller (n : Nat) : Assignment captures none := fun _ => symbol n

theorem the_first_row_is_available_at_seven : Matches locals captures (caller 7) (box (symbol 7)) first := by
  refine ⟨ContextualGuardMatching.Extension.identity none, (fun _ => symbol 7), ?_, rfl⟩
  intro equation member
  have only : equation = (observe (privateValue false), observe sharedValue) := List.mem_singleton.mp member
  subst equation
  rfl

/-- Both conditions are jointly satisfiable globally; that does not preserve each caller model. -/
theorem the_combined_conditions_are_globally_solvable : ContextualConditionalExecution.Solvable combined.obligations := by
  let images : Assignment declarations none := fun
    | .inl _ => symbol 9
    | .inr _ => symbol 9
  refine ⟨Empty, none, images, ?_⟩
  intro equation member
  change equation ∈ [(observe (privateValue false), observe sharedValue),
    (observe (privateValue true), observe sharedValue), (observe sharedValue, observe (symbol 9))] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

/-- Adding the dormant row condition suppresses a valid answer under the same shared capture. -/
theorem conjoining_the_dormant_condition_loses_the_answer :
    ¬ Matches locals captures (caller 7) (box (symbol 7)) combined := by
  rintro ⟨extension, images, model, _same⟩
  have equation : (observe sharedValue, observe (symbol 9)) ∈ combined.obligations := by
    simp [combined, first, second]
  have oneEquation : ContextualResidual.Models
      (ContextualGuardMatching.instanceAssignment locals images extension.assignment (caller 7))
      [(observe sharedValue, observe (symbol 9))] := by
    intro selected member
    have only := List.mem_singleton.mp member
    subst selected
    exact model _ equation
  have fixed := (ContextualResidual.models_observed_iff _ sharedValue (symbol 9)).mp oneEquation
  have captured : instantiate (ContextualGuardMatching.instanceAssignment locals images extension.assignment (caller 7)) sharedValue =
      symbol 7 := by
    erw [sharedValue, instantiate_generator]
    rfl
  have same := captured.symm.trans fixed
  have impossible : (7 : Nat) = 9 := DataOperator.symbol.inj (Sum.inl.inj (Term.op.inj same).1)
  omega

end SharedConditions

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformBirthControls
