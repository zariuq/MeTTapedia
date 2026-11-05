import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualAnswerFamilies
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionAmalgamation

/-!
# Independently named conditional problems share one solver problem

Each component uses its own tagged declaration family. Models of other
components can be added without narrowing the selected component's value
instances. Satisfiability and private-name separation are both essential;
captured equations are not silently discarded.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualIndependentProblems

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching

variable {S : Signature} {Index Next : Type} (Variables : Index → Type)
    (declarations : ∀ index, Variables index → MetaArity S)
    (conditions : ∀ index, ContextualResidual.Problem (declarations index))
    {next : Next → MetaArity S}

abbrev family := ContextualAnswerFamilies.family Variables declarations
abbrev inclusion := ContextualAnswerFamilies.inclusion Variables declarations

def problem (indices : List Index) : ContextualResidual.Problem (family Variables declarations) :=
  (indices.map fun index => ContextualResidual.mapProblem (inclusion Variables declarations index) (conditions index)).flatten

theorem models_iff (indices : List Index) (candidate : Assignment (family Variables declarations) next) :
    ContextualResidual.Models candidate (problem Variables declarations conditions indices) ↔
      ∀ index ∈ indices, ContextualResidual.Models
        (Assignment.compose candidate (inclusion Variables declarations index)) (conditions index) := by
  constructor
  · intro model index member
    apply (ContextualResidual.models_mapProblem _ _ _).mp
    intro equation inside
    exact model equation (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨index, member, rfl⟩, inside⟩)
  · intro component equation member
    obtain ⟨part, chosen, inside⟩ := List.mem_flatten.mp member
    obtain ⟨index, member, rfl⟩ := List.mem_map.mp chosen
    exact ((ContextualResidual.models_mapProblem _ _ _).mpr (component index member)) equation inside

structure Model {V : Type} (declaration : V → MetaArity S) (problem : ContextualResidual.Problem declaration) : Type 1 where
  Names : Type
  declarations : Names → MetaArity S
  images : Assignment declaration declarations
  valid : ContextualResidual.Models images problem

noncomputable def chooseModel {V : Type} {declaration : V → MetaArity S} {problem : ContextualResidual.Problem declaration}
    (consistent : ContextualConditionalExecution.Solvable problem) : Model declaration problem :=
  Classical.choice (by
    obtain ⟨Future, future, candidate, model⟩ := consistent
    exact ⟨⟨Future, future, candidate, model⟩⟩)

abbrev modelNames (models : ∀ index, Model (declarations index) (conditions index)) (index : Index) := (models index).Names
abbrev modelDecls (models : ∀ index, Model (declarations index) (conditions index)) (index : Index) := (models index).declarations
abbrev modelFamily (models : ∀ index, Model (declarations index) (conditions index)) :=
  ContextualAnswerFamilies.family (modelNames Variables declarations conditions models) (modelDecls Variables declarations conditions models)

def combinedImages (models : ∀ index, Model (declarations index) (conditions index)) :
    Assignment (family Variables declarations) (modelFamily Variables declarations conditions models) := fun ⟨index, name⟩ =>
  instantiate (ContextualAnswerFamilies.inclusion (modelNames Variables declarations conditions models)
    (modelDecls Variables declarations conditions models) index) ((models index).images name)

theorem combined_component (models : ∀ index, Model (declarations index) (conditions index)) (index : Index) :
    Assignment.compose (combinedImages Variables declarations conditions models) (inclusion Variables declarations index) =
      Assignment.compose (ContextualAnswerFamilies.inclusion (modelNames Variables declarations conditions models)
        (modelDecls Variables declarations conditions models) index) (models index).images := by
  funext name
  exact instantiate_generator _ _

theorem combined_model (models : ∀ index, Model (declarations index) (conditions index)) (indices : List Index) :
    ContextualResidual.Models (combinedImages Variables declarations conditions models)
      (problem Variables declarations conditions indices) := by
  apply (models_iff Variables declarations conditions indices _).mpr
  intro index _member
  rw [combined_component]
  exact ContextualResidual.models_compose (models index).valid _

theorem solvable (consistent : ∀ index, ContextualConditionalExecution.Solvable (conditions index)) (indices : List Index) :
    ContextualConditionalExecution.Solvable (problem Variables declarations conditions indices) := by
  let models := fun index => chooseModel (consistent index)
  exact ⟨_, modelFamily Variables declarations conditions models,
    combinedImages Variables declarations conditions models, combined_model Variables declarations conditions models indices⟩

variable [DecidableEq Index]

omit [DecidableEq Index] in
theorem holds_extension_iff {Local Shared O : Type} (locals : Local → MetaArity S)
    {captures : Shared → MetaArity S} (extension : Extension next) (candidate : Assignment captures next)
    {Γ : Ctx S} {sort : S.Srt} (rows : O → ContextualConditionalRows.Row locals captures Γ sort)
    (world : Finset O) (check : Check (Term (signature S captures) Γ sort)) :
    ContextualConditionalGuards.Holds locals (Assignment.compose extension.assignment candidate) rows world check ↔
      ContextualConditionalGuards.Holds locals candidate rows world check := by
  cases check with
  | equal first second =>
      change instantiate (Assignment.compose extension.assignment candidate) first =
        instantiate (Assignment.compose extension.assignment candidate) second ↔
        instantiate candidate first = instantiate candidate second
      rw [Assignment.instantiate_compose, Assignment.instantiate_compose]
      exact ⟨fun same => extension.instantiate_injective same, congrArg (instantiate extension.assignment)⟩
  | absent pattern =>
      simp only [ContextualConditionalGuards.Holds, Assignment.instantiate_compose,
        ContextualConditionalRealizations.matches_extension_iff]
  | count pattern cardinality =>
      have region : ContextualConditionalGuards.region locals (Assignment.compose extension.assignment candidate) rows world pattern =
          ContextualConditionalGuards.region locals candidate rows world pattern := by
        classical
        ext occurrence
        rw [ContextualConditionalGuards.mem_region, ContextualConditionalGuards.mem_region, Assignment.instantiate_compose]
        exact and_congr_right fun _ => ContextualConditionalRealizations.matches_extension_iff
          locals captures extension candidate (instantiate candidate pattern) (rows occurrence)
      change (ContextualConditionalGuards.region locals (Assignment.compose extension.assignment candidate) rows world pattern).card = cardinality ↔
        (ContextualConditionalGuards.region locals candidate rows world pattern).card = cardinality
      rw [region]

/-- A chosen component model extends to all components without changing its value assignment. -/
theorem extend_model (consistent : ∀ index, ContextualConditionalExecution.Solvable (conditions index))
    (indices : List Index) (selected : Index) (images : Assignment (declarations selected) next)
    (model : ContextualResidual.Models images (conditions selected)) :
    ∃ extension : Extension next, ∃ all : Assignment (family Variables declarations) extension.declarations,
      ContextualResidual.Models all (problem Variables declarations conditions indices) ∧
        Assignment.compose all (inclusion Variables declarations selected) = Assignment.compose extension.assignment images := by
  let models := fun index => chooseModel (consistent index)
  let extra := Extension.withLocals (modelFamily Variables declarations conditions models) next
  let others : Assignment (modelFamily Variables declarations conditions models) extra.declarations :=
    ContextualStoredRows.privateSource (modelFamily Variables declarations conditions models) next
  let all : Assignment (family Variables declarations) extra.declarations := fun ⟨index, name⟩ =>
    if same : index = selected then by
      subst index
      exact instantiate extra.assignment (images name)
    else instantiate others (combinedImages Variables declarations conditions models ⟨index, name⟩)
  have selectedMap : Assignment.compose all (inclusion Variables declarations selected) = Assignment.compose extra.assignment images := by
    funext name
    change instantiate all (generator (family Variables declarations) ⟨selected, name⟩) = instantiate extra.assignment (images name)
    rw [instantiate_generator]
    dsimp only [all]
    exact dif_pos rfl
  refine ⟨extra, all, ?_, selectedMap⟩
  apply (models_iff Variables declarations conditions indices _).mpr
  intro index _member
  by_cases same : index = selected
  · subst index
    rw [selectedMap]
    exact ContextualResidual.models_compose model extra.assignment
  · have otherMap : Assignment.compose all (inclusion Variables declarations index) =
        Assignment.compose others
          (Assignment.compose (combinedImages Variables declarations conditions models) (inclusion Variables declarations index)) := by
      funext name
      change instantiate all (generator (family Variables declarations) ⟨index, name⟩) =
        instantiate others (instantiate (combinedImages Variables declarations conditions models)
          (generator (family Variables declarations) ⟨index, name⟩))
      rw [instantiate_generator, instantiate_generator]
      dsimp only [all]
      exact dif_neg same
    rw [otherMap, combined_component]
    exact ContextualResidual.models_compose (ContextualResidual.models_compose (models index).valid _) others

/-- Independent satisfiable problems do not narrow the selected output's instance set. -/
theorem instances_iff (consistent : ∀ index, ContextualConditionalExecution.Solvable (conditions index))
    (indices : List Index) (selected : Index) (member : selected ∈ indices)
    {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S (declarations selected)) Γ sort)
    (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances (problem Variables declarations conditions indices)
      (instantiate (inclusion Variables declarations selected) value) next pattern ↔
      ContextualPublication.SourceInstances (conditions selected) value next pattern := by
  constructor
  · rintro ⟨extension, candidate, model, same⟩
    exact ⟨extension, Assignment.compose candidate (inclusion Variables declarations selected),
      (models_iff Variables declarations conditions indices candidate).mp model selected member,
      (Assignment.instantiate_compose candidate _ value).trans same⟩
  · rintro ⟨extension, images, model, same⟩
    obtain ⟨extra, all, joint, projected⟩ := extend_model Variables declarations conditions consistent indices selected images model
    refine ⟨extension.trans extra, all, joint, ?_⟩
    erw [← Assignment.instantiate_compose, projected, Assignment.instantiate_compose,
      Extension.trans_assignment, Assignment.instantiate_compose]
    exact congrArg (instantiate extra.assignment) same

/-- Independent satisfiable blocks also preserve an original guard at its own watched world. -/
theorem asks_iff (consistent : ∀ index, ContextualConditionalExecution.Solvable (conditions index))
    (indices : List Index) (selected : Index) (member : selected ∈ indices)
    {Local O : Type} (locals : Local → MetaArity S) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → ContextualConditionalRows.Row locals (declarations selected) Γ sort) (world : Finset O)
    (check : Check (Term (signature S (declarations selected)) Γ sort)) :
    ContextualConditionalGuards.Ask locals (problem Variables declarations conditions indices)
      (fun occurrence => (rows occurrence).map locals _ (inclusion Variables declarations selected)) world
      (check.map (instantiate (inclusion Variables declarations selected))) ↔
      ContextualConditionalGuards.Ask locals (conditions selected) rows world check := by
  constructor
  · intro asked Future future candidate model
    obtain ⟨extension, all, joint, projected⟩ := extend_model Variables declarations conditions consistent indices selected candidate model
    have original := (ContextualConditionalGuards.holds_transport locals (inclusion Variables declarations selected)
      all rows world check).mp (asked _ _ all joint)
    rw [projected] at original
    exact (holds_extension_iff locals extension candidate rows world check).mp original
  · intro asked Future future candidate model
    apply (ContextualConditionalGuards.holds_transport locals (inclusion Variables declarations selected) candidate rows world check).mpr
    exact asked Future future _ ((models_iff Variables declarations conditions indices candidate).mp model selected member)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualIndependentProblems
