import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixIsolation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldCompilerSteps

/-!
# An earlier schema must not inherit a later caller binding

One private clause publishes box(X) as an ordinary schema while X is free.
The next clause binds the caller's X to 1. The stored schema still matches
box(2). A naive fused ordinary output using the final problem does not.
A separate private variable for the saved schema restores that answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixPublicationControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualWorldComparison
open ContextualGuardMatching

inductive DataOperator where
  | symbol : Nat → DataOperator
  | box : DataOperator
  deriving DecidableEq

abbrev base : Signature where
  Srt := Unit
  Op _ := DataOperator
  arity
    | .symbol _ => []
    | .box => [([], ())]

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq DataOperator)

abbrev none (name : Empty) : MetaArity base := nomatch name
abbrev captures (_ : Unit) : MetaArity base := ([], ())
def symbol {V : Type} {decl : V → MetaArity base} (n : Nat) : Term (signature base decl) [] () :=
  .op (.inl (.symbol n)) .nil
def box {V : Type} {decl : V → MetaArity base} {Γ : Ctx base}
    (value : Term (signature base decl) Γ ()) : Term (signature base decl) Γ () :=
  .op (.inl .box) (.cons value .nil)

abbrev initial : ContextualClauseSourceState.World none Nat [] () :=
  ⟨Unit, inferInstance, captures, [], ∅, fun _ => ofStored none captures (.shared (symbol 0))⟩
local instance : DecidableEq initial.Names := initial.equality

abbrev actor := queryFamily none captures
def callerX : Term (signature base actor) [] () := generator actor (.inr ())
def firstCode : RuleInstance (Term (signature base actor) [] ()) := ⟨[], [], [], [], [box callerX]⟩
def firstPlan : ContextualPublication.Plan (Term (signature base actor) [] ()) := ⟨firstCode, [true], rfl⟩
def firstSelection : Selection Nat := ⟨[], [], [0]⟩
abbrev afterFirst := ContextualClauseSourceState.target none none initial firstPlan firstSelection
abbrev firstFamily := family none none captures
abbrev firstLocals := ContextualClauseSourceState.resultLocals none none initial
local instance : DecidableEq afterFirst.Names := afterFirst.equality

def firstX : Term (signature base firstFamily) [] () := generator firstFamily (.inr (.inr ()))
def secondActorX : Term (signature base (queryFamily none firstFamily)) [] () :=
  instantiate (ContextualSelectionViews.capturedSource none firstFamily) firstX
def secondCode : RuleInstance (Term (signature base (queryFamily none firstFamily)) [] ()) :=
  ⟨[], [], [(secondActorX, symbol 1)], [], []⟩
def secondPlan : ContextualPublication.Plan (Term (signature base (queryFamily none firstFamily)) [] ()) :=
  ⟨secondCode, [], rfl⟩
def secondSelection : Selection Nat := ⟨[], [], []⟩
abbrev secondFamily := family none firstLocals firstFamily
abbrev afterSecond := ContextualClauseSourceState.target none firstLocals afterFirst secondPlan secondSelection
def secondX : Term (signature base secondFamily) [] () :=
  instantiate (captureEmbedding none firstLocals firstFamily) firstX

def firstModel {V : Type} (decl : V → MetaArity base) (n : Nat) : Assignment firstFamily decl
  | .inl impossible => nomatch impossible
  | .inr (.inl ⟨_, impossible⟩) => nomatch impossible
  | .inr (.inr ()) => symbol n

def secondModel {V : Type} (decl : V → MetaArity base) : Assignment secondFamily decl
  | .inl impossible => nomatch impossible
  | .inr (.inl ⟨_, .inl impossible⟩) => nomatch impossible
  | .inr (.inl ⟨_, .inr name⟩) => firstModel decl 1 name
  | .inr (.inr name) => firstModel decl 1 name

theorem first_information : ContextualClauseSourceState.information none none initial firstPlan firstSelection = [] := by
  with_unfolding_all rfl

theorem second_information : ContextualClauseSourceState.information none firstLocals afterFirst secondPlan secondSelection =
    [(observe secondX, observe (symbol 1))] := by
  with_unfolding_all rfl

theorem first_admitted : ContextualClauseSourceState.Admitted none none initial firstPlan firstSelection := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · refine ⟨Empty, none, firstModel none 1, ?_⟩
    change ContextualResidual.Models (firstModel none 1)
      (ContextualClauseSourceState.information none none initial firstPlan firstSelection)
    erw [first_information]
    intro equation member
    cases member
  · intro check member
    cases member

theorem second_admitted : ContextualClauseSourceState.Admitted none firstLocals afterFirst secondPlan secondSelection := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · refine ⟨Empty, none, secondModel none, ?_⟩
    change ContextualResidual.Models (secondModel none)
      (ContextualClauseSourceState.information none firstLocals afterFirst secondPlan secondSelection)
    erw [second_information]
    intro equation member
    have only := List.mem_singleton.mp member
    subst equation
    rfl
  · intro check member
    cases member

theorem the_callers_variable_is_one {V : Type} (decl : V → MetaArity base)
    (candidate : Assignment secondFamily decl) (model : ContextualResidual.Models candidate afterSecond.equations) :
    instantiate candidate secondX = symbol 1 := by
  change ContextualResidual.Models candidate
    (ContextualClauseSourceState.information none firstLocals afterFirst secondPlan secondSelection) at model
  erw [second_information, ContextualResidual.models_observed_iff] at model
  exact model

theorem the_earlier_schema_still_matches_two {V : Type} (decl : V → MetaArity base)
    (candidate : Assignment secondFamily decl) :
    Matches (ContextualClauseSourceState.resultLocals none firstLocals afterFirst) secondFamily candidate
      (box (symbol 2)) (afterSecond.rows 0) := by
  apply (ContextualClauseSourceState.retained_matches (queries := none) (locals := firstLocals)
    (before := afterFirst) (plan := secondPlan) (picked := secondSelection) 0 (by simp [secondSelection]) decl candidate _).mpr
  apply (ContextualClauseSourceState.ordinary_output_instances first_admitted ⟨0, by decide +kernel⟩ rfl decl _ _).mpr
  refine ⟨ContextualGuardMatching.Extension.identity decl, firstModel decl 2, ?_, ?_⟩
  · erw [first_information]
    intro equation member
    cases member
  · rfl

def naiveCode : RuleInstance (Term (signature base actor) [] ()) :=
  ⟨[], [], [(callerX, symbol 1)], [], [box callerX]⟩
def naivePlan : ContextualPublication.Plan (Term (signature base actor) [] ()) := ⟨naiveCode, [true], rfl⟩
abbrev naiveWorld := ContextualClauseSourceState.target none none initial naivePlan firstSelection

theorem naive_information : ContextualClauseSourceState.information none none initial naivePlan firstSelection =
    [(observe firstX, observe (symbol 1))] := by
  with_unfolding_all rfl

theorem naive_admitted : ContextualClauseSourceState.Admitted none none initial naivePlan firstSelection := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · refine ⟨Empty, none, firstModel none 1, ?_⟩
    change ContextualResidual.Models (firstModel none 1)
      (ContextualClauseSourceState.information none none initial naivePlan firstSelection)
    erw [naive_information]
    intro equation member
    have only := List.mem_singleton.mp member
    subst equation
    rfl
  · intro check member
    cases member

private theorem box_injective {V : Type} {decl : V → MetaArity base}
    {first second : Term (signature base decl) [] ()} (same : box first = box second) : first = second :=
  (Args.cons.inj (eq_of_heq (Term.op.inj same).2)).1

theorem naive_fusion_loses_the_earlier_answer {V : Type} (decl : V → MetaArity base)
    (candidate : Assignment firstFamily decl) :
    ¬ Matches firstLocals firstFamily candidate (box (symbol 2)) (naiveWorld.rows 0) := by
  intro matched
  obtain ⟨extension, images, model, same⟩ :=
    (ContextualClauseSourceState.ordinary_output_instances naive_admitted ⟨0, by decide +kernel⟩ rfl decl candidate _).mp matched
  erw [naive_information, ContextualResidual.models_observed_iff] at model
  have fixed := model
  change instantiate images firstX = symbol 1 at fixed
  change box (instantiate images firstX) = box (symbol 2) at same
  rw [fixed] at same
  have different : (1 : Nat) = 2 := DataOperator.symbol.inj (Sum.inl.inj (Term.op.inj (box_injective same)).1)
  omega

abbrev copiedQueries (_ : Unit) : MetaArity base := ([], ())
abbrev copiedActor := queryFamily copiedQueries captures
abbrev copiedFamily := family copiedQueries none captures
def mainX : Term (signature base copiedActor) [] () := generator copiedActor (.inr ())
def savedX : Term (signature base copiedActor) [] () := generator copiedActor (.inl ())
def copiedCode : RuleInstance (Term (signature base copiedActor) [] ()) :=
  ⟨[], [], [(mainX, symbol 1)], [], [box savedX]⟩
def copiedPlan : ContextualPublication.Plan (Term (signature base copiedActor) [] ()) := ⟨copiedCode, [true], rfl⟩
abbrev copiedWorld := ContextualClauseSourceState.target copiedQueries none initial copiedPlan firstSelection
def copiedModel {V : Type} (decl : V → MetaArity base) (n : Nat) : Assignment copiedFamily decl
  | .inl () => symbol n
  | .inr (.inl ⟨_, impossible⟩) => nomatch impossible
  | .inr (.inr ()) => symbol 1

theorem copied_information : ContextualClauseSourceState.information copiedQueries none initial copiedPlan firstSelection =
    [(observe (generator copiedFamily (.inr (.inr ()))), observe (symbol 1))] := by
  with_unfolding_all rfl

theorem copied_admitted : ContextualClauseSourceState.Admitted copiedQueries none initial copiedPlan firstSelection := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · refine ⟨Empty, none, copiedModel none 0, ?_⟩
    change ContextualResidual.Models (copiedModel none 0)
      (ContextualClauseSourceState.information copiedQueries none initial copiedPlan firstSelection)
    erw [copied_information]
    intro equation member
    have only := List.mem_singleton.mp member
    subst equation
    rfl
  · intro check member
    cases member

theorem a_private_prefix_copy_preserves_the_answer {V : Type} (decl : V → MetaArity base)
    (candidate : Assignment copiedFamily decl) :
    Matches (ContextualClauseSourceState.resultLocals copiedQueries none initial) copiedFamily candidate
      (box (symbol 2)) (copiedWorld.rows 0) := by
  apply (ContextualClauseSourceState.ordinary_output_instances copied_admitted ⟨0, by decide +kernel⟩ rfl decl candidate _).mpr
  refine ⟨ContextualGuardMatching.Extension.identity decl, copiedModel decl 2, ?_, ?_⟩
  · erw [copied_information]
    intro equation member
    have only := List.mem_singleton.mp member
    subst equation
    rfl
  · rfl

theorem an_actual_single_firing_publishes_the_prefix_copy (fuel : Nat) :
    ∃ compiled : ContextualConditionalClauses.Compiled copiedQueries none (before := initial.native ∅)
        copiedPlan firstSelection, compiled.firing.fuel = fuel :=
  ContextualConditionalClauses.realize copiedQueries none (before := initial.native ∅)
    copiedPlan firstSelection copied_admitted fuel

def ambientProblem : ContextualResidual.Problem captures :=
  [(observe (generator captures ()), observe (symbol 1))]

theorem ambient_consistent : ContextualConditionalExecution.Solvable ambientProblem := by
  refine ⟨Empty, none, (fun _ => symbol 1), ?_⟩
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

abbrev firstFrame : Extension captures where
  Names := Empty ⊕ (Mettapedia.Logic.LP.ScopedVar Empty ⊕ Unit)
  declarations := firstFamily
  name _ := .inr (.inr ())
  injective first second _ := by cases first; cases second; rfl
  preserves _ := rfl

abbrev copiedFrame : Extension (ContextualPrefixIsolation.combined captures captures) where
  Names := Unit ⊕ (Mettapedia.Logic.LP.ScopedVar Empty ⊕ Unit)
  declarations := copiedFamily
  name
    | .inl () => .inl ()
    | .inr () => .inr (.inr ())
  injective := by
    intro first second same
    rcases first with ⟨⟩ | ⟨⟩ <;> rcases second with ⟨⟩ | ⟨⟩ <;> first | rfl | cases same
  preserves identity := by cases identity <;> rfl

theorem copied_problem_is_isolated :
    ContextualClauseSourceState.information copiedQueries none initial copiedPlan firstSelection =
      ContextualResidual.mapProblem copiedFrame.assignment
        (ContextualPrefixIsolation.problem captures captures [] ambientProblem) := by
  with_unfolding_all rfl

theorem copied_value_is_isolated :
    queryView copiedQueries none captures (box savedX) =
      instantiate copiedFrame.assignment
        (instantiate (ContextualStoredRows.privateSource captures captures) (box (generator captures ()))) := by
  with_unfolding_all rfl

theorem first_value_is_saved : queryView none none captures (box callerX) =
    instantiate firstFrame.assignment (box (generator captures ())) := by
  with_unfolding_all rfl

theorem copied_row_instances_are_exact {V : Type} (decl : V → MetaArity base)
    (candidate : Assignment copiedFamily decl) (pattern : Term (signature base decl) [] ()) :
    Matches (ContextualClauseSourceState.resultLocals copiedQueries none initial) copiedFamily candidate pattern
        (copiedWorld.rows 0) ↔
      ContextualPublication.SourceInstances ([] : ContextualResidual.Problem captures)
        (box (generator captures ())) decl pattern := by
  have ordinary := ContextualClauseSourceState.ordinary_output_instances copied_admitted
    ⟨0, by decide +kernel⟩ rfl decl candidate pattern
  change Matches _ _ _ _ _ ↔ ContextualPublication.SourceInstances
    (ContextualClauseSourceState.information copiedQueries none initial copiedPlan firstSelection)
    (queryView copiedQueries none captures (box savedX)) decl pattern at ordinary
  erw [copied_problem_is_isolated, copied_value_is_isolated] at ordinary
  exact ordinary.trans ((ContextualConditionalNaturality.source_instances_extension copiedFrame _ _ decl pattern).trans
    (ContextualPrefixIsolation.instances_iff captures captures [] ambientProblem ambient_consistent
      (box (generator captures ())) pattern))

theorem first_row_instances_are_exact {V : Type} (decl : V → MetaArity base)
    (candidate : Assignment firstFamily decl) (pattern : Term (signature base decl) [] ()) :
    Matches firstLocals firstFamily candidate pattern (afterFirst.rows 0) ↔
      ContextualPublication.SourceInstances ([] : ContextualResidual.Problem captures)
        (box (generator captures ())) decl pattern := by
  have ordinary := ContextualClauseSourceState.ordinary_output_instances first_admitted
    ⟨0, by decide +kernel⟩ rfl decl candidate pattern
  change Matches _ _ _ _ _ ↔ ContextualPublication.SourceInstances
    (ContextualClauseSourceState.information none none initial firstPlan firstSelection)
    (queryView none none captures (box callerX)) decl pattern at ordinary
  erw [first_information, first_value_is_saved] at ordinary
  exact ordinary.trans (ContextualConditionalNaturality.source_instances_extension firstFrame [] _ decl pattern)

theorem final_row_instances_are_exact {V : Type} (decl : V → MetaArity base)
    (candidate : Assignment secondFamily decl) (pattern : Term (signature base decl) [] ()) :
    Matches (ContextualClauseSourceState.resultLocals none firstLocals afterFirst) secondFamily candidate pattern
        (afterSecond.rows 0) ↔
      ContextualPublication.SourceInstances ([] : ContextualResidual.Problem captures)
        (box (generator captures ())) decl pattern := by
  exact (ContextualClauseSourceState.retained_matches (queries := none) (locals := firstLocals)
    (before := afterFirst) (plan := secondPlan) (picked := secondSelection) 0 (by simp [secondSelection]) decl candidate pattern).trans
    (first_row_instances_are_exact decl _ pattern)

theorem copied_model_valid {V : Type} (decl : V → MetaArity base) (n : Nat) :
    ContextualResidual.Models (copiedModel decl n) copiedWorld.equations := by
  change ContextualResidual.Models _
    (ContextualClauseSourceState.information copiedQueries none initial copiedPlan firstSelection)
  erw [copied_information]
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

theorem second_model_valid {V : Type} (decl : V → MetaArity base) :
    ContextualResidual.Models (secondModel decl) afterSecond.equations := by
  change ContextualResidual.Models _
    (ContextualClauseSourceState.information none firstLocals afterFirst secondPlan secondSelection)
  erw [second_information]
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

def sourceEnvironment : Assignment captures secondFamily := fun _ => secondX
def copiedEnvironment : Assignment captures copiedFamily := fun _ => generator copiedFamily (.inr (.inr ()))

theorem copied_main_is_one {V : Type} (decl : V → MetaArity base)
    (candidate : Assignment copiedFamily decl) (model : ContextualResidual.Models candidate copiedWorld.equations) :
    instantiate candidate (copiedEnvironment ()) = symbol 1 := by
  change ContextualResidual.Models _
    (ContextualClauseSourceState.information copiedQueries none initial copiedPlan firstSelection) at model
  erw [copied_information, ContextualResidual.models_observed_iff] at model
  exact model

theorem isolated_fusion_represents_the_two_private_steps :
    Equivalent afterSecond sourceEnvironment copiedWorld copiedEnvironment := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · intro Future future candidate model
    refine ⟨Extension.identity future, copiedModel future 0, ?_⟩
    have unit : (Extension.identity future).assignment = generator future := rfl
    erw [unit, Assignment.compose_identity_left]
    refine ⟨model, copied_model_valid future 0, ?_, ?_⟩
    · funext name
      cases name
      change instantiate candidate secondX = symbol 1
      exact the_callers_variable_is_one future candidate model
    · intro later pattern occurrence member
      have index : occurrence = 0 := by
        change occurrence ∈ ({0} : Finset Nat) at member
        exact Finset.mem_singleton.mp member
      subst occurrence
      exact (final_row_instances_are_exact later.declarations _ pattern).trans
        (copied_row_instances_are_exact later.declarations _ pattern).symm
  · intro Future future candidate model
    refine ⟨Extension.identity future, secondModel future, ?_⟩
    have unit : (Extension.identity future).assignment = generator future := rfl
    erw [unit, Assignment.compose_identity_left]
    refine ⟨second_model_valid future, model, ?_, ?_⟩
    · funext name
      cases name
      change symbol 1 = instantiate candidate (copiedEnvironment ())
      exact (copied_main_is_one future candidate model).symm
    · intro later pattern occurrence member
      have index : occurrence = 0 := by
        change occurrence ∈ ({0} : Finset Nat) at member
        exact Finset.mem_singleton.mp member
      subst occurrence
      exact (final_row_instances_are_exact later.declarations _ pattern).trans
        (copied_row_instances_are_exact later.declarations _ pattern).symm

theorem native_fusion_represents_the_two_private_steps
    (compiled : ContextualConditionalClauses.Compiled copiedQueries none (before := initial.native ∅)
      copiedPlan firstSelection) :
    Equivalent afterSecond sourceEnvironment (nativeWorld _ compiled.firing.target)
      (Assignment.compose compiled.continuationEnv (ContextualSelectionViews.capturedSource copiedQueries captures)) := by
  have represented := (actual_compiler_result (before := initial) (occupied := ∅) compiled).restrict
    (ContextualSelectionViews.capturedSource copiedQueries captures)
  have sameEnvironment : Assignment.compose (ContextualClauseSourceState.continuationEnv copiedQueries none initial)
      (ContextualSelectionViews.capturedSource copiedQueries captures) = copiedEnvironment := by
    funext name
    cases name
    rfl
  erw [sameEnvironment] at represented
  exact isolated_fusion_represents_the_two_private_steps.trans represented

theorem the_actual_fused_firing_keeps_the_earlier_answer
    (compiled : ContextualConditionalClauses.Compiled copiedQueries none (before := initial.native ∅)
      copiedPlan firstSelection) {V : Type} (decl : V → MetaArity base)
    (candidate : Assignment compiled.firing.target.declarations decl) :
    Matches (ContextualPublication.privateFamily (ContextualClauseFrames.bank copiedQueries none) compiled.firing.update.declaration)
      compiled.firing.target.declarations candidate (box (symbol 2)) (compiled.firing.target.rows 0) := by
  exact (ContextualClauseStateRefinement.all_row_observations (before := initial) (occupied := ∅)
    compiled 0 decl candidate (box (symbol 2))).mp
      (a_private_prefix_copy_preserves_the_answer decl (Assignment.compose candidate compiled.sourceFrame.assignment))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixPublicationControls
