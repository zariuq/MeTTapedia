import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReachExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTransportedActivation

/-!
# Joined reach admission uses the existing contextual execution

Locating a rule commutes with its one fresh contextual assignment. The
joined event's equations are exactly those prepared by the existing
activation owner, including the separately opened stored uses. Its guards,
physical selection and future-family solvability therefore supply semantic
admission to that owner. In the structural-pattern fragment, the existing
solver constructs a completed actual run. No solver result is a premise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReach

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {point : S.Srt} {Name V W Local Shared O : Type}
    {source : V → MetaArity (base S point Name)} {next : W → MetaArity (base S point Name)}

def spaceTerms (decl : V → MetaArity (base S point Name)) :
    NamedSpaces.SpaceTerms (ContextualFamilies.action decl [] point) Name where
  atSpace := place
  name := name
  apply_atSpace := fun _ _ _ => rfl
  E_atSpace := fun _ _ _ _ => ⟨place_injective,fun ⟨first,second⟩ => congrArg₂ place first second⟩
  atSpace_injective := fun _ _ _ _ => place_injective
  apply_name := fun _ _ => rfl
  E_name := by
    intro a b
    change (name (decl := decl) a) = name b ↔ a = b
    exact ⟨fun same => name_injective same,congrArg name⟩

def mapLocatedCheck {T U : Type} (change : T → U) : NamedSpaces.LocatedCheck T → NamedSpaces.LocatedCheck U
  | .equal left right => .equal (change left) (change right)
  | .absent address payload => .absent (change address) (change payload)
  | .count address payload number => .count (change address) (change payload) number

def mapLocated {T U : Type} (change : T → U) (rule : NamedSpaces.LocatedRule T) : NamedSpaces.LocatedRule U :=
  ⟨rule.take.map (fun p => (change p.1,change p.2)),
    rule.read.map (fun p => (change p.1,change p.2)),
    rule.tell.map (fun e => (change e.1,change e.2)),rule.checks.map (mapLocatedCheck change),
    rule.produce.map (fun p => (change p.1,change p.2))⟩

theorem locatedCheck_instantiation (assignment : Assignment source next)
    (check : NamedSpaces.LocatedCheck (Closed source)) :
    (mapLocatedCheck (instantiate assignment) check).toCheck (spaceTerms next) =
      (check.toCheck (spaceTerms source)).map (instantiate assignment) := by
  cases check <;> rfl

theorem locatedRule_instantiation (assignment : Assignment source next)
    (rule : NamedSpaces.LocatedRule (Closed source)) :
    (mapLocated (instantiate assignment) rule).toRule (spaceTerms next) =
      (rule.toRule (spaceTerms source)).map (instantiate assignment) := by
  cases rule
  simp only [mapLocated,NamedSpaces.LocatedRule.toRule,RuleInstance.map,List.map_map,
    Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro element _
  cases element <;> rfl

variable (locals : Local → MetaArity (base S point Name))
    (captures : Shared → MetaArity (base S point Name))

def freshLocated (occupied : Finset Nat) (selection : Selection O)
    (rule : NamedSpaces.LocatedRule (Closed (ContextualSelectionViews.source locals captures))) :=
  mapLocated (ContextualFreshening.termAt locals captures
    (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort selection))) rule

theorem lowerRule_eq_located (rule : NamedSpaces.LocatedRule (ActiveTerm locals captures)) :
    lowerRule locals captures rule = rule.toRule (spaceTerms (Active locals captures)) := by
  cases rule
  unfold lowerRule NamedSpaces.LocatedRule.toRule
  congr 1
  apply List.map_congr_left
  intro check _
  cases check <;> rfl

theorem prepared_located_rule (occupied : Finset Nat) (selection : Selection O)
    (rule : NamedSpaces.LocatedRule (Closed (ContextualSelectionViews.source locals captures)))
    (rows : O → ContextualStoredRows.Row locals captures [] point) :
    lowerRule locals captures (freshLocated locals captures occupied selection rule) =
      (ContextualActivatedStep.prepared locals captures occupied selection
        (rule.toRule (spaceTerms (ContextualSelectionViews.source locals captures))) rows).rule := by
  rw [lowerRule_eq_located]
  exact locatedRule_instantiation (ContextualFreshening.assignment locals captures
    (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort selection))) rule

theorem event_problem_is_actual_preparation (occupied : Finset Nat) (selection : Selection O)
    (rule : NamedSpaces.LocatedRule (Closed (ContextualSelectionViews.source locals captures)))
    (addresses : O → Closed captures) (rows : O → ContextualStoredRows.Row locals captures [] point)
    (before : Configuration (Closed captures) O) :
    eventProblem locals captures occupied selection addresses rows before
      (freshLocated locals captures occupied selection rule) =
    ContextualActivatedStep.problem locals captures occupied selection
      (rule.toRule (spaceTerms (ContextualSelectionViews.source locals captures)))
      (placedRows locals captures addresses rows) before := by
  let raw := rule.toRule (spaceTerms (ContextualSelectionViews.source locals captures))
  have taken : List.ofFn (ContextualActivatedStep.prepared locals captures occupied selection raw
      (placedRows locals captures addresses rows)).taken =
        (inputViews locals captures occupied selection addresses rows).1 := by
    apply congrArg List.ofFn
    funext port
    exact ContextualActivatedStep.prepared_taken_view locals captures occupied selection raw
      (placedRows locals captures addresses rows) port
  have read : List.ofFn (ContextualActivatedStep.prepared locals captures occupied selection raw
      (placedRows locals captures addresses rows)).read =
        (inputViews locals captures occupied selection addresses rows).2 := by
    apply congrArg List.ofFn
    funext port
    exact ContextualActivatedStep.prepared_read_view locals captures occupied selection raw
      (placedRows locals captures addresses rows) port
  rw [ContextualActivatedStep.problem_eq_frame_append]
  unfold eventProblem
  apply congrArg (fun extra => (ContextualActivatedStep.frame locals captures before).equations ++ extra)
  unfold eventEquations
  dsimp only [ContextualActivatedStep.addedEquations]
  rw [← prepared_located_rule locals captures occupied selection rule
    (placedRows locals captures addresses rows),taken,read]
  rfl

variable {locals captures} [DecidableEq Name] [DecidableEq O]
    {occupied : Finset Nat} {selection : Selection O} {known : Set (ActiveTerm locals captures)}
    {written : Set Name} {addresses : O → Closed captures}
    {rows : O → ContextualStoredRows.Row locals captures [] point}
    {before : Configuration (Closed captures) O} {outputs : O → ActiveTerm locals captures}

theorem Admits.semantic_admission
    {rule : NamedSpaces.LocatedRule (Closed (ContextualSelectionViews.source locals captures))}
    (admitted : Admits locals captures occupied selection known written addresses rows before
      (freshLocated locals captures occupied selection rule) outputs) :
    ContextualGuardedStep.Valid locals captures occupied selection
      (rule.toRule (spaceTerms (ContextualSelectionViews.source locals captures)))
      (placedRows locals captures addresses rows) before outputs := by
  have resources := (ContextualInteractionFactors.resources_iff outputs selection before.present).mp admitted.resources
  refine ⟨⟨resources.1,resources.2.1,?_,?_,?_,admitted.enabled,?_⟩,?_⟩
  · simpa only [NamedSpaces.LocatedRule.toRule,freshLocated,mapLocated,List.length_map] using admitted.take_length
  · simpa only [NamedSpaces.LocatedRule.toRule,freshLocated,mapLocated,List.length_map] using admitted.read_length
  · rw [← prepared_located_rule]
    exact admitted.outputs
  · intro check member
    rw [← prepared_located_rule] at member
    rw [← event_problem_is_actual_preparation]
    exact admitted.checks check member
  · rw [← event_problem_is_actual_preparation]
    exact admitted.consistent

theorem Admits.completed_run [DecidableEq Local] [DecidableEq Shared] [DecidableEq S.Srt]
    [∀ result, DecidableEq (S.Op result)]
    {rule : NamedSpaces.LocatedRule (Closed (ContextualSelectionViews.source locals captures))}
    (admitted : Admits locals captures occupied selection known written addresses rows before
      (freshLocated locals captures occupied selection rule) outputs)
    (patterned : ContextualPatternFragment.ProblemPattern (ContextualResidual.observeProblem
      (eventProblem locals captures occupied selection addresses rows before
        (freshLocated locals captures occupied selection rule)))) :
    ∃ fuel update, ContextualTransportedActivation.FromRun locals captures fuel occupied selection
      (rule.toRule (spaceTerms (ContextualSelectionViews.source locals captures)))
      (placedRows locals captures addresses rows) before outputs update := by
  rw [event_problem_is_actual_preparation] at patterned
  exact (ContextualTransportedActivation.semantic_admission_iff_completed_run locals captures patterned).mp
    admitted.semantic_admission

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchematicReach
