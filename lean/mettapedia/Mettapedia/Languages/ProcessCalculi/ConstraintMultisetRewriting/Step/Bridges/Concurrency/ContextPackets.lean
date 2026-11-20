import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.TaggedAssignments

/-!
# Observations, environments and physical identities in one actual action

An environment packet is an existing contextual assignment, with its domain
and tagged target. Instantiation composes at the target. Matching a capture
environment against an identity environment therefore retains the complete
captured assignment, rather than a finite selection of its values.

Rigid values carry physical occurrence identities. They are kept separate
from the contextual information that matching those occurrences produces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.ContextPackets

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open TaggedAssignments (Object Substitution)

universe uR

variable (S : Signature)

structure Environment where
  domain : Frames.Frame S
  target : Object S
  assignment : Assignment domain.arity target.2.arity

theorem Environment.assignment_heq {first second : Environment S} (equal : first = second) :
    HEq first.assignment second.assignment := by
  cases equal
  rfl

def Environment.apply (substitution : Substitution S) (environment : Environment S) : Environment S :=
  ⟨environment.domain,(substitution environment.target).1,
    Assignment.compose (substitution environment.target).2 environment.assignment⟩

theorem Environment.apply_identity (environment : Environment S) :
    environment.apply S (TaggedAssignments.identity S) = environment := by
  rcases environment with ⟨domain,target,assignment⟩
  change (Environment.mk domain target (Assignment.compose (generator target.2.arity) assignment)) = _
  rw [Assignment.compose_identity_left]

theorem Environment.apply_compose (outer inner : Substitution S) (environment : Environment S) :
    environment.apply S (TaggedAssignments.compose S outer inner) =
      (environment.apply S inner).apply S outer := by
  rcases environment with ⟨domain,target,assignment⟩
  change Environment.mk domain (outer (inner target).1).1
      (Assignment.compose (Assignment.compose (outer (inner target).1).2 (inner target).2) assignment) =
    Environment.mk domain (outer (inner target).1).1
      (Assignment.compose (outer (inner target).1).2 (Assignment.compose (inner target).2 assignment))
  rw [Assignment.compose_associative]

inductive Value (Rigid : Type uR) : Type (max 1 uR) where
  | rigid : Rigid → Value Rigid
  | observation : TaggedAssignments.Packed S → Value Rigid
  | environment : Environment S → Value Rigid
  | row : Rigid → Environment S → Value Rigid

def apply {Rigid : Type uR} (substitution : Substitution S) : Value S Rigid → Value S Rigid
  | .rigid value => .rigid value
  | .observation value => .observation (TaggedAssignments.apply S substitution value)
  | .environment value => .environment (value.apply S substitution)
  | .row code environment => .row code (environment.apply S substitution)

def action (Rigid : Type uR) : SubstitutionAction (Value S Rigid) (Substitution S) where
  E := Eq
  equivalence := ⟨Eq.refl,Eq.symm,Eq.trans⟩
  apply := apply S
  identity := TaggedAssignments.identity S
  compose := TaggedAssignments.compose S
  apply_identity value := by
    cases value with
    | rigid => rfl
    | observation value => exact congrArg Value.observation (TaggedAssignments.apply_identity S value)
    | environment value => exact congrArg Value.environment (Environment.apply_identity S value)
    | row code environment => exact congrArg (Value.row code) (Environment.apply_identity S environment)
  apply_compose outer inner value := by
    cases value with
    | rigid => rfl
    | observation value => exact congrArg Value.observation (TaggedAssignments.apply_compose S outer inner value)
    | environment value => exact congrArg Value.environment (Environment.apply_compose S outer inner value)
    | row code environment => exact congrArg (Value.row code) (Environment.apply_compose S outer inner environment)
  preserves substitution {_ _} equal := congrArg (apply S substitution) equal

variable {S} {Rigid : Type uR}

def observation (source : Object S) (value : Observation S source.2.arity) : Value S Rigid :=
  .observation (TaggedAssignments.pack source value)

def problem (source : Object S) (equations : ContextualResidual.Problem source.2.arity) :
    EquationStore (Value S Rigid) :=
  equations.map fun equation => (observation source equation.1,observation source equation.2)

theorem models_problem (substitution : Substitution S) (source : Object S)
    (equations : ContextualResidual.Problem source.2.arity) :
    (action S Rigid).Models substitution (problem source equations) ↔
      ContextualResidual.Models (substitution source).2 equations := by
  constructor
  · intro solved equation present
    have equal := solved _ (List.mem_map.mpr ⟨equation,present,rfl⟩)
    exact TaggedAssignments.pack_injective (substitution source).1 (Value.observation.inj equal)
  · intro solved equation present
    obtain ⟨original,inside,rfl⟩ := List.mem_map.mp present
    exact congrArg (fun value => Value.observation (TaggedAssignments.pack (substitution source).1 value))
      (solved original inside)

def anchor (source : Object S) : Value S Rigid :=
  .environment ⟨source.2,source,generator source.2.arity⟩

def capture {source : Object S} (target : Object S)
    (assignment : Assignment source.2.arity target.2.arity) : Value S Rigid :=
  .environment ⟨source.2,target,assignment⟩

theorem apply_anchor (substitution : Substitution S) (source : Object S) :
    apply S substitution (anchor source : Value S Rigid) =
      .environment ⟨source.2,(substitution source).1,(substitution source).2⟩ := by
  change Value.environment (Environment.mk source.2 (substitution source).1
    (Assignment.compose (substitution source).2 (generator source.2.arity))) = _
  rw [Assignment.compose_identity_right]

theorem capture_solution {source target : Object S}
    (assignment : Assignment source.2.arity target.2.arity) (substitution : Substitution S) :
    (action S Rigid).Solves substitution (capture target assignment,anchor source) ↔
      (Environment.mk source.2 (substitution target).1
        (Assignment.compose (substitution target).2 assignment)) =
      Environment.mk source.2 (substitution source).1 (substitution source).2 := by
  change apply S substitution (capture target assignment : Value S Rigid) =
    apply S substitution (anchor source) ↔ _
  rw [apply_anchor]
  change Value.environment _ = Value.environment _ ↔ _
  exact ⟨Value.environment.inj,congrArg Value.environment⟩

theorem capture_targets {source target : Object S}
    (assignment : Assignment source.2.arity target.2.arity) (substitution : Substitution S)
    (solved : (action S Rigid).Solves substitution (capture target assignment,anchor source)) :
    (substitution target).1 = (substitution source).1 :=
  congrArg Environment.target ((capture_solution assignment substitution).mp solved)

theorem capture_assignment {source target : Object S}
    (assignment : Assignment source.2.arity target.2.arity) (substitution : Substitution S)
    (solved : (action S Rigid).Solves substitution (capture target assignment,anchor source)) :
    HEq (Assignment.compose (substitution target).2 assignment) (substitution source).2 := by
  exact Environment.assignment_heq S ((capture_solution assignment substitution).mp solved)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.ContextPackets
