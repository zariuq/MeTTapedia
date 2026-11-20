import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Frames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualResidual

/-!
# A one-object action retaining contextual target frames

An observation retains its declaration frame and a tag. A substitution chooses
an actual contextual assignment at each tagged frame. Composition follows the
first assignment's target and composes the actual assignments there.

Restricting a substitution at one source recovers its original target frame
and assignment. Every such assignment has an extension to a substitution;
the values at other sources remain additional data. Thus this is no quotient
of contextual observations and uses no weakly terminal frame.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.TaggedAssignments

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable (S : Signature)

abbrev Object := Nat × Frames.Frame S

abbrev Packed := (source : Object S) × Observation S source.2.arity

abbrev Substitution := (source : Object S) →
  (target : Object S) × Assignment source.2.arity target.2.arity

def identity : Substitution S := fun source => ⟨source,generator source.2.arity⟩

def compose (outer inner : Substitution S) : Substitution S :=
  fun source => ⟨(outer (inner source).1).1,
    Assignment.compose (outer (inner source).1).2 (inner source).2⟩

def apply (substitution : Substitution S) : Packed S → Packed S
  | ⟨source,observation⟩ =>
      ⟨(substitution source).1,instantiateObservation (substitution source).2 observation⟩

theorem apply_identity (observation : Packed S) : apply S (identity S) observation = observation := by
  rcases observation with ⟨source,observation⟩
  change (⟨source,instantiateObservation (generator source.2.arity) observation⟩ : Packed S) =
    ⟨source,observation⟩
  rw [instantiateObservation_identity]

theorem apply_compose (outer inner : Substitution S) (observation : Packed S) :
    apply S (compose S outer inner) observation = apply S outer (apply S inner observation) := by
  rcases observation with ⟨source,observation⟩
  change (⟨(outer (inner source).1).1,
    instantiateObservation (Assignment.compose (outer (inner source).1).2 (inner source).2) observation⟩ : Packed S) = _
  rw [← instantiateObservation_comp]
  rfl

def action : SubstitutionAction (Packed S) (Substitution S) where
  E := Eq
  equivalence := ⟨Eq.refl,Eq.symm,Eq.trans⟩
  apply := apply S
  identity := identity S
  compose := compose S
  apply_identity := apply_identity S
  apply_compose := apply_compose S
  preserves := fun substitution {_ _} equal => congrArg (apply S substitution) equal

variable {S}

def pack (source : Object S) (observation : Observation S source.2.arity) : Packed S :=
  ⟨source,observation⟩

theorem pack_injective (source : Object S) : Function.Injective (pack source) :=
  fun _ _ equal => eq_of_heq (Sigma.mk.inj equal).2

theorem apply_pack (substitution : Substitution S) (source : Object S)
    (observation : Observation S source.2.arity) :
    apply S substitution (pack source observation) =
      pack (substitution source).1 (instantiateObservation (substitution source).2 observation) := rfl

def packProblem (source : Object S) (problem : ContextualResidual.Problem source.2.arity) :
    EquationStore (Packed S) :=
  problem.map fun equation => (pack source equation.1,pack source equation.2)

theorem models_pack (substitution : Substitution S) (source : Object S)
    (problem : ContextualResidual.Problem source.2.arity) :
    (action S).Models substitution (packProblem source problem) ↔
      ContextualResidual.Models (substitution source).2 problem := by
  constructor
  · intro solved equation present
    exact pack_injective (substitution source).1
      (solved _ (List.mem_map.mpr ⟨equation,present,rfl⟩))
  · intro solved equation present
    obtain ⟨original,inside,rfl⟩ := List.mem_map.mp present
    exact congrArg (pack (substitution source).1) (solved original inside)

/-- Extend one actual assignment; other sources keep their own names. -/
noncomputable def single (source target : Object S)
    (assignment : Assignment source.2.arity target.2.arity) : Substitution S := by
  classical
  intro current
  by_cases same : current = source
  · subst current
    exact ⟨target,assignment⟩
  · exact identity S current

theorem single_at (source target : Object S)
    (assignment : Assignment source.2.arity target.2.arity) :
    single source target assignment source = ⟨target,assignment⟩ := by
  classical
  simp [single]

theorem single_other (source target current : Object S)
    (assignment : Assignment source.2.arity target.2.arity) (different : current ≠ source) :
    single source target assignment current = identity S current := by
  classical
  simp [single,different]

theorem consistent_pack (source : Object S) (problem : ContextualResidual.Problem source.2.arity) :
    (action S).Consistent (packProblem source problem) ↔
      (Frames.contextual S).Solvable problem := by
  constructor
  · rintro ⟨substitution,solved⟩
    exact ⟨(substitution source).1.2,(substitution source).2,(models_pack substitution source problem).mp solved⟩
  · rintro ⟨target,assignment,solved⟩
    refine ⟨single source (0,target) assignment,(models_pack _ source problem).mpr ?_⟩
    rw [single_at source (0,target) assignment]
    exact solved

theorem entails_pack (source : Object S) (problem : ContextualResidual.Problem source.2.arity)
    (observation : (target : Frames.Frame S) → Assignment source.2.arity target.arity → Prop) :
    (action S).Entails (packProblem source problem)
        (fun substitution => observation (substitution source).1.2 (substitution source).2) ↔
      (Frames.contextual S).Entails problem observation := by
  constructor
  · intro asked target assignment solved
    have model : (action S).Models (single source (0,target) assignment) (packProblem source problem) :=
      (models_pack _ source problem).mpr (by
        rw [single_at source (0,target) assignment]
        exact solved)
    have holds := asked _ model
    dsimp only at holds
    rw [single_at source (0,target) assignment] at holds
    exact holds
  · intro asked substitution solved
    exact asked _ _ ((models_pack substitution source problem).mp solved)

theorem compose_at (outer inner : Substitution S) (source : Object S) :
    (compose S outer inner source).1 = (outer (inner source).1).1 ∧
      (compose S outer inner source).2 =
        Assignment.compose (outer (inner source).1).2 (inner source).2 := ⟨rfl,rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.TaggedAssignments
