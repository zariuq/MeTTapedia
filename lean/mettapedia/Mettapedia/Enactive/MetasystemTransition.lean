import Mettapedia.Cybernetics.ConstrainedVariety
import Mettapedia.Enactive.CompletionFibre
import Mettapedia.Enactive.PrimeGeneration

/-!
# Metasystem transitions as constrained variation of constraints

Heylighen's refinement of Valentin Turchin's programme distinguishes a
metasystem from a supersystem: a supersystem may merely collect object
systems, whereas a metasystem constrains witnessed variation of the
constraints that individuate those object systems.  Consequently the
proof-relevant change relation is primary here.  An external selector is
optional structure and cannot manufacture a transition without change
evidence.

Task generations are not inferred from systems language alone.  An explicit
task interpretation must prove that each admitted constraint change is a
strict child-to-parent step; only then is a Bennett generation derived.

References:

- V. Turchin, *The Phenomenon of Science* (1977).
- F. Heylighen, *(Meta)Systems as Constraints on Variation* (1995), especially
  the definition of a metasystem as constrained variation of constrained
  varieties and the distinction between constraint and external control.
-/

set_option autoImplicit false

namespace Mettapedia.Enactive.MetasystemTransition

open Mettapedia.Cybernetics
open Mettapedia.Enactive

universe uState uWitness uController uWorld

/-! ## General metasystem structure -/

/-- A metasystem over object states.  Its states at the meta-level are the
constraints that define admissible object-state varieties. -/
structure Metasystem (State : Type uState) where
  admittedSystems : Set (Constraint State)
  Change : Constraint State → Constraint State → Type uWitness
  source_admitted : ∀ {source target}, Change source target →
    source ∈ admittedSystems
  target_admitted : ∀ {source target}, Change source target →
    target ∈ admittedSystems
  constrained : ∃ rejected : Constraint State,
    rejected ∉ admittedSystems

namespace Metasystem

variable {State : Type uState}
  (metasystem : Metasystem.{uState, uWitness} State)

/-- A realized metasystem transition changes the constraint defining the
object system and retains the witness of that change. -/
structure Transition : Type (max uState uWitness) where
  source : Constraint State
  target : Constraint State
  evidence : metasystem.Change source target
  changesConstraint : source ≠ target

namespace Transition

variable {metasystem : Metasystem.{uState, uWitness} State}

theorem source_admitted (transition : metasystem.Transition) :
    transition.source ∈ metasystem.admittedSystems :=
  metasystem.source_admitted transition.evidence

theorem target_admitted (transition : metasystem.Transition) :
    transition.target ∈ metasystem.admittedSystems :=
  metasystem.target_admitted transition.evidence

end Transition

/-- A structurally separate selector.  It is deliberately weaker than a
metasystem transition: `select` need not witness any constraint change. -/
structure ExternalSelector : Type (max uState (uController + 1)) where
  Controller : Type uController
  select : Controller → Constraint State
  selected_admitted : ∀ controller,
    select controller ∈ metasystem.admittedSystems

/-- If the change relation has no inhabitants, no realized metasystem
transition exists, independently of any static aggregation or selector. -/
theorem noTransition_of_noChange
    (noChange : ∀ source target, IsEmpty (metasystem.Change source target)) :
    IsEmpty metasystem.Transition :=
  ⟨fun transition =>
    (noChange transition.source transition.target).false transition.evidence⟩

end Metasystem

/-! ## Completion fibres are constraint fibres -/

namespace Completion

variable {World : Type uWorld} {layer : AbstractionLayer World}

/-- Bennett's principal completion cone, regarded as a constraint on possible
target aspects. -/
def asConstraint (source : Aspect layer) : Constraint (Aspect layer) :=
  Mettapedia.Enactive.Completion.extension source

/-- The abstract constraint fibre is exactly the existing typed completion
fibre. -/
def fibreEquiv (source : Aspect layer) :
    Constraint.Fibre (asConstraint source) ≃
      Mettapedia.Enactive.Completion.Fibre source where
  toFun completion :=
    ⟨completion.1,
      Mettapedia.Enactive.Completion.mem_extension.mp completion.2⟩
  invFun completion :=
    ⟨completion.1,
      Mettapedia.Enactive.Completion.mem_extension.mpr completion.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Completion

/-! ## Earned task-generation interpretation -/

/-- An interpretation of every admitted metasystem change as a strict task
refinement. -/
structure TaskInterpretation
    {State : Type uState} (metasystem : Metasystem.{uState, uWitness} State)
    {World : Type uWorld} (layer : AbstractionLayer World) where
  task : Constraint State → Task layer
  change_isChild : ∀ {source target}, metasystem.Change source target →
    (task source).IsChild (task target)

namespace TaskInterpretation

variable {State : Type uState}
  {metasystem : Metasystem.{uState, uWitness} State}
  {World : Type uWorld} {layer : AbstractionLayer World}

/-- One realized metasystem transition introduces one task generation, but
only under the explicit task interpretation. -/
def generation (interpretation : TaskInterpretation metasystem layer)
    (transition : metasystem.Transition) :
    Task.Generation 1
      (interpretation.task transition.source)
      (interpretation.task transition.target) :=
  Task.Generation.step
    (interpretation.change_isChild transition.evidence)
    (Task.Generation.refl (interpretation.task transition.target))

end TaskInterpretation

/-! ## Positive transition and insufficiency controls -/

namespace Canary

def unrestricted : Constraint Bool := Set.univ

def requireTrue : Constraint Bool := {state | state = true}

def requireFalse : Constraint Bool := {state | state = false}

theorem unrestricted_ne_requireTrue : unrestricted ≠ requireTrue := by
  intro equal
  have member : false ∈ requireTrue := by
    rw [← equal]
    trivial
  simp [requireTrue] at member

theorem requireTrue_ne_unrestricted : requireTrue ≠ unrestricted :=
  Ne.symm unrestricted_ne_requireTrue

theorem requireFalse_ne_unrestricted : requireFalse ≠ unrestricted := by
  intro equal
  have member : true ∈ requireFalse := by
    rw [equal]
    trivial
  simp [requireFalse] at member

theorem requireFalse_ne_requireTrue : requireFalse ≠ requireTrue := by
  intro equal
  have member : false ∈ requireTrue := by
    rw [← equal]
    simp [requireFalse]
  simp [requireTrue] at member

def admittedSystems : Set (Constraint Bool) :=
  {constraint | constraint = unrestricted ∨ constraint = requireTrue}

inductive Change : Constraint Bool → Constraint Bool → Type where
  | organize : Change unrestricted requireTrue

/-- A scale-one positive example: the constraint on Bool states itself
changes from unrestricted to `requireTrue`. -/
def metasystem : Metasystem Bool where
  admittedSystems := admittedSystems
  Change := Change
  source_admitted := by
    intro source target change
    cases change
    exact Or.inl rfl
  target_admitted := by
    intro source target change
    cases change
    exact Or.inr rfl
  constrained := by
    refine ⟨requireFalse, ?_⟩
    rintro (equal | equal)
    · exact requireFalse_ne_unrestricted equal
    · exact requireFalse_ne_requireTrue equal

def transition : metasystem.Transition where
  source := unrestricted
  target := requireTrue
  evidence := .organize
  changesConstraint := unrestricted_ne_requireTrue

/-- The same static collection of object systems, but with no dynamic
variation.  This is the aggregate/supersystem negative control. -/
def rigidCollection : Metasystem Bool where
  admittedSystems := admittedSystems
  Change := fun _ _ => Empty
  source_admitted := fun change => nomatch change
  target_admitted := fun change => nomatch change
  constrained := metasystem.constrained

/-- A separate selector can exist over the rigid collection. -/
def rigidSelector : rigidCollection.ExternalSelector where
  Controller := Unit
  select := fun _ => unrestricted
  selected_admitted := fun _ => Or.inl rfl

/-- Static aggregation plus a separate selector still supplies no transition
when there is no witnessed variation of constraints. -/
theorem aggregation_and_selector_are_insufficient :
    Nonempty (Metasystem.ExternalSelector.{0, 0, 0} rigidCollection) ∧
      IsEmpty rigidCollection.Transition := by
  refine ⟨⟨rigidSelector⟩, ?_⟩
  exact rigidCollection.noTransition_of_noChange
    (fun _ _ => ⟨fun evidence => nomatch evidence⟩)

noncomputable def taskOf (constraint : Constraint Bool) :
    Task (AbstractionLayer.full Bool) :=
  if constraint = unrestricted then
    PrimeGeneration.Canary.childTask
  else
    PrimeGeneration.Canary.parentTask

noncomputable def interpretation :
    TaskInterpretation metasystem (AbstractionLayer.full Bool) where
  task := taskOf
  change_isChild := by
    intro source target change
    cases change
    simp only [taskOf, if_neg requireTrue_ne_unrestricted]
    exact PrimeGeneration.Canary.child_isChild_parent

@[simp] theorem taskOf_unrestricted :
    taskOf unrestricted = PrimeGeneration.Canary.childTask := by
  simp [taskOf]

@[simp] theorem taskOf_requireTrue :
    taskOf requireTrue = PrimeGeneration.Canary.parentTask := by
  simp [taskOf, requireTrue_ne_unrestricted]

/-- The positive metasystem transition earns the existing nontrivial Bennett
generation after, and only after, the task interpretation is supplied. -/
def interpretedGeneration :
    Task.Generation 1 PrimeGeneration.Canary.childTask
      PrimeGeneration.Canary.parentTask := by
  simpa [interpretation, transition, taskOf,
    requireTrue_ne_unrestricted] using
      interpretation.generation transition

end Canary

end Mettapedia.Enactive.MetasystemTransition

#print axioms Mettapedia.Enactive.MetasystemTransition.Completion.fibreEquiv
#print axioms Mettapedia.Enactive.MetasystemTransition.Canary.aggregation_and_selector_are_insufficient
#print axioms Mettapedia.Enactive.MetasystemTransition.Canary.interpretedGeneration
