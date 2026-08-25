import Mettapedia.Cybernetics.Individuation
import Mettapedia.Enactive.PrimeGeneration

/-!
# When an individuation process warrants a task generation

Closure does not itself manufacture a Bennett child relation.  A
`TaskInterpretation` is the missing semantic premise: it assigns a task to
each system state and proves that every selected individuation step is a
strict child-to-parent step.  Only then does a proof-relevant process induce a
task generation.
-/

set_option autoImplicit false

namespace Mettapedia.Enactive.IndividuationGeneration

open Mettapedia.Cybernetics
open Mettapedia.Enactive

universe uSystem uBoundary uStep uWorld

/-- An explicit task semantics for one individuation theory. -/
structure TaskInterpretation
    {System : Type uSystem} {Boundary : Type uBoundary}
    (theory : Individuation.Theory.{uSystem, uBoundary, uStep}
      System Boundary)
    {World : Type uWorld} (layer : AbstractionLayer World) where
  task : System → Task layer
  step_isChild : ∀ {first last}, theory.Step first last →
    (task first).IsChild (task last)

namespace TaskInterpretation

variable {System : Type uSystem} {Boundary : Type uBoundary}
  {theory : Individuation.Theory.{uSystem, uBoundary, uStep}
    System Boundary}
  {World : Type uWorld} {layer : AbstractionLayer World}

/-- The exact process length becomes the Bennett generation length. -/
def processGeneration (interpretation : TaskInterpretation theory layer)
    {steps : Nat} {first last : System}
    (process : Individuation.Process theory steps first last) :
    Task.Generation steps
      (interpretation.task first) (interpretation.task last) := by
  induction process with
  | refl state =>
      exact Task.Generation.refl (interpretation.task state)
  | @snoc steps first middle last history step historyGeneration =>
      have finalGeneration :
          Task.Generation 1
            (interpretation.task middle) (interpretation.task last) := by
        simpa using Task.Generation.step
          (interpretation.step_isChild step)
          (Task.Generation.refl (interpretation.task last))
      simpa using historyGeneration.append finalGeneration

end TaskInterpretation

/-! ## Positive and negative controls -/

namespace Canary

inductive Step : Bool → Bool → Type where
  | grow : Step false true

def theory : Individuation.Theory Bool Unit where
  Step := Step
  Closed := fun state _ => state = true
  Agrees := fun first last _ => first = last

def interpretation : TaskInterpretation theory
    (AbstractionLayer.full Bool) where
  task
    | false => PrimeGeneration.Canary.childTask
    | true => PrimeGeneration.Canary.parentTask
  step_isChild := by
    intro first last step
    cases step
    exact PrimeGeneration.Canary.child_isChild_parent

@[simp] theorem interpretation_task_false :
    interpretation.task false = PrimeGeneration.Canary.childTask := rfl

@[simp] theorem interpretation_task_true :
    interpretation.task true = PrimeGeneration.Canary.parentTask := rfl

def process : Individuation.Process theory 1 false true :=
  .snoc (.refl false) .grow

/-- A real interpreted individuation step yields the existing nontrivial
Bennett generation witness. -/
def interpretedGeneration :
    Task.Generation 1 PrimeGeneration.Canary.childTask
      PrimeGeneration.Canary.parentTask := by
  simpa [process,
    interpretation_task_false, interpretation_task_true] using
    interpretation.processGeneration process

/-- Even a statically closed singleton does not make a task its own child.
Thus closure without an explicit interpretation cannot create a generation. -/
theorem static_closure_does_not_make_generation
    {World : Type uWorld} {layer : AbstractionLayer World}
    (taskOf : Unit → Task layer) :
    ¬ (taskOf ()).IsChild (taskOf ()) :=
  Task.not_isChild_self (taskOf ())

end Canary

end Mettapedia.Enactive.IndividuationGeneration

#print axioms Mettapedia.Enactive.IndividuationGeneration.TaskInterpretation.processGeneration
#print axioms Mettapedia.Enactive.IndividuationGeneration.Canary.interpretedGeneration
#print axioms Mettapedia.Enactive.IndividuationGeneration.Canary.static_closure_does_not_make_generation
