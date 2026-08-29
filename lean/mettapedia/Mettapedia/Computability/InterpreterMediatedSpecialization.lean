import Mettapedia.Computability.PartialEvaluation
import Mettapedia.Enactive.MetasystemTransition

/-!
# Interpreter-mediated specialization

Turchin's interpreter-mediated transformation inserts an explicit
interpretive layer between a transformer and the subject program.  The
transformer is applied to an interpreter together with a formal description
of the subject program's computation histories, rather than directly to the
subject program.

This module isolates the specialization fragment of that construction.  A
proved interpreter presentation gives the equation

`evaluate interpreter (historyCode program, input) = evaluate program input`.

Specializing the interpreter to `historyCode program` then yields residual
code extensionally equivalent to the direct program.  The interpretive lift
also induces a proof-relevant transition between direct-program and
interpreted-history control constraints in the existing metasystem theory.

No claim of full supercompilation is made here: driving, generalization,
whistles, finite configuration closure, and transformation quality remain
separate obligations.

References:

- V. Turchin, *Program Transformation with Metasystem Transitions* (1993).
- V. Turchin, *Metacomputation: Metasystem Transitions plus
  Supercompilation* (1996).
- Y. Futamura, *Partial Evaluation of Computation Process—An Approach to a
  Compiler-Compiler* (1971; English retrospective edition 1999).
-/

set_option autoImplicit false

namespace Mettapedia.Computability.InterpreterMediatedSpecialization

open Mettapedia.Computability.PartialEvaluation
open Mettapedia.Cybernetics
open Mettapedia.Enactive.MetasystemTransition

universe uCode

/-- A formal history description and an interpreter proved extensionally
correct for it.  Keeping the history encoder explicit distinguishes an added
interpretive level from direct specialization of the subject program. -/
structure InterpreterPresentation {Code : Type uCode}
    (system : SelfApplicableSpecializer Code) where
  historyCode : Code → Code
  interpreterCode : Code
  interprets : ∀ program input,
    system.evaluate interpreterCode (system.pair (historyCode program) input) =
      system.evaluate program input

namespace InterpreterPresentation

variable {Code : Type uCode} {system : SelfApplicableSpecializer Code}

/-- Residualize the interpreter with respect to the formal computation-history
description of one subject program. -/
def residualProgram (presentation : InterpreterPresentation system)
    (program : Code) : Code :=
  system.specialize presentation.interpreterCode
    (presentation.historyCode program)

/-- Interpreter-mediated specialization preserves the subject program's
extensional behavior on every remaining input. -/
theorem evaluate_residualProgram
    (presentation : InterpreterPresentation system)
    (program input : Code) :
    system.evaluate (presentation.residualProgram program) input =
      system.evaluate program input := by
  calc
    system.evaluate (presentation.residualProgram program) input =
        system.evaluate presentation.interpreterCode
          (system.pair (presentation.historyCode program) input) :=
      system.specialization_correct presentation.interpreterCode
        (presentation.historyCode program) input
    _ = system.evaluate program input :=
      presentation.interprets program input

end InterpreterPresentation

/-! ## The added interpretive control level as a metasystem transition -/

/-- A direct program and a formal interpreted history occupy distinct control
levels even when both are represented in one code language. -/
inductive ControlState (Code : Type uCode) where
  | direct : Code → ControlState Code
  | interpreted : Code → ControlState Code
deriving DecidableEq

namespace ControlState

variable {Code : Type uCode}

/-- States controlled directly by a subject program. -/
def directConstraint : Constraint (ControlState Code) :=
  { state | ∃ program, state = .direct program }

/-- States controlled through a formal interpreted-history description. -/
def interpretedConstraint : Constraint (ControlState Code) :=
  { state | ∃ history, state = .interpreted history }

theorem directConstraint_ne_interpretedConstraint [Nonempty Code] :
    (directConstraint : Constraint (ControlState Code)) ≠
      interpretedConstraint := by
  obtain ⟨code⟩ := ‹Nonempty Code›
  intro equal
  have member : ControlState.direct code ∈
      (interpretedConstraint : Constraint (ControlState Code)) := by
    rw [← equal]
    exact ⟨code, rfl⟩
  simp [interpretedConstraint] at member

theorem univ_ne_directConstraint [Nonempty Code] :
    (Set.univ : Constraint (ControlState Code)) ≠ directConstraint := by
  obtain ⟨code⟩ := ‹Nonempty Code›
  intro equal
  have member : ControlState.interpreted code ∈
      (directConstraint : Constraint (ControlState Code)) := by
    rw [← equal]
    trivial
  simp [directConstraint] at member

theorem univ_ne_interpretedConstraint [Nonempty Code] :
    (Set.univ : Constraint (ControlState Code)) ≠ interpretedConstraint := by
  obtain ⟨code⟩ := ‹Nonempty Code›
  intro equal
  have member : ControlState.direct code ∈
      (interpretedConstraint : Constraint (ControlState Code)) := by
    rw [← equal]
    trivial
  simp [interpretedConstraint] at member

end ControlState

/-- A change of control level is admitted only when accompanied by a proved
interpreter presentation. -/
inductive ControlChange {Code : Type uCode}
    (system : SelfApplicableSpecializer Code) :
    Constraint (ControlState Code) → Constraint (ControlState Code) → Type uCode
  | interpretive (presentation : InterpreterPresentation system) :
      ControlChange system ControlState.directConstraint
        ControlState.interpretedConstraint

/-- The two admitted control levels and their proof-relevant interpretive
lift.  The unrelated universal constraint is excluded, so this is a genuine
constrained metasystem rather than a renamed unconstrained relation. -/
def controlMetasystem {Code : Type uCode} [Nonempty Code]
    (system : SelfApplicableSpecializer Code) :
    Metasystem (ControlState Code) where
  admittedSystems :=
    { constraint |
      constraint = ControlState.directConstraint ∨
        constraint = ControlState.interpretedConstraint }
  Change := ControlChange system
  source_admitted := by
    intro source target change
    cases change
    exact Or.inl rfl
  target_admitted := by
    intro source target change
    cases change
    exact Or.inr rfl
  constrained := by
    refine ⟨Set.univ, ?_⟩
    rintro (equal | equal)
    · exact ControlState.univ_ne_directConstraint equal
    · exact ControlState.univ_ne_interpretedConstraint equal

/-- A proved interpreter presentation realizes the corresponding change of
control constraint. -/
def controlTransition {Code : Type uCode} [Nonempty Code]
    {system : SelfApplicableSpecializer Code}
    (presentation : InterpreterPresentation system) :
    (controlMetasystem system).Transition where
  source := ControlState.directConstraint
  target := ControlState.interpretedConstraint
  evidence := .interpretive presentation
  changesConstraint :=
    ControlState.directConstraint_ne_interpretedConstraint

/-- Without any semantically valid interpreter presentation, the canonical
control metasystem has no realized transition.  Merely naming direct and
interpreted control levels cannot manufacture the missing lift. -/
theorem noControlTransition_of_noInterpreterPresentation
    {Code : Type uCode} [Nonempty Code]
    (system : SelfApplicableSpecializer Code)
    (noPresentation : IsEmpty (InterpreterPresentation system)) :
    IsEmpty (controlMetasystem system).Transition := by
  apply (controlMetasystem system).noTransition_of_noChange
  intro source target
  refine ⟨fun change => ?_⟩
  cases change with
  | interpretive presentation => exact noPresentation.false presentation

/-! ## Nondegenerate model and failing-interpreter control -/

namespace Canary

/-- Explicit residual, history, specializer, and interpreter syntax. -/
inductive Code where
  | literal : Nat → Code
  | pair : Code → Code → Code
  | history : Code → Code
  | residual : Code → Code → Code
  | specializer : Code
  | interpreter : Code
  | result : Code → Code → Code
deriving DecidableEq, Repr

instance : Nonempty Code := ⟨.literal 0⟩

/-- Executing the represented interpreter consumes a history description;
executing residual code supplies its stored static input. -/
def evaluate : Code → Code → Code
  | .residual program static, dynamic =>
      evaluate program (.pair static dynamic)
  | .specializer, .pair program static => .residual program static
  | .interpreter, .pair (.history program) input => evaluate program input
  | program, input => .result program input
termination_by program input =>
  (sizeOf program + sizeOf input, sizeOf program)
decreasing_by all_goals simp_wf; omega

def system : SelfApplicableSpecializer Code where
  pair := .pair
  evaluate := evaluate
  specialize := .residual
  specializerCode := .specializer
  specialization_correct := by
    intro program static dynamic
    simp [evaluate]
  self_application_correct := by
    intro program static
    simp [evaluate]

/-- A non-identity history representation with an explicit interpreter. -/
def presentation : InterpreterPresentation system where
  historyCode := .history
  interpreterCode := .interpreter
  interprets := by
    intro program input
    simp [system, evaluate]

theorem mediated_example :
    system.evaluate
        (presentation.residualProgram (.literal 5)) (.literal 7) =
      system.evaluate (.literal 5) (.literal 7) := by
  exact presentation.evaluate_residualProgram (.literal 5) (.literal 7)

/-- The residualized interpreter is syntactically distinct from the direct
subject program in the model. -/
theorem residualProgram_ne_direct :
    presentation.residualProgram (.literal 5) ≠ .literal 5 := by
  decide

/-- A literal used as a would-be interpreter does not interpret the encoded
history and therefore cannot supply an `InterpreterPresentation`. -/
theorem literal_not_interpreter :
    ¬ ∀ program input,
      system.evaluate (.literal 0)
          (system.pair (.history program) input) =
        system.evaluate program input := by
  intro alleged
  have contradiction := alleged (.literal 1) (.literal 2)
  simp [system, evaluate] at contradiction

/-- The nondegenerate presentation also supplies a genuine proof-relevant
metasystem transition. -/
def transition : (controlMetasystem system).Transition :=
  controlTransition presentation

end Canary

end Mettapedia.Computability.InterpreterMediatedSpecialization

#print axioms Mettapedia.Computability.InterpreterMediatedSpecialization.InterpreterPresentation.evaluate_residualProgram
#print axioms Mettapedia.Computability.InterpreterMediatedSpecialization.ControlState.directConstraint_ne_interpretedConstraint
#print axioms Mettapedia.Computability.InterpreterMediatedSpecialization.noControlTransition_of_noInterpreterPresentation
#print axioms Mettapedia.Computability.InterpreterMediatedSpecialization.Canary.mediated_example
#print axioms Mettapedia.Computability.InterpreterMediatedSpecialization.Canary.residualProgram_ne_direct
#print axioms Mettapedia.Computability.InterpreterMediatedSpecialization.Canary.literal_not_interpreter
