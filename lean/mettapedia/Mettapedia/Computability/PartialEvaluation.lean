/-!
# Self-applicable specialization and the Futamura projections

A partial evaluator specializes a program with respect to static input and
returns residual code for the remaining dynamic input.  When the specializer
is represented in its own code language, repeated self-application yields the
three Futamura projections: object-program generation, compiler generation,
and compiler-generator generation.

This module isolates their total semantic equations.  It does not claim
termination, binding-time optimality, or a concrete compiler implementation;
those require separately proved instances.  A small residual-syntax model
validates the equations with distinct interpreters, compilers, and compiler
generators, while `badSpecialize` shows that arbitrary static-input erasure
does not qualify as specialization.

References:

- Y. Futamura, *Partial Evaluation of Computation Process—An Approach to a
  Compiler-Compiler* (1971; English retrospective edition 1999).
- N. D. Jones, C. K. Gomard, and P. Sestoft, *Partial Evaluation and Automatic
  Program Generation* (1993).
- V. Turchin, *Program Transformation with Metasystem Transitions* (1993), for
  the distinct interpreter-mediated supercompilation construction.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.PartialEvaluation

universe uCode

/-- A code language with a semantically correct self-applicable specializer.
`pair static dynamic` is the complete input expected by the unspecialized
program. -/
structure SelfApplicableSpecializer (Code : Type uCode) where
  pair : Code → Code → Code
  evaluate : Code → Code → Code
  specialize : Code → Code → Code
  specializerCode : Code
  specialization_correct : ∀ program static dynamic,
    evaluate (specialize program static) dynamic =
      evaluate program (pair static dynamic)
  self_application_correct : ∀ program static,
    evaluate specializerCode (pair program static) =
      specialize program static

namespace SelfApplicableSpecializer

variable {Code : Type uCode}
  (system : SelfApplicableSpecializer Code)

/-- The first projection specializes an interpreter with a source program. -/
def objectProgram (interpreter source : Code) : Code :=
  system.specialize interpreter source

/-- The second projection specializes the represented specializer with an
interpreter. -/
def compiler (interpreter : Code) : Code :=
  system.specialize system.specializerCode interpreter

/-- The third projection specializes the represented specializer with
itself. -/
def compilerGenerator : Code :=
  system.specialize system.specializerCode system.specializerCode

/-- First Futamura projection equation. -/
theorem first_projection (interpreter source runtime : Code) :
    system.evaluate (system.objectProgram interpreter source) runtime =
      system.evaluate interpreter (system.pair source runtime) :=
  system.specialization_correct interpreter source runtime

/-- The generated compiler returns the same residual program as direct
specialization of the interpreter. -/
theorem second_projection (interpreter source : Code) :
    system.evaluate (system.compiler interpreter) source =
      system.objectProgram interpreter source := by
  calc
    system.evaluate (system.compiler interpreter) source =
        system.evaluate system.specializerCode
          (system.pair interpreter source) :=
      system.specialization_correct system.specializerCode interpreter source
    _ = system.specialize interpreter source :=
      system.self_application_correct interpreter source
    _ = system.objectProgram interpreter source := rfl

/-- The generated compiler generator returns the generated compiler. -/
theorem compilerGenerator_produces_compiler (interpreter : Code) :
    system.evaluate system.compilerGenerator interpreter =
      system.compiler interpreter := by
  calc
    system.evaluate system.compilerGenerator interpreter =
        system.evaluate system.specializerCode
          (system.pair system.specializerCode interpreter) :=
      system.specialization_correct system.specializerCode
        system.specializerCode interpreter
    _ = system.specialize system.specializerCode interpreter :=
      system.self_application_correct system.specializerCode interpreter
    _ = system.compiler interpreter := rfl

/-- Third Futamura projection equation: the generated compiler generator,
applied to an interpreter and then a source, produces the same object program
as direct specialization. -/
theorem third_projection (interpreter source : Code) :
    system.evaluate
        (system.evaluate system.compilerGenerator interpreter) source =
      system.objectProgram interpreter source := by
  rw [system.compilerGenerator_produces_compiler interpreter]
  exact system.second_projection interpreter source

end SelfApplicableSpecializer

/-! ## Nondegenerate residual-syntax model and failing-specializer control -/

namespace ResidualSyntaxCanary

/-- A small code language with explicit residual programs and a represented
specializer. -/
inductive Code where
  | literal : Nat → Code
  | pair : Code → Code → Code
  | residual : Code → Code → Code
  | specializer : Code
  | result : Code → Code → Code
deriving DecidableEq, Repr

/-- Executing residual code supplies its stored static input.  Executing the
represented specializer on a pair constructs residual syntax. -/
def evaluate : Code → Code → Code
  | .residual program static, dynamic =>
      evaluate program (.pair static dynamic)
  | .specializer, .pair program static => .residual program static
  | program, input => .result program input

/-- The residual-syntax model of self-applicable specialization. -/
def system : SelfApplicableSpecializer Code where
  pair := .pair
  evaluate := evaluate
  specialize := .residual
  specializerCode := .specializer
  specialization_correct := by
    intro program static dynamic
    rfl
  self_application_correct := by
    intro program static
    rfl

theorem first_projection_example :
    system.evaluate
        (system.objectProgram (.literal 5) (.literal 7)) (.literal 11) =
      .result (.literal 5) (.pair (.literal 7) (.literal 11)) := by
  rfl

theorem second_projection_example :
    system.evaluate (system.compiler (.literal 5)) (.literal 7) =
      system.objectProgram (.literal 5) (.literal 7) := by
  rfl

theorem third_projection_example :
    system.evaluate
        (system.evaluate system.compilerGenerator (.literal 5)) (.literal 7) =
      system.objectProgram (.literal 5) (.literal 7) := by
  rfl

/-- Compiler generation is not an identity construction in the model. -/
theorem compiler_ne_interpreter :
    system.compiler (.literal 5) ≠ .literal 5 := by
  decide

/-- Compiler-generator generation is likewise distinct from the represented
specializer. -/
theorem compilerGenerator_ne_specializer :
    system.compilerGenerator ≠ system.specializerCode := by
  decide

/-- A candidate that discards the static input instead of incorporating it
into residual code. -/
def badSpecialize (program _static : Code) : Code := program

/-- Ignoring static input violates the specialization equation in the
residual-syntax model. -/
theorem badSpecialize_not_correct :
    ¬ ∀ program static dynamic : Code,
      system.evaluate (badSpecialize program static) dynamic =
        system.evaluate program (system.pair static dynamic) := by
  intro allegedCorrectness
  have contradiction := allegedCorrectness
    (.literal 1) (.literal 2) (.literal 3)
  simp [system, badSpecialize, evaluate] at contradiction

end ResidualSyntaxCanary

end Mettapedia.Computability.PartialEvaluation

#print axioms Mettapedia.Computability.PartialEvaluation.SelfApplicableSpecializer.first_projection
#print axioms Mettapedia.Computability.PartialEvaluation.SelfApplicableSpecializer.second_projection
#print axioms Mettapedia.Computability.PartialEvaluation.SelfApplicableSpecializer.third_projection
#print axioms Mettapedia.Computability.PartialEvaluation.ResidualSyntaxCanary.first_projection_example
#print axioms Mettapedia.Computability.PartialEvaluation.ResidualSyntaxCanary.compiler_ne_interpreter
#print axioms Mettapedia.Computability.PartialEvaluation.ResidualSyntaxCanary.badSpecialize_not_correct
