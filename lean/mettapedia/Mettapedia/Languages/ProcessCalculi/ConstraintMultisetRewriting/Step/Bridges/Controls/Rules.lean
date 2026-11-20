import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Rules
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Typing.Programs

/-!
# The typed vector program crosses the actual rule-program bridge

Append's empty clause and the vector's first-element rule are both executed.
The received dependent run has exactly two firings and the independently
specified final state. The rigid-package control shows why the rule's answer
typing certificate cannot be inferred from step admission alone.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Rules

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open RuleSyntax.Dependent
open RuleSyntax.Typing.Programs

def syntaxPath (K : Package) : ExecutionPath
    (Execution.theory (Bridges.Rules.syntaxProgram (O := Nat) K.levels (program K)))
    (start K) (secondResult K) :=
  .cons ⟨⟨firstFiring K, firstFiring_admitted K, rfl⟩⟩
    (.cons ⟨⟨secondFiring K, secondFiring_admitted K, rfl⟩⟩ (.refl _))

def nativePath (K : Package) : ExecutionPath
    (Execution.theory (Bridges.Rules.dependentProgram (O := Nat) K.levels (program K)))
    (ofState (start K)) (ofState (secondResult K)) :=
  (Bridges.Rules.syntaxTranslation K.levels (program K)).mapRoute (syntaxPath K)

theorem two_actual_firings (K : Package) :
    ∃ run : (Bridges.Rules.dependentProgram (O := Nat) K.levels (program K)).Run (ofState (start K)),
      run.last = ofState (secondResult K) ∧ run.word.length = 2 := by
  obtain ⟨run, endpoint, length⟩ := Execution.path_has_run _ (nativePath K)
  refine ⟨run, endpoint, length.trans ?_⟩
  exact (Bridges.Rules.syntaxTranslation K.levels (program K)).mapRoute_length (syntaxPath K)

theorem declared_two_actual_firings :
    ∃ run : (Bridges.Rules.dependentProgram (O := Nat) declared.levels (program declared)).Run
        (ofState (start declared)),
      run.last = ofState (secondResult declared) ∧ run.word.length = 2 :=
  two_actual_firings declared

/-- The same physical run exists without the declared conversion, while
the corresponding answer-type promise is false in that package. -/
theorem rigid_admission_does_not_supply_answer_typing :
    (∃ run : (Bridges.Rules.dependentProgram (O := Nat) rigid.levels (program rigid)).Run
        (ofState (start rigid)),
      run.last = ofState (secondResult rigid) ∧ run.word.length = 2) ∧
      ¬ RuleSyntax.Typing.WellTypedRule rigid.levels (appendNil rigid) [some 0] :=
  ⟨two_actual_firings rigid, rigid_appendNil_not_wellTyped⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Rules

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Rules.declared_two_actual_firings
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Rules.rigid_admission_does_not_supply_answer_typing
