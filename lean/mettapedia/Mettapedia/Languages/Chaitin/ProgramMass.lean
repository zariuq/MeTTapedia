import Mettapedia.Languages.Chaitin.ProgramInput
import Mettapedia.Computability.KolmogorovComplexity.PrefixMass

/-!
# Length weight of actual completed Lisp programs

A program is counted only when the historical entry expression returns a
successful value and consumes its entire supplied input. The streaming
semantics proves prefix-freeness; the existing Kraft development supplies
the mass bound. No universality or computability of this mass is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin

open scoped ENNReal

def completedPrograms : Set (List Bool) := {program | ∃ value, programOutputs program value}

theorem completedPrograms_prefix_free : KolmogorovComplexity.PrefixFree completedPrograms := by
  intro first firstMember second secondMember different isPrefix
  obtain ⟨firstValue, firstRun⟩ := firstMember
  obtain ⟨secondValue, secondRun⟩ := secondMember
  exact different (programOutputs_prefix_free firstRun secondRun isPrefix)

/-- Discrete length weight of completed programs, not a prediction measure. -/
noncomputable def completedProgramMass : ENNReal :=
  KolmogorovComplexity.prefixProgramMass completedPrograms

theorem completedProgramMass_le_one : completedProgramMass ≤ 1 :=
  KolmogorovComplexity.prefixProgramMass_le_one _ completedPrograms_prefix_free

/-- A concrete historical program supplies a nonempty domain witness. -/
theorem word_a_is_completed : Reader.bits (.symbol "a") ∈ completedPrograms := by
  refine ⟨.symbol "a", programOutputs_of_completed_pure Reader.read_a ?_⟩
  exact PureEvaluation.PureEval.atom cleanEnvironment (.symbol "a") rfl

/-- Appending a bit to a completed input does not produce a second completed
program: the evaluator leaves that bit unread. -/
theorem extended_word_a_is_not_completed (bit : Bool) :
    Reader.bits (.symbol "a") ++ [bit] ∉ completedPrograms := by
  rintro ⟨value, run⟩
  have same := programOutputs_prefix_free
    (show programOutputs (Reader.bits (.symbol "a")) (.symbol "a") from
      programOutputs_of_completed_pure Reader.read_a (PureEvaluation.PureEval.atom cleanEnvironment (.symbol "a") rfl))
    run (List.prefix_append _ _)
  have lengths := congrArg List.length same
  simp only [List.length_append, List.length_singleton] at lengths
  omega

end Mettapedia.Languages.Chaitin
