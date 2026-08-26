import Mettapedia.Computability.KolmogorovComplexity.Conditional

/-!
# Directional algorithmic information

For a fixed reference machine, the expression

`K(target) - K(target | condition)`

has an oriented target and condition.  Swapping those arguments is not a
definitional rewrite.  This file supplies an executable prefix-free canary in
which one orientation is exactly zero and the reverse orientation is exactly
one bit.  Consequently, a theorem that needs the reverse orientation must
either assume it, or invoke a proved symmetry-of-information bound.

The canary is deliberately finite and is not presented as a universal machine.
Its role is to reject an invalid algebraic interchange before any asymptotic
properties of a universal reference machine are used.
-/

namespace KolmogorovComplexity

open scoped Classical

namespace DirectionalInformationCanary

def parameter : BinString := [false, false]

def model : BinString := [true, true]

/-- A finite conditional prefix-free machine with asymmetric use of auxiliary
information.

Under the empty condition, both distinguished outputs require a one-bit
program.  Giving `model` does not shorten `parameter`, whereas giving
`parameter` makes `model` available from the empty program. -/
def machine : ConditionalPrefixFreeMachine where
  compute := fun program condition =>
    if condition = [] then
      if program = [false] then some parameter
      else if program = [true] then some model
      else none
    else if condition = model then
      if program = [false] then some parameter else none
    else if condition = parameter then
      if program = [] then some model else none
    else none
  prefix_free := by
    intro condition p q hpref hpq hp
    by_cases hcEmpty : condition = []
    · subst condition
      simp only [ite_true] at hp ⊢
      by_cases hpFalse : p = [false]
      · subst p
        have hqFalse : q ≠ [false] := by
          intro h
          exact hpq h.symm
        have hqTrue : q ≠ [true] := by
          intro h
          subst q
          rcases hpref with ⟨suffix, hsuffix⟩
          simp at hsuffix
        simp [hqFalse, hqTrue]
      · rw [if_neg hpFalse] at hp
        have hpTrue : p = [true] := by
          by_contra h
          simp [h] at hp
        subst p
        have hqTrue : q ≠ [true] := by
          intro h
          exact hpq h.symm
        have hqFalse : q ≠ [false] := by
          intro h
          subst q
          rcases hpref with ⟨suffix, hsuffix⟩
          simp at hsuffix
        simp [hqFalse, hqTrue]
    · rw [if_neg hcEmpty] at hp ⊢
      by_cases hcModel : condition = model
      · subst condition
        simp only [ite_true] at hp ⊢
        have hpFalse : p = [false] := by
          by_contra h
          simp [h] at hp
        subst p
        have hqFalse : q ≠ [false] := by
          intro h
          exact hpq h.symm
        simp [hqFalse]
      · rw [if_neg hcModel] at hp ⊢
        by_cases hcParameter : condition = parameter
        · subst condition
          simp only [ite_true] at hp ⊢
          have hpEmpty : p = [] := by
            by_contra h
            simp [h] at hp
          subst p
          have hqNonempty : q ≠ [] := by
            intro h
            exact hpq h.symm
          simp [hqNonempty]
        · simp [hcParameter] at hp

theorem hasParameterUnconditionally :
    HasProgram machine [] parameter := by
  exact ⟨[false], by simp [IsProgram, machine, parameter, model]⟩

theorem hasModelUnconditionally :
    HasProgram machine [] model := by
  exact ⟨[true], by simp [IsProgram, machine, parameter, model]⟩

theorem hasParameterGivenModel :
    HasProgram machine model parameter := by
  exact ⟨[false], by simp [IsProgram, machine, parameter, model]⟩

theorem hasModelGivenParameter :
    HasProgram machine parameter model := by
  exact ⟨[], by simp [IsProgram, machine, parameter, model]⟩

private theorem complexity_eq_one
    (condition output witness : BinString)
    (has : HasProgram machine condition output)
    (runs : IsProgram machine witness condition output)
    (witnessLength : witness.length = 1)
    (emptyDoesNotRun : ¬ IsProgram machine [] condition output) :
    Kc[machine](output | condition) = 1 := by
  apply Nat.le_antisymm
  · simpa [witnessLength] using
      conditionalComplexity_le_program_length machine condition output witness runs
  · by_contra h
    have hzero : Kc[machine](output | condition) = 0 := by omega
    obtain ⟨program, programRuns, programLength⟩ :=
      exists_program_of_conditionalComplexity machine condition output has
    have : program = [] := by
      apply List.eq_nil_of_length_eq_zero
      omega
    subst program
    exact emptyDoesNotRun programRuns

theorem parameter_unconditional_complexity :
    Kc[machine](parameter | []) = 1 := by
  apply complexity_eq_one [] parameter [false]
  · exact hasParameterUnconditionally
  · simp [IsProgram, machine, parameter, model]
  · simp
  · simp [IsProgram, machine, parameter, model]

theorem model_unconditional_complexity :
    Kc[machine](model | []) = 1 := by
  apply complexity_eq_one [] model [true]
  · exact hasModelUnconditionally
  · simp [IsProgram, machine, parameter, model]
  · simp
  · simp [IsProgram, machine, parameter, model]

theorem parameter_given_model_complexity :
    Kc[machine](parameter | model) = 1 := by
  apply complexity_eq_one model parameter [false]
  · exact hasParameterGivenModel
  · simp [IsProgram, machine, parameter, model]
  · simp
  · simp [IsProgram, machine, parameter, model]

theorem model_given_parameter_complexity :
    Kc[machine](model | parameter) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact conditionalComplexity_le_program_length machine parameter model []
    (by simp [IsProgram, machine, parameter, model])

/-- Information about `parameter` supplied by `model` is zero. -/
theorem model_about_parameter_zero :
    directedAlgorithmicInformation machine model parameter = 0 := by
  simp [directedAlgorithmicInformation, inducedPrefixComplexity,
    parameter_unconditional_complexity, parameter_given_model_complexity]

/-- Reversing target and condition produces one bit on the same machine. -/
theorem parameter_about_model_one :
    directedAlgorithmicInformation machine parameter model = 1 := by
  simp [directedAlgorithmicInformation, inducedPrefixComplexity,
    model_unconditional_complexity, model_given_parameter_complexity]

/-- The two orientations cannot be exchanged definitionally, even when the
first one satisfies the strongest possible zero-information premise. -/
theorem orientation_swap_invalid :
    directedAlgorithmicInformation machine model parameter = 0 ∧
    directedAlgorithmicInformation machine parameter model ≠ 0 := by
  exact ⟨model_about_parameter_zero, by simp [parameter_about_model_one]⟩

#print axioms orientation_swap_invalid

end DirectionalInformationCanary

end KolmogorovComplexity
