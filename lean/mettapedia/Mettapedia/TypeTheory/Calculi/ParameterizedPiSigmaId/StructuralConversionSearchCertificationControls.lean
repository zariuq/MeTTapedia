import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSearchProjection

/-!
# Bounded conversion production controls

Beta reduction and a one-edge declared computation both retain accepted
recipes. A deliberately indiscriminate root search cannot apply that edge at
a different source. Altered output claims are rejected by the original
checker. Zero fuel retains a reducible source, witnessing the distinction
between an accepted candidate and a normal form.
The exact projection keeps these outputs and the dependence on fuel.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.StructuralConversionSearch.CertificationControls

open StructuralConversionCode

inductive RootCode (_ : Nat) where
  | zeroToOne

def computation : RootComputation Nat where
  step := fun {_} left right => left = .head 0 ∧ right = .head 1
  rename := by
    intro n m rho left right step
    rcases step with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  substitute := by
    intro n m sigma left right step
    rcases step with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

def decoder : RootDecoder computation where
  Code := RootCode
  decode := fun {_} _ => some (.head 0, .head 1)
  sound := by
    intro n code left right accepted
    cases code
    cases accepted
    exact ⟨rfl, rfl⟩
  complete := by
    intro n left right step
    rcases step with ⟨rfl, rfl⟩
    exact ⟨.zeroToOne, rfl⟩

def indiscriminateSearch {n : Nat} (_term : Tm Nat n) : Option (decoder.Code n) :=
  some .zeroToOne

def beta : Tm Nat 0 := .app (.lam (.var 0)) (.head 2)

def betaCandidate := produce decoder.decode indiscriminateSearch 4 beta

theorem beta_output : betaCandidate.term = .head 2 := by decide +kernel

theorem beta_checked :
    betaCandidate.recipe.check Eq decoder.decode beta (.head 2) = true := by
  rw [← beta_output]
  exact produce_checked Eq decoder.decode indiscriminateSearch 4 beta

theorem beta_wrong_output_refused :
    betaCandidate.recipe.check Eq decoder.decode beta (.head 3) = false := by
  decide +kernel

theorem normalization_keeps_candidate :
    normalize decoder indiscriminateSearch (headEq := Eq) 4 beta = some betaCandidate :=
  normalize_eq_some_produce Eq decoder indiscriminateSearch 4 beta

theorem zero_fuel_keeps_redex :
    (produce decoder.decode indiscriminateSearch 0 beta).term = beta := rfl

theorem zero_fuel_result_differs :
    (produce decoder.decode indiscriminateSearch 0 beta).term ≠ betaCandidate.term := by
  rw [zero_fuel_keeps_redex, beta_output]
  decide

theorem declared_output :
    (produce decoder.decode indiscriminateSearch 4 (.head 0 : Tm Nat 0)).term = .head 1 := by
  decide +kernel

theorem declared_recipe_checked :
    (produce decoder.decode indiscriminateSearch 4 (.head 0 : Tm Nat 0)).recipe.check
      Eq decoder.decode (.head 0) (.head 1) = true := by
  rw [← declared_output]
  exact produce_checked Eq decoder.decode indiscriminateSearch 4 (.head 0 : Tm Nat 0)

theorem mismatched_root_is_not_used :
    (produce decoder.decode indiscriminateSearch 4 (.head 2 : Tm Nat 0)).term = .head 2 := by
  decide +kernel

theorem mismatched_root_output_refused :
    (produce decoder.decode indiscriminateSearch 4 (.head 2 : Tm Nat 0)).recipe.check
      Eq decoder.decode (.head 2) (.head 1) = false := by
  decide +kernel

theorem beta_projection :
    termProjection decoder.decode indiscriminateSearch 4 beta = .head 2 := by
  rw [← produce_term]
  exact beta_output

theorem beta_projection_excludes_wrong_output :
    termProjection decoder.decode indiscriminateSearch 4 beta ≠ .head 3 := by
  rw [beta_projection]
  decide

theorem declared_projection :
    termProjection decoder.decode indiscriminateSearch 4 (.head 0 : Tm Nat 0) = .head 1 := by
  rw [← produce_term]
  exact declared_output

theorem mismatched_root_projection :
    termProjection decoder.decode indiscriminateSearch 4 (.head 2 : Tm Nat 0) = .head 2 := by
  rw [← produce_term]
  exact mismatched_root_is_not_used

theorem projection_retains_fuel_dependence :
    termProjection decoder.decode indiscriminateSearch 0 beta ≠
      termProjection decoder.decode indiscriminateSearch 4 beta := by
  rw [← produce_term, ← produce_term]
  exact zero_fuel_result_differs

#print axioms beta_checked
#print axioms beta_wrong_output_refused
#print axioms normalization_keeps_candidate
#print axioms zero_fuel_result_differs
#print axioms declared_recipe_checked
#print axioms mismatched_root_output_refused
#print axioms beta_projection
#print axioms beta_projection_excludes_wrong_output
#print axioms projection_retains_fuel_dependence

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.StructuralConversionSearch.CertificationControls
