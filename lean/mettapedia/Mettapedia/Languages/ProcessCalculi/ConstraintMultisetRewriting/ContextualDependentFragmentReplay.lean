import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDynamicFragmentStore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentExecutableConversion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalizingCertify

/-!
# Bounded recognition of dynamic pattern equations

The tower sweep and the individual controls use the same bounded recognizer.
Once normalization finishes, confluence makes its result sufficient to classify
every normal reduct of the opened side.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDynamicFragment

open Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentPatternSolver (lamDepth)
open ContextualDependentExecutableJoin

/-- An opened side is in the fragment by the normalizer: it reaches a normal form with Miller occurrences at the
declared arities. -/
def sideInsideAt (fuel : Nat) {n : Nat} (context : Tower.Ctx n) (count : Nat) (code : Tower.Tm (n + count)) : Bool :=
  if finished : (ContextualDependentExecutableConversion.red (L := Nat) fuel code).isSome = true then
    (ExecutableReduction.step Tower.rules (fun _ => none)
        ((ContextualDependentExecutableConversion.red (L := Nat) fuel code).get finished).val).isNone &&
      decide (InFragmentCode context count
        ((ContextualDependentExecutableConversion.red (L := Nat) fuel code).get finished).val)
  else false

theorem sideInsideAt_iff_of_normalized {fuel n count : Nat} {context : Tower.Ctx n}
    {code : Tower.Tm (n + count)}
    (finished : (ContextualDependentExecutableConversion.red (L := Nat) fuel code).isSome = true) :
    sideInsideAt fuel context count code = true ↔
      ∀ normal, Star (R := Tower.rules) code normal → Normal Tower.rules normal →
        InFragmentCode context count normal := by
  have computed := (Option.some_get finished).symm
  have path := ContextualDependentExecutableConversion.normalize_star fuel computed
  have stopped := ContextualDependentReductionBudget.stopped_of_success Tower.rules (fun _ => none) computed
  have normal := (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr stopped
  simp only [sideInsideAt, dif_pos finished, stopped, Option.isNone_none, Bool.true_and, decide_eq_true_eq]
  exact ⟨side_of_normal_form rfl path normal, fun every => every _ path normal⟩

theorem sideInsideAt_sound {fuel n count : Nat} {context : Tower.Ctx n} {code : Tower.Tm (n + count)}
    (accepted : sideInsideAt fuel context count code = true) :
    ∀ normal, Star (R := Tower.rules) code normal → Normal Tower.rules normal →
      InFragmentCode context count normal := by
  by_cases finished : (ContextualDependentExecutableConversion.red (L := Nat) fuel code).isSome = true
  · exact (sideInsideAt_iff_of_normalized finished).mp accepted
  · simp [sideInsideAt, finished] at accepted

/-- **The membership test of an equation.** -/
def equationInsideAt (fuel : Nat) {Γ : Context Tower.rules} (equation : Equation (TotalTerm Γ)) : Bool :=
  decide (equation.2.1.code = equation.1.1.code) &&
    (ExecutableReduction.step Tower.rules (fun _ => none) equation.1.1.code).isNone &&
    decide (lamDepth equation.1.2.code ≤ piCount equation.1.1.code) &&
    sideInsideAt fuel Γ.raw (lamDepth equation.1.2.code) (openCode (lamDepth equation.1.2.code) equation.1.2.code) &&
    sideInsideAt fuel Γ.raw (lamDepth equation.1.2.code) (openCode (lamDepth equation.1.2.code) equation.2.2.code)

/-- **The membership test is sound** for the dynamic pattern fragment. -/
theorem equationInsideAt_sound {fuel : Nat} {Γ : Context Tower.rules} {equation : Equation (TotalTerm Γ)}
    (accepted : equationInsideAt fuel equation = true) : InFragment equation := by
  unfold equationInsideAt at accepted
  simp only [Bool.and_eq_true] at accepted
  obtain ⟨⟨⟨⟨same, normal⟩, depth⟩, left⟩, right⟩ := accepted
  refine ⟨?_, ?_, of_decide_eq_true depth, sideInsideAt_sound left, sideInsideAt_sound right⟩
  · rw [of_decide_eq_true same]
    exact IsType.refl equation.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (Option.isNone_iff_eq_none.mp normal)

/-- **The membership test of a store.** -/
def storeInsideAt (fuel : Nat) {Γ : Context Tower.rules} (store : EquationStore (TotalTerm Γ)) : Bool :=
  store.all (equationInsideAt fuel)

theorem storeInsideAt_sound {fuel : Nat} {Γ : Context Tower.rules} {store : EquationStore (TotalTerm Γ)}
    (accepted : storeInsideAt fuel store = true) : InFragmentStore store := fun equation member =>
  equationInsideAt_sound (List.all_eq_true.mp accepted equation member)

end ContextualDependentDynamicFragment
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
