import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DefinitionalExpansion

/-!
# Dependent-pair conversion qualification

The pure conversion metatheory retains Sigma components and separates Sigma
from universe heads. Qualified closed constant expansions transfer these
facts to nonempty definition packages. These are the constructor laws needed
for projection preservation, not a termination theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation

variable {Head : Type} {n : Nat} {R : Rules Head}

structure SigmaConversionBoundary (R : Rules Head) : Prop where
  components {n : Nat} {A A' : Tm Head n} {B B' : Tm Head (n + 1)} :
    Conv R.headEq (.sigma A B) (.sigma A' B') R.computation →
      Conv R.headEq A A' R.computation ∧ Conv R.headEq B B' R.computation
  headDisjoint {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} {head : Head} :
    ¬ Conv R.headEq (.sigma A B) (.head head) R.computation

/-- Cumulativity cannot participate in an adjustment whose target conversion
class contains no head. This applies to both dependent functions and pairs. -/
theorem TypeAdjustment.toConvOfTargetDisjointHeads {source target : Tm Head n}
    (adjustment : TypeAdjustment R source target)
    (disjoint : ∀ head, ¬ Conv R.headEq target (.head head) R.computation) :
    Conv R.headEq source target R.computation := by
  induction adjustment with
  | refl type => exact .refl _
  | conversion conversion => exact conversion
  | cumulative order => exact False.elim (disjoint _ (.refl _))
  | @trans source middle target first second ihFirst ihSecond =>
      have secondConversion := ihSecond disjoint
      have middleDisjoint : ∀ head, ¬ Conv R.headEq middle (.head head) R.computation := by
        intro head conversion
        exact disjoint head (.trans _ _ _ (.symm _ _ secondConversion) conversion)
      exact .trans _ _ _ (ihFirst middleDisjoint) secondConversion

theorem TypeAdjustment.toConvOfSigmaTarget (boundary : SigmaConversionBoundary R)
    {source A : Tm Head n} {B : Tm Head (n + 1)}
    (adjustment : TypeAdjustment R source (.sigma A B)) :
    Conv R.headEq source (.sigma A B) R.computation :=
  adjustment.toConvOfTargetDisjointHeads (fun _ => boundary.headDisjoint)

/-- Dually, no cumulative step can be reached from a source conversion
class containing no head. -/
theorem TypeAdjustment.toConvOfSourceDisjointHeads {source target : Tm Head n}
    (adjustment : TypeAdjustment R source target)
    (disjoint : ∀ head, ¬ Conv R.headEq source (.head head) R.computation) :
    Conv R.headEq source target R.computation := by
  induction adjustment with
  | refl type => exact .refl _
  | conversion conversion => exact conversion
  | cumulative order => exact False.elim (disjoint _ (.refl _))
  | @trans source middle target first second ihFirst ihSecond =>
      have firstConversion := ihFirst disjoint
      have middleDisjoint : ∀ head, ¬ Conv R.headEq middle (.head head) R.computation := by
        intro head conversion
        exact disjoint head (.trans _ _ _ firstConversion conversion)
      exact .trans _ _ _ firstConversion (ihSecond middleDisjoint)

namespace PureConversion

open ConversionCoherence

private theorem sigma_step_decomp (empty : R.computation = RootComputation.empty)
    {A : Tm Head n} {B : Tm Head (n + 1)} {target : Tm Head n}
    (step : Step R.headEq (.sigma A B) target R.computation) :
    ∃ A' B', target = .sigma A' B' ∧ StepStar R A A' ∧ StepStar R B B' := by
  cases step with
  | root equation => rw [empty] at equation; exact equation.elim
  | congSigmaDom inner =>
      exact ⟨_, _, rfl, .tail .refl inner, .refl⟩
  | congSigmaCod inner =>
      exact ⟨_, _, rfl, .refl, .tail .refl inner⟩

theorem sigma_stepStar_decomp (empty : R.computation = RootComputation.empty)
    {A : Tm Head n} {B : Tm Head (n + 1)} {target : Tm Head n}
    (steps : StepStar R (.sigma A B) target) :
    ∃ A' B', target = .sigma A' B' ∧ StepStar R A A' ∧ StepStar R B B' := by
  induction steps with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | tail previous finalStep ih =>
      obtain ⟨A', B', rfl, first, second⟩ := ih
      obtain ⟨A'', B'', rfl, lastFirst, lastSecond⟩ := sigma_step_decomp empty finalStep
      exact ⟨_, _, rfl, first.trans lastFirst, second.trans lastSecond⟩

def sigmaConversionBoundary (R : Rules Head)
    (empty : R.computation = RootComputation.empty)
    (symmetric : Std.Symm R.headEq) : SigmaConversionBoundary R where
  components := by
    intro n A A' B B' conversion
    obtain ⟨common, firstSteps, secondSteps⟩ := churchRosser R empty symmetric conversion
    obtain ⟨firstA, firstB, firstShape, firstAPath, firstBPath⟩ :=
      sigma_stepStar_decomp empty firstSteps
    obtain ⟨secondA, secondB, secondShape, secondAPath, secondBPath⟩ :=
      sigma_stepStar_decomp empty secondSteps
    have equality := firstShape.symm.trans secondShape
    injection equality with domains codomains
    subst secondA
    subst secondB
    exact ⟨.trans _ _ _ (stepStar_implies_conv firstAPath)
      (.symm _ _ (stepStar_implies_conv secondAPath)),
      .trans _ _ _ (stepStar_implies_conv firstBPath)
        (.symm _ _ (stepStar_implies_conv secondBPath))⟩
  headDisjoint := by
    intro n A B head conversion
    obtain ⟨common, sigmaSteps, headSteps⟩ := churchRosser R empty symmetric conversion
    obtain ⟨A', B', sigmaShape, _, _⟩ := sigma_stepStar_decomp empty sigmaSteps
    obtain ⟨head', headShape⟩ := stepStar_head_shape (rootPiHeadNeutral R empty) headSteps
    rw [sigmaShape] at headShape
    cases headShape

end PureConversion

namespace ConstantExpansion

def Qualification.sigmaConversionBoundary (qualification : Qualification R)
    (symmetric : Std.Symm R.headEq) : SigmaConversionBoundary R where
  components := by
    intro n A A' B B' conversion
    have expanded := (qualification.conversion_iff _ _).mp conversion
    obtain ⟨domains, codomains⟩ :=
      (PureConversion.sigmaConversionBoundary (pureRules R) rfl symmetric).components expanded
    exact ⟨(qualification.conversion_iff _ _).mpr domains,
      (qualification.conversion_iff _ _).mpr codomains⟩
  headDisjoint := by
    intro n A B head conversion
    exact (PureConversion.sigmaConversionBoundary (pureRules R) rfl symmetric).headDisjoint
      ((qualification.conversion_iff _ _).mp conversion)

end ConstantExpansion

#print axioms TypeAdjustment.toConvOfTargetDisjointHeads
#print axioms TypeAdjustment.toConvOfSigmaTarget
#print axioms TypeAdjustment.toConvOfSourceDisjointHeads
#print axioms PureConversion.sigma_stepStar_decomp
#print axioms PureConversion.sigmaConversionBoundary
#print axioms ConstantExpansion.Qualification.sigmaConversionBoundary
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
