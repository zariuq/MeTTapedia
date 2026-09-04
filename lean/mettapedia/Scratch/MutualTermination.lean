import Mettapedia.Languages.Metamath.InferenceActiveHypothesisReflection
import Mettapedia.Languages.Metamath.InferenceAssertionRootReflection

namespace Scratch.MutualTermination

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceProjection

example {target : ValidatedPresentation} {premise : Pattern}
    {premises : List Pattern} (head : Derivation target premise)
    (tail : DerivationList target premises) :
    sizeOf head < sizeOf (DerivationList.cons head tail) := by
  simp_wf
  omega

example {target : ValidatedPresentation} {premise : Pattern}
    {premises : List Pattern} (head : Derivation target premise)
    (tail : DerivationList target premises) :
    sizeOf tail < sizeOf (DerivationList.cons head tail) := by
  simp

example {target : ValidatedPresentation} {premise : Pattern}
    {premises : List Pattern} (head : Derivation target premise)
    (tail : DerivationList target premises) :
    sizeOf head < sizeOf (DerivationList.cons head tail) := by
  change sizeOf head < 1 + sizeOf premise + sizeOf premises + sizeOf head + sizeOf tail
  omega

mutual

theorem simpleF {target : ValidatedPresentation} {goal : Pattern}
    (derivation : Derivation target goal) : True := by
  cases derivation with
  | byRule _ _ children =>
      have _ := simpleG children
      trivial
termination_by sizeOf derivation
decreasing_by
  simp_wf

theorem simpleG {target : ValidatedPresentation} {goals : List Pattern}
    (children : DerivationList target goals) : True := by
  cases children with
  | nil => trivial
  | cons head tail =>
      have _ := simpleF head
      have _ := simpleG tail
      trivial
termination_by sizeOf children
decreasing_by
  simp_wf
  omega
  simp

end

theorem boundedG {target : ValidatedPresentation} (bound : Nat)
    (reflect : ∀ {goal : Pattern} (d : Derivation target goal),
      sizeOf d < bound → True)
    (hypotheses : List HypothesisView) (bodies : List Pattern)
    (hlength : bodies.length = hypotheses.length) (suffix : List Pattern)
    (children : DerivationList target
      (rawAssertionProvesPremises hypotheses bodies ++ suffix))
    (hbound : sizeOf children < bound) : True := by
  revert bodies
  cases hypotheses with
  | nil =>
      intro bodies
      cases bodies with
      | nil => intro _ _ _; trivial
      | cons _ _ => intro h; simp at h
  | cons hypothesis hypotheses =>
      intro bodies
      cases bodies with
      | nil => intro h; simp at h
      | cons body bodies =>
          intro hlength children hbound
          have htailLength : bodies.length = hypotheses.length := by
            simpa using hlength
          cases children with
          | cons head tail =>
              have hheadLocal : sizeOf head < sizeOf (DerivationList.cons head tail) := by
                simp_wf
                omega
              have htailLocal : sizeOf tail < sizeOf (DerivationList.cons head tail) := by
                simp
              have _ := reflect head (lt_trans hheadLocal hbound)
              have _ := boundedG bound reflect hypotheses bodies htailLength suffix tail
                (lt_trans htailLocal hbound)
              trivial
termination_by hypotheses.length
decreasing_by simp_all

mutual

theorem dependentF {target : ValidatedPresentation} {goal : Pattern}
    (derivation : Derivation target goal) : True := by
  cases hderivation : derivation with
  | byRule _ _ children =>
      have hchildrenSize : sizeOf children < sizeOf derivation := by
        rw [hderivation]
        simp_wf
        omega
      have _ := dependentG ([] : List HypothesisView) [] rfl _ children
      trivial
termination_by sizeOf derivation
decreasing_by assumption

theorem dependentG {target : ValidatedPresentation}
    (hypotheses : List HypothesisView) (bodies : List Pattern)
    (hlength : bodies.length = hypotheses.length) (suffix : List Pattern)
    (children : DerivationList target
      (rawAssertionProvesPremises hypotheses bodies ++ suffix)) : True := by
  revert bodies
  cases hypotheses with
  | nil =>
      intro bodies
      cases bodies with
      | nil =>
          intro _ children
          trivial
      | cons _ _ => intro h; simp at h
  | cons hypothesis hypotheses =>
      intro bodies
      cases bodies with
      | nil => intro h; simp at h
      | cons body bodies =>
          intro hlength children
          have htailLength : bodies.length = hypotheses.length := by
            simpa using hlength
          cases children with
          | cons head tail =>
              have _ := dependentF head
              have _ := dependentG hypotheses bodies htailLength suffix tail
              trivial
termination_by sizeOf children
decreasing_by
  all_goals simp_all
  all_goals omega

end

end Scratch.MutualTermination
