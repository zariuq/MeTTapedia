import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplayContextConversion

/-!
# Computation of native introduction/elimination certificates

The beta and pair-projection roots are executed on their actual introduction
certificates. Dependent second projection keeps the original displayed type:
the result proof carries a computed conversion of its index and independently
computed result formation. No normalizer or proof search supplies that proof.

These are the introduction-root cases of certificate-preserving reduction.
Inverting an arbitrary converted function/pair certificate and interpreting
every contextual or declared root are separate obligations.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay
namespace IntroductionComputation

open Presentation StructuralTypingReplay NativeIndexedFamilies

def betaPi {n : Nat} (body type : Tower.Tm (n + 1)) (argument : Tower.Tm n)
    (bodyCode : Code (n + 1)) (argumentCode : Code n) : Code n :=
  StructuralTypingReplay.Code.instantiate NativeRelatorConversionChecking.rename
    NativeRelatorConversionChecking.substitute body type argument bodyCode argumentCode

/-- The computed beta certificate is accepted at the source's actual
dependent result type, and the same endpoints pass directed-step replay. -/
theorem betaPi_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {A argument : Tower.Tm n} {body B : Tower.Tm (n + 1)} {u : Tower.Head}
    {formation argumentCode : Code n} {bodyCode : Code (n + 1)}
    (accepted : check context (.app (.lam body) argument) (inst0 argument B) contextCode
      (.appElim A B (.lamIntro u formation bodyCode) argumentCode) = true) :
    check context (inst0 argument body) (inst0 argument B) contextCode
        (betaPi body B argument bodyCode argumentCode) = true ∧
      NativeRelatorConversionChecking.checkStep (.betaPi body argument)
        (.app (.lam body) argument) (inst0 argument body) = true := by
  simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true,
    decide_eq_true_eq] at accepted
  refine ⟨?_, by simp [NativeRelatorConversionChecking.checkStep,
    StructuralConversionCode.StepCode.check, StructuralConversionCode.StepCode.decode]⟩
  simp only [check, checkJudgment, Bool.and_eq_true]
  exact ⟨accepted.1, StructuralTypingReplay.Code.instantiate_checked
    NativeRelatorConversionChecking.rename NativeRelatorConversionChecking.substitute
    IntrinsicRelator.rules NativeRelatorConversionChecking.check
    NativeRelatorConversionChecking.check_rename NativeRelatorConversionChecking.check_substitute
    accepted.2.1.1.2 accepted.2.1.2⟩

theorem betaSigmaFst_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {A first second : Tower.Tm n} {B : Tower.Tm (n + 1)} {u : Tower.Head}
    {formation firstCode secondCode : Code n}
    (accepted : check context (.fst (.pair first second)) A contextCode
      (.fstElim B (.pairIntro u formation firstCode secondCode)) = true) :
    check context first A contextCode firstCode = true ∧
      NativeRelatorConversionChecking.checkStep (.betaSigmaFst first second)
        (.fst (.pair first second)) first = true := by
  simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true] at accepted
  refine ⟨?_, by simp [NativeRelatorConversionChecking.checkStep,
    StructuralConversionCode.StepCode.check, StructuralConversionCode.StepCode.decode]⟩
  simp only [check, checkJudgment, Bool.and_eq_true]
  exact And.intro accepted.1 accepted.2.1.2

def betaSigmaSnd {n : Nat} (contextCode : ContextCode n) (A : Tower.Tm n) (B : Tower.Tm (n + 1))
    (first second : Tower.Tm n) (u : Tower.Head) (formation firstCode secondCode : Code n) : Option (Code n) :=
  (resultFormation contextCode (.snd (.pair first second)) (inst0 (.fst (.pair first second)) B)
    (.sndElim A B (.pairIntro u formation firstCode secondCode))).map fun formed =>
      .convert (inst0 first B) formed.1 secondCode formed.2
        (.symm (NativeRelatorConversionChecking.inst0Argument (.fst (.pair first second)) first
          (.single (.betaSigmaFst first second)) B))

theorem betaSigmaSnd_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {A first second : Tower.Tm n} {B : Tower.Tm (n + 1)} {u : Tower.Head}
    {formation firstCode secondCode : Code n}
    (accepted : check context (.snd (.pair first second)) (inst0 (.fst (.pair first second)) B) contextCode
      (.sndElim A B (.pairIntro u formation firstCode secondCode)) = true) :
    ∃ resultCode, betaSigmaSnd contextCode A B first second u formation firstCode secondCode = some resultCode ∧
      check context second (inst0 (.fst (.pair first second)) B) contextCode resultCode = true ∧
      NativeRelatorConversionChecking.checkStep (.betaSigmaSnd first second)
        (.snd (.pair first second)) second = true := by
  obtain ⟨level, resultFormationCode, computed, isUniverse, resultFormed⟩ := resultFormation_checked accepted
  have inputs := accepted
  simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true] at inputs
  simp only [check, checkJudgment, Bool.and_eq_true] at resultFormed
  refine ⟨.convert (inst0 first B) level secondCode resultFormationCode
    (.symm (NativeRelatorConversionChecking.inst0Argument (.fst (.pair first second)) first
      (.single (.betaSigmaFst first second)) B)), ?_, ?_, by simp [NativeRelatorConversionChecking.checkStep,
    StructuralConversionCode.StepCode.check, StructuralConversionCode.StepCode.decode]⟩
  · simp only [betaSigmaSnd, computed, Option.map_some]
  · simp only [check, checkJudgment, StructuralTypingReplay.check, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨inputs.1, ⟨⟨⟨isUniverse, inputs.2.1.2⟩, resultFormed.2⟩, ?_⟩⟩
    apply StructuralConversionCode.Code.check_symm Tower.HeadEq NativeRelatorRootConversionCode.decode
    exact NativeRelatorConversionChecking.check_inst0Argument (by
      simp [NativeRelatorConversionChecking.check, StructuralConversionCode.Code.check,
        StructuralConversionCode.Code.decode, StructuralConversionCode.StepCode.decode]) B

namespace Controls

open NativeRelatorConversionChecking.Examples (ground betaArgument)

def projectedCode : Code 1 :=
  .convert (.id ground (.var 0) (.var 0)) (.sort Tower.zero)
    (.reflIntro ground .var)
    (.idForm (.sort Tower.zero) .headType .var
      (.fstElim (.id ground (.var 1) (.var 0)) FormationControls.pairCode))
    (.symm (NativeRelatorConversionChecking.inst0Argument (.fst FormationControls.pairTerm) (.var 0)
      (.single (.betaSigmaFst (.var 0) (.refl (.var 0)))) (.id ground (.var 1) (.var 0))))

theorem dependent_projection_certificate_computes :
    betaSigmaSnd NativeJudgmentReplay.Controls.contextCode ground (.id ground (.var 1) (.var 0))
      (.var 0) (.refl (.var 0)) (.sort (.max Tower.zero Tower.zero))
      (.sigmaForm (.sort Tower.zero) (.sort Tower.zero) .headType
        (.idForm (.sort Tower.zero) .headType .var .var)) .var (.reflIntro ground .var) =
      some projectedCode := by rfl

theorem dependent_projection_certificate_checked :
    check NativeJudgmentReplay.Controls.context (.refl (.var 0))
      (inst0 (.fst FormationControls.pairTerm) (.id ground (.var 1) (.var 0)))
      NativeJudgmentReplay.Controls.contextCode projectedCode = true := by decide +kernel

theorem projection_without_index_conversion_rejected :
    check NativeJudgmentReplay.Controls.context (.refl (.var 0))
      (inst0 (.fst FormationControls.pairTerm) (.id ground (.var 1) (.var 0)))
      NativeJudgmentReplay.Controls.contextCode (.reflIntro ground .var) = false := by decide +kernel

theorem dependent_beta_certificate_checked :
    check NativeJudgmentReplay.Controls.context (.refl (betaArgument (.var 0)))
      FormationControls.applicationType NativeJudgmentReplay.Controls.contextCode
      (betaPi (.refl (.var 0)) (.id ground (.var 0) (.var 0)) (betaArgument (.var 0))
        (.reflIntro ground .var) NativeJudgmentReplay.Controls.betaArgumentCode) = true := by
  have accepted : check NativeJudgmentReplay.Controls.context FormationControls.application
      FormationControls.applicationType NativeJudgmentReplay.Controls.contextCode
      FormationControls.applicationCode = true := by decide +kernel
  exact (betaPi_checked accepted).1

end Controls

#print axioms betaPi_checked
#print axioms betaSigmaFst_checked
#print axioms betaSigmaSnd_checked
#print axioms Controls.dependent_projection_certificate_computes
#print axioms Controls.dependent_projection_certificate_checked
#print axioms Controls.projection_without_index_conversion_rejected
#print axioms Controls.dependent_beta_certificate_checked

end IntroductionComputation
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay
