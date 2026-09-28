import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeCheckedPathControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetTraceIdentityTypeInterpretation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayCoherence

/-!
# One checked J source has the same value in replay and native interpretation

The existing native J declaration and iota rule are used unchanged. The
certificate proposal supplies an actual retained source tree; the replay
checker, not the proposal, admits it. The general supported-expression
comparison then identifies that tree's set value with the structural
interpretation, whose J-iota theorem computes a nontrivial type code.

The theorem is for this declared fixed-universe J instance and its formed
context. It does not assert general certificate coherence or a C refinement.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayDeclaredJAgreement

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay
open ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open ZFSetInterpretation (Code El)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open Mettapedia.TypeTheory.UniverseLevel.ZFSetInterpretation.Controls (twoCode)
open NativeIndexedFamilies
open NativeIndexedFamilies.Intrinsic (identityEliminateApp)
open NativeJudgmentReplay
open ZFSetTraceIdentityTypeInterpretation
open ZFSetTraceIdentityDeclaration (motiveCode motiveAt reflValue)

universe u

theorem source_supported :
    ZFSetTypeExpressionInterpretation.supported Intrinsic.identityIotaLeft = true := by
  decide

/-- For any supported arguments and two actually checked trees at the same
displayed type, the declared J-iota computation agrees with its returned
method on the supplied environment. This is value comparison, conditional on
the stated set-code membership premises, not soundness for every declaration
in the native signature. -/
theorem accepted_declared_j_iota_value
    {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {i j n : Nat}
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (env : Environment.{u} n) (context : Tower.Ctx n)
    (A X P D displayed : Tower.Tm n) (hA : ZFSetTypeExpressionInterpretation.supported A = true)
    (hX : ZFSetTypeExpressionInterpretation.supported X = true)
    (hP : ZFSetTypeExpressionInterpretation.supported P = true)
    (hD : ZFSetTypeExpressionInterpretation.supported D = true)
    (a : Code h seed i) (x : El a) (p : El (motiveCode j a x))
    (d : El (motiveAt a x p x (reflValue a x)))
    (atA : ZFSetTypeExpressionInterpretation.interpret heads
      (identityConstants h seed i j constants) A hA env = a.1)
    (atX : ZFSetTypeExpressionInterpretation.interpret heads
      (identityConstants h seed i j constants) X hX env = x.1)
    (atP : ZFSetTypeExpressionInterpretation.interpret heads
      (identityConstants h seed i j constants) P hP env = p.1)
    (atD : ZFSetTypeExpressionInterpretation.interpret heads
      (identityConstants h seed i j constants) D hD env = d.1)
    (sourceCode targetCode : NativeJudgmentReplay.Code n)
    (sourceChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check context
      (identityEliminateApp A X P D X (.refl X)) displayed sourceCode = true)
    (targetChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check context D displayed targetCode = true) :
    ∃ sourceMeaning targetMeaning,
      assemble heads (identityConstants h seed i j constants) sourceCode
        (identityEliminateApp A X P D X (.refl X)) displayed = some sourceMeaning ∧
      assemble heads (identityConstants h seed i j constants) targetCode
        D displayed = some targetMeaning ∧
      sourceMeaning.value env = targetMeaning.value env := by
  obtain ⟨sourceMeaning, atSource, _⟩ := accepted_assembles heads
    (identityConstants h seed i j constants) IntrinsicRelator.rules
    NativeRelatorConversionChecking.check sourceCode sourceChecked
  obtain ⟨targetMeaning, atTarget, _⟩ := accepted_assembles heads
    (identityConstants h seed i j constants) IntrinsicRelator.rules
    NativeRelatorConversionChecking.check targetCode targetChecked
  refine ⟨sourceMeaning, targetMeaning, atSource, atTarget, ?_⟩
  have sourceSupported := application_supported A X P D X (.refl X)
    hA hX hP hD hX hX
  calc
    sourceMeaning.value env =
        ZFSetTypeExpressionInterpretation.interpret heads
          (identityConstants h seed i j constants)
          (identityEliminateApp A X P D X (.refl X)) sourceSupported env :=
      agrees_with_type_expressions heads (identityConstants h seed i j constants)
        sourceCode _ displayed sourceMeaning sourceSupported atSource env
    _ = ZFSetTypeExpressionInterpretation.interpret heads
          (identityConstants h seed i j constants) D hD env :=
      identity_iota_interpretation (h := h) (seed := seed) (i := i) (j := j)
        heads constants env A X P D hA hX hP hD a x p d atA atX atP atD
    _ = targetMeaning.value env :=
      (agrees_with_type_expressions heads (identityConstants h seed i j constants)
        targetCode D displayed targetMeaning hD atTarget env).symm

/-- The semantic admission condition for J's four explicit arguments. It is
not replaced by syntactic context validity or an implicit soundness claim. -/
def AdmittedJArguments
    (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (i j : Nat)
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    {n : Nat} (A X P D : Tower.Tm n)
    (hA : ZFSetTypeExpressionInterpretation.supported A = true)
    (hX : ZFSetTypeExpressionInterpretation.supported X = true)
    (hP : ZFSetTypeExpressionInterpretation.supported P = true)
    (hD : ZFSetTypeExpressionInterpretation.supported D = true)
    (env : Environment.{u} n) : Prop :=
  ∃ (a : Code h seed i) (x : El a) (p : El (motiveCode j a x))
    (d : El (motiveAt a x p x (reflValue a x))),
    ZFSetTypeExpressionInterpretation.interpret heads
      (identityConstants h seed i j constants) A hA env = a.1 ∧
    ZFSetTypeExpressionInterpretation.interpret heads
      (identityConstants h seed i j constants) X hX env = x.1 ∧
    ZFSetTypeExpressionInterpretation.interpret heads
      (identityConstants h seed i j constants) P hP env = p.1 ∧
    ZFSetTypeExpressionInterpretation.interpret heads
      (identityConstants h seed i j constants) D hD env = d.1

/-- Accepted source and return assemblies are fixed once. Their values then
agree at every environment whose J arguments inhabit the actual set codes. -/
theorem accepted_declared_j_iota_on_admitted_environments
    (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (i j : Nat)
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    {n : Nat} (context : Tower.Ctx n) (A X P D displayed : Tower.Tm n)
    (hA : ZFSetTypeExpressionInterpretation.supported A = true)
    (hX : ZFSetTypeExpressionInterpretation.supported X = true)
    (hP : ZFSetTypeExpressionInterpretation.supported P = true)
    (hD : ZFSetTypeExpressionInterpretation.supported D = true)
    (sourceCode targetCode : NativeJudgmentReplay.Code n)
    (sourceChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check context
      (identityEliminateApp A X P D X (.refl X)) displayed sourceCode = true)
    (targetChecked : StructuralTypingReplay.check IntrinsicRelator.rules
      NativeRelatorConversionChecking.check context D displayed targetCode = true) :
    ∃ sourceMeaning targetMeaning,
      assemble heads (identityConstants h seed i j constants) sourceCode
        (identityEliminateApp A X P D X (.refl X)) displayed = some sourceMeaning ∧
      assemble heads (identityConstants h seed i j constants) targetCode
        D displayed = some targetMeaning ∧
      ∀ env, AdmittedJArguments h seed i j heads constants A X P D hA hX hP hD env →
        sourceMeaning.value env = targetMeaning.value env := by
  obtain ⟨sourceMeaning, atSource, _⟩ := accepted_assembles heads
    (identityConstants h seed i j constants) IntrinsicRelator.rules
    NativeRelatorConversionChecking.check sourceCode sourceChecked
  obtain ⟨targetMeaning, atTarget, _⟩ := accepted_assembles heads
    (identityConstants h seed i j constants) IntrinsicRelator.rules
    NativeRelatorConversionChecking.check targetCode targetChecked
  refine ⟨sourceMeaning, targetMeaning, atSource, atTarget, ?_⟩
  intro env admitted
  obtain ⟨a, x, p, d, atA, atX, atP, atD⟩ := admitted
  obtain ⟨sourceOther, targetOther, atSourceOther, atTargetOther, agree⟩ :=
    accepted_declared_j_iota_value heads constants env context A X P D displayed
      hA hX hP hD a x p d atA atX atP atD sourceCode targetCode
      sourceChecked targetChecked
  rw [atSource] at atSourceOther
  cases Option.some.inj atSourceOther
  rw [atTarget] at atTargetOther
  cases Option.some.inj atTargetOther
  exact agree

/-- Any actually accepted replay tree for this J redex agrees with the
native declared operation at the concrete typed universe environment. -/
theorem accepted_source_value
    (h : CofinalInaccessibles.{u}) (heads : Tower.Head → ZFSet.{u})
    (constants : DeclName → ZFSet.{u})
    (contextCode : NativeJudgmentReplay.ContextCode 4)
    (sourceCode : NativeJudgmentReplay.Code 4)
    (accepted : NativeJudgmentReplay.check Intrinsic.contextAXPD
      Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType contextCode sourceCode = true) :
    ∃ meaning,
      assemble heads (identityConstants h ∅ 0 1 constants) sourceCode
        Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType = some meaning ∧
      meaning.value (Controls.universeEnvironment h) = (twoCode h).1 := by
  have sourceChecked :
      StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD
        Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType sourceCode = true := by
    change checkJudgment IntrinsicRelator.rules NativeRelatorConversionChecking.check
      Intrinsic.contextAXPD Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
      contextCode sourceCode = true at accepted
    simp only [checkJudgment, Bool.and_eq_true] at accepted
    exact accepted.2
  obtain ⟨meaning, atSource, _⟩ := accepted_assembles heads
    (identityConstants h ∅ 0 1 constants) IntrinsicRelator.rules
    NativeRelatorConversionChecking.check sourceCode sourceChecked
  refine ⟨meaning, atSource, ?_⟩
  calc
    meaning.value (Controls.universeEnvironment h) =
        ZFSetTypeExpressionInterpretation.interpret heads
          (identityConstants h ∅ 0 1 constants) Intrinsic.identityIotaLeft
          source_supported (Controls.universeEnvironment h) :=
      agrees_with_type_expressions heads (identityConstants h ∅ 0 1 constants)
        sourceCode Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType meaning
        source_supported atSource _
    _ = (twoCode h).1 := Controls.universe_type_returned h heads constants

/-- Extract exactly the proposal's computed tree, without a fallback code.
Acceptance below is still established independently by replay. -/
def sourceProposal : Tower.Tm 4 × NativeJudgmentReplay.Code 4 :=
  (CertificateProposal.term 64 Intrinsic.contextAXPD Intrinsic.identityIotaLeft).get
    (by decide +kernel)

def sourceCode : NativeJudgmentReplay.Code 4 := sourceProposal.2

def contextCode : NativeJudgmentReplay.ContextCode 4 :=
  (CertificateProposal.context Intrinsic.contextAXPD).get (by decide +kernel)

theorem proposal_type : sourceProposal.1 = Intrinsic.identityIotaResultType := by
  decide +kernel

theorem context_proposal_receipt :
    CertificateProposal.context Intrinsic.contextAXPD = some contextCode := by
  rfl

theorem source_proposal_receipt :
    CertificateProposal.term 64 Intrinsic.contextAXPD Intrinsic.identityIotaLeft =
      some (Intrinsic.identityIotaResultType, sourceCode) := by
  rfl

theorem proposal_accepted : NativeJudgmentReplay.check Intrinsic.contextAXPD
    Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType contextCode sourceCode = true := by
  decide +kernel

theorem context_formed :
    StructuralTypingReplay.checkContext IntrinsicRelator.rules
      NativeRelatorConversionChecking.check Intrinsic.contextAXPD contextCode = true := by
  decide +kernel

def checkedContext : NativeCheckedSubstitution.Context :=
  ⟨4, Intrinsic.contextAXPD, contextCode, context_formed⟩

private def jSteps : List (NativeRelatorConversionChecking.StepCode 4) :=
  [.root NativeRelatorRootConversionCode.Examples.identityCode]

private def returned : Option (Tower.Tm 4 × NativeJudgmentReplay.Code 4) :=
  NativeCheckedPathExecution.runCodes checkedContext Intrinsic.identityIotaLeft
    Intrinsic.identityIotaResultType sourceCode jSteps

theorem returned_exists : returned.isSome = true := by
  decide +kernel

def returnedReceipt : Tower.Tm 4 × NativeJudgmentReplay.Code 4 :=
  returned.get (by simpa only [Option.isSome_iff_ne_none] using returned_exists)

theorem returned_receipt : returned = some returnedReceipt := by
  rfl

theorem returned_term : returnedReceipt.1 = Intrinsic.identityIotaRight := by
  decide +kernel

theorem returned_accepted : NativeJudgmentReplay.check Intrinsic.contextAXPD
    Intrinsic.identityIotaRight Intrinsic.identityIotaResultType contextCode
    returnedReceipt.2 = true := by
  have checked := NativeCheckedPathExecution.runCodes_sound checkedContext returned_receipt
  change NativeJudgmentReplay.check Intrinsic.contextAXPD returnedReceipt.1
    Intrinsic.identityIotaResultType contextCode returnedReceipt.2 = true at checked
  simpa only [returned_term] using checked

/-- The very same checked source certificate participates in finite native
execution and in the set-semantic square. The iota result is a type code,
not the proof token `∅`. -/
theorem checked_j_execution_and_meaning
    (h : CofinalInaccessibles.{u}) (heads : Tower.Head → ZFSet.{u})
    (constants : DeclName → ZFSet.{u}) :
    NativeCheckedPathExecution.Controls.replay Intrinsic.contextAXPD contextCode
      Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
      Intrinsic.identityIotaRight sourceCode
      [.root NativeRelatorRootConversionCode.Examples.identityCode] = true ∧
    ∃ meaning,
      assemble heads (identityConstants h ∅ 0 1 constants) sourceCode
        Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType = some meaning ∧
      meaning.value (Controls.universeEnvironment h) = (twoCode h).1 := by
  constructor
  · have executed := NativeCheckedPathExecution.Controls.declared_identity_elimination_executes
    simpa only [NativeCheckedPathExecution.Controls.proposedReplay,
      context_proposal_receipt, source_proposal_receipt] using executed
  · exact accepted_source_value h heads constants contextCode sourceCode proposal_accepted

/-- The same declared J step cannot turn an untyped variable tree into its
source, nor claim the reflexivity witness as the computed method. -/
theorem malformed_or_wrong_j_result_rejected :
    NativeCheckedPathExecution.Controls.replay Intrinsic.contextAXPD contextCode
      Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
      Intrinsic.identityIotaRight .var jSteps = false ∧
    NativeCheckedPathExecution.Controls.replay Intrinsic.contextAXPD contextCode
      Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
      (.refl (.var 2)) sourceCode jSteps = false := by
  decide +kernel

/-- The certificate *returned* by the selected J step is accepted and
assembles at the same dependent result type. Source and returned values agree
at the valid universe environment; neither is the erased proof token. -/
theorem checked_j_source_and_result_agree
    (h : CofinalInaccessibles.{u}) (heads : Tower.Head → ZFSet.{u})
    (constants : DeclName → ZFSet.{u}) :
    ∃ sourceMeaning resultMeaning,
      assemble heads (identityConstants h ∅ 0 1 constants) sourceCode
        Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType = some sourceMeaning ∧
      assemble heads (identityConstants h ∅ 0 1 constants) returnedReceipt.2
        Intrinsic.identityIotaRight Intrinsic.identityIotaResultType = some resultMeaning ∧
      sourceMeaning.value (Controls.universeEnvironment h) =
        resultMeaning.value (Controls.universeEnvironment h) ∧
      resultMeaning.value (Controls.universeEnvironment h) = (twoCode h).1 ∧
      resultMeaning.value (Controls.universeEnvironment h) ≠ ∅ := by
  have sourceChecked :
      StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD
        Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType sourceCode = true := by
    have accepted := proposal_accepted
    change checkJudgment IntrinsicRelator.rules NativeRelatorConversionChecking.check
      Intrinsic.contextAXPD Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
      contextCode sourceCode = true at accepted
    simp only [checkJudgment, Bool.and_eq_true] at accepted
    exact accepted.2
  have resultChecked :
      StructuralTypingReplay.check IntrinsicRelator.rules
        NativeRelatorConversionChecking.check Intrinsic.contextAXPD
        Intrinsic.identityIotaRight Intrinsic.identityIotaResultType returnedReceipt.2 = true := by
    have accepted := returned_accepted
    change checkJudgment IntrinsicRelator.rules NativeRelatorConversionChecking.check
      Intrinsic.contextAXPD Intrinsic.identityIotaRight Intrinsic.identityIotaResultType
      contextCode returnedReceipt.2 = true at accepted
    simp only [checkJudgment, Bool.and_eq_true] at accepted
    exact accepted.2
  obtain ⟨sourceMeaning, resultMeaning, atSource, atResult, agree⟩ :=
    accepted_declared_j_iota_value (h := h) (seed := ∅) (i := 0) (j := 1)
      heads constants (Controls.universeEnvironment h) Intrinsic.contextAXPD
      (.var 3) (.var 2) (.var 1) (.var 0) Intrinsic.identityIotaResultType
      (by decide) (by decide) (by decide) (by decide)
      (twoCode h) (ZFSetTraceIdentityDeclaration.Controls.zeroPoint h)
      (ZFSetTraceIdentityDeclaration.Controls.universeMotive h)
      (ZFSetTraceIdentityDeclaration.Controls.universeMethod h)
      rfl rfl rfl rfl sourceCode returnedReceipt.2 sourceChecked resultChecked
  have sourceValue :
      sourceMeaning.value (Controls.universeEnvironment h) = (twoCode h).1 := by
    calc
      sourceMeaning.value (Controls.universeEnvironment h) =
          ZFSetTypeExpressionInterpretation.interpret heads
            (identityConstants h ∅ 0 1 constants)
            Intrinsic.identityIotaLeft source_supported
            (Controls.universeEnvironment h) :=
        agrees_with_type_expressions heads (identityConstants h ∅ 0 1 constants)
          sourceCode Intrinsic.identityIotaLeft Intrinsic.identityIotaResultType
          sourceMeaning source_supported atSource _
      _ = (twoCode h).1 := Controls.universe_type_returned h heads constants
  have resultValue :
      resultMeaning.value (Controls.universeEnvironment h) = (twoCode h).1 :=
    agree.symm.trans sourceValue
  refine ⟨sourceMeaning, resultMeaning, atSource, atResult, agree, resultValue, ?_⟩
  · rw [resultValue]
    intro empty
    have member : (∅ : ZFSet.{u}) ∈ (twoCode h).1 :=
      ZFSetDependentProducts.Controls.empty_mem_two
    rw [empty] at member
    exact ZFSet.notMem_empty _ member

#print axioms source_supported
#print axioms accepted_declared_j_iota_value
#print axioms accepted_declared_j_iota_on_admitted_environments
#print axioms accepted_source_value
#print axioms proposal_type
#print axioms context_proposal_receipt
#print axioms source_proposal_receipt
#print axioms proposal_accepted
#print axioms context_formed
#print axioms returned_exists
#print axioms returned_receipt
#print axioms returned_term
#print axioms returned_accepted
#print axioms checked_j_execution_and_meaning
#print axioms malformed_or_wrong_j_result_rejected
#print axioms checked_j_source_and_result_agree

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayDeclaredJAgreement
