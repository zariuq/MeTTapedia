import Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.MILCheckedNativeListPrograms
import Mettapedia.GSLT.LanguageDef.CertificateGSLTLedgerDependentFamily

/-!
# The checked recursive List program in the exact-ledger trinity

The existing learned List-relator program already has one checked certificate,
an independent recursive semantic witness, and a native dependent List term.
This bridge retains that very checked certificate as an open proof over the
empty premise context. It then obtains an exact-ledger displayed point and
an OSLF closure-completion receipt without replacing the program by a more
convenient proof. The malformed missing-tail program remains impossible.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory
namespace MILCheckedNativeListOpenSearchTrinity

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenSearchMachine
open MILCheckedNativeListPrograms

private abbrev programGoal : Pattern :=
  mapRel successor singletonSource singletonTarget

private def programContext : ClassifyingContext learned.target := ⟨[]⟩

/-- Every checked raw recursive List program enters the exact displayed
proof family with its very same checked certificate. -/
noncomputable def checkedProgramExactReceipt
    {sources targets : Pattern} {raw : RawProof}
    (program : CheckedRawNativeMapProgram sources targets raw) :
    exactDerivationFibre learned.target programContext
      (mapRel successor sources targets) [] :=
  closedExactDerivationFibre program.checked

theorem checkedProgramExactReceipt_close
    {sources targets : Pattern} {raw : RawProof}
    (program : CheckedRawNativeMapProgram sources targets raw) :
    (checkedProgramExactReceipt program).val.close = program.checked := by
  exact closedExactDerivationFibre_close program.checked

/-- Exact checker erasure survives the passage into the displayed family. -/
theorem checkedProgramExactReceipt_erases
    {sources targets : Pattern} {raw : RawProof}
    (program : CheckedRawNativeMapProgram sources targets raw) :
    (checkedProgramExactReceipt program).val.close.erase = raw := by
  rw [checkedProgramExactReceipt_close]
  exact program.erases

/-- The same checked recursive program supplies a retained operational route
and its exact discharge ledger, with no fresh proof chosen for the route. -/
noncomputable def checkedProgramOperationalReceipt
    {sources targets : Pattern} {raw : RawProof}
    (program : CheckedRawNativeMapProgram sources targets raw) :=
  exactDerivationRouteReceipt (checkedProgramExactReceipt program)

theorem checkedProgramOperationalReceipt_recovers
    {sources targets : Pattern} {raw : RawProof}
    (program : CheckedRawNativeMapProgram sources targets raw) :
    (derivationOfCompleteRoute
      (checkedProgramOperationalReceipt program).2).close =
        program.checked := by
  rw [checkedProgramOperationalReceipt,
    exactDerivationRouteReceipt_reconstruct]
  exact checkedProgramExactReceipt_close program

/-- Operational reconstruction, exact raw erasure, recursive list semantics,
and native dependent typing all refer to one checked program. -/
theorem checkedProgram_operational_semantics_and_native_typing
    {sources targets : Pattern} {raw : RawProof}
    (program : CheckedRawNativeMapProgram sources targets raw) :
    (derivationOfCompleteRoute
        (checkedProgramOperationalReceipt program).2).close.erase = raw ∧
      Nonempty (ListStep successor sources targets) ∧
      NativeCanary.NativeHasType NativeCanary.contextABRSourceTargetEdge
        program.toChecked.nativeTerm.code
        program.toChecked.nativeImage.typeOver.code := by
  refine ⟨?_, ⟨program.toChecked.semanticEvidence⟩,
    program.toChecked.nativeTerm.typed⟩
  rw [checkedProgramOperationalReceipt_recovers]
  exact program.erases

/-- The displayed proof, recursive semantic witness, and intrinsic List
typing all arise from the same checked program. -/
theorem checkedProgram_receipt_semantics_and_native_typing
    {sources targets : Pattern} {raw : RawProof}
    (program : CheckedRawNativeMapProgram sources targets raw) :
    (checkedProgramExactReceipt program).val.close.erase = raw ∧
      Nonempty (ListStep successor sources targets) ∧
      NativeCanary.NativeHasType NativeCanary.contextABRSourceTargetEdge
        program.toChecked.nativeTerm.code
        program.toChecked.nativeImage.typeOver.code := by
  exact ⟨checkedProgramExactReceipt_erases program,
    ⟨program.toChecked.semanticEvidence⟩,
    program.toChecked.nativeTerm.typed⟩

/-- A term of the proof-relevant displayed family, retaining the same
recursive checked proof that builds the native List relation. -/
noncomputable def programExactReceipt :
    exactDerivationFibre learned.target programContext programGoal [] :=
  checkedProgramExactReceipt singletonNative

theorem programExactReceipt_is_original :
    programExactReceipt.val.close = singletonNative.checked := by
  exact checkedProgramExactReceipt_close singletonNative

/-- The proof term lives in the complete substitution-coherent displayed
family, not only in a pointwise `Nonempty` proposition. -/
noncomputable def programDisplayedPoint :
    (exactDerivationDisplayedFamily learned.target).Elements :=
  closedExactDisplayedPoint singletonNative.checked

/-- Its extensional completion observation is available only after the
actual checked proof has supplied the proof-bearing receipt. -/
theorem programClosureCompletion :
    gsltDiamond
      (Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenSearchModalAdequacy.theory
        learned.target []).closure
      (fun candidate => candidate =
        (⟨[], []⟩ : State []))
      ⟨[programGoal], []⟩ :=
  (exactDerivationFibre_nonempty_iff_closureDiamond learned.target
    programContext programGoal []).mp ⟨programExactReceipt⟩

/-- The missing recursive tail cannot be laundered into an exact-ledger
receipt for this program goal, regardless of which checked proof is proposed. -/
theorem missing_tail_no_exact_receipt :
    ¬ ∃ receipt : exactDerivationFibre learned.target programContext
        programGoal [],
      receipt.val.close.erase = missingTailProof := by
  rintro ⟨receipt, erases⟩
  have accepted := checkRaw_erase receipt.val.close
  rw [erases, missingTailProof_rejected] at accepted
  contradiction

end MILCheckedNativeListOpenSearchTrinity
end Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory

#print axioms Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.MILCheckedNativeListOpenSearchTrinity.programExactReceipt_is_original
#print axioms Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.MILCheckedNativeListOpenSearchTrinity.checkedProgram_receipt_semantics_and_native_typing
#print axioms Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.MILCheckedNativeListOpenSearchTrinity.checkedProgramOperationalReceipt_recovers
#print axioms Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.MILCheckedNativeListOpenSearchTrinity.checkedProgram_operational_semantics_and_native_typing
#print axioms Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.MILCheckedNativeListOpenSearchTrinity.programClosureCompletion
#print axioms Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory.MILCheckedNativeListOpenSearchTrinity.missing_tail_no_exact_receipt
