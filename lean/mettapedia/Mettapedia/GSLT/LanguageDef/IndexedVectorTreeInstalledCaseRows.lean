import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeConstructorInstallation
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceLogicalRows

/-!
# Original source case rows with the constructor programs installed

Both original universally guarded rows are transported from the same
seven-variable source telescope. The derived family, represented answer
predicate and actual constructor lambdas replace their source parameters.
The two case-method guards and the caller's primitive premises remain;
arbitrary child arrays are not assumed to have a source Vector decoder.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeInstalledCaseRows
open Mettapedia.Logic Mettapedia.Logic.HOL
namespace Install
export IndexedVectorTreeConstructorInstallation
  (Base Const target images assumptions realizes_free transportWithRoots transportWithRoots_free)
namespace Native
export IndexedVectorTreeConstructorInstallation.Native (N E V W original selection)
end Native
namespace Reading
export IndexedVectorTreeConstructorInstallation.Reading (assumptions)
end Reading
end Install
namespace Rows
export IndexedVectorTreeNativeSourceLogicalRows
  (solvedAmbient branchAmbient solvedRow closedBranchRow solvedRowProof closedBranchRowProof
   solvedRowProof_free closedBranchRowProof_free solved_original_ambient_telescope branch_original_ambient_telescope)
end Rows

private def originalSolved (roots : List (ClosedFormula Install.Const)) :
    ProofSyntax Install.Const
      (IndexedVectorTreeNativeSourceReading.ambientContext.hypotheses roots) Rows.solvedRow :=
  .castIndices (by
    simp only [Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading.GuardedContext.hypotheses,
      Rows.solved_original_ambient_telescope]) rfl (Rows.solvedRowProof roots)

private def originalBranch (roots : List (ClosedFormula Install.Const)) :
    ProofSyntax Install.Const
      (IndexedVectorTreeNativeSourceReading.ambientContext.hypotheses roots) Rows.closedBranchRow :=
  .castIndices (by
    simp only [Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading.GuardedContext.hypotheses,
      Rows.branch_original_ambient_telescope]) rfl (Rows.closedBranchRowProof roots)

private theorem originalSolved_free (roots : List (ClosedFormula Install.Const)) :
    (originalSolved roots).FunctionExtensionalityFree := by
  unfold originalSolved
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr (Rows.solvedRowProof_free roots)

private theorem originalBranch_free (roots : List (ClosedFormula Install.Const)) :
    (originalBranch roots).FunctionExtensionalityFree := by
  unfold originalBranch
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr (Rows.closedBranchRowProof_free roots)

variable {Γ : Ctx Install.Base} {A : Ty Install.Base}
  (elementSelection : ClosedTerm Install.Const (SelectionProofs.Selection (Install.Native.N ⇒ Install.Native.E)))
  (arraySelection : ClosedTerm Install.Const (SelectionProofs.Selection (Install.Native.N ⇒ Install.Native.V ⇒ Install.Native.N ⇒ Install.Native.E)))
  (input : VectorTreeFieldEmbedding.Inputs Install.Const Γ Install.Native.N A Install.Native.E)
  (parameter : Term Install.Const Γ (A ⇒ .prop)) (numbers : Term Install.Const Γ (Install.Native.N ⇒ .prop))
  (one : ClosedTerm Install.Const Install.Native.N) (ordinals : Nat → Term Install.Const Γ Install.Native.N)
  (bottom : Term Install.Const Γ Install.Native.E) {Δ : List (Formula Install.Const Γ)}
  (recognition : ProofSyntax Install.Const Δ (IndexedVectorTreeConstructorFunctions.Native.numberRecognition numbers))
  (premises : (IndexedVectorTreeConstructorFunctions.Native.arrays Install.Native.original elementSelection arraySelection).ComputationPremises Δ)
  (arithmetic : SuccessorOrder.PeanoEvidence Install.Native.original.successor Install.Native.original.zero Δ)
  (roots : List (ClosedFormula Install.Const))
  (rootProofs : ProofSyntax.HypothesisSubstitution (Install.Reading.assumptions roots Γ) Δ)

def solvedRow : Formula Install.Const (Install.target Γ) :=
  HOL.subst (Install.images elementSelection arraySelection input parameter numbers one ordinals bottom) Rows.solvedRow

def branchRow : Formula Install.Const (Install.target Γ) :=
  HOL.subst (Install.images elementSelection arraySelection input parameter numbers one ordinals bottom) Rows.closedBranchRow

@[irreducible] def solved : ProofSyntax Install.Const
    (Install.assumptions elementSelection arraySelection input parameter numbers one ordinals bottom (Δ := Δ))
    (solvedRow elementSelection arraySelection input parameter numbers one ordinals bottom) :=
  Install.transportWithRoots elementSelection arraySelection input parameter numbers one ordinals bottom recognition premises arithmetic
    roots rootProofs (originalSolved roots)

@[irreducible] def branch : ProofSyntax Install.Const
    (Install.assumptions elementSelection arraySelection input parameter numbers one ordinals bottom (Δ := Δ))
    (branchRow elementSelection arraySelection input parameter numbers one ordinals bottom) :=
  Install.transportWithRoots elementSelection arraySelection input parameter numbers one ordinals bottom recognition premises arithmetic
    roots rootProofs (originalBranch roots)

theorem solved_free (recognitionFree : recognition.FunctionExtensionalityFree)
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free)
    (rootsFree : ∀ occurrence, (rootProofs occurrence).FunctionExtensionalityFree) :
    (solved elementSelection arraySelection input parameter numbers one ordinals bottom recognition premises arithmetic
      roots rootProofs).FunctionExtensionalityFree := by
  unfold solved
  exact Install.transportWithRoots_free _ _ _ _ _ _ _ _ _ _ _ _ _ _
    recognitionFree premisesFree arithmeticFree rootsFree (originalSolved_free roots)

theorem branch_free (recognitionFree : recognition.FunctionExtensionalityFree)
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free)
    (rootsFree : ∀ occurrence, (rootProofs occurrence).FunctionExtensionalityFree) :
    (branch elementSelection arraySelection input parameter numbers one ordinals bottom recognition premises arithmetic
      roots rootProofs).FunctionExtensionalityFree := by
  unfold branch
  exact Install.transportWithRoots_free _ _ _ _ _ _ _ _ _ _ _ _ _ _
    recognitionFree premisesFree arithmeticFree rootsFree (originalBranch_free roots)

#print axioms solved_free
#print axioms branch_free
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeInstalledCaseRows
