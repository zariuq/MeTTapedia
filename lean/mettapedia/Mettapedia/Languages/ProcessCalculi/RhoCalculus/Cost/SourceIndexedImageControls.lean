import Mettapedia.GSLT.LanguageDef.Cost.SourceIndexedSemanticImage
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.KeyObservationControls
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostCanonicalLaws

/-!
# Actual rho inhabitants of the static source-indexed compiler image

Zero, parallel zero, and the selected inert Drop of quoted zero all admit
the existing static insertion.  Their retained compiler outputs retain the
complete authored patterns, while their original source keys distinguish
canonical classes rather than literal syntax.  A closed typed input is
excluded: the selected input constructor is an interaction principal, whose
continuation parameter requires the position-sensitive Cost translation.

These controls concern the generated retained semantic carrier.  They do not
construct funded executions, compile every source program, or authorize
current-layer purses inside quoted code at a later Cost layer.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SourceIndexedImageControls

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open LanguageDefGSLT LanguageDefRewriteSystem LanguageDefSemanticAgreement
open LanguageDefContinuedInteraction CostCanonicalLaws
open Mettapedia.GSLT.LanguageDef.Cost.SourceIndexedSemanticImage

set_option autoImplicit false

def zeroSource : CertifiedSource rhoCIGSLT := by
  refine ⟨KeyObservationControls.asKeyCarrier KeyObservationControls.zero, ?_⟩
  apply (KeyObservationControls.asKeyCarrier KeyObservationControls.zero).2.1.1.withConstructors
  · exact (checkConstructorsIn_eq_true_iff _ _).mp (by decide +kernel)
  · exact rhoBareCollectionConstructorsWrapped

def parallelZeroSource : CertifiedSource rhoCIGSLT := by
  refine ⟨KeyObservationControls.asKeyCarrier KeyObservationControls.parallelZero, ?_⟩
  apply (KeyObservationControls.asKeyCarrier KeyObservationControls.parallelZero).2.1.1.withConstructors
  · exact (checkConstructorsIn_eq_true_iff _ _).mp (by decide +kernel)
  · exact rhoBareCollectionConstructorsWrapped

def freeDropSource : CertifiedSource rhoCIGSLT := by
  refine ⟨KeyObservationControls.asKeyCarrier closedFreeDrop, ?_⟩
  apply (KeyObservationControls.asKeyCarrier closedFreeDrop).2.1.1.withConstructors
  · exact (checkConstructorsIn_eq_true_iff _ _).mp (by decide +kernel)
  · exact rhoBareCollectionConstructorsWrapped

def zeroImage (color : CostStaticColor) :=
  ofSource rhoCIGSLT rho_costStaticCanonicalPathSafe color zeroSource

def parallelZeroImage (color : CostStaticColor) :=
  ofSource rhoCIGSLT rho_costStaticCanonicalPathSafe color parallelZeroSource

def freeDropImage (color : CostStaticColor) :=
  ofSource rhoCIGSLT rho_costStaticCanonicalPathSafe color freeDropSource

/-- Each selected generated colour has an actual retained source-image inhabitant. -/
theorem compiler_image_inhabited (color : CostStaticColor) :
    Nonempty (Carrier rhoCIGSLT rho_costStaticCanonicalPathSafe color) :=
  ⟨zeroImage color⟩

/-- Initial retained output is lossless at the complete authored literal term. -/
theorem parallel_compile_ne_zero (color : CostStaticColor) :
    compile rhoCIGSLT rho_costStaticCanonicalPathSafe color parallelZeroSource ≠
      compile rhoCIGSLT rho_costStaticCanonicalPathSafe color zeroSource := by
  intro equality
  have sourceEquality := compile_injective rhoCIGSLT
    rho_costStaticCanonicalPathSafe color equality
  exact KeyObservationControls.parallelZero_literal_ne_zero
    (congrArg (fun term : CertifiedSource rhoCIGSLT => term.1.1) sourceEquality)

/-- Keeping literal source evidence does not confuse its canonical-class observation. -/
theorem parallel_image_key_eq_zero (color : CostStaticColor) :
    sourceKey (parallelZeroImage color) = sourceKey (zeroImage color) :=
  KeyObservationControls.parallelZero_key_eq_zero

/-- The original-key observation of the constructed carrier is nonconstant. -/
theorem freeDrop_image_key_ne_zero (color : CostStaticColor) :
    sourceKey (freeDropImage color) ≠ sourceKey (zeroImage color) :=
  KeyObservationControls.freeDrop_key_ne_zero

/-- Actual in-place normalization retains the original whole rho key. -/
theorem normalize_parallel_image_key (color : CostStaticColor) :
    sourceKey (normalize (safe := rho_costStaticCanonicalPathSafe)
      (parallelZeroImage color)) = sourceKey (zeroImage color) :=
  parallel_image_key_eq_zero color

/-- A closed input with a closed quoted channel is admitted source syntax. -/
def closedInput : RhoProcess :=
  ⟨.apply "PInput"
    [.apply "NQuote" [.apply "PZero" []], .lambda none (.apply "PZero" [])],
    (rhoClosedTermWellSorted_process_iff _).mpr
      ⟨.input (.quote .unit) .unit, by decide +kernel⟩⟩

/-- The actual source carrier contains this principal-bearing term. -/
def closedInputSource : rhoCIGSLT.CanonicalCarrier :=
  KeyObservationControls.asKeyCarrier closedInput

/-- The uniform static insertion genuinely omits an admitted interaction principal. -/
theorem closedInput_not_certified :
    ¬ WellSorted.HasTypeWithConstructors
      rhoCIGSLT.theory.presentation.presentation.language
      (· ∈ rhoCIGSLT.continuationRetyping.wrappedLabels)
      WellSorted.FreeTypeContext.empty [] closedInputSource.1
      (.base rhoCIGSLT.theory.presentation.interactingLangSort.1) := by
  intro supported
  have constructorAllowed := supported.constructorsWithin
  change "PInput" ∈ rhoCIGSLT.continuationRetyping.wrappedLabels ∧ _
    at constructorAllowed
  exact (by decide +kernel :
    ¬ "PInput" ∈ rhoCIGSLT.continuationRetyping.wrappedLabels) constructorAllowed.1

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SourceIndexedImageControls
