import Mettapedia.Languages.VibeITP.Presentation.OSLFBridge
import Mettapedia.Languages.VibeITP.Presentation.KernelControls

/-!
# Accepted and impossible behaviors in the Vibe proof-search OSLF

The accepted modus-ponens article witnesses the generated reachability type.
Division by zero has no operation derivation, hence no successful search
trace or reachability-type inhabitant. This is a statement about the
operation judgment, not consistency of the theory's declared axioms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.OSLFControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.CalculusOSLFSemantics
open KernelControls

theorem modus_ponens_has_nativeType :
    (gsltOSLF (proofSearchGSLT (kernelValidated controlTheory 4))).satisfies
        [jThm (encTerm controlTheory.sig atomB)]
        (derivableNativeType (kernelValidated controlTheory 4)).pred :=
  (kernel_nativeType_iff_checkRaw controlTheory 4 _).mpr
    ⟨mpArticle, modus_ponens_accepts⟩

theorem division_zero_has_no_nativeType (a : Nat) (q r : Pattern) :
    ¬ (gsltOSLF (proofSearchGSLT (kernelValidated controlTheory 4))).satisfies
        [jNDivMod (encNat a) (encNat 0) q r]
        (derivableNativeType (kernelValidated controlTheory 4)).pred := by
  intro member
  exact division_zero_no_operation_derivation a q r
    ((kernel_nativeType_iff_foDerivable controlTheory 4 _).mp member)

theorem division_zero_cannot_discharge (a : Nat) (q r : Pattern) :
    ¬ (proofSearchGSLT (kernelValidated controlTheory 4)).MultiStep
        [jNDivMod (encNat a) (encNat 0) q r] [] :=
  division_zero_has_no_nativeType a q r

end Mettapedia.Languages.VibeITP.Presentation.OSLFControls
