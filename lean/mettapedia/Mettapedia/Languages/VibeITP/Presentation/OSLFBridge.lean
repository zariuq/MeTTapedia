import Mettapedia.Languages.VibeITP.Presentation.CompleteCorrespondence
import Mettapedia.GSLT.LanguageDef.CalculusOSLFSemantics

/-!
# Vibe derivations as OSLF proof-search behavior

The admitted Vibe calculus induces a GSLT of ordered proof obligations.
Its generated OSLF reachability type agrees with the independent static
kernel and with accepted NIK articles. The source-specific content comes
from the existing complete kernel correspondence; the proof-search and
native-type constructions are shared. These results do not assert native C
correspondence or include machine-code execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
open Mettapedia.GSLT.LanguageDef.CalculusOSLFSemantics
open Mettapedia.Languages.VibeITP.Spec

/-- The generated reachability type covers every judgment of the actual
theory-extended package, including its auxiliary operation judgments. -/
theorem kernel_nativeType_iff_foDerivable (T : Theory) (n : Nat) (goal : Pattern) :
    (gsltOSLF (proofSearchGSLT (kernelValidated T n))).satisfies [goal]
        (derivableNativeType (kernelValidated T n)).pred ↔
      FODerivable (kernelRules ++ theoryRules T n) goal :=
  (satisfies_derivableNativeType_iff_derivation (kernelValidated T n) goal).trans
    (derivation_iff_foDerivable (kernelValidated_presents T n) goal)

/-- Behavioral type membership is exactly independent static derivability
under the structural hosting conditions of the Vibe theory. -/
theorem kernel_nativeType_iff_derives {T : Theory} {n : Nat}
    (hosted : Hosted T n) (statement : Term) :
    (gsltOSLF (proofSearchGSLT (kernelValidated T n))).satisfies
        [jThm (encTerm T.sig statement)]
        (derivableNativeType (kernelValidated T n)).pred ↔
      Derives T statement :=
  (kernel_nativeType_iff_foDerivable T n _).trans
    (derives_iff_foDerivable hosted statement).symm

/-- A native-type inhabitant has a finite article accepted by the generic
checker, and every accepted article witnesses that same behavioral type. -/
theorem kernel_nativeType_iff_checkRaw (T : Theory) (n : Nat) (goal : Pattern) :
    (gsltOSLF (proofSearchGSLT (kernelValidated T n))).satisfies [goal]
        (derivableNativeType (kernelValidated T n)).pred ↔
      ∃ article : RawProof, checkRaw (kernelValidated T n) goal article = true :=
  (kernel_nativeType_iff_foDerivable T n goal).trans
    (checkRaw_exists_iff_foDerivable (kernelValidated_presents T n) goal).symm

/-- Discharging all proof obligations and independent kernel derivability
coincide; no terminating proof-search strategy is assumed. -/
theorem kernel_proofSearch_iff_derives {T : Theory} {n : Nat}
    (hosted : Hosted T n) (statement : Term) :
    (proofSearchGSLT (kernelValidated T n)).MultiStep
        [jThm (encTerm T.sig statement)] [] ↔
      Derives T statement :=
  (derivation_nonempty_iff_proofSearch (kernelValidated T n) _).symm.trans
    ((derivation_iff_foDerivable (kernelValidated_presents T n) _).trans
      (derives_iff_foDerivable hosted statement).symm)

end Mettapedia.Languages.VibeITP.Presentation
