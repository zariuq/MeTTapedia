import Mettapedia.Languages.Agda.Core.Presentation
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenSearchModalAdequacy

/-!
# Qualification boundaries of the Agda rule presentation

Local rule validity and finite-Horn projectability are checked here. The modal
statement concerns the native inference/search GSLT, not reduction of Agda
programs and not the scheduling of the C worklist. Source-calculus adequacy and
the native implementation correspondence remain separate obligations.
-/

namespace Mettapedia.Languages.Agda.Core

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenSearchMachine
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenSearchModalAdequacy
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem presentation_valid : presentation.isValid = true := by decide +kernel

def validated : ValidatedCalculusLanguageDef := ⟨presentation, presentation_valid⟩

theorem finiteHorn_projectable : rendered.isSome = true := by decide +kernel

/-- The optional binary certificate root imposes no restriction on the arity
of typed conversion as an ordinary native judgment. -/
theorem typed_conversion_is_declared :
    presentation.lookupJudgment? "AgdaEqual" 5 = some { head := "AgdaEqual", arity := 5 } := by
  decide

theorem no_binary_conversion_root : presentation.conversion = none := by decide +kernel

/-- This is a connection to behavioral logic about inference states. It makes
no assertion that an Agda source parser or a term-reduction OSLF was built. -/
theorem derivation_iff_inference_diamond (goal : Pattern) :
    Nonempty { d : OpenDerivation validated [] goal // holeOccurrences d = [] } ↔
      gsltDiamond (theory validated []).closure
        (fun candidate => candidate = (⟨[], []⟩ : State []))
        ⟨[goal], []⟩ :=
  exactDischarge_iff_closureDiamond validated [] goal []

end Mettapedia.Languages.Agda.Core

#print axioms Mettapedia.Languages.Agda.Core.presentation_valid
#print axioms Mettapedia.Languages.Agda.Core.finiteHorn_projectable
#print axioms Mettapedia.Languages.Agda.Core.derivation_iff_inference_diamond
