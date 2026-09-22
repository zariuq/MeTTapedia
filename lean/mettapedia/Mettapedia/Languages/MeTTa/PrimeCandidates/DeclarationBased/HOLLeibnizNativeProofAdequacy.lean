import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLLeibnizRepresentationSemantics
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizMapFusionNative

/-!
# Compiled HOL proofs and their independently interpreted conclusions

The actual proof compiler, its native typing theorem and the constructorwise
Henkin interpretation meet at the very same represented proposition. Source
proof soundness supplies truth of that proposition's independently defined
meaning. This is source adequacy of successful translation, not a soundness
theorem for arbitrary native inhabitants or a model of the entire decoder.

The map-fusion instance traverses the original proof, abstracting its five
original theory assumptions as explicit inputs. Those inputs are not silently
replaced by native inductive declarations.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLLeibnizNativeProofAdequacy

open Presentation Mettapedia.Logic HOL.UniformListInduction
open NativeHOLFragmentDenotation HOLLeibnizRepresentationSemantics

universe w
variable {model : HOL.HenkinModel.{0, 0, w} BaseSort Symbol}

/-- Successful source compilation supplies native admission, a separately
constructed interpretation of its conclusion and source-justified truth.
No semantic interpretation is defined to mean compiler acceptance. -/
theorem compiled_closed_adequacy {phi : Sentence []}
    (source : HOL.ProofSyntax Symbol [] phi) {native : Tower.Tm 0}
    (compiled : HOLLeibnizNativeProofTranslation.compile source Fin.elim0 Fin.elim0 = some native)
    (respects : model.FunctionsRespectEqv)
    (valuation : model.Valuation []) (admissible : model.ValuationAdmissible valuation) :
    ∃ code, FormationSensitiveHOLInterface.represent New.signature phi = some code ∧
      FormationSensitive.Judgment FormationSensitiveHOLProofFamily.rules .nil native
        (FormationSensitiveHOLProofFamily.proof code) ∧
      Denotes model (type := .prop) code (fun rho => model.denote (expand phi) rho) ∧
      (model.denote (expand phi) valuation).down := by
  obtain ⟨code, represented, typed⟩ :=
    HOLLeibnizNativeProofTranslation.NativeTyping.compile_closed source compiled
  have represented' : FormationSensitiveHOLInterface.represent New.signature phi = some code := represented
  obtain ⟨meaning, agrees⟩ := native_representation_meaning phi represented' respects valuation admissible
  have sourceTruth := HOL.Soundness.extDerivation_sound source.erase respects admissible
    (by intro formula member; cases member)
  exact ⟨code, represented', typed, meaning, agrees.mpr sourceTruth⟩

theorem original_map_fusion_crossing
    (respects : model.FunctionsRespectEqv)
    (valuation : model.Valuation []) (admissible : model.ValuationAdmissible valuation) :
    ∃ code,
      HOLLeibnizNativeProofTranslation.compile HOLLeibnizMapFusionNative.closedProof
        Fin.elim0 Fin.elim0 = some HOLLeibnizMapFusionNative.nativeProof ∧
      FormationSensitiveHOLInterface.represent New.signature HOLLeibnizMapFusionNative.closedClaim = some code ∧
      FormationSensitive.Judgment FormationSensitiveHOLProofFamily.rules .nil
        HOLLeibnizMapFusionNative.nativeProof (FormationSensitiveHOLProofFamily.proof code) ∧
      Denotes model (type := .prop) code
        (fun rho => model.denote (expand HOLLeibnizMapFusionNative.closedClaim) rho) ∧
      (model.denote (expand HOLLeibnizMapFusionNative.closedClaim) valuation).down := by
  obtain ⟨code, represented, typed, meaning, holds⟩ := compiled_closed_adequacy
    HOLLeibnizMapFusionNative.closedProof HOLLeibnizMapFusionNative.compiler_emits_nativeProof
    respects valuation admissible
  exact ⟨code, HOLLeibnizMapFusionNative.compiler_emits_nativeProof, represented, typed, meaning, holds⟩

/-- Coherence fixes the meaning of the actual output proposition, not only
the canonical semantic witness used in the construction. -/
theorem every_interpretation_of_compiled_conclusion_true {phi : Sentence []}
    (source : HOL.ProofSyntax Symbol [] phi) {native code : Tower.Tm 0}
    (compiled : HOLLeibnizNativeProofTranslation.compile source Fin.elim0 Fin.elim0 = some native)
    (represented : FormationSensitiveHOLInterface.represent New.signature phi = some code)
    {value : model.Valuation [] → HOL.Ty.denote model.Carrier .prop}
    (meaning : Denotes model (gamma := []) (type := .prop) code value)
    (respects : model.FunctionsRespectEqv)
    (valuation : model.Valuation []) (admissible : model.ValuationAdmissible valuation) :
    (value valuation).down := by
  obtain ⟨actualCode, actualRepresented, _, canonical, holds⟩ :=
    compiled_closed_adequacy source compiled respects valuation admissible
  have same : actualCode = code := Option.some.inj (actualRepresented.symm.trans represented)
  subst actualCode
  rw [meaning.coherent canonical valuation]
  exact holds

namespace Controls

theorem falseClaim_has_no_closed_source_proof :
    ¬ Nonempty (HOL.ProofSyntax Symbol [] HOLLeibnizRepresentationSemantics.Controls.falseClaim) := by
  rintro ⟨proof⟩
  have holds := HOL.Soundness.extDerivation_sound proof.erase
    NativeHOLLeibnizDenotation.Controls.standard_respects
    HOLLeibnizRepresentationSemantics.Controls.admissible
    (by intro formula member; cases member)
  change (ULift.up 0 : StandardListModel.LiftedCount) = ULift.up 1 at holds
  cases holds

end Controls

#print axioms compiled_closed_adequacy
#print axioms original_map_fusion_crossing
#print axioms every_interpretation_of_compiled_conclusion_true
#print axioms Controls.falseClaim_has_no_closed_source_proof

end HOLLeibnizNativeProofAdequacy
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
