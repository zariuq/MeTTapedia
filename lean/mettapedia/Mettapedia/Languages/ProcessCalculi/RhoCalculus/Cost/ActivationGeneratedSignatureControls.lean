import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedSignatureStability
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedNormalizationControls

/-!
# Literal signature admission and raw typing boundary

Unit/product object syntax has exact stable keys. A raw typed explicit
substitution can instead change under wrapped normalization, and the actual
signature decoder rejects it. The positive law therefore uses decoder
admission rather than an unrestricted raw typing derivation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedSignatureControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Cost.SignatureSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open ActivationGenerated
open ActivationGeneratedControls

def schemaSignature : Pattern := .subst unitSignature
  (ActivationGeneratedNormalizationControls.quote
    (ActivationGeneratedNormalizationControls.drop
      (ActivationGeneratedNormalizationControls.quote ActivationGeneratedNormalizationControls.zero)))

def normalizedSchemaSignature : Pattern := .subst unitSignature
  (ActivationGeneratedNormalizationControls.quote ActivationGeneratedNormalizationControls.zero)

theorem schema_signature_raw_typed :
    HasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty [] schemaSignature
      (.base costSignatureSortName) := by
  exact .subst (domain := .base (costBaseSortName "Name"))
    (checkHasType_sound (by decide +kernel)) (checkHasType_sound (by decide +kernel))

theorem schema_signature_normalization_changes :
    normalizeReflective wrappedRhoDeclaration schemaSignature = normalizedSchemaSignature := by
  decide +kernel

theorem schema_signature_literal_keys_distinct :
    ({schemaSignature} : CostSig LiteralAuthority) ≠ {normalizedSchemaSignature} := by
  decide +kernel

theorem raw_typed_signature_normalization_identity_fails :
    normalizeReflective wrappedRhoDeclaration schemaSignature ≠ schemaSignature := by
  rw [schema_signature_normalization_changes]
  decide +kernel

theorem schema_signature_rejected_by_actual_decoder : signature? schemaSignature = none := rfl

theorem schema_signature_is_not_object_syntax : isObjectPattern schemaSignature = false := rfl

theorem unit_and_product_admitted : (signature? unitSignature).isSome = true ∧
    (signature? productSignature).isSome = true := by
  decide +kernel

theorem product_exact_key_stable (depth : Nat) (replacement : Pattern) :
    normalizeReflective wrappedRhoDeclaration productSignature = productSignature ∧
    substituteReflective wrappedRhoDeclaration depth replacement productSignature = productSignature :=
  ⟨(LiteralSignatureSyntax.product .unit .unit).normalize_identity,
   (LiteralSignatureSyntax.product .unit .unit).substitute_identity depth replacement⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedSignatureControls
