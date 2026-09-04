import Mettapedia.GSLT.LanguageDef.NIKAuthorityCategory
import Mettapedia.GSLT.LanguageDef.CertificateGSLTInterpretation

/-!
# Functorial NIK authority generation for semantic CertificateGSLTs

A validated calculus by itself determines derivability but not external
meaning.  This module therefore takes an independently chosen predicate on
ground judgments and forms the category of validated CertificateGSLT
presentations whose primitive rules preserve that predicate.  Morphisms are
derivation-valued interpretations: one source rule may be implemented by an
open target derivation, and interpretation composition is proof substitution.

From every such presentation we generate the direct native clone checker.
Its certificates retain a closed derivation together with its conclusion;
checking compares that retained conclusion with the submitted claim.  Every
semantic interpretation transports those certificates by recursively mapping
their derivations.  The resulting checker square commutes exactly, and the
construction preserves identity and composition.  Hence this is an actual
functor from a nontrivial category of semantically qualified presentations to
the heterogeneous NIK authority category.

The claim representation is fixed to ground `Pattern`s in this first theorem.
Syntax-translating interpretations require an additional claim map and are a
strict later generalization.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLTAuthorityFunctor

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.NIKAuthorityCategory
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

/-- Semantic preservation required of every primitive rule application in one
validated presentation. -/
abbrev RulesSound (object : CertificateGSLT.Object)
    (Meaning : Pattern -> Prop) : Prop :=
  forall ruleInstance premises conclusion,
    RuleApplication object.definition ruleInstance premises conclusion ->
      (forall premise, premise ∈ premises -> Meaning premise) ->
        Meaning conclusion

/-- A validated CertificateGSLT together with independent meaning and a proof
that all of its authored rules preserve that meaning. -/
structure SoundPresentation (Meaning : Pattern -> Prop) where
  object : CertificateGSLT.Object
  rulesSound : RulesSound object Meaning

namespace SoundPresentation

variable {Meaning : Pattern -> Prop}

/-- Morphisms are genuine derivation-valued interpretations of the underlying
presentations. -/
@[reducible] instance : CategoryTheory.Category (SoundPresentation Meaning) where
  Hom source target := Interpretation source.object target.object
  id source := Interpretation.id source.object
  comp earlier later := Interpretation.comp earlier later
  id_comp interpretation := by
    apply Interpretation.ext
    intro ruleInstance premises conclusion application
    simp only [Interpretation.comp, Interpretation.mapOpen,
      Interpretation.id]
    rw [Interpretation.mapOpenList_assumptionEnvironment,
      OpenDerivation.bind_assumptionEnvironment]
  comp_id interpretation := by
    apply Interpretation.ext
    intro ruleInstance premises conclusion application
    exact Interpretation.id_mapOpen
      (interpretation.onRule ruleInstance application)
  assoc first second third := by
    apply Interpretation.ext
    intro ruleInstance premises conclusion application
    exact (Interpretation.comp_mapOpen second third
      (first.onRule ruleInstance application)).symm

/-- The semantic interpretation of every native closed derivation follows by
induction over the derivation rather than by replaying the checker. -/
def soundClone (presentation : SoundPresentation Meaning) :
    SoundClone (derivationClone presentation.object) Meaning :=
  NIKMetalogic.CertificateGSLTCloneCanary.soundClone
    presentation.object Meaning presentation.rulesSound

end SoundPresentation

/-! ## Generated theory and native authority -/

/-- The signature fibre is a singleton containing the exact presentation that
generated the authority.  Retaining the presentation makes source identity
visible without introducing irrelevant alternative signatures. -/
def PresentationSignature {Meaning : Pattern -> Prop}
    (presentation : SoundPresentation Meaning) :=
  { object : CertificateGSLT.Object // object = presentation.object }

instance {Meaning : Pattern -> Prop}
    (presentation : SoundPresentation Meaning) :
    Subsingleton (PresentationSignature presentation) where
  allEq left right := by
    apply Subtype.ext
    exact left.property.trans right.property.symm

/-- Native derivability is the inhabited judged proof fibre of the open
derivation clone. -/
def theory {Meaning : Pattern -> Prop}
    (presentation : SoundPresentation Meaning) : TheoryFamily Unit where
  Signature := PresentationSignature presentation
  signatureOf := fun _ => ⟨presentation.object, rfl⟩
  Claim := fun _ => Pattern
  Scope := fun _ claim => Nonempty
    ((cloneNativeProofSystem (derivationClone presentation.object)).ProofFibre
      claim)
  Meaning := fun _ => Meaning
  scope_sound := by
    intro _kind claim inScope
    rcases inScope with ⟨judgedProof⟩
    exact presentation.soundClone.closed_sound
      ((closedProofFibreEquiv (derivationClone presentation.object) claim).symm
        judgedProof)

/-- The generated checker is the direct native clone kernel. -/
def nativeKernel {Meaning : Pattern -> Prop}
    (presentation : SoundPresentation Meaning) :=
  NIKMetalogic.CertificateGSLTCloneCanary.nativeKernel presentation.object

/-- The direct clone checker has exact authority for the generated native
proof scope. -/
def contract {Meaning : Pattern -> Prop}
    (presentation : SoundPresentation Meaning) :
    AuthorityContract (theory presentation) where
  Certificate := fun _ =>
    (cloneNativeProofSystem (derivationClone presentation.object)).ProofObject
  checker := fun _ => (nativeKernel presentation).toChecker
  scopeAuthority := fun _ => (nativeKernel presentation).authority

/-- Bundle one generated theory and checker as an object of the heterogeneous
authority category. -/
def generatedAuthority {Meaning : Pattern -> Prop}
    (presentation : SoundPresentation Meaning) : AuthorityObject where
  Kind := Unit
  family := theory presentation
  contract := contract presentation

/-! ## Action on presentation morphisms -/

/-- Recursively transport the retained native derivation while leaving its
conclusion index unchanged. -/
def mapCertificate {Meaning : Pattern -> Prop}
    {source target : SoundPresentation Meaning}
    (interpretation : Interpretation source.object target.object) :
    (cloneNativeProofSystem (derivationClone source.object)).ProofObject ->
      (cloneNativeProofSystem (derivationClone target.object)).ProofObject
  | ⟨claim, proof⟩ => ⟨claim, interpretation.mapOpen proof⟩

/-- Every semantic presentation interpretation generates an exact authority
translation.  Exact replay is structural: both native kernels compare the
same retained conclusion with the same submitted claim. -/
def map {Meaning : Pattern -> Prop}
    {source target : SoundPresentation Meaning}
    (interpretation : Interpretation source.object target.object) :
    AuthorityTranslation (contract source) (contract target) where
  mapKind := id
  mapSignature := fun _ => ⟨target.object, rfl⟩
  signature_commutes := by intro kind; cases kind; rfl
  mapClaim := fun _ claim => claim
  mapCertificate := fun _ certificate =>
    mapCertificate interpretation certificate
  check_commutes := by
    intro kind claim certificate
    cases kind
    cases certificate
    rfl
  meaning_preserved := by
    intro kind claim meaningful
    exact meaningful

/-- Generated certificate transport preserves the retained conclusion
exactly. -/
@[simp] theorem mapCertificate_claim {Meaning : Pattern -> Prop}
    {source target : SoundPresentation Meaning}
    (interpretation : Interpretation source.object target.object)
    (certificate :
      (cloneNativeProofSystem (derivationClone source.object)).ProofObject) :
    (mapCertificate interpretation certificate).1 = certificate.1 := by
  cases certificate
  rfl

/-- Identity interpretations act identically on generated certificates. -/
@[simp] theorem mapCertificate_id {Meaning : Pattern -> Prop}
    {presentation : SoundPresentation Meaning}
    (certificate :
      (cloneNativeProofSystem
        (derivationClone presentation.object)).ProofObject) :
    mapCertificate (Interpretation.id presentation.object) certificate =
      certificate := by
  rcases certificate with ⟨claim, proof⟩
  simp [mapCertificate]

/-- Certificate transport respects interpretation composition. -/
theorem mapCertificate_comp {Meaning : Pattern -> Prop}
    {first middle last : SoundPresentation Meaning}
    (earlier : Interpretation first.object middle.object)
    (later : Interpretation middle.object last.object)
    (certificate :
      (cloneNativeProofSystem (derivationClone first.object)).ProofObject) :
    mapCertificate (Interpretation.comp earlier later) certificate =
      mapCertificate later (mapCertificate earlier certificate) := by
  rcases certificate with ⟨claim, proof⟩
  simp only [mapCertificate]
  congr 1
  exact Interpretation.comp_mapOpen earlier later proof

/-! ## The generation functor -/

/-- Semantically qualified CertificateGSLT presentations generate exact NIK
authorities functorially. -/
def generationFunctor (Meaning : Pattern -> Prop) :
    CategoryTheory.Functor (SoundPresentation Meaning) AuthorityObject where
  obj := generatedAuthority
  map := by
    intro source target interpretation
    change Interpretation source.object target.object at interpretation
    exact map interpretation
  map_id presentation := by
    apply NIKAuthorityCategory.AuthorityTranslation.ext_data
    · intro kind
      rfl
    · intro signature
      change (⟨presentation.object, rfl⟩ :
          PresentationSignature presentation) = signature
      exact Subtype.ext signature.property.symm
    · intro kind claim
      exact HEq.rfl
    · intro kind certificate
      cases kind
      exact heq_of_eq (mapCertificate_id certificate)
  map_comp earlier later := by
    apply NIKAuthorityCategory.AuthorityTranslation.ext_data
    · intro kind
      rfl
    · intro signature
      rfl
    · intro kind claim
      exact HEq.rfl
    · intro kind certificate
      cases kind
      exact heq_of_eq (mapCertificate_comp earlier later certificate)

/-! ## Positive and negative controls -/

/-- The generated translation exposes its exact replay equation for every
claim and native certificate. -/
theorem generated_map_check_commutes {Meaning : Pattern -> Prop}
    {source target : SoundPresentation Meaning}
    (interpretation : Interpretation source.object target.object)
    (claim : Pattern)
    (certificate : (contract source).Certificate ()) :
    ((contract target).checker ()).check claim
        ((map interpretation).mapCertificate () certificate) =
      ((contract source).checker ()).check claim certificate :=
  (map interpretation).check_commutes () claim certificate

/-- A native derivation is accepted at its retained conclusion. -/
theorem generated_checker_accepts_exact_claim {Meaning : Pattern -> Prop}
    (presentation : SoundPresentation Meaning) {claim : Pattern}
    (proof : (derivationClone presentation.object).Hom [] claim) :
    ((contract presentation).checker ()).check claim ⟨claim, proof⟩ = true := by
  change decide (claim = claim) = true
  simp

/-- The same intrinsically valid derivation is rejected when submitted at a
different claim.  Generated checking therefore does not erase its conclusion
index. -/
theorem generated_checker_rejects_wrong_claim {Meaning : Pattern -> Prop}
    (presentation : SoundPresentation Meaning) {actual submitted : Pattern}
    (different : actual ≠ submitted)
    (proof : (derivationClone presentation.object).Hom [] actual) :
    ((contract presentation).checker ()).check submitted ⟨actual, proof⟩ =
      false := by
  change decide (actual = submitted) = false
  rw [decide_eq_false_iff_not]
  exact different

#print axioms SoundPresentation.soundClone
#print axioms contract
#print axioms map
#print axioms mapCertificate_id
#print axioms mapCertificate_comp
#print axioms generationFunctor
#print axioms generated_map_check_commutes
#print axioms generated_checker_accepts_exact_claim
#print axioms generated_checker_rejects_wrong_claim

end Mettapedia.GSLT.LanguageDef.CertificateGSLTAuthorityFunctor
