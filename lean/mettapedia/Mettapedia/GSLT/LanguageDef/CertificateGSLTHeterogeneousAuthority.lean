import Mettapedia.GSLT.LanguageDef.CertificateGSLTAuthorityFunctor
import Mettapedia.GSLT.LanguageDef.CertificateGSLTJudgmentEmbedding

/-!
# Heterogeneous semantic authority generation for CertificateGSLTs

The first CertificateGSLT generation functor fixes one predicate on a common
ground-judgment representation.  This module separates the two restrictions.
Each presentation owns its independently selected meaning predicate, and a
morphism may inject source judgments into a different target representation.

A morphism has two obligations which must not be conflated:

* a proof-relevant `JudgmentEmbedding` implements every source rule by a
  target open derivation over the pointwise embedded premise occurrences; and
* semantic preservation maps independently supplied source meaning into
  independently supplied target meaning.

Generated certificates retain both the translated conclusion and translated
derivation.  Injectivity of the judgment map is exactly what makes native
checker replay commute in both the accepting and rejecting cases.  No
semantic predicate is defined from checker acceptance.

This remains the ground action of a future binding-signature translation.  It
does not claim to translate ABT constructors or binding signatures.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.NIKAuthorityCategory
open Mettapedia.GSLT.LanguageDef.NIKHeterogeneousTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLTAuthorityFunctor

/-- A validated ground CertificateGSLT with its own independent semantics. -/
structure SemanticPresentation where
  object : CertificateGSLT.Object
  Meaning : Pattern → Prop
  rulesSound : RulesSound object Meaning

namespace SemanticPresentation

/-- Forget that the meaning predicate varies between objects. -/
def toSoundPresentation (presentation : SemanticPresentation) :
    SoundPresentation presentation.Meaning where
  object := presentation.object
  rulesSound := presentation.rulesSound

/-- Semantic validity of all closed native derivations is inherited from the
authored primitive-rule preservation theorem. -/
def soundClone (presentation : SemanticPresentation) :
    SoundClone (derivationClone presentation.object) presentation.Meaning :=
  presentation.toSoundPresentation.soundClone

end SemanticPresentation

/-- A heterogeneous semantic presentation morphism changes ground judgments,
implements source rules proof-relevantly, and preserves independent meaning. -/
structure SemanticEmbedding
    (source target : SemanticPresentation) where
  proof : JudgmentEmbedding source.object target.object
  meaning_preserved : ∀ claim,
    source.Meaning claim → target.Meaning (proof.mapClaim claim)

namespace SemanticEmbedding

/-- Semantic identity retains both judgments and meaning. -/
def identity (presentation : SemanticPresentation) :
    SemanticEmbedding presentation presentation where
  proof := JudgmentEmbedding.identity presentation.object
  meaning_preserved := by
    intro claim meaningful
    exact meaningful

/-- Semantic embeddings compose by proof substitution and ordinary semantic
implication. -/
def comp {first middle last : SemanticPresentation}
    (earlier : SemanticEmbedding first middle)
    (later : SemanticEmbedding middle last) :
    SemanticEmbedding first last where
  proof := JudgmentEmbedding.comp earlier.proof later.proof
  meaning_preserved := by
    intro claim meaningful
    exact later.meaning_preserved _ (earlier.meaning_preserved claim meaningful)

end SemanticEmbedding

/-! ## Generated heterogeneous theories and authorities -/

/-- The generated theory keeps the exact source presentation in its singleton
signature fibre and uses that presentation's independent meaning. -/
def theory (presentation : SemanticPresentation) : TheoryFamily Unit :=
  CertificateGSLTAuthorityFunctor.theory presentation.toSoundPresentation

/-- The generated direct native clone checker. -/
def nativeKernel (presentation : SemanticPresentation) :=
  CertificateGSLTAuthorityFunctor.nativeKernel presentation.toSoundPresentation

/-- Exact authority for native derivability of one heterogeneous semantic
presentation. -/
def contract (presentation : SemanticPresentation) :
    AuthorityContract (theory presentation) :=
  CertificateGSLTAuthorityFunctor.contract presentation.toSoundPresentation

/-- Bundle a semantic presentation and its generated checker as a NIK
authority object. -/
def generatedAuthority (presentation : SemanticPresentation) :
    AuthorityObject where
  Kind := Unit
  family := theory presentation
  contract := contract presentation

/-! ## Exact action on heterogeneous semantic embeddings -/

/-- Translate both the retained conclusion and its closed derivation. -/
def mapCertificate {source target : SemanticPresentation}
    (translation : SemanticEmbedding source target) :
    (cloneNativeProofSystem (derivationClone source.object)).ProofObject →
      (cloneNativeProofSystem (derivationClone target.object)).ProofObject
  | ⟨claim, derivation⟩ =>
      ⟨translation.proof.mapClaim claim,
        translation.proof.mapOpen derivation⟩

@[simp] theorem mapCertificate_claim
    {source target : SemanticPresentation}
    (translation : SemanticEmbedding source target)
    (certificate :
      (cloneNativeProofSystem (derivationClone source.object)).ProofObject) :
    (mapCertificate translation certificate).1 =
      translation.proof.mapClaim certificate.1 := by
  cases certificate
  rfl

/-- A heterogeneous semantic embedding generates an exact NIK authority
translation.  Injectivity reflects the retained-conclusion comparison made by
the target checker back to the source comparison. -/
def map {source target : SemanticPresentation}
    (translation : SemanticEmbedding source target) :
    AuthorityTranslation (contract source) (contract target) where
  mapKind := id
  mapSignature := fun _ => ⟨target.object, rfl⟩
  signature_commutes := by intro kind; cases kind; rfl
  mapClaim := fun _ claim => translation.proof.mapClaim claim
  mapCertificate := fun _ certificate => mapCertificate translation certificate
  check_commutes := by
    intro kind claim certificate
    cases kind
    change Pattern at claim
    rcases certificate with ⟨actual, derivation⟩
    change decide
        (translation.proof.mapClaim actual =
          translation.proof.mapClaim claim) =
      decide (actual = claim)
    by_cases equal : actual = claim
    · subst claim
      simp
    · have mappedDifferent :
          translation.proof.mapClaim actual ≠
            translation.proof.mapClaim claim := by
        intro collision
        exact equal (translation.proof.mapClaim_injective collision)
      simp [equal, mappedDifferent]
  meaning_preserved := by
    intro kind claim meaningful
    exact translation.meaning_preserved claim meaningful

/-- Scope preservation is derived from exact replay rather than added as an
independent premise. -/
theorem map_scope_preserved {source target : SemanticPresentation}
    (translation : SemanticEmbedding source target)
    (claim : Pattern) (inScope : (theory source).Scope () claim) :
    (theory target).Scope () (translation.proof.mapClaim claim) :=
  (map translation).scope_preserved () claim inScope

/-- The generated theory translation exposes independent semantic
preservation at the translated claim. -/
theorem map_meaning_preserved {source target : SemanticPresentation}
    (translation : SemanticEmbedding source target)
    (claim : Pattern) (meaningful : source.Meaning claim) :
    target.Meaning (translation.proof.mapClaim claim) :=
  (map translation).meaning_preserved () claim meaningful

/-- Exact checker replay includes negative results: changing syntax cannot
turn a rejected retained-conclusion comparison into acceptance. -/
theorem map_check_commutes {source target : SemanticPresentation}
    (translation : SemanticEmbedding source target)
    (claim : Pattern) (certificate : (contract source).Certificate ()) :
    ((contract target).checker ()).check
        (translation.proof.mapClaim claim)
        ((map translation).mapCertificate () certificate) =
      ((contract source).checker ()).check claim certificate :=
  (map translation).check_commutes () claim certificate

/-! ## Collision and rejection controls -/

/-- A source certificate submitted at the wrong source claim remains rejected
after heterogeneous transport. -/
theorem mapped_certificate_rejects_wrong_claim
    {source target : SemanticPresentation}
    (translation : SemanticEmbedding source target)
    {actual submitted : Pattern} (different : actual ≠ submitted)
    (derivation : (derivationClone source.object).Hom [] actual) :
    ((contract target).checker ()).check
        (translation.proof.mapClaim submitted)
        (mapCertificate translation ⟨actual, derivation⟩) = false := by
  change decide
      (translation.proof.mapClaim actual =
        translation.proof.mapClaim submitted) = false
  rw [decide_eq_false_iff_not]
  intro collision
  exact different (translation.proof.mapClaim_injective collision)

/-- Exact heterogeneous generation cannot be instantiated with a claim map
that merges two distinguishable source judgments. -/
theorem no_collision_in_generated_map
    {source target : SemanticPresentation}
    (translation : SemanticEmbedding source target)
    {left right : Pattern} (different : left ≠ right) :
    translation.proof.mapClaim left ≠ translation.proof.mapClaim right := by
  intro collision
  exact different (translation.proof.mapClaim_injective collision)

#print axioms SemanticPresentation.soundClone
#print axioms map
#print axioms map_scope_preserved
#print axioms map_meaning_preserved
#print axioms map_check_commutes
#print axioms mapped_certificate_rejects_wrong_claim
#print axioms no_collision_in_generated_map

end Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority
