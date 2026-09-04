import Mettapedia.GSLT.LanguageDef.CertificateGSLTStoneGunkSemanticAuthority
import Mettapedia.GSLT.LanguageDef.CertificateGSLTUltrafilterSemanticAuthority

/-!
# Ordinary Stone meaning and ultrafilter-relative meaning share one checker

The concrete Cantor-clopen calculus has an ordinary structural semantics.
This module equips the same calculus with a coordinate atlas.  Every ordinary
Stone-gunk fact holds at every coordinate, while one additional declared
verdict holds at all nonzero coordinates.

At the principal view at zero, ultrafilter-relative meaning is exactly the
ordinary structural meaning.  At the free hyperfilter, every ordinary fact
is still meaningful and the cofinite verdict is meaningful as well.  The
identity judgment map consequently gives semantic embeddings from ordinary
meaning to both selected views, but no identity-on-claims semantic embedding
can return from the free view to ordinary meaning.

The underlying CertificateGSLT object, certificate representation, and
checker are unchanged throughout.  This is a basis-comparison theorem, not a
claim that either semantic basis is uniquely foundational.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLTStoneUltraBasisBridge

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLTHeterogeneousAuthority
open Mettapedia.GSLT.LanguageDef.CertificateGSLTUltrafilterSemanticAuthority
open Mettapedia.GSLT.LanguageDef.CertificateGSLTStoneGunkSemanticAuthority
open Mettapedia.Logic.Metaphysics

/-- A semantic verdict deliberately absent from the ordinary Stone model but
true on the cofinite tail of the coordinate atlas. -/
def cofinitePerspectiveClaim : Pattern :=
  .apply "stone-cofinite-perspective" []

/-- Every ordinary Stone fact is coordinate-invariant.  The additional
perspective verdict records a genuine tail-dependent semantic extension. -/
def meaningAt (index : ℕ) (claim : Pattern) : Prop :=
  Meaning claim ∨
    (claim = cofinitePerspectiveClaim ∧ index ≠ 0)

theorem coordinate_rules_sound :
    CoordinateRulesSound object meaningAt := by
  intro ruleInstance premises conclusion application index _premisesMeaning
  change RuleApplication validated ruleInstance premises conclusion at application
  rcases application_shape ruleInstance application with
      ⟨_, conclusionShape⟩ |
      ⟨_, conclusionShape⟩ |
      ⟨_, conclusionShape⟩
  · subst conclusion
    exact Or.inl gunk_has_independent_meaning
  · subst conclusion
    exact Or.inl freeUltrafilter_has_independent_meaning
  · subst conclusion
    exact Or.inl perfectStone_has_independent_meaning

def perspectivePresentation : PerspectivePresentation ℕ where
  object := object
  meaningAt := meaningAt
  rulesSoundAt := coordinate_rules_sound

def principalPresentation : SemanticPresentation :=
  perspectivePresentation.select (pure 0)

noncomputable def freePresentation : SemanticPresentation :=
  perspectivePresentation.select (Filter.hyperfilter ℕ)

/-! ## Principal calibration -/

/-- The principal zero view recovers the ordinary structural meaning for
every ground claim, not only for the selected positive examples. -/
theorem principal_meaning_iff_ordinary (claim : Pattern) :
    principalPresentation.Meaning claim ↔ Meaning claim := by
  change UltraMeaning (pure 0) meaningAt claim ↔ Meaning claim
  rw [ultraMeaning_pure]
  simp [meaningAt]

def ordinaryToPrincipal :
    SemanticEmbedding presentation principalPresentation where
  proof := JudgmentEmbedding.identity object
  meaning_preserved := by
    intro claim meaningful
    exact (principal_meaning_iff_ordinary claim).mpr meaningful

def principalToOrdinary :
    SemanticEmbedding principalPresentation presentation where
  proof := JudgmentEmbedding.identity object
  meaning_preserved := by
    intro claim meaningful
    exact (principal_meaning_iff_ordinary claim).mp meaningful

/-- Principal calibration is a two-way semantic equivalence over the identity
ground-judgment representation. -/
theorem principal_calibration_two_way :
    (∀ claim, Meaning claim → principalPresentation.Meaning claim) ∧
      (∀ claim, principalPresentation.Meaning claim → Meaning claim) :=
  ⟨ordinaryToPrincipal.meaning_preserved,
    principalToOrdinary.meaning_preserved⟩

/-! ## Free-perspective extension -/

def ordinaryToFree :
    SemanticEmbedding presentation freePresentation where
  proof := JudgmentEmbedding.identity object
  meaning_preserved := by
    intro claim meaningful
    change UltraMeaning (Filter.hyperfilter ℕ) meaningAt claim
    exact Filter.Eventually.of_forall (fun _index => Or.inl meaningful)

theorem ordinary_meaning_survives_free (claim : Pattern)
    (meaningful : Meaning claim) :
    freePresentation.Meaning claim :=
  ordinaryToFree.meaning_preserved claim meaningful

/-- The cofinite verdict is selected by the free hyperfilter. -/
theorem cofinitePerspective_free_meaning :
    freePresentation.Meaning cofinitePerspectiveClaim := by
  change UltraMeaning (Filter.hyperfilter ℕ) meaningAt
    cofinitePerspectiveClaim
  exact hyperfilter_pure_disagree.1.mono (by
    intro index nonzero
    exact Or.inr ⟨rfl, nonzero⟩)

/-- The same verdict is not part of the ordinary structural semantics. -/
theorem cofinitePerspective_not_ordinary :
    ¬ Meaning cofinitePerspectiveClaim := by
  rw [meaning_iff_selected_positive_claims]
  simp [cofinitePerspectiveClaim, gunkClaim,
    freeUltrafilterClaim, perfectStoneClaim]

/-- Principal calibration rejects the tail-only verdict. -/
theorem cofinitePerspective_not_principal :
    ¬ principalPresentation.Meaning cofinitePerspectiveClaim := by
  rw [principal_meaning_iff_ordinary]
  exact cofinitePerspective_not_ordinary

/-- The free semantic extension cannot be reflected to ordinary meaning while
every claim keeps its spelling. -/
theorem no_identity_semantic_embedding_free_to_ordinary :
    ¬ ∃ translation :
        SemanticEmbedding freePresentation presentation,
      translation.proof.mapClaim = id := by
  rintro ⟨translation, identityMap⟩
  have ordinaryTail := translation.meaning_preserved
    cofinitePerspectiveClaim cofinitePerspective_free_meaning
  have mapsTail :
      translation.proof.mapClaim cofinitePerspectiveClaim =
        cofinitePerspectiveClaim :=
    congrFun identityMap cofinitePerspectiveClaim
  rw [mapsTail] at ordinaryTail
  exact cofinitePerspective_not_ordinary ordinaryTail

/-- The ordinary and free selected meanings are genuinely different
predicates despite sharing their calculus and checker. -/
theorem ordinary_and_free_meanings_differ :
    Meaning ≠ freePresentation.Meaning := by
  intro equality
  apply cofinitePerspective_not_ordinary
  rw [equality]
  exact cofinitePerspective_free_meaning

/-! ## Operational invariance -/

/-- Selecting another semantic basis does not alter native replay. -/
theorem perfectStone_checker_basis_invariant :
    ((contract presentation).checker ()).check
        perfectStoneClaim perfectStoneCertificate =
      ((contract freePresentation).checker ()).check
        perfectStoneClaim perfectStoneCertificate :=
  rfl

theorem free_checker_accepts_perfectStone :
    ((contract freePresentation).checker ()).check
        perfectStoneClaim perfectStoneCertificate = true :=
  perfectStone_certificate_accepted

/-- Semantic extension cannot make a certificate for a different retained
conclusion pass as evidence for the cofinite verdict. -/
theorem perfectStone_certificate_rejected_at_cofinitePerspective :
    ((contract freePresentation).checker ()).check
        cofinitePerspectiveClaim perfectStoneCertificate = false := by
  change decide
    (perfectStoneClaim = cofinitePerspectiveClaim) = false
  decide

/-- The free-perspective verdict is meaningful but remains outside native
proof scope.  Semantic extension therefore does not rewrite the calculus. -/
theorem cofinitePerspective_meaning_but_not_scope :
    freePresentation.Meaning cofinitePerspectiveClaim ∧
      ¬ (theory freePresentation).Scope () cofinitePerspectiveClaim := by
  refine ⟨cofinitePerspective_free_meaning, ?_⟩
  rintro ⟨judgedProof⟩
  have closed :
      (derivationClone object).Hom [] cofinitePerspectiveClaim :=
    (closedProofFibreEquiv (derivationClone object)
      cofinitePerspectiveClaim).symm judgedProof
  rcases closed_derivation_conclusion closed with
      conclusionShape | conclusionShape | conclusionShape <;>
    simp [cofinitePerspectiveClaim, gunkClaim,
      freeUltrafilterClaim, perfectStoneClaim] at conclusionShape

#print axioms coordinate_rules_sound
#print axioms principal_meaning_iff_ordinary
#print axioms principal_calibration_two_way
#print axioms ordinary_meaning_survives_free
#print axioms cofinitePerspective_free_meaning
#print axioms no_identity_semantic_embedding_free_to_ordinary
#print axioms ordinary_and_free_meanings_differ
#print axioms perfectStone_checker_basis_invariant
#print axioms cofinitePerspective_meaning_but_not_scope

end Mettapedia.GSLT.LanguageDef.CertificateGSLTStoneUltraBasisBridge
