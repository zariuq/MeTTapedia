import Mettapedia.TypeTheory.DisplayedPresheafCwf
import Mathlib.CategoryTheory.Yoneda

/-!
# Source CwF types as coherent presheaf families

The Yoneda image of a source context extension displays a semantic family
over the represented context. Its fibre over a substitution consists of
arrows above that substitution. Comprehension identifies these arrows
exactly with source terms of the substituted type.

This construction applies to an existing CwF. It does not assume that its
source is initial or that its types contain any particular type formers.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CwfYoneda

open CategoryTheory Opposite
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension

universe u v w w'

variable (C : Cwf.{u, v, w, w'})

abbrev context (Γ : C.Ctx) : C.base.Context := ⟨Γ⟩

abbrev contextFace (Γ : C.Ctx) := yoneda.obj (context C Γ)

/-- The actual source display map, represented as a presheaf map. -/
def display {Γ : C.Ctx} (A : C.Ty Γ) :
    contextFace C (C.ext Γ A) ⟶ contextFace C Γ :=
  yoneda.map (show context C (C.ext Γ A) ⟶ context C Γ from C.wk A)

/-- A source type interpreted in the existing coherent family carrier. -/
def family {Γ : C.Ctx} (A : C.Ty Γ) :
    DisplayedFamily (contextFace C Γ) :=
  observationFibreFamily (display C A)

def encodeTerm {Γ Δ : C.Ctx} (A : C.Ty Γ) (σ : C.Sub Δ Γ)
    (t : C.Tm Δ (C.tySub A σ)) :
    (family C A).obj ⟨op (context C Δ), σ⟩ :=
  ⟨C.pair σ A t, C.wk_pair σ A t⟩

def decodeTerm {Γ Δ : C.Ctx} (A : C.Ty Γ) (σ : C.Sub Δ Γ)
    (receipt : (family C A).obj ⟨op (context C Δ), σ⟩) :
    C.Tm Δ (C.tySub A σ) :=
  cast (by
    have over : C.compS (C.wk A) receipt.val = σ := receipt.property
    rw [← C.tySub_comp, over]) (C.tmSub (C.vz A) receipt.val)

theorem decode_encode {Γ Δ : C.Ctx} (A : C.Ty Γ) (σ : C.Sub Δ Γ)
    (t : C.Tm Δ (C.tySub A σ)) :
    decodeTerm C A σ (encodeTerm C A σ t) = t := by
  apply eq_of_heq
  exact (cast_heq _ _).trans
    ((heq_of_eq (C.vz_pair σ A t)).trans (cast_heq _ _))

theorem encode_decode {Γ Δ : C.Ctx} (A : C.Ty Γ) (σ : C.Sub Δ Γ)
    (receipt : (family C A).obj ⟨op (context C Δ), σ⟩) :
    encodeTerm C A σ (decodeTerm C A σ receipt) = receipt := by
  apply Subtype.ext
  apply TypeOver.substitution_ext
  · exact (C.wk_pair _ _ _).trans receipt.property.symm
  · exact (heq_of_eq (C.vz_pair _ _ _)).trans
      ((cast_heq _ _).trans (cast_heq _ _))

/-- Every semantic fibre is exactly the corresponding source term type. -/
def termFibreEquiv {Γ Δ : C.Ctx} (A : C.Ty Γ) (σ : C.Sub Δ Γ) :
    C.Tm Δ (C.tySub A σ) ≃
      (family C A).obj ⟨op (context C Δ), σ⟩ where
  toFun := encodeTerm C A σ
  invFun := decodeTerm C A σ
  left_inv := decode_encode C A σ
  right_inv := encode_decode C A σ

/-- Semantic context extension recovers the represented source extension. -/
def comprehensionIso {Γ : C.Ctx} (A : C.Ty Γ) :
    totalSpace (family C A) ≅ contextFace C (C.ext Γ A) :=
  observationTotalIso (display C A)

/-- This recovery also preserves the context-extension projection. -/
theorem comprehension_projection {Γ : C.Ctx} (A : C.Ty Γ) :
    (comprehensionIso C A).hom ≫ display C A =
      totalProjection (family C A) :=
  observationTotalIso_projection (display C A)

/-- Source pairing commutes with substitution, retaining the actual term. -/
theorem pair_compose {Γ Δ Θ : C.Ctx} (A : C.Ty Γ)
    (σ : C.Sub Δ Γ) (τ : C.Sub Θ Δ) (t : C.Tm Δ (C.tySub A σ)) :
    C.compS (C.pair σ A t) τ =
      C.pair (C.compS σ τ) A
        (cast (congrArg (C.Tm Θ) (C.tySub_comp A σ τ).symm)
          (C.tmSub t τ)) := by
  apply TypeOver.substitution_ext
  · rw [← C.comp_assoc, C.wk_pair, C.wk_pair]
  · have paired : HEq (C.tmSub (C.vz A) (C.pair σ A t)) t :=
      (heq_of_eq (C.vz_pair σ A t)).trans (cast_heq _ _)
    have types : C.tySub (C.tySub A (C.wk A)) (C.pair σ A t) =
        C.tySub A σ := by rw [← C.tySub_comp, C.wk_pair]
    exact (TypeOver.tmSub_comp_heq (C.vz A) (C.pair σ A t) τ).trans
      ((TypeOver.tmSub_heq types paired τ).trans
        ((cast_heq _ _).symm.trans
          ((cast_heq _ _).symm.trans (heq_of_eq (C.vz_pair _ _ _)).symm)))

/-- The fibre equivalence intertwines semantic transport and actual source
term substitution. The only adjustment is the CwF's type-composition cast. -/
theorem encodeTerm_substitution {Γ Δ Θ : C.Ctx} (A : C.Ty Γ)
    (σ : C.Sub Δ Γ) (τ : C.Sub Θ Δ) (t : C.Tm Δ (C.tySub A σ)) :
    (family C A).map
        (CategoryOfElements.homMk
          (⟨op (context C Δ), σ⟩ : (contextFace C Γ).Elements)
          ⟨op (context C Θ), C.compS σ τ⟩
          (show op (context C Δ) ⟶ op (context C Θ) from
            (show context C Θ ⟶ context C Δ from τ).op) rfl)
        (encodeTerm C A σ t) =
      encodeTerm C A (C.compS σ τ)
        (cast (congrArg (C.Tm Θ) (C.tySub_comp A σ τ).symm)
          (C.tmSub t τ)) :=
  Subtype.ext (pair_compose C A σ τ t)

/-- A source term gives a natural section of the interpreted family. -/
def interpretTerm {Γ : C.Ctx} {A : C.Ty Γ} (t : C.Tm Γ A) :
    (family C A).sections where
  val point := encodeTerm C A point.2 (C.tmSub t point.2)
  property := by
    rintro ⟨Δ, σ⟩ ⟨Θ, ρ⟩ ⟨τ, follows⟩
    change Δ ⟶ Θ at τ
    change C.Sub Θ.unop.val Γ at ρ
    change C.compS σ τ.unop = ρ at follows
    subst ρ
    apply Subtype.ext
    change C.compS (C.pair σ A (C.tmSub t σ)) τ.unop =
      C.pair (C.compS σ τ.unop) A (C.tmSub t (C.compS σ τ.unop))
    rw [pair_compose, C.tmSub_comp]

/-- Read a natural semantic term at the identity source environment. -/
def recoverTerm {Γ : C.Ctx} {A : C.Ty Γ}
    (sectionValue : (family C A).sections) : C.Tm Γ A :=
  cast (congrArg (C.Tm Γ) (C.tySub_id A))
    (decodeTerm C A (C.idS Γ)
      (sectionValue.val ⟨op (context C Γ), C.idS Γ⟩))

theorem recover_interpret {Γ : C.Ctx} {A : C.Ty Γ} (t : C.Tm Γ A) :
    recoverTerm C (interpretTerm C t) = t := by
  apply eq_of_heq
  exact (cast_heq _ _).trans
    ((heq_of_eq (decode_encode C A (C.idS Γ) (C.tmSub t (C.idS Γ)))).trans
      ((heq_of_eq (C.tmSub_id t)).trans (cast_heq _ _)))

theorem interpret_recover {Γ : C.Ctx} {A : C.Ty Γ}
    (sectionValue : (family C A).sections) :
    interpretTerm C (recoverTerm C sectionValue) = sectionValue := by
  apply (Functor.sections_ext_iff).2
  intro point
  let identityPoint : (contextFace C Γ).Elements :=
    ⟨op (context C Γ), C.idS Γ⟩
  let arrow : identityPoint ⟶ point :=
    ⟨(show point.1.unop ⟶ context C Γ from point.2).op,
      C.id_comp point.2⟩
  have natural := sectionValue.property arrow
  change (family C A).map arrow (sectionValue.val identityPoint) =
    sectionValue.val point at natural
  rw [← natural]
  apply Subtype.ext
  apply TypeOver.substitution_ext
  · change C.compS (C.wk A)
        (C.pair point.2 A (C.tmSub (recoverTerm C sectionValue) point.2)) =
      C.compS (C.wk A) (C.compS (sectionValue.val identityPoint).val point.2)
    rw [C.wk_pair, ← C.comp_assoc]
    have over : C.compS (C.wk A) (sectionValue.val identityPoint).val =
        C.idS Γ := (sectionValue.val identityPoint).property
    rw [over, C.id_comp]
  · have decoded : HEq (recoverTerm C sectionValue)
        (C.tmSub (C.vz A) (sectionValue.val identityPoint).val) :=
      (cast_heq _ _).trans (cast_heq _ _)
    have types : A = C.tySub (C.tySub A (C.wk A))
        (sectionValue.val identityPoint).val := by
      have over : C.compS (C.wk A) (sectionValue.val identityPoint).val =
          C.idS Γ := (sectionValue.val identityPoint).property
      rw [← C.tySub_comp, over, C.tySub_id]
    exact (heq_of_eq (C.vz_pair _ _ _)).trans
      ((cast_heq _ _).trans
        ((TypeOver.tmSub_heq types decoded point.2).trans
          (TypeOver.tmSub_comp_heq (C.vz A)
            (sectionValue.val identityPoint).val point.2).symm))

/-- Natural semantic terms are exactly source terms, not merely sound
observations of them. This is relative to the represented source type. -/
def termSectionEquiv {Γ : C.Ctx} (A : C.Ty Γ) :
    C.Tm Γ A ≃ (family C A).sections where
  toFun := interpretTerm C
  invFun := recoverTerm C
  left_inv := recover_interpret C
  right_inv := interpret_recover C

/-- The source comprehension lift sends a term presentation to that same
term with the type-substitution composition cast. -/
theorem extension_encode {Γ Δ Θ : C.Ctx} (A : C.Ty Γ)
    (σ : C.Sub Δ Γ) (τ : C.Sub Θ Δ)
    (t : C.Tm Θ (C.tySub (C.tySub A σ) τ)) :
    C.compS (TypeOver.extensionSubstitution σ A)
        (C.pair τ (C.tySub A σ) t) =
      C.pair (C.compS σ τ) A
        (cast (congrArg (C.Tm Θ) (C.tySub_comp A σ τ).symm) t) := by
  apply TypeOver.substitution_ext
  · rw [← C.comp_assoc, TypeOver.wk_extensionSubstitution,
      C.comp_assoc, C.wk_pair, C.wk_pair]
  · have types : C.tySub (C.tySub A (C.wk A))
        (TypeOver.extensionSubstitution σ A) =
        C.tySub (C.tySub A σ) (C.wk (C.tySub A σ)) := by
      rw [← C.tySub_comp, TypeOver.wk_extensionSubstitution, C.tySub_comp]
    exact (TypeOver.tmSub_comp_heq (C.vz A) _ _).trans
      ((TypeOver.tmSub_heq types (TypeOver.vz_extensionSubstitution σ A) _).trans
        ((heq_of_eq (C.vz_pair _ _ _)).trans
          ((cast_heq _ _).trans
            ((cast_heq _ _).symm.trans
              ((cast_heq _ _).symm.trans (heq_of_eq (C.vz_pair _ _ _)).symm)))))

/-- The fibre comparison is built from comprehension and the source
substitution-composition law, rather than assumed as a representation. -/
def substitutionFibreEquiv {Γ Δ : C.Ctx} (A : C.Ty Γ) (σ : C.Sub Δ Γ)
    (point : (contextFace C Δ).Elements) :
    (family C (C.tySub A σ)).obj point ≃
      (reindexDisplayed (yoneda.map
        (show context C Δ ⟶ context C Γ from σ)) (family C A)).obj point :=
  ((termFibreEquiv C (C.tySub A σ) point.2).symm.trans
    (Equiv.cast (congrArg (C.Tm point.1.unop.val)
      (C.tySub_comp A σ point.2).symm))).trans
    (termFibreEquiv C A (C.compS σ point.2))

theorem substitutionFibreEquiv_val {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (σ : C.Sub Δ Γ) (point : (contextFace C Δ).Elements)
    (receipt : (family C (C.tySub A σ)).obj point) :
    (substitutionFibreEquiv C A σ point receipt).val =
      C.compS (TypeOver.extensionSubstitution σ A) receipt.val := by
  change (C.pair (C.compS σ point.2) A
    (cast _ (decodeTerm C (C.tySub A σ) point.2 receipt))) = _
  rw [← extension_encode]
  exact congrArg (C.compS (TypeOver.extensionSubstitution σ A))
    (congrArg Subtype.val (encode_decode C (C.tySub A σ) point.2 receipt))

/-- Interpretation preserves type substitution by a natural isomorphism
of whole displayed families, including their action on substitutions. -/
def substitutionIso {Γ Δ : C.Ctx} (A : C.Ty Γ) (σ : C.Sub Δ Γ) :
    family C (C.tySub A σ) ≅
      reindexDisplayed (yoneda.map
        (show context C Δ ⟶ context C Γ from σ)) (family C A) := by
  refine NatIso.ofComponents
    (fun point => (substitutionFibreEquiv C A σ point).toIso) ?_
  intro source target arrow
  apply ConcreteCategory.hom_ext
  intro receipt
  apply Subtype.ext
  change (substitutionFibreEquiv C A σ target
      ((family C (C.tySub A σ)).map arrow receipt)).val =
    C.compS (substitutionFibreEquiv C A σ source receipt).val arrow.val.unop
  rw [substitutionFibreEquiv_val, substitutionFibreEquiv_val]
  exact (C.comp_assoc _ _ _).symm

/-- The family comparison takes an interpreted substituted term to the
reindexed interpretation of the original term, at every contextual point. -/
theorem substitutionIso_term {Γ Δ : C.Ctx} {A : C.Ty Γ}
    (t : C.Tm Γ A) (σ : C.Sub Δ Γ)
    (point : (contextFace C Δ).Elements) :
    (substitutionIso C A σ).hom.app point
        ((interpretTerm C (C.tmSub t σ)).val point) =
      (reindexDisplayedSection
        (yoneda.map (show context C Δ ⟶ context C Γ from σ))
        (family C A) (interpretTerm C t)).val point := by
  apply Subtype.ext
  change (substitutionFibreEquiv C A σ point
      (encodeTerm C (C.tySub A σ) point.2
        (C.tmSub (C.tmSub t σ) point.2))).val =
    (C.pair (C.compS σ point.2) A (C.tmSub t (C.compS σ point.2)))
  refine (substitutionFibreEquiv_val C A σ point _).trans ?_
  change C.compS (TypeOver.extensionSubstitution σ A)
      (C.pair point.2 (C.tySub A σ) (C.tmSub (C.tmSub t σ) point.2)) = _
  rw [extension_encode, C.tmSub_comp]

#print axioms termFibreEquiv
#print axioms comprehensionIso
#print axioms comprehension_projection
#print axioms pair_compose
#print axioms encodeTerm_substitution
#print axioms termSectionEquiv
#print axioms substitutionIso
#print axioms substitutionIso_term

end Mettapedia.TypeTheory.CwfYoneda
