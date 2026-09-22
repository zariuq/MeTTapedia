import Mettapedia.TypeTheory.CwfYoneda
import Mettapedia.GSLT.Core.ContextualTypeReindexingCoherence

/-!
# Coherence of represented dependent types

The representation of source types by their display-map fibres is functorial
on display maps. Its substitution comparisons respect type morphisms,
identity substitutions, and composition of substitutions. All comparisons
are tied to the source CwF's selected comprehension lifts.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CwfYoneda

open CategoryTheory CategoryTheory.Functor Opposite
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension

universe u v w w'

variable (C : Cwf.{u, v, w, w'})

/-- Interpret a source display map by postcomposition on the actual arrows
retained in the represented fibres. -/
def familyMap {Γ : C.Ctx} {A B : TypeOver C Γ} (arrow : A ⟶ B) :
    family C A.val ⟶ family C B.val where
  app point := TypeCat.ofHom fun receipt =>
    ⟨C.compS arrow.substitution receipt.val, by
      change C.compS (C.wk B.val) (C.compS arrow.substitution receipt.val) = point.2
      rw [← C.comp_assoc, arrow.over]
      exact receipt.property⟩
  naturality := by
    intro source target substitution
    apply ConcreteCategory.hom_ext
    intro receipt
    apply Subtype.ext
    exact (C.comp_assoc arrow.substitution receipt.val substitution.val.unop).symm

/-- The type interpretation acts on the existing category of source display
maps, not only on its objects. -/
def familyFunctor (Γ : C.Ctx) :
    TypeOver C Γ ⥤ DisplayedFamily (contextFace C Γ) where
  obj A := family C A.val
  map := familyMap C
  map_id A := by
    ext point receipt
    apply Subtype.ext
    exact C.id_comp receipt.val
  map_comp first second := by
    ext point receipt
    apply Subtype.ext
    exact C.comp_assoc second.substitution first.substitution receipt.val

/-- Recover a source display map by evaluating a natural family map at the
generic source variable. -/
def recoverFamilyMap {Γ : C.Ctx} {A B : TypeOver C Γ}
    (map : family C A.val ⟶ family C B.val) : A ⟶ B where
  substitution := (map.app ⟨op (context C (C.ext Γ A.val)), C.wk A.val⟩
    ⟨C.idS (C.ext Γ A.val), C.comp_id (C.wk A.val)⟩).val
  over := (map.app ⟨op (context C (C.ext Γ A.val)), C.wk A.val⟩
    ⟨C.idS (C.ext Γ A.val), C.comp_id (C.wk A.val)⟩).property

theorem recoverFamilyMap_familyMap {Γ : C.Ctx} {A B : TypeOver C Γ}
    (arrow : A ⟶ B) : recoverFamilyMap C (familyMap C arrow) = arrow :=
  TypeOver.Hom.ext (C.comp_id arrow.substitution)

/-- Naturality determines a family map from its action at the generic
variable. This gives the converse to interpretation of display maps. -/
theorem familyMap_recoverFamilyMap {Γ : C.Ctx} {A B : TypeOver C Γ}
    (map : family C A.val ⟶ family C B.val) :
    familyMap C (recoverFamilyMap C map) = map := by
  ext point receipt
  let generic : (contextFace C Γ).Elements :=
    ⟨op (context C (C.ext Γ A.val)), C.wk A.val⟩
  let variableReceipt : (family C A.val).obj generic :=
    ⟨C.idS (C.ext Γ A.val), C.comp_id (C.wk A.val)⟩
  let arrow : generic ⟶ point :=
    ⟨(show point.1.unop ⟶ context C (C.ext Γ A.val) from receipt.val).op,
      receipt.property⟩
  have transported : (family C A.val).map arrow variableReceipt = receipt :=
    Subtype.ext (C.id_comp receipt.val)
  have natural := map.naturality_apply arrow variableReceipt
  rw [transported] at natural
  exact natural.symm

/-- All natural maps between represented source types come from unique
source display maps. This concerns the represented image, not all semantic
types or an initiality property of the source CwF. -/
def familyFullyFaithful (Γ : C.Ctx) : (familyFunctor C Γ).FullyFaithful where
  preimage := recoverFamilyMap C
  map_preimage := familyMap_recoverFamilyMap C
  preimage_map := recoverFamilyMap_familyMap C

/-- Type morphisms commute with the comparison between represented source
substitution and semantic pullback. -/
theorem substitutionIso_naturality {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    {A B : TypeOver C Γ} (arrow : A ⟶ B) :
    familyMap C (TypeOver.reindexArrow σ arrow) ≫
        (substitutionIso C B.val σ).hom =
      (substitutionIso C A.val σ).hom ≫
        whiskerLeft (yoneda.map
          (show context C Δ ⟶ context C Γ from σ)).mapElements
          (familyMap C arrow) := by
  ext point receipt
  apply Subtype.ext
  change (substitutionFibreEquiv C B.val σ point
      ((familyMap C (TypeOver.reindexArrow σ arrow)).app point receipt)).val =
    C.compS arrow.substitution (substitutionFibreEquiv C A.val σ point receipt).val
  rw [substitutionFibreEquiv_val, substitutionFibreEquiv_val]
  change C.compS (TypeOver.extensionSubstitution σ B.val)
      (C.compS (TypeOver.reindexArrow σ arrow).substitution receipt.val) = _
  rw [← C.comp_assoc, TypeOver.extensionSubstitution_naturality, C.comp_assoc]
  rfl

/-- The substitution comparisons form a natural isomorphism of functors on
the category of source types, in addition to their contextual naturality. -/
def substitutionNaturalIso {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) :
    TypeOver.reindexFunctor σ ⋙ familyFunctor C Δ ≅
      familyFunctor C Γ ⋙
        (whiskeringLeft _ _ _).obj
          (yoneda.map (show context C Δ ⟶ context C Γ from σ)).mapElements :=
  NatIso.ofComponents (fun A => substitutionIso C A.val σ)
    (fun arrow => substitutionIso_naturality C σ arrow)

/-- Changing only the equality presentation of a base map does not change
the source arrow retained in a represented fibre. -/
theorem reindex_eqToHom_val {Γ Δ : C.Ctx} (A : C.Ty Γ)
    {left right : contextFace C Δ ⟶ contextFace C Γ} (equal : left = right)
    (point : (contextFace C Δ).Elements)
    (receipt : (reindexDisplayed left (family C A)).obj point) :
    ((eqToHom (congrArg (fun change => reindexDisplayed change (family C A)) equal)).app
      point receipt).val = receipt.val := by
  cases equal
  rfl

/-- The substitution comparison at the identity is exactly the represented
source unit comparison, after the canonical semantic unit identification. -/
theorem substitutionIso_id {Γ : C.Ctx} (A : C.Ty Γ) :
    (substitutionIso C A (C.idS Γ)).hom ≫
        eqToHom (congrArg (fun change => reindexDisplayed change (family C A))
          (yoneda.map_id (context C Γ))) =
      familyMap C (TypeOver.identityObjectIso (⟨A⟩ : TypeOver C Γ)).hom := by
  ext point receipt
  apply Subtype.ext
  refine (reindex_eqToHom_val C A (yoneda.map_id (context C Γ)) point _).trans ?_
  change (substitutionFibreEquiv C A (C.idS Γ) point receipt).val =
    C.compS (TypeOver.identityObjectIso (⟨A⟩ : TypeOver C Γ)).hom.substitution receipt.val
  rw [substitutionFibreEquiv_val, TypeOver.identityObjectIso_hom_substitution]

/-- Two successive substitution comparisons equal the comparison for their
composite, with the source and semantic composition identifications made
explicit. This is an equality of natural transformations of whole families. -/
theorem substitutionIso_comp {Γ Δ Θ : C.Ctx} (A : C.Ty Γ)
    (σ : C.Sub Δ Γ) (τ : C.Sub Θ Δ) :
    familyMap C (TypeOver.compositionObjectIso σ τ (⟨A⟩ : TypeOver C Γ)).hom ≫
        (substitutionIso C (C.tySub A σ) τ).hom ≫
        whiskerLeft (yoneda.map
          (show context C Θ ⟶ context C Δ from τ)).mapElements
          (substitutionIso C A σ).hom =
      (substitutionIso C A (C.compS σ τ)).hom ≫
        eqToHom (congrArg (fun change => reindexDisplayed change (family C A))
          (yoneda.map_comp
            (show context C Θ ⟶ context C Δ from τ)
            (show context C Δ ⟶ context C Γ from σ))) := by
  ext point receipt
  apply Subtype.ext
  symm
  refine (reindex_eqToHom_val C A (yoneda.map_comp
    (show context C Θ ⟶ context C Δ from τ)
    (show context C Δ ⟶ context C Γ from σ)) point _).trans ?_
  change (substitutionFibreEquiv C A (C.compS σ τ) point receipt).val =
    (substitutionFibreEquiv C A σ
      ((yoneda.map (show context C Θ ⟶ context C Δ from τ)).mapElements.obj point)
      (substitutionFibreEquiv C (C.tySub A σ) τ point
        ((familyMap C (TypeOver.compositionObjectIso σ τ
          (⟨A⟩ : TypeOver C Γ)).hom).app point receipt))).val
  rw [substitutionFibreEquiv_val]
  refine Eq.trans ?_ (substitutionFibreEquiv_val C A σ
    ((yoneda.map (show context C Θ ⟶ context C Δ from τ)).mapElements.obj point) _).symm
  rw [substitutionFibreEquiv_val]
  change C.compS (TypeOver.extensionSubstitution (C.compS σ τ) A) receipt.val =
    C.compS (TypeOver.extensionSubstitution σ A)
      (C.compS (TypeOver.extensionSubstitution τ (C.tySub A σ))
        (C.compS (TypeOver.compositionObjectIso σ τ
          (⟨A⟩ : TypeOver C Γ)).hom.substitution receipt.val))
  rw [← C.comp_assoc, ← C.comp_assoc]
  exact congrArg (fun lift => C.compS lift receipt.val)
    (TypeOver.compositionObjectIso_hom_lift σ τ (⟨A⟩ : TypeOver C Γ)).symm

/-- Term substitution is preserved as an equality of natural sections,
using the same family comparison that satisfies the unit/composition laws. -/
theorem substitutionIso_section {Γ Δ : C.Ctx} {A : C.Ty Γ}
    (t : C.Tm Γ A) (σ : C.Sub Δ Γ) :
    (sectionsFunctor _).map (substitutionIso C A σ).hom
        (interpretTerm C (C.tmSub t σ)) =
      reindexDisplayedSection
        (yoneda.map (show context C Δ ⟶ context C Γ from σ))
        (family C A) (interpretTerm C t) := by
  apply (Functor.sections_ext_iff).2
  exact substitutionIso_term C t σ

/-- Reindex a represented section and return it to the represented source
fibre using the canonical substitution comparison. This acts on arbitrary
semantic sections, not only on a selected image of syntax. -/
def substituteSection {Γ Δ : C.Ctx} {A : C.Ty Γ} (σ : C.Sub Δ Γ)
    (sectionValue : (family C A).sections) :
    (family C (C.tySub A σ)).sections :=
  (sectionsFunctor _).map (substitutionIso C A σ).inv
    (reindexDisplayedSection
      (yoneda.map (show context C Δ ⟶ context C Γ from σ))
      (family C A) sectionValue)

theorem substituteSection_interpret {Γ Δ : C.Ctx} {A : C.Ty Γ}
    (σ : C.Sub Δ Γ) (term : C.Tm Γ A) :
    substituteSection C σ (interpretTerm C term) = interpretTerm C (C.tmSub term σ) := by
  unfold substituteSection
  rw [← substitutionIso_section C term σ]
  exact ConcreteCategory.congr_hom
    ((sectionsFunctor _).mapIso (substitutionIso C A σ)).hom_inv_id _

/-- Recovery of a source term is natural for all represented sections.
Together with the inverse laws, this upgrades pointwise recovery to a
substitution-compatible correspondence. -/
theorem recoverTerm_substituteSection {Γ Δ : C.Ctx} {A : C.Ty Γ}
    (σ : C.Sub Δ Γ) (sectionValue : (family C A).sections) :
    recoverTerm C (substituteSection C σ sectionValue) =
      C.tmSub (recoverTerm C sectionValue) σ := by
  conv_lhs => rw [← interpret_recover C sectionValue]
  rw [substituteSection_interpret, recover_interpret]

theorem interpretTerm_cast {Γ : C.Ctx} {A B : C.Ty Γ} (equal : A = B)
    (term : C.Tm Γ A) :
    interpretTerm C (cast (congrArg (C.Tm Γ) equal) term) =
      cast (congrArg (fun type => (family C type).sections) equal) (interpretTerm C term) := by
  cases equal
  rfl

/-- The induced action on all represented sections has the source's unit
law, with its dependent type-index transport explicit. -/
theorem substituteSection_id {Γ : C.Ctx} {A : C.Ty Γ}
    (sectionValue : (family C A).sections) :
    substituteSection C (C.idS Γ) sectionValue =
      cast (congrArg (fun type => (family C type).sections) (C.tySub_id A).symm)
        sectionValue := by
  conv_lhs => rw [← interpret_recover C sectionValue]
  rw [substituteSection_interpret, C.tmSub_id,
    interpretTerm_cast C (C.tySub_id A).symm, interpret_recover]

/-- Substituting represented sections in stages agrees with the composite
substitution on the original section, including its dependent type index. -/
theorem substituteSection_comp {Γ Δ Θ : C.Ctx} {A : C.Ty Γ}
    (σ : C.Sub Δ Γ) (τ : C.Sub Θ Δ) (sectionValue : (family C A).sections) :
    substituteSection C (C.compS σ τ) sectionValue =
      cast (congrArg (fun type => (family C type).sections) (C.tySub_comp A σ τ).symm)
        (substituteSection C τ (substituteSection C σ sectionValue)) := by
  rw [← interpret_recover C sectionValue]
  rw [substituteSection_interpret, substituteSection_interpret,
    substituteSection_interpret, C.tmSub_comp,
    interpretTerm_cast C (C.tySub_comp A σ τ).symm]

/-- Pairing a translated substitution with a translated dependent term
recovers the Yoneda image of the actual source pairing. The term is retained
through the selected substitution and comprehension comparisons. -/
theorem pairing_preserved {Γ Δ : C.Ctx} (A : C.Ty Γ) (σ : C.Sub Δ Γ)
    (t : C.Tm Δ (C.tySub A σ)) :
    DisplayedPresheafCwf.presheafPair
        (yoneda.map (show context C Δ ⟶ context C Γ from σ))
        (family C A)
        ((sectionsFunctor _).map (substitutionIso C A σ).hom (interpretTerm C t)) ≫
        (comprehensionIso C A).hom =
      yoneda.map (show context C Δ ⟶ context C (C.ext Γ A) from C.pair σ A t) := by
  ext point substitution
  change (substitutionFibreEquiv C A σ ⟨point, substitution⟩
      (encodeTerm C (C.tySub A σ) substitution (C.tmSub t substitution))).val =
    C.compS (C.pair σ A t) substitution
  refine (substitutionFibreEquiv_val C A σ ⟨point, substitution⟩ _).trans ?_
  change C.compS (TypeOver.extensionSubstitution σ A)
      (C.pair substitution (C.tySub A σ) (C.tmSub t substitution)) = _
  rw [extension_encode, pair_compose]

/-- The source's chosen empty context represents the semantic terminal
context. The inverse sends the singleton to the source's unique empty
substitution, with naturality following from its proved uniqueness. -/
def terminalIso (D : CwfWithTerminal.{u, v, w, w'}) :
    contextFace D.toCwf D.empty ≅ DisplayedPresheafCwf.terminalFace D.toCwf.base.Context where
  hom := {
    app _ := TypeCat.ofHom fun _ => PUnit.unit
    naturality := by intros; rfl }
  inv := {
    app point := TypeCat.ofHom fun _ => D.toEmpty point.unop.val
    naturality := by
      intro source target substitution
      apply ConcreteCategory.hom_ext
      intro value
      exact (D.toEmpty_unique target.unop.val
        (D.toCwf.compS (D.toEmpty source.unop.val) substitution.unop)).symm }
  hom_inv_id := by
    ext point substitution
    exact (D.toEmpty_unique point.unop.val substitution).symm
  inv_hom_id := by
    ext point value
    cases value
    rfl

#print axioms familyFunctor
#print axioms familyFullyFaithful
#print axioms substitutionNaturalIso
#print axioms substitutionIso_naturality
#print axioms substitutionIso_id
#print axioms substitutionIso_comp
#print axioms substitutionIso_section
#print axioms substituteSection_interpret
#print axioms recoverTerm_substituteSection
#print axioms substituteSection_id
#print axioms substituteSection_comp
#print axioms pairing_preserved
#print axioms terminalIso

end Mettapedia.TypeTheory.CwfYoneda
