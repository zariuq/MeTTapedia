import Mettapedia.GSLT.Topos.PresheafImageComprehension
import Mettapedia.GSLT.Topos.PresheafPredicateHeyting
import Mettapedia.GSLT.Topos.PresheafPredicateUniversalQuantifier
import Mettapedia.GSLT.Topos.PresheafEventModalities

/-!
# Presheaf restriction transports the native logical structure

A base functor acts contravariantly on presheaves, predicates and dependent
types. The predicate action includes theory natural transformations, their
vertical composition and horizontal whiskering. Image and comprehension
commute with that action, including the adjunction unit and counit.

Restriction preserves conjunction, disjunction, existential image and
substitution exactly. Implication and universal quantification have canonical
one-way comparisons; `LiftsRestrictions` is a geometric sufficient condition
for equality. It lifts substitution arrows up to an isomorphism, and is
closed under identity and composition. It is not asserted necessary for an
arbitrary base category, nor identified with a runtime transition condition.

For an internal event graph, restriction of both states and events commutes
with diamond. The two universal modalities have the same qualified transport
as universal quantification. An arbitrary simulation between different event
graphs does not receive these equalities from this construction.

References: Williams and Stay, Native Type Theory (2021), Sections 3 and 5;
Mac Lane and Moerdijk, Sheaves in Geometry and Logic (1994), presheaf logic.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.LogicalTransport

open _root_.CategoryTheory _root_.CategoryTheory.Functor ImageComprehension

universe u
variable {B C D E : Type u} [Category.{u} B] [Category.{u} C] [Category.{u} D] [Category.{u} E]

abbrev restrictPresheaves (F : C ⥤ D) : (Dᵒᵖ ⥤ Type u) ⥤ (Cᵒᵖ ⥤ Type u) :=
  (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u)).obj F.op

def restrictPredicate (F : C ⥤ D) {P : Dᵒᵖ ⥤ Type u}
    (φ : Subfunctor P) : Subfunctor (restrictPresheaves F |>.obj P) where
  obj U := φ.obj (F.op.obj U)
  map i := φ.map (F.op.map i)

def restrictPredicates (F : C ⥤ D) :
    PresheafPredicateTotal D ⥤ PresheafPredicateTotal C where
  obj a := totalOfPredicate ((restrictPresheaves F).obj a.base)
    (restrictPredicate F (objectPredicate a))
  map f := homOfEntailment ((restrictPresheaves F).map f.base)
    (fun U _ member => hom_entailment f (F.op.obj U) member)
  map_id _ := hom_ext _ _ rfl
  map_comp _ _ := hom_ext _ _ rfl

abbrev restrictDependentTypes (F : C ⥤ D) :
    Arrow (Dᵒᵖ ⥤ Type u) ⥤ Arrow (Cᵒᵖ ⥤ Type u) :=
  (restrictPresheaves F).mapArrow

theorem restrictPredicate_top (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) :
    restrictPredicate F (⊤ : Subfunctor P) = ⊤ := rfl

theorem restrictPredicate_bot (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) :
    restrictPredicate F (⊥ : Subfunctor P) = ⊥ := rfl

theorem restrictPredicate_inf (F : C ⥤ D) {P : Dᵒᵖ ⥤ Type u}
    (φ ψ : Subfunctor P) :
    restrictPredicate F (φ ⊓ ψ) = restrictPredicate F φ ⊓ restrictPredicate F ψ := rfl

theorem restrictPredicate_sup (F : C ⥤ D) {P : Dᵒᵖ ⥤ Type u}
    (φ ψ : Subfunctor P) :
    restrictPredicate F (φ ⊔ ψ) = restrictPredicate F φ ⊔ restrictPredicate F ψ := rfl

theorem restrictPredicate_preimage (F : C ⥤ D) {P Q : Dᵒᵖ ⥤ Type u}
    (φ : Subfunctor Q) (f : P ⟶ Q) :
    restrictPredicate F (φ.preimage f) =
      (restrictPredicate F φ).preimage ((restrictPresheaves F).map f) := rfl

theorem restrictPredicate_image (F : C ⥤ D) {P Q : Dᵒᵖ ⥤ Type u}
    (φ : Subfunctor P) (f : P ⟶ Q) :
    restrictPredicate F (φ.image f) =
      (restrictPredicate F φ).image ((restrictPresheaves F).map f) := rfl

theorem restrictPredicate_range (F : C ⥤ D) {P Q : Dᵒᵖ ⥤ Type u}
    (f : P ⟶ Q) :
    restrictPredicate F (Subfunctor.range f) =
      Subfunctor.range ((restrictPresheaves F).map f) := rfl

theorem restrict_implication_le (F : C ⥤ D) {P : Dᵒᵖ ⥤ Type u}
    (φ ψ : Subfunctor P) :
    restrictPredicate F (φ ⇨ ψ) ≤ restrictPredicate F φ ⇨ restrictPredicate F ψ := by
  rw [← himpPointwise_eq_himp, ← himpPointwise_eq_himp]
  intro U x member V i antecedent
  exact member (F.op.obj V) (F.op.map i) antecedent

def imageComparison (F : C ⥤ D) :
    restrictDependentTypes F ⋙ imageFunctor ≅ imageFunctor ⋙ restrictPredicates F :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro p q f; rfl)

def comprehensionComparison (F : C ⥤ D) :
    restrictPredicates F ⋙ comprehensionFunctor ≅
      comprehensionFunctor ⋙ restrictDependentTypes F :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro a b f; rfl)

theorem homEquiv_restrict (F : C ⥤ D)
    {p : Arrow (Dᵒᵖ ⥤ Type u)} {a : PresheafPredicateTotal D}
    (f : imageObject p ⟶ a) :
    toComprehension (p := (restrictDependentTypes F).obj p)
      (a := (restrictPredicates F).obj a) ((restrictPredicates F).map f) =
      (restrictDependentTypes F).map (toComprehension f) := by
  apply Arrow.hom_ext
  · ext U x
    rfl
  · rfl

/-- A natural transformation of theories induces restriction in the opposite
 direction, including its action on predicates. -/
abbrev restrictPresheavesMap {F G : C ⥤ D} (α : F ⟶ G) :
    restrictPresheaves G ⟶ restrictPresheaves F :=
  (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u)).map (NatTrans.op α)

def restrictPredicatesMap {F G : C ⥤ D} (α : F ⟶ G) :
    restrictPredicates G ⟶ restrictPredicates F where
  app a := homOfEntailment ((restrictPresheavesMap α).app a.base)
    (fun U _ member => (objectPredicate a).map ((NatTrans.op α).app U) member)
  naturality := by
    intro a b f
    apply hom_ext
    ext U x
    exact (NatTrans.naturality_apply f.base ((NatTrans.op α).app U) x).symm

abbrev restrictDependentTypesMap {F G : C ⥤ D} (α : F ⟶ G) :
    restrictDependentTypes G ⟶ restrictDependentTypes F :=
  (Functor.mapArrowFunctor _ _).map (restrictPresheavesMap α)

theorem restrictPredicates_id : restrictPredicates (𝟭 C) = 𝟭 _ := rfl

theorem restrictPredicates_comp (F : C ⥤ D) (G : D ⥤ E) :
    restrictPredicates (F ⋙ G) = restrictPredicates G ⋙ restrictPredicates F := rfl

theorem restrictDependentTypes_id : restrictDependentTypes (𝟭 C) = 𝟭 _ := rfl

theorem restrictDependentTypes_comp (F : C ⥤ D) (G : D ⥤ E) :
    restrictDependentTypes (F ⋙ G) = restrictDependentTypes G ⋙ restrictDependentTypes F := rfl

theorem restrictPredicatesMap_id (F : C ⥤ D) :
    restrictPredicatesMap (𝟙 F) = 𝟙 (restrictPredicates F) := by
  apply NatTrans.ext
  funext a
  apply hom_ext
  ext U x
  exact a.base.map_id_apply (F.op.obj U) x

theorem restrictPredicatesMap_comp {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) :
    restrictPredicatesMap (α ≫ β) = restrictPredicatesMap β ≫ restrictPredicatesMap α := by
  apply NatTrans.ext
  funext a
  apply hom_ext
  ext U x
  exact a.base.map_comp_apply ((NatTrans.op β).app U) ((NatTrans.op α).app U) x

/-- The action on theory transformations is a functor, not merely a choice
of object maps. Its source is opposite because presheaves are contravariant. -/
def predicateTranslationFunctor : (C ⥤ D)ᵒᵖ ⥤
    (PresheafPredicateTotal D ⥤ PresheafPredicateTotal C) where
  obj F := restrictPredicates F.unop
  map α := restrictPredicatesMap α.unop
  map_id F := restrictPredicatesMap_id F.unop
  map_comp α β := restrictPredicatesMap_comp β.unop α.unop

/-- Horizontal coherence for the action on theory transformations. -/
theorem restrictPredicatesMap_whiskerLeft {F G : C ⥤ D}
    (H : B ⥤ C) (α : F ⟶ G) :
    restrictPredicatesMap (whiskerLeft H α) =
      whiskerRight (restrictPredicatesMap α) (restrictPredicates H) := by
  apply NatTrans.ext
  funext a
  exact hom_ext _ _ rfl

theorem restrictPredicatesMap_whiskerRight {F G : C ⥤ D}
    (α : F ⟶ G) (H : D ⥤ E) :
    restrictPredicatesMap (whiskerRight α H) =
      whiskerLeft (restrictPredicates H) (restrictPredicatesMap α) := by
  apply NatTrans.ext
  funext a
  exact hom_ext _ _ rfl

/-- The adjunction unit survives the same theory restriction. -/
theorem unit_restrict (F : C ⥤ D) (p : Arrow (Dᵒᵖ ⥤ Type u)) :
    (restrictDependentTypes F).map (adjunction.unit.app p) =
      adjunction.unit.app ((restrictDependentTypes F).obj p) := by
  apply Arrow.hom_ext
  · ext U x
    rfl
  · rfl

/-- The adjunction counit survives the same theory restriction. -/
theorem counit_restrict (F : C ⥤ D) (a : PresheafPredicateTotal D) :
    (restrictPredicates F).map (adjunction.counit.app a) =
      adjunction.counit.app ((restrictPredicates F).obj a) := hom_ext _ _ rfl

theorem image_naturality (F : C ⥤ D) :
    restrictDependentTypes F ⋙ imageFunctor = imageFunctor ⋙ restrictPredicates F := rfl

theorem comprehension_naturality (F : C ⥤ D) :
    restrictPredicates F ⋙ comprehensionFunctor =
      comprehensionFunctor ⋙ restrictDependentTypes F := rfl

/-- Image formation is compatible with transformations between theories. -/
theorem image_transformation {F G : C ⥤ D} (α : F ⟶ G) :
    whiskerRight (restrictDependentTypesMap α) imageFunctor =
      whiskerLeft imageFunctor (restrictPredicatesMap α) := by
  apply NatTrans.ext
  funext p
  exact hom_ext _ _ rfl

theorem comprehension_transformation {F G : C ⥤ D} (α : F ⟶ G) :
    whiskerRight (restrictPredicatesMap α) comprehensionFunctor =
      whiskerLeft comprehensionFunctor (restrictDependentTypesMap α) := by
  apply NatTrans.ext
  funext a
  apply Arrow.hom_ext
  · ext U x
    rfl
  · rfl

theorem restrict_forall_le (F : C ⥤ D) {P Q : Dᵒᵖ ⥤ Type u}
    (f : P ⟶ Q) (φ : Subfunctor P) :
    restrictPredicate F (forallAlong f φ) ≤
      forallAlong ((restrictPresheaves F).map f) (restrictPredicate F φ) := by
  intro U x member V i p himage
  exact member (F.op.obj V) (F.op.map i) p himage

/-- Every restriction of an image context lifts up to an isomorphism of its
endpoint. This is a condition on substitution contexts, not on runtime steps. -/
def LiftsRestrictions (F : C ⥤ D) : Prop :=
  ∀ (U : Cᵒᵖ) (V : Dᵒᵖ) (i : F.op.obj U ⟶ V),
    ∃ (W : Cᵒᵖ) (j : U ⟶ W) (e : F.op.obj W ≅ V), F.op.map j ≫ e.hom = i

theorem liftsRestrictions_id : LiftsRestrictions (𝟭 C) := by
  intro U V i
  exact ⟨V, i, Iso.refl V, Category.comp_id i⟩

theorem liftsRestrictions_comp {F : C ⥤ D} {G : D ⥤ E}
    (hF : LiftsRestrictions F) (hG : LiftsRestrictions G) :
    LiftsRestrictions (F ⋙ G) := by
  intro U V i
  obtain ⟨W, j, e, rfl⟩ := hG (F.op.obj U) V i
  obtain ⟨X, k, d, rfl⟩ := hF U W j
  refine ⟨X, k, G.op.mapIso d ≪≫ e, ?_⟩
  change G.op.map (F.op.map k) ≫ G.op.map d.hom ≫ e.hom =
    G.op.map (F.op.map k ≫ d.hom) ≫ e.hom
  rw [Functor.map_comp, Category.assoc]

theorem restrict_implication_eq {F : C ⥤ D} (lifting : LiftsRestrictions F)
    {P : Dᵒᵖ ⥤ Type u} (φ ψ : Subfunctor P) :
    restrictPredicate F (φ ⇨ ψ) = restrictPredicate F φ ⇨ restrictPredicate F ψ := by
  apply le_antisymm (restrict_implication_le F φ ψ)
  rw [← himpPointwise_eq_himp, ← himpPointwise_eq_himp]
  intro U x member V i antecedent
  obtain ⟨W, j, e, rfl⟩ := lifting U V i
  have before : P.map (F.op.map j) x ∈ φ.obj (F.op.obj W) := by
    have h := φ.map e.inv antecedent
    change P.map e.inv (P.map (F.op.map j ≫ e.hom) x) ∈ φ.obj (F.op.obj W) at h
    simpa only [← Functor.map_comp_apply, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] using h
  have after := ψ.map e.hom (member W j before)
  change P.map e.hom (P.map (F.op.map j) x) ∈ ψ.obj V at after
  simpa only [Functor.map_comp_apply] using after

theorem restrict_forall_eq {F : C ⥤ D} (lifting : LiftsRestrictions F)
    {P Q : Dᵒᵖ ⥤ Type u} (f : P ⟶ Q) (φ : Subfunctor P) :
    restrictPredicate F (forallAlong f φ) =
      forallAlong ((restrictPresheaves F).map f) (restrictPredicate F φ) := by
  apply le_antisymm (restrict_forall_le F f φ)
  intro U x member V i p himage
  obtain ⟨W, j, e, rfl⟩ := lifting U V i
  have before : f.app (F.op.obj W) (P.map e.inv p) = Q.map (F.op.map j) x := by
    rw [NatTrans.naturality_apply, himage]
    simp only [← Functor.map_comp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have after := φ.map e.hom (member W j (P.map e.inv p) before)
  change P.map e.hom (P.map e.inv p) ∈ φ.obj V at after
  simpa only [← Functor.map_comp_apply, Iso.inv_hom_id, Functor.map_id_apply] using after

/-- Theory restriction acts on both the states and the retained events of
an internal graph. This is stronger than an arbitrary forward simulation. -/
def restrictEventGraph (F : C ⥤ D) (G : ConstructivePresheaf.EventGraph Dᵒᵖ) :
    ConstructivePresheaf.EventGraph Cᵒᵖ where
  vertex := (restrictPresheaves F).obj G.vertex
  edge := (restrictPresheaves F).obj G.edge
  source := (restrictPresheaves F).map G.source
  target := (restrictPresheaves F).map G.target

/-- Existential event observation commutes exactly with restriction of the
whole event graph. No converse simulation theorem is assumed. -/
theorem restrict_diamond (F : C ⥤ D) (G : ConstructivePresheaf.EventGraph Dᵒᵖ)
    (φ : Subfunctor G.vertex) :
    restrictPredicate F (PresheafEventModalities.diamond G φ) =
      PresheafEventModalities.diamond (restrictEventGraph F G) (restrictPredicate F φ) := rfl

theorem restrict_box_le (F : C ⥤ D) (G : ConstructivePresheaf.EventGraph Dᵒᵖ)
    (φ : Subfunctor G.vertex) :
    restrictPredicate F (PresheafEventModalities.box G φ) ≤
      PresheafEventModalities.box (restrictEventGraph F G) (restrictPredicate F φ) :=
  restrict_forall_le F G.target (φ.preimage G.source)

theorem restrict_forwardBox_le (F : C ⥤ D) (G : ConstructivePresheaf.EventGraph Dᵒᵖ)
    (φ : Subfunctor G.vertex) :
    restrictPredicate F (PresheafEventModalities.forwardBox G φ) ≤
      PresheafEventModalities.forwardBox (restrictEventGraph F G) (restrictPredicate F φ) :=
  restrict_forall_le F G.source (φ.preimage G.target)

theorem restrict_box_eq {F : C ⥤ D} (lifting : LiftsRestrictions F)
    (G : ConstructivePresheaf.EventGraph Dᵒᵖ) (φ : Subfunctor G.vertex) :
    restrictPredicate F (PresheafEventModalities.box G φ) =
      PresheafEventModalities.box (restrictEventGraph F G) (restrictPredicate F φ) :=
  restrict_forall_eq lifting G.target (φ.preimage G.source)

theorem restrict_forwardBox_eq {F : C ⥤ D} (lifting : LiftsRestrictions F)
    (G : ConstructivePresheaf.EventGraph Dᵒᵖ) (φ : Subfunctor G.vertex) :
    restrictPredicate F (PresheafEventModalities.forwardBox G φ) =
      PresheafEventModalities.forwardBox (restrictEventGraph F G) (restrictPredicate F φ) :=
  restrict_forall_eq lifting G.source (φ.preimage G.target)

end Mettapedia.GSLT.Topos.LogicalTransport
