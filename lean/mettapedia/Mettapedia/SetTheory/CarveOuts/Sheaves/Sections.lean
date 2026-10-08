import Mettapedia.SetTheory.CarveOuts.Sheaves.Collection

/-!
# Sections of sheaves on a space: gluing, products, pullbacks and subobjects

Working tools for sheaves of sets on a topological space, stated with the covers of
`Sites.ProductSite` (`Covered`):

* **Gluing.** Sections of a sheaf given on the parts of a cover, agreeing below any two parts, glue
  to a section (`sheaf_glue`). Conversely, a presheaf whose sections are determined on covers and
  glue along covers is a sheaf (`isSheaf_of_covered`). On an open set with no points a sheaf has at
  most one section (`sheaf_sections_subsingleton_of_empty`).
* **Finite limits are computed on sections.** The terminal sheaf has one section on every open
  set; a section of a product is a pair of sections (`prod_sections_ext`,
  `prod_sections_exists`); a square of sheaves is a pullback exactly when it is a pullback of sets
  on every open set (`isPullback_sections`, `isPullback_of_sections`).
* **Monomorphisms and subobjects.** A map of sheaves is mono exactly when it is injective on
  sections (`injective_of_mono`, `mono_of_injective`). A subobject is determined by the sections
  that factor through it (`subobject_le_of_sections`, `subobject_eq_of_sections`), which are
  computed for `Subobject.mk` and for pullbacks of subobjects (`mk_arrow_sections`,
  `pullback_arrow_sections`).

Mathlib's limits in the category of sheaves are chosen limits; the lemmas here read them through
the evaluation functors, which preserve and jointly reflect them.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.Sheaves

open CategoryTheory Limits TopologicalSpace Opposite
open Mettapedia.SetTheory.CarveOuts.Sites

universe u

variable {X : Type u} [TopologicalSpace X]

/-! ## Gluing -/

section Gluing

/-- **Gluing.** Sections of a sheaf on the parts of a cover that agree below any two parts are the
restrictions of one section. -/
theorem sheaf_glue (F : SheafOn X) {U : Opens X} {P : (V : Opens X) → V ≤ U → Prop}
    (hP : Covered U P) (s : ∀ (V : Opens X) (h : V ≤ U), P V h → F.obj.obj (op V))
    (compat : ∀ (V V' : Opens X) (h : V ≤ U) (h' : V' ≤ U) (p : P V h) (p' : P V' h')
      (Z : Opens X) (hZ : Z ≤ V) (hZ' : Z ≤ V'),
        res F.obj hZ (s V h p) = res F.obj hZ' (s V' h' p')) :
    ∃ t : F.obj.obj (op U), ∀ (V : Opens X) (h : V ≤ U) (p : P V h), res F.obj h t = s V h p := by
  have hsheaf := (isSheaf_iff_isSheaf_of_type _ F.obj).mp F.property
  let S : Sieve U :=
    { arrows := fun Y _ => ∃ (V : Opens X) (h : V ≤ U), P V h ∧ Y ≤ V
      downward_closed := by
        rintro Y Z f ⟨V, h, p, hY⟩ g
        exact ⟨V, h, p, le_trans (leOfHom g) hY⟩ }
  have hS : S ∈ Opens.grothendieckTopology X U :=
    (covered_iff_mem S).mp (covered_mono (fun V h p => ⟨V, h, p, le_rfl⟩) hP)
  let x : Presieve.FamilyOfElements F.obj S.arrows := fun Y _ hf =>
    res F.obj hf.choose_spec.snd.2 (s _ hf.choose_spec.fst hf.choose_spec.snd.1)
  have hx : x.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ _
    change res F.obj (leOfHom g₁) (res F.obj _ _) = res F.obj (leOfHom g₂) (res F.obj _ _)
    rw [res_res, res_res]
    exact compat _ _ _ _ _ _ (unop (op Z)) _ _
  obtain ⟨t, ht, -⟩ := hsheaf S hS x hx
  refine ⟨t, fun V h p => (ht (homOfLE h) ⟨V, h, p, le_rfl⟩).trans ?_⟩
  change res F.obj _ (s _ _ _) = s V h p
  rw [compat _ V _ h _ p V _ le_rfl, res_self]

/-- **A presheaf is a sheaf when sections are determined on covers and glue along covers.** The
gluing is asked only for down-closed covers, with sections that restrict to each other. -/
theorem isSheaf_of_covered (F : (Opens X)ᵒᵖ ⥤ Type u)
    (sep : ∀ (U : Opens X) (s t : F.obj (op U)),
      Covered U (fun _ h => res F h s = res F h t) → s = t)
    (glue : ∀ (U : Opens X) (P : (V : Opens X) → V ≤ U → Prop),
      (∀ (V W : Opens X) (h : V ≤ U) (hW : W ≤ V), P V h → P W (le_trans hW h)) → Covered U P →
      ∀ s : (∀ (V : Opens X) (h : V ≤ U), P V h → F.obj (op V)),
      (∀ (V W : Opens X) (h : V ≤ U) (hW : W ≤ V) (p : P V h) (p' : P W (le_trans hW h)),
        res F hW (s V h p) = s W (le_trans hW h) p') →
      ∃ t : F.obj (op U), ∀ (V : Opens X) (h : V ≤ U) (p : P V h), res F h t = s V h p) :
    Presieve.IsSheaf (Opens.grothendieckTopology X) F := by
  intro U S hS x hx
  have hcov : Covered U fun V h => S (homOfLE h) := (covered_iff_mem S).mpr hS
  obtain ⟨t, ht⟩ := glue U (fun V h => S (homOfLE h))
    (fun _ W h hW p => S.downward_closed p (homOfLE hW)) hcov
    (fun V h p => x (homOfLE h) p)
    (fun V W h hW p p' => by
      have key := hx (homOfLE hW) (𝟙 W) p p' rfl
      rw [op_id, F.map_id] at key
      exact key)
  refine ⟨t, fun Y f hf => ht Y (leOfHom f) hf, fun t' ht' => sep U t' t ?_⟩
  refine covered_mono (fun V h hV => ?_) hcov
  exact (ht' (homOfLE h) hV).trans (ht V h hV).symm

/-- On an open set with no points, a sheaf has at most one section. -/
theorem sheaf_sections_subsingleton_of_empty (F : SheafOn X) {W : Opens X}
    (hW : ∀ x, x ∉ W) : Subsingleton (F.obj.obj (op W)) :=
  ⟨fun _ _ => sheaf_eq_of_covered F fun x hx => (hW x hx).elim⟩

end Gluing

/-! ## Finite limits on sections -/

section Limits

/-- The terminal sheaf has at most one section on every open set. -/
theorem terminal_sections_subsingleton (U : Opens X) :
    Subsingleton ((⊤_ SheafOn X).obj.obj (op U)) :=
  @Unique.instSubsingleton _ (Types.isTerminalEquivUnique _ (IsTerminal.isTerminalObj
    (sheafToPresheaf (Opens.grothendieckTopology X) (Type u) ⋙ (evaluation _ _).obj (op U)) _
      terminalIsTerminal))

/-- The terminal sheaf has a section on every open set. -/
theorem terminal_sections_nonempty (U : Opens X) :
    Nonempty ((⊤_ SheafOn X).obj.obj (op U)) :=
  ⟨(Types.isTerminalEquivUnique _ (IsTerminal.isTerminalObj
    (sheafToPresheaf (Opens.grothendieckTopology X) (Type u) ⋙ (evaluation _ _).obj (op U)) _
      terminalIsTerminal)).default⟩

/-- A pullback square of sheaves is a pullback square of sets on every open set. -/
theorem isPullback_sections {P A B C : SheafOn X} {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ C}
    {g : B ⟶ C} (sq : IsPullback fst snd f g) (U : Opens X) :
    IsPullback (fst.hom.app (op U)) (snd.hom.app (op U)) (f.hom.app (op U)) (g.hom.app (op U)) :=
  Functor.map_isPullback ((evaluation _ _).obj (op U))
    (Functor.map_isPullback (sheafToPresheaf (Opens.grothendieckTopology X) (Type u)) sq)

/-- A commuting square of sheaves that is a pullback of sets on every open set is a pullback. -/
theorem isPullback_of_sections {P A B C : SheafOn X} {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ C}
    {g : B ⟶ C} (w : fst ≫ f = snd ≫ g)
    (h : ∀ U : Opens X,
      IsPullback (fst.hom.app (op U)) (snd.hom.app (op U)) (f.hom.app (op U)) (g.hom.app (op U))) :
    IsPullback fst snd f g :=
  IsPullback.of_map (sheafToPresheaf (Opens.grothendieckTopology X) (Type u)) w
    (IsPullback.of_forall_isPullback_app fun U => h (unop U))

/-- A section of a product is a pair of sections: two with the same components are equal. -/
theorem prod_sections_ext (A B : SheafOn X) {U : Opens X} {s t : (A ⨯ B).obj.obj (op U)}
    (h₁ : (prod.fst : A ⨯ B ⟶ A).hom.app (op U) s = (prod.fst : A ⨯ B ⟶ A).hom.app (op U) t)
    (h₂ : (prod.snd : A ⨯ B ⟶ B).hom.app (op U) s = (prod.snd : A ⨯ B ⟶ B).hom.app (op U) t) :
    s = t :=
  Types.ext_of_isPullback (isPullback_sections (IsPullback.of_hasBinaryProduct' A B) U) h₁ h₂

/-- Every pair of sections is a section of the product. -/
theorem prod_sections_exists (A B : SheafOn X) {U : Opens X} (a : A.obj.obj (op U))
    (b : B.obj.obj (op U)) :
    ∃ s : (A ⨯ B).obj.obj (op U), (prod.fst : A ⨯ B ⟶ A).hom.app (op U) s = a ∧
      (prod.snd : A ⨯ B ⟶ B).hom.app (op U) s = b :=
  haveI := terminal_sections_subsingleton (X := X) U
  Types.exists_of_isPullback (isPullback_sections (IsPullback.of_hasBinaryProduct' A B) U) a b
    (Subsingleton.elim _ _)

end Limits

/-! ## Monomorphisms and subobjects -/

section Subobjects

/-- A mono of sheaves is injective on sections. -/
theorem injective_of_mono {A B : SheafOn X} (m : A ⟶ B) [Mono m] (U : Opens X) :
    Function.Injective (m.hom.app (op U)) := by
  have : Mono m.hom := (sheafToPresheaf (Opens.grothendieckTopology X) (Type u)).map_mono m
  exact (mono_iff_injective (m.hom.app (op U))).mp ((NatTrans.mono_iff_mono_app m.hom).mp this _)

/-- A map of sheaves injective on sections is mono. -/
theorem mono_of_injective {A B : SheafOn X} (m : A ⟶ B)
    (h : ∀ U : Opens X, Function.Injective (m.hom.app (op U))) : Mono m := by
  have : ∀ U, Mono (m.hom.app U) := fun U => (mono_iff_injective (m.hom.app U)).mpr (h (unop U))
  have : Mono m.hom := NatTrans.mono_of_mono_app m.hom
  exact (sheafToPresheaf (Opens.grothendieckTopology X) (Type u)).mono_of_mono_map this

/-- A subobject is below another when every section factoring through the first factors through
the second. -/
theorem subobject_le_of_sections {F : SheafOn X} {R₁ R₂ : Subobject F}
    (h : ∀ (U : Opens X) (r : (R₁ : SheafOn X).obj.obj (op U)),
      ∃ r' : (R₂ : SheafOn X).obj.obj (op U),
        R₂.arrow.hom.app (op U) r' = R₁.arrow.hom.app (op U) r) :
    R₁ ≤ R₂ := by
  let φ : (R₁ : SheafOn X).obj ⟶ (R₂ : SheafOn X).obj :=
    { app := fun U => TypeCat.ofHom fun r => (h (unop U) r).choose
      naturality := by
        intro U V k
        ext r
        apply injective_of_mono R₂.arrow (unop V)
        have e₁ := (h (unop V) ((R₁ : SheafOn X).obj.map k r)).choose_spec
        have e₂ := (h (unop U) r).choose_spec
        have n₁ := NatTrans.naturality_apply R₁.arrow.hom k r
        have n₂ := NatTrans.naturality_apply R₂.arrow.hom k (h (unop U) r).choose
        exact e₁.trans (n₁.trans ((congrArg (F.obj.map k) e₂.symm).trans n₂.symm)) }
  refine Subobject.le_of_comm (ObjectProperty.homMk φ) ?_
  apply Sheaf.hom_ext
  ext U r
  exact (h (unop U) r).choose_spec

/-- **A subobject of a sheaf is determined by the sections that factor through it.** -/
theorem subobject_eq_of_sections {F : SheafOn X} {R₁ R₂ : Subobject F}
    (h : ∀ (U : Opens X) (s : F.obj.obj (op U)),
      (∃ r, R₁.arrow.hom.app (op U) r = s) ↔ (∃ r, R₂.arrow.hom.app (op U) r = s)) :
    R₁ = R₂ :=
  le_antisymm (subobject_le_of_sections fun U r => (h U _).mp ⟨r, rfl⟩)
    (subobject_le_of_sections fun U r => (h U _).mpr ⟨r, rfl⟩)

/-- The sections factoring through `Subobject.mk f` are those in the image of `f`. -/
theorem mk_arrow_sections {F A : SheafOn X} (f : A ⟶ F) [Mono f] (U : Opens X)
    (s : F.obj.obj (op U)) :
    (∃ r, (Subobject.mk f).arrow.hom.app (op U) r = s) ↔ ∃ a, f.hom.app (op U) a = s := by
  have e := Subobject.underlyingIso_hom_comp_eq_mk f
  constructor
  · rintro ⟨r, rfl⟩
    refine ⟨(Subobject.underlyingIso f).hom.hom.app (op U) r, ?_⟩
    exact congrArg (fun k => k.hom.app (op U) r) e
  · rintro ⟨a, rfl⟩
    refine ⟨(Subobject.underlyingIso f).inv.hom.app (op U) a, ?_⟩
    rw [← e]
    change f.hom.app (op U) (((Subobject.underlyingIso f).inv ≫
      (Subobject.underlyingIso f).hom).hom.app (op U) a) = _
    rw [Iso.inv_hom_id]
    rfl

/-- The sections factoring through the pullback of a subobject along `g` are those whose image
under `g` factors through the subobject. -/
theorem pullback_arrow_sections {F G : SheafOn X} (g : G ⟶ F) (y : Subobject F) (U : Opens X)
    (s : G.obj.obj (op U)) :
    (∃ r, ((Subobject.pullback g).obj y).arrow.hom.app (op U) r = s) ↔
      ∃ r, y.arrow.hom.app (op U) r = g.hom.app (op U) s := by
  have sq := isPullback_sections (Subobject.isPullback g y) U
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨(Subobject.pullbackπ g y).hom.app (op U) r,
      congrArg (fun k => k.hom.app (op U) r) (Subobject.isPullback g y).w⟩
  · rintro ⟨r, hr⟩
    obtain ⟨p, -, hp⟩ := Types.exists_of_isPullback sq r s hr
    exact ⟨p, hp⟩

end Subobjects

end Mettapedia.SetTheory.CarveOuts.Sheaves
