import Mettapedia.SetTheory.CarveOuts.Sheaves.Forcing
import Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# Small maps on sheaves over a space: epimorphisms are local surjections

The category is `Sheaf (Opens.grothendieckTopology X) (Type u)`, sheaves of sets on a space `X`
whose open sets form a `w`-small type. Epimorphisms of sheaves are the **locally surjective**
maps (Mathlib's `Sheaf.isLocallySurjective_iff_epi`), not the pointwise surjective ones, so the
covers of `X` enter the axioms.

**The class.** A map of sheaves is small when its fibres are `w`-small at every open set
(`sheafSmall`), the pointwise definition of van den Berg and Moerdijk, *Aspects of predicative
algebraic set theory III: sheaves* (§4.2).

**The axioms proved** (`sheafSmall_smallMapClass`, `sheafSmall_monosSmall`):

* (S1) composition and identities, (S2) pullback, (M) monos and so (S3) diagonals: limits and
  monos of sheaves are those of presheaves.
* (S4) quotients along an epimorphism, which is only locally surjective
  (`fibrewiseSmall_of_covered_surjective`): an element of a fibre is determined by the set of
  local preimages it has, because a sheaf is separated. That set lives in the power set of a
  small type; this is where the host's power sets stand in for the fullness axiom that van den
  Berg and Moerdijk use (their Proposition 4.5).
* (S5) copairing: the sections of a coproduct of sheaves are locally in one of the two summands
  (`coprod_covered`, proved from the universal property with the image subsheaf), and (S4)'s
  argument applies.

(P1), (I), (R) and (E) are left as hypotheses (`sheaf_basicSmallMapAxioms`). Collection is
in `Sheaves.Collection`.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.Sheaves

open CategoryTheory Limits TopologicalSpace Opposite
open Mettapedia.SetTheory.CarveOuts.Sites
open Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps

universe w u

variable {X : Type u} [TopologicalSpace X]

/-- The sheaves of sets on a space. -/
abbrev SheafOn (X : Type u) [TopologicalSpace X] : Type (u + 1) :=
  Sheaf (Opens.grothendieckTopology X) (Type u)

/-- **Small maps of sheaves**: maps whose fibres are `w`-small at every open set. -/
def sheafSmall : MorphismProperty (SheafOn X) :=
  fun _ _ f => fibrewiseSmall.{w} f.hom

/-! ## Covers from Mathlib's local surjectivity -/

/-- A locally surjective map of presheaves: every section is, on a cover, an image. -/
theorem covered_surjective_of_isLocallySurjective {P Q : (Opens X)ᵒᵖ ⥤ Type u} (e : P ⟶ Q)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) e] (U : Opens X)
    (y : Q.obj (op U)) :
    Covered U fun V h => ∃ c : P.obj (op V), e.app (op V) c = Q.map (homOfLE h).op y :=
  covered_of_mem (Presheaf.imageSieve_mem (Opens.grothendieckTopology X) e (U := op U) y)
    fun _ _ ⟨c, hc⟩ => ⟨c, hc⟩

/-- An epimorphism of sheaves: every section is, on a cover, an image. -/
theorem covered_surjective_of_epi {P Q : SheafOn X} (e : P ⟶ Q) [Epi e] (U : Opens X)
    (y : Q.obj.obj (op U)) :
    Covered U fun V h => ∃ c : P.obj.obj (op V), e.hom.app (op V) c = Q.obj.map (homOfLE h).op y := by
  have : Sheaf.IsLocallySurjective e := (Sheaf.isLocallySurjective_iff_epi e).mpr inferInstance
  exact covered_surjective_of_isLocallySurjective e.hom U y

/-! ## Quotients along local surjections -/

/-- **The quotient lemma.** Let `e : P ⟶ Q` be locally surjective onto a sheaf and `g : Q ⟶ R`.
If `e ≫ g` has small fibres, so does `g`: a section in a fibre of `g` is determined by its set of
local preimages, a subset of a small type. -/
theorem fibrewiseSmall_of_covered_surjective [Small.{w} (Opens X)] {P R : (Opens X)ᵒᵖ ⥤ Type u}
    {Q : SheafOn X} (e : P ⟶ Q.obj) (g : Q.obj ⟶ R)
    (he : ∀ (U : Opens X) (y : Q.obj.obj (op U)),
      Covered U fun V h => ∃ c : P.obj (op V), e.app (op V) c = Q.obj.map (homOfLE h).op y)
    (small : fibrewiseSmall.{w} (e ≫ g)) : fibrewiseSmall.{w} g := by
  intro U a
  let Index := Σ V : {V : Opens X // V ≤ unop U},
    {c : P.obj (op V.1) // (e ≫ g).app (op V.1) c = R.map (homOfLE V.2).op a}
  have : ∀ V : {V : Opens X // V ≤ unop U},
      Small.{w} {c : P.obj (op V.1) // (e ≫ g).app (op V.1) c = R.map (homOfLE V.2).op a} :=
    fun V => small (op V.1) _
  let encode : {y // g.app U y = a} → Set Index := fun y =>
    {t | e.app (op t.1.1) t.2.1 = Q.obj.map (homOfLE t.1.2).op y.1}
  refine small_of_injective (f := encode) fun y y' same => Subtype.ext ?_
  refine sheaf_eq_of_covered Q (U := unop U)
    (covered_mono (fun V h ⟨c, hc⟩ => ?_) (he (unop U) y.1))
  have fibre : (e ≫ g).app (op V) c = R.map (homOfLE h).op a := by
    rw [NatTrans.comp_app_apply, hc, NatTrans.naturality_apply, y.2]
  have mem : (⟨⟨V, h⟩, ⟨c, fibre⟩⟩ : Index) ∈ encode y := hc
  rw [same] at mem
  exact hc.symm.trans mem

/-! ## Coproducts of sheaves are locally one summand -/

/-- The pointwise sum of two presheaves. -/
def sumPresheaf (P₁ P₂ : (Opens X)ᵒᵖ ⥤ Type u) : (Opens X)ᵒᵖ ⥤ Type u where
  obj U := P₁.obj U ⊕ P₂.obj U
  map f := TypeCat.ofHom (Sum.map (P₁.map f) (P₂.map f))
  map_id U := by
    ext s
    rcases s with s | s
    · exact congrArg Sum.inl (P₁.map_id_apply U s)
    · exact congrArg Sum.inr (P₂.map_id_apply U s)
  map_comp f g := by
    ext s
    rcases s with s | s
    · exact congrArg Sum.inl (P₁.map_comp_apply f g s)
    · exact congrArg Sum.inr (P₂.map_comp_apply f g s)

/-- The two coprojections of a cofan, as one map from the pointwise sum. -/
def cofanSum {C₁ C₂ : SheafOn X} (c : BinaryCofan C₁ C₂) :
    sumPresheaf C₁.obj C₂.obj ⟶ c.pt.obj where
  app U := TypeCat.ofHom (Sum.elim (c.inl.hom.app U) (c.inr.hom.app U))
  naturality U V f := by
    ext s
    rcases s with s | s
    · exact NatTrans.naturality_apply c.inl.hom f s
    · exact NatTrans.naturality_apply c.inr.hom f s

/-- **The sections of a coproduct of sheaves are locally in one summand.** The closure of the
union of the two images is a subsheaf through which both coprojections factor; by the universal
property it is everything. -/
theorem coprod_covered {C₁ C₂ : SheafOn X} (c : BinaryCofan C₁ C₂) (hc : IsColimit c)
    (U : Opens X) (y : c.pt.obj.obj (op U)) :
    Covered U fun V h => ∃ s : (sumPresheaf C₁.obj C₂.obj).obj (op V),
      (cofanSum c).app (op V) s = c.pt.obj.map (homOfLE h).op y := by
  have hsheaf : Presieve.IsSheaf (Opens.grothendieckTopology X) c.pt.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).mp c.pt.property
  let G := (Subfunctor.range (cofanSum c)).sheafify (Opens.grothendieckTopology X)
  let S : SheafOn X := ⟨G.toFunctor, (isSheaf_iff_isSheaf_of_type _ _).mpr
    ((Subfunctor.range (cofanSum c)).sheafify_isSheaf hsheaf)⟩
  let ι : S ⟶ c.pt := ObjectProperty.homMk G.ι
  have range_le : ∀ {P : (Opens X)ᵒᵖ ⥤ Type u} (k : P ⟶ c.pt.obj),
      (∀ V (s : P.obj V), ∃ t, (cofanSum c).app V t = k.app V s) → Subfunctor.range k ≤ G := by
    intro P k hk V _ ⟨s, hs⟩
    obtain ⟨t, ht⟩ := hk V s
    exact Subfunctor.le_sheafify _ _ _ ⟨t, ht.trans hs⟩
  let inl' : C₁ ⟶ S := ObjectProperty.homMk (Subfunctor.lift c.inl.hom
    (range_le c.inl.hom fun _ s => ⟨Sum.inl s, rfl⟩))
  let inr' : C₂ ⟶ S := ObjectProperty.homMk (Subfunctor.lift c.inr.hom
    (range_le c.inr.hom fun _ s => ⟨Sum.inr s, rfl⟩))
  let back : c.pt ⟶ S := BinaryCofan.IsColimit.desc hc inl' inr'
  have section_ : back ≫ ι = 𝟙 c.pt := by
    refine BinaryCofan.IsColimit.hom_ext hc ?_ ?_
    · apply Sheaf.hom_ext
      have h1 : c.inl.hom ≫ back.hom = inl'.hom :=
        congrArg (fun k => k.hom) (BinaryCofan.IsColimit.inl_desc hc inl' inr')
      show c.inl.hom ≫ back.hom ≫ G.ι = c.inl.hom ≫ 𝟙 _
      rw [← Category.assoc, h1, Category.comp_id]
      rfl
    · apply Sheaf.hom_ext
      have h1 : c.inr.hom ≫ back.hom = inr'.hom :=
        congrArg (fun k => k.hom) (BinaryCofan.IsColimit.inr_desc hc inl' inr')
      show c.inr.hom ≫ back.hom ≫ G.ι = c.inr.hom ≫ 𝟙 _
      rw [← Category.assoc, h1, Category.comp_id]
      rfl
  have mem : y ∈ G.obj (op U) := by
    have same := congrArg (fun k => k.hom.app (op U) y) section_
    change G.ι.app _ (back.hom.app _ y) = y at same
    rw [← same]
    exact (back.hom.app (op U) y).2
  exact covered_of_mem mem fun V f ⟨s, hs⟩ => ⟨s, hs⟩

/-! ## The axioms -/

theorem sheafSmall_comp {F G K : SheafOn X} (f : F ⟶ G) (g : G ⟶ K) (hf : sheafSmall.{w} f)
    (hg : sheafSmall.{w} g) : sheafSmall.{w} (f ≫ g) :=
  fibrewiseSmall_comp f.hom g.hom hf hg

/-- **(M) Every mono of sheaves has small fibres.** -/
theorem sheafSmall_monosSmall : MonosSmall (sheafSmall.{w} : MorphismProperty (SheafOn X)) := by
  intro F G m hm
  have : Mono m.hom := (sheafToPresheaf (Opens.grothendieckTopology X) (Type u)).map_mono m
  exact fibrewiseSmall_monosSmall m.hom this

theorem sheafSmall_pullback {P F G K : SheafOn X} {fst : P ⟶ F} {snd : P ⟶ G} {f : F ⟶ K}
    {g : G ⟶ K} (sq : IsPullback fst snd f g) (hg : sheafSmall.{w} g) : sheafSmall.{w} fst :=
  fibrewiseSmall_pullback (Functor.map_isPullback
    (sheafToPresheaf (Opens.grothendieckTopology X) (Type u)) sq) hg

variable [Small.{w} (Opens X)]

/-- **(S4) Quotients along an epimorphism of sheaves**, which is only locally surjective. -/
theorem sheafSmall_quotient {C Q A : SheafOn X} (e : C ⟶ Q) (g : Q ⟶ A) (he : Epi e)
    (h : sheafSmall.{w} (e ≫ g)) : sheafSmall.{w} g :=
  fibrewiseSmall_of_covered_surjective e.hom g.hom (covered_surjective_of_epi e) h

/-- **(S5) Copairing**, for any colimit cofan. -/
theorem sheafSmall_copair_of_isColimit {C₁ C₂ A : SheafOn X} (c : BinaryCofan C₁ C₂)
    (hc : IsColimit c) (f : C₁ ⟶ A) (g : C₂ ⟶ A) (k : c.pt ⟶ A) (hk₁ : c.inl ≫ k = f)
    (hk₂ : c.inr ≫ k = g) (hf : sheafSmall.{w} f) (hg : sheafSmall.{w} g) :
    sheafSmall.{w} k := by
  refine fibrewiseSmall_of_covered_surjective (cofanSum c) k.hom (coprod_covered c hc) ?_
  intro U a
  have := hf U a
  have := hg U a
  refine small_of_injective (β := {s // f.hom.app U s = a} ⊕ {s // g.hom.app U s = a})
    (f := fun s => match s with
      | ⟨Sum.inl s, hs⟩ => Sum.inl ⟨s, by rw [← hk₁]; exact hs⟩
      | ⟨Sum.inr s, hs⟩ => Sum.inr ⟨s, by rw [← hk₂]; exact hs⟩) ?_
  rintro ⟨s | s, hs⟩ ⟨s' | s', hs'⟩ same
  · simp only [Sum.inl.injEq, Subtype.mk.injEq] at same
    subst same
    rfl
  · simp at same
  · simp at same
  · simp only [Sum.inr.injEq, Subtype.mk.injEq] at same
    subst same
    rfl

/-- **(S1)–(S5) for small maps of sheaves.** -/
theorem sheafSmall_smallMapClass :
    SmallMapClass (sheafSmall.{w} : MorphismProperty (SheafOn X)) where
  comp f g hf hg := sheafSmall_comp f g hf hg
  id F := fibrewiseSmall_of_injective (𝟙 F.obj) fun _ _ _ h => h
  pullback sq hg := sheafSmall_pullback sq hg
  diagonal F := sheafSmall_monosSmall _ (mono_of_mono_fac (prod.lift_fst (𝟙 F) (𝟙 F)))
  quotient e g he h := sheafSmall_quotient e g he h
  copair f g hf hg := sheafSmall_copair_of_isColimit _ (coprodIsCoprod _ _) f g
    (coprod.desc f g) (coprod.inl_desc f g) (coprod.inr_desc f g) hf hg

/-- **The remaining axioms are hypotheses.** With (P1), (I) and (R) supplied, small maps of
sheaves satisfy the basic small-map axioms. -/
theorem sheaf_basicSmallMapAxioms
    (powerClass : PowerClassAxiom (sheafSmall.{w} : MorphismProperty (SheafOn X)))
    (naturalsSmall : NaturalsSmallAxiom (sheafSmall.{w} : MorphismProperty (SheafOn X)))
    (representable : RepresentabilityAxiom (sheafSmall.{w} : MorphismProperty (SheafOn X))) :
    BasicSmallMapAxioms (sheafSmall.{w} : MorphismProperty (SheafOn X)) :=
  ⟨sheafSmall_smallMapClass, powerClass, naturalsSmall, representable⟩

end Mettapedia.SetTheory.CarveOuts.Sheaves
