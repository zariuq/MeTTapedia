import Mettapedia.SetTheory.CarveOuts.Sites.ProductSite
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.Topology.Sets.Opens
import Mathlib.Logic.Small.Basic

/-!
# Classes of small maps: the basic small-map axioms

The final coalgebra of the power-class functor of a class of small maps is a model of
non-well-founded set theory with Aczel's anti-foundation axiom (van den Berg and De Marchi,
*Models of non-well-founded sets via an indexed final coalgebra theorem*, 2007). Their
Theorem 3.7 gives the indexed final coalgebra and Corollary 4.3 makes it a model of
`CZF₀ + AFA`. Both assume an ambient Heyting pretopos with an indexed natural numbers object,
and a class of small maps satisfying the basic axioms in indexed form, stable under slicing.
This module states the basic axioms and proves those that hold on presheaves. It states none
of the ambient structure and does not construct the coalgebra.

**The axioms** (in the formulation the paper takes from Awodey and others), for a class `S` of
maps of a category `E`:

* (S1) closed under composition and identities; (S2) stable under pullback; (S3) diagonals are
  small; (S4) if `e ≫ g` is small and `e` is epi, then `g` is small; (S5) the copairing of two
  small maps is small. Together: `SmallMapClass`.
* (P1) power classes: small relations into `X` are classified by maps into an object `Pₛ X`
  (`PowerClass`, `PowerClassAxiom`).
* (I) the natural numbers object is small (`ParamNNO`, `NaturalsSmallAxiom`). As stated, (I)
  quantifies over the parametrised natural numbers objects of `E`: it assumes one is given and
  does not carry one.
* (R) representability: one small map of which every small map is locally a pullback
  (`RepresentabilityAxiom`).

`BasicSmallMapAxioms` collects them: the basic axioms only. An earlier name for the bundle
suggested the final coalgebra itself; the ambient obligations (a Heyting pretopos, an indexed
natural numbers object, the axioms in indexed form, the power-class functor as an indexed
functor) and the final coalgebra are separate. Stronger set theories need further axioms,
stated for reference: (M) every mono is small (`MonosSmall`); (C) collection
(`CollectionAxiom`); (E) dependent products along small maps preserve small maps
(`ExponentiationAxiom`), for the paper's Theorem 4.4. The axioms (P2), for Theorem 4.5 with (M)
and (C), and (F), for Theorem 4.7 with (C), are not stated.

**The test case.** On presheaves `C ⥤ Type v` over any category, the maps whose fibres are
`w`-small at every point (`fibrewiseSmall`) satisfy (S1)–(S5) (`fibrewiseSmall_smallMapClass`)
and (M) (`fibrewiseSmall_monosSmall`). On the product site of contexts and the open sets of
Cantor space this gives `cantor_smallMapClass`; (P1), (I) and (R) remain hypotheses
(`cantor_basicSmallMapAxioms`). These are presheaves on the site: the covers of Cantor space
play no part in the proved axioms, and the category of sheaves, where epimorphisms are local
surjections, is not built here. None of Collection, power classes or universes is derived from
the frame.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps

open CategoryTheory Limits

universe w v u u'

/-! ## The axioms -/

section Axioms

variable {E : Type u} [Category.{v} E]

/-- **A class of small maps**: the axioms (S1)–(S5). -/
structure SmallMapClass [HasBinaryProducts E] [HasBinaryCoproducts E] (S : MorphismProperty E) :
    Prop where
  /-- (S1) Composition. -/
  comp : ∀ {X Y Z : E} (f : X ⟶ Y) (g : Y ⟶ Z), S f → S g → S (f ≫ g)
  /-- (S1) Identities. -/
  id : ∀ X : E, S (𝟙 X)
  /-- (S2) The pullback `fst` of a small `g` along `f` is small. -/
  pullback : ∀ {P X Y Z : E} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z},
    IsPullback fst snd f g → S g → S fst
  /-- (S3) Diagonals. -/
  diagonal : ∀ X : E, S (prod.lift (𝟙 X) (𝟙 X))
  /-- (S4) Quotients: a map through which a small map factors by an epi is small. -/
  quotient : ∀ {C D A : E} (e : C ⟶ D) (g : D ⟶ A), Epi e → S (e ≫ g) → S g
  /-- (S5) Copairing. -/
  copair : ∀ {C D A : E} (f : C ⟶ A) (g : D ⟶ A), S f → S g → S (coprod.desc f g)

/-- A small relation between `I` and `X`: a subobject of `I ⨯ X` small over `I`. -/
def IsSmallRelation [HasBinaryProducts E] (S : MorphismProperty E) {I X : E}
    (R : Subobject (I ⨯ X)) : Prop :=
  S (R.arrow ≫ prod.fst)

/-- **(P1) A power class of `X`**: an object `Pₛ X` with a small membership relation that
classifies every small relation into `X`, by pulling back along a unique map. -/
structure PowerClass [HasBinaryProducts E] [HasPullbacks E] (S : MorphismProperty E) (X : E) where
  obj : E
  mem : Subobject (obj ⨯ X)
  mem_small : IsSmallRelation S mem
  classify : ∀ {I : E} (R : Subobject (I ⨯ X)), IsSmallRelation S R →
    ∃! χ : I ⟶ obj, (Subobject.pullback (prod.map χ (𝟙 X))).obj mem = R

/-- (P1) Every object has a power class. -/
def PowerClassAxiom [HasBinaryProducts E] [HasPullbacks E] (S : MorphismProperty E) : Prop :=
  ∀ X : E, Nonempty (PowerClass S X)

/-- A parametrised natural numbers object. -/
structure ParamNNO (E : Type u) [Category.{v} E] [HasBinaryProducts E] [HasTerminal E] where
  N : E
  zero : ⊤_ E ⟶ N
  succ : N ⟶ N
  recursion : ∀ {P Y : E} (f : P ⟶ Y) (t : P ⨯ Y ⟶ Y), ∃! h : P ⨯ N ⟶ Y,
    prod.lift (𝟙 P) (terminal.from P ≫ zero) ≫ h = f ∧
      prod.map (𝟙 P) succ ≫ h = prod.lift prod.fst h ≫ t

/-- (I) The natural numbers object is small. -/
def NaturalsSmallAxiom [HasBinaryProducts E] [HasTerminal E] (S : MorphismProperty E) : Prop :=
  ∀ nno : ParamNNO E, S (terminal.from nno.N)

/-- (R) **Representability**: one small map `π` such that every small map is, over an epi, a
pullback of `π`. -/
def RepresentabilityAxiom (S : MorphismProperty E) : Prop :=
  ∃ (U El : E) (π : El ⟶ U), S π ∧ ∀ {A B : E} (f : A ⟶ B), S f →
    ∃ (B' A' : E) (q : B' ⟶ B) (k : B' ⟶ U) (f' : A' ⟶ B') (l : A' ⟶ A) (m : A' ⟶ El),
      Epi q ∧ IsPullback l f' f q ∧ IsPullback m f' π k

/-- **The basic small-map axioms** (S1)–(S5), (P1), (I) and (R). They are what the final
coalgebra of the power-class functor needs of the class of small maps, in non-indexed form; the
ambient structure that construction also needs is not part of this bundle. -/
structure BasicSmallMapAxioms [HasBinaryProducts E] [HasBinaryCoproducts E] [HasPullbacks E]
    [HasTerminal E] (S : MorphismProperty E) : Prop where
  smallMaps : SmallMapClass S
  powerClass : PowerClassAxiom S
  naturalsSmall : NaturalsSmallAxiom S
  representable : RepresentabilityAxiom S

/-- (M) Every monomorphism is small. -/
def MonosSmall (S : MorphismProperty E) : Prop :=
  ∀ {X Y : E} (m : X ⟶ Y), Mono m → S m

/-- (C) **Collection.** Over an epi onto the domain of a small map, a small map covering it can
be chosen, up to a further epi. -/
def CollectionAxiom [HasPullbacks E] (S : MorphismProperty E) : Prop :=
  ∀ {Y X A : E} (p : Y ⟶ X) (f : X ⟶ A), Epi p → S f →
    ∃ (Z B : E) (z : Z ⟶ Y) (g : Z ⟶ B) (h : B ⟶ A) (w : (z ≫ p) ≫ f = g ≫ h),
      Epi h ∧ S g ∧ Epi (pullback.lift (z ≫ p) g w)

/-- (E) Dependent products along small maps preserve small maps. -/
def ExponentiationAxiom [HasPullbacks E] (S : MorphismProperty E) : Prop :=
  ∀ {X Y : E} (f : X ⟶ Y), S f → ∀ (pi : Over X ⥤ Over Y), (Over.pullback f ⊣ pi) →
    ∀ A : Over X, S A.hom → S (pi.obj A).hom

end Axioms

/-! ## Presheaves: maps with small fibres -/

section Presheaves

variable {C : Type u} [Category.{u'} C]

/-- The maps of presheaves whose fibres are `w`-small at every point. -/
def fibrewiseSmall : MorphismProperty (C ⥤ Type v) :=
  fun _ G η => ∀ (c : C) (x : G.obj c), Small.{w} {y // η.app c y = x}

theorem fibrewiseSmall_comp {F G K : C ⥤ Type v} (η : F ⟶ G) (θ : G ⟶ K)
    (hη : fibrewiseSmall.{w} η) (hθ : fibrewiseSmall.{w} θ) : fibrewiseSmall.{w} (η ≫ θ) := by
  intro c z
  have := hθ c z
  have : ∀ x : {x // θ.app c x = z}, Small.{w} {y // η.app c y = x.1} := fun x => hη c x.1
  refine small_of_injective (β := Σ x : {x // θ.app c x = z}, {y // η.app c y = x.1})
    (f := fun y => ⟨⟨η.app c y.1, y.2⟩, ⟨y.1, rfl⟩⟩) fun a b h => ?_
  exact Subtype.ext (congrArg (fun s : Σ x : {x // θ.app c x = z}, {y // η.app c y = x.1} => s.2.1) h)

theorem fibrewiseSmall_of_injective {F G : C ⥤ Type v} (η : F ⟶ G)
    (h : ∀ c, Function.Injective (η.app c)) : fibrewiseSmall.{w} η := by
  intro c x
  have : Subsingleton {y // η.app c y = x} :=
    ⟨fun a b => Subtype.ext (h c (a.2.trans b.2.symm))⟩
  infer_instance

/-- **(M) Every mono of presheaves has small fibres.** -/
theorem fibrewiseSmall_monosSmall : MonosSmall (fibrewiseSmall.{w} : MorphismProperty (C ⥤ Type v)) := by
  intro X Y m hm
  exact fibrewiseSmall_of_injective m fun c =>
    (mono_iff_injective (m.app c)).mp ((NatTrans.mono_iff_mono_app m).mp hm c)

theorem fibrewiseSmall_pullback {P X Y Z : C ⥤ Type v} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (sq : IsPullback fst snd f g) (hg : fibrewiseSmall.{w} g) :
    fibrewiseSmall.{w} fst := by
  intro c x
  have sqc : IsPullback (fst.app c) (snd.app c) (f.app c) (g.app c) :=
    Functor.map_isPullback ((evaluation C (Type v)).obj c) sq
  have := hg c (f.app c x)
  have commutes : ∀ y, f.app c (fst.app c y) = g.app c (snd.app c y) := fun y =>
    congr_fun (congrArg (fun k => (ConcreteCategory.hom k : _ → _)) sqc.w) y
  refine small_of_injective (β := {y // g.app c y = f.app c x})
    (f := fun p => ⟨snd.app c p.1, (commutes p.1).symm.trans (congrArg (fun y => f.app c y) p.2)⟩)
    fun a b h => ?_
  exact Subtype.ext (Types.ext_of_isPullback sqc (a.2.trans b.2.symm)
      (congrArg Subtype.val h))

theorem fibrewiseSmall_quotient {Cₒ D A : C ⥤ Type v} (e : Cₒ ⟶ D) (g : D ⟶ A) (he : Epi e)
    (h : fibrewiseSmall.{w} (e ≫ g)) : fibrewiseSmall.{w} g := by
  intro c a
  have := h c a
  have surj : Function.Surjective (e.app c) :=
    (epi_iff_surjective (e.app c)).mp ((NatTrans.epi_iff_epi_app e).mp he c)
  refine small_of_surjective (α := {y // (e ≫ g).app c y = a})
    (f := fun y => ⟨e.app c y.1, y.2⟩) fun x => ?_
  obtain ⟨y, hy⟩ := surj x.1
  refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
  show g.app c (e.app c y) = a
  rw [hy]
  exact x.2

theorem fibrewiseSmall_copair {Cₒ D A : C ⥤ Type v} (f : Cₒ ⟶ A) (g : D ⟶ A)
    (hf : fibrewiseSmall.{w} f) (hg : fibrewiseSmall.{w} g) :
    fibrewiseSmall.{w} (coprod.desc f g) := by
  intro c a
  have := hf c a
  have := hg c a
  have colim : IsColimit (BinaryCofan.mk ((coprod.inl : Cₒ ⟶ Cₒ ⨿ D).app c)
      ((coprod.inr : D ⟶ Cₒ ⨿ D).app c)) :=
    (isColimitMapCoconeBinaryCofanEquiv ((evaluation C (Type v)).obj c) coprod.inl coprod.inr)
      (isColimitOfPreserves ((evaluation C (Type v)).obj c) (coprodIsCoprod Cₒ D))
  have covers := ((Types.binaryCofan_isColimit_iff _).mp ⟨colim⟩).2.2.sup_eq_top
  have inl_desc : ∀ y, (coprod.desc f g).app c ((coprod.inl : Cₒ ⟶ Cₒ ⨿ D).app c y) = f.app c y :=
    fun y => congr_fun (congrArg (fun k => (ConcreteCategory.hom k : _ → _))
      (congrArg (fun k => NatTrans.app k c) (coprod.inl_desc f g))) y
  have inr_desc : ∀ y, (coprod.desc f g).app c ((coprod.inr : D ⟶ Cₒ ⨿ D).app c y) = g.app c y :=
    fun y => congr_fun (congrArg (fun k => (ConcreteCategory.hom k : _ → _))
      (congrArg (fun k => NatTrans.app k c) (coprod.inr_desc f g))) y
  refine small_of_surjective (α := {y // f.app c y = a} ⊕ {y // g.app c y = a})
    (f := Sum.elim (fun y => ⟨(coprod.inl : Cₒ ⟶ Cₒ ⨿ D).app c y.1, (inl_desc y.1).trans y.2⟩)
      (fun y => ⟨(coprod.inr : D ⟶ Cₒ ⨿ D).app c y.1, (inr_desc y.1).trans y.2⟩)) fun x => ?_
  have hx : x.1 ∈ Set.range ((coprod.inl : Cₒ ⟶ Cₒ ⨿ D).app c) ⊔
      Set.range ((coprod.inr : D ⟶ Cₒ ⨿ D).app c) := by
    rw [show Set.range ((coprod.inl : Cₒ ⟶ Cₒ ⨿ D).app c) ⊔
      Set.range ((coprod.inr : D ⟶ Cₒ ⨿ D).app c) = ⊤ from covers]
    trivial
  rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
  · refine ⟨Sum.inl ⟨y, ?_⟩, Subtype.ext hy⟩
    rw [← inl_desc y, hy]
    exact x.2
  · refine ⟨Sum.inr ⟨y, ?_⟩, Subtype.ext hy⟩
    rw [← inr_desc y, hy]
    exact x.2

/-- **(S1)–(S5) hold for maps of presheaves with small fibres.** -/
theorem fibrewiseSmall_smallMapClass :
    SmallMapClass (fibrewiseSmall.{w} : MorphismProperty (C ⥤ Type v)) where
  comp f g hf hg := fibrewiseSmall_comp f g hf hg
  id X := fibrewiseSmall_of_injective (𝟙 X) fun _ => fun _ _ h => h
  pullback sq hg := fibrewiseSmall_pullback sq hg
  diagonal X := fibrewiseSmall_monosSmall _ (mono_of_mono_fac (prod.lift_fst (𝟙 X) (𝟙 X)))
  quotient e g he h := fibrewiseSmall_quotient e g he h
  copair f g hf hg := fibrewiseSmall_copair f g hf hg

end Presheaves

/-! ## The Cantor test case -/

section Cantor

/-- The product site of a context category and the open sets of Cantor space. -/
abbrev CantorSite (D : Type) [Category.{0} D] : Type :=
  D × (TopologicalSpace.Opens (ℕ → Bool))ᵒᵈ

variable (D : Type) [Category.{0} D]

/-- **(S1)–(S5) on presheaves over the Cantor product site.** -/
theorem cantor_smallMapClass :
    SmallMapClass (fibrewiseSmall.{w} : MorphismProperty (CantorSite D ⥤ Type v)) :=
  fibrewiseSmall_smallMapClass

/-- **(M) on presheaves over the Cantor product site.** -/
theorem cantor_monosSmall : MonosSmall (fibrewiseSmall.{w} : MorphismProperty (CantorSite D ⥤ Type v)) :=
  fibrewiseSmall_monosSmall

/-- **The remaining axioms are hypotheses.** With (P1), (I) and (R) supplied, presheaves over
the Cantor product site satisfy the basic small-map axioms. -/
theorem cantor_basicSmallMapAxioms
    (powerClass : PowerClassAxiom (fibrewiseSmall.{w} : MorphismProperty (CantorSite D ⥤ Type v)))
    (naturalsSmall : NaturalsSmallAxiom (fibrewiseSmall.{w} : MorphismProperty (CantorSite D ⥤ Type v)))
    (representable : RepresentabilityAxiom (fibrewiseSmall.{w} : MorphismProperty (CantorSite D ⥤ Type v))) :
    BasicSmallMapAxioms (fibrewiseSmall.{w} : MorphismProperty (CantorSite D ⥤ Type v)) :=
  ⟨cantor_smallMapClass D, powerClass, naturalsSmall, representable⟩

end Cantor

end Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps
