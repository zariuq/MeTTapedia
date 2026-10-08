import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.GaloisConnection.Defs

/-!
# Indexed first-order and higher-order predicate doctrines

Predicate fibres are actual Heyting algebras, with contravariant substitution
preserving their finite logical operations. Quantification has both adjunctions,
Frobenius reciprocity and Beck--Chevalley across actual pullback squares.
The associated contravariant Grothendieck construction is the categorical
fibration, rather than an object-indexed collection of orders.

The higher-order extension has a generic predicate whose substitutions classify
every predicate uniquely. Its characteristic maps are not assumed to classify
arbitrary proof-valued dependent families.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.PredicateDoctrine

open _root_.CategoryTheory _root_.CategoryTheory.Functor
  _root_.CategoryTheory.Limits Opposite MonoidalCategory

universe u v w

variable (B : Type u) [Category.{v} B]

/-- An indexed Heyting algebra with strict substitution. -/
structure IndexedHeyting where
  Fiber : B → Type w
  [algebra : ∀ X, HeytingAlgebra (Fiber X)]
  reindex : ∀ {X Y : B}, (X ⟶ Y) → Fiber Y → Fiber X
  reindex_mono : ∀ {X Y : B} (f : X ⟶ Y), Monotone (reindex f)
  reindex_id : ∀ X (φ : Fiber X), reindex (𝟙 X) φ = φ
  reindex_comp : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) (φ : Fiber Z),
    reindex (f ≫ g) φ = reindex f (reindex g φ)
  reindex_top : ∀ {X Y : B} (f : X ⟶ Y), reindex f ⊤ = ⊤
  reindex_bot : ∀ {X Y : B} (f : X ⟶ Y), reindex f ⊥ = ⊥
  reindex_inf : ∀ {X Y : B} (f : X ⟶ Y) (φ ψ : Fiber Y),
    reindex f (φ ⊓ ψ) = reindex f φ ⊓ reindex f ψ
  reindex_sup : ∀ {X Y : B} (f : X ⟶ Y) (φ ψ : Fiber Y),
    reindex f (φ ⊔ ψ) = reindex f φ ⊔ reindex f ψ
  reindex_himp : ∀ {X Y : B} (f : X ⟶ Y) (φ ψ : Fiber Y),
    reindex f (φ ⇨ ψ) = reindex f φ ⇨ reindex f ψ

attribute [instance] IndexedHeyting.algebra

namespace IndexedHeyting

variable {B} (D : IndexedHeyting.{u,v,w} B)

/-- The actual substitution functor between order categories. -/
def reindexFunctor {X Y : B} (f : X ⟶ Y) : D.Fiber Y ⥤ D.Fiber X :=
  (D.reindex_mono f).functor

theorem reindexFunctor_id (X : B) : D.reindexFunctor (𝟙 X) = 𝟭 (D.Fiber X) := by
  refine CategoryTheory.Functor.ext (D.reindex_id X) ?_
  intros
  apply Subsingleton.elim

theorem reindexFunctor_comp {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    D.reindexFunctor (f ≫ g) = D.reindexFunctor g ⋙ D.reindexFunctor f := by
  refine CategoryTheory.Functor.ext (D.reindex_comp f g) ?_
  intros
  apply Subsingleton.elim

/-- The concrete contravariant categorical action of the doctrine. -/
def indexedFunctor : Bᵒᵖ ⥤ Cat.{w,w} where
  obj X := Cat.of (D.Fiber X.unop)
  map f := (D.reindexFunctor f.unop).toCatHom
  map_id X := by
    apply Cat.ext
    exact D.reindexFunctor_id X.unop
  map_comp f g := by
    apply Cat.ext
    exact D.reindexFunctor_comp g.unop f.unop

abbrev pseudofunctor := D.indexedFunctor.toPseudofunctor'

abbrev Total := Pseudofunctor.CoGrothendieck D.pseudofunctor

abbrev projection : D.Total ⥤ B :=
  Pseudofunctor.CoGrothendieck.forget D.pseudofunctor

theorem projection_fibered : IsFibered D.projection := inferInstance

/-- The categorical Cartesian lift uses precisely doctrine substitution. -/
abbrev liftDomain {X Y : B} (φ : D.Fiber Y) (f : X ⟶ Y) : D.Total :=
  Pseudofunctor.CoGrothendieck.domainCartesianLift (F := D.pseudofunctor) φ f

abbrev lift {X Y : B} (φ : D.Fiber Y) (f : X ⟶ Y) :
    D.liftDomain φ f ⟶ (⟨Y,φ⟩ : D.Total) :=
  Pseudofunctor.CoGrothendieck.cartesianLift (F := D.pseudofunctor) φ f

theorem lift_fiber {X Y : B} (φ : D.Fiber Y) (f : X ⟶ Y) :
    (D.liftDomain φ f).fiber = D.reindex f φ := rfl

theorem lift_cartesian {X Y : B} (φ : D.Fiber Y) (f : X ⟶ Y) :
    IsStronglyCartesian D.projection f (D.lift φ f) :=
  Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift
    (F := D.pseudofunctor) φ f

/-- Total morphisms are exactly base maps satisfying the indexed entailment. -/
def totalHomEquiv (a b : D.Total) :
    (a ⟶ b) ≃ {f : a.base ⟶ b.base //
      (show D.Fiber a.base from a.fiber) ≤ D.reindex f b.fiber} where
  toFun arrow := ⟨arrow.base, by
    have inclusion : (show D.Fiber a.base from a.fiber) ⟶ D.reindex arrow.base b.fiber :=
      arrow.fiber
    exact inclusion.le⟩
  invFun arrow := ⟨arrow.val, by
    change (show D.Fiber a.base from a.fiber) ⟶ D.reindex arrow.val b.fiber
    exact homOfLE arrow.property⟩
  left_inv arrow := by
    refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl ?_
    exact @Subsingleton.elim
      ((show D.Fiber a.base from a.fiber) ⟶ D.reindex arrow.base b.fiber)
      inferInstance _ _
  right_inv arrow := by
    apply Subtype.ext
    rfl

end IndexedHeyting

/-- First-order predicate structure. Adjoints along every map strengthen the
simple quantification required along projections and diagonals. -/
structure FirstOrder extends IndexedHeyting.{u,v,w} B where
  existsAlong : ∀ {X Y : B}, (X ⟶ Y) → Fiber X → Fiber Y
  forallAlong : ∀ {X Y : B}, (X ⟶ Y) → Fiber X → Fiber Y
  exists_mono : ∀ {X Y : B} (f : X ⟶ Y), Monotone (existsAlong f)
  forall_mono : ∀ {X Y : B} (f : X ⟶ Y), Monotone (forallAlong f)
  exists_adj : ∀ {X Y : B} (f : X ⟶ Y), GaloisConnection (existsAlong f) (reindex f)
  forall_adj : ∀ {X Y : B} (f : X ⟶ Y), GaloisConnection (reindex f) (forallAlong f)
  frobenius : ∀ {X Y : B} (f : X ⟶ Y) (φ : Fiber X) (ψ : Fiber Y),
    existsAlong f (φ ⊓ reindex f ψ) = existsAlong f φ ⊓ ψ
  exists_baseChange : ∀ {P Q R S : B} (top : P ⟶ Q) (left : P ⟶ R)
      (right : Q ⟶ S) (bottom : R ⟶ S), IsPullback top left right bottom →
      ∀ φ : Fiber Q, reindex bottom (existsAlong right φ) =
        existsAlong left (reindex top φ)
  forall_baseChange : ∀ {P Q R S : B} (top : P ⟶ Q) (left : P ⟶ R)
      (right : Q ⟶ S) (bottom : R ⟶ S), IsPullback top left right bottom →
      ∀ φ : Fiber Q, reindex bottom (forallAlong right φ) =
        forallAlong left (reindex top φ)

namespace FirstOrder

variable {B} (D : FirstOrder.{u,v,w} B)

def existsFunctor {X Y : B} (f : X ⟶ Y) : D.Fiber X ⥤ D.Fiber Y :=
  (D.exists_mono f).functor

def forallFunctor {X Y : B} (f : X ⟶ Y) : D.Fiber X ⥤ D.Fiber Y :=
  (D.forall_mono f).functor

/-- A Galois connection gives the categorical hom bijection, retaining both
directions rather than only its unit or counit inequality. -/
private def orderHomEquiv {A : Type*} {E : Type*} [Preorder A] [Preorder E]
    {f : A → E} {g : E → A} (adj : GaloisConnection f g) (a : A) (e : E) :
    (f a ⟶ e) ≃ (a ⟶ g e) where
  toFun arrow := homOfLE ((adj a e).mp arrow.le)
  invFun arrow := homOfLE ((adj a e).mpr arrow.le)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

def existsAdjunction {X Y : B} (f : X ⟶ Y) :
    D.existsFunctor f ⊣ D.toIndexedHeyting.reindexFunctor f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := orderHomEquiv (D.exists_adj f)
      homEquiv_naturality_left_symm := by intros; apply Subsingleton.elim
      homEquiv_naturality_right := by intros; apply Subsingleton.elim }

def forallAdjunction {X Y : B} (f : X ⟶ Y) :
    D.toIndexedHeyting.reindexFunctor f ⊣ D.forallFunctor f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := orderHomEquiv (D.forall_adj f)
      homEquiv_naturality_left_symm := by intros; apply Subsingleton.elim
      homEquiv_naturality_right := by intros; apply Subsingleton.elim }

variable [CartesianMonoidalCategory B]

/-- Equality is the diagonal image of truth, in the actual product context. -/
def equality (X : B) : D.Fiber (X ⊗ X) :=
  D.existsAlong (CartesianMonoidalCategory.lift (𝟙 X) (𝟙 X)) ⊤

theorem equality_adj (X : B) (φ : D.Fiber X) (ψ : D.Fiber (X ⊗ X)) :
    D.existsAlong (CartesianMonoidalCategory.lift (𝟙 X) (𝟙 X)) φ ≤ ψ ↔
      φ ≤ D.reindex (CartesianMonoidalCategory.lift (𝟙 X) (𝟙 X)) ψ :=
  D.exists_adj _ φ ψ

theorem equality_frobenius (X : B) (φ : D.Fiber X) (ψ : D.Fiber (X ⊗ X)) :
    D.existsAlong (CartesianMonoidalCategory.lift (𝟙 X) (𝟙 X))
        (φ ⊓ D.reindex (CartesianMonoidalCategory.lift (𝟙 X) (𝟙 X)) ψ) =
      D.existsAlong (CartesianMonoidalCategory.lift (𝟙 X) (𝟙 X)) φ ⊓ ψ :=
  D.frobenius _ φ ψ

end FirstOrder

/-- A generic predicate uniquely classifies every fibre predicate. -/
structure GenericPredicate (D : IndexedHeyting.{u,v,w} B) where
  object : B
  truth : D.Fiber object
  characteristic : ∀ X, D.Fiber X → (X ⟶ object)
  classifies : ∀ X (φ : D.Fiber X), D.reindex (characteristic X φ) truth = φ
  unique : ∀ X (φ : D.Fiber X) (f : X ⟶ object),
    D.reindex f truth = φ → f = characteristic X φ

namespace GenericPredicate

variable {B} {D : IndexedHeyting.{u,v,w} B} (G : GenericPredicate B D)

/-- Substitution of predicates is actual composition of their characteristic maps. -/
theorem characteristic_reindex {X Y : B} (f : X ⟶ Y) (φ : D.Fiber Y) :
    G.characteristic X (D.reindex f φ) = f ≫ G.characteristic Y φ := by
  apply Eq.symm
  apply G.unique
  rw [D.reindex_comp, G.classifies]

/-- The characteristic-map bijection is earned from classification and uniqueness. -/
def characteristicEquiv (X : B) : (X ⟶ G.object) ≃ D.Fiber X where
  toFun f := D.reindex f G.truth
  invFun φ := G.characteristic X φ
  left_inv f := (G.unique X (D.reindex f G.truth) f rfl).symm
  right_inv φ := G.classifies X φ

end GenericPredicate

/-- Higher-order predicate structure adds a generic predicate on a CCC base.
The associated categorical fibration is the doctrine's actual total projection. -/
structure HigherOrder [CartesianMonoidalCategory B] [MonoidalClosed B]
    extends FirstOrder.{u,v,w} B where
  generic : GenericPredicate B toIndexedHeyting

end Mettapedia.CategoryTheory.PredicateDoctrine
