import Mettapedia.TypeTheory.MaterialSets.Hypersets.Finality
import Mettapedia.TypeTheory.MaterialSets.Hypersets.NoUniversalSet
import Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# The hypersets as a final coalgebra of the powerset functor

`powersetFunctor` is the covariant powerset functor on `Type v`, acting on maps by direct image.
Its coalgebras are graphs, and a morphism of coalgebras is exactly a bounded morphism of graphs
(`homEquiv`).

A graph with nodes in `Type u` is a coalgebra on `Type (u + 1)` (`graphCoalgebra`), and so is the
membership graph of hypersets (`hsetCoalgebra`). The finality of hypersets among small graphs is
the statement that there is exactly one coalgebra morphism from each small graph to the
hypersets, its decoration (`instUniqueGraphCoalgebraHom`), and that the only endomorphism of the
hypersets is the identity (`instUniqueHSetCoalgebraHom`).

**Control.** Finality holds among small graphs, not among all coalgebras of the powerset functor
on `Type (u + 1)`. The coalgebra `coveringCoalgebra` adds to the hypersets one node whose
children are all the hypersets. A morphism to the hypersets would send that node to a hyperset
containing every hyperset, and there is none (`isEmpty_coveringCoalgebra_hom`), so the
hypersets are not terminal among all coalgebras (`not_forall_nonempty_hom_hsetCoalgebra`).

No choice is used.

J. J. M. M. Rutten, *Universal coalgebra: a theory of systems*, Theoretical Computer Science
249, 2000; P. Aczel and N. Mendler, *A final coalgebra theorem*, Category Theory and Computer
Science, LNCS 389, 1989.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

open CategoryTheory

universe u v

/-- Morphisms of `Type v` are determined by their values. -/
theorem types_hom_ext {X Y : Type v} {f g : X ⟶ Y} (h : ∀ x, f x = g x) : f = g :=
  TypeCat.homEquiv.injective (funext h)

/-- The covariant powerset functor: a map acts by direct image. -/
def powersetFunctor : Type v ⥤ Type v where
  obj X := Set X
  map f := ↾(Set.image f)
  map_id _ := types_hom_ext fun s => Set.image_id s
  map_comp f g := types_hom_ext fun s => Set.image_comp g f s

theorem powersetFunctor_obj (X : Type v) : powersetFunctor.obj X = Set X :=
  rfl

namespace PowersetCoalgebra

/-- The children of a node of a coalgebra of the powerset functor: its structure set. -/
def children (V : Endofunctor.Coalgebra powersetFunctor.{v}) (a : V.V) : Set V.V :=
  V.str a

/-- The graph of a coalgebra of the powerset functor: an edge from `a` to each member of its
structure set. -/
def edge (V : Endofunctor.Coalgebra powersetFunctor.{v}) (a b : V.V) : Prop :=
  b ∈ children V a

/-- The morphism condition of coalgebras is the condition of bounded morphisms. -/
theorem hom_condition_iff {V₀ V₁ : Endofunctor.Coalgebra powersetFunctor.{v}}
    (f : V₀.V ⟶ V₁.V) :
    V₀.str ≫ powersetFunctor.map f = f ≫ V₁.str ↔ IsBoundedMorphism (edge V₀) (edge V₁) f := by
  rw [isBoundedMorphism_iff_image_eq]
  exact ⟨fun h a => ConcreteCategory.congr_hom h a,
    fun h => types_hom_ext h⟩

/-- Morphisms of coalgebras of the powerset functor are bounded morphisms of their graphs. -/
def homEquiv (V₀ V₁ : Endofunctor.Coalgebra powersetFunctor.{v}) :
    (V₀ ⟶ V₁) ≃ {f : V₀.V → V₁.V // IsBoundedMorphism (edge V₀) (edge V₁) f} where
  toFun φ := ⟨φ.f, (hom_condition_iff φ.f).mp φ.h⟩
  invFun f := ⟨↾f.1, (hom_condition_iff (↾f.1)).mpr f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem isBoundedMorphism_hom {V₀ V₁ : Endofunctor.Coalgebra powersetFunctor.{v}}
    (φ : V₀ ⟶ V₁) : IsBoundedMorphism (edge V₀) (edge V₁) φ.f :=
  (hom_condition_iff φ.f).mp φ.h

/-- A graph with nodes in `Type u`, as a coalgebra on `Type (u + 1)`. -/
def graphCoalgebra {α : Type u} (r : α → α → Prop) :
    Endofunctor.Coalgebra powersetFunctor.{u + 1} where
  V := ULift.{u + 1} α
  str := ↾fun a => ({b | r a.down b.down} : Set (ULift.{u + 1} α))

/-- The membership graph of hypersets, as a coalgebra. -/
def hsetCoalgebra : Endofunctor.Coalgebra powersetFunctor.{u + 1} where
  V := HSet.{u}
  str := ↾fun x => ({y | y ∈ x} : Set HSet.{u})

theorem edge_hsetCoalgebra : edge hsetCoalgebra.{u} = HSet.membershipGraph :=
  rfl

/-- The decoration of a small graph, as a coalgebra morphism. -/
def decorateHom {α : Type u} (r : α → α → Prop) : graphCoalgebra r ⟶ hsetCoalgebra.{u} :=
  (homEquiv _ _).symm ⟨fun a => HSet.decorate r a.down,
    ⟨fun _ _ h => (HSet.isBoundedMorphism_decorate r).map h, fun a y h => by
      obtain ⟨b, hb, rfl⟩ := (HSet.isBoundedMorphism_decorate r).lift h
      exact ⟨⟨b⟩, hb, rfl⟩⟩⟩

/-- Finality among small graphs: from each small graph there is exactly one coalgebra morphism
to the hypersets, its decoration. -/
instance instUniqueGraphCoalgebraHom {α : Type u} (r : α → α → Prop) :
    Unique (graphCoalgebra r ⟶ hsetCoalgebra.{u}) where
  default := decorateHom r
  uniq φ := by
    ext a
    have bounded : IsBoundedMorphism r HSet.membershipGraph fun b => φ.f ⟨b⟩ :=
      ⟨fun _ _ h => (isBoundedMorphism_hom φ).map h, fun a y h => by
        obtain ⟨b, hb, rfl⟩ := (isBoundedMorphism_hom φ).lift h
        exact ⟨b.down, hb, rfl⟩⟩
    exact congrFun bounded.eq_decorate a.down

/-- The only endomorphism of the hypersets is the identity. -/
instance instUniqueHSetCoalgebraHom : Unique (hsetCoalgebra.{u} ⟶ hsetCoalgebra.{u}) where
  default := 𝟙 _
  uniq φ := by
    ext x
    exact congrFun (HSet.isBoundedMorphism_self_iff.mp (isBoundedMorphism_hom φ)) x

/-! ## Control: finality is among small graphs -/

/-- The hypersets with one more node, `none`, whose children are all the hypersets. -/
def coveringCoalgebra : Endofunctor.Coalgebra powersetFunctor.{u + 1} where
  V := Option HSet.{u}
  str := ↾fun a => (match a with
    | none => Set.range some
    | some x => some '' {y | y ∈ x} : Set (Option HSet.{u}))

/-- No coalgebra morphism sends the covering coalgebra to the hypersets. -/
instance isEmpty_coveringCoalgebra_hom : IsEmpty (coveringCoalgebra.{u} ⟶ hsetCoalgebra.{u}) := by
  refine ⟨fun φ => ?_⟩
  have bounded := isBoundedMorphism_hom φ
  have restricted : IsBoundedMorphism HSet.membershipGraph HSet.membershipGraph
      fun x => φ.f (some x) :=
    ⟨fun x _ h => bounded.map (a := some x) ⟨_, h, rfl⟩, fun x y h => by
      obtain ⟨_, ⟨z, hz, rfl⟩, e⟩ := bounded.lift (a := some x) h
      exact ⟨z, hz, e⟩⟩
  have identity := HSet.isBoundedMorphism_self_iff.mp restricted
  refine HSet.not_exists_universal ⟨φ.f none, fun x => ?_⟩
  have edge : x = φ.f (some x) := (congrFun identity x).symm
  rw [edge]
  exact bounded.map (a := none) ⟨x, rfl⟩

/-- The hypersets are not terminal among all coalgebras of the powerset functor on
`Type (u + 1)`: some coalgebra has no morphism to them. -/
theorem not_forall_nonempty_hom_hsetCoalgebra :
    ¬ ∀ V : Endofunctor.Coalgebra powersetFunctor.{u + 1}, Nonempty (V ⟶ hsetCoalgebra.{u}) :=
  fun h => (h coveringCoalgebra).elim isEmptyElim

end PowersetCoalgebra

end Mettapedia.TypeTheory.MaterialSets.Hypersets
