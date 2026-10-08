import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# A monad lifting and the cofree distributive law

An actual lifting of a monad to endofunctor coalgebras determines a
distributive law over the cofree comonad. The component is obtained by
transposing the mapped cofree counit. Its four Beck equations follow from
cofree uniqueness and the coalgebra compatibility of the lifted unit and
multiplication. The lifting is recovered by the one-step cofree readout.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.CategoryTheory.CoalgebraMonadDistributive

open _root_.CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] (B : C ⥤ C) (T : Monad C)

/-- Local structure and compatibility data for an actual monad lifting.
The carrier, maps, unit and multiplication are those of the supplied monad. -/
structure Lift where
  structureMap : (object : Endofunctor.Coalgebra B) →
    T.obj object.V ⟶ B.obj (T.obj object.V)
  map_compatible : ∀ {first second : Endofunctor.Coalgebra B} (mapping : first ⟶ second),
    structureMap first ≫ B.map (T.map mapping.f) = T.map mapping.f ≫ structureMap second
  unit_compatible : ∀ object : Endofunctor.Coalgebra B,
    object.str ≫ B.map (T.η.app object.V) = T.η.app object.V ≫ structureMap object
  multiplication_compatible : ∀ object : Endofunctor.Coalgebra B,
    structureMap { V := T.obj object.V, str := structureMap object } ≫
      B.map (T.μ.app object.V) = T.μ.app object.V ≫ structureMap object

namespace Lift

variable {B T} (lifting : Lift B T)

/-- Equip the actual monad carrier with the independently supplied lifted behavior. -/
abbrev object (coalgebra : Endofunctor.Coalgebra B) : Endofunctor.Coalgebra B where
  V := T.obj coalgebra.V
  str := lifting.structureMap coalgebra

/-- The original monad map, now carrying its earned coalgebra square. -/
abbrev map {first second : Endofunctor.Coalgebra B} (mapping : first ⟶ second) :
    lifting.object first ⟶ lifting.object second where
  f := T.map mapping.f
  h := lifting.map_compatible mapping

/-- The original unit, with the supplied local compatibility proof. -/
abbrev unit (coalgebra : Endofunctor.Coalgebra B) : coalgebra ⟶ lifting.object coalgebra where
  f := T.η.app coalgebra.V
  h := lifting.unit_compatible coalgebra

/-- The original multiplication is a genuine coalgebra morphism. -/
abbrev multiplication (coalgebra : Endofunctor.Coalgebra B) :
    lifting.object (lifting.object coalgebra) ⟶ lifting.object coalgebra where
  f := T.μ.app coalgebra.V
  h := lifting.multiplication_compatible coalgebra

end Lift

variable {B T} (lifting : Lift B T)
    (cofree : C ⥤ Endofunctor.Coalgebra B)
    (adjunction : Endofunctor.Coalgebra.forget B ⊣ cofree)

/-- Transpose the mapped counit through the actual cofree adjunction. -/
def componentCoalgebra (X : C) : lifting.object (cofree.obj X) ⟶ cofree.obj (T.obj X) :=
  adjunction.homEquiv _ _ (T.map (adjunction.counit.app X))

theorem counit_natural {X Y : C} (mapping : X ⟶ Y) :
    (cofree.map mapping).f ≫ adjunction.counit.app Y = adjunction.counit.app X ≫ mapping :=
  adjunction.counit.naturality mapping

theorem unit_counit (object : Endofunctor.Coalgebra B) :
    (adjunction.unit.app object).f ≫ adjunction.counit.app object.V = 𝟙 object.V :=
  adjunction.left_triangle_components object

theorem unit_structure (object : Endofunctor.Coalgebra B) :
    (adjunction.unit.app object).f ≫ (cofree.obj object.V).str =
      object.str ≫ B.map (adjunction.unit.app object).f :=
  (adjunction.unit.app object).h.symm

theorem component_counit (X : C) :
    (componentCoalgebra lifting cofree adjunction X).f ≫ adjunction.counit.app (T.obj X) =
      T.map (adjunction.counit.app X) := by
  change (adjunction.homEquiv _ _).symm (componentCoalgebra lifting cofree adjunction X) = _
  exact (adjunction.homEquiv _ _).symm_apply_apply _

/-- Cofree maps are equal once their actual counit readings agree. -/
theorem cofree_ext {source : Endofunctor.Coalgebra B} {X : C}
    (first second : source ⟶ cofree.obj X)
    (readings : first.f ≫ adjunction.counit.app X =
      second.f ≫ adjunction.counit.app X) : first = second := by
  apply (adjunction.homEquiv _ _).symm.injective
  exact readings

theorem component_natural {X Y : C} (mapping : X ⟶ Y) :
    lifting.map (cofree.map mapping) ≫ componentCoalgebra lifting cofree adjunction Y =
      componentCoalgebra lifting cofree adjunction X ≫ cofree.map (T.map mapping) := by
  apply cofree_ext cofree adjunction
  simp only [Endofunctor.Coalgebra.comp_f, Category.assoc]
  change T.map ((cofree.map mapping).f) ≫
      (componentCoalgebra lifting cofree adjunction Y).f ≫ adjunction.counit.app (T.obj Y) =
    (componentCoalgebra lifting cofree adjunction X).f ≫
      (cofree.map (T.map mapping)).f ≫ adjunction.counit.app (T.obj Y)
  rw [component_counit, counit_natural, ← Category.assoc, component_counit]
  rw [← T.map_comp, ← T.map_comp]
  exact congrArg T.map (counit_natural cofree adjunction mapping)

/-- The genuine natural transformation `T D ⟶ D T`. -/
def distributive : adjunction.toComonad.toFunctor ⋙ T.toFunctor ⟶
    T.toFunctor ⋙ adjunction.toComonad.toFunctor where
  app X := (componentCoalgebra lifting cofree adjunction X).f
  naturality {_ _} mapping := congrArg Endofunctor.Coalgebra.Hom.f
    (component_natural lifting cofree adjunction mapping)

theorem unit_coalgebra (X : C) :
    lifting.unit (cofree.obj X) ≫ componentCoalgebra lifting cofree adjunction X =
      cofree.map (T.η.app X) := by
  apply cofree_ext cofree adjunction
  simp only [Endofunctor.Coalgebra.comp_f, Category.assoc]
  change T.η.app (cofree.obj X).V ≫
      (componentCoalgebra lifting cofree adjunction X).f ≫ adjunction.counit.app (T.obj X) =
    (cofree.map (T.η.app X)).f ≫ adjunction.counit.app (T.obj X)
  rw [component_counit, counit_natural]
  exact (T.η.naturality (adjunction.counit.app X)).symm

theorem multiplication_coalgebra (X : C) :
    lifting.multiplication (cofree.obj X) ≫ componentCoalgebra lifting cofree adjunction X =
      lifting.map (componentCoalgebra lifting cofree adjunction X) ≫
        componentCoalgebra lifting cofree adjunction (T.obj X) ≫ cofree.map (T.μ.app X) := by
  apply cofree_ext cofree adjunction
  simp only [Endofunctor.Coalgebra.comp_f, Category.assoc]
  change T.μ.app (cofree.obj X).V ≫
      (componentCoalgebra lifting cofree adjunction X).f ≫ adjunction.counit.app (T.obj X) =
    T.map (componentCoalgebra lifting cofree adjunction X).f ≫
      (componentCoalgebra lifting cofree adjunction (T.obj X)).f ≫
      (cofree.map (T.μ.app X)).f ≫ adjunction.counit.app (T.obj X)
  rw [component_counit, counit_natural]
  change T.μ.app (cofree.obj X).V ≫ T.map (adjunction.counit.app X) =
    T.map (componentCoalgebra lifting cofree adjunction X).f ≫
      (componentCoalgebra lifting cofree adjunction (T.obj X)).f ≫
        adjunction.counit.app (T.obj (T.obj X)) ≫ T.μ.app X
  rw [← Category.assoc (componentCoalgebra lifting cofree adjunction (T.obj X)).f
      (adjunction.counit.app (T.obj (T.obj X))) (T.μ.app X),
    component_counit, ← Category.assoc, ← T.map_comp, component_counit]
  exact (T.μ.naturality (adjunction.counit.app X)).symm

theorem duplication_coalgebra (X : C) :
    componentCoalgebra lifting cofree adjunction X ≫ adjunction.unit.app (cofree.obj (T.obj X)) =
      lifting.map (adjunction.unit.app (cofree.obj X)) ≫
        componentCoalgebra lifting cofree adjunction ((cofree.obj X).V) ≫
          cofree.map (componentCoalgebra lifting cofree adjunction X).f := by
  apply cofree_ext cofree adjunction
  simp only [Endofunctor.Coalgebra.comp_f, Category.assoc]
  change (componentCoalgebra lifting cofree adjunction X).f ≫
      (adjunction.unit.app (cofree.obj (T.obj X))).f ≫
      adjunction.counit.app (cofree.obj (T.obj X)).V =
    T.map (adjunction.unit.app (cofree.obj X)).f ≫
      (componentCoalgebra lifting cofree adjunction (cofree.obj X).V).f ≫
      (cofree.map (componentCoalgebra lifting cofree adjunction X).f).f ≫
      adjunction.counit.app (cofree.obj (T.obj X)).V
  rw [unit_counit, Category.comp_id, counit_natural,
    ← Category.assoc (componentCoalgebra lifting cofree adjunction (cofree.obj X).V).f
      (adjunction.counit.app (T.obj (cofree.obj X).V))
      (componentCoalgebra lifting cofree adjunction X).f,
    component_counit, ← Category.assoc, ← T.map_comp, unit_counit]
  exact (Category.id_comp _).symm.trans
    (congrArg (fun arrow => arrow ≫ (componentCoalgebra lifting cofree adjunction X).f)
      (T.map_id (cofree.obj X).V)).symm

/-- Beck's monad-unit equation, derived from the actual lifted unit. -/
theorem beck_unit (X : C) :
    T.η.app (adjunction.toComonad.obj X) ≫ (distributive lifting cofree adjunction).app X =
      adjunction.toComonad.map (T.η.app X) :=
  congrArg Endofunctor.Coalgebra.Hom.f (unit_coalgebra lifting cofree adjunction X)

/-- Beck's monad-multiplication equation, derived from the actual lifted multiplication. -/
theorem beck_multiplication (X : C) :
    T.μ.app (adjunction.toComonad.obj X) ≫ (distributive lifting cofree adjunction).app X =
      T.map ((distributive lifting cofree adjunction).app X) ≫
        (distributive lifting cofree adjunction).app (T.obj X) ≫
          adjunction.toComonad.map (T.μ.app X) :=
  congrArg Endofunctor.Coalgebra.Hom.f (multiplication_coalgebra lifting cofree adjunction X)

/-- Beck's comonad-counit equation is the earned transpose computation. -/
theorem beck_counit (X : C) :
    (distributive lifting cofree adjunction).app X ≫ adjunction.toComonad.ε.app (T.obj X) =
      T.map (adjunction.toComonad.ε.app X) :=
  component_counit lifting cofree adjunction X

/-- Beck's comonad-comultiplication equation is earned by cofree uniqueness. -/
theorem beck_comultiplication (X : C) :
    (distributive lifting cofree adjunction).app X ≫ adjunction.toComonad.δ.app (T.obj X) =
      T.map (adjunction.toComonad.δ.app X) ≫
        (distributive lifting cofree adjunction).app (adjunction.toComonad.obj X) ≫
          adjunction.toComonad.map ((distributive lifting cofree adjunction).app X) :=
  congrArg Endofunctor.Coalgebra.Hom.f (duplication_coalgebra lifting cofree adjunction X)

theorem lifting_unit_recovered (object : Endofunctor.Coalgebra B) :
    lifting.map (adjunction.unit.app object) ≫
        componentCoalgebra lifting cofree adjunction object.V =
      adjunction.unit.app (lifting.object object) := by
  apply cofree_ext cofree adjunction
  simp only [Endofunctor.Coalgebra.comp_f, Category.assoc]
  change T.map (adjunction.unit.app object).f ≫
      (componentCoalgebra lifting cofree adjunction object.V).f ≫
      adjunction.counit.app (T.obj object.V) =
    (adjunction.unit.app (lifting.object object)).f ≫ adjunction.counit.app (T.obj object.V)
  rw [component_counit, ← T.map_comp, unit_counit]
  exact (T.map_id object.V).trans (unit_counit cofree adjunction (lifting.object object)).symm

/-- The complete original one-step lifted behavior is recovered from the distributive law. -/
theorem lifting_recovered (object : Endofunctor.Coalgebra B) :
    lifting.structureMap object =
      T.map (adjunction.unit.app object).f ≫
        (distributive lifting cofree adjunction).app object.V ≫
          (cofree.obj (T.obj object.V)).str ≫ B.map (adjunction.counit.app (T.obj object.V)) := by
  have recovered := congrArg Endofunctor.Coalgebra.Hom.f
    (lifting_unit_recovered lifting cofree adjunction object)
  change lifting.structureMap object =
    T.map (adjunction.unit.app object).f ≫
      (componentCoalgebra lifting cofree adjunction object.V).f ≫
        (cofree.obj (T.obj object.V)).str ≫ B.map (adjunction.counit.app (T.obj object.V))
  change T.map (adjunction.unit.app object).f ≫
    (componentCoalgebra lifting cofree adjunction object.V).f =
      (adjunction.unit.app (lifting.object object)).f at recovered
  symm
  calc
    _ = (T.map (adjunction.unit.app object).f ≫
      (componentCoalgebra lifting cofree adjunction object.V).f) ≫
        (cofree.obj (T.obj object.V)).str ≫ B.map (adjunction.counit.app (T.obj object.V)) := by
      rw [Category.assoc]
    _ = (adjunction.unit.app (lifting.object object)).f ≫
        (cofree.obj (T.obj object.V)).str ≫ B.map (adjunction.counit.app (T.obj object.V)) := by
      rw [recovered]
    _ = lifting.structureMap object ≫
        B.map (adjunction.unit.app (lifting.object object)).f ≫
          B.map (adjunction.counit.app (T.obj object.V)) := by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun arrow => arrow ≫ B.map (adjunction.counit.app (T.obj object.V)))
          (unit_structure cofree adjunction (lifting.object object))).trans (Category.assoc _ _ _))
    _ = lifting.structureMap object := by
      rw [← B.map_comp, unit_counit, B.map_id, Category.comp_id]

end Mettapedia.CategoryTheory.CoalgebraMonadDistributive
