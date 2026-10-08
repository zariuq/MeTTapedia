import Mettapedia.CategoryTheory.CoalgebraMonadDistributive
import Mathlib.CategoryTheory.Monad.Algebra
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Compatible algebras and a final behavior algebra

An actual monad lifting to endofunctor coalgebras gives a monad on that
coalgebra category. Its Eilenberg–Moore algebras retain both the original
monad algebra and its earned coalgebra compatibility. A final coalgebra
has a unique such action, obtained from its final map; the algebra laws
and finality in the compatible-algebra category follow from coalgebra
finality. Every final observation is therefore an algebra morphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.CategoryTheory.CoalgebraMonadBialgebra

open _root_.CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {B : C ⥤ C} {T : Monad C}
    (lifting : CoalgebraMonadDistributive.Lift B T)

/-- The original monad functor acts on actual behavior coalgebras. -/
def liftedFunctor : Endofunctor.Coalgebra B ⥤ Endofunctor.Coalgebra B where
  obj := lifting.object
  map := lifting.map
  map_id object := by
    apply Endofunctor.Coalgebra.ext
    exact T.map_id object.V
  map_comp first second := by
    apply Endofunctor.Coalgebra.ext
    exact T.map_comp first.f second.f

/-- The original unit is a natural coalgebra morphism. -/
def liftedUnit : 𝟭 (Endofunctor.Coalgebra B) ⟶ liftedFunctor lifting where
  app := lifting.unit
  naturality {_ _} mapping := by
    apply Endofunctor.Coalgebra.ext
    exact T.η.naturality mapping.f

/-- The original multiplication is a natural coalgebra morphism. -/
def liftedMultiplication : liftedFunctor lifting ⋙ liftedFunctor lifting ⟶
    liftedFunctor lifting where
  app := lifting.multiplication
  naturality {_ _} mapping := by
    apply Endofunctor.Coalgebra.ext
    exact T.μ.naturality mapping.f

/-- A genuine monad on behavior coalgebras, with all three laws earned. -/
def liftedMonad : Monad (Endofunctor.Coalgebra B) where
  toFunctor := liftedFunctor lifting
  η := liftedUnit lifting
  μ := liftedMultiplication lifting
  assoc object := by
    apply Endofunctor.Coalgebra.ext
    exact T.assoc object.V
  left_unit object := by
    apply Endofunctor.Coalgebra.ext
    exact T.left_unit object.V
  right_unit object := by
    apply Endofunctor.Coalgebra.ext
    exact T.right_unit object.V

/-- Compatible algebras use the actual Eilenberg–Moore category of the lifted monad. -/
abbrev CompatibleAlgebra := Monad.Algebra (liftedMonad lifting)

/-- Forgetting behavior retains the independently given original monad algebra. -/
def underlyingAlgebra (algebra : CompatibleAlgebra lifting) : Monad.Algebra T where
  A := algebra.A.V
  a := algebra.a.f
  unit := congrArg Endofunctor.Coalgebra.Hom.f algebra.unit
  assoc := congrArg Endofunctor.Coalgebra.Hom.f algebra.assoc

/-- The action's behavior compatibility is part of its actual coalgebra morphism. -/
theorem action_compatible (algebra : CompatibleAlgebra lifting) :
    lifting.structureMap algebra.A ≫ B.map algebra.a.f =
      algebra.a.f ≫ algebra.A.str :=
  algebra.a.h

/-- A compatible algebra map preserves the original monad algebra action. -/
def underlyingMap {first second : CompatibleAlgebra lifting} (mapping : first ⟶ second) :
    underlyingAlgebra lifting first ⟶ underlyingAlgebra lifting second where
  f := mapping.f.f
  h := congrArg Endofunctor.Coalgebra.Hom.f mapping.h

/-- The category retains both actual structure maps under forgetting. -/
def forgetBehaviour : CompatibleAlgebra lifting ⥤ Monad.Algebra T where
  obj := underlyingAlgebra lifting
  map := underlyingMap lifting
  map_id _ := rfl
  map_comp _ _ := rfl

variable {finalObject : Endofunctor.Coalgebra B} (finality : Limits.IsTerminal finalObject)

/-- The complete final behavior action is the unique actual lifted coalgebra map. -/
def finalAlgebra : CompatibleAlgebra lifting where
  A := finalObject
  a := finality.from (lifting.object finalObject)
  unit := finality.hom_ext _ _
  assoc := finality.hom_ext _ _

/-- Any compatible algebra's final observation preserves its whole algebra action. -/
def observation (algebra : CompatibleAlgebra lifting) :
    algebra ⟶ finalAlgebra lifting finality where
  f := finality.from algebra.A
  h := finality.hom_ext _ _

theorem observation_unique (algebra : CompatibleAlgebra lifting)
    (mapping : algebra ⟶ finalAlgebra lifting finality) :
    mapping = observation lifting finality algebra := by
  apply Monad.Algebra.Hom.ext
  exact finality.hom_ext _ _

/-- The independently constructed final behavior algebra is terminal among compatible algebras. -/
def isFinalAlgebra : Limits.IsTerminal (finalAlgebra lifting finality) :=
  Limits.IsTerminal.ofUniqueHom (observation lifting finality)
    (observation_unique lifting finality)

/-- Complete final observation commutes with the original monad action. -/
theorem observation_action (algebra : CompatibleAlgebra lifting) :
    T.map (finality.from algebra.A).f ≫
        (finality.from (lifting.object finalObject)).f =
      algebra.a.f ≫ (finality.from algebra.A).f :=
  congrArg Endofunctor.Coalgebra.Hom.f (observation lifting finality algebra).h

end Mettapedia.CategoryTheory.CoalgebraMonadBialgebra
