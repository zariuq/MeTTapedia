import Mettapedia.TypeTheory.IndexedGSOSOperational
import Mettapedia.CategoryTheory.CoalgebraMonadDistributive

/-!
# The actual free monad lifted to arbitrary behavior coalgebras

The operational fold supplies the structure on every original free carrier.
Its relabeling, unit and multiplication are actual coalgebra morphisms.
All compatibility fields in the reusable monad-lifting interface are proved
from the given natural GSOS law, rather than supplied as hypotheses. The
lifted categorical monad retains the original free-algebra adjunction's
carrier and substitution. This does not assert a cofree adjunction for an
arbitrary behavior functor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.IndexedGSOS.Operational

open _root_.CategoryTheory IndexedPolynomial

universe u

variable {Base : Type u} {Index : Base → Type u}
variable {P : IndexedPolynomial.{u, u, u, u} Base Index}
variable {B : Family Base Index ⥤ Family Base Index} (law : Law P B)

/-- The compatibility record is constructed from the actual operational
fold and theorems on complete terms. -/
noncomputable def lifting :
    Mettapedia.CategoryTheory.CoalgebraMonadDistributive.Lift B (FreeAdjunction.monad P) where
  structureMap object := coalgebra law object.str
  map_compatible {first second} mapping := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro term
    have inputs : ∀ base index value,
        second.str base index (mapping.f base index value) =
          B.map mapping.f base index (first.str base index value) := by
      intro base index value
      exact (congrArg (fun arrow => arrow base index value) mapping.h).symm
    exact (coalgebra_rename law first.str second.str mapping.f inputs base index term).symm
  unit_compatible object := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro value
    exact (coalgebra_pure law object.str value).symm
  multiplication_compatible object := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro term
    exact (coalgebra_join law object.str base index term).symm

noncomputable def liftObject (object : Endofunctor.Coalgebra B) : Endofunctor.Coalgebra B :=
  (lifting law).object object

noncomputable def liftMap {first second : Endofunctor.Coalgebra B} (mapping : first ⟶ second) :
    liftObject law first ⟶ liftObject law second :=
  (lifting law).map mapping

noncomputable def liftFunctor : Endofunctor.Coalgebra B ⥤ Endofunctor.Coalgebra B where
  obj := liftObject law
  map := liftMap law
  map_id object := by
    apply Endofunctor.Coalgebra.ext
    exact (FreeAdjunction.monad P).map_id object.V
  map_comp before after := by
    apply Endofunctor.Coalgebra.ext
    exact (FreeAdjunction.monad P).map_comp before.f after.f

noncomputable def liftUnit : 𝟭 (Endofunctor.Coalgebra B) ⟶ liftFunctor law where
  app object := (lifting law).unit object
  naturality {_ _} mapping := by
    apply Endofunctor.Coalgebra.ext
    exact (FreeAdjunction.monad P).η.naturality mapping.f

noncomputable def liftMultiplication : liftFunctor law ⋙ liftFunctor law ⟶ liftFunctor law where
  app object := (lifting law).multiplication object
  naturality {_ _} mapping := by
    apply Endofunctor.Coalgebra.ext
    exact (FreeAdjunction.monad P).μ.naturality mapping.f

/-- A genuine categorical lifting of the original adjunction-generated
free monad, with all behavior squares earned from the GSOS law. -/
noncomputable def liftedMonad : Monad (Endofunctor.Coalgebra B) where
  toFunctor := liftFunctor law
  η := liftUnit law
  μ := liftMultiplication law
  assoc object := by
    apply Endofunctor.Coalgebra.ext
    exact (FreeAdjunction.monad P).assoc object.V
  left_unit object := by
    apply Endofunctor.Coalgebra.ext
    exact (FreeAdjunction.monad P).left_unit object.V
  right_unit object := by
    apply Endofunctor.Coalgebra.ext
    exact (FreeAdjunction.monad P).right_unit object.V

/-- The underlying carrier and map functor is the original actual free
monad. The extra operational structure was constructed by the fold. -/
theorem forget_liftedFunctor :
    liftFunctor law ⋙ Endofunctor.Coalgebra.forget B =
      Endofunctor.Coalgebra.forget B ⋙ (FreeAdjunction.monad P).toFunctor := rfl

theorem lifted_unit_readout (object : Endofunctor.Coalgebra B)
    (base : Base) (index : Index base) (value : object.V base index) :
    ((liftedMonad law).η.app object).f base index value = Free.pure P value := rfl

theorem lifted_multiplication_readout (object : Endofunctor.Coalgebra B)
    (base : Base) (index : Index base) (term : P.Free (P.Free object.V) base index) :
    ((liftedMonad law).μ.app object).f base index term = Free.join P term := rfl

end Mettapedia.TypeTheory.IndexedGSOS.Operational
