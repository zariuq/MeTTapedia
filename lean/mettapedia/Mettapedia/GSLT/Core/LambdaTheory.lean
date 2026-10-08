import Mettapedia.GSLT.Core.LambdaTheoryCategory
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Closed theories with equality

A theory is a category with chosen finite products, exponentials and finite
limits. Every cartesian closed category with pullbacks supplies such a theory;
the finite limits are derived from its terminal object and pullbacks. No
additional predicate or Frame data is required.

Theory maps preserve finite limits and the actual canonical exponential
comparison. The older Frame-enriched interface has an explicit forgetful
bridge into this categorical interface.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u₁ u₂ u₃

-- As for Mathlib's Cat, the bundle is used with independent explicit universe levels.
set_option linter.checkUnivs false in
/-- A cartesian closed category with equality interpreted by finite limits. -/
structure LambdaTheory where
  Obj : Type u
  instCategory : Category.{v} Obj
  instCartesianMonoidal : CartesianMonoidalCategory Obj
  instMonoidalClosed : MonoidalClosed Obj
  instHasFiniteLimits : HasFiniteLimits Obj

attribute [instance] LambdaTheory.instCategory LambdaTheory.instCartesianMonoidal
  LambdaTheory.instMonoidalClosed LambdaTheory.instHasFiniteLimits

namespace LambdaTheory

/-- Bundle an independently supplied cartesian closed, finitely complete category. -/
def ofCategory (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C]
    [MonoidalClosed C] [HasFiniteLimits C] : LambdaTheory.{u, v} where
  Obj := C
  instCategory := inferInstance
  instCartesianMonoidal := inferInstance
  instMonoidalClosed := inferInstance
  instHasFiniteLimits := inferInstance

/-- The source's cartesian closed categories with pullbacks are all included. -/
def ofCartesianClosedWithPullbacks (C : Type u) [Category.{v} C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] [HasPullbacks C] :
    LambdaTheory.{u, v} where
  Obj := C
  instCategory := inferInstance
  instCartesianMonoidal := inferInstance
  instMonoidalClosed := inferInstance
  instHasFiniteLimits := hasFiniteLimits_of_hasTerminal_and_pullbacks

end LambdaTheory

/-- A finite-limit-preserving functor whose canonical exponential comparison
is invertible. Products and the terminal object are already preserved by its
finite-limit field. The object universes of source and target may differ;
the hom universe is shared as required by the canonical comparison. -/
structure LambdaTheoryMap (source : LambdaTheory.{u₁, v})
    (target : LambdaTheory.{u₂, v}) where
  functor : source.Obj ⥤ target.Obj
  preservesFiniteLimits : PreservesFiniteLimits functor
  preservesExponentials : MonoidalClosedFunctor functor

attribute [instance] LambdaTheoryMap.preservesFiniteLimits
  LambdaTheoryMap.preservesExponentials

namespace LambdaTheoryMap

def id (source : LambdaTheory.{u, v}) : LambdaTheoryMap source source where
  functor := Functor.id source.Obj
  preservesFiniteLimits := inferInstance
  preservesExponentials :=
    cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts _ Adjunction.id

/-- The first route is followed by the second route. -/
def comp {source : LambdaTheory.{u₁, v}} {middle : LambdaTheory.{u₂, v}}
    {target : LambdaTheory.{u₃, v}}
    (second : LambdaTheoryMap middle target) (first : LambdaTheoryMap source middle) :
    LambdaTheoryMap source target where
  functor := first.functor ⋙ second.functor
  preservesFiniteLimits := comp_preservesFiniteLimits first.functor second.functor
  preservesExponentials :=
    Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence.closed_composition
      first.functor second.functor

@[ext] theorem ext {source : LambdaTheory.{u₁, v}} {target : LambdaTheory.{u₂, v}}
    {first second : LambdaTheoryMap source target}
    (same : first.functor = second.functor) : first = second := by
  cases first
  cases second
  cases same
  rfl

/-- An equivalence is a closed finite-limit map, with preservation derived
from its actual adjunctions. -/
noncomputable def ofEquivalence {source : LambdaTheory.{u₁, v}}
    {target : LambdaTheory.{u₂, v}}
    (equivalence : source.Obj ≌ target.Obj) : LambdaTheoryMap source target where
  functor := equivalence.functor
  preservesFiniteLimits := inferInstance
  preservesExponentials := cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts
    equivalence.functor equivalence.symm.toAdjunction

noncomputable def exponentialIso {source : LambdaTheory.{u₁, v}}
    {target : LambdaTheory.{u₂, v}}
    (route : LambdaTheoryMap source target) (A B : source.Obj) :
    route.functor.obj ((ihom A).obj B) ≅
      (ihom (route.functor.obj A)).obj (route.functor.obj B) :=
  asIso ((expComparison route.functor A).natTrans.app B)

theorem exponential_comp {source : LambdaTheory.{u₁, v}} {middle : LambdaTheory.{u₂, v}}
    {target : LambdaTheory.{u₃, v}}
    (second : LambdaTheoryMap middle target) (first : LambdaTheoryMap source middle)
    (A B : source.Obj) :
    (expComparison (comp second first).functor A).natTrans.app B =
      second.functor.map ((expComparison first.functor A).natTrans.app B) ≫
        (expComparison second.functor (first.functor.obj A)).natTrans.app
          (first.functor.obj B) :=
  Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence.exponential_composition
    first.functor second.functor A B

theorem exponential_id (source : LambdaTheory.{u, v}) (A B : source.Obj) :
    (expComparison (id source).functor A).natTrans.app B = 𝟙 ((ihom A).obj B) :=
  Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence.exponential_identity A B

end LambdaTheoryMap

/-- Forget only the legacy object's independent Frame enrichment. -/
def LambdaTheoryWithEquality.toLambdaTheory (source : LambdaTheoryWithEquality) :
    LambdaTheory where
  Obj := source.Obj
  instCategory := source.instCategory
  instCartesianMonoidal := source.instCartesianMonoidal
  instMonoidalClosed := source.instMonoidalClosed
  instHasFiniteLimits := source.instHasFiniteLimits

/-- The legacy closed map has exactly the same categorical functor after forgetting. -/
def LambdaTheoryMorphism.toLambdaTheoryMap {source target : LambdaTheoryWithEquality}
    (route : LambdaTheoryMorphism source target) :
    LambdaTheoryMap source.toLambdaTheory target.toLambdaTheory where
  functor := route.functor
  preservesFiniteLimits := route.preservesFiniteLimits
  preservesExponentials := route.preservesExponentials

end Mettapedia.GSLT.Core
