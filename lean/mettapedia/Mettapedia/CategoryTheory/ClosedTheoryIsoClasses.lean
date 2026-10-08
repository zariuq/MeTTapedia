import Mettapedia.CategoryTheory.BicategoryIsoClasses
import Mettapedia.GSLT.Core.LambdaTheoryBicategory

/-!
# Closed theory maps up to natural isomorphism

Every supplied finite-limit cartesian closed theory remains an object. Maps
are actual finite-limit and canonical-exponential preserving functors,
identified precisely when their complete functors are naturally isomorphic.
No object or raw presentation is quotiented.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

open _root_.CategoryTheory
open Mettapedia.GSLT.Core

universe u k

namespace ClosedTheoryIsoClasses

def of (theory : LambdaTheory.{u,k}) : BicategoryIsoClasses LambdaTheory.{u,k} :=
  BicategoryIsoClasses.of theory

def classOf {source target : LambdaTheory.{u,k}} (mapping : LambdaTheoryMap source target) :
    of source ⟶ of target := BicategoryIsoClasses.classOf mapping

theorem classOf_equal_iff {source target : LambdaTheory.{u,k}}
    (first second : LambdaTheoryMap source target) :
    classOf first = classOf second ↔ Nonempty (first.functor ≅ second.functor) := by
  constructor
  · intro same
    obtain ⟨comparison⟩ := (show Nonempty (first ≅ second) from Quotient.exact same)
    exact ⟨⟨comparison.hom, comparison.inv, comparison.hom_inv_id, comparison.inv_hom_id⟩⟩
  · rintro ⟨comparison⟩
    exact Quotient.sound ⟨LambdaTheory.isoOfNatIso comparison⟩

theorem classOf_identity (source : LambdaTheory.{u,k}) :
    classOf (LambdaTheoryMap.id source) = 𝟙 (of source) := rfl

theorem classOf_compose {source middle target : LambdaTheory.{u,k}}
    (before : LambdaTheoryMap source middle) (after : LambdaTheoryMap middle target) :
    classOf (LambdaTheoryMap.comp after before) = classOf before ≫ classOf after := rfl

end ClosedTheoryIsoClasses

end Mettapedia.CategoryTheory
