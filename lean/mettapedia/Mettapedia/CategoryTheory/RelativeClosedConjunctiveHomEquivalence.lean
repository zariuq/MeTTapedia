import Mettapedia.CategoryTheory.ConjunctiveClosedTheory
import Mettapedia.CategoryTheory.RelativeClosedConjunctiveModelReadout

/-!
# The complete free conjunctive hom correspondence

Restriction remembers the entire weak closed base functor. Independently
supplied target operations give the inverse extension by the earned generated
interpretation. The local operation squares and base natural isomorphism
derive a compatible natural isomorphism on every generated object and arrow.
Both hom-set roundtrips follow; neither global interpretation nor a desired
universal property is supplied as model data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedConjunctive.HomEquivalence

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core
open RelativeClosedSyntax GeneratedCategory
open ConjunctiveClosedTheory

universe k

def freeObject (source : LambdaTheory.{k,k}) : ConjunctiveClosedTheory.{k} where
  closed := theory (C := source.Obj)
  operations := NativePredicates.operations (C := source.Obj)
  laws := NativePredicates.laws (C := source.Obj)

def unitMap (source : LambdaTheory.{k,k}) : LambdaTheoryMap source (freeObject source).closed :=
  baseMap (C := source.Obj)

variable (source : LambdaTheory.{k,k}) (target : ConjunctiveClosedTheory.{k})

def extension (base : LambdaTheoryMap source target.closed) : Map (freeObject source) target where
  declarations := ModelReadout.mapping base.functor target.operations target.laws
  finite := ModelReadout.diagram_lex base.functor target.operations target.laws
  closed := ModelReadout.diagram_closed base.functor target.operations target.laws

def restriction (mapping : Map (freeObject source) target) : LambdaTheoryMap source target.closed :=
  LambdaTheoryMap.comp mapping.underlying (unitMap source)

def extension_base (base : LambdaTheoryMap source target.closed) :
    (restriction source target (extension source target base)).functor ≅ base.functor :=
  ModelReadout.baseComparison base.functor target.operations target.laws

variable (base : LambdaTheoryMap source target.closed)
variable (mapping : Map (freeObject source) target)
variable (baseComparison : (restriction source target mapping).functor ≅ base.functor)

def completeComparison : MapIso mapping (extension source target base) where
  comparison := by
    letI : PreservesFiniteLimits mapping.declarations.functor := mapping.finite
    letI : MonoidalClosedFunctor mapping.declarations.functor := mapping.closed
    exact Universal.comparison base.functor target.operations mapping.declarations baseComparison target.laws
  proposition := by
    let : PreservesFiniteLimits mapping.declarations.functor := mapping.finite
    let : MonoidalClosedFunctor mapping.declarations.functor := mapping.closed
    have complete := Universal.comparison_admitted base.functor target.operations
      mapping.declarations baseComparison target.laws
    have localRead := complete.object (ULift.up (ULift.up ()))
    change (Universal.comparison base.functor target.operations mapping.declarations baseComparison target.laws).hom.app
      (NativePredicates.operations (C := source.Obj)).proposition =
        mapping.declarations.proposition.hom ≫
          eqToHom (ModelReadout.proposition_read base.functor target.operations target.laws).symm at localRead
    change (Universal.comparison base.functor target.operations mapping.declarations baseComparison target.laws).hom.app
      (NativePredicates.operations (C := source.Obj)).proposition ≫
        eqToHom (ModelReadout.proposition_read base.functor target.operations target.laws) =
          mapping.declarations.proposition.hom
    rw [localRead, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

def mapIsoOfRestriction {first second : Map (freeObject source) target}
    (comparison : (restriction source target first).functor ≅ (restriction source target second).functor) :
    MapIso first second :=
  (completeComparison source target (restriction source target second) first comparison).trans
    (completeComparison source target (restriction source target second) second (Iso.refl _)).symm

def restriction_comparison {first second : Map (freeObject source) target}
    (comparison : MapIso first second) :
    (restriction source target first).functor ≅ (restriction source target second).functor :=
  Functor.isoWhiskerLeft (unitMap source).functor comparison.comparison

def extension_comparison {first second : LambdaTheoryMap source target.closed}
    (comparison : first.functor ≅ second.functor) :
    MapIso (extension source target first) (extension source target second) :=
  mapIsoOfRestriction source target
    (extension_base source target first ≪≫ comparison ≪≫ (extension_base source target second).symm)

def restrict : (freeObject source ⟶ target) →
    (ClosedTheoryIsoClasses.of source ⟶ ClosedTheoryIsoClasses.of target.closed) :=
  Quotient.map (restriction source target)
    (fun first second comparison => by
      obtain ⟨comparison⟩ := (show Nonempty (MapIso first second) from comparison)
      exact ⟨LambdaTheory.isoOfNatIso (restriction_comparison source target comparison)⟩)

def extend : (ClosedTheoryIsoClasses.of source ⟶ ClosedTheoryIsoClasses.of target.closed) →
    (freeObject source ⟶ target) :=
  Quotient.map (extension source target)
    (fun first second comparison => by
      obtain ⟨comparison⟩ := (show Nonempty (first ≅ second) from comparison)
      exact ⟨extension_comparison source target
        ⟨comparison.hom, comparison.inv, comparison.hom_inv_id, comparison.inv_hom_id⟩⟩)

theorem restrict_classOf (mapping : Map (freeObject source) target) :
    restrict source target (ConjunctiveClosedTheory.classOf mapping) =
      ClosedTheoryIsoClasses.classOf (restriction source target mapping) := rfl

theorem extend_classOf (base : LambdaTheoryMap source target.closed) :
    extend source target (ClosedTheoryIsoClasses.classOf base) =
      ConjunctiveClosedTheory.classOf (extension source target base) := rfl

theorem restrict_extend
    (base : ClosedTheoryIsoClasses.of source ⟶ ClosedTheoryIsoClasses.of target.closed) :
    restrict source target (extend source target base) = base := by
  refine Quotient.inductionOn base fun base => ?_
  exact (ClosedTheoryIsoClasses.classOf_equal_iff _ _).mpr ⟨extension_base source target base⟩

theorem restrict_injective : Function.Injective (restrict source target) := by
  intro first second
  refine Quotient.inductionOn₂ first second fun first second same => ?_
  have comparison := (ClosedTheoryIsoClasses.classOf_equal_iff
    (restriction source target first) (restriction source target second)).mp same
  obtain ⟨comparison⟩ := comparison
  exact Quotient.sound ⟨mapIsoOfRestriction source target comparison⟩

theorem extend_restrict (mapping : freeObject source ⟶ target) :
    extend source target (restrict source target mapping) = mapping :=
  restrict_injective source target (restrict_extend source target (restrict source target mapping))

def homEquiv : (freeObject source ⟶ target) ≃
    (ClosedTheoryIsoClasses.of source ⟶ ClosedTheoryIsoClasses.of target.closed) where
  toFun := restrict source target
  invFun := extend source target
  left_inv := extend_restrict source target
  right_inv := restrict_extend source target

theorem restrict_as_base_composition (mapping : freeObject source ⟶ target) :
    restrict source target mapping =
      ClosedTheoryIsoClasses.classOf (unitMap source) ≫ ConjunctiveClosedTheory.forget.map mapping := by
  refine Quotient.inductionOn mapping fun mapping => ?_
  rfl

theorem restrict_postcompose {later : ConjunctiveClosedTheory.{k}}
    (before : freeObject source ⟶ target) (after : target ⟶ later) :
    restrict source later (before ≫ after) =
      restrict source target before ≫ ConjunctiveClosedTheory.forget.map after := by
  rw [restrict_as_base_composition, restrict_as_base_composition,
    ConjunctiveClosedTheory.forget.map_comp, Category.assoc]

end Mettapedia.CategoryTheory.RelativeClosedConjunctive.HomEquivalence
