import Mettapedia.CategoryTheory.RelativeClosedInternalCategoryPresentation
import Mettapedia.CategoryTheory.InternalCategoryPresentedDiagrams

/-!
# The internal category earned by the final authored presentation

Every declaration-preserving extension retains the actual edge, endpoints,
matching-pair and matching-triple objects. The generated equations supply
their seven local diagrams. The independently earned pullback limits then
construct an actual internal category in the extended theory, including the
native base-comparison extension.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedInternalCategory.NativeCategory

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory

universe k w z a

variable {C : Type k} [Category.{k} C] (vertex : C)
variable {D : Type w} [Category.{z} D] {nextSymbols : Symbols.{a}}
variable {next : Signature (C := D) (symbols := nextSymbols)}
variable (extension : SignatureMap (Presentation.signature vertex) next)

def raw {source target : Object (endpointSignature vertex)} (arrow : RawHom source target) :=
  extension.rawArrow ((Presentation.inclusion vertex).rawArrow arrow)

def object (source : Object (endpointSignature vertex)) : Object next :=
  extension.object ((Presentation.inclusion vertex).object source)

def vertexObject := object vertex extension (Endpoints.vertexObject vertex)
def edgeObject := object vertex extension (Endpoints.edgeObject vertex)
def source : RawHom (edgeObject vertex extension) (vertexObject vertex extension) :=
  raw vertex extension (Endpoints.source vertex)
def target : RawHom (edgeObject vertex extension) (vertexObject vertex extension) :=
  raw vertex extension (Endpoints.target vertex)
def unit : RawHom (vertexObject vertex extension) (edgeObject vertex extension) :=
  raw vertex extension (Endpoints.unit vertex)
def pairObject : Object next := PresentedPullback.object (target vertex extension) (source vertex extension)
def composition : RawHom (pairObject vertex extension) (edgeObject vertex extension) :=
  raw vertex extension (Endpoints.composition vertex)

def pair : @PullbackCone (Object next) (GeneratedCategory.category next)
    (edgeObject vertex extension) (edgeObject vertex extension) (vertexObject vertex extension)
    (classOf (target vertex extension)) (classOf (source vertex extension)) :=
  PullbackCone.mk (classOf (PresentedPullback.first (target vertex extension) (source vertex extension)))
    (classOf (PresentedPullback.second (target vertex extension) (source vertex extension)))
    (by simpa only [classOf_compose] using PresentedPullback.condition (target vertex extension) (source vertex extension))

def endpoints : InternalCategoryPresentedDiagrams.Endpoints (Object next) where
  vertex := vertexObject vertex extension
  edge := edgeObject vertex extension
  source := classOf (source vertex extension)
  target := classOf (target vertex extension)
  pair := pair vertex extension
  pairLimit := PresentedPullback.isLimit (target vertex extension) (source vertex extension)
  unit := classOf (unit vertex extension)
  composition := classOf (composition vertex extension)
  unitSource := by
    have law := congrArg (fun arrow => extension.functor.map
      ((Presentation.inclusion vertex).functor.map arrow)) (Endpoints.unit_source vertex)
    change classOf ((unit vertex extension).compose (source vertex extension)) =
      classOf (RawHom.identity (vertexObject vertex extension))
    exact law
  unitTarget := by
    have law := congrArg (fun arrow => extension.functor.map
      ((Presentation.inclusion vertex).functor.map arrow)) (Endpoints.unit_target vertex)
    change classOf ((unit vertex extension).compose (target vertex extension)) =
      classOf (RawHom.identity (vertexObject vertex extension))
    exact law
  compositionSource := by
    have law := congrArg (fun arrow => extension.functor.map
      ((Presentation.inclusion vertex).functor.map arrow)) (Endpoints.composition_source vertex)
    change classOf ((composition vertex extension).compose (source vertex extension)) =
      classOf ((PresentedPullback.first (target vertex extension) (source vertex extension)).compose
        (source vertex extension))
    exact law
  compositionTarget := by
    have law := congrArg (fun arrow => extension.functor.map
      ((Presentation.inclusion vertex).functor.map arrow)) (Endpoints.composition_target vertex)
    change classOf ((composition vertex extension).compose (target vertex extension)) =
      classOf ((PresentedPullback.second (target vertex extension) (source vertex extension)).compose
        (target vertex extension))
    exact law

def triples : InternalCategoryPresentedDiagrams.TripleCone (endpoints vertex extension) :=
  PullbackCone.mk (classOf (raw vertex extension (Endpoints.initialPair vertex)))
    (classOf (raw vertex extension (Endpoints.tripleLast vertex))) (by
      have law := congrArg (fun arrow => extension.functor.map
        ((Presentation.inclusion vertex).functor.map arrow))
        (PresentedPullback.condition ((Endpoints.second vertex).compose (Endpoints.target vertex)) (Endpoints.source vertex))
      exact law)

def tripleLimit : IsLimit (triples vertex extension) :=
  PresentedPullback.isLimit
    ((PresentedPullback.second (target vertex extension) (source vertex extension)).compose (target vertex extension))
    (source vertex extension)

theorem mapped_matching {stage : Object (endpointSignature vertex)}
    (first second : RawHom stage (Endpoints.edgeObject vertex))
    (matching : classOf (first.compose (Endpoints.target vertex)) =
      classOf (second.compose (Endpoints.source vertex))) :
    classOf (raw vertex extension first) ≫ (endpoints vertex extension).target =
      classOf (raw vertex extension second) ≫ (endpoints vertex extension).source :=
  congrArg (fun arrow => extension.functor.map ((Presentation.inclusion vertex).functor.map arrow)) matching

theorem pair_lift_read {stage : Object (endpointSignature vertex)}
    (first second : RawHom stage (Endpoints.edgeObject vertex))
    (matching : classOf (first.compose (Endpoints.target vertex)) =
      classOf (second.compose (Endpoints.source vertex))) :
    InternalCategoryPresentedDiagrams.pairLift (endpoints vertex extension)
      (classOf (raw vertex extension first)) (classOf (raw vertex extension second))
      (by
        have law := congrArg (fun arrow => extension.functor.map
          ((Presentation.inclusion vertex).functor.map arrow)) matching
        exact law) =
      classOf (raw vertex extension (PresentedPullback.lift (Endpoints.target vertex) (Endpoints.source vertex)
        first second matching)) := by
  apply PullbackCone.IsLimit.hom_ext (endpoints vertex extension).pairLimit
  · rw [InternalCategoryPresentedDiagrams.pairLift, PullbackCone.IsLimit.lift_fst]
    exact (congrArg (fun arrow => extension.functor.map
      ((Presentation.inclusion vertex).functor.map arrow))
      (PresentedPullback.lift_first (Endpoints.target vertex) (Endpoints.source vertex) first second matching)).symm
  · rw [InternalCategoryPresentedDiagrams.pairLift, PullbackCone.IsLimit.lift_snd]
    exact (congrArg (fun arrow => extension.functor.map
      ((Presentation.inclusion vertex).functor.map arrow))
      (PresentedPullback.lift_second (Endpoints.target vertex) (Endpoints.source vertex) first second matching)).symm

theorem laws : InternalCategoryPresentedDiagrams.Laws (endpoints vertex extension) (triples vertex extension) where
  leftUnit := by
    have law := congrArg extension.functor.map (Presentation.declared_law vertex (ULift.up Presentation.Law.leftUnit))
    have matching : classOf (((Endpoints.source vertex).compose (Endpoints.unit vertex)).compose (Endpoints.target vertex)) =
        classOf ((RawHom.identity (Endpoints.edgeObject vertex)).compose (Endpoints.source vertex)) := by
      have original := Endpoints.unit_target vertex
      simpa only [classOf_compose, classOf_identity, Category.assoc, Category.comp_id, Category.id_comp] using
        congrArg (fun arrow : Endpoints.vertexObject vertex ⟶ Endpoints.vertexObject vertex =>
          (classOf (Endpoints.source vertex) : Endpoints.edgeObject vertex ⟶ Endpoints.vertexObject vertex) ≫ arrow) original
    have lift := pair_lift_read vertex extension
      ((Endpoints.source vertex).compose (Endpoints.unit vertex)) (RawHom.identity (Endpoints.edgeObject vertex)) matching
    change InternalCategoryPresentedDiagrams.pairLift (endpoints vertex extension)
        (classOf (raw vertex extension ((Endpoints.source vertex).compose (Endpoints.unit vertex))))
        (classOf (raw vertex extension (RawHom.identity (Endpoints.edgeObject vertex))))
        (mapped_matching vertex extension _ _ matching) ≫
        classOf (raw vertex extension (Endpoints.composition vertex)) =
      classOf (raw vertex extension (RawHom.identity (Endpoints.edgeObject vertex)))
    rw [lift]
    exact law
  rightUnit := by
    have law := congrArg extension.functor.map (Presentation.declared_law vertex (ULift.up Presentation.Law.rightUnit))
    have matching : classOf ((RawHom.identity (Endpoints.edgeObject vertex)).compose (Endpoints.target vertex)) =
        classOf (((Endpoints.target vertex).compose (Endpoints.unit vertex)).compose (Endpoints.source vertex)) := by
      have original := Endpoints.unit_source vertex
      simpa only [classOf_compose, classOf_identity, Category.assoc, Category.comp_id, Category.id_comp] using
        (congrArg (fun arrow : Endpoints.vertexObject vertex ⟶ Endpoints.vertexObject vertex =>
          (classOf (Endpoints.target vertex) : Endpoints.edgeObject vertex ⟶ Endpoints.vertexObject vertex) ≫ arrow) original).symm
    have lift := pair_lift_read vertex extension
      (RawHom.identity (Endpoints.edgeObject vertex)) ((Endpoints.target vertex).compose (Endpoints.unit vertex)) matching
    change InternalCategoryPresentedDiagrams.pairLift (endpoints vertex extension)
        (classOf (raw vertex extension (RawHom.identity (Endpoints.edgeObject vertex))))
        (classOf (raw vertex extension ((Endpoints.target vertex).compose (Endpoints.unit vertex))))
        (mapped_matching vertex extension _ _ matching) ≫
        classOf (raw vertex extension (Endpoints.composition vertex)) =
      classOf (raw vertex extension (RawHom.identity (Endpoints.edgeObject vertex)))
    rw [lift]
    exact law
  associativity := by
    have law := congrArg extension.functor.map (Presentation.declared_law vertex (ULift.up Presentation.Law.associativity))
    have inner := pair_lift_read vertex extension (Endpoints.tripleMiddle vertex) (Endpoints.tripleLast vertex)
      (Endpoints.triple_second_matching vertex)
    have left := pair_lift_read vertex extension (Endpoints.composedFirst vertex) (Endpoints.tripleLast vertex)
      (Endpoints.composed_first_matching vertex)
    have right := pair_lift_read vertex extension (Endpoints.tripleFirst vertex) (Endpoints.composedLast vertex)
      (Endpoints.composed_last_matching vertex)
    have firstMatch := mapped_matching vertex extension _ _ (Endpoints.triple_first_matching vertex)
    have secondMatch := mapped_matching vertex extension _ _ (Endpoints.triple_second_matching vertex)
    have leftMatch := mapped_matching vertex extension _ _ (Endpoints.composed_first_matching vertex)
    have rightMatch := mapped_matching vertex extension _ _ (Endpoints.composed_last_matching vertex)
    change InternalCategoryPresentedDiagrams.compose (endpoints vertex extension)
        (classOf (raw vertex extension (Endpoints.composedFirst vertex)))
        (classOf (raw vertex extension (Endpoints.tripleLast vertex))) leftMatch =
      InternalCategoryPresentedDiagrams.compose (endpoints vertex extension)
        (classOf (raw vertex extension (Endpoints.tripleFirst vertex)))
        (InternalCategoryPresentedDiagrams.compose (endpoints vertex extension)
          (classOf (raw vertex extension (Endpoints.tripleMiddle vertex)))
          (classOf (raw vertex extension (Endpoints.tripleLast vertex))) secondMatch)
        (by rw [InternalCategoryPresentedDiagrams.compose_source]; exact firstMatch)
    have middleRead : InternalCategoryPresentedDiagrams.compose (endpoints vertex extension)
        (classOf (raw vertex extension (Endpoints.tripleMiddle vertex)))
        (classOf (raw vertex extension (Endpoints.tripleLast vertex))) secondMatch =
      classOf (raw vertex extension (Endpoints.composedLast vertex)) := by
      rw [InternalCategoryPresentedDiagrams.compose, inner]
      rfl
    have rightChange := InternalCategoryPresentedDiagrams.compose_congr (endpoints vertex extension)
      (rfl : classOf (raw vertex extension (Endpoints.tripleFirst vertex)) =
        classOf (raw vertex extension (Endpoints.tripleFirst vertex))) middleRead
      (by rw [InternalCategoryPresentedDiagrams.compose_source]; exact firstMatch) rightMatch
    have leftRead : InternalCategoryPresentedDiagrams.compose (endpoints vertex extension)
        (classOf (raw vertex extension (Endpoints.composedFirst vertex)))
        (classOf (raw vertex extension (Endpoints.tripleLast vertex))) leftMatch =
      classOf (raw vertex extension (Presentation.associateLeft vertex)) := by
      rw [InternalCategoryPresentedDiagrams.compose, left]
      rfl
    have rightRead : InternalCategoryPresentedDiagrams.compose (endpoints vertex extension)
        (classOf (raw vertex extension (Endpoints.tripleFirst vertex)))
        (classOf (raw vertex extension (Endpoints.composedLast vertex))) rightMatch =
      classOf (raw vertex extension (Presentation.associateRight vertex)) := by
      rw [InternalCategoryPresentedDiagrams.compose, right]
      rfl
    exact leftRead.trans (law.trans (rightChange.trans rightRead).symm)

def category : InternalCategory (Object next) :=
  InternalCategoryPresentedDiagrams.category (endpoints vertex extension) (triples vertex extension)
    (tripleLimit vertex extension) (laws vertex extension)

variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]

def nativeCategory : InternalCategory (Object (Presentation.nativeSignature vertex)) :=
  category vertex (Presentation.nativeInclusion vertex)

end Mettapedia.CategoryTheory.RelativeClosedInternalCategory.NativeCategory
