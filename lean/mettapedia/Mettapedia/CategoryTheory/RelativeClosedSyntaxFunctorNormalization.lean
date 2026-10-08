import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationObjects
import Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence

/-!
# Native choices and independent primitive meanings of a closed functor

The constructor-built object comparisons conjugate an actual functor into a
functor on the target's native object choices. Its complete natural
isomorphism, finite-limit preservation and canonical closedness are earned
from those comparisons.

The separate assignment retains the supplied images of base and fresh
objects. Each fresh arrow is the actual mapped source arrow, transported
through its independently formed header comparisons. No realization or
compatibility with the structural evaluator is supplied here.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (mapping : Object signature ⥤ D) [PreservesFiniteLimits mapping]
variable [MonoidalClosedFunctor mapping]

def normalizedFunctor : Object signature ⥤ D where
  obj source := (objectImage mapping source).value
  map {source target} arrow := (objectImage mapping source).comparison.inv ≫
    mapping.map arrow ≫ (objectImage mapping target).comparison.hom
  map_id source := by
    simp only [mapping.map_id, Category.id_comp, Iso.inv_hom_id]
  map_comp before after := by
    simp only [mapping.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

def comparison : mapping ≅ normalizedFunctor mapping :=
  NatIso.ofComponents (fun source => (objectImage mapping source).comparison) (by
    intro source target arrow
    change mapping.map arrow ≫ (objectImage mapping target).comparison.hom =
      (objectImage mapping source).comparison.hom ≫
        (objectImage mapping source).comparison.inv ≫ mapping.map arrow ≫
          (objectImage mapping target).comparison.hom
    simp only [Iso.hom_inv_id_assoc])

@[simp] theorem comparison_hom_app (source : Object signature) :
    (comparison mapping).hom.app source = (objectImage mapping source).comparison.hom := rfl

@[simp] theorem comparison_inv_app (source : Object signature) :
    (comparison mapping).inv.app source = (objectImage mapping source).comparison.inv := rfl

theorem normalized_map {source target : Object signature} (arrow : source ⟶ target) :
    (normalizedFunctor mapping).map arrow = (objectImage mapping source).comparison.inv ≫
      mapping.map arrow ≫ (objectImage mapping target).comparison.hom := rfl

instance normalized_preservesFiniteLimits : PreservesFiniteLimits (normalizedFunctor mapping) :=
  preservesFiniteLimits_of_natIso (comparison mapping)

instance normalized_closed : MonoidalClosedFunctor (normalizedFunctor mapping) :=
  CartesianClosedFunctorCoherence.closed_of_naturalIso (comparison mapping).symm

def namedObject (origin : symbols.ObjectName) : Object signature :=
  ⟨.name origin, ⟨.objectName origin⟩⟩

def headerSource (headers : HeaderFormation signature) (origin : symbols.ArrowName) :
    Object signature := ⟨signature.source origin, ⟨headers.source origin⟩⟩

def headerTarget (headers : HeaderFormation signature) (origin : symbols.ArrowName) :
    Object signature := ⟨signature.target origin, ⟨headers.target origin⟩⟩

def namedArrow (headers : HeaderFormation signature) (origin : symbols.ArrowName) :
    RawHom (headerSource headers origin) (headerTarget headers origin) :=
  ⟨.name origin, ⟨.arrowName origin (headers.source origin) (headers.target origin)⟩⟩

def assignment (headers : HeaderFormation signature) : Interpretation.Assignment C symbols D where
  base := baseFunctor signature ⋙ mapping
  object origin := mapping.obj (namedObject origin)
  arrow origin := ⟨(objectImage mapping (headerSource headers origin)).value,
    (objectImage mapping (headerTarget headers origin)).value,
    (normalizedFunctor mapping).map (classOf (namedArrow headers origin))⟩

theorem assignment_base (headers : HeaderFormation signature) :
    (assignment mapping headers).base = baseFunctor signature ⋙ mapping := rfl

theorem assignment_object (headers : HeaderFormation signature) (origin : symbols.ObjectName) :
    (assignment mapping headers).object origin = mapping.obj (namedObject origin) := rfl

theorem assignment_arrow (headers : HeaderFormation signature) (origin : symbols.ArrowName) :
    (assignment mapping headers).arrow origin =
      ⟨(objectImage mapping (headerSource headers origin)).value,
        (objectImage mapping (headerTarget headers origin)).value,
        (objectImage mapping (headerSource headers origin)).comparison.inv ≫
          mapping.map (classOf (namedArrow headers origin)) ≫
            (objectImage mapping (headerTarget headers origin)).comparison.hom⟩ := rfl

end Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization
