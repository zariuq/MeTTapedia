import Mathlib.CategoryTheory.Grothendieck
import Mettapedia.GSLT.Core.IndexedOperational

/-!
# The path-indexed candidate for the GSLT-IL semantic waist

This module extracts the category-valued structure already forced by forward
operational translations.  A GSLT contributes its free category of finite,
proof-relevant execution paths.  A forward translation acts functorially on
that category, and the resulting functor into `Cat` has a standard
Grothendieck total category.

This is a theorem-level account of the functional indexed candidate for
GSLT-IL.  It does not assert that every authored route is functional, nor
that a Grothendieck category alone represents refinement cells or relational
routes.  Those are separate comparison obligations.
-/

namespace Mettapedia.GSLT.IndexedOperational

open CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite

universe uTerm uSourceTerm uTargetTerm

/-! ## Free execution-path categories -/

/-- A distinct category carrier for the terms of one GSLT. -/
def ExecutionObject (system : GSLT.{uTerm}) := system.Term

/-- The original term represented by an execution-category object. -/
def ExecutionObject.term {system : GSLT.{uTerm}} :
    ExecutionObject system -> system.Term :=
  id

/-- Finite proof-relevant executions are the homs of the free path category. -/
abbrev ExecutionPath (system : GSLT.{uTerm})
    (source target : ExecutionObject system) :=
  Route (fun left right : system.Term => PLift (system.Step left right))
    source target

instance executionCategory (system : GSLT.{uTerm}) :
    CategoryTheory.Category (ExecutionObject system) where
  Hom := ExecutionPath system
  id object := .refl object
  comp first second := first.append second
  id_comp morphism := Route.refl_append morphism
  comp_id morphism := Route.append_refl morphism
  assoc first second third := Route.append_assoc first second third

/-! ## Functorial transport of complete executions -/

namespace OperationalTranslation

/-- A forward operational translation maps every retained step of a finite
execution path. -/
def mapRoute {source : GSLT.{uSourceTerm}} {target : GSLT.{uTargetTerm}}
    (translation : OperationalTranslation source target) :
    {first last : source.Term} ->
      Route (fun left right => PLift (source.Step left right)) first last ->
      Route (fun left right => PLift (target.Step left right))
        (translation.mapTerm first) (translation.mapTerm last)
  | _, _, .refl object => .refl (translation.mapTerm object)
  | _, _, .cons step rest =>
      .cons ⟨translation.mapStep step.down⟩ (translation.mapRoute rest)

@[simp] theorem mapRoute_refl
    {source : GSLT.{uSourceTerm}} {target : GSLT.{uTargetTerm}}
    (translation : OperationalTranslation source target)
    (object : source.Term) :
    translation.mapRoute (.refl object) =
      .refl (translation.mapTerm object) :=
  rfl

@[simp] theorem mapRoute_append
    {source : GSLT.{uSourceTerm}} {target : GSLT.{uTargetTerm}}
    (translation : OperationalTranslation source target)
    {first middle last : source.Term}
    (earlier : Route (fun left right => PLift (source.Step left right)) first middle)
    (later : Route (fun left right => PLift (source.Step left right)) middle last) :
    translation.mapRoute (earlier.append later) =
      (translation.mapRoute earlier).append (translation.mapRoute later) := by
  induction earlier with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      simp [Route.append, mapRoute, inductionHypothesis]

@[simp] theorem mapRoute_length
    {source : GSLT.{uSourceTerm}} {target : GSLT.{uTargetTerm}}
    (translation : OperationalTranslation source target)
    {first last : source.Term}
    (route : Route (fun left right => PLift (source.Step left right)) first last) :
    (translation.mapRoute route).length = route.length := by
  induction route with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      simp [mapRoute, Route.length, inductionHypothesis]

@[simp] theorem mapRoute_id
    {system : GSLT.{uTerm}} {first last : system.Term}
    (route : Route (fun left right => PLift (system.Step left right)) first last) :
    (OperationalTranslation.id system).mapRoute route = route := by
  induction route with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      cases step
      simp only [mapRoute]
      congr

@[simp] theorem mapRoute_comp
    {first : GSLT.{uSourceTerm}} {middle : GSLT.{uTerm}}
    {last : GSLT.{uTargetTerm}}
    (earlier : OperationalTranslation first middle)
    (later : OperationalTranslation middle last)
    {source target : first.Term}
    (route : Route (fun left right => PLift (first.Step left right)) source target) :
    (earlier.comp later).mapRoute route =
      later.mapRoute (earlier.mapRoute route) := by
  induction route with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      cases step
      simp only [mapRoute]
      congr

/-- Every forward operational translation induces a functor between free
execution-path categories. -/
def pathFunctor {source : GSLT.{uTerm}} {target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target) :
    CategoryTheory.Functor (ExecutionObject source) (ExecutionObject target) where
  obj := translation.mapTerm
  map := translation.mapRoute
  map_id _ := rfl
  map_comp first second := translation.mapRoute_append first second

@[simp] theorem pathFunctor_obj
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target)
    (term : ExecutionObject source) :
    (translation.pathFunctor).obj term = translation.mapTerm term :=
  rfl

@[simp] theorem pathFunctor_map
    {source target : GSLT.{uTerm}}
    (translation : OperationalTranslation source target)
    {first last : ExecutionObject source}
    (route : first ⟶ last) :
    (translation.pathFunctor).map route = translation.mapRoute route :=
  rfl

end OperationalTranslation

/-! ## The category-valued index and its total category -/

/-- Functional operational transport is a category-valued indexed system of
proof-relevant execution paths. -/
def executionIndex :
    CategoryTheory.Functor OperationalTheory.{uTerm}
      CategoryTheory.Cat.{uTerm, uTerm} where
  obj system := CategoryTheory.Cat.of (ExecutionObject system.theory)
  map translation := translation.pathFunctor.toCatHom
  map_id system := by
    apply CategoryTheory.Cat.ext
    refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
    intro first last route
    exact heq_of_eq (OperationalTranslation.mapRoute_id route)
  map_comp earlier later := by
    apply CategoryTheory.Cat.ext
    refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
    intro first last route
    exact heq_of_eq (OperationalTranslation.mapRoute_comp earlier later route)

/-- The standard Grothendieck total category of a GSLT together with one of
its states.  A total morphism retains both the selected language translation
and the target-fibre execution following transport. -/
abbrev OperationalExecutionTotal :=
  CategoryTheory.Grothendieck executionIndex

/-- Embed a language/state pair as an object of the operational total
category. -/
def totalObject (system : OperationalTheory.{uTerm})
    (state : ExecutionObject system.theory) :
    OperationalExecutionTotal :=
  ⟨system, state⟩

end Mettapedia.GSLT.IndexedOperational
