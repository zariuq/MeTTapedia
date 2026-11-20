import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentContextInterchange
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunRearrangementDomain
import Mathlib.CategoryTheory.NatIso

/-!
# Context placement on the groupoid of licensed runs

The domain retains the local resource and query grade on every run used by
the comparison. Similarity and interchange generators map to actual placed
comparison cells. Free interpretation supplies identities, composition and
inversion without treating a raw certificate's grade as a trace invariant.

The two event functors agree after the length-preserving alignment of placed
positions. Thus arbitrary composed comparisons retain the original event
permutation, not just their endpoints or event count.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open Transport.RunRearrangement

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O]

noncomputable section

def placementGenerators (extra : Finset O) (start : State rules O) :
    Qualified (helperTransport levels O) (RunSafe (state := start) extra) ⥤q
      Groupoid (helperTransport levels O) (place extra start) where
  obj run := object (helperTransport levels O) (placeRun extra run.val run.property)
  map {first second} witness := match witness with
    | .inl similar => generator (helperTransport levels O)
        (.inl (placeSimilarity extra similar first.property second.property))
    | .inr interchange => interchangeCell extra interchange first.property second.property

def placementFunctor (extra : Finset O) (start : State rules O) :
    QualifiedGroupoid (T := helperTransport levels O) (start := start) (RunSafe extra) ⥤
      Groupoid (helperTransport levels O) (place extra start) :=
  Quiver.FreeGroupoid.lift (placementGenerators extra start)

theorem placement_generator (extra : Finset O) (start : State rules O)
    {first second : Qualified (helperTransport levels O) (RunSafe (state := start) extra)}
    (witness : Generator (helperTransport levels O) first.val second.val) :
    (placementFunctor extra start).map
      ((Quiver.FreeGroupoid.of (Qualified (helperTransport levels O) (RunSafe extra))).map witness) =
        (placementGenerators extra start).map witness :=
  Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec (placementGenerators extra start)) witness

theorem generator_event (extra : Finset O) (start : State rules O)
    {first second : Qualified (helperTransport levels O) (RunSafe (state := start) extra)}
    (witness : Generator (helperTransport levels O) first.val second.val)
    (event : Fin (placeRun extra first.val first.property).word.length) :
    (events (helperTransport levels O) ((placementGenerators extra start).map witness) event).val =
      (Generator.events (helperTransport levels O) witness
        (finCongr (placeRun_event_count extra first.val first.property) event)).val := by
  cases witness with
  | inl similar =>
      change ((placeSimilarity extra similar first.property second.property).events event).val = event.val
      rfl
  | inr interchange => exact interchange_event extra interchange first.property second.property event

def qualifiedEventObjects (extra : Finset O) (start : State rules O)
    (run : QualifiedGroupoid (T := helperTransport levels O) (start := start) (RunSafe extra)) : Core (Type) :=
  ⟨Fin run.as.val.word.length⟩

def eventAlignment (extra : Finset O) (start : State rules O)
    (run : QualifiedGroupoid (T := helperTransport levels O) (start := start) (RunSafe extra)) :
    ((placementFunctor extra start) ⋙ eventFunctor (helperTransport levels O) (place extra start)).obj run ≅
      qualifiedEventObjects extra start run :=
  Core.isoMk (finCongr (placeRun_event_count extra run.as.val run.as.property)).toIso

def alignedEvents (extra : Finset O) (start : State rules O) :
    QualifiedGroupoid (T := helperTransport levels O) (start := start) (RunSafe extra) ⥤ Core (Type) :=
  ((placementFunctor extra start) ⋙ eventFunctor (helperTransport levels O) (place extra start)).copyObj
    (qualifiedEventObjects extra start) (eventAlignment extra start)

def sourceEventGenerators (extra : Finset O) (start : State rules O) :
    Qualified (helperTransport levels O) (RunSafe (state := start) extra) ⥤q Core (Type) :=
  forgetGenerators (T := helperTransport levels O) (RunSafe extra) ⋙q eventGenerators (helperTransport levels O) start

theorem aligned_generators (extra : Finset O) (start : State rules O) :
    Quiver.FreeGroupoid.of (Qualified (helperTransport levels O) (RunSafe (state := start) extra)) ⋙q
      (alignedEvents (levels := levels) extra start).toPrefunctor = sourceEventGenerators (levels := levels) extra start := by
  refine Prefunctor.ext
    (F := Quiver.FreeGroupoid.of (Qualified (helperTransport levels O) (RunSafe (state := start) extra)) ⋙q
      (alignedEvents (levels := levels) extra start).toPrefunctor)
    (G := sourceEventGenerators (levels := levels) extra start) (fun _ => rfl) ?_
  intro first second witness
  change ((alignedEvents (levels := levels) extra start).map
      ((Quiver.FreeGroupoid.of (Qualified (helperTransport levels O) (RunSafe extra))).map witness)) =
    (sourceEventGenerators (levels := levels) extra start).map witness
  apply Core.hom_ext
  apply ConcreteCategory.hom_ext
  intro event
  apply Fin.ext
  change (events (helperTransport levels O)
    ((placementFunctor extra start).map
      ((Quiver.FreeGroupoid.of (Qualified (helperTransport levels O) (RunSafe extra))).map witness))
    (finCongr (placeRun_event_count extra first.val first.property).symm event)).val =
      (Generator.events (helperTransport levels O) witness event).val
  rw [placement_generator]
  exact generator_event extra start witness _

theorem aligned_events_equal (extra : Finset O) (start : State rules O) :
    alignedEvents (levels := levels) extra start =
      forgetFunctor (T := helperTransport levels O) (RunSafe (state := start) extra) ⋙ eventFunctor (helperTransport levels O) start := by
  have first := Quiver.FreeGroupoid.lift_unique (sourceEventGenerators (levels := levels) extra start)
    (alignedEvents (levels := levels) extra start) (aligned_generators (levels := levels) extra start)
  have second : forgetFunctor (T := helperTransport levels O) (RunSafe (state := start) extra) ⋙ eventFunctor (helperTransport levels O) start =
      Quiver.FreeGroupoid.lift (sourceEventGenerators (levels := levels) extra start) := by
    apply Quiver.FreeGroupoid.lift_unique
    rw [← Functor.toPrefunctor_comp, ← Prefunctor.comp_assoc]
    have forget := Quiver.FreeGroupoid.lift_spec
      (forgetGenerators (T := helperTransport levels O) (RunSafe (state := start) extra) ⋙q
        Quiver.FreeGroupoid.of (Object (helperTransport levels O) start))
    change Quiver.FreeGroupoid.of _ ⋙q (forgetFunctor (T := helperTransport levels O) (RunSafe (state := start) extra)).toPrefunctor = _ at forget
    rw [forget, Prefunctor.comp_assoc, eventFunctor_generators]
    rfl
  exact first.trans second.symm

theorem placement_events (extra : Finset O) (start : State rules O)
    {first second : Qualified (helperTransport levels O) (RunSafe (state := start) extra)}
    (cell : qualifiedObject first.val first.property ⟶ qualifiedObject second.val second.property)
    (event : Fin first.val.word.length) :
    (events (helperTransport levels O) ((placementFunctor extra start).map cell)
      (finCongr (placeRun_event_count extra first.val first.property).symm event)).val =
      (events (helperTransport levels O)
        ((forgetFunctor (T := helperTransport levels O) (RunSafe extra)).map cell) event).val := by
  have same := eq_of_heq (Functor.hcongr_hom (aligned_events_equal extra start) cell)
  exact congrArg (fun arrow : CoreHom (⟨Fin first.val.word.length⟩ : Core (Type))
    ⟨Fin second.val.word.length⟩ => (arrow.iso.toEquiv event).val) same

end

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement.placementFunctor
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement.aligned_events_equal
