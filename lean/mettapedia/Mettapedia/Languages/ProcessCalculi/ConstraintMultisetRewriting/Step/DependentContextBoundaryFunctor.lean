import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentContextWitnessBoundary

/-!
# Context placement preserves the complete boundary interpretation

Interpreting a licensed comparison after placement gives the same state
comparison as placing its original interpretation. The functor equality
uses the actual equalities of complete placed endpoints. The resulting map
equality is heterogeneous only because those endpoints are not definitionally
identical; it does not weaken the comparison to mere existence.
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

def statePlacement (extra : Finset O) : RunStateGroupoid.Object levels O ⥤ RunStateGroupoid.Object levels O where
  obj := place extra
  map := placeIso extra
  map_id state := placeIso_refl extra state
  map_comp first second := placeIso_trans extra first second

def sourceBoundaryGenerators (extra : Finset O) (start : State rules O) :
    Qualified (helperTransport levels O) (RunSafe (state := start) extra) ⥤q RunStateGroupoid.Object levels O where
  obj run := place extra run.val.last
  map witness := placeIso extra ((RunStateGroupoid.endpointGenerators levels O start).map witness)

theorem generators_boundary (extra : Finset O) (start : State rules O) :
    placementGenerators (levels := levels) extra start ⋙q
        (RunStateGroupoid.endpointFunctor levels O (place extra start)).toPrefunctor =
      sourceBoundaryGenerators (levels := levels) extra start := by
  refine Prefunctor.ext'
    (F := placementGenerators (levels := levels) extra start ⋙q
      (RunStateGroupoid.endpointFunctor levels O (place extra start)).toPrefunctor)
    (G := sourceBoundaryGenerators (levels := levels) extra start)
    (fun run => placeRun_last extra run.val run.property) ?_
  intro first second witness
  apply eq_of_heq
  have maps : HEq
      (RunStateGroupoid.endpointMap levels O ((placementGenerators extra start).map witness))
      ((sourceBoundaryGenerators (levels := levels) extra start).map witness) := by
    apply iso_hext (placeRun_last extra first.val first.property)
      (placeRun_last extra second.val second.property)
    cases witness with
    | inl similar =>
        change frameMap (RunStateGroupoid.endpointMap levels O
          (generator (helperTransport levels O) (.inl (placeSimilarity extra similar first.property second.property)))) =
          frameMap (placeIso extra similar.lastIso)
        rw [RunStateGroupoid.endpointMap_generator]
        exact placeSimilarity_frame extra similar first.property second.property
    | inr interchange => exact interchangeCell_frame extra interchange first.property second.property
  exact maps.trans (Quiver.homOfEq_heq (V := RunStateGroupoid.Object levels O)
    (placeRun_last extra first.val first.property).symm
    (placeRun_last extra second.val second.property).symm
    ((sourceBoundaryGenerators (levels := levels) extra start).map witness)).symm

theorem boundary_functors_equal (extra : Finset O) (start : State rules O) :
    placementFunctor (levels := levels) extra start ⋙
        RunStateGroupoid.endpointFunctor levels O (place extra start) =
      forgetFunctor (T := helperTransport levels O) (RunSafe (state := start) extra) ⋙
        RunStateGroupoid.endpointFunctor levels O start ⋙ statePlacement (levels := levels) extra := by
  have first : placementFunctor (levels := levels) extra start ⋙
      RunStateGroupoid.endpointFunctor levels O (place extra start) =
        Quiver.FreeGroupoid.lift (sourceBoundaryGenerators (levels := levels) extra start) := by
    apply Quiver.FreeGroupoid.lift_unique
    rw [← Functor.toPrefunctor_comp, ← Prefunctor.comp_assoc]
    have generators := Quiver.FreeGroupoid.lift_spec (placementGenerators (levels := levels) extra start)
    change Quiver.FreeGroupoid.of _ ⋙q (placementFunctor (levels := levels) extra start).toPrefunctor = _ at generators
    rw [generators]
    exact generators_boundary extra start
  have second : forgetFunctor (T := helperTransport levels O) (RunSafe (state := start) extra) ⋙
      RunStateGroupoid.endpointFunctor levels O start ⋙ statePlacement (levels := levels) extra =
        Quiver.FreeGroupoid.lift (sourceBoundaryGenerators (levels := levels) extra start) := by
    apply Quiver.FreeGroupoid.lift_unique
    rw [← Functor.toPrefunctor_comp, ← Prefunctor.comp_assoc]
    have forget := Quiver.FreeGroupoid.lift_spec
      (forgetGenerators (T := helperTransport levels O) (RunSafe (state := start) extra) ⋙q
        Quiver.FreeGroupoid.of (Object (helperTransport levels O) start))
    change Quiver.FreeGroupoid.of _ ⋙q
      (forgetFunctor (T := helperTransport levels O) (RunSafe (state := start) extra)).toPrefunctor = _ at forget
    have endpoints := Quiver.FreeGroupoid.lift_spec (RunStateGroupoid.endpointGenerators levels O start)
    change Quiver.FreeGroupoid.of _ ⋙q (RunStateGroupoid.endpointFunctor levels O start).toPrefunctor = _ at endpoints
    have tail : Quiver.FreeGroupoid.of (Object (helperTransport levels O) start) ⋙q
        (RunStateGroupoid.endpointFunctor levels O start ⋙ statePlacement (levels := levels) extra).toPrefunctor =
        RunStateGroupoid.endpointGenerators levels O start ⋙q (statePlacement (levels := levels) extra).toPrefunctor := by
      rw [← Functor.toPrefunctor_comp, ← Prefunctor.comp_assoc, endpoints]
    rw [forget, Prefunctor.comp_assoc, tail]
    rfl
  exact first.trans second.symm

theorem placement_boundary (extra : Finset O) (start : State rules O)
    {first second : Qualified (helperTransport levels O) (RunSafe (state := start) extra)}
    (cell : qualifiedObject first.val first.property ⟶ qualifiedObject second.val second.property) :
    HEq (RunStateGroupoid.endpointMap levels O ((placementFunctor extra start).map cell))
      (placeIso extra (RunStateGroupoid.endpointMap levels O
        ((forgetFunctor (T := helperTransport levels O) (RunSafe extra)).map cell))) :=
  Functor.hcongr_hom (boundary_functors_equal extra start) cell

end

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement.boundary_functors_equal
