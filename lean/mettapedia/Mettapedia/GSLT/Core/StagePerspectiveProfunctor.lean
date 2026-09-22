import Mettapedia.GSLT.Core.Ultrainfinite

/-!
# The stage--perspective profunctor

A filtered presentation with a perspective cone has two independently
meaningful indices:

* filtered stages enter the ambient object; and
* cofiltered perspectives receive projections from it.

For any stage diagram `stages : J ⥤ C` and perspective diagram
`shadows : I ⥤ C`, the hom-sets

```text
(stage, perspective) ↦ (stages.obj stage ⟶ shadows.obj perspective)
```

form a profunctor `Jᵒᵖ ⥤ I ⥤ Type`.  This is the variable-set object already
implicit in the two variances: changing a stage acts by precomposition and
changing a perspective acts by postcomposition.

An `FilteredPresentationWithCone` supplies one coherent element of every such hom-set through
`stageToShadow`.  The two naturality theorems below prove that these elements
respect both indices.  Neither the profunctor nor its distinguished coherent
element says that the stages or shadows reconstruct the ambient object;
reconstruction remains the separate colimit/limit obligation declared in
`Ultrainfinite.lean`.
-/

namespace Mettapedia.GSLT.Ultrainfinite

open CategoryTheory

universe uC vC uJ vJ uI vI

variable {C : Type uC} [Category.{vC} C]
variable {J : Type uJ} [Category.{vJ} J]
variable {I : Type uI} [Category.{vI} I]

/-- The stage--perspective matrix as a profunctor.  Its values are sets of
maps, contravariant in stages and covariant in perspectives. -/
def stagePerspectiveProfunctor
    (stages : J ⥤ C) (shadows : I ⥤ C) : Jᵒᵖ ⥤ I ⥤ Type vC where
  obj stage :=
    { obj := fun perspective =>
        stages.obj stage.unop ⟶ shadows.obj perspective
      map := fun {first second} perspectiveMap =>
        ↾(fun stageView : stages.obj stage.unop ⟶ shadows.obj first =>
          stageView ≫ shadows.map perspectiveMap)
      map_id := by
        intro perspective
        ext stageView
        simp
      map_comp := by
        intro first second third firstMap secondMap
        ext stageView
        simp [Category.assoc] }
  map := fun {first second} stageMap =>
    { app := fun perspective =>
        ↾(fun stageView :
            stages.obj first.unop ⟶ shadows.obj perspective =>
          stages.map stageMap.unop ≫ stageView)
      naturality := by
        intro first second perspectiveMap
        ext stageView
        simp [Category.assoc] }
  map_id := by
    intro stage
    ext perspective stageView
    simp
  map_comp := by
    intro first second third firstMap secondMap
    ext perspective stageView
    simp [Category.assoc]

namespace FilteredPresentationWithCone

variable {J : Type uJ} [SmallCategory J] [IsFiltered J]
variable {I : Type uI} [SmallCategory I] [IsCofiltered I]
variable {stages : J ⥤ C} {shadows : I ⥤ C}

/-- The canonical stage-to-shadow map is natural in the filtered-stage
direction.  Enlarging a stage and then observing it is the same map as
observing the earlier stage directly. -/
theorem stageToShadow_natural_stage
    (presentation : FilteredPresentationWithCone stages shadows)
    {first second : J} (stageMap : first ⟶ second)
    (perspective : I) :
    stages.map stageMap ≫ presentation.stageToShadow second perspective =
      presentation.stageToShadow first perspective := by
  have stageNaturality :
      stages.map stageMap ≫ presentation.growth.cocone.ι.app second =
        presentation.growth.cocone.ι.app first :=
    presentation.growth.cocone.w stageMap
  simpa only [stageToShadow, Category.assoc] using!
    stageNaturality =≫
      (presentation.identifyApex.hom ≫
        presentation.perspectives.toPerspectiveCone.project perspective)

/-- The canonical stage-to-shadow map is natural in the perspective
direction.  Observing a stage and then refining its perspective is the same
map as observing it directly at the refined perspective. -/
theorem stageToShadow_natural_perspective
    (presentation : FilteredPresentationWithCone stages shadows)
    (stage : J) {first second : I}
    (perspectiveMap : first ⟶ second) :
    presentation.stageToShadow stage first ≫ shadows.map perspectiveMap =
      presentation.stageToShadow stage second := by
  have perspectiveNaturality :=
    presentation.perspectives.toPerspectiveCone.cone.w perspectiveMap
  have whiskered := congrArg
    (fun projection =>
      presentation.growth.cocone.ι.app stage ≫ presentation.identifyApex.hom ≫
        projection)
    perspectiveNaturality
  simpa only [stageToShadow, PerspectiveCone.project, Category.assoc]
    using whiskered

/-- The terminal-valued profunctor used to express a coherent chosen element
of every stage--perspective hom-set. -/
private def terminalProfunctor : Jᵒᵖ ⥤ I ⥤ Type vC :=
  (Functor.const Jᵒᵖ).obj
    ((Functor.const I).obj (ULift.{vC} PUnit))

/-- A filtered presentation with a perspective cone selects a coherent element of the stage--perspective
profunctor.  This packages both naturality laws into one natural
transformation without adding a reconstruction assumption. -/
def stageToShadowSection
    (presentation : FilteredPresentationWithCone stages shadows) :
    terminalProfunctor ⟶ stagePerspectiveProfunctor stages shadows where
  app stage :=
    { app := fun perspective =>
        ↾(fun _ : ULift.{vC} PUnit =>
          presentation.stageToShadow stage.unop perspective)
      naturality := by
        intro first second perspectiveMap
        ext element
        exact (presentation.stageToShadow_natural_perspective
          stage.unop perspectiveMap).symm }
  naturality := by
    intro first second stageMap
    ext perspective element
    exact (presentation.stageToShadow_natural_stage stageMap.unop perspective).symm

/-- Evaluating the coherent section recovers the original composite through
the ambient object. -/
theorem stageToShadowSection_apply
    (presentation : FilteredPresentationWithCone stages shadows)
    (stage : J) (perspective : I) :
    (presentation.stageToShadowSection.app (Opposite.op stage)).app perspective
        (ULift.up PUnit.unit) =
      presentation.stageToShadow stage perspective :=
  rfl

end FilteredPresentationWithCone

#print axioms stagePerspectiveProfunctor
#print axioms FilteredPresentationWithCone.stageToShadow_natural_stage
#print axioms FilteredPresentationWithCone.stageToShadow_natural_perspective
#print axioms FilteredPresentationWithCone.stageToShadowSection

end Mettapedia.GSLT.Ultrainfinite
