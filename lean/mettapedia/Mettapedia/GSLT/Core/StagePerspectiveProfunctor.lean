import Mettapedia.GSLT.Core.Ultrainfinite

/-!
# The stage--perspective profunctor

An ultrainfinite ambient chart has two independently meaningful indices:

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

An `AmbientChart` supplies one coherent element of every such hom-set through
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

namespace AmbientChart

variable {J : Type uJ} [SmallCategory J] [IsFiltered J]
variable {I : Type uI} [SmallCategory I] [IsCofiltered I]
variable {stages : J ⥤ C} {shadows : I ⥤ C}

/-- The canonical stage-to-shadow map is natural in the filtered-stage
direction.  Enlarging a stage and then observing it is the same map as
observing the earlier stage directly. -/
theorem stageToShadow_natural_stage
    (chart : AmbientChart stages shadows)
    {first second : J} (stageMap : first ⟶ second)
    (perspective : I) :
    stages.map stageMap ≫ chart.stageToShadow second perspective =
      chart.stageToShadow first perspective := by
  have stageNaturality :
      stages.map stageMap ≫ chart.growth.cocone.ι.app second =
        chart.growth.cocone.ι.app first :=
    chart.growth.cocone.w stageMap
  simpa only [stageToShadow, Category.assoc] using!
    stageNaturality =≫
      (chart.identifyApex.hom ≫
        chart.atlas.toPerspectiveAtlas.project perspective)

/-- The canonical stage-to-shadow map is natural in the perspective
direction.  Observing a stage and then refining its perspective is the same
map as observing it directly at the refined perspective. -/
theorem stageToShadow_natural_perspective
    (chart : AmbientChart stages shadows)
    (stage : J) {first second : I}
    (perspectiveMap : first ⟶ second) :
    chart.stageToShadow stage first ≫ shadows.map perspectiveMap =
      chart.stageToShadow stage second := by
  have perspectiveNaturality :=
    chart.atlas.toPerspectiveAtlas.cone.w perspectiveMap
  have whiskered := congrArg
    (fun projection =>
      chart.growth.cocone.ι.app stage ≫ chart.identifyApex.hom ≫
        projection)
    perspectiveNaturality
  simpa only [stageToShadow, PerspectiveAtlas.project, Category.assoc]
    using whiskered

/-- The terminal-valued profunctor used to express a coherent chosen element
of every stage--perspective hom-set. -/
private def terminalProfunctor : Jᵒᵖ ⥤ I ⥤ Type vC :=
  (Functor.const Jᵒᵖ).obj
    ((Functor.const I).obj (ULift.{vC} PUnit))

/-- An ambient chart selects a coherent element of the stage--perspective
profunctor.  This packages both naturality laws into one natural
transformation without adding a reconstruction assumption. -/
def stageToShadowSection
    (chart : AmbientChart stages shadows) :
    terminalProfunctor ⟶ stagePerspectiveProfunctor stages shadows where
  app stage :=
    { app := fun perspective =>
        ↾(fun _ : ULift.{vC} PUnit =>
          chart.stageToShadow stage.unop perspective)
      naturality := by
        intro first second perspectiveMap
        ext element
        simpa [terminalProfunctor, stagePerspectiveProfunctor] using
          (chart.stageToShadow_natural_perspective
            stage.unop perspectiveMap).symm }
  naturality := by
    intro first second stageMap
    ext perspective element
    simpa [terminalProfunctor, stagePerspectiveProfunctor] using
      (chart.stageToShadow_natural_stage stageMap.unop perspective).symm

/-- Evaluating the coherent section recovers the original composite through
the ambient object. -/
theorem stageToShadowSection_apply
    (chart : AmbientChart stages shadows)
    (stage : J) (perspective : I) :
    (chart.stageToShadowSection.app (Opposite.op stage)).app perspective
        (ULift.up PUnit.unit) =
      chart.stageToShadow stage perspective :=
  rfl

end AmbientChart

#print axioms stagePerspectiveProfunctor
#print axioms AmbientChart.stageToShadow_natural_stage
#print axioms AmbientChart.stageToShadow_natural_perspective
#print axioms AmbientChart.stageToShadowSection

end Mettapedia.GSLT.Ultrainfinite
