import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.ConeCategory
import Mathlib.CategoryTheory.Presentable.Finite
import Mettapedia.GSLT.Core.GSLT
import Mettapedia.GSLT.Meredith.Bisimulation
import Mettapedia.Logic.Metaphysics.UltrainfinitismCore

/-!
# Ambient-first and proof-relevant structure beyond filtered GSLT growth

This file fixes the abstraction boundary for the ultrainfinite GSLT programme.
It is deliberately above any particular proof checker, evaluator, source logic,
or runtime.

There are two different directions around an ambient object, and neither may
be silently substituted for the other:

* a filtered growth presentation has maps from compact stages *into* an
  ambient object (the Ind-like direction);
* a perspective atlas has maps from an ambient object *out to* its shadows
  (the Pro/limit-like direction).

An `AmbientChart` may carry both.  It does not assert that the shadows
reconstruct the ambient object, that one coordinate is canonical, or that the
ambient object is nothing but its finite stages.

Reasoning also needs more than the ordinary one-category of GSLTs.  `Route`
retains a composite as data, `GeneratedTwoCell` freely closes authored
2-generators under composition and whiskering, and `FilledDiamond` carries a
chosen comparison between two routes.  These form raw two-dimensional syntax,
not yet a bicategory and not a claim that an `(infinity,2)`-category has already
been constructed.  They state the boundary that such a completion must extend:
coherence laws and all higher witnesses remain genuine obligations.

Finally, `BisimulationWitness` de-truncates the existential definition of
strong bisimilarity.  It retains the matching successor selected for every
transition and maps soundly into the existing bisimulation quotient.  This is
the first nontrivial reason the two-dimensional layer is useful: a witness can
be transported, compared, costed, and executed, while the quotient equality
is only its shadow.
-/

namespace Mettapedia.GSLT.Ultrainfinite

open CategoryTheory Limits
open Mettapedia.GSLT

universe uC vC uJ vJ uI vI uWhole uPerspective uShadow uObservation
universe uObj uStep uCell

/-! ## The two variances around an ambient object -/

/-- A filtered-colimit presentation of an object by finitely presentable
stages.  This is the shape supplied by an Ind-style growth construction; it is
not the definition of the ambient object itself. -/
structure FilteredGrowth
    {C : Type uC} [Category.{vC} C]
    {J : Type uJ} [SmallCategory J] [IsFiltered J]
    (stages : J ⥤ C) where
  cocone : Cocone stages
  isColimit : IsColimit cocone
  stage_compact : ∀ stage,
    IsFinitelyPresentable.{uJ} (stages.obj stage)

namespace FilteredGrowth

/-- Every map from a genuinely finitely presentable probe into the ambient
apex factors through some finite stage.  This is the compact-support theorem
that makes the Ind-like label mathematical rather than documentary. -/
theorem compact_factor
    {C : Type uC} [Category.{vC} C]
    {J : Type uJ} [SmallCategory J] [IsFiltered J]
    {stages : J ⥤ C} (growth : FilteredGrowth stages)
    {probe : C} [IsFinitelyPresentable.{uJ} probe]
    (map : probe ⟶ growth.cocone.pt) :
    ∃ (stage : J) (through : probe ⟶ stages.obj stage),
      through ≫ growth.cocone.ι.app stage = map :=
  IsFinitelyPresentable.exists_hom_of_isColimit growth.isColimit map

end FilteredGrowth

/-- A coherent family of shadows of one primary ambient object.  The apex of
the cone is the ambient object and each cone leg is a projection to one
perspective.  No limit or reconstruction property is assumed. -/
structure PerspectiveAtlas
    {C : Type uC} [Category.{vC} C]
    {I : Type uI} [Category.{vI} I]
    (shadows : I ⥤ C) where
  cone : Cone shadows

namespace PerspectiveAtlas

/-- The primary object from which all coordinates are projected. -/
abbrev ambient
    {C : Type uC} [Category.{vC} C]
    {I : Type uI} [Category.{vI} I]
    {shadows : I ⥤ C} (atlas : PerspectiveAtlas shadows) : C :=
  atlas.cone.pt

/-- Projection to one perspective. -/
def project
    {C : Type uC} [Category.{vC} C]
    {I : Type uI} [Category.{vI} I]
    {shadows : I ⥤ C} (atlas : PerspectiveAtlas shadows)
    (perspective : I) : atlas.ambient ⟶ shadows.obj perspective :=
  atlas.cone.π.app perspective

/-- Reconstruction from the whole coherent atlas is an additional property,
not part of having finite shadows. -/
def Reconstructs
    {C : Type uC} [Category.{vC} C]
    {I : Type uI} [Category.{vI} I]
    {shadows : I ⥤ C} (atlas : PerspectiveAtlas shadows) : Prop :=
  Nonempty (IsLimit atlas.cone)

end PerspectiveAtlas

/-- A small cofiltered atlas of finitely presentable shadows.  This is the
Pro-shaped perspective direction used by the present construction.  It is
stronger than an arbitrary cone but still does not say that its cone is a
limit: recoverability of the ambient object remains a separate property. -/
structure CompactPerspectiveAtlas
    {C : Type uC} [Category.{vC} C]
    {I : Type uI} [SmallCategory I] [IsCofiltered I]
    (shadows : I ⥤ C) extends PerspectiveAtlas shadows where
  shadow_compact : ∀ perspective,
    IsFinitelyPresentable.{uI} (shadows.obj perspective)

/-- One ambient object equipped both with an Ind-like growth presentation and
with a perspective atlas.  The isomorphism identifies the two named apexes;
it does not reverse any shadow projection. -/
structure AmbientChart
    {C : Type uC} [Category.{vC} C]
    {J : Type uJ} [SmallCategory J] [IsFiltered J]
    {I : Type uI} [SmallCategory I] [IsCofiltered I]
    (stages : J ⥤ C) (shadows : I ⥤ C) where
  growth : FilteredGrowth stages
  atlas : CompactPerspectiveAtlas shadows
  identifyApex : growth.cocone.pt ≅ atlas.toPerspectiveAtlas.ambient

namespace AmbientChart

/-- Every compact stage has a view in every perspective, by entering the
ambient object and then projecting out.  This composite is the basic bridge
between the two variances. -/
def stageToShadow
    {C : Type uC} [Category.{vC} C]
    {J : Type uJ} [SmallCategory J] [IsFiltered J]
    {I : Type uI} [SmallCategory I] [IsCofiltered I]
    {stages : J ⥤ C} {shadows : I ⥤ C}
    (chart : AmbientChart stages shadows)
    (stage : J) (perspective : I) :
    stages.obj stage ⟶ shadows.obj perspective :=
  chart.growth.cocone.ι.app stage ≫ chart.identifyApex.hom ≫
    chart.atlas.toPerspectiveAtlas.project perspective

end AmbientChart

/-! ### The specialization to the live behavioral GSLT category -/

/-- An Ind-shaped filtered presentation inside the existing category of
abstract behavioral GSLTs.  This asks for finite presentability stage by stage;
it does not assume that the whole GSLT category is locally finitely
presentable. -/
abbrev FilteredGSLTGrowth
    {J : Type uJ} [SmallCategory J] [IsFiltered J]
    (stages : J ⥤ GSLT) :=
  FilteredGrowth stages

/-- A small cofiltered atlas of finitely presentable behavioral GSLT
shadows.  Limit reconstruction remains optional. -/
abbrev GSLTPerspectiveAtlas
    {I : Type uI} [SmallCategory I] [IsCofiltered I]
    (shadows : I ⥤ GSLT) :=
  CompactPerspectiveAtlas shadows

/-- The two-sided chart over the live GSLT category.  This is the first honest
formal object *beyond* an Ind-only view: growth and observation coexist with
opposite variances around one ambient GSLT. -/
abbrev UltrainfiniteGSLTChart
    {J : Type uJ} [SmallCategory J] [IsFiltered J]
    {I : Type uI} [SmallCategory I] [IsCofiltered I]
    (stages : J ⥤ GSLT) (shadows : I ⥤ GSLT) :=
  AmbientChart stages shadows

/-! ## Type-level observations and the ultrafilter dial -/

/-- A perspective-indexed projection whose shadows preserve a declared
observation.  Observation types may vary by perspective.  Adequacy is local to
that observation and deliberately does not assert whole-object recovery. -/
structure PerspectiveProjection
    (Whole : Type uWhole) (Perspective : Type uPerspective)
    (Shadow : Perspective → Type uShadow)
    (Observation : Perspective → Type uObservation) where
  project : (perspective : Perspective) → Whole → Shadow perspective
  observeWhole : (perspective : Perspective) → Whole → Observation perspective
  observeShadow : (perspective : Perspective) →
    Shadow perspective → Observation perspective
  adequate : ∀ perspective whole,
    observeShadow perspective (project perspective whole) =
      observeWhole perspective whole

namespace PerspectiveProjection

/-- The proposition seen at each coordinate after projecting the primary
object. -/
def verdictFamily
    {Whole : Type uWhole} {Perspective : Type uPerspective}
    {Shadow : Perspective → Type uShadow}
    {Observation : Perspective → Type uObservation}
    (projection : PerspectiveProjection Whole Perspective Shadow Observation)
    (whole : Whole)
    (verdict : (perspective : Perspective) →
      Observation perspective → Prop) : Perspective → Prop :=
  fun perspective =>
    verdict perspective
      (projection.observeShadow perspective
        (projection.project perspective whole))

/-- Shadow evaluation agrees coordinatewise with direct observation of the
ambient object. -/
theorem verdictFamily_eq_ambient
    {Whole : Type uWhole} {Perspective : Type uPerspective}
    {Shadow : Perspective → Type uShadow}
    {Observation : Perspective → Type uObservation}
    (projection : PerspectiveProjection Whole Perspective Shadow Observation)
    (whole : Whole)
    (verdict : (perspective : Perspective) →
      Observation perspective → Prop) :
    projection.verdictFamily whole verdict =
      fun perspective =>
        verdict perspective (projection.observeWhole perspective whole) := by
  funext perspective
  simp [verdictFamily, projection.adequate]

/-- Precision is unanimity across all ultrafilter perspectives. -/
def Precise
    {Whole : Type uWhole} {Perspective : Type uPerspective}
    {Shadow : Perspective → Type uShadow}
    {Observation : Perspective → Type uObservation}
    (projection : PerspectiveProjection Whole Perspective Shadow Observation)
    (whole : Whole)
    (verdict : (perspective : Perspective) →
      Observation perspective → Prop) : Prop :=
  Mettapedia.Logic.Metaphysics.PreciseFamily
    (projection.verdictFamily whole verdict)

/-- Openness is genuine disagreement between ultrafilter perspectives. -/
def Open
    {Whole : Type uWhole} {Perspective : Type uPerspective}
    {Shadow : Perspective → Type uShadow}
    {Observation : Perspective → Type uObservation}
    (projection : PerspectiveProjection Whole Perspective Shadow Observation)
    (whole : Whole)
    (verdict : (perspective : Perspective) →
      Observation perspective → Prop) : Prop :=
  Mettapedia.Logic.Metaphysics.OpenFamily
    (projection.verdictFamily whole verdict)

theorem open_iff_not_precise
    {Whole : Type uWhole} {Perspective : Type uPerspective}
    {Shadow : Perspective → Type uShadow}
    {Observation : Perspective → Type uObservation}
    (projection : PerspectiveProjection Whole Perspective Shadow Observation)
    (whole : Whole)
    (verdict : (perspective : Perspective) →
      Observation perspective → Prop) :
    projection.Open whole verdict ↔ ¬ projection.Precise whole verdict :=
  Mettapedia.Logic.Metaphysics.openFamily_iff_not_precise _

/-- Principal collapse for an arbitrary adequate shadow system.  Selecting
one coordinate by a principal ultrafilter is exactly evaluating that shadow. -/
theorem ultraTrue_pure
    {Whole : Type uWhole} {Perspective : Type uPerspective}
    {Shadow : Perspective → Type uShadow}
    {Observation : Perspective → Type uObservation}
    (projection : PerspectiveProjection Whole Perspective Shadow Observation)
    (whole : Whole)
    (verdict : (perspective : Perspective) →
      Observation perspective → Prop)
  (perspective : Perspective) :
    Mettapedia.Logic.Metaphysics.UltraTrue (pure perspective)
        (projection.verdictFamily whole verdict) ↔
      verdict perspective (projection.observeWhole perspective whole) := by
  rw [Mettapedia.Logic.Metaphysics.ultraTrue_pure]
  simp [verdictFamily, projection.adequate]

/-- Reindexing perspectives changes coordinates, not the ultrafilter verdict. -/
theorem ultraTrue_reindex
    {Whole : Type uWhole} {Perspective : Type uPerspective}
    {Shadow : Perspective → Type uShadow}
    {Observation : Perspective → Type uObservation}
    (projection : PerspectiveProjection Whole Perspective Shadow Observation)
    (whole : Whole)
    (verdict : (perspective : Perspective) →
      Observation perspective → Prop)
    (coordinate : Perspective → Perspective)
    (view : Ultrafilter Perspective) :
    Mettapedia.Logic.Metaphysics.UltraTrue (view.map coordinate)
        (projection.verdictFamily whole verdict) ↔
      Mettapedia.Logic.Metaphysics.UltraTrue view
        (fun perspective =>
          projection.verdictFamily whole verdict (coordinate perspective)) :=
  Mettapedia.Logic.Metaphysics.ultraTrue_map coordinate view _

end PerspectiveProjection

/-! ## Proof-relevant paths and a two-dimensional substrate -/

/-- A route retains its authored one-steps instead of collapsing them to a
composite or an endpoint relation. -/
inductive Route {Object : Type uObj}
    (Step : Object → Object → Type uStep) : Object → Object → Type _ where
  | refl (object : Object) : Route Step object object
  | cons {source middle target : Object} :
      Step source middle → Route Step middle target → Route Step source target

namespace Route

def append {Object : Type uObj} {Step : Object → Object → Type uStep}
    {source middle target : Object}
    (first : Route Step source middle) (second : Route Step middle target) :
    Route Step source target :=
  match first with
  | .refl _ => second
  | .cons step rest => .cons step (append rest second)

def length {Object : Type uObj} {Step : Object → Object → Type uStep}
    {source target : Object} : Route Step source target → Nat
  | .refl _ => 0
  | .cons _ rest => rest.length + 1

@[simp] theorem refl_append
    {Object : Type uObj} {Step : Object → Object → Type uStep}
    {source target : Object} (route : Route Step source target) :
    append (.refl source) route = route := rfl

@[simp] theorem append_refl
    {Object : Type uObj} {Step : Object → Object → Type uStep}
    {source target : Object} (route : Route Step source target) :
    append route (.refl target) = route := by
  induction route with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      simp [append, inductionHypothesis]

theorem append_assoc
    {Object : Type uObj} {Step : Object → Object → Type uStep}
    {a b c d : Object}
    (first : Route Step a b) (second : Route Step b c)
    (third : Route Step c d) :
    append (append first second) third =
      append first (append second third) := by
  induction first with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      simp [append, inductionHypothesis]

@[simp] theorem length_append
    {Object : Type uObj} {Step : Object → Object → Type uStep}
    {source middle target : Object}
    (first : Route Step source middle) (second : Route Step middle target) :
    (append first second).length = first.length + second.length := by
  induction first with
  | refl => simp [append, length]
  | cons step rest inductionHypothesis =>
      simp [append, length, inductionHypothesis, Nat.add_assoc,
        Nat.add_comm]

/-- A step-invariant observation is invariant along every proof-relevant
route.  This is the reusable conservation law behind staged routes: retaining
the individual steps changes the available evidence, not the observation. -/
theorem observe_eq_of_route
    {Object : Type uObj} {Step : Object → Object → Type uStep}
    {Observation : Type uObservation}
    (observe : Object → Observation)
    (stepInvariant : ∀ {source target}, Step source target →
      observe source = observe target)
    {source target : Object} (route : Route Step source target) :
    observe source = observe target := by
  induction route with
  | refl => rfl
  | cons step rest inductionHypothesis =>
      exact (stepInvariant step).trans inductionHypothesis

end Route

/-- The raw free closure of authored two-dimensional generators.  It has
formal vertical composition and left/right whiskering.  No quotient by
coherence laws and no infinite tower of higher cells is claimed here. -/
inductive GeneratedTwoCell
    {Object : Type uObj} {Step : Object → Object → Type uStep}
    (Generator : {source target : Object} →
      Route Step source target → Route Step source target → Type uCell) :
    {source target : Object} →
      Route Step source target → Route Step source target → Type _ where
  | refl {source target} (route : Route Step source target) :
      GeneratedTwoCell Generator route route
  | generator {source target} {first second : Route Step source target} :
      Generator first second → GeneratedTwoCell Generator first second
  | vertical {source target} {first middle last : Route Step source target} :
      GeneratedTwoCell Generator first middle →
      GeneratedTwoCell Generator middle last →
      GeneratedTwoCell Generator first last
  | whiskerLeft {a b c} (initial : Route Step a b)
      {first second : Route Step b c} :
      GeneratedTwoCell Generator first second →
      GeneratedTwoCell Generator (initial.append first) (initial.append second)
  | whiskerRight {a b c} {first second : Route Step a b}
      (suffix : Route Step b c) :
      GeneratedTwoCell Generator first second →
      GeneratedTwoCell Generator (first.append suffix) (second.append suffix)

/-- A chosen higher comparison between two complete routes around a diamond.
The branches and the filler remain data. -/
structure FilledDiamond
    {Object : Type uObj} (Step : Object → Object → Type uStep)
    (Cell : {source target : Object} →
      Route Step source target → Route Step source target → Type uCell)
    (source left right : Object) where
  leftBranch : Route Step source left
  rightBranch : Route Step source right
  join : Object
  closeLeft : Route Step left join
  closeRight : Route Step right join
  filler : Cell (leftBranch.append closeLeft)
    (rightBranch.append closeRight)

/-! ## Observational return is weaker than syntactic return -/

/-- Compilation may return a different ambient object while preserving the
observation that defines its semantics. -/
structure ObservationalRetraction
    (Ambient : Type uWhole) (Code : Type uShadow)
    (Observation : Type uObservation) where
  compile : Ambient → Code
  decompile : Code → Ambient
  observe : Ambient → Observation
  roundTrip_observation : ∀ ambient,
    observe (decompile (compile ambient)) = observe ambient

/-- Exact syntactic return is a strictly stronger optional property. -/
def ObservationalRetraction.Syntactic
    {Ambient : Type uWhole} {Code : Type uShadow}
    {Observation : Type uObservation}
    (retraction : ObservationalRetraction Ambient Code Observation) : Prop :=
  ∀ ambient, retraction.decompile (retraction.compile ambient) = ambient

theorem ObservationalRetraction.observation_of_syntactic
    {Ambient : Type uWhole} {Code : Type uShadow}
    {Observation : Type uObservation}
    (compile : Ambient → Code) (decompile : Code → Ambient)
    (observe : Ambient → Observation)
    (syntactic : ∀ ambient, decompile (compile ambient) = ambient) :
    ∀ ambient, observe (decompile (compile ambient)) = observe ambient := by
  intro ambient
  rw [syntactic ambient]

/-! ## A carried bisimulation witness and its ontological shadow -/

/-- One selected matching transition. -/
structure BisimulationMatch (system : GSLT)
    (Related : system.Term → system.Term → Type uCell)
    (sourceTarget otherSource : system.Term) where
  otherTarget : system.Term
  step : system.Step otherSource otherTarget
  related : Related sourceTarget otherTarget

/-- A proof-relevant bisimulation.  Unlike `GSLT.Bisimilar`, this retains the
relation witness and the chosen response to every transition. -/
structure BisimulationWitness (system : GSLT) where
  Related : system.Term → system.Term → Type uCell
  forward : ∀ {left right}, Related left right →
    ∀ {leftTarget}, system.Step left leftTarget →
      BisimulationMatch system Related leftTarget right
  backward : ∀ {left right}, Related left right →
    ∀ {rightTarget}, system.Step right rightTarget →
      BisimulationMatch system (fun right' left' => Related left' right')
        rightTarget left

namespace BisimulationWitness

/-- Equality carries the reflexive proof-relevant bisimulation. -/
def refl (system : GSLT) : BisimulationWitness system where
  Related := fun left right => PLift (left = right)
  forward := by
    intro left right related leftTarget step
    cases related.down
    exact ⟨leftTarget, step, ⟨rfl⟩⟩
  backward := by
    intro left right related rightTarget step
    cases related.down
    exact ⟨rightTarget, step, ⟨rfl⟩⟩

/-- Reversing the retained relation and its chosen matchers retains a
proof-relevant bisimulation in the opposite direction. -/
def symm {system : GSLT} (witness : BisimulationWitness system) :
    BisimulationWitness system where
  Related := fun left right => witness.Related right left
  forward := by
    intro left right related leftTarget step
    exact witness.backward related step
  backward := by
    intro left right related rightTarget step
    exact witness.forward related step

/-- Relational composition composes the selected matching transitions, while
retaining the intermediate term and both component witnesses. -/
def trans {system : GSLT}
    (first second : BisimulationWitness system) :
    BisimulationWitness system where
  Related := fun left right =>
    Σ middle, first.Related left middle × second.Related middle right
  forward := by
    intro left right related leftTarget step
    obtain ⟨middle, firstRelated, secondRelated⟩ := related
    let firstMatch := first.forward firstRelated step
    let secondMatch := second.forward secondRelated firstMatch.step
    exact ⟨secondMatch.otherTarget, secondMatch.step,
      ⟨firstMatch.otherTarget, firstMatch.related, secondMatch.related⟩⟩
  backward := by
    intro left right related rightTarget step
    obtain ⟨middle, firstRelated, secondRelated⟩ := related
    let secondMatch := second.backward secondRelated step
    let firstMatch := first.backward firstRelated secondMatch.step
    exact ⟨firstMatch.otherTarget, firstMatch.step,
      ⟨secondMatch.otherTarget, firstMatch.related, secondMatch.related⟩⟩

/-- Propositional erasure of the carried relation is an ordinary
bisimulation. -/
theorem toIsBisimulation {system : GSLT}
    (witness : BisimulationWitness system) :
    system.IsBisimulation
      (fun left right => Nonempty (witness.Related left right)) := by
  constructor
  · rintro left right ⟨related⟩ leftTarget step
    let matched := witness.forward related step
    exact ⟨matched.otherTarget, matched.step, ⟨matched.related⟩⟩
  · rintro left right ⟨related⟩ rightTarget step
    let matched := witness.backward related step
    exact ⟨matched.otherTarget, matched.step, ⟨matched.related⟩⟩

/-- A carried witness entails the existing existential bisimilarity
proposition. -/
theorem toBisimilar {system : GSLT}
    (witness : BisimulationWitness system) {left right : system.Term}
    (related : witness.Related left right) : system.Bisimilar left right :=
  ⟨fun first second => Nonempty (witness.Related first second),
    witness.toIsBisimulation, ⟨related⟩⟩

/-- Consequently, a carried witness identifies the terms in Meredith's
bisimulation quotient.  The quotient equality is a shadow of the witness, not
its replacement. -/
theorem toBisimClass_eq {system : GSLT}
    (witness : BisimulationWitness system) {left right : system.Term}
    (related : witness.Related left right) :
    Mettapedia.GSLT.Meredith.Bisimulation.toBisimClass system left =
      Mettapedia.GSLT.Meredith.Bisimulation.toBisimClass system right :=
  (Mettapedia.GSLT.Meredith.Bisimulation.bisimClass_eq_iff
    system left right).2 (witness.toBisimilar related)

end BisimulationWitness

end Mettapedia.GSLT.Ultrainfinite
