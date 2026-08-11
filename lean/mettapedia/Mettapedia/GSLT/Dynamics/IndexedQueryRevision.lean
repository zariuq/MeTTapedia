import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.GSLT.Dynamics.QueryRevision

/-!
# Indexed query and revision theories

Theory growth and world revision are different axes.  A stage translation
maps worlds, revision events, queries, and observations; its laws say both
that revision steps are preserved and that queries commute with transport.
It need not reflect newly available target revisions.  `ExactTranslation`
adds that stronger condition explicitly.

Each query/revision theory has a generated GSLT whose terms are worlds and
whose reductions are labelled revision events with the label existentially
hidden at the propositional boundary.  Consequently a diagram of queryable
world theories feeds the generic indexed command calculus directly.  Its
existing naturality cell is then the theory-stage/world-revision square,
rather than a second hand-authored execution relation.
-/

namespace Mettapedia.GSLT.Dynamics.IndexedQueryRevision

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics.QueryRevision
open Mettapedia.GSLT.IndexedOperational

universe uWorld uRevision uQuery uObservation uIndex vIndex

/-! ## Stage translations -/

/-- A forward translation of queryable revision theories.  It preserves
revision events and the complete declared query interface, but may expose new
target revisions at translated worlds. -/
structure Translation (source target : Theory) where
  mapWorld : source.World → target.World
  mapRevision : source.Revision → target.Revision
  mapQuery : source.Query → target.Query
  mapObservation : source.Observation → target.Observation
  step_map : ∀ {revision sourceWorld targetWorld},
    source.Step revision sourceWorld targetWorld →
      target.Step (mapRevision revision) (mapWorld sourceWorld)
        (mapWorld targetWorld)
  query_natural : ∀ world query,
    target.query (mapWorld world) (mapQuery query) =
      mapObservation (source.query world query)

namespace Translation

@[ext]
theorem ext {source target : Theory}
    {first second : Translation source target}
    (world : first.mapWorld = second.mapWorld)
    (revision : first.mapRevision = second.mapRevision)
    (query : first.mapQuery = second.mapQuery)
    (observation : first.mapObservation = second.mapObservation) :
    first = second := by
  cases first
  cases second
  cases world
  cases revision
  cases query
  cases observation
  rfl

/-- Identity translation. -/
def id (theory : Theory) : Translation theory theory where
  mapWorld := _root_.id
  mapRevision := _root_.id
  mapQuery := _root_.id
  mapObservation := _root_.id
  step_map := fun step => step
  query_natural := fun _ _ => rfl

/-- Stage translations compose in execution order. -/
def comp {first middle last : Theory}
    (earlier : Translation first middle)
    (later : Translation middle last) : Translation first last where
  mapWorld := later.mapWorld ∘ earlier.mapWorld
  mapRevision := later.mapRevision ∘ earlier.mapRevision
  mapQuery := later.mapQuery ∘ earlier.mapQuery
  mapObservation := later.mapObservation ∘ earlier.mapObservation
  step_map := fun step => later.step_map (earlier.step_map step)
  query_natural := by
    intro world query
    change last.query
        (later.mapWorld (earlier.mapWorld world))
        (later.mapQuery (earlier.mapQuery query)) =
      later.mapObservation
        (earlier.mapObservation (first.query world query))
    rw [later.query_natural, earlier.query_natural]

end Translation

/-- Exact stage transport additionally lifts every target revision leaving a
translated world, including the revision identity.  This is appropriate for
conservative operational embeddings and exact realizations, but not for a
theory extension which intentionally adds behavior. -/
structure ExactTranslation (source target : Theory)
    extends Translation source target where
  liftStep : ∀ {sourceWorld targetWorld targetRevision},
    target.Step targetRevision (toTranslation.mapWorld sourceWorld)
        targetWorld →
      ∃ sourceRevision sourceTarget,
        source.Step sourceRevision sourceWorld sourceTarget ∧
        toTranslation.mapRevision sourceRevision = targetRevision ∧
        toTranslation.mapWorld sourceTarget = targetWorld

namespace ExactTranslation

/-- Forget exact local reflection. -/
abbrev forget {source target : Theory}
    (translation : ExactTranslation source target) :
    Translation source target :=
  translation.toTranslation

@[ext]
theorem ext {source target : Theory}
    {first second : ExactTranslation source target}
    (translation : first.toTranslation = second.toTranslation) :
    first = second := by
  cases first
  cases second
  cases translation
  rfl

/-- Identity is exact. -/
def id (theory : Theory) : ExactTranslation theory theory where
  toTranslation := Translation.id theory
  liftStep := by
    intro sourceWorld targetWorld targetRevision step
    exact ⟨targetRevision, targetWorld, step, rfl, rfl⟩

/-- Exact translations compose, retaining both the lifted event identity and
the lifted target world. -/
def comp {first middle last : Theory}
    (earlier : ExactTranslation first middle)
    (later : ExactTranslation middle last) :
    ExactTranslation first last where
  toTranslation := earlier.toTranslation.comp later.toTranslation
  liftStep := by
    intro sourceWorld targetWorld targetRevision step
    obtain ⟨middleRevision, middleTarget, middleStep,
        middleRevisionEq, middleTargetEq⟩ :=
      later.liftStep step
    obtain ⟨sourceRevision, sourceTarget, sourceStep,
        sourceRevisionEq, sourceTargetEq⟩ :=
      earlier.liftStep middleStep
    exact ⟨sourceRevision, sourceTarget, sourceStep,
      (congrArg later.mapRevision sourceRevisionEq).trans middleRevisionEq,
      (congrArg later.mapWorld sourceTargetEq).trans middleTargetEq⟩

end ExactTranslation

/-! ## Generated operational GSLTs -/

/-- World revision as a GSLT.  The event label remains in the step witness;
the public reduction proposition existentially hides which event fired. -/
def revisionGSLT (theory : Theory) : GSLT where
  Term := theory.World
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target =>
    ∃ revision, theory.Step revision source target
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- A named revision step is a generated GSLT step. -/
theorem revision_is_step
    {theory : Theory} {revision : theory.Revision}
    {source target : theory.World}
    (step : theory.Step revision source target) :
    (revisionGSLT theory).Step source target :=
  ⟨revision, step⟩

/-- A forward query/revision translation induces a forward operational GSLT
translation on worlds. -/
def Translation.toOperational
    {source target : Theory} (translation : Translation source target) :
    OperationalTranslation (revisionGSLT source) (revisionGSLT target) where
  mapTerm := translation.mapWorld
  mapEquiv := by
    intro left right equal
    cases equal
    rfl
  mapStep := by
    rintro left right ⟨revision, step⟩
    exact ⟨translation.mapRevision revision, translation.step_map step⟩

/-- Exact query/revision transport induces exact local step coverage after
event labels are hidden by the GSLT relation. -/
def ExactTranslation.toCoveredOperational
    {source target : Theory}
    (translation : ExactTranslation source target) :
    CoveredTranslation (revisionGSLT source) (revisionGSLT target) where
  mapTerm := translation.mapWorld
  mapEquiv := by
    intro left right equal
    cases equal
    rfl
  cover :=
    { mapStep := translation.toTranslation.toOperational.mapStep
      liftStep := by
        rintro sourceWorld targetWorld ⟨targetRevision, targetStep⟩
        obtain ⟨sourceRevision, sourceTarget, sourceStep, _, targetEq⟩ :=
          translation.liftStep targetStep
        exact ⟨sourceTarget, ⟨sourceRevision, sourceStep⟩, targetEq⟩ }

/-! ## Categorical stage diagrams -/

/-- Objects of the category of queryable world theories. -/
structure QueryableTheory where
  theory : Theory.{uWorld, uRevision, uQuery, uObservation}

instance : CategoryTheory.Category QueryableTheory where
  Hom source target := Translation source.theory target.theory
  id object := Translation.id object.theory
  comp earlier later := earlier.comp later
  id_comp translation := by
    apply Translation.ext <;> rfl
  comp_id translation := by
    apply Translation.ext <;> rfl
  assoc first second third := by
    apply Translation.ext <;> rfl

/-- The exact-transport category has the same objects but admits only locally
reflecting revision translations. -/
structure ExactQueryableTheory where
  theory : Theory.{uWorld, uRevision, uQuery, uObservation}

instance : CategoryTheory.Category ExactQueryableTheory where
  Hom source target := ExactTranslation source.theory target.theory
  id object := ExactTranslation.id object.theory
  comp earlier later := earlier.comp later
  id_comp translation := by
    apply ExactTranslation.ext
    apply Translation.ext <;> rfl
  comp_id translation := by
    apply ExactTranslation.ext
    apply Translation.ext <;> rfl
  assoc first second third := by
    apply ExactTranslation.ext
    apply Translation.ext <;> rfl

/-- Forget exact reflection while preserving all forward query/revision
structure. -/
def forgetExact :
    CategoryTheory.Functor ExactQueryableTheory QueryableTheory where
  obj object := ⟨object.theory⟩
  map translation := translation.toTranslation
  map_id object := by
    apply Translation.ext <;> rfl
  map_comp earlier later := by
    apply Translation.ext <;> rfl

/-- Generate the forward operational GSLT category from queryable worlds. -/
def toOperationalFunctor :
    CategoryTheory.Functor QueryableTheory OperationalTheory where
  obj object := ⟨revisionGSLT object.theory⟩
  map translation := translation.toOperational
  map_id object := by
    apply OperationalTranslation.ext
    rfl
  map_comp earlier later := by
    apply OperationalTranslation.ext
    rfl

/-- Generate exact covered GSLT transports from exact query/revision maps. -/
def toCoveredOperationalFunctor :
    CategoryTheory.Functor ExactQueryableTheory CoveredTheory where
  obj object := ⟨revisionGSLT object.theory⟩
  map translation := translation.toCoveredOperational
  map_id object := by
    apply CoveredTranslation.ext
    rfl
  map_comp earlier later := by
    apply CoveredTranslation.ext
    rfl

/-- A growing family of query/revision theories. -/
abbrev Diagram (Index : Type uIndex)
    [CategoryTheory.Category.{vIndex} Index] :=
  CategoryTheory.Functor Index QueryableTheory

/-- A diagram all of whose theory-stage maps are exact locally. -/
abbrev ExactDiagram (Index : Type uIndex)
    [CategoryTheory.Category.{vIndex} Index] :=
  CategoryTheory.Functor Index ExactQueryableTheory

/-- The generated operational diagram uses precisely the same stage maps. -/
def Diagram.toOperational
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : Diagram Index) :
    IndexedOperational.Diagram Index :=
  CategoryTheory.Functor.comp diagram toOperationalFunctor

/-- Generate the covered operational diagram of an exact revision diagram. -/
def ExactDiagram.toCoveredOperational
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : ExactDiagram Index) :
    IndexedOperational.CoveredDiagram Index :=
  CategoryTheory.Functor.comp diagram toCoveredOperationalFunctor

/-- Transporting a world along a theory-stage map. -/
def transportWorld
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : Diagram Index)
    {source target : Index} (route : source ⟶ target) :
    (diagram.obj source).theory.World → (diagram.obj target).theory.World :=
  (diagram.map route).mapWorld

/-- Querying commutes with theory-stage transport under the declared maps of
queries and observations. -/
theorem query_transport
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : Diagram Index)
    {source target : Index} (route : source ⟶ target)
    (world : (diagram.obj source).theory.World)
    (query : (diagram.obj source).theory.Query) :
    (diagram.obj target).theory.query
        (transportWorld diagram route world)
        ((diagram.map route).mapQuery query) =
      (diagram.map route).mapObservation
        ((diagram.obj source).theory.query world query) :=
  (diagram.map route).query_natural world query

/-- A named world revision generates a semantic fibre step in the operational
diagram. -/
def revisionSemanticStep
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : Diagram Index)
    (stage : Index)
    {revision : (diagram.obj stage).theory.Revision}
    {source target : (diagram.obj stage).theory.World}
    (step : (diagram.obj stage).theory.Step revision source target) :
    SemanticStep (diagram.toOperational.obj stage).theory
      (Quotient.mk _ source) (Quotient.mk _ target) :=
  semanticStep_mk (revision_is_step step)

/-- The generic indexed naturality cell is exactly the square between
changing world state and changing theory stage. -/
def revisionNaturalityDiamond
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : Diagram Index)
    {sourceStage targetStage : Index} (route : sourceStage ⟶ targetStage)
    {revision : (diagram.obj sourceStage).theory.Revision}
    {sourceWorld targetWorld : (diagram.obj sourceStage).theory.World}
    (step : (diagram.obj sourceStage).theory.Step
      revision sourceWorld targetWorld) :=
  IndexedOperational.Command.naturalityDiamond diagram.toOperational route
    (revisionSemanticStep diagram sourceStage step)

/-! ## Compact execution over filtered theory growth -/

/-- A supplied filtered colimit of the generated operational stages.  This
name is deliberately explicit: the present module consumes such a colimit; it
does not claim that every authority category already has the required
colimits. -/
abbrev SuppliedFilteredGrowth
    {J : Type uIndex} [CategoryTheory.SmallCategory J]
    [CategoryTheory.IsFiltered J]
    (stages : Diagram J) :=
  IndexedOperational.FilteredGrowth stages.toOperational

/-- Every finitely presentable operational request into a supplied filtered
query/revision growth factors through one finite theory stage. -/
theorem compact_request_factors_through_world_stage
    {J : Type uIndex} [CategoryTheory.SmallCategory J]
    [CategoryTheory.IsFiltered J]
    {stages : Diagram J}
    (growth : SuppliedFilteredGrowth stages)
    {request : OperationalTheory}
    [CategoryTheory.IsFinitelyPresentable.{uIndex} request]
    (run : request ⟶ growth.cocone.pt) :
    ∃ (stage : J) (through : request ⟶ stages.toOperational.obj stage),
      CategoryTheory.CategoryStruct.comp through
        (growth.cocone.ι.app stage) = run :=
  IndexedOperational.compact_request_factors growth run

end Mettapedia.GSLT.Dynamics.IndexedQueryRevision
