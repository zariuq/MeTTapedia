import Mettapedia.OSLF.Syntax.CategoricalAuthoredReductionObservations
import Mettapedia.OSLF.Syntax.CategoricalAuthoredExtraEvents
import Mathlib.Combinatorics.Quiver.Path

/-!
# Finite paths of individual authored firing events

The internal event object becomes a quiver on program states when the
semantic target is `Type`. An edge contains the particular firing witness,
not merely a proof that some pair of endpoints reduces. Mathlib's path
construction then retains ordered finite histories and their endpoints.
Maps of authored operational models induce maps of these quivers and paths.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalAuthoredEventPaths

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.CategoricalAuthoredRuleInterpretation
open Mettapedia.OSLF.Binding.CategoricalAuthoredProgramCarrierMaps
open Mettapedia.OSLF.Binding.CategoricalAuthoredOperationalModels
open Mettapedia.OSLF.Binding.CategoricalAuthoredExtraEvents
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u
variable {S : Signature} {schema : List (MetaArity S)}
variable {equations : EquationPresentation S schema}
variable {rules : List (IntrinsicScopedConditionalPolynomial.Rule S schema)}
variable {X Y Z : PresentedModel (D := Type u) equations rules}

/-- A one-step edge retains exactly one authored firing with the displayed
program endpoints. Equal endpoint pairs can carry different edges. -/
abbrev EventEdge (X : PresentedModel (D := Type u) equations rules)
    (source target : X.base.carrier.program) : Type u :=
  {event : X.event // X.endpoints event = (source, target)}

/-- The proof-relevant event graph of an authored operational model. -/
abbrev eventQuiver (X : PresentedModel (D := Type u) equations rules) :
    Quiver X.base.carrier.program where
  Hom := EventEdge X

/-- The finite history of particular firings, retaining their order. -/
abbrev EventPath (X : PresentedModel (D := Type u) equations rules)
    (source target : X.base.carrier.program) : Type u :=
  @Quiver.Path X.base.carrier.program (eventQuiver X) source target

/-- A map of program and event objects carries each actual firing to a
firing with the mapped program endpoints. -/
def mapEdge (f : PresentedModel.Hom X Y)
    {source target : X.base.carrier.program}
    (edge : EventEdge X source target) :
    EventEdge Y (f.base.program source) (f.base.program target) := by
  refine ⟨f.event edge.1, ?_⟩
  have square := congrArg
    (fun arrow : X.event ⟶ EndpointPairs Y.base.binding Y.base.carrier =>
      arrow edge.1) f.endpoints_comm
  change Y.endpoints (f.event edge.1) =
    f.base.endpointMap (X.endpoints edge.1) at square
  rw [edge.2] at square
  exact square

/-- Ordinary model maps induce quiver maps; they need not be injective or
surjective on edges. -/
def eventPrefunctor (f : PresentedModel.Hom X Y) :
    @Prefunctor X.base.carrier.program (eventQuiver X)
      Y.base.carrier.program (eventQuiver Y) := by
  letI : Quiver X.base.carrier.program := eventQuiver X
  letI : Quiver Y.base.carrier.program := eventQuiver Y
  exact { obj := fun value => f.base.program value
          map := fun edge => mapEdge f edge }

/-- Map an ordered finite firing history without replacing it by endpoint
reachability. -/
def mapPath (f : PresentedModel.Hom X Y)
    {source target : X.base.carrier.program}
    (path : EventPath X source target) :
    EventPath Y (f.base.program source) (f.base.program target) := by
  letI := eventQuiver X
  letI := eventQuiver Y
  exact (eventPrefunctor f).mapPath path

theorem mapPath_nil (f : PresentedModel.Hom X Y)
    (source : X.base.carrier.program) :
    mapPath f (@Quiver.Path.nil _ (eventQuiver X) source) =
      @Quiver.Path.nil _ (eventQuiver Y) (f.base.program source) := by
  let _ := eventQuiver X
  let _ := eventQuiver Y
  exact Prefunctor.mapPath_nil (eventPrefunctor f) source

/-- Mapping a finite history preserves concatenation and its ordered edge
occurrences. -/
theorem mapPath_comp (f : PresentedModel.Hom X Y)
    {source middle target : X.base.carrier.program}
    (first : EventPath X source middle)
    (second : EventPath X middle target) :
    mapPath f (@Quiver.Path.comp _ (eventQuiver X) _ _ _ first second) =
      @Quiver.Path.comp _ (eventQuiver Y) _ _ _
        (mapPath f first) (mapPath f second) := by
  let _ := eventQuiver X
  let _ := eventQuiver Y
  exact Prefunctor.mapPath_comp (eventPrefunctor f) first second

/-- Identity interpretation leaves the individual event occurrence intact. -/
theorem mapEdge_id (X : PresentedModel (D := Type u) equations rules)
    {source target : X.base.carrier.program}
    (edge : EventEdge X source target) :
    mapEdge (PresentedModel.Hom.id X) edge = edge := by
  apply Subtype.ext
  rfl

/-- Event mapping composes on each particular occurrence. -/
theorem mapEdge_model_comp (f : PresentedModel.Hom X Y)
    (g : PresentedModel.Hom Y Z)
    {source target : X.base.carrier.program}
    (edge : EventEdge X source target) :
    mapEdge (f.comp g) edge = mapEdge g (mapEdge f edge) := by
  apply Subtype.ext
  rfl

/-- The empty and nonempty histories together give functorial action on
finite paths of individual authored firings. -/
theorem mapPath_model_id (X : PresentedModel (D := Type u) equations rules)
    {source target : X.base.carrier.program}
    (path : EventPath X source target) :
    mapPath (PresentedModel.Hom.id X) path = path := by
  let _ := eventQuiver X
  induction path with
  | nil => rfl
  | cons first edge ih =>
      change Quiver.Path.cons (mapPath (PresentedModel.Hom.id X) first)
        (mapEdge (PresentedModel.Hom.id X) edge) =
          Quiver.Path.cons first edge
      rw [ih, mapEdge_id]
      rfl

theorem mapPath_model_comp (f : PresentedModel.Hom X Y)
    (g : PresentedModel.Hom Y Z)
    {source target : X.base.carrier.program}
    (path : EventPath X source target) :
    mapPath (f.comp g) path = mapPath g (mapPath f path) := by
  let _ := eventQuiver X
  let _ := eventQuiver Y
  let _ := eventQuiver Z
  induction path with
  | nil => rfl
  | cons first edge ih =>
      change Quiver.Path.cons (mapPath (f.comp g) first)
        (mapEdge (f.comp g) edge) =
          Quiver.Path.cons (mapPath g (mapPath f first))
            (mapEdge g (mapEdge f edge))
      rw [ih, mapEdge_model_comp]
      rfl

/-- Two separate firings may have exactly the same source and target.
The edge type therefore contains more information than endpoint reachability. -/
def originalEdge (X : PresentedModel (D := Type u) equations [])
    (seed : X.event) :
    EventEdge (withExtraEvent X seed)
      (X.endpoints seed).1 (X.endpoints seed).2 :=
  ⟨Sum.inl seed, rfl⟩

def addedEdge (X : PresentedModel (D := Type u) equations [])
    (seed : X.event) :
    EventEdge (withExtraEvent X seed)
      (X.endpoints seed).1 (X.endpoints seed).2 :=
  ⟨Sum.inr PUnit.unit, rfl⟩

theorem originalEdge_ne_addedEdge
    (X : PresentedModel (D := Type u) equations [])
    (seed : X.event) :
    originalEdge X seed ≠ addedEdge X seed := by
  intro same
  have sameEvent := congrArg Subtype.val same
  cases sameEvent

end Mettapedia.OSLF.Binding.CategoricalAuthoredEventPaths
