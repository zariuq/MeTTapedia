import Mettapedia.GSLT.Dynamics.OrderedOccurrenceBodyAlgebra

/-!
# Transformations between Region/Hole realizations

A Region/Hole presentation can have several physical realizations.  A delayed
source view, an eagerly materialized term, a rollback store, and a persistent
image may all interpret the same typed path without sharing a carrier.

This module gives the comparison its categorical form.  A transformation
provides one component arrow at every source object and a commuting square for
every deterministic region and every explicit hole.  Naturality then extends
from generators to every authored path and to its canonical alternating normal
form.

The hole square is load-bearing.  It permits effectful or observational holes;
it does not require their absence.  A realization may defer construction
through surrounding regions only when crossing each hole and then observing
commutes with the reference realization.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.RegionHolePlan

open OrderedOccurrenceBodyAlgebra

universe uObj uRegion uHole uMeaningObj uMeaning uFinalObj uFinal

/-- A natural transformation between two realizations of one Region/Hole
presentation in a common target category.  Besides ordinary region
naturality, every authored hole has its own commuting square. -/
structure RealizationTransformation
    {Obj : Type uObj}
    {Region : Obj → Obj → Type uRegion}
    {Hole : Obj → Obj → Type uHole}
    {MeaningObj : Type uMeaningObj}
    {Meaning : MeaningObj → MeaningObj → Type uMeaning}
    {source : IndexedCategory Obj Region}
    {target : IndexedCategory MeaningObj Meaning}
    (origin destination : Realization source Hole target) where
  component : (X : Obj) →
    Meaning (origin.objectMap X) (destination.objectMap X)
  region_naturality : ∀ {X Y : Obj} (arrow : Region X Y),
    target.compose (origin.mapRegion arrow) (component Y) =
      target.compose (component X) (destination.mapRegion arrow)
  hole_naturality : ∀ {X Y : Obj} (opening : Hole X Y),
    target.compose (origin.mapHole opening) (component Y) =
      target.compose (component X) (destination.mapHole opening)

namespace RealizationTransformation

variable
    {Obj : Type uObj}
    {Region : Obj → Obj → Type uRegion}
    {Hole : Obj → Obj → Type uHole}
    {MeaningObj : Type uMeaningObj}
    {Meaning : MeaningObj → MeaningObj → Type uMeaning}
    {source : IndexedCategory Obj Region}
    {target : IndexedCategory MeaningObj Meaning}
    {first second third : Realization source Hole target}

/-- Identity comparison for one realization. -/
def identity (realization : Realization source Hole target) :
    RealizationTransformation realization realization where
  component X := target.identity (realization.objectMap X)
  region_naturality arrow := by
    rw [target.compose_identity, target.identity_compose]
  hole_naturality opening := by
    rw [target.compose_identity, target.identity_compose]

/-- Vertical composition of realization transformations. -/
def compose
    (earlier : RealizationTransformation first second)
    (later : RealizationTransformation second third) :
    RealizationTransformation first third where
  component X := target.compose (earlier.component X) (later.component X)
  region_naturality arrow := by
    rw [← target.compose_assoc, earlier.region_naturality arrow,
      target.compose_assoc, later.region_naturality arrow,
      ← target.compose_assoc]
  hole_naturality opening := by
    rw [← target.compose_assoc, earlier.hole_naturality opening,
      target.compose_assoc, later.hole_naturality opening,
      ← target.compose_assoc]

@[simp] theorem identity_component
    (realization : Realization source Hole target) (X : Obj) :
    (identity realization).component X =
      target.identity (realization.objectMap X) :=
  rfl

@[simp] theorem compose_component
    (earlier : RealizationTransformation first second)
    (later : RealizationTransformation second third) (X : Obj) :
    (earlier.compose later).component X =
      target.compose (earlier.component X) (later.component X) :=
  rfl

/-- Naturality on generators extends to every exact authored Region/Hole
path.  In particular, effectful holes need not disappear: their declared
square is composed in authored order with all surrounding region squares. -/
theorem plan_naturality
    (transformation : RealizationTransformation first second)
    {X Y : Obj} (plan : Plan Obj Region Hole X Y) :
    target.compose (Plan.denote first plan) (transformation.component Y) =
      target.compose (transformation.component X)
        (Plan.denote second plan) := by
  induction plan with
  | nil object =>
      rw [Plan.denote, Plan.denote,
        target.identity_compose, target.compose_identity]
  | region arrow rest inductionHypothesis =>
      simp only [Plan.denote]
      rw [target.compose_assoc, inductionHypothesis,
        ← target.compose_assoc,
        transformation.region_naturality arrow,
        target.compose_assoc]
  | hole opening rest inductionHypothesis =>
      simp only [Plan.denote]
      rw [target.compose_assoc, inductionHypothesis,
        ← target.compose_assoc,
        transformation.hole_naturality opening,
        target.compose_assoc]

/-- The same naturality square holds after categorical normalization.  Thus
fusing adjacent regions cannot erase or move an effect/observer hole. -/
theorem normalize_naturality
    (transformation : RealizationTransformation first second)
    {X Y : Obj} (plan : Plan Obj Region Hole X Y) :
    target.compose
        (NormalForm.denote first (normalize source plan))
        (transformation.component Y) =
      target.compose (transformation.component X)
        (NormalForm.denote second (normalize source plan)) := by
  rw [normalize_exact first plan, normalize_exact second plan]
  exact plan_naturality transformation plan

end RealizationTransformation

/-! ## Change of target and locally preordered refinement -/

/-- A functor between indexed categories.  This is deliberately independent
of any Region/Hole presentation: semantic erasure, resource enrichment, and
representation change are all target-level structure. -/
structure IndexedFunctor
    {SourceObj : Type uMeaningObj}
    {SourceHom : SourceObj → SourceObj → Type uMeaning}
    {TargetObj : Type uFinalObj}
    {TargetHom : TargetObj → TargetObj → Type uFinal}
    (sourceCategory : IndexedCategory SourceObj SourceHom)
    (targetCategory : IndexedCategory TargetObj TargetHom) where
  objectMap : SourceObj → TargetObj
  mapArrow : {X Y : SourceObj} →
    SourceHom X Y → TargetHom (objectMap X) (objectMap Y)
  map_identity : ∀ X : SourceObj,
    mapArrow (sourceCategory.identity X) =
      targetCategory.identity (objectMap X)
  map_compose : ∀ {X Y Z : SourceObj}
      (first : SourceHom X Y) (second : SourceHom Y Z),
    mapArrow (sourceCategory.compose first second) =
      targetCategory.compose (mapArrow first) (mapArrow second)

namespace Realization

variable
    {Obj : Type uObj}
    {Region : Obj → Obj → Type uRegion}
    {Hole : Obj → Obj → Type uHole}
    {MeaningObj : Type uMeaningObj}
    {Meaning : MeaningObj → MeaningObj → Type uMeaning}
    {FinalObj : Type uFinalObj}
    {Final : FinalObj → FinalObj → Type uFinal}
    {source : IndexedCategory Obj Region}
    {target : IndexedCategory MeaningObj Meaning}
    {finalTarget : IndexedCategory FinalObj Final}

/-- Postcompose a realization with a target functor. -/
def pushForward
    (functor : IndexedFunctor target finalTarget)
    (realization : Realization source Hole target) :
    Realization source Hole finalTarget where
  objectMap X := functor.objectMap (realization.objectMap X)
  mapRegion arrow := functor.mapArrow (realization.mapRegion arrow)
  mapHole opening := functor.mapArrow (realization.mapHole opening)
  map_identity X := by
    rw [realization.map_identity, functor.map_identity]
  map_compose first second := by
    rw [realization.map_compose, functor.map_compose]

end Realization

namespace RealizationTransformation

variable
    {Obj : Type uObj}
    {Region : Obj → Obj → Type uRegion}
    {Hole : Obj → Obj → Type uHole}
    {MeaningObj : Type uMeaningObj}
    {Meaning : MeaningObj → MeaningObj → Type uMeaning}
    {FinalObj : Type uFinalObj}
    {Final : FinalObj → FinalObj → Type uFinal}
    {source : IndexedCategory Obj Region}
    {target : IndexedCategory MeaningObj Meaning}
    {finalTarget : IndexedCategory FinalObj Final}
    {origin destination : Realization source Hole target}

/-- Naturality is preserved by every functor on the realization target. -/
def pushForward
    (functor : IndexedFunctor target finalTarget)
    (transformation : RealizationTransformation origin destination) :
    RealizationTransformation
      (origin.pushForward functor) (destination.pushForward functor) where
  component X := functor.mapArrow (transformation.component X)
  region_naturality arrow := by
    change finalTarget.compose
        (functor.mapArrow (origin.mapRegion arrow))
        (functor.mapArrow (transformation.component _)) =
      finalTarget.compose
        (functor.mapArrow (transformation.component _))
        (functor.mapArrow (destination.mapRegion arrow))
    rw [← functor.map_compose, transformation.region_naturality arrow,
      functor.map_compose]
  hole_naturality opening := by
    change finalTarget.compose
        (functor.mapArrow (origin.mapHole opening))
        (functor.mapArrow (transformation.component _)) =
      finalTarget.compose
        (functor.mapArrow (transformation.component _))
        (functor.mapArrow (destination.mapHole opening))
    rw [← functor.map_compose, transformation.hole_naturality opening,
      functor.map_compose]

end RealizationTransformation

/-- A local preorder on every hom-family, compatible with composition.

Equality-valued naturality is appropriate for exact semantic observations.
Optimization admission is often locally ordered instead: arrows must retain
the same meaning while improving a selected resource order. -/
structure IndexedPreorderEnrichment
    {Obj : Type uMeaningObj}
    {Hom : Obj → Obj → Type uMeaning}
    (category : IndexedCategory Obj Hom) where
  le : {X Y : Obj} → Hom X Y → Hom X Y → Prop
  le_refl : ∀ {X Y : Obj} (arrow : Hom X Y), le arrow arrow
  le_trans : ∀ {X Y : Obj} {first second third : Hom X Y},
    le first second → le second third → le first third
  compose_mono : ∀ {W X Y : Obj}
      {first first' : Hom W X} {second second' : Hom X Y},
    le first first' → le second second' →
      le (category.compose first second)
        (category.compose first' second')

/-- A locally ordered comparison between two realizations.  The orientation
is `optimized <= reference`; an instantiation chooses what the local order
observes, such as equal results with no greater work. -/
structure RealizationRefinement
    {Obj : Type uObj}
    {Region : Obj → Obj → Type uRegion}
    {Hole : Obj → Obj → Type uHole}
    {MeaningObj : Type uMeaningObj}
    {Meaning : MeaningObj → MeaningObj → Type uMeaning}
    {source : IndexedCategory Obj Region}
    {target : IndexedCategory MeaningObj Meaning}
    (enrichment : IndexedPreorderEnrichment target)
    (optimized reference : Realization source Hole target) where
  component : (X : Obj) →
    Meaning (optimized.objectMap X) (reference.objectMap X)
  region_refinement : ∀ {X Y : Obj} (arrow : Region X Y),
    enrichment.le
      (target.compose (optimized.mapRegion arrow) (component Y))
      (target.compose (component X) (reference.mapRegion arrow))
  hole_refinement : ∀ {X Y : Obj} (opening : Hole X Y),
    enrichment.le
      (target.compose (optimized.mapHole opening) (component Y))
      (target.compose (component X) (reference.mapHole opening))

namespace RealizationRefinement

variable
    {Obj : Type uObj}
    {Region : Obj → Obj → Type uRegion}
    {Hole : Obj → Obj → Type uHole}
    {MeaningObj : Type uMeaningObj}
    {Meaning : MeaningObj → MeaningObj → Type uMeaning}
    {source : IndexedCategory Obj Region}
    {target : IndexedCategory MeaningObj Meaning}
    {enrichment : IndexedPreorderEnrichment target}
    {first second third : Realization source Hole target}

/-- Reflexivity of realization refinement. -/
def identity (realization : Realization source Hole target) :
    RealizationRefinement enrichment realization realization where
  component X := target.identity (realization.objectMap X)
  region_refinement arrow := by
    simpa only [target.compose_identity, target.identity_compose] using
      enrichment.le_refl (realization.mapRegion arrow)
  hole_refinement opening := by
    simpa only [target.compose_identity, target.identity_compose] using
      enrichment.le_refl (realization.mapHole opening)

/-- Transitivity of realization refinement. -/
def compose
    (earlier : RealizationRefinement enrichment first second)
    (later : RealizationRefinement enrichment second third) :
    RealizationRefinement enrichment first third where
  component X := target.compose (earlier.component X) (later.component X)
  region_refinement arrow := by
    apply enrichment.le_trans
      (second := target.compose (earlier.component _)
        (target.compose (second.mapRegion arrow) (later.component _)))
    · simpa only [target.compose_assoc] using
        enrichment.compose_mono
          (earlier.region_refinement arrow)
          (enrichment.le_refl (later.component _))
    · simpa only [target.compose_assoc] using
        enrichment.compose_mono
          (enrichment.le_refl (earlier.component _))
          (later.region_refinement arrow)
  hole_refinement opening := by
    apply enrichment.le_trans
      (second := target.compose (earlier.component _)
        (target.compose (second.mapHole opening) (later.component _)))
    · simpa only [target.compose_assoc] using
        enrichment.compose_mono
          (earlier.hole_refinement opening)
          (enrichment.le_refl (later.component _))
    · simpa only [target.compose_assoc] using
        enrichment.compose_mono
          (enrichment.le_refl (earlier.component _))
          (later.hole_refinement opening)

/-- Generator-level refinement extends to every exact authored path. -/
theorem plan_refinement
    (refinement : RealizationRefinement enrichment first second)
    {X Y : Obj} (plan : Plan Obj Region Hole X Y) :
    enrichment.le
      (target.compose (Plan.denote first plan) (refinement.component Y))
      (target.compose (refinement.component X)
        (Plan.denote second plan)) := by
  induction plan with
  | nil object =>
      simpa only [Plan.denote, target.identity_compose,
        target.compose_identity] using
          enrichment.le_refl (refinement.component object)
  | region arrow rest inductionHypothesis =>
      simp only [Plan.denote]
      apply enrichment.le_trans
        (second := target.compose (first.mapRegion arrow)
          (target.compose (refinement.component _)
            (Plan.denote second rest)))
      · simpa only [target.compose_assoc] using
          enrichment.compose_mono
            (enrichment.le_refl (first.mapRegion arrow))
            inductionHypothesis
      · simpa only [target.compose_assoc] using
          enrichment.compose_mono
            (refinement.region_refinement arrow)
            (enrichment.le_refl (Plan.denote second rest))
  | hole opening rest inductionHypothesis =>
      simp only [Plan.denote]
      apply enrichment.le_trans
        (second := target.compose (first.mapHole opening)
          (target.compose (refinement.component _)
            (Plan.denote second rest)))
      · simpa only [target.compose_assoc] using
          enrichment.compose_mono
            (enrichment.le_refl (first.mapHole opening))
            inductionHypothesis
      · simpa only [target.compose_assoc] using
          enrichment.compose_mono
            (refinement.hole_refinement opening)
            (enrichment.le_refl (Plan.denote second rest))

/-- Refinement is invariant under canonical Region/Hole normalization. -/
theorem normalize_refinement
    (refinement : RealizationRefinement enrichment first second)
    {X Y : Obj} (plan : Plan Obj Region Hole X Y) :
    enrichment.le
      (target.compose
        (NormalForm.denote first (normalize source plan))
        (refinement.component Y))
      (target.compose (refinement.component X)
        (NormalForm.denote second (normalize source plan))) := by
  rw [normalize_exact first plan, normalize_exact second plan]
  exact plan_refinement refinement plan

end RealizationRefinement

/-! ## Effect-observing delayed-source canary -/

namespace EffectCanary

/-- One-object additive source category.  A region label records delayed
deterministic work; a hole label below records an observable effect token. -/
def additiveCategory :
    IndexedCategory Unit (fun _ _ : Unit => Nat) where
  identity _ := 0
  compose first second := first + second
  identity_compose arrow := Nat.zero_add arrow
  compose_identity arrow := Nat.add_zero arrow
  compose_assoc first second third := Nat.add_assoc first second third

/-- A delayed carrier retains deterministic additions until an observation
boundary forces them. -/
structure DelayedState where
  base : Nat
  pending : Nat
  trace : List Nat
  deriving DecidableEq, Repr

/-- The eager carrier always stores the current value. -/
structure EagerState where
  value : Nat
  trace : List Nat
  deriving DecidableEq, Repr

def forceState (state : DelayedState) : EagerState :=
  { value := state.base + state.pending
    trace := state.trace }

def delayedRegion (amount : Nat) : Segment DelayedState DelayedState :=
  deterministic fun state =>
    { state with pending := state.pending + amount }

def eagerRegion (amount : Nat) : Segment EagerState EagerState :=
  deterministic fun state =>
    { state with value := state.value + amount }

/-- The hole observes the current value together with its token.  The delayed
realization must therefore force pending work exactly at this boundary. -/
def delayedHole (token : Nat) : Segment DelayedState DelayedState :=
  fun state =>
    let value := state.base + state.pending
    [{ base := value
       pending := 0
       trace := state.trace ++ [value + token] }]

def eagerHole (token : Nat) : Segment EagerState EagerState :=
  fun state =>
    [{ state with trace := state.trace ++ [state.value + token] }]

def delayedRealization :
    Realization additiveCategory (fun _ _ : Unit => Nat)
      occurrenceKleisliCategory where
  objectMap _ := DelayedState
  mapRegion := delayedRegion
  mapHole := delayedHole
  map_identity _ := by
    funext state
    cases state
    rfl
  map_compose first second := by
    funext state
    cases state
    simp [additiveCategory, occurrenceKleisliCategory, delayedRegion,
      deterministic, thenSegment, run, Nat.add_assoc]

def eagerRealization :
    Realization additiveCategory (fun _ _ : Unit => Nat)
      occurrenceKleisliCategory where
  objectMap _ := EagerState
  mapRegion := eagerRegion
  mapHole := eagerHole
  map_identity _ := by
    funext state
    cases state
    rfl
  map_compose first second := by
    funext state
    cases state
    simp [additiveCategory, occurrenceKleisliCategory, eagerRegion,
      deterministic, thenSegment, run, Nat.add_assoc]

/-- Forcing is the component arrow from delayed to eager execution. -/
def forceSegment : Segment DelayedState EagerState :=
  deterministic forceState

/-- Delayed deterministic regions and effect-observing holes both commute
with forcing. -/
def delayedToEager :
    RealizationTransformation delayedRealization eagerRealization where
  component _ := forceSegment
  region_naturality amount := by
    funext state
    cases state with
    | mk base pending trace =>
        change
          [({ value := base + (pending + amount), trace := trace } :
              EagerState)] =
            [({ value := (base + pending) + amount, trace := trace } :
              EagerState)]
        rw [Nat.add_assoc]
  hole_naturality token := by
    funext state
    cases state with
    | mk base pending trace =>
        change
          [({ value := (base + pending) + 0,
              trace := trace ++ [(base + pending) + token] } :
              EagerState)] =
            [({ value := base + pending,
                trace := trace ++ [(base + pending) + token] } :
                EagerState)]
        simp

/-- A region, a genuinely observing hole, and a later region. -/
def effectfulPlan :
    Plan Unit (fun _ _ : Unit => Nat) (fun _ _ : Unit => Nat) () () :=
  Plan.region (X := ()) (Y := ()) (Z := ()) 2
    (Plan.hole (X := ()) (Y := ()) (Z := ()) 7
      (Plan.region (X := ()) (Y := ()) (Z := ()) 3 (Plan.nil ())))

def delayedEntrance : DelayedState :=
  { base := 10, pending := 0, trace := [] }

/-- Local generator squares imply exact end-to-end execution even though the
plan contains an effect-observing hole. -/
theorem effectful_plan_exact :
    occurrenceKleisliCategory.compose
        (Plan.denote delayedRealization effectfulPlan)
        forceSegment delayedEntrance =
      occurrenceKleisliCategory.compose forceSegment
        (Plan.denote eagerRealization effectfulPlan) delayedEntrance := by
  have naturality := RealizationTransformation.plan_naturality
    (first := delayedRealization) (second := eagerRealization)
    delayedToEager effectfulPlan
  exact congrFun naturality delayedEntrance

/-- The concrete observation sees the value after the first region, then the
final value after the second region. -/
theorem effectful_plan_result :
    occurrenceKleisliCategory.compose
        (Plan.denote delayedRealization effectfulPlan)
        forceSegment delayedEntrance =
      [{ value := 15, trace := [19] }] := by
  simp [effectfulPlan, delayedRealization, forceSegment, forceState,
    delayedRegion, delayedHole, delayedEntrance, Plan.denote,
    occurrenceKleisliCategory, deterministic, thenSegment, run]

/-- Negative control: recording an effect without forcing pending work does
not satisfy the hole square and changes the visible trace. -/
def unforcedHole (token : Nat) : Segment DelayedState DelayedState :=
  fun state =>
    [{ state with trace := state.trace ++ [state.base + token] }]

theorem unforced_hole_changes_observation :
    occurrenceKleisliCategory.compose (unforcedHole 7) forceSegment
        { base := 10, pending := 2, trace := [] } ≠
      occurrenceKleisliCategory.compose forceSegment (eagerHole 7)
        { base := 10, pending := 2, trace := [] } := by
  decide

end EffectCanary

/-! ## Work-refinement canary -/

namespace WorkCanary

/-- One arrow carries both its semantic action and a selected exact-work
grade.  The grade is additional structure; erasing it leaves the same bare
semantic arrow. -/
structure WorkArrow where
  semantic : Nat
  work : Nat
  deriving DecidableEq, Repr

def workCategory :
    IndexedCategory Unit (fun _ _ : Unit => WorkArrow) where
  identity _ := { semantic := 0, work := 0 }
  compose first second :=
    { semantic := first.semantic + second.semantic
      work := first.work + second.work }
  identity_compose arrow := by
    cases arrow
    simp
  compose_identity arrow := by
    cases arrow
    simp
  compose_assoc first second third := by
    cases first
    cases second
    cases third
    simp [Nat.add_assoc]

/-- Equal semantics and no greater work form a local compositional preorder. -/
def workEnrichment : IndexedPreorderEnrichment workCategory where
  le first second :=
    first.semantic = second.semantic ∧ first.work ≤ second.work
  le_refl arrow := ⟨rfl, Nat.le_refl arrow.work⟩
  le_trans firstSecond secondThird :=
    ⟨firstSecond.1.trans secondThird.1,
      Nat.le_trans firstSecond.2 secondThird.2⟩
  compose_mono := by
    intro W X Y first first' second second' firstLe secondLe
    constructor
    · simp only [workCategory]
      rw [firstLe.1, secondLe.1]
    · simp only [workCategory]
      exact Nat.add_le_add firstLe.2 secondLe.2

/-- The optimized realization performs one unit of work per region unit. -/
def optimizedRealization :
    Realization EffectCanary.additiveCategory
      (fun _ _ : Unit => Nat) workCategory where
  objectMap _ := ()
  mapRegion amount := { semantic := amount, work := amount }
  mapHole token := { semantic := token, work := 1 }
  map_identity _ := rfl
  map_compose _ _ := rfl

/-- The reference realization has the same meaning and holes, but performs
two work units per deterministic region unit. -/
def referenceRealization :
    Realization EffectCanary.additiveCategory
      (fun _ _ : Unit => Nat) workCategory where
  objectMap _ := ()
  mapRegion amount := { semantic := amount, work := amount * 2 }
  mapHole token := { semantic := token, work := 1 }
  map_identity _ := rfl
  map_compose first second := by
    simp [EffectCanary.additiveCategory, workCategory, Nat.add_mul]

/-- A semantically equal but more expensive realization. -/
def slowerRealization :
    Realization EffectCanary.additiveCategory
      (fun _ _ : Unit => Nat) workCategory where
  objectMap _ := ()
  mapRegion amount := { semantic := amount, work := amount * 3 }
  mapHole token := { semantic := token, work := 1 }
  map_identity _ := rfl
  map_compose first second := by
    simp [EffectCanary.additiveCategory, workCategory, Nat.add_mul]

/-- The optimized realization refines the reference in the selected local
work order, including at explicit holes. -/
def optimizedToReference :
    RealizationRefinement workEnrichment
      optimizedRealization referenceRealization where
  component _ := { semantic := 0, work := 0 }
  region_refinement amount := by
    simp [workEnrichment, workCategory, optimizedRealization,
      referenceRealization]
    omega
  hole_refinement token := by
    simp [workEnrichment, workCategory, optimizedRealization,
      referenceRealization]

def mixedPlan :
    Plan Unit (fun _ _ : Unit => Nat) (fun _ _ : Unit => Nat) () () :=
  .region (X := ()) (Y := ()) (Z := ()) 3
    (.hole (X := ()) (Y := ()) (Z := ()) 9
      (.region (X := ()) (Y := ()) (Z := ()) 2 (.nil ())))

/-- Generator-local work refinement composes through a mixed Region/Hole
path. -/
theorem mixedPlan_refines :
    workEnrichment.le (X := ()) (Y := ())
      (workCategory.compose (X := ()) (Y := ()) (Z := ())
        (Plan.denote optimizedRealization mixedPlan)
        (optimizedToReference.component ()))
      (workCategory.compose (X := ()) (Y := ()) (Z := ())
        (optimizedToReference.component ())
        (Plan.denote referenceRealization mixedPlan)) :=
  RealizationRefinement.plan_refinement optimizedToReference mixedPlan

/-- The concrete receipt exposes the strict improvement. -/
theorem mixedPlan_work_receipt :
    (Plan.denote optimizedRealization mixedPlan).work = 6 ∧
      (Plan.denote referenceRealization mixedPlan).work = 11 := by
  simp [mixedPlan, optimizedRealization, referenceRealization,
    Plan.denote, workCategory]

/-- Forget the selected work grade while retaining semantic action. -/
def eraseWork : IndexedFunctor workCategory EffectCanary.additiveCategory where
  objectMap _ := ()
  mapArrow arrow := arrow.semantic
  map_identity _ := rfl
  map_compose _ _ := rfl

/-- After work erasure, even the slower realization is naturally identical
to the reference realization. -/
def slowerToReferenceAfterErasure :
    RealizationTransformation
      (slowerRealization.pushForward eraseWork)
      (referenceRealization.pushForward eraseWork) where
  component _ := 0
  region_naturality amount := by
    simp [Realization.pushForward, eraseWork, slowerRealization,
      referenceRealization, EffectCanary.additiveCategory, workCategory]
  hole_naturality token := by
    simp [Realization.pushForward, eraseWork, slowerRealization,
      referenceRealization, EffectCanary.additiveCategory, workCategory]

/-- Negative control: semantic naturality after erasure cannot manufacture
a profitability refinement.  At one region unit the slower realization pays
three units and the reference pays two, independently of the component. -/
theorem no_slower_work_refinement :
    ¬ Nonempty (RealizationRefinement workEnrichment
      slowerRealization referenceRealization) := by
  rintro ⟨refinement⟩
  have comparison :=
    refinement.region_refinement (X := ()) (Y := ()) 1
  have workBound := comparison.2
  change 3 + (refinement.component ()).work ≤
    (refinement.component ()).work + 2 at workBound
  omega

end WorkCanary

/-! ## Lifetime-indexed hole canary -/

namespace LifetimeCanary

/-- A delayed value is either borrowed from a bounded region or rooted for
escape beyond that region. -/
inductive Residence where
  | borrowed
  | rooted
  deriving DecidableEq, Repr

/-- Concrete evidence authorizing a borrowed value to become rooted. -/
structure RootToken where
  generation : Nat
  deriving DecidableEq, Repr

/-- Lifetime changes are typed arrows.  There is no arrow which forgets a
root, and acquisition carries explicit evidence. -/
inductive LifetimeRegion : Residence → Residence → Type where
  | borrowedIdentity : LifetimeRegion .borrowed .borrowed
  | rootedIdentity : LifetimeRegion .rooted .rooted
  | acquire (token : RootToken) : LifetimeRegion .borrowed .rooted

def lifetimeIdentity : (residence : Residence) →
    LifetimeRegion residence residence
  | .borrowed => .borrowedIdentity
  | .rooted => .rootedIdentity

def lifetimeCompose {X Y Z : Residence} :
    LifetimeRegion X Y → LifetimeRegion Y Z → LifetimeRegion X Z
  | .borrowedIdentity, .borrowedIdentity => .borrowedIdentity
  | .borrowedIdentity, .acquire token => .acquire token
  | .rootedIdentity, .rootedIdentity => .rootedIdentity
  | .acquire token, .rootedIdentity => .acquire token

def lifetimeCategory : IndexedCategory Residence LifetimeRegion where
  identity := lifetimeIdentity
  compose := lifetimeCompose
  identity_compose arrow := by cases arrow <;> rfl
  compose_identity arrow := by cases arrow <;> rfl
  compose_assoc first second third := by
    cases first <;> cases second <;> cases third <;> rfl

/-- Publication is an explicit hole and requires a rooted input. -/
inductive PublicationHole : Residence → Residence → Type where
  | publish : PublicationHole .rooted .rooted

/-- A lawful escaping plan first acquires a root, then crosses the publication
hole. -/
def rootedPublicationPlan :
    Plan Residence LifetimeRegion PublicationHole .borrowed .rooted :=
  .region (X := Residence.borrowed) (Y := Residence.rooted)
    (Z := Residence.rooted) (.acquire { generation := 7 })
    (.hole (X := Residence.rooted) (Y := Residence.rooted)
      (Z := Residence.rooted) .publish (.nil Residence.rooted))

theorem rooted_publication_has_one_hole :
    rootedPublicationPlan.holeCount = 1 :=
  by simp [rootedPublicationPlan, Plan.holeCount, Plan.holeTrace]

/-- Negative control: publication directly from borrowed state is not merely
rejected dynamically; the required hole has no inhabitant. -/
theorem borrowed_publication_uninhabited :
    ¬ Nonempty (PublicationHole .borrowed .borrowed) := by
  rintro ⟨opening⟩
  nomatch opening

end LifetimeCanary

#print axioms RealizationTransformation.plan_naturality
#print axioms RealizationTransformation.normalize_naturality
#print axioms RealizationRefinement.plan_refinement
#print axioms RealizationRefinement.normalize_refinement
#print axioms EffectCanary.effectful_plan_exact
#print axioms EffectCanary.effectful_plan_result
#print axioms EffectCanary.unforced_hole_changes_observation
#print axioms WorkCanary.mixedPlan_refines
#print axioms WorkCanary.mixedPlan_work_receipt
#print axioms WorkCanary.no_slower_work_refinement
#print axioms LifetimeCanary.rooted_publication_has_one_hole
#print axioms LifetimeCanary.borrowed_publication_uninhabited

end Mettapedia.GSLT.Dynamics.RegionHolePlan
