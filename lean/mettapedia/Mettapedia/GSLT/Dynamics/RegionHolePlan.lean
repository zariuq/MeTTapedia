import Mathlib.Data.List.Basic

/-!
# Typed region/hole plans

A region/hole plan is an ordered typed path whose deterministic arrows may be
composed and whose suspension holes must remain explicit.  The construction is
independent of clauses, equations, a particular evaluator, and a physical
instruction format.

The source category may carry any additional structure in its objects and
arrows: live support, revision authority, effects, observations, ownership, or
exact work grades.  Normalization uses only its category laws.  It fuses every
maximal run of region arrows and preserves the exact ordered occurrence trace
of holes.

`Realization` is an identity-independent interpretation into another indexed
category.  Its object map and region functor laws keep semantic meaning
separate from the source presentation, while each hole receives an explicit
interpretation.  The resulting denotation is the unique fold with those
actions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.RegionHolePlan

universe uObj uRegion uHole uMeaningObj uMeaning

/-! ## Categories presented by indexed hom-families -/

/-- A category whose objects and hom-family are explicit parameters.

This form is useful when several categories share the same object language:
it avoids installing competing global `Category` instances while retaining
the ordinary identity and associativity laws. -/
structure IndexedCategory
    (Obj : Type uObj) (Hom : Obj → Obj → Type uRegion) where
  identity : (X : Obj) → Hom X X
  compose : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  identity_compose : ∀ {X Y : Obj} (arrow : Hom X Y),
    compose (identity X) arrow = arrow
  compose_identity : ∀ {X Y : Obj} (arrow : Hom X Y),
    compose arrow (identity Y) = arrow
  compose_assoc : ∀ {W X Y Z : Obj}
      (first : Hom W X) (second : Hom X Y) (third : Hom Y Z),
    compose (compose first second) third = compose first (compose second third)

/-! ## A canonical category of deterministic partial arrows -/

/-- The result of one deterministic partial arrow.

`absent` is an ordinary semantic failure (for example, a pattern mismatch),
whereas `fault` is an explicit incomplete result (for example, exhausted
capacity).  Keeping these constructors distinct prevents a physical refusal
from being mistaken for a logical negative answer. -/
inductive PartialResult (Failure : Type uHole) (Value : Type uObj) where
  | absent
  | value (result : Value)
  | fault (reason : Failure)
deriving Repr

/-- A deterministic partial arrow with typed incomplete results. -/
abbrev PartialArrow (Failure : Type uHole)
    (Source Target : Type uObj) := Source -> PartialResult Failure Target

namespace PartialArrow

variable {Failure : Type uHole}
  {Source Middle Target Final : Type uObj}

/-- Identity returns its input without manufacturing failure or absence. -/
def identity (Source : Type uObj) : PartialArrow Failure Source Source :=
  PartialResult.value

/-- Sequential composition propagates semantic absence and typed faults;
only a produced value enters the second arrow. -/
def compose
    (first : PartialArrow Failure Source Middle)
    (second : PartialArrow Failure Middle Target) :
    PartialArrow Failure Source Target :=
  fun input =>
    match first input with
    | .absent => .absent
    | .value middle => second middle
    | .fault reason => .fault reason

@[simp] theorem identity_compose
    (arrow : PartialArrow Failure Source Target) :
    compose (identity Source) arrow = arrow := by
  rfl

@[simp] theorem compose_identity
    (arrow : PartialArrow Failure Source Target) :
    compose arrow (identity Target) = arrow := by
  funext input
  cases observed : arrow input <;> simp [compose, identity, observed]

theorem compose_assoc
    (first : PartialArrow Failure Source Middle)
    (second : PartialArrow Failure Middle Target)
    (third : PartialArrow Failure Target Final) :
    compose (compose first second) third =
      compose first (compose second third) := by
  funext input
  cases firstObserved : first input with
  | absent => simp [compose, firstObserved]
  | value middle =>
      cases secondObserved : second middle <;>
        simp [compose, firstObserved, secondObserved]
  | fault reason => simp [compose, firstObserved]

/-- Deterministic partial computations form an indexed category.  This is the
runtime-relevant instance of the abstract Region/Hole construction: matching,
guards, scalar regions, and constructors compose here until an explicit hole
returns control to the scheduler. -/
def category (Failure : Type uHole) :
    IndexedCategory (Type uObj) (PartialArrow Failure) where
  identity := identity
  compose := compose
  identity_compose := identity_compose
  compose_identity := compose_identity
  compose_assoc := compose_assoc

/-- A fault in the first arrow cannot be hidden by later specialization. -/
theorem fault_compose
    (reason : Failure)
    (later : PartialArrow Failure Middle Target) :
    compose (fun _ : Source => .fault reason) later =
      (fun _ => .fault reason) := by
  rfl

/-- An ordinary absence also bypasses later work, but remains observably
different from a capacity fault. -/
theorem absent_compose
    (later : PartialArrow Failure Middle Target) :
    compose (fun _ : Source => .absent) later =
      (fun _ => .absent) := by
  rfl

end PartialArrow

/-! ## The free typed region/hole path -/

/-- A typed source presentation.  Regions and holes retain authored order and
occurrence multiplicity; no constructor silently identifies either kind. -/
inductive Plan
    (Obj : Type uObj)
    (Region : Obj → Obj → Type uRegion)
    (Hole : Obj → Obj → Type uHole) :
    Obj → Obj → Type (max uObj uRegion uHole) where
  | nil (X : Obj) : Plan Obj Region Hole X X
  | region {X Y Z : Obj} (arrow : Region X Y)
      (rest : Plan Obj Region Hole Y Z) : Plan Obj Region Hole X Z
  | hole {X Y Z : Obj} (opening : Hole X Y)
      (rest : Plan Obj Region Hole Y Z) : Plan Obj Region Hole X Z

/-- One hole occurrence with its exact typed endpoints and source label. -/
abbrev HoleOccurrence
    (Obj : Type uObj) (Hole : Obj → Obj → Type uHole) :=
  Σ source : Obj, Σ target : Obj, Hole source target

namespace Plan

variable {Obj : Type uObj}
  {Region : Obj → Obj → Type uRegion}
  {Hole : Obj → Obj → Type uHole}
  {W X Y Z : Obj}

/-- Concatenate two typed source paths. -/
def append : {W X Y : Obj} →
    Plan Obj Region Hole W X →
      Plan Obj Region Hole X Y → Plan Obj Region Hole W Y
  | _, _, _, .nil _, later => later
  | _, _, _, .region arrow rest, later =>
      .region arrow (append rest later)
  | _, _, _, .hole opening rest, later =>
      .hole opening (append rest later)

@[simp] theorem nil_append (later : Plan Obj Region Hole X Y) :
    (Plan.nil X).append later = later :=
  rfl

@[simp] theorem append_nil (plan : Plan Obj Region Hole X Y) :
    plan.append (Plan.nil Y) = plan := by
  induction plan with
  | nil => rfl
  | region arrow rest inductionHypothesis =>
      simp [append, inductionHypothesis]
  | hole opening rest inductionHypothesis =>
      simp [append, inductionHypothesis]

theorem append_assoc
    (first : Plan Obj Region Hole W X)
    (second : Plan Obj Region Hole X Y)
    (third : Plan Obj Region Hole Y Z) :
    (first.append second).append third = first.append (second.append third) := by
  induction first with
  | nil => rfl
  | region arrow rest inductionHypothesis =>
      simp [append, inductionHypothesis]
  | hole opening rest inductionHypothesis =>
      simp [append, inductionHypothesis]

/-- Exact authored hole occurrences, retaining order and duplicates. -/
def holeTrace : {X Y : Obj} →
    Plan Obj Region Hole X Y → List (HoleOccurrence Obj Hole)
  | _, _, .nil _ => []
  | _, _, .region _ rest => holeTrace rest
  | _, _, .hole (X := source) (Y := target) opening rest =>
      ⟨source, target, opening⟩ :: holeTrace rest

/-- The number of genuine suspension holes. -/
def holeCount (plan : Plan Obj Region Hole X Y) : Nat :=
  plan.holeTrace.length

@[simp] theorem holeTrace_append
    (first : Plan Obj Region Hole W X)
    (second : Plan Obj Region Hole X Y) :
    (first.append second).holeTrace = first.holeTrace ++ second.holeTrace := by
  induction first with
  | nil => rfl
  | region arrow rest inductionHypothesis =>
      simp [append, holeTrace, inductionHypothesis]
  | hole opening rest inductionHypothesis =>
      simp [append, holeTrace, inductionHypothesis]

end Plan

/-! ## Realizations and independent denotation -/

/-- Interpret region arrows functorially and interpret each hole explicitly
in a target category.  The target objects need not be the source objects. -/
structure Realization
    {Obj : Type uObj}
    {Region : Obj → Obj → Type uRegion}
    (source : IndexedCategory Obj Region)
    (Hole : Obj → Obj → Type uHole)
    {MeaningObj : Type uMeaningObj}
    {Meaning : MeaningObj → MeaningObj → Type uMeaning}
    (target : IndexedCategory MeaningObj Meaning) where
  objectMap : Obj → MeaningObj
  mapRegion : {X Y : Obj} →
    Region X Y → Meaning (objectMap X) (objectMap Y)
  mapHole : {X Y : Obj} →
    Hole X Y → Meaning (objectMap X) (objectMap Y)
  map_identity : ∀ X : Obj,
    mapRegion (source.identity X) = target.identity (objectMap X)
  map_compose : ∀ {X Y Z : Obj}
      (first : Region X Y) (second : Region Y Z),
    mapRegion (source.compose first second) =
      target.compose (mapRegion first) (mapRegion second)

namespace Plan

variable {Obj : Type uObj}
  {Region : Obj → Obj → Type uRegion}
  {Hole : Obj → Obj → Type uHole}
  {MeaningObj : Type uMeaningObj}
  {Meaning : MeaningObj → MeaningObj → Type uMeaning}
  {source : IndexedCategory Obj Region}
  {target : IndexedCategory MeaningObj Meaning}
  (realization : Realization source Hole target)

/-- Fold a source presentation through an independently supplied
realization. -/
def denote : {X Y : Obj} → Plan Obj Region Hole X Y →
    Meaning (realization.objectMap X) (realization.objectMap Y)
  | X, _, .nil _ => target.identity (realization.objectMap X)
  | _, _, .region arrow rest =>
      target.compose (realization.mapRegion arrow) (denote rest)
  | _, _, .hole opening rest =>
      target.compose (realization.mapHole opening) (denote rest)

@[simp] theorem denote_nil (X : Obj) :
    denote realization (Plan.nil X) =
      target.identity (realization.objectMap X) :=
  rfl

theorem denote_append
    {W X Y : Obj}
    (first : Plan Obj Region Hole W X)
    (second : Plan Obj Region Hole X Y) :
    denote realization (first.append second) =
      target.compose (denote realization first) (denote realization second) := by
  induction first with
  | nil =>
      rw [nil_append, denote_nil, target.identity_compose]
  | region arrow rest inductionHypothesis =>
      simp only [append, denote]
      rw [inductionHypothesis, target.compose_assoc]
  | hole opening rest inductionHypothesis =>
      simp only [append, denote]
      rw [inductionHypothesis, target.compose_assoc]

/-- Universal property: the denotation fold is the unique interpretation
with the declared actions on identity, region, and hole constructors. -/
theorem denote_unique
    (candidate : {X Y : Obj} → Plan Obj Region Hole X Y →
      Meaning (realization.objectMap X) (realization.objectMap Y))
    (candidate_nil : ∀ X : Obj,
      candidate (Plan.nil X) = target.identity (realization.objectMap X))
    (candidate_region : ∀ {X Y Z : Obj} (arrow : Region X Y)
        (rest : Plan Obj Region Hole Y Z),
      candidate (.region arrow rest) =
        target.compose (realization.mapRegion arrow) (candidate rest))
    (candidate_hole : ∀ {X Y Z : Obj} (opening : Hole X Y)
        (rest : Plan Obj Region Hole Y Z),
      candidate (.hole opening rest) =
        target.compose (realization.mapHole opening) (candidate rest))
    {X Y : Obj} (plan : Plan Obj Region Hole X Y) :
    candidate plan = denote realization plan := by
  induction plan with
  | nil X => exact candidate_nil X
  | region arrow rest inductionHypothesis =>
      rw [candidate_region, denote, inductionHypothesis]
  | hole opening rest inductionHypothesis =>
      rw [candidate_hole, denote, inductionHypothesis]

end Plan

/-! ## Canonical alternating normal form -/

/-- Exactly one fused region before the first hole and after every hole.
Adjacent regions and adjacent holes are unrepresentable. -/
inductive NormalForm
    {Obj : Type uObj}
    (Region : Obj → Obj → Type uRegion)
    (Hole : Obj → Obj → Type uHole) :
    Obj → Obj → Type (max uObj uRegion uHole) where
  | final {X Y : Obj} (region : Region X Y) : NormalForm Region Hole X Y
  | step {W X Y Z : Obj} (region : Region W X) (opening : Hole X Y)
      (rest : NormalForm Region Hole Y Z) : NormalForm Region Hole W Z

namespace NormalForm

variable {Obj : Type uObj}
  {Region : Obj → Obj → Type uRegion}
  {Hole : Obj → Obj → Type uHole}
  (source : IndexedCategory Obj Region)

/-- Fuse a region into the unique first region of a normal form. -/
def prependRegion {W X Y : Obj} (first : Region W X) :
    NormalForm Region Hole X Y → NormalForm Region Hole W Y
  | .final second => .final (source.compose first second)
  | .step second opening rest =>
      .step (source.compose first second) opening rest

/-- Compose two normal forms, fusing only the region pair at their join. -/
def compose : {W X Y : Obj} →
    NormalForm Region Hole W X → NormalForm Region Hole X Y →
      NormalForm Region Hole W Y
  | _, _, _, .final first, later => prependRegion source first later
  | _, _, _, .step first opening rest, later =>
      .step first opening (compose rest later)

/-- Reify the alternating form as an exact typed source path. -/
def toPlan : {X Y : Obj} →
    NormalForm Region Hole X Y → Plan Obj Region Hole X Y
  | _, _, .final region => .region region (.nil _)
  | _, _, .step region opening rest =>
      .region region (.hole opening (toPlan rest))

/-- Exact ordered hole occurrences in a normal form. -/
def holeTrace : {X Y : Obj} → NormalForm Region Hole X Y →
    List (HoleOccurrence Obj Hole)
  | _, _, .final _ => []
  | _, _, .step (X := sourceObject) (Y := targetObject)
      _ opening rest =>
      ⟨sourceObject, targetObject, opening⟩ :: holeTrace rest

def holeCount {X Y : Obj} (normal : NormalForm Region Hole X Y) : Nat :=
  normal.holeTrace.length

/-- A normal form has exactly one region more than holes. -/
def regionCount {X Y : Obj} (normal : NormalForm Region Hole X Y) : Nat :=
  normal.holeCount + 1

end NormalForm

/-! ## Normalization -/

variable {Obj : Type uObj}
  {Region : Obj → Obj → Type uRegion}
  {Hole : Obj → Obj → Type uHole}

/-- Normalize a typed source path.  Regions compose; holes are retained as
exact ordered occurrences. -/
def normalize (source : IndexedCategory Obj Region) :
    {X Y : Obj} → Plan Obj Region Hole X Y → NormalForm Region Hole X Y
  | X, _, .nil _ => .final (source.identity X)
  | _, _, .region arrow rest =>
      (normalize source rest).prependRegion source arrow
  | _, _, .hole opening rest =>
      .step (source.identity _) opening (normalize source rest)

namespace NormalForm

variable (source : IndexedCategory Obj Region)

@[simp] theorem prepend_identity {X Y : Obj}
    (normal : NormalForm Region Hole X Y) :
    normal.prependRegion source (source.identity X) = normal := by
  cases normal with
  | final region => simp [prependRegion, source.identity_compose]
  | step region opening rest =>
      simp [prependRegion, source.identity_compose]

theorem prepend_assoc {V W X Y : Obj}
    (first : Region V W) (second : Region W X)
    (normal : NormalForm Region Hole X Y) :
    normal.prependRegion source (source.compose first second) =
      (normal.prependRegion source second).prependRegion source first := by
  cases normal with
  | final region => simp [prependRegion, source.compose_assoc]
  | step region opening rest =>
      simp [prependRegion, source.compose_assoc]

@[simp] theorem identity_compose {X Y : Obj}
    (normal : NormalForm Region Hole X Y) :
    compose source (.final (source.identity X)) normal = normal := by
  exact prepend_identity source normal

@[simp] theorem compose_identity {X Y : Obj}
    (normal : NormalForm Region Hole X Y) :
    compose source normal (.final (source.identity Y)) = normal := by
  induction normal with
  | final region => simp [compose, prependRegion, source.compose_identity]
  | step region opening rest inductionHypothesis =>
      simp [compose, inductionHypothesis]

theorem prepend_compose {V W X Y : Obj}
    (region : Region V W)
    (first : NormalForm Region Hole W X)
    (second : NormalForm Region Hole X Y) :
    compose source (first.prependRegion source region) second =
      (compose source first second).prependRegion source region := by
  induction first with
  | final next =>
      simp only [prependRegion, compose]
      exact prepend_assoc source region next second
  | step next opening rest inductionHypothesis =>
      simp [prependRegion, compose]

theorem compose_assoc {V W X Y : Obj}
    (first : NormalForm Region Hole V W)
    (second : NormalForm Region Hole W X)
    (third : NormalForm Region Hole X Y) :
    compose source (compose source first second) third =
      compose source first (compose source second third) := by
  induction first with
  | final region => exact prepend_compose source region second third
  | step region opening rest inductionHypothesis =>
      simp [compose, inductionHypothesis]

theorem toPlan_holeTrace {X Y : Obj}
    (normal : NormalForm Region Hole X Y) :
    normal.toPlan.holeTrace = normal.holeTrace := by
  induction normal with
  | final region => rfl
  | step region opening rest inductionHypothesis =>
      simp [toPlan, Plan.holeTrace, holeTrace, inductionHypothesis]

end NormalForm

/-! ## Independent normalization theorem -/

namespace NormalForm

variable {MeaningObj : Type uMeaningObj}
  {Meaning : MeaningObj → MeaningObj → Type uMeaning}
  {source : IndexedCategory Obj Region}
  {target : IndexedCategory MeaningObj Meaning}
  (realization : Realization source Hole target)

/-- Interpret a canonical alternating form. -/
def denote : {X Y : Obj} → NormalForm Region Hole X Y →
    Meaning (realization.objectMap X) (realization.objectMap Y)
  | _, _, .final region => realization.mapRegion region
  | _, _, .step region opening rest =>
      target.compose (realization.mapRegion region)
        (target.compose (realization.mapHole opening) (denote rest))

theorem denote_prependRegion {W X Y : Obj}
    (region : Region W X) (normal : NormalForm Region Hole X Y) :
    denote realization (normal.prependRegion source region) =
      target.compose (realization.mapRegion region) (denote realization normal) := by
  cases normal with
  | final next =>
      simp only [prependRegion, denote, realization.map_compose]
  | step next opening rest =>
      simp only [prependRegion, denote, realization.map_compose]
      rw [target.compose_assoc]

theorem denote_compose {W X Y : Obj}
    (first : NormalForm Region Hole W X)
    (second : NormalForm Region Hole X Y) :
    denote realization (NormalForm.compose source first second) =
      target.compose (denote realization first) (denote realization second) := by
  induction first with
  | final region => exact denote_prependRegion realization region second
  | step region opening rest inductionHypothesis =>
      simp only [NormalForm.compose, denote]
      rw [inductionHypothesis, target.compose_assoc, target.compose_assoc]

end NormalForm

/-- Categorical normalization preserves the independently defined denotation
for every lawful realization. -/
theorem normalize_exact
    {MeaningObj : Type uMeaningObj}
    {Meaning : MeaningObj → MeaningObj → Type uMeaning}
    {source : IndexedCategory Obj Region}
    {target : IndexedCategory MeaningObj Meaning}
    (realization : Realization source Hole target)
    {X Y : Obj} (plan : Plan Obj Region Hole X Y) :
    NormalForm.denote realization (normalize source plan) =
      Plan.denote realization plan := by
  induction plan with
  | nil object =>
      simp [normalize, NormalForm.denote, Plan.denote,
        realization.map_identity]
  | region arrow rest inductionHypothesis =>
      rw [normalize, NormalForm.denote_prependRegion, Plan.denote,
        inductionHypothesis]
  | hole opening rest inductionHypothesis =>
      simp only [normalize, NormalForm.denote, Plan.denote,
        realization.map_identity]
      rw [target.identity_compose, inductionHypothesis]

/-- Normalization preserves exact ordered hole labels, endpoints,
multiplicity, and order. -/
theorem normalize_holeTrace
    (source : IndexedCategory Obj Region)
    {X Y : Obj} (plan : Plan Obj Region Hole X Y) :
    (normalize source plan).holeTrace = plan.holeTrace := by
  induction plan with
  | nil object => rfl
  | region arrow rest inductionHypothesis =>
      cases normalized : normalize source rest with
      | final next =>
          rw [normalized] at inductionHypothesis
          simpa [normalize, NormalForm.prependRegion, NormalForm.holeTrace,
            Plan.holeTrace, normalized] using inductionHypothesis
      | step next opening tail =>
          rw [normalized] at inductionHypothesis
          simpa [normalize, NormalForm.prependRegion, NormalForm.holeTrace,
            Plan.holeTrace, normalized] using inductionHypothesis
  | hole opening rest inductionHypothesis =>
      simp [normalize, NormalForm.holeTrace, Plan.holeTrace,
        inductionHypothesis]

/-- Reifying and renormalizing an alternating normal form is the identity.
This makes normalization a retraction, not merely a semantic peephole. -/
theorem normalize_toPlan
    (source : IndexedCategory Obj Region)
    {X Y : Obj} (normal : NormalForm Region Hole X Y) :
    normalize source normal.toPlan = normal := by
  induction normal with
  | final region =>
      simp [NormalForm.toPlan, normalize, NormalForm.prependRegion,
        source.compose_identity]
  | step region opening rest inductionHypothesis =>
      simp [NormalForm.toPlan, normalize, NormalForm.prependRegion,
        source.compose_identity, inductionHypothesis]

/-- Normalization is idempotent after the canonical form is reified. -/
theorem normalize_idempotent
    (source : IndexedCategory Obj Region)
    {X Y : Obj} (plan : Plan Obj Region Hole X Y) :
    normalize source (normalize source plan).toPlan =
      normalize source plan :=
  normalize_toPlan source (normalize source plan)

/-- Canonical forms are uniquely determined by their exact reified source
path. -/
theorem normalForm_unique
    (source : IndexedCategory Obj Region)
    {X Y : Obj} {first second : NormalForm Region Hole X Y}
    (samePath : first.toPlan = second.toPlan) :
    first = second := by
  have normalized := congrArg (normalize source) samePath
  simpa [normalize_toPlan source] using normalized

/-- Any candidate retaining the source hole trace in order has at least as
many holes as the canonical normal form. -/
theorem normalize_hole_minimal
    (source : IndexedCategory Obj Region)
    {X Y : Obj} (plan candidate : Plan Obj Region Hole X Y)
    (retains : plan.holeTrace.Sublist candidate.holeTrace) :
    (normalize source plan).holeCount ≤ candidate.holeCount := by
  rw [NormalForm.holeCount, normalize_holeTrace source plan,
    Plan.holeCount]
  exact retains.length_le

/-! ## Positive and negative structural controls -/

namespace Canaries

inductive Object where
  | input
  | middle
  | output
deriving DecidableEq, Repr

inductive TestRegion : Object → Object → Type where
  | identity (object : Object) : TestRegion object object
  | inputMiddle : TestRegion .input .middle
  | middleOutput : TestRegion .middle .output
  | inputOutput : TestRegion .input .output

def regionCategory : IndexedCategory Object TestRegion where
  identity := TestRegion.identity
  compose first second :=
    match first, second with
    | .identity _, later => later
    | earlier, .identity _ => earlier
    | .inputMiddle, .middleOutput => .inputOutput
  identity_compose _ := rfl
  compose_identity arrow := by cases arrow <;> rfl
  compose_assoc first second third := by
    cases first <;> cases second <;> cases third <;> rfl

inductive TestHole : Object → Object → Type where
  | suspend : TestHole .middle .middle

def examplePlan : Plan Object TestRegion TestHole .input .output :=
  .region .inputMiddle
    (.hole .suspend (.region .middleOutput (.nil Object.output)))

/-- Positive: typed normalization retains the hole and its endpoints while
fusing only region gaps. -/
example : (normalize regionCategory examplePlan).holeCount = 1 := by rfl

/-- Negative: a typed source path cannot place the middle-only hole after an
arrow which has already reached the output object. -/
example :
    ¬ Nonempty (TestRegion .output .input) := by
  intro impossible
  obtain ⟨arrow⟩ := impossible
  cases arrow

/-- Negative: a hole-free candidate does not retain the authored hole trace. -/
example :
    ¬ examplePlan.holeTrace.Sublist
      (Plan.region TestRegion.inputOutput (Plan.nil Object.output) :
        Plan Object TestRegion TestHole Object.input Object.output).holeTrace := by
  simp [examplePlan, Plan.holeTrace]

end Canaries

#print axioms Plan.append_assoc
#print axioms PartialArrow.identity_compose
#print axioms PartialArrow.compose_identity
#print axioms PartialArrow.compose_assoc
#print axioms PartialArrow.fault_compose
#print axioms PartialArrow.absent_compose
#print axioms Plan.denote_append
#print axioms Plan.denote_unique
#print axioms NormalForm.compose_assoc
#print axioms NormalForm.denote_compose
#print axioms normalize_exact
#print axioms normalize_holeTrace
#print axioms normalize_toPlan
#print axioms normalize_idempotent
#print axioms normalForm_unique
#print axioms normalize_hole_minimal

end Mettapedia.GSLT.Dynamics.RegionHolePlan
