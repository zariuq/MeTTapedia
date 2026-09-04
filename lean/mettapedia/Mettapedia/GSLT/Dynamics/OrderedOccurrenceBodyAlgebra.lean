import Mettapedia.GSLT.LanguageDef.EmptyDemandCoherence
import Mettapedia.GSLT.Dynamics.RegionHolePlan

/-!
# Ordered occurrence bodies and suspension holes

PeTTa exposes authored order and occurrence multiplicity to observations such
as `once`.  The appropriate finite nondeterminism carrier is therefore an
ordered occurrence list, not its commutative bag quotient.

This module characterizes exactly which whole-family transformations preserve
the ordered choice operation.  A transformation preserves zero and append if
and only if it is the `flatMap` lifting of a unique per-occurrence step.  This
is the free-monoid universal property in executable form.  It licenses
candidate-local guards, deterministic prepared segments, and open-call
suspension holes without deriving the source semantics from any particular
abstract machine.

Kleisli composition then gives the body law: a prepared segment can stop at
an open call, let the canonical relation evaluator produce its ordered
occurrences, and continue independently for every occurrence.  Fusion may
change the internal path, while exact output and no-invention remain visible.

The final section keeps finite operational grades honest.  Equality after
erasing work is insufficient for a finite-fuel optimization; the graded
occurrence family itself must commute.  This is why an unlimited-fuel fast
path does not automatically authorize the same lowering under finite fuel.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.OrderedOccurrenceBodyAlgebra

open RegionHolePlan

universe uInput uMiddle uOutput

/-- Ordered nondeterministic occurrences retain source order and duplicates. -/
abbrev Occurrences (Output : Type uOutput) := List Output

/-- One source-derived body segment.  Zero, one, or many ordered occurrences
may be emitted for one input occurrence. -/
abbrev Segment (Input : Type uInput) (Output : Type uOutput) :=
  Input → Occurrences Output

/-- Lift a per-occurrence segment over an authored occurrence family. -/
def run {Input : Type uInput} {Output : Type uOutput}
    (segment : Segment Input Output) (inputs : Occurrences Input) :
    Occurrences Output :=
  inputs.flatMap segment

/-- A whole-family transformation preserves computational zero and authored
choice composition. -/
def PreservesOrderedChoice
    {Input : Type uInput} {Output : Type uOutput}
    (transform : Occurrences Input → Occurrences Output) : Prop :=
  transform [] = [] ∧
    ∀ left right, transform (left ++ right) =
      transform left ++ transform right

/-- A transformation is candidate-local when one fixed segment is lifted
independently over every input occurrence. -/
def CandidateLocalizable
    {Input : Type uInput} {Output : Type uOutput}
    (transform : Occurrences Input → Occurrences Output) : Prop :=
  ∃ segment : Segment Input Output,
    ∀ inputs, transform inputs = run segment inputs

/-- Every candidate-local lifting preserves ordered choice. -/
theorem preservesOrderedChoice_of_candidateLocalizable
    {Input : Type uInput} {Output : Type uOutput}
    {transform : Occurrences Input → Occurrences Output}
    (localizable : CandidateLocalizable transform) :
    PreservesOrderedChoice transform := by
  obtain ⟨segment, equality⟩ := localizable
  constructor
  · simp [equality, run]
  · intro left right
    simp [equality, run, List.flatMap_append]

/-- Conversely, every transformation preserving zero and append is the
lifting of its action on singleton occurrences. -/
theorem candidateLocalizable_of_preservesOrderedChoice
    {Input : Type uInput} {Output : Type uOutput}
    {transform : Occurrences Input → Occurrences Output}
    (preserves : PreservesOrderedChoice transform) :
    CandidateLocalizable transform := by
  refine ⟨fun input => transform [input], ?_⟩
  intro inputs
  induction inputs with
  | nil =>
      simpa [run] using preserves.1
  | cons head tail inductionHypothesis =>
      calc
        transform (head :: tail) =
            transform ([head] ++ tail) := rfl
        _ = transform [head] ++ transform tail :=
            preserves.2 [head] tail
        _ = transform [head] ++
            run (fun input => transform [input]) tail := by
              rw [inductionHypothesis]
        _ = run (fun input => transform [input]) (head :: tail) := by
              rfl

/-- Ordered choice preservation is exactly candidate-localizability. -/
theorem preservesOrderedChoice_iff_candidateLocalizable
    {Input : Type uInput} {Output : Type uOutput}
    (transform : Occurrences Input → Occurrences Output) :
    PreservesOrderedChoice transform ↔ CandidateLocalizable transform := by
  constructor
  · exact candidateLocalizable_of_preservesOrderedChoice
  · exact preservesOrderedChoice_of_candidateLocalizable

/-- The local segment representing an ordered-choice homomorphism is unique.
It is recovered by observing singleton inputs. -/
theorem local_segment_unique
    {Input : Type uInput} {Output : Type uOutput}
    {transform : Occurrences Input → Occurrences Output}
    {first second : Segment Input Output}
    (firstExact : ∀ inputs, transform inputs = run first inputs)
    (secondExact : ∀ inputs, transform inputs = run second inputs) :
    first = second := by
  funext input
  calc
    first input = run first [input] := by simp [run]
    _ = transform [input] := (firstExact [input]).symm
    _ = run second [input] := secondExact [input]
    _ = second input := by simp [run]

/-! ## Guards, prepared prefixes, and suspension holes -/

variable {Input : Type uInput} {Middle : Type uMiddle}
  {Output : Type uOutput}

/-- A source-local crisp guard emits the same occurrence or computational
zero. -/
def guard (accepts : Input → Bool) : Segment Input Input :=
  fun input => if accepts input then [input] else []

@[simp] theorem guard_accepts (accepts : Input → Bool) (input : Input)
    (accepted : accepts input = true) :
    guard accepts input = [input] := by
  simp [guard, accepted]

@[simp] theorem guard_rejects (accepts : Input → Bool) (input : Input)
    (rejected : accepts input = false) :
    guard accepts input = [] := by
  simp [guard, rejected]

/-- Guard lifting is stable list filtering, so it preserves authored order and
every accepted duplicate occurrence. -/
theorem run_guard_eq_filter (accepts : Input → Bool)
    (inputs : Occurrences Input) :
    run (guard accepts) inputs = inputs.filter accepts := by
  induction inputs with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have tailEquality :
          tail.flatMap (guard accepts) = tail.filter accepts := by
        simpa [run] using inductionHypothesis
      cases accepted : accepts head <;>
        simp [run, guard, accepted, tailEquality]

/-- A deterministic prepared segment emits exactly one occurrence. -/
def deterministic (prepare : Input → Output) : Segment Input Output :=
  fun input => [prepare input]

/-- Deterministic lifting is ordinary order-preserving map. -/
theorem run_deterministic_eq_map (prepare : Input → Output)
    (inputs : Occurrences Input) :
    run (deterministic prepare) inputs = inputs.map prepare := by
  induction inputs with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have tailEquality :
          tail.flatMap (deterministic prepare) = tail.map prepare := by
        simpa [run] using inductionHypothesis
      simp [run, deterministic, tailEquality]

/-- Kleisli composition: `first` may be prepared straight-line work and
`second` may be an open canonical relation call or another prepared segment. -/
def thenSegment
    (first : Segment Input Middle) (second : Segment Middle Output) :
    Segment Input Output :=
  fun input => run second (first input)

/-- Running a segment, suspending at an open call, and continuing per result
is exactly one composed ordered-occurrence body. -/
theorem run_thenSegment
    (first : Segment Input Middle) (second : Segment Middle Output)
    (inputs : Occurrences Input) :
    run second (run first inputs) = run (thenSegment first second) inputs := by
  change (inputs.flatMap first).flatMap second =
    inputs.flatMap (fun input => (first input).flatMap second)
  exact List.flatMap_assoc

/-! ## Delayed observations after suspension holes -/

/-- Reference interpretation of an observation after an open call: each
produced closure is materialized, then inspected.  The closure may include a
source term, logical environment, occurrence identity, revision, and world. -/
def materializedObservationAfterHole
    {Closure : Type uMiddle} {Materialized : Type uOutput}
    {Result : Type*}
    (producer : Segment Input Closure)
    (materialize : Closure → Materialized)
    (observe : Closure → Materialized → Result) :
    Segment Input Result :=
  fun input => (producer input).map fun closure =>
    observe closure (materialize closure)

/-- Direct interpretation of the same observation.  This is admissible only
with the pointwise commutation law used below. -/
def directObservationAfterHole
    {Closure : Type uMiddle} {Result : Type*}
    (producer : Segment Input Closure)
    (observeDirect : Closure → Result) : Segment Input Result :=
  fun input => (producer input).map observeDirect

/-- A commuting direct observer may cross a suspension hole occurrence by
occurrence.  Authored order, duplicates, zero-result calls, and branch-local
closure state are retained because both sides map the same producer list. -/
theorem directObservationAfterHole_exact
    {Closure : Type uMiddle} {Materialized : Type uOutput}
    {Result : Type*}
    (producer : Segment Input Closure)
    (materialize : Closure → Materialized)
    (observe : Closure → Materialized → Result)
    (observeDirect : Closure → Result)
    (commutes : ∀ closure,
      observeDirect closure = observe closure (materialize closure)) :
    directObservationAfterHole producer observeDirect =
      materializedObservationAfterHole producer materialize observe := by
  funext input
  apply List.map_congr_left
  intro closure present
  exact commutes closure

/-- Positive canary: duplicate hole results remain duplicate observations. -/
theorem directObservationAfterHole_duplicate_canary :
    directObservationAfterHole
        (fun _ : Unit => [(2, 10), (2, 10), (3, 20)])
        (fun closure : Nat × Nat => closure.1 + closure.2) () =
      [12, 12, 23] := by
  rfl

/-- Negative canary: merely having a direct observer does not license it.
Without commutation, replacing materialize-then-observe changes the result. -/
theorem noncommuting_direct_observation_not_exact :
    directObservationAfterHole
        (fun _ : Unit => [(2, 10)])
        (fun closure : Nat × Nat => closure.1) () ≠
      materializedObservationAfterHole
        (fun _ : Unit => [(2, 10)])
        (fun closure : Nat × Nat => closure.1 + closure.2)
        (fun _ materialized => materialized) () := by
  decide

/-- Composition of suspension-bearing body segments is associative. -/
theorem thenSegment_assoc
    {Final : Type*}
    (first : Segment Input Middle) (second : Segment Middle Output)
    (third : Segment Output Final) :
    thenSegment (thenSegment first second) third =
      thenSegment first (thenSegment second third) := by
  funext input
  simpa [thenSegment] using run_thenSegment second third (first input)

/-- Singleton identity is a left identity for ordered-occurrence Kleisli
composition. -/
@[simp] theorem identity_thenSegment (segment : Segment Input Output) :
    thenSegment (deterministic id) segment = segment := by
  funext input
  simp [thenSegment, deterministic, run]

/-- Singleton identity is a right identity for ordered-occurrence Kleisli
composition. -/
@[simp] theorem thenSegment_identity (segment : Segment Input Output) :
    thenSegment segment (deterministic id) = segment := by
  funext input
  change (segment input).flatMap (fun output => [output]) = segment input
  induction values : segment input with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp

/-! ## Categorical presentation -/

/-- Ordinary functions form the deterministic region category. -/
def functionCategory :
    IndexedCategory (Type uInput)
      (fun Source Target : Type uInput => Source → Target) where
  identity _ := id
  compose first second := second ∘ first
  identity_compose _ := rfl
  compose_identity _ := rfl
  compose_assoc _ _ _ := rfl

/-- Ordered-occurrence segments form the Kleisli category of finite lists. -/
def occurrenceKleisliCategory :
    IndexedCategory (Type uInput)
      (fun Source Target : Type uInput => Segment Source Target) where
  identity _ := deterministic id
  compose := thenSegment
  identity_compose := identity_thenSegment
  compose_identity := thenSegment_identity
  compose_assoc := thenSegment_assoc

/-- Deterministic regions and genuinely branching holes interpreted in the
ordered-occurrence Kleisli category. -/
def occurrenceRealization :
    Realization
      functionCategory
      (fun Source Target : Type uInput => Segment Source Target)
      occurrenceKleisliCategory where
  objectMap := id
  mapRegion := deterministic
  mapHole := id
  map_identity _ := rfl
  map_compose first second := by
    funext input
    change [second (first input)] = [second (first input)]
    rfl

abbrev OccurrencePlan (Source Target : Type uInput) :=
  RegionHolePlan.Plan
    (Type uInput)
    (fun Left Right : Type uInput => Left → Right)
    (fun Left Right : Type uInput => Segment Left Right)
    Source Target

abbrev OccurrenceNormalForm (Source Target : Type uInput) :=
  RegionHolePlan.NormalForm
    (fun Left Right : Type uInput => Left → Right)
    (fun Left Right : Type uInput => Segment Left Right)
    Source Target

def normalizeOccurrencePlan
    {Source Target : Type uInput}
    (plan : OccurrencePlan Source Target) :
    OccurrenceNormalForm Source Target :=
  RegionHolePlan.normalize functionCategory plan

def denoteOccurrencePlan
    {Source Target : Type uInput}
    (plan : OccurrencePlan Source Target) : Segment Source Target :=
  RegionHolePlan.Plan.denote occurrenceRealization plan

def denoteOccurrenceNormalForm
    {Source Target : Type uInput}
    (normal : OccurrenceNormalForm Source Target) : Segment Source Target :=
  RegionHolePlan.NormalForm.denote occurrenceRealization normal

theorem normalizeOccurrencePlan_exact
    {Source Target : Type uInput}
    (plan : OccurrencePlan Source Target) :
    denoteOccurrenceNormalForm (normalizeOccurrencePlan plan) =
      denoteOccurrencePlan plan :=
  RegionHolePlan.normalize_exact occurrenceRealization plan

/-- A guard before an open call has the direct source meaning: rejected
inputs make no call; accepted inputs invoke the hole exactly once. -/
theorem guard_then_open_exact
    (accepts : Input → Bool) (openCall : Segment Input Output)
    (input : Input) :
    thenSegment (guard accepts) openCall input =
      if accepts input then openCall input else [] := by
  cases accepted : accepts input <;>
    simp [thenSegment, run, guard, accepted]

/-- Positive fusion control: two deterministic internal paths fuse to one
path without changing the occurrence result. -/
theorem deterministic_fusion
    (first : Input → Middle) (second : Middle → Output) :
    thenSegment (deterministic first) (deterministic second) =
      deterministic (second ∘ first) := by
  funext input
  simp [thenSegment, deterministic, run, Function.comp_apply]

/-! ## Anonymous binders retain holes and erase only their match step -/

/-- Matching an unbound anonymous variable against one producer result always
succeeds exactly once.  Its result carries no user-addressable binding. -/
def anonymousMatch : Segment Middle Unit :=
  fun _ => [()]

/-- Canonical `let` interpretation with an explicit anonymous-variable match
between an open producer and its continuation.  `Middle` may include a
branch-local world as well as the produced value; the continuation receives
that complete occurrence unchanged. -/
def viaAnonymousMatch
    (producer : Segment Input Middle)
    (resume : Input → Middle → Occurrences Output) :
    Segment Input Output :=
  fun input =>
    (producer input).flatMap fun middle =>
      (anonymousMatch middle).flatMap fun _ => resume input middle

/-- The lowered form omits only the always-singleton anonymous match.  The
open producer and one continuation resumption per produced occurrence remain
explicit. -/
def resumeAfterHole
    (producer : Segment Input Middle)
    (resume : Input → Middle → Occurrences Output) :
    Segment Input Output :=
  fun input => (producer input).flatMap (resume input)

/-- An anonymous binder's match step is an exact identity in the ordered
occurrence Kleisli category.  Eliminating it preserves order, duplicates,
branch-local worlds, and every zero-result producer. -/
theorem anonymous_binding_elision
    (producer : Segment Input Middle)
    (resume : Input → Middle → Occurrences Output) :
    viaAnonymousMatch producer resume = resumeAfterHole producer resume := by
  funext input
  simp [viaAnonymousMatch, resumeAfterHole, anonymousMatch]

/-- Positive canary: duplicate producer occurrences each resume the
continuation independently after anonymous-binding elimination. -/
theorem anonymous_binding_duplicate_canary :
    resumeAfterHole
      (fun _ : Unit => [1, 1, 2])
      (fun (_ : Unit) (value : Nat) => [value, value + 10]) () =
        [1, 11, 1, 11, 2, 12] := by
  rfl

/-- Negative canary: eliminating the open producer together with its
anonymous binder would lose occurrence multiplicity. -/
theorem anonymous_binding_does_not_license_hole_erasure :
    resumeAfterHole
        (fun _ : Unit => [1, 1])
        (fun (_ : Unit) (_ : Nat) => ["kept"]) () ≠
      ["kept"] := by
  decide

def branchingNormalizationPlan : OccurrencePlan Nat Nat :=
  .region (fun value : Nat => value + 1)
    (.region (fun value : Nat => value * 2)
      (.hole (fun value : Nat => [value == 4, false])
        (.region (fun selected : Bool => if selected then 7 else 17)
          (.nil Nat))))

/-- Positive categorical canary: adjacent deterministic regions fuse before a
typed branching hole, whose ordered results are resumed independently. -/
theorem normalizeOccurrencePlan_branching_canary :
    denoteOccurrenceNormalForm
        (normalizeOccurrencePlan branchingNormalizationPlan) 1 = [7, 17] := by
  decide

/-- Negative categorical canary: normalization cannot erase a genuinely
branching hole, even when both surrounding regions are identities. -/
theorem dropping_branching_hole_not_exact :
    denoteOccurrencePlan
        (.hole (fun value : Nat => [value, value + 1]) (.nil Nat)) 0 ≠
      denoteOccurrencePlan (.nil Nat) 0 := by
  decide

/-- Every output of a lifted segment originates in one input occurrence and
that occurrence's source-derived segment result. -/
theorem run_no_invention
    (segment : Segment Input Output) (inputs : Occurrences Input)
    {output : Output} (present : output ∈ run segment inputs) :
    ∃ input ∈ inputs, output ∈ segment input := by
  induction inputs with
  | nil => simp [run] at present
  | cons head tail inductionHypothesis =>
      simp only [run, List.flatMap_cons, List.mem_append] at present
      rcases present with inHead | inTail
      · exact ⟨head, by simp, inHead⟩
      · obtain ⟨input, inputPresent, outputPresent⟩ :=
          inductionHypothesis inTail
        exact ⟨input, by simp [inputPresent], outputPresent⟩

/-! ## Whole-race operations remain outside the local body algebra -/

/-- Keep only the first occurrence of a whole authored family. -/
def first : Occurrences Input → Occurrences Input
  | [] => []
  | head :: _ => [head]

/-- First-result observation cannot be implemented as an ordered-choice
homomorphism: resolving two singleton races separately keeps both winners,
while resolving their concatenation keeps only the first. -/
theorem first_not_preservesOrderedChoice (left right : Input) :
    ¬ PreservesOrderedChoice (first : Occurrences Input → Occurrences Input) := by
  intro preserves
  have combined := preserves.2 [left] [right]
  have lengths := congrArg List.length combined
  simp [first] at lengths

/-- Selecting from an occurrence-preserving schedule cannot invent a witness.
It may, however, select a different source witness from authored-order
selection; that distinction is made explicit below. -/
theorem scheduled_first_no_invention
    {source scheduled : Occurrences Input} {output : Input}
    (permutation : scheduled.Perm source)
    (present : output ∈ first scheduled) :
    output ∈ source := by
  cases scheduledEquality : scheduled with
  | nil =>
      simp [first, scheduledEquality] at present
  | cons head tail =>
      have outputEquality : output = head := by
        simpa [first, scheduledEquality] using present
      have inScheduled : output ∈ scheduled := by
        simp [scheduledEquality, outputEquality]
      exact permutation.mem_iff.mp inScheduled

/-- With no schedule transformation, first-result observation retains the
authored first occurrence exactly. -/
theorem identity_schedule_preserves_first (inputs : Occurrences Input) :
    first (id inputs) = first inputs :=
  rfl

/-- Occurrence preservation alone does not preserve first-witness identity.
Swapping two distinct source occurrences retains the complete occurrence bag
but changes the first observation. -/
theorem occurrence_preserving_schedule_can_change_first
    (left right : Input) (distinct : left ≠ right) :
    ([right, left] : Occurrences Input).Perm [left, right] ∧
      first [right, left] ≠ first [left, right] := by
  constructor
  · exact List.Perm.swap left right []
  · simp [first, Ne.symm distinct]

/-! ## Negative no-invention control -/

def sourceZero : Segment Unit Unit := fun _ => []
def inventingTarget : Segment Unit Unit := fun _ => [()]

/-- Forward execution alone is not an adequacy theorem: a target that invents
one result disagrees with the source even on a singleton input. -/
theorem inventing_target_not_exact :
    run inventingTarget [()] ≠ run sourceZero [()] := by
  simp [run, inventingTarget, sourceZero]

/-! ## Finite work is an independent observation axis -/

/-- A result occurrence paired with exact additive work. -/
abbrev GradedOccurrence (Output : Type uOutput) := Output × Nat

/-- Erase work only at an observer that explicitly does not inspect it. -/
def eraseWork {Output : Type uOutput}
    (outputs : Occurrences (GradedOccurrence Output)) : Occurrences Output :=
  outputs.map Prod.fst

def zeroWork (output : Output) : Segment Unit (GradedOccurrence Output) :=
  fun _ => [(output, 0)]

def oneWork (output : Output) : Segment Unit (GradedOccurrence Output) :=
  fun _ => [(output, 1)]

/-- An unlimited observer sees the same value from two differently graded
segments. -/
theorem zeroWork_oneWork_erasure_equal (output : Output) :
    eraseWork (run (zeroWork output) [()]) =
      eraseWork (run (oneWork output) [()]) := by
  simp [eraseWork, run, zeroWork, oneWork]

/-- A finite-work observer distinguishes those segments.  Erased answer
agreement therefore cannot license finite-fuel compilation. -/
theorem zeroWork_oneWork_graded_unequal (output : Output) :
    run (zeroWork output) [()] ≠ run (oneWork output) [()] := by
  simp [run, zeroWork, oneWork]

/-! ## Axiom audit targets -/

#print axioms preservesOrderedChoice_iff_candidateLocalizable
#print axioms local_segment_unique
#print axioms run_thenSegment
#print axioms directObservationAfterHole_exact
#print axioms directObservationAfterHole_duplicate_canary
#print axioms noncommuting_direct_observation_not_exact
#print axioms thenSegment_assoc
#print axioms identity_thenSegment
#print axioms thenSegment_identity
#print axioms guard_then_open_exact
#print axioms deterministic_fusion
#print axioms anonymous_binding_elision
#print axioms anonymous_binding_duplicate_canary
#print axioms anonymous_binding_does_not_license_hole_erasure
#print axioms normalizeOccurrencePlan_exact
#print axioms normalizeOccurrencePlan_branching_canary
#print axioms dropping_branching_hole_not_exact
#print axioms run_no_invention
#print axioms first_not_preservesOrderedChoice
#print axioms scheduled_first_no_invention
#print axioms identity_schedule_preserves_first
#print axioms occurrence_preserving_schedule_can_change_first
#print axioms inventing_target_not_exact
#print axioms zeroWork_oneWork_graded_unequal

end Mettapedia.GSLT.Dynamics.OrderedOccurrenceBodyAlgebra
