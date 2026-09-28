import Mettapedia.OSLF.Syntax.CanonicalConditionalRuleFrames

/-!
# Retaining the source of a relation-query premise

The canonical relation interpreter enumerates built-in and external tuples,
matches the query arguments against each tuple, and merges the resulting
extension into the current assignment. Its returned list records only the
final assignment. An event below retains the selected tuple and selected
argument match, including their positions in the two ordered lists.

Forgetting an event gives exactly an existing engine result. Distinct tuple
positions are not identified even when they produce equal assignments.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CanonicalRelationQueryEvents

open Mettapedia.OSLF.Binding.CanonicalConditionalRuleFrames
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-- The exact ordered relation table consulted by the engine after applying
the current assignment to the query arguments. -/
def relationTuples (relEnv : RelationEnv) (lang : LanguageDef)
    (initial : Bindings) (relation : String) (arguments : List Pattern) :
    List (List Pattern) :=
  let instantiated := arguments.map (applyBindings initial)
  builtinRelationTuples lang relation instantiated ++
    relEnv.tuples relation instantiated

/-- One actual relation-query event, retaining both nondeterministic choices
and the merge equation. -/
structure Event (relEnv : RelationEnv) (lang : LanguageDef)
    (initial : Bindings) (relation : String) (arguments : List Pattern)
    (final : Bindings) where
  tuple : List Pattern
  selectedTuple : ListedWitness
    (relationTuples relEnv lang initial relation arguments) tuple
  extension : Bindings
  selectedMatch : ListedWitness
    (matchRelationArgs initial arguments tuple) extension
  merge : mergeBindings initial extension = some final

/-- A computable event record for the engine's ordered enumeration. The two
numbers are the original tuple and argument-match positions. -/
structure RecordedEvent where
  tuplePosition : Nat
  tuple : List Pattern
  matchPosition : Nat
  extension : Bindings
  final : Bindings

/-- Enumerate the provenance of every emitted relation-query result. The
outer and inner `zipIdx` operations retain duplicate rows and matches. -/
def recordedEvents (relEnv : RelationEnv) (lang : LanguageDef)
    (initial : Bindings) (relation : String) (arguments : List Pattern) :
    List RecordedEvent :=
  (relationTuples relEnv lang initial relation arguments).zipIdx.flatMap
    fun (tuple, tuplePosition) =>
      (matchRelationArgs initial arguments tuple).zipIdx.filterMap
        fun (extension, matchPosition) =>
          (mergeBindings initial extension).map fun final =>
            { tuplePosition, tuple, matchPosition, extension, final }

/-- Adding positions to a filtered list does not change its ordered results
when those positions are forgotten. -/
private theorem map_zipIdx_filterMap {α β γ : Type}
    (values : List α) (f : α → Option β)
    (make : Nat → α → β → γ)
    (forget : γ → β)
    (hforget : ∀ index value result,
      forget (make index value result) = result)
    (start : Nat) :
    ((values.zipIdx start).filterMap fun (value, index) =>
      (f value).map (make index value)).map forget =
      values.filterMap f := by
  induction values generalizing start with
  | nil => rfl
  | cons value tail ih =>
      cases h : f value <;>
        simp [List.zipIdx_cons, h, hforget, ih]

private theorem zipIdx_flatMap_ignore_position {α β : Type}
    (values : List α) (f : α → List β) (start : Nat) :
    (values.zipIdx start).flatMap (fun pair => f pair.1) =
      values.flatMap f := by
  induction values generalizing start with
  | nil => rfl
  | cons value tail ih =>
      simp [List.zipIdx_cons, ih]

/-- The recorded events and the existing engine result list agree in order
and multiplicity, not merely after conversion to a set or proposition. -/
theorem recordedEvents_results (relEnv : RelationEnv) (lang : LanguageDef)
    (initial : Bindings) (relation : String) (arguments : List Pattern) :
    (recordedEvents relEnv lang initial relation arguments).map
      RecordedEvent.final =
      relationQueryStep relEnv lang initial relation arguments := by
  unfold recordedEvents relationQueryStep
  rw [List.map_flatMap]
  have inner (tuple : List Pattern) (tuplePosition : Nat) :
      (List.filterMap
        (fun pair => (mergeBindings initial pair.1).map
          (fun final => RecordedEvent.mk tuplePosition tuple pair.2
            pair.1 final))
        (matchRelationArgs initial arguments tuple).zipIdx).map
        RecordedEvent.final =
        (matchRelationArgs initial arguments tuple).filterMap
          (mergeBindings initial) := by
    exact map_zipIdx_filterMap _ _ _ _
      (by intros; rfl) 0
  simp only [inner]
  simpa only [relationTuples] using
    zipIdx_flatMap_ignore_position
      (relationTuples relEnv lang initial relation arguments)
      (fun tuple => (matchRelationArgs initial arguments tuple).filterMap
        (mergeBindings initial)) 0

/-- A particular occurrence of an engine result has a recorded tuple and
match event at exactly the same list position. Equal result values do not
make this provenance ambiguous. -/
theorem selected_result_has_recorded_event
    (relEnv : RelationEnv) (lang : LanguageDef)
    (initial : Bindings) (relation : String) (arguments : List Pattern)
    (final : Bindings)
    (selected : ListedWitness
      (relationQueryStep relEnv lang initial relation arguments) final) :
    ∃ event : RecordedEvent,
      ∃ occurrence : ListedWitness
        (recordedEvents relEnv lang initial relation arguments) event,
        event.final = final ∧
          occurrence.position.1 = selected.position.1 := by
  let selected' : ListedWitness
      ((recordedEvents relEnv lang initial relation arguments).map
        RecordedEvent.final) final :=
    { position := ⟨selected.position.1, by
        simpa only [recordedEvents_results] using selected.position.2⟩
      represents := by
        have hbound : selected.position.1 <
            ((recordedEvents relEnv lang initial relation arguments).map
              RecordedEvent.final).length := by
          simpa only [recordedEvents_results] using selected.position.2
        change ((recordedEvents relEnv lang initial relation arguments).map
          RecordedEvent.final)[selected.position.1]'hbound = final
        simpa only [recordedEvents_results, List.get_eq_getElem] using
          selected.represents }
  obtain ⟨event, occurrence, finalEq, positionEq⟩ :=
    ListedWitness.map_has_preimage RecordedEvent.final selected'
  exact ⟨event, occurrence, finalEq, positionEq⟩

/-- Every member of the computable event enumeration satisfies the dependent
tuple-selection, match-selection, and merge contract. -/
theorem recorded_event_valid
    (relEnv : RelationEnv) (lang : LanguageDef)
    (initial : Bindings) (relation : String) (arguments : List Pattern)
    (recorded : RecordedEvent)
    (member : recorded ∈
      recordedEvents relEnv lang initial relation arguments) :
    Nonempty (Event relEnv lang initial relation arguments
      recorded.final) := by
  simp only [recordedEvents, List.mem_flatMap] at member
  obtain ⟨⟨tuple, tuplePosition⟩, tupleMem, innerMem⟩ := member
  obtain ⟨⟨extension, matchPosition⟩, matchMem, recordEq⟩ :=
    List.mem_filterMap.mp innerMem
  cases mergeEq : mergeBindings initial extension with
  | none => simp [mergeEq] at recordEq
  | some final =>
      simp only [mergeEq, Option.map_some] at recordEq
      cases recordEq
      obtain ⟨tupleBound, tupleAt⟩ := List.mem_zipIdx' tupleMem
      obtain ⟨matchBound, matchAt⟩ := List.mem_zipIdx' matchMem
      exact ⟨⟨tuple, ⟨⟨tuplePosition, tupleBound⟩, tupleAt.symm⟩,
        extension, ⟨⟨matchPosition, matchBound⟩, matchAt.symm⟩,
        mergeEq⟩⟩

/-- Every retained event is an output of the executable relation query. -/
theorem event_mem_result {relEnv : RelationEnv} {lang : LanguageDef}
    {initial final : Bindings} {relation : String}
    {arguments : List Pattern}
    (event : Event relEnv lang initial relation arguments final) :
    final ∈ relationQueryStep relEnv lang initial relation arguments := by
  simp only [relationQueryStep, List.mem_flatMap]
  refine ⟨event.tuple, event.selectedTuple.mem, ?_⟩
  exact List.mem_filterMap.mpr
    ⟨event.extension, event.selectedMatch.mem, event.merge⟩

/-- Conversely, every executable result has a tuple occurrence and a match
occurrence that produced it. -/
theorem result_iff_event {relEnv : RelationEnv} {lang : LanguageDef}
    {initial final : Bindings} {relation : String}
    {arguments : List Pattern} :
    final ∈ relationQueryStep relEnv lang initial relation arguments ↔
      Nonempty (Event relEnv lang initial relation arguments final) := by
  constructor
  · intro result
    simp only [relationQueryStep, List.mem_flatMap] at result
    obtain ⟨tuple, tupleMem, matchMem⟩ := result
    obtain ⟨extension, extensionMem, merge⟩ :=
      List.mem_filterMap.mp matchMem
    obtain ⟨selectedTuple⟩ :=
      ListedWitness.nonempty_iff_mem.mpr tupleMem
    obtain ⟨selectedMatch⟩ :=
      ListedWitness.nonempty_iff_mem.mpr extensionMem
    exact ⟨⟨tuple, selectedTuple, extension, selectedMatch, merge⟩⟩
  · rintro ⟨event⟩
    exact event_mem_result event

/-- The engine's existing relation-query frame is inhabited exactly when a
retained relation event exists. This connects table-row provenance to the
canonical conditional-rule constructor. -/
theorem frame_iff_event {relEnv : RelationEnv} {lang : LanguageDef}
    {initial final : Bindings} {relation : String}
    {arguments : List Pattern} :
    Nonempty (PremiseFrame (engineBasePremises relEnv) lang
      initial (.relationQuery relation arguments) final) ↔
      Nonempty (Event relEnv lang initial relation arguments final) := by
  constructor
  · rintro ⟨frame⟩
    cases frame with
    | relationQuery selected =>
        exact result_iff_event.mp (by simpa [engineBasePremises,
          premiseStepWithEnv] using selected.mem)
  · rintro ⟨event⟩
    have result : final ∈ engineBasePremises relEnv lang initial
        (.relationQuery relation arguments) := by
      simpa [engineBasePremises, premiseStepWithEnv] using
        event_mem_result event
    obtain ⟨selected⟩ := ListedWitness.nonempty_iff_mem.mpr result
    exact ⟨.relationQuery selected⟩

/-- The exact selected result of a canonical relation premise determines the
recorded tuple and match event at the same output-list position. This is the
provenance bridge used when a full authored rule frame carries that premise. -/
theorem selected_frame_has_recorded_event
    {relEnv : RelationEnv} {lang : LanguageDef}
    {initial final : Bindings} {relation : String}
    {arguments : List Pattern}
    (frame : PremiseFrame (engineBasePremises relEnv) lang
      initial (.relationQuery relation arguments) final) :
    ∃ event : RecordedEvent,
      ∃ occurrence : ListedWitness
        (recordedEvents relEnv lang initial relation arguments) event,
        event.final = final ∧
          occurrence.position.1 =
            (match frame with
            | .relationQuery selected => selected.position.1) := by
  cases frame with
  | relationQuery selected =>
      change ListedWitness
        (relationQueryStep relEnv lang initial relation arguments) final
        at selected
      exact selected_result_has_recorded_event
        relEnv lang initial relation arguments final selected

/-- The selected tuple comes from one of the two declared providers. This
disjunction does not erase its original position in the event. -/
theorem tuple_from_builtin_or_environment
    {relEnv : RelationEnv} {lang : LanguageDef}
    {initial final : Bindings} {relation : String}
    {arguments : List Pattern}
    (event : Event relEnv lang initial relation arguments final) :
    event.tuple ∈ builtinRelationTuples lang relation
        (arguments.map (applyBindings initial)) ∨
      event.tuple ∈ relEnv.tuples relation
        (arguments.map (applyBindings initial)) := by
  exact List.mem_append.mp event.selectedTuple.mem

/-- An equality of events must preserve the selected tuple occurrence, even
if two table entries and their final assignments are identical. -/
theorem distinct_tuple_positions
    {relEnv : RelationEnv} {lang : LanguageDef}
    {initial final : Bindings} {relation : String}
    {arguments : List Pattern}
    (first second : Event relEnv lang initial relation arguments final)
    (different : first.selectedTuple.position.1 ≠
      second.selectedTuple.position.1) : first ≠ second := by
  intro equal
  apply different
  cases equal
  rfl

#print axioms event_mem_result
#print axioms recordedEvents_results
#print axioms selected_result_has_recorded_event
#print axioms recorded_event_valid
#print axioms result_iff_event
#print axioms frame_iff_event
#print axioms selected_frame_has_recorded_event
#print axioms tuple_from_builtin_or_environment
#print axioms distinct_tuple_positions

end Mettapedia.OSLF.Binding.CanonicalRelationQueryEvents
