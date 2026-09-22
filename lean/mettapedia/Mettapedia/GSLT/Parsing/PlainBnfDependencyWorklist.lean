import Mettapedia.GSLT.Parsing.PlainBnfOrderedGraphDiscovery
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Sort

/-!
# Dependency-local ordered discovery for plain BNF

The worklist stores ready, unpublished definition positions. Publication removes
one position and rechecks only definitions referring to it. Reference incidence
is built once into an array. Selection follows the source scan cursor, wrapping
only when no pending position remains in the current suffix.

This is a finite grammar algorithm, not a grammar logic or a generic evaluator.
The source-GSLT and native-realization bridges are separate. The finite-set
reference queue is not claimed to be an asymptotically optimal priority queue.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfDependencyWorklist

open PlainBnfOrderedGraphDiscovery

def refersTo {size : Nat} (grammar : Grammar size) (source target : Fin size) : Bool :=
  (grammar target).any fun alternative => alternative.references.contains source

def incidence {size : Nat} (grammar : Grammar size) : Array (Finset (Fin size)) :=
  Array.ofFn fun source => Finset.univ.filter fun target => refersTo grammar source target

def dependents {size : Nat} (grammar : Grammar size) (source : Fin size) : Finset (Fin size) :=
  (incidence grammar)[source.val]'(by simp [incidence])

theorem mem_dependents {size : Nat} (grammar : Grammar size) (source target : Fin size) :
    target ∈ dependents grammar source ↔ refersTo grammar source target = true := by
  simp [dependents, incidence]

/-- Auxiliary incidence edges retain each authored reference occurrence.
They do not replace the grammar or its ordered alternatives. -/
def referenceEdges {size : Nat} (grammar : Grammar size) : List (Fin size × Fin size) :=
  (List.finRange size).flatMap fun target =>
    (grammar target).flatMap fun alternative =>
      alternative.references.map fun source => (source, target)

theorem mem_referenceEdges {size : Nat} (grammar : Grammar size) (source target : Fin size) :
    (source, target) ∈ referenceEdges grammar ↔ refersTo grammar source target = true := by
  simp [referenceEdges, refersTo, List.any_eq_true]

def addEdges {size : Nat} :
    List (Fin size × Fin size) → Array (Finset (Fin size)) → Array (Finset (Fin size))
  | [], index => index
  | (source, target) :: rest, index =>
      addEdges rest (index.modify source.val fun previous => insert target previous)

theorem addEdges_size {size : Nat} (edges : List (Fin size × Fin size))
    (index : Array (Finset (Fin size))) : (addEdges edges index).size = index.size := by
  induction edges generalizing index with
  | nil => rfl
  | cons edge rest ih => simpa [addEdges] using ih (index.modify edge.1.val (insert edge.2))

theorem mem_addEdges {size : Nat} (edges : List (Fin size × Fin size))
    (index : Array (Finset (Fin size))) (sized : index.size = size) (source target : Fin size) :
    target ∈ (addEdges edges index)[source.val]'(by rw [addEdges_size, sized]; exact source.isLt) ↔
      target ∈ index[source.val]'(by rw [sized]; exact source.isLt) ∨ (source, target) ∈ edges := by
  induction edges generalizing index with
  | nil => simp [addEdges]
  | cons edge rest ih =>
      rcases edge with ⟨previous, next⟩
      simp only [addEdges]
      rw [ih _ (by simpa using sized)]
      simp only [Array.getElem_modify, List.mem_cons]
      by_cases same : previous = source
      ·
        subst previous
        simp only [↓reduceIte, Finset.mem_insert, Prod.mk.injEq, true_and]
        tauto
      · have differentValues : previous.val ≠ source.val := fun sameValues => same (Fin.ext sameValues)
        simp [differentValues, Prod.ext_iff, Ne.symm same]

/-- Construct the reverse index by visiting each reference occurrence once,
rather than asking every grammar definition about every possible source. -/
def buildIncidence {size : Nat} (grammar : Grammar size) : Array (Finset (Fin size)) :=
  addEdges (referenceEdges grammar) (Array.replicate size ∅)

theorem buildIncidence_eq {size : Nat} (grammar : Grammar size) :
    buildIncidence grammar = incidence grammar := by
  have sized : (buildIncidence grammar).size = size := by simp [buildIncidence, addEdges_size]
  apply Array.ext (by simp [sized, incidence])
  intro i leftBound rightBound
  have bounded : i < size := by simpa [sized] using leftBound
  apply Finset.ext
  intro target
  have law := mem_addEdges (referenceEdges grammar) (Array.replicate size ∅)
    (by simp) ⟨i, bounded⟩ target
  simpa [buildIncidence, incidence, mem_referenceEdges] using law

def initialQueue {size : Nat} (grammar : Grammar size) (known : Known size) : Finset (Fin size) :=
  Finset.univ.filter fun position => ready grammar known position

theorem publish_preserves_true {size : Nat} (known : Known size) (source target : Fin size)
    (already : known target = true) : publish known source target = true := by
  simp [publish, already]

theorem ready_publish_preserved {size : Nat} (grammar : Grammar size) (known : Known size)
    (source target : Fin size) (different : target ≠ source)
    (enabled : ready grammar known target = true) :
    ready grammar (publish known source) target = true := by
  simp only [ready, alternativeReady, Bool.and_eq_true, List.any_eq_true]
    at enabled ⊢
  obtain ⟨unknown, alternative, member, leaves, references⟩ := enabled
  refine ⟨by simpa [publish, different] using unknown, alternative, member, leaves, ?_⟩
  simp only [List.all_eq_true] at references ⊢
  exact fun reference inside => publish_preserves_true known source reference (references _ inside)

theorem ready_publish_unchanged_without_dependency {size : Nat} (grammar : Grammar size)
    (known : Known size) (source target : Fin size) (different : target ≠ source)
    (unrelated : refersTo grammar source target = false) :
    ready grammar (publish known source) target = ready grammar known target := by
  have noReference : ∀ alternative ∈ grammar target, source ∉ alternative.references := by
    simpa [refersTo, List.any_eq_false] using unrelated
  have unchanged : ∀ alternative ∈ grammar target,
      alternativeReady (publish known source) alternative = alternativeReady known alternative := by
    intro alternative member
    unfold alternativeReady
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    have pointwise : ∀ reference ∈ alternative.references,
        publish known source reference = known reference := by
      intro reference inside
      have differentReference : reference ≠ source := by
        intro same
        exact noReference alternative member (same ▸ inside)
      simp [publish, differentReference]
    constructor
    · exact fun all reference inside => (pointwise reference inside) ▸ all reference inside
    · exact fun all reference inside => (pointwise reference inside).symm ▸ all reference inside
  simp only [ready, publish, different, ↓reduceIte]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨alternative, member, enabled⟩
    exact ⟨alternative, member, (unchanged alternative member) ▸ enabled⟩
  · rintro ⟨alternative, member, enabled⟩
    exact ⟨alternative, member, (unchanged alternative member).symm ▸ enabled⟩

def refresh {size : Nat} (grammar : Grammar size)
    (reverseIndex : Array (Finset (Fin size))) (known : Known size)
    (source : Fin size) (queue : Finset (Fin size)) : Finset (Fin size) :=
  queue.erase source ∪
    (reverseIndex[source.val]?.getD ∅).filter fun target =>
      ready grammar (publish known source) target

/-- The maintenance invariant is derived from the grammar, not supplied as
an answer oracle. Already-ready definitions remain queued; a newly-ready
definition must mention the published source. -/
theorem refresh_exact {size : Nat} (grammar : Grammar size) (known : Known size)
    (source : Fin size) :
    refresh grammar (incidence grammar) known source (initialQueue grammar known) =
      initialQueue grammar (publish known source) := by
  ext target
  have index : (incidence grammar)[source.val]?.getD ∅ = dependents grammar source := by
    simp [dependents, incidence]
  simp only [refresh, index, Finset.mem_union, Finset.mem_erase, initialQueue,
    Finset.mem_filter, Finset.mem_univ, true_and, mem_dependents]
  constructor
  · rintro (⟨different, enabled⟩ | ⟨_, enabled⟩)
    · exact ready_publish_preserved grammar known source target different enabled
    · exact enabled
  · intro enabled
    have different : target ≠ source := by
      intro same
      simp [same, ready, publish] at enabled
    cases related : refersTo grammar source target with
    | true => exact Or.inr ⟨rfl, enabled⟩
    | false =>
        exact Or.inl ⟨different, by
          rwa [ready_publish_unchanged_without_dependency grammar known source target
            different related] at enabled⟩

def least {size : Nat} (queue : Finset (Fin size)) : Option (Fin size) :=
  if occupied : queue.Nonempty then some (queue.min' occupied) else none

theorem least_some_iff {size : Nat} (queue : Finset (Fin size)) (position : Fin size) :
    least queue = some position ↔ position ∈ queue ∧ ∀ other ∈ queue, position ≤ other := by
  unfold least
  split
  · simp only [Option.some.injEq]
    exact Finset.min'_eq_iff _ _ _
  · rename_i empty
    constructor
    · intro impossible
      cases impossible
    · intro member
      exact (empty ⟨position, member.1⟩).elim

theorem least_none_iff {size : Nat} (queue : Finset (Fin size)) :
    least queue = none ↔ queue = ∅ := by
  simp [least, Finset.not_nonempty_iff_eq_empty]

theorem nextReady_position_eq_least {size : Nat} (grammar : Grammar size)
    (known : Known size) (positions : List (Fin size))
    (ordered : positions.Pairwise (· ≤ ·)) :
    (nextReady grammar positions known).map Prod.fst =
      least (positions.toFinset.filter fun position => ready grammar known position) := by
  induction positions with
  | nil => simp [nextReady, least]
  | cons head tail ih =>
      have order := List.pairwise_cons.mp ordered
      cases enabled : ready grammar known head with
      | false =>
          simpa [nextReady, enabled, Finset.filter_insert] using ih order.2
      | true =>
          simp only [nextReady, enabled, ↓reduceIte, Option.map_some]
          symm
          apply (least_some_iff _ _).mpr
          refine ⟨by simp [enabled], ?_⟩
          intro other member
          have inside : other ∈ head :: tail := by
            exact List.mem_toFinset.mp (Finset.mem_filter.mp member).1
          rcases List.mem_cons.mp inside with same | rest
          · exact le_of_eq same.symm
          · exact order.1 other rest

theorem mem_finRange_drop {size cursor : Nat} (position : Fin size) :
    position ∈ (List.finRange size).drop cursor ↔ cursor ≤ position.val := by
  rw [List.mem_drop_iff_getElem]
  constructor
  · rintro ⟨offset, _, entry⟩
    have values := congrArg Fin.val entry
    simp at values
    omega
  · intro later
    refine ⟨position.val - cursor, by simp; omega, ?_⟩
    apply Fin.ext
    simp
    omega

theorem finRange_pairwise_le (size : Nat) : (List.finRange size).Pairwise (· ≤ ·) :=
  (List.sortedLT_finRange size).pairwise.imp fun related => le_of_lt related

theorem suffix_ready_set {size : Nat} (grammar : Grammar size) (known : Known size)
    (cursor : Nat) :
    ((List.finRange size).drop cursor).toFinset.filter (fun position => ready grammar known position) =
      (initialQueue grammar known).filter (fun position => cursor ≤ position.val) := by
  ext position
  simp [initialQueue, mem_finRange_drop, and_comm]

theorem all_ready_set {size : Nat} (grammar : Grammar size) (known : Known size) :
    (List.finRange size).toFinset.filter (fun position => ready grammar known position) =
      initialQueue grammar known := by
  ext position
  simp [initialQueue]

def select {size : Nat} (queue : Finset (Fin size)) (round cursor : Nat) : Option (Event size) :=
  match least (queue.filter fun position => cursor ≤ position.val) with
  | some position => some ⟨round, position⟩
  | none => (least queue).map fun position => ⟨round + 1, position⟩

/-- The least pending position in the current source suffix is the next
discovery of the full scan. If there is none, both routes wrap once. -/
theorem select_eq_nextEvent {size : Nat} (grammar : Grammar size) (known : Known size)
    (round cursor : Nat) :
    select (initialQueue grammar known) round cursor = nextEvent grammar known round cursor := by
  have suffix := nextReady_position_eq_least grammar known ((List.finRange size).drop cursor)
    (finRange_pairwise_le size).drop
  rw [suffix_ready_set] at suffix
  have entire := nextReady_position_eq_least grammar known (List.finRange size)
    (finRange_pairwise_le size)
  rw [all_ready_set] at entire
  unfold select nextEvent
  dsimp only
  rw [← suffix, ← entire]
  cases nextReady grammar ((List.finRange size).drop cursor) known with
  | none =>
      cases nextReady grammar (List.finRange size) known <;> rfl
  | some selected => cases selected; rfl

theorem selected_mem_queue {size : Nat} (queue : Finset (Fin size)) (round cursor : Nat)
    {event : Event size} (selected : select queue round cursor = some event) :
    event.position ∈ queue := by
  unfold select at selected
  cases suffix : least (queue.filter fun position => cursor ≤ position.val) with
  | none =>
      simp only [suffix] at selected
      cases entire : least queue with
      | none => simp [entire] at selected
      | some position =>
          have fields : event = ⟨round + 1, position⟩ := by
            simpa [entire] using selected.symm
          rw [fields]
          exact ((least_some_iff queue position).mp entire).1
  | some position =>
      have fields : event = ⟨round, position⟩ := by
        simpa [suffix] using selected.symm
      rw [fields]
      exact (Finset.mem_filter.mp ((least_some_iff _ _).mp suffix).1).1

def unpublished {size : Nat} (known : Known size) : Finset (Fin size) :=
  Finset.univ.filter fun position => known position = false

theorem unpublished_publish {size : Nat} (known : Known size) (position : Fin size) :
    unpublished (publish known position) = (unpublished known).erase position := by
  ext other
  by_cases same : other = position
  · simp [unpublished, publish, same]
  · simp [unpublished, publish, same]

theorem publication_decreases_count {size : Nat} (known : Known size) (position : Fin size)
    (fresh : known position = false) :
    (unpublished (publish known position)).card + 1 = (unpublished known).card := by
  rw [unpublished_publish]
  exact Finset.card_erase_add_one (by simp [unpublished, fresh])

theorem empty_unpublished_queue {size : Nat} (grammar : Grammar size) (known : Known size)
    (empty : (unpublished known).card = 0) : initialQueue grammar known = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro position member
  have fresh : known position = false := by
    have enabled := (Finset.mem_filter.mp member).2
    simp only [ready, Bool.and_eq_true] at enabled
    simpa using enabled.1
  have absent := Finset.card_eq_zero.mp empty
  have present : position ∈ unpublished known := by simp [unpublished, fresh]
  simp [absent] at present

def run {size : Nat} (grammar : Grammar size) (reverseIndex : Array (Finset (Fin size))) :
    Nat → Known size → Finset (Fin size) → Nat → Nat → List (Event size)
  | 0, _, _, _, _ => []
  | fuel + 1, known, queue, round, cursor =>
      match select queue round cursor with
      | none => []
      | some event =>
          event :: run grammar reverseIndex fuel (publish known event.position)
            (refresh grammar reverseIndex known event.position queue)
            event.round (event.position.val + 1)

/-- Exact round/position trace equality for arbitrary finite fuel and initial
known state. The executable worklist is seeded from grammar data, and its
invariant is maintained by dependency-local updates. -/
theorem run_eq_runEvents {size : Nat} (grammar : Grammar size) (fuel : Nat)
    (known : Known size) (round cursor : Nat) :
    run grammar (incidence grammar) fuel known (initialQueue grammar known) round cursor =
      runEvents grammar fuel known round cursor := by
  induction fuel generalizing known round cursor with
  | zero => rfl
  | succ fuel ih =>
      simp only [run, runEvents, select_eq_nextEvent]
      cases nextEvent grammar known round cursor with
      | none => rfl
      | some event =>
          simp only [refresh_exact]
          rw [ih]

/-- Sufficient fuel depends only on the number of unpublished definitions.
Cycles without seeds may stop sooner, but cannot require extra fuel. -/
theorem run_stable {size : Nat} (grammar : Grammar size) (fuel extra : Nat)
    (known : Known size) (round cursor : Nat)
    (enough : (unpublished known).card ≤ fuel) :
    run grammar (incidence grammar) (fuel + extra) known (initialQueue grammar known) round cursor =
      run grammar (incidence grammar) fuel known (initialQueue grammar known) round cursor := by
  induction fuel generalizing known round cursor with
  | zero =>
      have empty := empty_unpublished_queue grammar known (Nat.eq_zero_of_le_zero enough)
      cases extra <;> simp [run, empty, select, least]
  | succ fuel ih =>
      simp only [Nat.succ_add, run]
      cases selected : select (initialQueue grammar known) round cursor with
      | none => rfl
      | some event =>
          have member := selected_mem_queue (initialQueue grammar known) round cursor selected
          have fresh : known event.position = false := by
            have enabled := (Finset.mem_filter.mp member).2
            simp only [ready, Bool.and_eq_true] at enabled
            simpa using enabled.1
          have decrease := publication_decreases_count known event.position fresh
          simp only [refresh_exact]
          rw [ih (publish known event.position) event.round (event.position.val + 1) (by omega)]

def discover {size : Nat} (grammar : Grammar size) (known : Known size) : List (Event size) :=
  run grammar (buildIncidence grammar) size known (initialQueue grammar known) 0 0

theorem discover_eq_reference {size : Nat} (grammar : Grammar size) (known : Known size) :
    discover grammar known = runEvents grammar size known 0 0 := by
  rw [discover, buildIncidence_eq]
  exact run_eq_runEvents grammar size known 0 0

/-- The public finite algorithm is complete for its dependency-discovery
reference: increasing its discovery bound cannot add any event. -/
theorem discover_saturated {size : Nat} (grammar : Grammar size) (known : Known size)
    (extra : Nat) :
    run grammar (buildIncidence grammar) (size + extra) known (initialQueue grammar known) 0 0 =
      discover grammar known := by
  rw [discover, buildIncidence_eq]
  apply run_stable
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

private def cascade : Grammar 3 := fun position =>
  if position = 1 then [⟨[0], true⟩] else [⟨[], true⟩]

theorem cascade_precedes_independent_seed :
    discover cascade (fun _ => false) = [⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩] := by decide

/-- A stale or absent incidence index misses a real discovery, even though
every initial seed is still present. The index is a semantic input. -/
theorem missing_dependency_changes_trace :
    run cascade #[] 3 (fun _ => false) (initialQueue cascade (fun _ => false)) 0 0 =
      [⟨0, 0⟩, ⟨0, 2⟩] ∧
      discover cascade (fun _ => false) ≠ [⟨0, 0⟩, ⟨0, 2⟩] := by decide

private def deferred : Grammar 3 := fun position =>
  if position = 0 then [⟨[1], true⟩]
  else if position = 1 then [⟨[], true⟩]
  else [⟨[0], true⟩]

theorem deferred_publication_preserves_round :
    discover deferred (fun _ => false) = [⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩] := by decide

/-- The dependency index may notify a target once because this algorithm
rechecks all its reference occurrences; it does not decrement an occurrence
counter once for an arbitrarily deduplicated group. -/
theorem repeated_references_are_rechecked :
    discover (fun position : Fin 2 =>
      if position = 0 then [⟨[1, 1], true⟩] else [⟨[], true⟩]) (fun _ => false) =
      [⟨0, 1⟩, ⟨1, 0⟩] := by decide

theorem unseeded_cycle_stays_unpublished :
    discover (fun _ : Fin 1 => [⟨[0], true⟩]) (fun _ => false) = [] := by decide

theorem excluded_leaves_do_not_seed :
    discover (fun _ : Fin 1 => [⟨[], false⟩]) (fun _ => false) = [] := by decide

end Mettapedia.GSLT.Parsing.PlainBnfDependencyWorklist
