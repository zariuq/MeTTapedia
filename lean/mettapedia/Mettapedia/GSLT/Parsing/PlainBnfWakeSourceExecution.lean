import Mettapedia.GSLT.Parsing.PlainBnfReverseIndexSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfScheduleWorklistBridge

/-!
# Ordered Wake traversal and scheduled-name invariants

The independent observation processes the existing ranked definitions and
pairing heaps in source order. Readiness is a mathematical parameter here,
not an operational provider. Connecting the entire authored Wake family
requires the actual productive/nullable source calls in addition to scheduling.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfWakeSourceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises)
open PlainBnfSourceRank (Rank value)
open PlainBnfReverseIndexSourceExecution (Item key)
open PlainBnfStructuredDenotation (Expression)
open PlainBnfReferenceCollectionSourceExecution (expression span)
open PlainBnfGraphNameTrie (Trie lookup insertFirst)
open PlainBnfCollectorSourceExecution (name)
open PlainBnfHeapSourceExecution (itemLE)
open PlainBnfScheduleSourceExecution (singleton toCurrent)
open PlainBnfTrieSourceExecution (scalarRelations result)
open PlainBnfTwoHeapWorklist
open Batteries.PairingHeapImp (Heap)

abbrev HeapItem := PlainBnfHeapSourceExecution.Item
abbrev Queues := Heap HeapItem × Heap HeapItem × Trie SExpr

def heapItem (item : Item) : HeapItem :=
  PlainBnfScheduleSourceExecution.node item.1 (key item.2.name)
    (expression item.2.expression) (span item.2.span)

theorem node_wire (item : Item) :
    PlainBnfHeapSourceExecution.rankedDefinition (heapItem item) =
      PlainBnfReverseIndexSourceExecution.node item := rfl

def encodeQueues (queues : Queues) : SExpr :=
  PlainBnfScheduleSourceExecution.queues queues.1 queues.2.1 queues.2.2

/-- The selected source's existing schedule update, on its three ordinary
components. The underlying heap operation is Batteries' `merge`. -/
def enqueue (origin : Option Rank) (item : Item) (queues : Queues) : Queues :=
  (if toCurrent item.1 origin then (singleton (heapItem item)).merge itemLE queues.1 else queues.1,
   if toCurrent item.1 origin then queues.2.1 else (singleton (heapItem item)).merge itemLE queues.2.1,
   insertFirst (key item.2.name) (name (key item.2.name)) queues.2.2)

theorem enqueue_executes (origin : Option Rank) (item : Item) (queues : Queues) :
    Step (engineBasePremises scalarRelations) PlainBnfScheduleSourceExecution.language
      (PlainBnfScheduleSourceExecution.scheduleCall origin (heapItem item)
        queues.1 queues.2.1 queues.2.2)
      (result (encodeQueues (enqueue origin item queues))) := by
  unfold heapItem
  rw [PlainBnfScheduleSourceExecution.schedule_step_iff]
  rfl

def wakeStep (ready : Expression → Bool) (origin : Option Rank) (queues : Queues)
    (item : Item) : Queues :=
  if lookup (key item.2.name) queues.2.2 = none then
    if ready item.2.expression then enqueue origin item queues else queues
  else queues

def wake (ready : Expression → Bool) (origin : Option Rank)
    (input : List Item) (queues : Queues) : Queues :=
  input.foldl (wakeStep ready origin) queues

theorem wake_nil (ready : Expression → Bool) (origin : Option Rank) (queues : Queues) :
    wake ready origin [] queues = queues := rfl

theorem wake_cons (ready : Expression → Bool) (origin : Option Rank)
    (item : Item) (rest : List Item) (queues : Queues) :
    wake ready origin (item :: rest) queues =
      wake ready origin rest (wakeStep ready origin queues item) := rfl

theorem wake_append (ready : Expression → Bool) (origin : Option Rank)
    (first second : List Item) (queues : Queues) :
    wake ready origin (first ++ second) queues =
      wake ready origin second (wake ready origin first queues) := by
  simp [wake, List.foldl_append]

/-- Every found payload suppresses scheduling, even a non-name payload.
Wake does not compare the stored payload with the candidate's name. -/
theorem found_payload_skips (ready : Expression → Bool) (origin : Option Rank)
    (item : Item) (rest : List Item) (queues : Queues) (payload : SExpr)
    (found : lookup (key item.2.name) queues.2.2 = some payload) :
    wake ready origin (item :: rest) queues = wake ready origin rest queues := by
  simp [wake_cons, wakeStep, found]

theorem unready_skips (ready : Expression → Bool) (origin : Option Rank)
    (item : Item) (rest : List Item) (queues : Queues)
    (unready : ready item.2.expression = false) :
    wake ready origin (item :: rest) queues = wake ready origin rest queues := by
  simp [wake_cons, wakeStep, unready]

theorem ready_missing_enqueues (ready : Expression → Bool) (origin : Option Rank)
    (item : Item) (rest : List Item) (queues : Queues)
    (missing : lookup (key item.2.name) queues.2.2 = none)
    (available : ready item.2.expression = true) :
    wake ready origin (item :: rest) queues =
      wake ready origin rest (enqueue origin item queues) := by
  simp [wake_cons, wakeStep, missing, available]

theorem enqueue_mark (origin : Option Rank) (item : Item) (queues : Queues) :
    lookup (key item.2.name) (enqueue origin item queues).2.2 =
      (lookup (key item.2.name) queues.2.2).or (some (name (key item.2.name))) := by
  exact PlainBnfGraphNameTrie.lookup_inserted _ _ _

theorem enqueue_preserves_existing (origin : Option Rank) (item : Item) (queues : Queues)
    (query : List Nat) (payload : SExpr) (found : lookup query queues.2.2 = some payload) :
    lookup query (enqueue origin item queues).2.2 = some payload := by
  simp only [enqueue, PlainBnfGraphNameTrie.lookup_insertFirst]
  split <;> simp_all

theorem wake_preserves_existing (ready : Expression → Bool) (origin : Option Rank)
    (input : List Item) (queues : Queues) (query : List Nat) (payload : SExpr)
    (found : lookup query queues.2.2 = some payload) :
    lookup query (wake ready origin input queues).2.2 = some payload := by
  induction input generalizing queues with
  | nil => exact found
  | cons item rest ih =>
      rw [wake_cons]
      apply ih
      unfold wakeStep
      split
      · split
        · exact enqueue_preserves_existing origin item queues query payload found
        · exact found
      · exact found

/-- This ledger observes which original occurrences are newly scheduled.
It is not an execution provider or an unordered set of names. -/
def selected (ready : Expression → Bool) : List Item → Trie SExpr → List Item
  | [], _ => []
  | item :: rest, scheduled =>
      if lookup (key item.2.name) scheduled = none then
        if ready item.2.expression then
          item :: selected ready rest
            (insertFirst (key item.2.name) (name (key item.2.name)) scheduled)
        else selected ready rest scheduled
      else selected ready rest scheduled

theorem selected_sublist (ready : Expression → Bool) (input : List Item) (scheduled : Trie SExpr) :
    (selected ready input scheduled).Sublist input := by
  induction input generalizing scheduled with
  | nil => exact .refl []
  | cons item rest ih =>
      simp only [selected]
      split
      · split
        · exact (ih _).cons_cons item
        · exact (ih _).cons item
      · exact (ih _).cons item

theorem selected_is_ready (ready : Expression → Bool) (input : List Item) (scheduled : Trie SExpr)
    (item : Item) (member : item ∈ selected ready input scheduled) :
    ready item.2.expression = true := by
  induction input generalizing scheduled with
  | nil => simp [selected] at member
  | cons first rest ih =>
      simp only [selected] at member
      split at member
      · split at member
        · rcases List.mem_cons.mp member with equal | inside
          · subst item; assumption
          · exact ih _ inside
        · exact ih _ member
      · exact ih _ member

theorem selected_initially_missing (ready : Expression → Bool) (input : List Item)
    (scheduled : Trie SExpr) (item : Item) (member : item ∈ selected ready input scheduled) :
    lookup (key item.2.name) scheduled = none := by
  induction input generalizing scheduled with
  | nil => simp [selected] at member
  | cons first rest ih =>
      simp only [selected] at member
      split at member
      · split at member
        · rcases List.mem_cons.mp member with equal | inside
          · subst item; assumption
          · have missing := ih _ inside
            rw [PlainBnfGraphNameTrie.lookup_insertFirst] at missing
            split at missing
            · simp at missing
            · exact missing
        · exact ih _ member
      · exact ih _ member

theorem selected_names_nodup (ready : Expression → Bool) (input : List Item)
    (scheduled : Trie SExpr) :
    ((selected ready input scheduled).map (fun item => key item.2.name)).Nodup := by
  induction input generalizing scheduled with
  | nil => simp [selected]
  | cons first rest ih =>
      simp only [selected]
      split
      · split
        · simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, ih _⟩
          intro duplicate
          obtain ⟨other, member, same⟩ := List.mem_map.mp duplicate
          have missing := selected_initially_missing ready rest _ other member
          rw [same, PlainBnfGraphNameTrie.lookup_inserted] at missing
          simp at missing
        · exact ih _
      · exact ih _

theorem wake_eq_ordered_schedules (ready : Expression → Bool) (origin : Option Rank)
    (input : List Item) (queues : Queues) :
    wake ready origin input queues =
      (selected ready input queues.2.2).foldl (fun current item => enqueue origin item current) queues := by
  induction input generalizing queues with
  | nil => rfl
  | cons item rest ih =>
      simp only [wake_cons, wakeStep, selected]
      split
      · split
        · simpa only [List.foldl_cons, enqueue] using ih (enqueue origin item queues)
        · exact ih queues
      · exact ih queues

def Ordered (queues : Queues) : Prop :=
  queues.1.WF itemLE ∧ queues.2.1.WF itemLE

theorem enqueue_ordered (origin : Option Rank) (item : Item) (queues : Queues)
    (ordered : Ordered queues) : Ordered (enqueue origin item queues) := by
  unfold Ordered enqueue
  cases toCurrent item.1 origin <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact ⟨ordered.1, Heap.WF.singleton.merge ordered.2⟩
  · exact ⟨Heap.WF.singleton.merge ordered.1, ordered.2⟩

private theorem noSibling_of_WF {heap : Heap HeapItem} (ordered : heap.WF itemLE) :
    heap.NoSibling := by cases ordered <;> constructor

variable {size : Nat}

def pending (coordinate : HeapItem → Fin size) (queues : Queues) : Finset (Fin size) :=
  positions coordinate queues.1 ∪ positions coordinate queues.2.1

theorem enqueue_pending (coordinate : HeapItem → Fin size) (origin : Option Rank)
    (item : Item) (queues : Queues) (ordered : Ordered queues) :
    pending coordinate (enqueue origin item queues) =
      insert (coordinate (heapItem item)) (pending coordinate queues) := by
  unfold pending enqueue PlainBnfScheduleSourceExecution.singleton
  cases toCurrent item.1 origin <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [positions_merge_singleton coordinate itemLE _ _ (noSibling_of_WF ordered.2)]
    simp [Finset.union_insert]
  · rw [positions_merge_singleton coordinate itemLE _ _ (noSibling_of_WF ordered.1)]
    simp

/-- Every queued position already has a persistent name mark. Published
positions may also retain marks; this condition never equates marks with only
the currently pending set. `nameAt` is supplied by the source coordinate map. -/
def MarkedPositions (coordinate : HeapItem → Fin size) (nameAt : Fin size → List Nat)
    (queues : Queues) : Prop :=
  ∀ position ∈ pending coordinate queues, lookup (nameAt position) queues.2.2 ≠ none

theorem missing_is_fresh (coordinate : HeapItem → Fin size) (nameAt : Fin size → List Nat)
    (item : Item) (queues : Queues)
    (marked : MarkedPositions coordinate nameAt queues)
    (keyCoordinate : nameAt (coordinate (heapItem item)) = key item.2.name)
    (missing : lookup (key item.2.name) queues.2.2 = none) :
    coordinate (heapItem item) ∉ pending coordinate queues := by
  intro member
  exact marked _ member (keyCoordinate ▸ missing)

theorem enqueue_marked (coordinate : HeapItem → Fin size) (nameAt : Fin size → List Nat)
    (origin : Option Rank) (item : Item) (queues : Queues)
    (ordered : Ordered queues) (marked : MarkedPositions coordinate nameAt queues)
    (keyCoordinate : nameAt (coordinate (heapItem item)) = key item.2.name) :
    MarkedPositions coordinate nameAt (enqueue origin item queues) := by
  intro position member
  rw [enqueue_pending coordinate origin item queues ordered] at member
  rcases Finset.mem_insert.mp member with same | old
  · subst position
    rw [keyCoordinate, enqueue_mark]
    simp
  · have found := marked position old
    cases stored : lookup (nameAt position) queues.2.2 with
    | none => exact False.elim (found stored)
    | some payload =>
        rw [enqueue_preserves_existing origin item queues _ payload stored]
        simp

def WellPlaced (coordinate : HeapItem → Fin size) (origin : Option Rank) (queues : Queues) : Prop :=
  Partitioned coordinate (pending coordinate queues)
    (PlainBnfScheduleWorklistBridge.cursor origin) queues.1 queues.2.1

theorem enqueue_wellPlaced (coordinate : HeapItem → Fin size) (origin : Option Rank)
    (item : Item) (queues : Queues) (ordered : Ordered queues)
    (placed : WellPlaced coordinate origin queues)
    (rankCoordinate : value item.1 = (coordinate (heapItem item)).val) :
    WellPlaced coordinate origin (enqueue origin item queues) := by
  have checked := PlainBnfScheduleWorklistBridge.execution_partition
    coordinate origin item.1 (key item.2.name) (expression item.2.expression) (span item.2.span)
    queues.1 queues.2.1 queues.2.2 (pending coordinate queues)
    ordered.1 ordered.2 placed rankCoordinate _ (enqueue_executes origin item queues)
  unfold WellPlaced
  rw [enqueue_pending coordinate origin item queues ordered]
  exact checked.2.1

theorem enqueue_unique (coordinate : HeapItem → Fin size) (origin : Option Rank)
    (item : Item) (queues : Queues) (ordered : Ordered queues)
    (unique : UniquePositions coordinate queues.1 queues.2.1)
    (fresh : coordinate (heapItem item) ∉ pending coordinate queues) :
    UniquePositions coordinate (enqueue origin item queues).1 (enqueue origin item queues).2.1 := by
  have checked := PlainBnfScheduleWorklistBridge.execution_unique
    coordinate origin item.1 (key item.2.name) (expression item.2.expression) (span item.2.span)
    queues.1 queues.2.1 queues.2.2 ordered.1 ordered.2 unique fresh _
    (enqueue_executes origin item queues)
  exact checked.2

/-- Wake's mark check supplies the freshness premise that the scheduling
clauses alone cannot establish. The coordinate/name hypotheses are explicit;
they are not inferred from arbitrary caller-supplied heaps. -/
theorem wake_invariants (ready : Expression → Bool) (coordinate : HeapItem → Fin size)
    (nameAt : Fin size → List Nat) (origin : Option Rank) (input : List Item) (queues : Queues)
    (ordered : Ordered queues) (placed : WellPlaced coordinate origin queues)
    (unique : UniquePositions coordinate queues.1 queues.2.1)
    (marked : MarkedPositions coordinate nameAt queues)
    (rankCoordinates : ∀ item ∈ input, value item.1 = (coordinate (heapItem item)).val)
    (keyCoordinates : ∀ item ∈ input, nameAt (coordinate (heapItem item)) = key item.2.name) :
    let after := wake ready origin input queues
    Ordered after ∧ WellPlaced coordinate origin after ∧
      UniquePositions coordinate after.1 after.2.1 ∧ MarkedPositions coordinate nameAt after := by
  induction input generalizing queues with
  | nil => exact ⟨ordered, placed, unique, marked⟩
  | cons item rest ih =>
      simp only [wake_cons]
      have restRanks : ∀ next ∈ rest, value next.1 = (coordinate (heapItem next)).val :=
        fun next member => rankCoordinates next (by simp [member])
      have restKeys : ∀ next ∈ rest, nameAt (coordinate (heapItem next)) = key next.2.name :=
        fun next member => keyCoordinates next (by simp [member])
      unfold wakeStep
      split
      · rename_i missing
        split
        · apply ih (enqueue origin item queues)
          · exact enqueue_ordered origin item queues ordered
          · exact enqueue_wellPlaced coordinate origin item queues ordered placed
              (rankCoordinates item (by simp))
          · exact enqueue_unique coordinate origin item queues ordered unique
              (missing_is_fresh coordinate nameAt item queues marked
                (keyCoordinates item (by simp)) missing)
          · exact enqueue_marked coordinate nameAt origin item queues ordered marked
              (keyCoordinates item (by simp))
          · exact restRanks
          · exact restKeys
        · exact ih queues ordered placed unique marked restRanks restKeys
      · exact ih queues ordered placed unique marked restRanks restKeys

def contents (queues : Queues) : Multiset HeapItem :=
  PlainBnfPairingHeapObservation.contents queues.1 +
    PlainBnfPairingHeapObservation.contents queues.2.1

theorem enqueue_contents (origin : Option Rank) (item : Item) (queues : Queues)
    (ordered : Ordered queues) :
    contents (enqueue origin item queues) = heapItem item ::ₘ contents queues := by
  unfold contents enqueue
  cases toCurrent item.1 origin <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [PlainBnfPairingHeapObservation.contents_merge itemLE
      (by constructor) (noSibling_of_WF ordered.2)]
    simp [PlainBnfScheduleSourceExecution.singleton,
      PlainBnfPairingHeapObservation.contents, Multiset.add_cons]
  · rw [PlainBnfPairingHeapObservation.contents_merge itemLE
      (by constructor) (noSibling_of_WF ordered.1)]
    simp [PlainBnfScheduleSourceExecution.singleton, PlainBnfPairingHeapObservation.contents]

theorem wake_contents (ready : Expression → Bool) (origin : Option Rank)
    (input : List Item) (queues : Queues) (ordered : Ordered queues) :
    contents (wake ready origin input queues) =
      (↑((selected ready input queues.2.2).map heapItem) : Multiset HeapItem) + contents queues := by
  induction input generalizing queues with
  | nil => simp [wake_nil, selected]
  | cons item rest ih =>
      simp only [wake_cons, wakeStep, selected]
      split
      · split
        · rw [ih _ (enqueue_ordered origin item queues ordered), enqueue_contents origin item queues ordered]
          simp only [enqueue, List.map_cons, ← Multiset.cons_coe, Multiset.add_cons, Multiset.cons_add]
        · exact ih queues ordered
      · exact ih queues ordered

theorem pending_from_contents (coordinate : HeapItem → Fin size) (queues : Queues) :
    pending coordinate queues = ((contents queues).map coordinate).toFinset := by
  simp [pending, positions, contents]

theorem wake_pending (ready : Expression → Bool) (coordinate : HeapItem → Fin size)
    (origin : Option Rank) (input : List Item) (queues : Queues) (ordered : Ordered queues) :
    pending coordinate (wake ready origin input queues) =
      ((selected ready input queues.2.2).map (fun item => coordinate (heapItem item))).toFinset ∪
        pending coordinate queues := by
  rw [pending_from_contents, wake_contents ready origin input queues ordered,
    pending_from_contents]
  simp [List.map_map, Function.comp_def]

theorem lookup_ordered_schedules (origin : Option Rank) (input : List Item)
    (queues : Queues) (query : List Nat) :
    lookup query
        (input.foldl (fun current item => enqueue origin item current) queues).2.2 =
      (lookup query queues.2.2).or
        (if query ∈ input.map (fun item => key item.2.name) then some (name query) else none) := by
  induction input generalizing queues with
  | nil => simp
  | cons item rest ih =>
      rw [List.foldl_cons, ih]
      simp only [enqueue, PlainBnfGraphNameTrie.lookup_insertFirst, List.map_cons,
        List.mem_cons]
      by_cases same : query = key item.2.name
      · subst query
        cases lookup (key item.2.name) queues.2.2 <;> simp
      · simp only [same, false_or]
        cases lookup query queues.2.2 <;> rfl

theorem wake_marks_exact (ready : Expression → Bool) (origin : Option Rank)
    (input : List Item) (queues : Queues) (query : List Nat) :
    lookup query (wake ready origin input queues).2.2 =
      (lookup query queues.2.2).or
        (if query ∈ (selected ready input queues.2.2).map (fun item => key item.2.name)
          then some (name query) else none) := by
  rw [wake_eq_ordered_schedules, lookup_ordered_schedules]

/-- Repetition in dependency buckets does not enqueue a second occurrence
after a name has been marked. The original occurrence ledger is not edited. -/
theorem repeated_name_suppressed (ready : Expression → Bool) (origin : Option Rank)
    (first second : Item) (queues : Queues)
    (sameName : first.2.name = second.2.name)
    (missing : lookup (key first.2.name) queues.2.2 = none)
    (available : ready first.2.expression = true) :
    selected ready [first, second] queues.2.2 = [first] ∧
      wake ready origin [first, second] queues = enqueue origin first queues := by
  have sameKey : key second.2.name = key first.2.name := congrArg key sameName.symm
  have marked : lookup (key second.2.name) (enqueue origin first queues).2.2 =
      some (name (key first.2.name)) := by
    rw [sameKey, enqueue_mark, missing]
    rfl
  constructor
  · simp [selected, missing, available, sameKey, PlainBnfGraphNameTrie.lookup_insertFirst]
  · rw [ready_missing_enqueues ready origin first [second] queues missing available,
      found_payload_skips ready origin second [] _ _ marked, wake_nil]

/-- Deduplicating input before testing readiness is unsound on arbitrary
occurrences with the same name: an unready first body must not hide a later
ready body. Admission may separately exclude such duplicate declarations. -/
theorem unready_first_does_not_hide_ready_second (ready : Expression → Bool)
    (first second : Item) (scheduled : Trie SExpr)
    (missing : lookup (key second.2.name) scheduled = none)
    (unavailable : ready first.2.expression = false)
    (available : ready second.2.expression = true) :
    selected ready [first, second] scheduled = [second] := by
  simp [selected, unavailable, available, missing]

theorem initially_marked_input_is_unchanged (ready : Expression → Bool) (origin : Option Rank)
    (input : List Item) (queues : Queues)
    (marked : ∀ item ∈ input, lookup (key item.2.name) queues.2.2 ≠ none) :
    wake ready origin input queues = queues := by
  induction input with
  | nil => rfl
  | cons item rest ih =>
      rw [wake_cons]
      simp only [wakeStep, if_neg (marked item (by simp))]
      exact ih (fun next member => marked next (by simp [member]))

theorem distinct_ready_occurrences_retain_order (ready : Expression → Bool)
    (first second : Item) (different : first.2.name ≠ second.2.name)
    (firstReady : ready first.2.expression = true)
    (secondReady : ready second.2.expression = true) :
    selected ready [first, second] .empty = [first, second] := by
  have differentKeys : key second.2.name ≠ key first.2.name := by
    intro same
    exact different (PlainBnfReverseIndexSourceExecution.key_injective same).symm
  simp [selected, firstReady, secondReady, PlainBnfGraphNameTrie.lookup_insertFirst, differentKeys]

theorem reversing_selected_occurrences_is_not_authorized (ready : Expression → Bool)
    (first second : Item) (different : first.2.name ≠ second.2.name)
    (firstReady : ready first.2.expression = true)
    (secondReady : ready second.2.expression = true) :
    selected ready [first, second] .empty ≠ [second, first] := by
  rw [distinct_ready_occurrences_retain_order ready first second different firstReady secondReady]
  intro equal
  have firstEqual := (List.cons.inj equal).1
  exact different (congrArg (fun item : Item => item.2.name) firstEqual)

/-- Arbitrary stale marks can suppress a ready candidate while both heaps
are empty. A whole-controller theorem must establish mark provenance, not
infer it merely from the freshness invariant above. -/
theorem stale_mark_can_suppress (ready : Expression → Bool) (item : Item) (payload : SExpr) :
    let queues : Queues :=
      (.nil, .nil, insertFirst (key item.2.name) payload .empty)
    wake ready none [item] queues = queues := by
  dsimp only
  apply initially_marked_input_is_unchanged
  intro other member
  have same : other = item := by simpa using member
  subst other
  simp [PlainBnfGraphNameTrie.lookup_insertFirst]

section AuthoredClauses

open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Rewrite decodeList)
open Mettapedia.OSLF.MeTTaIL.Syntax (Premise RewriteRule)
open SourceSExprPatternInstantiation (pattern)

def wakeMode? : String → Option (Nat × Nat)
  | "BNFDiscoveryWakeV1" => some (6, 1)
  | "BNFDiscoveryAfterScheduledV1" | "BNFDiscoveryAfterReadyV1" => some (8, 1)
  | _ => none

def mode? (relation : String) : Option (Nat × Nat) :=
  if relation = "BNFDiscoveryReadyV1" then some (4, 1)
  else (wakeMode? relation).or (PlainBnfScheduleSourceExecution.mode? relation)

def splitCall? : SExpr → Option (SExpr × SExpr)
  | .list (.atom relation :: arguments) => do
      let (inputs, outputs) ← mode? relation
      if arguments.length = inputs + outputs then
        some (.list (.atom relation :: arguments.take inputs), .list (arguments.drop inputs))
      else none
  | _ => none

/-- Ready is translated as an ordinary recursive source call, never a
primitive that supplies the final readiness result. -/
def lowerPremise? (source : SExpr) : Option Premise := do
  let (input, output) ← splitCall? source
  some (.congruence (pattern input) (pattern output))

def lowerRule? (source : Rewrite) : Option RewriteRule := do
  let (input, output) ← splitCall? source.head
  let premises ← decodeList lowerPremise? source.body
  some {
    name := source.name
    typeContext := []
    premises := premises
    left := pattern input
    right := pattern output }

def rows : List Rewrite :=
  (PlainBnfCollectorSourceAdmission.discoverySource.rewrites.drop 67).take 6

def rules : List RewriteRule := (rows.mapM lowerRule?).get (by rfl)

theorem source_translation_exact : rows.mapM lowerRule? = some rules := rfl

theorem source_occurrences_exact : rows.zipIdx 67 =
    ((PlainBnfCollectorSourceAdmission.discoverySource.rewrites.zipIdx).drop 67).take 6 := rfl

theorem source_family_exhaustive :
    PlainBnfCollectorSourceAdmission.discoverySource.rewrites.filter (fun row =>
      match row.head with
      | .list (.atom head :: _) => (wakeMode? head).isSome
      | _ => false) = rows := rfl

theorem translated_calls_are_not_providers :
    rules.all (fun rule => rule.premises.all (fun
      | .congruence _ _ => true
      | _ => false)) = true := rfl

end AuthoredClauses

#print axioms enqueue_executes
#print axioms selected_names_nodup
#print axioms wake_eq_ordered_schedules
#print axioms wake_invariants
#print axioms wake_contents
#print axioms wake_pending
#print axioms wake_marks_exact
#print axioms source_translation_exact

end Mettapedia.GSLT.Parsing.PlainBnfWakeSourceExecution
