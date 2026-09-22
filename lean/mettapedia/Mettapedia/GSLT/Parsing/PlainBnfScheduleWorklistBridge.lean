import Mettapedia.GSLT.Parsing.PlainBnfScheduleSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfHeapCombineSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfTwoHeapWorklist

/-!
# Authored scheduling preserves the two-heap worklist observation

The selected actual source clauses execute the existing heap merge and trie
insertion; the actual child-forest combine supplies removal of the published
root. Their exact execution results are connected here to the independent
source-position partition and uniqueness laws. No new queue carrier or
execution mechanism is introduced.

The source wake loop must separately establish freshness, and ranked source
enumeration must establish coordinates. In particular, scheduling alone does
not suppress a duplicate name, and the persistent scheduled trie is not just
the pending queue. This module does not claim whole-loop or native adequacy.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfScheduleWorklistBridge

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises)
open PlainBnfSourceRank (Rank value)
open PlainBnfHeapSourceExecution (Item itemLE)
open PlainBnfGraphNameTrie (Trie insertFirst)
open PlainBnfCollectorSourceExecution (NameScalarCodec name)
open PlainBnfTrieSourceExecution (scalarRelations)
open PlainBnfRankSourceExecution (result)
open PlainBnfScheduleSourceExecution
  (language node queues singleton updated toCurrent scheduleCall schedule_step_iff)
open PlainBnfTwoHeapWorklist
open Batteries.PairingHeapImp (Heap)

variable {Scalar : Type} [NameScalarCodec Scalar] [DecidableEq Scalar] {size : Nat}

/-- The source stores the last published rank. The independent scan stores
the first not-yet-scanned position, hence the successor in the second case. -/
def cursor : Option Rank → Nat
  | none => 0
  | some origin => value origin + 1

theorem toCurrent_iff_suffix (priority : Rank) (origin : Option Rank) :
    toCurrent priority origin = true ↔ cursor origin ≤ value priority := by
  cases origin with
  | none => simp [toCurrent, cursor]
  | some origin =>
      rw [PlainBnfScheduleSourceExecution.toCurrent_after_iff]
      simp only [cursor]
      omega

private theorem noSibling_of_WF {heap : Heap Item} (ordered : heap.WF itemLE) :
    heap.NoSibling := by cases ordered <;> constructor

/-- An arbitrary result of actual source scheduling has the exact queue
components below; those components preserve the independent cursor partition
and heap ordering. Only the scheduled item's live coordinate is required. -/
theorem execution_partition
    (coordinate : Item → Fin size) (origin : Option Rank) (priority : Rank)
    (key : List Scalar) (expression span : SExpr)
    (current following : Heap Item) (scheduled : Trie SExpr Scalar)
    (pending : Finset (Fin size))
    (currentWF : current.WF itemLE) (followingWF : following.WF itemLE)
    (partition : Partitioned coordinate pending (cursor origin) current following)
    (itemCoordinate : value priority = (coordinate (node priority key expression span)).val)
    (target : Pattern)
    (executed : Step (engineBasePremises scalarRelations) language
      (scheduleCall origin (node priority key expression span) current following scheduled) target) :
    let item := node priority key expression span
    let nextCurrent := if toCurrent priority origin then (singleton item).merge itemLE current else current
    let nextFollowing := if toCurrent priority origin then following else (singleton item).merge itemLE following
    target = result (queues nextCurrent nextFollowing (insertFirst key (name key) scheduled)) ∧
      Partitioned coordinate (insert (coordinate item) pending) (cursor origin) nextCurrent nextFollowing ∧
      nextCurrent.WF itemLE ∧ nextFollowing.WF itemLE := by
  dsimp only
  refine ⟨?_, ?_⟩
  · simpa only [updated] using
      (schedule_step_iff origin priority key expression span current following scheduled target).mp executed
  · cases side : toCurrent priority origin with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have bound : value priority < cursor origin := by
          have notLater : ¬ cursor origin ≤ value priority := by
            intro later
            have wrong := (toCurrent_iff_suffix priority origin).mpr later
            rw [side] at wrong
            cases wrong
          omega
        refine ⟨?_, currentWF, ?_⟩
        · exact enqueue_following_partition coordinate itemLE _ current following
            (noSibling_of_WF followingWF) pending (cursor origin) partition
            (by simpa only [itemCoordinate] using bound)
        · exact Heap.WF.singleton.merge followingWF
    | true =>
        simp only [↓reduceIte]
        refine ⟨?_, ?_, followingWF⟩
        · exact enqueue_current_partition coordinate itemLE _ current following
            (noSibling_of_WF currentWF) pending (cursor origin) partition
            (by simpa only [itemCoordinate] using (toCurrent_iff_suffix priority origin).mp side)
        · exact Heap.WF.singleton.merge currentWF

/-- Freshness is an explicit premise furnished by Wake's scheduled-name
test and the name/position correspondence, not by the scheduling clauses. -/
theorem execution_unique
    (coordinate : Item → Fin size) (origin : Option Rank) (priority : Rank)
    (key : List Scalar) (expression span : SExpr)
    (current following : Heap Item) (scheduled : Trie SExpr Scalar)
    (currentWF : current.WF itemLE) (followingWF : following.WF itemLE)
    (unique : UniquePositions coordinate current following)
    (fresh : coordinate (node priority key expression span) ∉
      positions coordinate current ∪ positions coordinate following)
    (target : Pattern)
    (executed : Step (engineBasePremises scalarRelations) language
      (scheduleCall origin (node priority key expression span) current following scheduled) target) :
    let item := node priority key expression span
    let nextCurrent := if toCurrent priority origin then (singleton item).merge itemLE current else current
    let nextFollowing := if toCurrent priority origin then following else (singleton item).merge itemLE following
    target = result (queues nextCurrent nextFollowing (insertFirst key (name key) scheduled)) ∧
      UniquePositions coordinate nextCurrent nextFollowing := by
  dsimp only
  constructor
  · simpa only [updated] using
      (schedule_step_iff origin priority key expression span current following scheduled target).mp executed
  · cases side : toCurrent priority origin with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact enqueue_following_unique coordinate itemLE _ current following
          (noSibling_of_WF followingWF) unique fresh
    | true =>
        simp only [↓reduceIte]
        exact enqueue_current_unique coordinate itemLE _ current following
          (noSibling_of_WF currentWF) unique fresh

/-- The actual combine call used after publication yields precisely the heap
on which the pop/advance law applies. This does not yet execute Run or Wake. -/
theorem combine_execution_pop
    (env : RelationEnv) (coordinate : Item → Fin size)
    (item : Item) (children following rest : Heap Item)
    (pending : Finset (Fin size)) (before : Nat)
    (ordered : (Heap.node item children .nil).WF itemLE)
    (coordinates : ∀ a ∈ PlainBnfPairingHeapObservation.contents (.node item children .nil),
      ∀ b ∈ PlainBnfPairingHeapObservation.contents (.node item children .nil),
      itemLE a b = true → coordinate a ≤ coordinate b)
    (unique : UniquePositions coordinate (.node item children .nil) following)
    (partition : Partitioned coordinate pending before (.node item children .nil) following)
    (executed : Step (engineBasePremises env) PlainBnfHeapCombineSourceExecution.language
      (PlainBnfHeapCombineSourceExecution.combineCall children)
      (result (PlainBnfHeapSourceExecution.heap rest))) :
    Partitioned coordinate (pending.erase (coordinate item)) ((coordinate item).val + 1) rest following ∧
      UniquePositions coordinate rest following ∧ rest.WF itemLE := by
  have exactRest := (PlainBnfHeapCombineSourceExecution.combine_decoded_step_iff env children rest).mp executed
  have popped : (Heap.node item children .nil).deleteMin itemLE = some (item, rest) := by
    rw [exactRest]
    rfl
  refine ⟨?_, pop_current_unique coordinate itemLE (.node _ _) unique popped,
    ordered.deleteMin popped⟩
  exact pop_current_partition coordinate itemLE
    (fun first second => PlainBnfSourceRank.rankLE_trans first second)
    ordered coordinates (unique_current coordinate unique) popped pending before partition

/-- In source-position terms the equal case belongs to the following round,
not the current suffix. Both ranks must be related to their original source
positions, including the already-published origin outside the current heap. -/
theorem source_coordinate_branch (origin target : Rank) (before after : Fin size)
    (originCoordinate : value origin = before.val)
    (targetCoordinate : value target = after.val) :
    toCurrent target (some origin) = true ↔ before.val < after.val := by
  rw [toCurrent_iff_suffix]
  simp only [cursor, originCoordinate, targetCoordinate]
  omega

open PlainBnfEnumerationSourceExecution (enumerate value_iterate)

/-- The coordinate used above is supplied by the original source enumeration,
whose execution correspondence is proved in EnumerationSourceExecution. It
does not depend on names being unequal or on expressions being different. -/
theorem enumerated_rank_coordinate
    (input : List PlainBnfHeapSourceExecution.Definition) (index : Fin input.length) :
    value ((enumerate input .zero)[index.val]'(by
      simpa only [enumerate, List.length_map, List.length_zipIdx] using index.isLt)).1 =
      index.val := by
  simp [enumerate, value_iterate, PlainBnfSourceRank.value]

theorem enumerated_source_branch
    (input : List PlainBnfHeapSourceExecution.Definition) (before after : Fin input.length) :
    toCurrent ((enumerate input .zero)[after.val]'(by
      simpa only [enumerate, List.length_map, List.length_zipIdx] using after.isLt)).1
      (some ((enumerate input .zero)[before.val]'(by
        simpa only [enumerate, List.length_map, List.length_zipIdx] using before.isLt)).1) = true ↔
      before.val < after.val := by
  rw [PlainBnfScheduleSourceExecution.toCurrent_after_iff,
    enumerated_rank_coordinate input before, enumerated_rank_coordinate input after]

#print axioms execution_partition
#print axioms execution_unique
#print axioms combine_execution_pop
#print axioms source_coordinate_branch
#print axioms enumerated_source_branch

end Mettapedia.GSLT.Parsing.PlainBnfScheduleWorklistBridge
