import Mettapedia.Machines.Cursor.ReaderDenseMultiplicity

/-!
# Packed multiplicity controls and exportable native expectations
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderDenseMultiplicity.Controls

def singleton (copies : Nat) : Table := ⟨0, 1, fun tuple => if tuple = 0 then [⟨0, copies⟩] else []⟩
def original : Table := singleton 3
def warmed : Reader := (step original (start original)).2

def afterAdd : Table := addCopy original 0
def afterOne : Table := removeOne original 0
def afterAll : Table := removeAll original 0
def afterAddOne : Table := removeOne afterAdd 0
def afterAddAll : Table := removeAll afterAdd 0

theorem original_reader_count : warmed = ⟨0, 1, 0, 1, some 3⟩ := by decide

theorem live_count_is_not_old_residual :
    remaining afterAdd warmed = 2 ∧ liveCount afterAdd 0 - warmed.used = 3 := by decide

theorem remove_one_does_not_shrink_old_residual :
    remaining afterOne warmed = 2 ∧ liveCount afterOne 0 - warmed.used = 1 := by decide

theorem remove_all_does_not_erase_old_residual :
    remaining afterAll warmed = 2 ∧ liveCount afterAll 0 = 0 := by decide

theorem add_then_remove_one_can_mask_bad_counting :
    remaining afterAddOne warmed = 2 ∧ liveCount afterAddOne 0 - warmed.used = 2 := by decide

def twoTuples : Table := ⟨0, 2, fun tuple =>
  if tuple = 0 then [⟨0, 1⟩] else if tuple = 1 then [⟨0, 3⟩] else []⟩

def firstDelivered : Reader := (step twoTuples (start twoTuples)).2
def targetChanged : Table := addCopy twoTuples 1
def targetReached : Reader := (step targetChanged firstDelivered).2

/-- Tuple0 was delivered first. Tuple1 changed before any visit; its first
visit must still capture3 at epoch0, even though its live count is now4. -/
theorem delayed_first_visit_uses_entry_epoch :
    (step twoTuples (start twoTuples)).1 = .copy 0 0 ∧
      targetReached = ⟨0, 2, 1, 0, none⟩ ∧
      liveCount targetChanged 1 = 4 ∧ quota targetChanged targetReached = 3 ∧
      run targetChanged 10 targetReached = [(1, 0), (1, 1), (1, 2)] := by decide

def badQuota (table : Table) (reader : Reader) : Nat :=
  match reader.cached with
  | some copies => copies
  | none => liveCount table reader.tuple

theorem first_visit_live_capture_is_wrong :
    badQuota targetChanged targetReached = 4 ∧ quota targetChanged targetReached = 3 := by decide

structure ThinSummary where
  clock : Nat
  tupleCeiling : Nat
  tuple : Nat
  born : Nat
  death : Option Nat
  currentCopies : Nat
  entryEpoch : Nat
  delivered : Nat
  deriving Repr, DecidableEq

def summary (table : Table) (reader : Reader) : ThinSummary :=
  ⟨table.clock, reader.ceiling, reader.tuple, 0,
    if liveCount table reader.tuple = 0 then some table.clock else none,
    liveCount table reader.tuple, reader.epoch, reader.used⟩

def otherOriginal : Table := singleton 4
def otherReader : Reader := (step otherOriginal (start otherOriginal)).2
def otherCurrent : Table := publish otherOriginal 0 4

theorem ceiling_and_death_stamp_do_not_determine_old_count :
    summary afterAdd warmed = summary otherCurrent otherReader ∧
      remaining afterAdd warmed = 2 ∧ remaining otherCurrent otherReader = 3 := by decide

theorem no_thin_summary_decoder (recover : ThinSummary → Nat) :
    ¬ (recover (summary afterAdd warmed) = 2 ∧
      recover (summary otherCurrent otherReader) = 3) := by
  intro ⟨first, second⟩
  rw [(ceiling_and_death_stamp_do_not_determine_old_count).1] at first
  omega

def caseTable (scenario : Nat) (he : Bool) : Table :=
  match scenario with
  | 0 => afterAdd
  | 1 => if he then afterOne else afterAll
  | _ => if he then afterAddOne else afterAddAll

def markers (count : Nat) : String :=
  "(" ++ String.intercalate " " (List.replicate count "x") ++ ")"

def expected (scenario : Nat) (he : Bool) : String :=
  let table := caseTable scenario he
  "(rr-packed (x) " ++ markers (run table 10 warmed).length ++ " " ++
    markers (liveCount table 0) ++ ")"

theorem all_ground_expected_counts :
    (run afterAdd 10 warmed).length = 2 ∧ liveCount afterAdd 0 = 4 ∧
    (run afterOne 10 warmed).length = 2 ∧ liveCount afterOne 0 = 2 ∧
    (run afterAll 10 warmed).length = 2 ∧ liveCount afterAll 0 = 0 ∧
    (run afterAddOne 10 warmed).length = 2 ∧ liveCount afterAddOne 0 = 3 ∧
    (run afterAddAll 10 warmed).length = 2 ∧ liveCount afterAddAll 0 = 0 := by decide

def fillerBag (count : Nat) : List Int := (List.range count).map (fun n => Int.ofNat (n + 1))
def initialBag (count : Nat) : List Int := fillerBag count ++ [0, 0, 0, -1, -1, -1]

theorem initial_bag_size (count : Nat) : (initialBag count).length = count + 6 := by
  simp [initialBag, fillerBag]

def packedInitial (count : Nat) : Table :=
  ⟨0, count + 2, fun tuple => [⟨0, if tuple < count then 1 else if tuple < count + 2 then 3 else 0⟩]⟩

def decode (count tuple : Nat) : Int :=
  if tuple < count then Int.ofNat (tuple + 1) else if tuple = count then 0 else -1

theorem packed_initial_bag (count : Nat) :
    (entryCopies (packedInitial count) 0 (count + 2)).map (decode count) = initialBag count := by
  have prefixCopies : (List.range count).flatMap
      (fun tuple => List.replicate (countAt (packedInitial count) 0 tuple) tuple) = List.range count := by
    calc
      _ = (List.range count).flatMap (fun tuple => [tuple]) := by
        apply List.flatMap_congr
        intro tuple member
        simp [countAt, packedInitial, lookupCount, List.mem_range.mp member]
      _ = _ := by simp
  have decodedPrefix : (List.range count).map (decode count) = fillerBag count := by
    unfold fillerBag
    apply List.map_congr_left
    intro tuple member
    simp [decode, List.mem_range.mp member]
  simp only [entryCopies, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    prefixCopies]
  simp [countAt, packedInitial, lookupCount, List.map_append, decodedPrefix, decode, initialBag]

def exportLines : List String := (List.range 3).flatMap fun scenario =>
  [toString scenario ++ "-he\t" ++ expected scenario true,
   toString scenario ++ "-petta\t" ++ expected scenario false]

#eval for line in exportLines do IO.println line
#print axioms delayed_first_visit_uses_entry_epoch
#print axioms no_thin_summary_decoder
#print axioms all_ground_expected_counts
#print axioms countAt_all_edits
#print axioms quota_is_entry_count
#print axioms packed_initial_bag

end Mettapedia.Machines.Cursor.ReaderDenseMultiplicity.Controls
