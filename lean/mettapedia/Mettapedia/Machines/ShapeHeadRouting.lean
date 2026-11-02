import Mettapedia.Machines.HybridShapeStore

/-!
# Per-head promotion with an all-rows trace oracle

Promotion changes routing, not the placement of older rows. Admitted new facts
use the compact component only after their head is enabled; equal compact facts
spill to ordinary rows. Settling one head materializes its compact facts and
disables that head. Queries observe both components as a bag.

The trace theorem covers every sequential interleaving of logical atomic
operations, including promotion and settling. It is not a proof of concurrent
publication, native admission, row lifetimes, or C execution.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ShapeHeadRouting

open HybridShapeStore

variable {Head Fact : Type} [DecidableEq Head] [DecidableEq Fact]

structure State (Head Fact : Type) where
  enabled : Head → Bool
  data : Store Fact

def fromRows (rows : Multiset Fact) : State Head Fact := ⟨fun _ => false, ⟨∅, rows⟩⟩

def observe (s : State Head Fact) : Multiset Fact := denote s.data

def Valid (head : Fact → Head) (eligible : Fact → Bool) (s : State Head Fact) : Prop :=
  ∀ x ∈ s.data.compact, s.enabled (head x) = true ∧ eligible x = true

def promote (h : Head) (s : State Head Fact) : State Head Fact :=
  { s with enabled := Function.update s.enabled h true }

def add (head : Fact → Head) (eligible : Fact → Bool) (x : Fact) (s : State Head Fact) : State Head Fact :=
  { s with data := if s.enabled (head x) && eligible x then HybridShapeStore.add x s.data
      else ⟨s.data.compact, x ::ₘ s.data.rows⟩ }

def remove (x : Fact) (s : State Head Fact) : Bool × State Head Fact :=
  let answer := removeOne x s.data
  (answer.1, { s with data := answer.2 })

def settleHead (head : Fact → Head) (h : Head) (s : State Head Fact) : State Head Fact :=
  ⟨Function.update s.enabled h false,
    ⟨s.data.compact.filter (fun x => head x ≠ h),
      (s.data.compact.filter (fun x => head x = h)).val + s.data.rows⟩⟩

def matchPhysical (accept : Fact → Bool) (s : State Head Fact) : Multiset Fact :=
  s.data.compact.val.filter (fun x => accept x = true) +
    s.data.rows.filter (fun x => accept x = true)

def countPhysical (x : Fact) (s : State Head Fact) : Nat :=
  (if x ∈ s.data.compact then 1 else 0) + s.data.rows.count x

omit [DecidableEq Head] [DecidableEq Fact] in
@[simp] theorem observe_fromRows (rows : Multiset Fact) :
    observe (fromRows (Head := Head) rows) = rows := by simp [observe, fromRows, denote]

omit [DecidableEq Fact] in
@[simp] theorem observe_promote (h : Head) (s : State Head Fact) :
    observe (promote h s) = observe s := rfl

omit [DecidableEq Fact] in
theorem promotion_keeps_old_rows (h : Head) (s : State Head Fact) :
    (promote h s).data = s.data := rfl

omit [DecidableEq Head] [DecidableEq Fact] in
theorem disabled_head_has_no_compact (head : Fact → Head) (eligible : Fact → Bool)
    (s : State Head Fact) (valid : Valid head eligible s) (h : Head) (off : s.enabled h = false) :
    ∀ x ∈ s.data.compact, head x ≠ h := by
  intro x hx eq
  have enabled := (valid x hx).1
  rw [eq, off] at enabled
  cases enabled

omit [DecidableEq Head] in
@[simp] theorem observe_add (head : Fact → Head) (eligible : Fact → Bool)
    (x : Fact) (s : State Head Fact) : observe (add head eligible x s) = x ::ₘ observe s := by
  unfold add
  split
  · exact denote_add x s.data
  · simp [observe, denote]

omit [DecidableEq Head] in
@[simp] theorem observe_remove (x : Fact) (s : State Head Fact) :
    observe (remove x s).2 = (observe s).erase x := denote_removeOne x s.data

omit [DecidableEq Head] in
theorem remove_status (x : Fact) (s : State Head Fact) :
    (remove x s).1 = decide (x ∈ observe s) := by
  apply Bool.eq_iff_iff.mpr
  change (removeOne x s.data).1 = true ↔ decide (x ∈ denote s.data) = true
  rw [decide_eq_true_eq]
  exact removed_iff x s.data

omit [DecidableEq Fact] in
@[simp] theorem observe_settleHead (head : Fact → Head) (h : Head) (s : State Head Fact) :
    observe (settleHead head h s) = observe s := by
  simp only [observe, settleHead, denote, Finset.filter_val, ← add_assoc]
  rw [add_comm (Multiset.filter _ _) (Multiset.filter _ _), Multiset.filter_add_not]

omit [DecidableEq Head] [DecidableEq Fact] in
theorem matchPhysical_refines (accept : Fact → Bool) (s : State Head Fact) :
    matchPhysical accept s = (observe s).filter (fun x => accept x = true) := by
  simp [matchPhysical, observe, denote, Multiset.filter_add]

omit [DecidableEq Head] in
theorem countPhysical_refines (x : Fact) (s : State Head Fact) :
    countPhysical x s = (observe s).count x := (count_denote x s.data).symm

omit [DecidableEq Head] [DecidableEq Fact] in
theorem valid_fromRows (head : Fact → Head) (eligible : Fact → Bool) (rows : Multiset Fact) :
    Valid head eligible (fromRows rows) := by simp [Valid, fromRows]

omit [DecidableEq Fact] in
theorem valid_promote (head : Fact → Head) (eligible : Fact → Bool) (h : Head)
    (s : State Head Fact) (valid : Valid head eligible s) : Valid head eligible (promote h s) := by
  intro x hx
  refine ⟨?_, (valid x hx).2⟩
  by_cases he : head x = h <;> simp [promote, Function.update, he, (valid x hx).1]

omit [DecidableEq Head] in
theorem valid_add (head : Fact → Head) (eligible : Fact → Bool) (x : Fact)
    (s : State Head Fact) (valid : Valid head eligible s) : Valid head eligible (add head eligible x s) := by
  unfold add
  split
  · rename_i active
    have ha : s.enabled (head x) = true ∧ eligible x = true := by
      simpa only [Bool.and_eq_true] using active
    by_cases hc : x ∈ s.data.compact
    · simpa [Valid, HybridShapeStore.add, hc] using valid
    · intro y hy
      simp only [HybridShapeStore.add, if_neg hc, Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact ha
      · exact valid y hy
  · exact valid

omit [DecidableEq Head] in
theorem valid_remove (head : Fact → Head) (eligible : Fact → Bool) (x : Fact)
    (s : State Head Fact) (valid : Valid head eligible s) : Valid head eligible (remove x s).2 := by
  unfold remove removeOne
  split
  · intro y hy; exact valid y (Finset.mem_of_mem_erase hy)
  · split <;> exact valid

omit [DecidableEq Fact] in
theorem valid_settleHead (head : Fact → Head) (eligible : Fact → Bool) (h : Head)
    (s : State Head Fact) (valid : Valid head eligible s) : Valid head eligible (settleHead head h s) := by
  intro x hx
  obtain ⟨member, different⟩ := Finset.mem_filter.mp hx
  exact ⟨by simpa [settleHead, Function.update, different] using (valid x member).1,
    (valid x member).2⟩

inductive Op (Head Fact : Type) where
  | insert (x : Fact)
  | eraseOne (x : Fact)
  | promote (h : Head)
  | settle (h : Head)
  | matchRows (accept : Fact → Bool)
  | count (x : Fact)

inductive Answer (Fact : Type) where
  | silent
  | removed (found : Bool)
  | matches (rows : Multiset Fact)
  | count (n : Nat)
  deriving DecidableEq

def step (head : Fact → Head) (eligible : Fact → Bool) (op : Op Head Fact)
    (s : State Head Fact) : Answer Fact × State Head Fact :=
  match op with
  | .insert x => (.silent, add head eligible x s)
  | .eraseOne x => let result := remove x s; (.removed result.1, result.2)
  | .promote h => (.silent, promote h s)
  | .settle h => (.silent, settleHead head h s)
  | .matchRows accept => (.matches (matchPhysical accept s), s)
  | .count x => (.count (countPhysical x s), s)

def referenceStep (op : Op Head Fact) (rows : Multiset Fact) : Answer Fact × Multiset Fact :=
  match op with
  | .insert x => (.silent, x ::ₘ rows)
  | .eraseOne x => (.removed (decide (x ∈ rows)), rows.erase x)
  | .promote _ | .settle _ => (.silent, rows)
  | .matchRows accept => (.matches (rows.filter (fun x => accept x = true)), rows)
  | .count x => (.count (rows.count x), rows)

theorem step_refines (head : Fact → Head) (eligible : Fact → Bool) (op : Op Head Fact)
    (s : State Head Fact) :
    ((step head eligible op s).1, observe (step head eligible op s).2) = referenceStep op (observe s) := by
  cases op <;> simp [step, referenceStep, remove_status, matchPhysical_refines, countPhysical_refines]

theorem step_valid (head : Fact → Head) (eligible : Fact → Bool) (op : Op Head Fact)
    (s : State Head Fact) (valid : Valid head eligible s) : Valid head eligible (step head eligible op s).2 := by
  cases op with
  | insert x => exact valid_add head eligible x s valid
  | eraseOne x => exact valid_remove head eligible x s valid
  | promote h => exact valid_promote head eligible h s valid
  | settle h => exact valid_settleHead head eligible h s valid
  | matchRows _ | count _ => exact valid

def run (head : Fact → Head) (eligible : Fact → Bool) :
    List (Op Head Fact) → State Head Fact → List (Answer Fact) × State Head Fact
  | [], s => ([], s)
  | op :: ops, s =>
    let first := step head eligible op s
    let rest := run head eligible ops first.2
    (first.1 :: rest.1, rest.2)

def referenceRun : List (Op Head Fact) → Multiset Fact → List (Answer Fact) × Multiset Fact
  | [], rows => ([], rows)
  | op :: ops, rows =>
    let first := referenceStep op rows
    let rest := referenceRun ops first.2
    (first.1 :: rest.1, rest.2)

/-- The complete query/status trace and final bag agree for every operation interleaving. -/
theorem run_refines (head : Fact → Head) (eligible : Fact → Bool) (ops : List (Op Head Fact))
    (s : State Head Fact) :
    ((run head eligible ops s).1, observe (run head eligible ops s).2) = referenceRun ops (observe s) := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    have hs := step_refines head eligible op s
    have hr := ih (step head eligible op s).2
    have hsa := congrArg Prod.fst hs
    have hss := congrArg Prod.snd hs
    have hra := congrArg Prod.fst hr
    have hrs := congrArg Prod.snd hr
    dsimp only at hsa hss hra hrs
    simp only [run, referenceRun]
    rw [hsa, hra, hrs, hss]

theorem run_valid (head : Fact → Head) (eligible : Fact → Bool) (ops : List (Op Head Fact))
    (s : State Head Fact) (valid : Valid head eligible s) : Valid head eligible (run head eligible ops s).2 := by
  induction ops generalizing s with
  | nil => exact valid
  | cons op ops ih => exact ih _ (step_valid head eligible op s valid)

example :
    let old : State Unit Nat := fromRows {7}
    let enabled := promote () old
    let updated := add (fun _ => ()) (fun _ => true) 7 enabled
    enabled.data.rows = {7} ∧ updated.data.compact = {7} ∧ (observe updated).count 7 = 2 := by decide

/-- Adding an inadmissible fact never installs it in the compact component. -/
example : (add (fun _ : Nat => ()) (fun _ => false) 7
    (promote () (fromRows 0))).data.compact = ∅ := by decide

example :
    (run (fun _ : Nat => ()) (fun _ => true)
      [.insert 7, .promote (), .insert 7, .count 7, .matchRows (fun n => n == 7),
        .settle (), .eraseOne 7, .count 7] (fromRows 0)).1 =
      [.silent, .silent, .silent, .count 2, .matches {7, 7}, .silent, .removed true, .count 1] := by decide

/-- Copying old rows into the table while retaining those rows would duplicate facts. -/
example : observe (⟨fun _ : Unit => true, ⟨{7}, {7}⟩⟩ : State Unit Nat) ≠
    observe (promote () (fromRows ({7} : Multiset Nat))) := by decide

#print axioms run_refines
#print axioms run_valid
#print axioms observe_settleHead

end Mettapedia.Machines.ShapeHeadRouting
