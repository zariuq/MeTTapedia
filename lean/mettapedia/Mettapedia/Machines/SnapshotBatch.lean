import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-!
# Snapshot reads and privately owned batch updates

A kernel reads one immutable shared snapshot and one privately owned value.
Its input seed is attached to the logical item, not to a worker or a schedule.
The sequential implementation updates the live indexed store item by item.
The batch implementation instead computes all writes from the initial store,
then publishes those writes. Distinct destination identifiers make these two
implementations equal, including when the items are partitioned or reordered.

This module establishes semantic permission. It does not assume a scheduler,
assign resource budgets, or claim a physical speedup. The shared snapshot may
contain arbitrary read-only graph, program, or environment data. A private
value may itself be a structured continuation or a private write buffer.
-/

namespace Mettapedia.Machines.SnapshotBatch

universe uSnapshot uItem uSeed uId uValue

/-- A private update may read the whole immutable snapshot, but it receives
only its own writable value. Seeds are explicit inputs to the pure kernel. -/
structure Kernel (Snapshot : Type uSnapshot) (Item : Type uItem)
    (Seed : Type uSeed) (Id : Type uId) (Value : Type uValue) where
  destination : Item → Id
  compute : Snapshot → Item → Seed → Value → Value

variable {Snapshot : Type uSnapshot} {Item : Type uItem}
  {Seed : Type uSeed} {Id : Type uId} {Value : Type uValue}
  [DecidableEq Id]

namespace Kernel

variable (kernel : Kernel Snapshot Item Seed Id Value)
  (snapshot : Snapshot) (seeds : Item → Seed)

/-- Sequential execution reads the current value of the owned destination. -/
def step (state : Id → Value) (item : Item) : Id → Value :=
  Function.update state (kernel.destination item)
    (kernel.compute snapshot item (seeds item) (state (kernel.destination item)))

/-- The reference evaluator threads an indexed store through every item. -/
def run (state : Id → Value) (items : List Item) : Id → Value :=
  items.foldl (kernel.step snapshot seeds) state

/-- Independent workers compute private writes from one fixed initial store. -/
def prepare (initial : Id → Value) (items : List Item) : List (Id × Value) :=
  items.map fun item =>
    (kernel.destination item,
      kernel.compute snapshot item (seeds item) (initial (kernel.destination item)))

/-- Publication applies already computed writes; it never reruns a kernel. -/
def publish (state : Id → Value) (writes : List (Id × Value)) : Id → Value :=
  writes.foldl (fun current write => Function.update current write.1 write.2) state

/-- Compute independently, then publish. -/
def batch (initial : Id → Value) (items : List Item) : Id → Value :=
  publish initial (kernel.prepare snapshot seeds initial items)

/-- Destination uniqueness preserves each private initial value until its
owner runs. Equal item values at two positions therefore need distinct owned
identifiers if the two occurrences are to run independently. -/
def Disjoint (items : List Item) : Prop :=
  (items.map kernel.destination).Nodup

instance decidableDisjoint (items : List Item) : Decidable (kernel.Disjoint items) :=
  inferInstanceAs (Decidable ((items.map kernel.destination).Nodup))

@[simp] theorem run_nil (state : Id → Value) :
    kernel.run snapshot seeds state [] = state := rfl

@[simp] theorem run_cons (state : Id → Value) (item : Item) (items : List Item) :
    kernel.run snapshot seeds state (item :: items) =
      kernel.run snapshot seeds (kernel.step snapshot seeds state item) items := rfl

omit [DecidableEq Id] in
@[simp] theorem prepare_nil (state : Id → Value) :
    kernel.prepare snapshot seeds state [] = [] := rfl

omit [DecidableEq Id] in
@[simp] theorem prepare_cons (state : Id → Value) (item : Item) (items : List Item) :
    kernel.prepare snapshot seeds state (item :: items) =
      (kernel.destination item,
        kernel.compute snapshot item (seeds item) (state (kernel.destination item))) ::
      kernel.prepare snapshot seeds state items := rfl

@[simp] theorem publish_nil (state : Id → Value) : publish state [] = state := rfl

@[simp] theorem publish_cons (state : Id → Value) (write : Id × Value)
    (writes : List (Id × Value)) :
    publish state (write :: writes) =
      publish (Function.update state write.1 write.2) writes := rfl

/-- A remaining suffix resumes from the actual store without replaying the
prefix. Its snapshot and logical seed assignment stay fixed. -/
theorem run_append (state : Id → Value) (left right : List Item) :
    kernel.run snapshot seeds state (left ++ right) =
      kernel.run snapshot seeds (kernel.run snapshot seeds state left) right := by
  simp [run, List.foldl_append]

/-- The key locality law: two distinct owners commute at the full store,
not merely after taking a quotient of the answers. -/
theorem step_commute (state : Id → Value) (left right : Item)
    (distinct : kernel.destination left ≠ kernel.destination right) :
    kernel.step snapshot seeds (kernel.step snapshot seeds state left) right =
      kernel.step snapshot seeds (kernel.step snapshot seeds state right) left := by
  simp only [step, Function.update_of_ne distinct,
    Function.update_of_ne distinct.symm]
  exact Function.update_comm distinct _ _ _

/-- Locations outside the destination support are an unchanged frame. -/
theorem run_preserves_outside (state : Id → Value) (items : List Item) (location : Id)
    (outside : location ∉ items.map kernel.destination) :
    kernel.run snapshot seeds state items location = state location := by
  induction items generalizing state with
  | nil => rfl
  | cons item rest ih =>
    have absent : location ≠ kernel.destination item ∧
        location ∉ rest.map kernel.destination := by
      simpa only [List.map_cons, List.mem_cons, not_or] using outside
    rw [run_cons, ih (kernel.step snapshot seeds state item) absent.2]
    exact Function.update_of_ne absent.1 _ _

/-- The final value at an owned location is exactly that owner's independent
computation from the initial store. Together with `run_preserves_outside`, this
is a pointwise characterization of the whole batch result. -/
theorem run_at_owned (state : Id → Value) (items : List Item)
    (disjoint : kernel.Disjoint items) (item : Item) (member : item ∈ items) :
    kernel.run snapshot seeds state items (kernel.destination item) =
      kernel.compute snapshot item (seeds item) (state (kernel.destination item)) := by
  induction items generalizing state with
  | nil => simp at member
  | cons first rest ih =>
    have split := List.nodup_cons.mp disjoint
    rcases List.mem_cons.mp member with equal | inRest
    · subst item
      rw [run_cons, run_preserves_outside _ _ _ _ _ _ split.1]
      simp [step]
    · have different : kernel.destination item ≠ kernel.destination first := by
        intro equal
        exact split.1 (equal ▸ List.mem_map.mpr ⟨item, inRest, rfl⟩)
      rw [run_cons, ih (kernel.step snapshot seeds state first) split.2 inRest]
      simp only [step, Function.update_of_ne different]

/-- A generalized induction invariant allows the publication store to contain
earlier writes while every remaining owner's input still agrees with the
shared preparation snapshot. -/
theorem run_eq_publish_of_agree (initial state : Id → Value) (items : List Item)
    (disjoint : kernel.Disjoint items)
    (agree : ∀ item ∈ items, state (kernel.destination item) =
      initial (kernel.destination item)) :
    kernel.run snapshot seeds state items =
      publish state (kernel.prepare snapshot seeds initial items) := by
  induction items generalizing state with
  | nil => rfl
  | cons item rest ih =>
    have split := List.nodup_cons.mp disjoint
    have headAgree := agree item (by simp)
    have tailAgree : ∀ other ∈ rest,
        (kernel.step snapshot seeds state item) (kernel.destination other) =
          initial (kernel.destination other) := by
      intro other member
      have distinct : kernel.destination other ≠ kernel.destination item := by
        intro equal
        exact split.1 (equal ▸ List.mem_map.mpr ⟨other, member, rfl⟩)
      simpa [step, Function.update_of_ne distinct] using
        agree other (List.mem_cons_of_mem item member)
    rw [run_cons, prepare_cons, publish_cons]
    rw [ih (kernel.step snapshot seeds state item) split.2 tailAgree]
    simp only [step, headAgree]

/-- Independent private writes realize the sequential reference exactly. -/
theorem batch_eq_run (initial : Id → Value) (items : List Item)
    (disjoint : kernel.Disjoint items) :
    kernel.batch snapshot seeds initial items =
      kernel.run snapshot seeds initial items := by
  exact (kernel.run_eq_publish_of_agree snapshot seeds initial initial items
    disjoint (by intros; rfl)).symm

/-- Permuting a disjoint batch preserves the complete resulting store. -/
theorem run_perm (initial : Id → Value) {left right : List Item}
    (permutation : left.Perm right) (disjoint : kernel.Disjoint left) :
    kernel.run snapshot seeds initial left =
      kernel.run snapshot seeds initial right := by
  apply permutation.foldl_eq'
  intro first firstMem second secondMem state
  by_cases equal : first = second
  · subst second; rfl
  · exact kernel.step_commute snapshot seeds state first second (by
      intro destinationsEqual
      exact equal ((List.inj_on_of_nodup_map disjoint) firstMem
        secondMem destinationsEqual))

/-- The prepared writes can be generated separately by any partition of the
logical items. Every worker uses the same initial store and logical seeds. -/
def partitioned (initial : Id → Value) (parts : List (List Item)) : Id → Value :=
  publish initial ((parts.map (kernel.prepare snapshot seeds initial)).flatten)

omit [DecidableEq Id] in
theorem prepare_flatten (initial : Id → Value) (parts : List (List Item)) :
    kernel.prepare snapshot seeds initial parts.flatten =
      (parts.map (kernel.prepare snapshot seeds initial)).flatten := by
  unfold prepare
  simp [List.map_flatten]

/-- Chunking changes worker placement without changing private writes. -/
theorem partitioned_eq_batch (initial : Id → Value) (parts : List (List Item)) :
    kernel.partitioned snapshot seeds initial parts =
      kernel.batch snapshot seeds initial parts.flatten := by
  simp only [partitioned, batch, prepare_flatten]

/-- Any exact partition/permutation realizes the original reference program.
The permutation retains occurrence multiplicity, while destination uniqueness
prevents two occurrences from silently sharing one writable location. -/
theorem partitioned_eq_run (initial : Id → Value) (parts : List (List Item))
    (items : List Item) (coverage : parts.flatten.Perm items)
    (disjoint : kernel.Disjoint items) :
    kernel.partitioned snapshot seeds initial parts =
      kernel.run snapshot seeds initial items := by
  have partitionDisjoint : kernel.Disjoint parts.flatten :=
    (coverage.map kernel.destination).nodup_iff.mpr disjoint
  rw [partitioned_eq_batch,
    kernel.batch_eq_run snapshot seeds initial parts.flatten partitionDisjoint]
  exact kernel.run_perm snapshot seeds initial coverage partitionDisjoint

end Kernel

namespace Controls

/-- Logical seeds may carry previously sampled randomness or explicit input
data. They remain attached to item identifiers when workers are exchanged. -/
def privateKernel : Kernel Nat (Fin 3) Nat (Fin 3) Nat where
  destination := id
  compute snapshot _item seed value := snapshot + seed + value

theorem three_workers_same_result :
    privateKernel.partitioned 10 (fun item => item.val + 1) (fun _ => 0)
      [[2], [0], [1]] =
    privateKernel.run 10 (fun item => item.val + 1) (fun _ => 0) [0, 1, 2] := by
  apply Kernel.partitioned_eq_run
  · decide
  · decide

theorem three_workers_values :
    privateKernel.partitioned 10 (fun item => item.val + 1) (fun _ => 0)
      [[2], [0], [1]] = ![11, 12, 13] := by
  funext item
  fin_cases item <;> decide

/-- Two distinct logical items alias one destination. Their updates do not
commute, and computing both from the initial value changes the result. -/
def aliasedKernel : Kernel Unit Bool Unit Unit Nat where
  destination _ := ()
  compute _ item _ value := if item then value + 1 else value * 2

theorem aliases_reject_independent_batch :
    ¬ aliasedKernel.Disjoint [true, false] ∧
    aliasedKernel.run () (fun _ => ()) (fun _ => 1) [true, false] () = 4 ∧
    aliasedKernel.run () (fun _ => ()) (fun _ => 1) [false, true] () = 3 ∧
    aliasedKernel.batch () (fun _ => ()) (fun _ => 1) [true, false] () = 2 := by
  decide

/-- A live read of the other destination violates the immutable-snapshot
boundary, even though the two write destinations are distinct. -/
def feedbackStep (state : Bool → Nat) (item : Bool) : Bool → Nat :=
  Function.update state item (state (!item) + 1)

theorem live_feedback_not_commuting :
    feedbackStep (feedbackStep (fun _ => 0) false) true ≠
      feedbackStep (feedbackStep (fun _ => 0) true) false := by
  intro equal
  have atFalse := congrFun equal false
  norm_num [feedbackStep] at atFalse

/-- Assigning fresh seeds by worker position would change even this fully
private computation. The theorem above deliberately fixes logical seeds. -/
theorem changed_seed_assignment_changes_result :
    privateKernel.run 10 (fun item => item.val + 1) (fun _ => 0) [0, 1, 2] ≠
      privateKernel.run 10 (fun item => 3 - item.val) (fun _ => 0) [0, 1, 2] := by
  intro equal
  have atZero := congrFun equal (0 : Fin 3)
  exact (by decide :
    privateKernel.run 10 (fun item => item.val + 1) (fun _ => 0) [0, 1, 2] 0 ≠
      privateKernel.run 10 (fun item => 3 - item.val) (fun _ => 0) [0, 1, 2] 0) atZero

end Controls

end Mettapedia.Machines.SnapshotBatch
