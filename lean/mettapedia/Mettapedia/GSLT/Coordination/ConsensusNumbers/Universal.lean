import Mettapedia.GSLT.Coordination.ConsensusNumbers.Linearizability

/-!
# Herlihy's universal construction

From consensus objects and registers, every object given by a sequential specification has a
wait-free, linearizable implementation for any number `n` of processes (Herlihy, *Wait-free
synchronization*, 1991, §4).

## The log

The processes agree on a **log**: a sequence of places `0, 1, 2, …`, each holding one operation of
one process (an `Entry`: whose operation, and which). Place `k` is decided by its own consensus
**slot**: the first proposal made to it stays, and anyone can learn it afterwards. The target's
state after the first `k` places is obtained by applying their operations in order, so every
process that has read the first `k` places knows it (`Seen`, `logSeen`).

Example (a counter, two processes): if the log reads `(0, inc), (1, inc), (0, get)`, process `0`'s
`get` sits at place `2` and answers `2`.

## Helping

Each process has, for each of its operations in turn, an **announcement**: the operation and its
number among that process's operations (its *tag*). To perform an operation, process `i`:

1. announces it (`announce`);
2. for each place `k` from where it stopped reading, reads the announcement of process `k mod n`
   with the tag that process's next operation will have (`read`); if there is one, it proposes that
   operation for place `k`, otherwise its own (`claim`); then it learns what place `k` holds
   (`learn`);
3. when it learns its own operation, it returns the answer the operation has at its place
   (`done`).

The helping rule is what makes the construction wait-free: once `i` has announced, consider the
first place `k ≡ i (mod n)` beyond every place decided at that time. Everyone who proposes for
place `k` read `i`'s announcement after it was made, so either `i`'s operation was placed earlier
or it is placed at `k`. Without helping, a process could lose every place forever.

## What the base must offer

`Board X n Op` says how the base object `X` provides the slots and the announcements, through views
of its state (`slot`, `ann`) and laws about the operations `claim`, `learn`, `write` and `read`.
Announcements are viewed by tag; writing the announcement with tag `t` leaves the view of older tags
unspecified, so both a register that is overwritten and a space that only grows fit.

## The proofs

* **Linearizable** (`universal_linearizable`): each configuration is related to one of the target
  used atomically: the target's state is the state after the decided places; an operation takes
  effect when its entry is placed, possibly by another process's claim. The invariant (`Inv`) says
  that decided places form an initial segment, each process's knowledge is the log read up to its
  position, announcements are as described, a process's entries are where they should be, a
  proposal for the first undecided place is an operation still in progress, and each announced
  operation not yet placed has a **safe** place ahead (`Safe`): one that every proposer will give it.
* **Wait-free** (`universal_waitFree`): a busy process that keeps moving advances one place every
  three moves and never passes its safe place without its operation being placed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.ConsensusNumbers

namespace Universal

/-! ## The log -/

/-- A place of the log: whose operation it is, and the operation. -/
abbrev Entry (n : ℕ) (Op : Type) := Fin n × Op

variable {n : ℕ} {Y : DetObject}

/-- What a process has read of the log: how many places, the target's state after them, and how
many operations of each process they hold. -/
structure Seen (n : ℕ) (Y : DetObject) where
  pos : ℕ
  state : Y.State
  count : Fin n → ℕ

/-- Read one more place, holding `e`. -/
def Seen.add (K : Seen n Y) (e : Entry n Y.Op) : Seen n Y :=
  ⟨K.pos + 1, (Y.apply K.state e.2).1, Function.update K.count e.1 (K.count e.1 + 1)⟩

/-- Pass a place that holds nothing (never used for decided places). -/
def Seen.skip (K : Seen n Y) : Seen n Y := ⟨K.pos + 1, K.state, K.count⟩

/-- Nothing read yet. -/
def Seen.start (s₀ : Y.State) : Seen n Y := ⟨0, s₀, fun _ => 0⟩

/-- The log `L` read up to place `k`, from the target's state `s₀`. -/
def logSeen (s₀ : Y.State) (L : ℕ → Option (Entry n Y.Op)) : ℕ → Seen n Y
  | 0 => Seen.start s₀
  | k + 1 => match L k with
    | some e => (logSeen s₀ L k).add e
    | none => (logSeen s₀ L k).skip

section Log

variable {s₀ : Y.State} {L L' : ℕ → Option (Entry n Y.Op)}

@[simp] theorem logSeen_zero : logSeen s₀ L 0 = Seen.start s₀ := rfl

theorem logSeen_succ_some {k : ℕ} {e : Entry n Y.Op} (h : L k = some e) :
    logSeen s₀ L (k + 1) = (logSeen s₀ L k).add e := by
  simp [logSeen, h]

theorem logSeen_succ_none {k : ℕ} (h : L k = none) :
    logSeen s₀ L (k + 1) = (logSeen s₀ L k).skip := by
  simp [logSeen, h]

@[simp] theorem logSeen_pos (k : ℕ) : (logSeen s₀ L k).pos = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      cases h : L k with
      | none => rw [logSeen_succ_none h]; simp [Seen.skip, ih]
      | some e => rw [logSeen_succ_some h]; simp [Seen.add, ih]

/-- The log read up to `k` depends only on the places before `k`. -/
theorem logSeen_congr {k : ℕ} (agree : ∀ i, i < k → L i = L' i) :
    logSeen s₀ L k = logSeen s₀ L' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have below : ∀ i, i < k → L i = L' i := fun i hi => agree i (by omega)
      have here := agree k (by omega)
      cases h : L k with
      | none =>
          rw [logSeen_succ_none h, logSeen_succ_none (here ▸ h), ih below]
      | some e =>
          rw [logSeen_succ_some h, logSeen_succ_some (here ▸ h), ih below]

theorem count_add_self (K : Seen n Y) (e : Entry n Y.Op) : (K.add e).count e.1 = K.count e.1 + 1 := by
  simp [Seen.add]

theorem count_add_other (K : Seen n Y) {e : Entry n Y.Op} {j : Fin n} (h : e.1 ≠ j) :
    (K.add e).count j = K.count j := by
  simp [Seen.add, Function.update_of_ne (Ne.symm h)]

theorem count_succ_owned {k : ℕ} {e : Entry n Y.Op} (h : L k = some e) :
    (logSeen s₀ L (k + 1)).count e.1 = (logSeen s₀ L k).count e.1 + 1 := by
  rw [logSeen_succ_some h, count_add_self]

theorem count_succ_not_owned {k : ℕ} {j : Fin n} (h : ∀ e, L k = some e → e.1 ≠ j) :
    (logSeen s₀ L (k + 1)).count j = (logSeen s₀ L k).count j := by
  cases hk : L k with
  | none => rw [logSeen_succ_none hk]; rfl
  | some e => rw [logSeen_succ_some hk, count_add_other _ (h e hk)]

theorem count_succ_le (k : ℕ) (j : Fin n) :
    (logSeen s₀ L (k + 1)).count j ≤ (logSeen s₀ L k).count j + 1 := by
  cases hk : L k with
  | none => rw [logSeen_succ_none hk]; simp [Seen.skip]
  | some e =>
      by_cases owner : e.1 = j
      · subst owner; rw [count_succ_owned hk]
      · rw [count_succ_not_owned (j := j) (fun e' he' => by rw [hk] at he'; cases he'; exact owner)]
        omega

theorem count_mono {a b : ℕ} (le : a ≤ b) (j : Fin n) :
    (logSeen s₀ L a).count j ≤ (logSeen s₀ L b).count j := by
  induction b with
  | zero => obtain rfl : a = 0 := by omega
            exact le_rfl
  | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with lt | ge
      · refine (ih (by omega)).trans ?_
        cases hk : L b with
        | none => rw [logSeen_succ_none hk]; simp [Seen.skip]
        | some e =>
            by_cases owner : e.1 = j
            · subst owner; rw [count_succ_owned hk]; omega
            · rw [count_succ_not_owned (j := j) (fun e' he' => by
                rw [hk] at he'; cases he'; exact owner)]
      · obtain rfl : a = b + 1 := by omega
        exact le_rfl

/-- An entry of `j` between `a` and `b` raises `j`'s count. -/
theorem count_lt_of_owned {a b s : ℕ} {e : Entry n Y.Op} (as : a ≤ s) (sb : s < b)
    (h : L s = some e) : (logSeen s₀ L a).count e.1 + 1 ≤ (logSeen s₀ L b).count e.1 := by
  have one := count_mono (s₀ := s₀) (L := L) as e.1
  have two := count_succ_owned (s₀ := s₀) h
  have three := count_mono (s₀ := s₀) (L := L) (show s + 1 ≤ b by omega) e.1
  omega

/-- Two entries of `j` between `a` and `b` raise `j`'s count by two. -/
theorem count_lt_of_two_owned {a b s s' : ℕ} {e e' : Entry n Y.Op} (as : a ≤ s) (ss : s < s')
    (sb : s' < b) (h : L s = some e) (h' : L s' = some e') (same : e'.1 = e.1) :
    (logSeen s₀ L a).count e.1 + 2 ≤ (logSeen s₀ L b).count e.1 := by
  have one := count_lt_of_owned (s₀ := s₀) as ss h
  have two := count_lt_of_owned (s₀ := s₀) (show s' ≤ s' from le_rfl) sb h'
  rw [same] at two
  have three := count_mono (s₀ := s₀) (L := L) (show s + 1 ≤ s' by omega) e.1
  have four := count_mono (s₀ := s₀) (L := L) (show s' ≤ s' from le_rfl) e.1
  omega

/-- If `j`'s count did not grow between `a` and `b`, no place between them holds an entry of `j`. -/
theorem not_owned_of_count_eq {a b s : ℕ} {j : Fin n} (eq : (logSeen s₀ L b).count j =
    (logSeen s₀ L a).count j) (as : a ≤ s) (sb : s < b) {e : Entry n Y.Op} (h : L s = some e) :
    e.1 ≠ j := by
  rintro rfl
  have := count_lt_of_owned (s₀ := s₀) as sb h
  omega

/-- If no place between `a` and `b` holds an entry of `j`, its count did not grow. -/
theorem count_eq_of_not_owned {a b : ℕ} {j : Fin n} (ab : a ≤ b)
    (none : ∀ s e, a ≤ s → s < b → L s = some e → e.1 ≠ j) :
    (logSeen s₀ L b).count j = (logSeen s₀ L a).count j := by
  induction b with
  | zero => obtain rfl : a = 0 := by omega
            rfl
  | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with lt | ge
      · rw [count_succ_not_owned (fun e he => none b e (by omega) (by omega) he),
          ih (by omega) (fun s e h1 h2 h3 => none s e h1 (by omega) h3)]
      · obtain rfl : a = b + 1 := by omega
        rfl

end Log

/-! ## What the base must offer -/

/-- The base object `X` offers consensus slots for the places of the log and announcements for the
processes, seen through the views `slot` and `ann`. -/
structure Board (X : DetObject) (n : ℕ) (Op : Type) where
  /-- What place `k` holds, if it is decided. -/
  slot : X.State → ℕ → Option (Entry n Op)
  /-- The operation process `i` announced with tag `t`, if any. -/
  ann : X.State → Fin n → ℕ → Option Op
  /-- The initial state: nothing decided, nothing announced. -/
  init : X.State
  /-- Propose an entry for a place. -/
  claim : ℕ → Entry n Op → X.Op
  /-- Learn what a place holds; the entry is a default for reading the answer. -/
  learn : ℕ → Entry n Op → X.Op
  /-- What place `k` holds, read from the answer of `learn`. -/
  learned : ℕ → X.Res → Entry n Op → Entry n Op
  /-- Announce an operation with a tag. -/
  write : Fin n → ℕ → Op → X.Op
  /-- Read a process's announcement with a tag. -/
  read : Fin n → ℕ → X.Op
  /-- Process `i`'s announcement with tag `t`, read from the answer of `read`. -/
  readOut : Fin n → ℕ → X.Res → Option Op
  init_slot : ∀ k, slot init k = none
  init_ann : ∀ i t, ann init i t = none
  /-- A claim decides an undecided place, and changes nothing else. -/
  claim_slot : ∀ s k e, slot (X.apply s (claim k e)).1 =
    Function.update (slot s) k (some ((slot s k).getD e))
  claim_ann : ∀ s k e, ann (X.apply s (claim k e)).1 = ann s
  /-- Learning a decided place changes nothing and tells what it holds. -/
  learn_slot : ∀ s k e w, slot s k = some w → slot (X.apply s (learn k e)).1 = slot s
  learn_ann : ∀ s k e w, slot s k = some w → ann (X.apply s (learn k e)).1 = ann s
  learn_out : ∀ s k e w, slot s k = some w → learned k (X.apply s (learn k e)).2 e = w
  /-- Announcing with a tag above all present makes it the announcement with that tag. -/
  write_slot : ∀ s i t op, slot (X.apply s (write i t op)).1 = slot s
  write_self : ∀ s i t op, (∀ t', t ≤ t' → ann s i t' = none) →
    ann (X.apply s (write i t op)).1 i t = some op
  write_above : ∀ s i t op, (∀ t', t ≤ t' → ann s i t' = none) →
    ∀ t', t < t' → ann (X.apply s (write i t op)).1 i t' = none
  write_other : ∀ s i t op j, j ≠ i → ann (X.apply s (write i t op)).1 j = ann s j
  /-- Reading changes nothing and tells the announcement. -/
  read_slot : ∀ s i t, slot (X.apply s (read i t)).1 = slot s
  read_ann : ∀ s i t, ann (X.apply s (read i t)).1 = ann s
  read_out : ∀ s i t, readOut i t (X.apply s (read i t)).2 = ann s i t

/-! ## The construction -/

/-- Where a process is within an operation. -/
inductive Stage (n : ℕ) (Y : DetObject) where
  /-- About to announce `op`. -/
  | announce (op : Y.Op) (K : Seen n Y)
  /-- About to read the announcement for place `K.pos`. -/
  | read (op : Y.Op) (K : Seen n Y)
  /-- About to propose `p` for place `K.pos`. -/
  | claim (op : Y.Op) (K : Seen n Y) (p : Entry n Y.Op)
  /-- About to learn what place `K.pos` holds. -/
  | learn (op : Y.Op) (K : Seen n Y) (p : Entry n Y.Op)
  /-- About to return `r`. -/
  | done (r : Y.Res) (K : Seen n Y)

/-- The process whose announcement is read for place `k`: `k mod n`. (`i` only witnesses that
there are processes.) -/
def helpee (i : Fin n) (k : ℕ) : Fin n := ⟨k % n, Nat.mod_lt k i.pos⟩

theorem helpee_val (i : Fin n) (k : ℕ) : (helpee i k).val = k % n := rfl

/-- The proposal for place `K.pos`: the announced operation read, if any, else one's own. -/
def propose (i : Fin n) (op : Y.Op) (K : Seen n Y) : Option Y.Op → Entry n Y.Op
  | some op' => (helpee i K.pos, op')
  | none => (i, op)

/-- After learning that the place holds `e`: return if it is one's own operation, else go on. -/
def afterLearn (i : Fin n) (op : Y.Op) (K : Seen n Y) (e : Entry n Y.Op) : Stage n Y :=
  if e.1 = i then .done (Y.apply K.state e.2).2 (K.add e) else .read op (K.add e)

variable {X : DetObject}

/-- **The universal construction** over a board, for the target `Y` started at `s₀`. -/
def universal (B : Board X n Y.Op) (s₀ : Y.State) : Implementation X.toObject Y n where
  init := B.init
  Mem := Seen n Y
  Work := Stage n Y
  mem₀ _ := Seen.start s₀
  begin _ K op := .announce op K
  move i w := match w with
    | .announce op K => .call (B.write i (K.count i) op)
    | .read _ K => .call (B.read (helpee i K.pos) (K.count (helpee i K.pos)))
    | .claim _ K p => .call (B.claim K.pos p)
    | .learn _ K p => .call (B.learn K.pos p)
    | .done r K => .ret r K
  next i w ans := match w with
    | .announce op K => .read op K
    | .read op K => .claim op K
        (propose i op K (B.readOut (helpee i K.pos) (K.count (helpee i K.pos)) ans))
    | .claim op K p => .learn op K p
    | .learn op K p => afterLearn i op K (B.learned K.pos ans p)
    | .done r K => .done r K

/-! ## The invariant, on abstract configurations -/

/-- A process's status, without reference to the board. -/
inductive UStatus (n : ℕ) (Y : DetObject) where
  | idle (K : Seen n Y)
  | busy (w : Stage n Y)

/-- What a process has seen, whatever it is doing. -/
def seenOf : UStatus n Y → Seen n Y
  | .idle K => K
  | .busy (.announce _ K) => K
  | .busy (.read _ K) => K
  | .busy (.claim _ K _) => K
  | .busy (.learn _ K _) => K
  | .busy (.done _ K) => K

/-- The operation a process has announced and not yet learned the place of, with its knowledge. -/
def announcedOf : UStatus n Y → Option (Y.Op × Seen n Y)
  | .busy (.read op K) => some (op, K)
  | .busy (.claim op K _) => some (op, K)
  | .busy (.learn op K _) => some (op, K)
  | _ => none

/-- A proposal about to be made, with the proposer's knowledge. -/
def claimOf : UStatus n Y → Option (Seen n Y × Entry n Y.Op)
  | .busy (.claim _ K p) => some (K, p)
  | _ => none

section Inv

variable (s₀ : Y.State)

/-- `j`'s count of entries in the log up to `D`. -/
abbrev logCount (L : ℕ → Option (Entry n Y.Op)) (D : ℕ) (j : Fin n) : ℕ :=
  (logSeen s₀ L D).count j

/-- An entry is **pending**: its owner has announced it and it is not yet in the log. -/
def Pending (L : ℕ → Option (Entry n Y.Op)) (D : ℕ) (loc : Fin n → UStatus n Y)
    (p : Entry n Y.Op) : Prop :=
  ∃ K, announcedOf (loc p.1) = some (p.2, K) ∧ logCount s₀ L D p.1 = K.count p.1

/-- Place `k` is **safe** for `j`'s operation `op`: it is `j`'s turn to be helped there, it is not
decided, and everyone about to propose for it proposes `op`. -/
def Safe (D : ℕ) (loc : Fin n → UStatus n Y) (j : Fin n) (op : Y.Op) (k : ℕ) : Prop :=
  k % n = j.val ∧ D ≤ k ∧ ∀ q K p, claimOf (loc q) = some (K, p) → K.pos = k → p = (j, op)

/-- **The invariant** of the universal construction, with `D` places decided. -/
structure Inv (L : ℕ → Option (Entry n Y.Op)) (An : Fin n → ℕ → Option Y.Op) (D : ℕ)
    (loc : Fin n → UStatus n Y) : Prop where
  /-- The decided places are `0, …, D - 1`. -/
  decided : ∀ k, (L k).isSome ↔ k < D
  /-- Each process knows the log up to its position, which is at most `D`. -/
  seen : ∀ j, seenOf (loc j) = logSeen s₀ L (seenOf (loc j)).pos
  seenLe : ∀ j, (seenOf (loc j)).pos ≤ D
  /-- A process about to learn a place has seen it decided. -/
  learnLt : ∀ j op K p, loc j = .busy (.learn op K p) → K.pos < D
  /-- A process with nothing announced has all its entries behind it and no announcement ahead. -/
  quiet : ∀ j, announcedOf (loc j) = none →
    logCount s₀ L D j = (seenOf (loc j)).count j ∧
      ∀ t, (seenOf (loc j)).count j ≤ t → An j t = none
  /-- A process that announced `op` with tag `K.count j` has at most that entry ahead of it. -/
  loud : ∀ j op K, announcedOf (loc j) = some (op, K) →
    An j (K.count j) = some op ∧ (∀ t, K.count j < t → An j t = none) ∧
      logCount s₀ L D j ≤ K.count j + 1 ∧
      ∀ s e, K.pos ≤ s → s < D → L s = some e → e.1 = j → e.2 = op
  /-- A proposal for the first undecided place is pending. -/
  proposal : ∀ j K p, claimOf (loc j) = some (K, p) → K.pos = D → Pending s₀ L D loc p
  /-- An announced operation not yet placed has a safe place. -/
  helped : ∀ j op K, announcedOf (loc j) = some (op, K) → logCount s₀ L D j = K.count j →
    ∃ k, Safe D loc j op k

end Inv

/-! ## The invariant is kept -/

section Keep

variable {s₀ : Y.State} {L : ℕ → Option (Entry n Y.Op)} {An : Fin n → ℕ → Option Y.Op} {D : ℕ}
  {loc : Fin n → UStatus n Y}

theorem update_apply_eq {α : Type} (f : Fin n → α) (j : Fin n) (a : α) (q : Fin n) :
    Function.update f j a q = if q = j then a else f q := by
  by_cases h : q = j
  · subst h; simp
  · simp [h]

/-- Some place beyond `D` is `j`'s turn to be helped. -/
theorem exists_turn (j : Fin n) (D : ℕ) : ∃ k, D < k ∧ k % n = j.val := by
  refine ⟨n * (D + 1) + j.val, ?_, ?_⟩
  · have : 1 ≤ n := j.pos
    nlinarith
  · rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt j.isLt

theorem Inv.count_seen (inv : Inv s₀ L An D loc) (q : Fin n) :
    (seenOf (loc q)).count q = logCount s₀ L (seenOf (loc q)).pos q := by
  conv_lhs => rw [inv.seen q]

/-- An announced operation is either not placed, or placed at one place ahead of its owner. -/
theorem Inv.count_ge (inv : Inv s₀ L An D loc) {q : Fin n} {op : Y.Op} {K : Seen n Y}
    (h : announcedOf (loc q) = some (op, K)) : K.count q ≤ logCount s₀ L D q := by
  have seenK : seenOf (loc q) = K := by
    revert h; cases loc q with
    | idle K' => simp [announcedOf]
    | busy w => cases w <;> simp [announcedOf, seenOf]
  have := inv.count_seen q
  rw [seenK] at this
  rw [this]
  exact count_mono (by have := inv.seenLe q; rwa [seenK] at this) q

theorem seenOf_of_announced {st : UStatus n Y} {op : Y.Op} {K : Seen n Y}
    (h : announcedOf st = some (op, K)) : seenOf st = K := by
  revert h; cases st with
  | idle K' => simp [announcedOf]
  | busy w => cases w <;> simp [announcedOf, seenOf]

theorem seenOf_of_claim {st : UStatus n Y} {K : Seen n Y} {p : Entry n Y.Op}
    (h : claimOf st = some (K, p)) : seenOf st = K := by
  revert h; cases st with
  | idle K' => simp [claimOf]
  | busy w =>
      cases w <;> simp [claimOf, seenOf]
      intro h _; exact h

/-- **Calling an idle process keeps the invariant.** -/
theorem Inv.invoke (inv : Inv s₀ L An D loc) {j : Fin n} {K : Seen n Y} (op : Y.Op)
    (hj : loc j = .idle K) : Inv s₀ L An D (Function.update loc j (.busy (.announce op K))) := by
  have keep : ∀ q, seenOf (Function.update loc j (.busy (.announce op K)) q) = seenOf (loc q) := by
    intro q; by_cases h : q = j
    · subst h; simp [hj, seenOf]
    · simp [Function.update_of_ne h]
  have ann : ∀ q, announcedOf (Function.update loc j (.busy (.announce op K)) q) =
      if q = j then none else announcedOf (loc q) := by
    intro q; rw [update_apply_eq]; split_ifs <;> rfl
  have cl : ∀ q, claimOf (Function.update loc j (.busy (.announce op K)) q) =
      if q = j then none else claimOf (loc q) := by
    intro q; rw [update_apply_eq]; split_ifs <;> rfl
  refine ⟨inv.decided, fun q => by rw [keep]; exact inv.seen q,
    fun q => by rw [keep]; exact inv.seenLe q, ?_, ?_, ?_, ?_, ?_⟩
  · intro q op' K' p' h
    by_cases hq : q = j
    · subst hq; simp at h
    · rw [Function.update_of_ne hq] at h; exact inv.learnLt q op' K' p' h
  · intro q hq
    rw [keep]
    by_cases hqj : q = j
    · subst hqj; exact inv.quiet q (by rw [hj]; rfl)
    · rw [ann, if_neg hqj] at hq; exact inv.quiet q hq
  · intro q op' K' h
    rw [ann] at h
    split_ifs at h with hqj
    exact inv.loud q op' K' h
  · intro q K' p h hpos
    rw [cl] at h
    split_ifs at h with hqj
    obtain ⟨K'', h1, h2⟩ := inv.proposal q K' p h hpos
    refine ⟨K'', ?_, h2⟩
    rw [ann]
    split_ifs with hpj
    · rw [hpj, hj] at h1; cases h1
    · exact h1
  · intro q op' K' h hc
    rw [ann] at h
    split_ifs at h with hqj
    obtain ⟨k, hk, hD, hcl⟩ := inv.helped q op' K' h hc
    refine ⟨k, hk, hD, fun r K'' p'' hr hpos => ?_⟩
    rw [cl] at hr
    split_ifs at hr with hrj
    exact hcl r K'' p'' hr hpos

/-- **Announcing keeps the invariant.** -/
theorem Inv.announce (inv : Inv s₀ L An D loc) {j : Fin n} {op : Y.Op} {K : Seen n Y}
    (hj : loc j = .busy (.announce op K)) {An' : Fin n → ℕ → Option Y.Op}
    (self : An' j (K.count j) = some op) (above : ∀ t, K.count j < t → An' j t = none)
    (other : ∀ q, q ≠ j → An' q = An q) :
    Inv s₀ L An' D (Function.update loc j (.busy (.read op K))) := by
  set loc' := Function.update loc j (.busy (.read op K))
  have keep : ∀ q, seenOf (loc' q) = seenOf (loc q) := by
    intro q; by_cases h : q = j
    · subst h; simp [loc', hj, seenOf]
    · simp [loc', Function.update_of_ne h]
  have ann : ∀ q, announcedOf (loc' q) = if q = j then some (op, K) else announcedOf (loc q) := by
    intro q; simp only [loc']; rw [update_apply_eq]; split_ifs <;> rfl
  have cl : ∀ q, claimOf (loc' q) = if q = j then none else claimOf (loc q) := by
    intro q; simp only [loc']; rw [update_apply_eq]; split_ifs <;> rfl
  have quietJ := inv.quiet j (by rw [hj]; rfl)
  have seenJ : seenOf (loc j) = K := by rw [hj]; rfl
  rw [seenJ] at quietJ
  refine ⟨inv.decided, fun q => by rw [keep]; exact inv.seen q,
    fun q => by rw [keep]; exact inv.seenLe q, ?_, ?_, ?_, ?_, ?_⟩
  · intro q op' K' p' h
    by_cases hq : q = j
    · subst hq; simp [loc'] at h
    · simp only [loc', Function.update_of_ne hq] at h; exact inv.learnLt q op' K' p' h
  · intro q hq
    rw [keep]
    by_cases hqj : q = j
    · rw [ann, if_pos hqj] at hq; cases hq
    · rw [ann, if_neg hqj] at hq
      rw [other q hqj]
      exact inv.quiet q hq
  · intro q op' K' h
    rw [ann] at h
    split_ifs at h with hqj
    · subst hqj
      cases h
      refine ⟨self, above, by omega, fun s e hs hsD he hown => ?_⟩
      have seen := inv.seen q
      rw [seenJ] at seen
      have eq : logCount s₀ L D q = logCount s₀ L K.pos q := by
        rw [quietJ.1, seen]; simp
      exact absurd hown (not_owned_of_count_eq eq hs hsD he)
    · rw [other q hqj]; exact inv.loud q op' K' h
  · intro q K' p h hpos
    rw [cl] at h
    split_ifs at h with hqj
    obtain ⟨K'', h1, h2⟩ := inv.proposal q K' p h hpos
    refine ⟨K'', ?_, h2⟩
    rw [ann]
    split_ifs with hpj
    · rw [hpj, hj] at h1; cases h1
    · exact h1
  · intro q op' K' h hc
    rw [ann] at h
    split_ifs at h with hqj
    · subst hqj
      cases h
      obtain ⟨k, hk, hmod⟩ := exists_turn q D
      refine ⟨k, hmod, by omega, fun r K'' p'' hr hpos => ?_⟩
      rw [cl] at hr
      split_ifs at hr with hrj
      have := inv.seenLe r
      rw [seenOf_of_claim hr] at this
      omega
    · obtain ⟨k, hk, hD, hcl⟩ := inv.helped q op' K' h hc
      refine ⟨k, hk, hD, fun r K'' p'' hr hpos => ?_⟩
      rw [cl] at hr
      split_ifs at hr with hrj
      exact hcl r K'' p'' hr hpos

/-- What a process reading the announcement for place `K.pos` proposes. -/
def proposalOf (An : Fin n → ℕ → Option Y.Op) (j : Fin n) (op : Y.Op) (K : Seen n Y) :
    Entry n Y.Op :=
  propose j op K (An (helpee j K.pos) (K.count (helpee j K.pos)))

/-- At the first undecided place, a read finds the announcement of `h`'s pending operation, if any. -/
theorem Inv.read_finds (inv : Inv s₀ L An D loc) {K : Seen n Y} (hK : K = logSeen s₀ L D)
    (h : Fin n) {op' : Y.Op} (found : An h (K.count h) = some op') :
    ∃ Kh, announcedOf (loc h) = some (op', Kh) ∧ logCount s₀ L D h = Kh.count h := by
  have count : K.count h = logCount s₀ L D h := by rw [hK]
  cases hh : announcedOf (loc h) with
  | none =>
      have := (inv.quiet h hh).2 (K.count h) (by rw [count, (inv.quiet h hh).1])
      rw [found] at this; cases this
  | some pair =>
      obtain ⟨oph, Kh⟩ := pair
      obtain ⟨self, above, le, -⟩ := inv.loud h oph Kh hh
      have ge := inv.count_ge hh
      rcases Nat.lt_or_ge (Kh.count h) (logCount s₀ L D h) with lt | le'
      · have := above (K.count h) (by omega)
        rw [found] at this; cases this
      · have eq : logCount s₀ L D h = Kh.count h := by omega
        rw [count, eq, self] at found
        cases found
        exact ⟨Kh, rfl, eq⟩

/-- **Reading an announcement keeps the invariant.** -/
theorem Inv.read (inv : Inv s₀ L An D loc) {j : Fin n} {op : Y.Op} {K : Seen n Y}
    (hj : loc j = .busy (.read op K)) :
    Inv s₀ L An D (Function.update loc j (.busy (.claim op K (proposalOf An j op K)))) := by
  set p := proposalOf An j op K
  set loc' := Function.update loc j (.busy (.claim op K p))
  have keep : ∀ q, seenOf (loc' q) = seenOf (loc q) := by
    intro q; by_cases h : q = j
    · subst h; simp [loc', hj, seenOf]
    · simp [loc', Function.update_of_ne h]
  have ann : ∀ q, announcedOf (loc' q) = announcedOf (loc q) := by
    intro q; by_cases h : q = j
    · subst h; simp [loc', hj, announcedOf]
    · simp [loc', Function.update_of_ne h]
  have cl : ∀ q, claimOf (loc' q) = if q = j then some (K, p) else claimOf (loc q) := by
    intro q; simp only [loc']; rw [update_apply_eq]; split_ifs <;> rfl
  have annJ : announcedOf (loc j) = some (op, K) := by rw [hj]; rfl
  have seenJ : K = logSeen s₀ L K.pos := by
    have := inv.seen j; rw [hj] at this; exact this
  -- the new proposal, when the place is the first undecided one
  have fresh : K.pos = D → Pending s₀ L D loc' p := by
    intro hpos
    have hK : K = logSeen s₀ L D := by rw [← hpos]; exact seenJ
    simp only [p, proposalOf]
    cases found : An (helpee j K.pos) (K.count (helpee j K.pos)) with
    | some op' =>
        obtain ⟨Kh, h1, h2⟩ := inv.read_finds hK _ found
        exact ⟨Kh, by rw [ann]; exact h1, h2⟩
    | none =>
        refine ⟨K, by rw [ann]; exact annJ, ?_⟩
        have := count_eq_of_not_owned (s₀ := s₀) (L := L) (j := j) (le_of_eq hpos)
          (fun s e h1 h2 _ => by omega)
        show (logSeen s₀ L D).count j = K.count j
        rw [this, ← seenJ]
  refine ⟨inv.decided, fun q => by rw [keep]; exact inv.seen q,
    fun q => by rw [keep]; exact inv.seenLe q, ?_, ?_, ?_, ?_, ?_⟩
  · intro q op' K' p' h
    by_cases hq : q = j
    · subst hq; simp [loc'] at h
    · simp only [loc', Function.update_of_ne hq] at h; exact inv.learnLt q op' K' p' h
  · intro q hq
    rw [keep]; rw [ann] at hq; exact inv.quiet q hq
  · intro q op' K' h
    rw [ann] at h; exact inv.loud q op' K' h
  · intro q K' p' h hpos
    rw [cl] at h
    split_ifs at h with hqj
    · cases h; exact fresh hpos
    · obtain ⟨K'', h1, h2⟩ := inv.proposal q K' p' h hpos
      exact ⟨K'', by rw [ann]; exact h1, h2⟩
  · intro q op' K' h hc
    rw [ann] at h
    obtain ⟨k, hk, hD, hcl⟩ := inv.helped q op' K' h hc
    refine ⟨k, hk, hD, fun r K'' p'' hr hpos => ?_⟩
    rw [cl] at hr
    split_ifs at hr with hrj
    · cases hr
      -- the reader proposes for place `k`, which is `q`'s turn: it found `q`'s announcement
      have kD : K.pos = D := by have := inv.seenLe j; rw [hj] at this; simp [seenOf] at this; omega
      have hK : K = logSeen s₀ L D := by rw [← kD]; exact seenJ
      have who : helpee j K.pos = q := Fin.ext (by rw [helpee_val, hpos, hk])
      have count : K.count q = K'.count q := by
        have : K.count q = logCount s₀ L D q := by rw [hK]
        rw [this, hc]
      have found : An q (K.count q) = some op' := by
        rw [count]; exact (inv.loud q op' K' h).1
      simp only [p, proposalOf, who, found, propose]
    · exact hcl r K'' p'' hr hpos


/-- **A claim of an already decided place keeps the invariant.** -/
theorem Inv.claimOld (inv : Inv s₀ L An D loc) {j : Fin n} {op : Y.Op} {K : Seen n Y}
    {p : Entry n Y.Op} (hj : loc j = .busy (.claim op K p)) (lt : K.pos < D) :
    Inv s₀ L An D (Function.update loc j (.busy (.learn op K p))) := by
  set loc' := Function.update loc j (.busy (.learn op K p))
  have keep : ∀ q, seenOf (loc' q) = seenOf (loc q) := by
    intro q; by_cases h : q = j
    · subst h; simp [loc', hj, seenOf]
    · simp [loc', Function.update_of_ne h]
  have ann : ∀ q, announcedOf (loc' q) = announcedOf (loc q) := by
    intro q; by_cases h : q = j
    · subst h; simp [loc', hj, announcedOf]
    · simp [loc', Function.update_of_ne h]
  have cl : ∀ q, claimOf (loc' q) = if q = j then none else claimOf (loc q) := by
    intro q; simp only [loc']; rw [update_apply_eq]; split_ifs <;> rfl
  refine ⟨inv.decided, fun q => by rw [keep]; exact inv.seen q,
    fun q => by rw [keep]; exact inv.seenLe q, ?_, ?_, ?_, ?_, ?_⟩
  · intro q op' K' p' h
    by_cases hq : q = j
    · subst hq; simp only [loc', Function.update_self, UStatus.busy.injEq, Stage.learn.injEq] at h
      obtain ⟨-, rfl, -⟩ := h; exact lt
    · simp only [loc', Function.update_of_ne hq] at h; exact inv.learnLt q op' K' p' h
  · intro q hq; rw [keep]; rw [ann] at hq; exact inv.quiet q hq
  · intro q op' K' h; rw [ann] at h; exact inv.loud q op' K' h
  · intro q K' p' h hpos
    rw [cl] at h
    split_ifs at h with hqj
    obtain ⟨K'', h1, h2⟩ := inv.proposal q K' p' h hpos
    exact ⟨K'', by rw [ann]; exact h1, h2⟩
  · intro q op' K' h hc
    rw [ann] at h
    obtain ⟨k, hk, hD, hcl⟩ := inv.helped q op' K' h hc
    refine ⟨k, hk, hD, fun r K'' p'' hr hpos => ?_⟩
    rw [cl] at hr
    split_ifs at hr with hrj
    exact hcl r K'' p'' hr hpos

/-- **A claim of the first undecided place decides it and keeps the invariant**, with one more
place decided. -/
theorem Inv.claimNew (inv : Inv s₀ L An D loc) {j : Fin n} {op : Y.Op} {K : Seen n Y}
    {p : Entry n Y.Op} (hj : loc j = .busy (.claim op K p)) (hpos : K.pos = D) :
    Inv s₀ (Function.update L D (some p)) An (D + 1)
      (Function.update loc j (.busy (.learn op K p))) := by
  set L' := Function.update L D (some p)
  set loc' := Function.update loc j (.busy (.learn op K p))
  have keep : ∀ q, seenOf (loc' q) = seenOf (loc q) := by
    intro q; by_cases h : q = j
    · subst h; simp [loc', hj, seenOf]
    · simp [loc', Function.update_of_ne h]
  have ann : ∀ q, announcedOf (loc' q) = announcedOf (loc q) := by
    intro q; by_cases h : q = j
    · subst h; simp [loc', hj, announcedOf]
    · simp [loc', Function.update_of_ne h]
  have cl : ∀ q, claimOf (loc' q) = if q = j then none else claimOf (loc q) := by
    intro q; simp only [loc']; rw [update_apply_eq]; split_ifs <;> rfl
  have hLD : L D = none := by
    cases h : L D with
    | none => rfl
    | some e => have := (inv.decided D).mp (by rw [h]; rfl); omega
  have below : ∀ k, k ≤ D → logSeen s₀ L' k = logSeen s₀ L k := fun k hk =>
    logSeen_congr fun i hi => by simp only [L']; rw [Function.update_of_ne (by omega)]
  have succ : logSeen s₀ L' (D + 1) = (logSeen s₀ L D).add p := by
    rw [logSeen_succ_some (show L' D = some p by simp [L']), below D le_rfl]
  have count' : ∀ q, logCount s₀ L' (D + 1) q =
      logCount s₀ L D q + if p.1 = q then 1 else 0 := by
    intro q
    show (logSeen s₀ L' (D + 1)).count q = _
    rw [succ]
    by_cases h : p.1 = q
    · subst h; rw [count_add_self, if_pos rfl]
    · rw [count_add_other _ h, if_neg h]; rfl
  obtain ⟨Ko, ho, hco⟩ := inv.proposal j K p (by rw [hj]; rfl) hpos
  have claimLe : ∀ q K' p', claimOf (loc q) = some (K', p') → K'.pos ≤ D := by
    intro q K' p' h
    have := inv.seenLe q
    rwa [seenOf_of_claim h] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k = D
    · subst hk; simp [L']
    · simp only [L', Function.update_of_ne hk]
      rw [inv.decided k]; omega
  · intro q
    rw [keep, below _ (inv.seenLe q)]
    exact inv.seen q
  · intro q; rw [keep]; have := inv.seenLe q; omega
  · intro q op' K' p' h
    by_cases hq : q = j
    · subst hq; simp only [loc', Function.update_self, UStatus.busy.injEq, Stage.learn.injEq] at h
      obtain ⟨-, rfl, -⟩ := h; omega
    · simp only [loc', Function.update_of_ne hq] at h; have := inv.learnLt q op' K' p' h; omega
  · intro q hq
    rw [keep]; rw [ann] at hq
    have ne : p.1 ≠ q := by rintro rfl; rw [ho] at hq; cases hq
    rw [count', if_neg ne, add_zero]
    exact inv.quiet q hq
  · intro q op' K' h
    rw [ann] at h
    obtain ⟨self, above, le, entries⟩ := inv.loud q op' K' h
    refine ⟨self, above, ?_, ?_⟩
    · rw [count']
      split_ifs with hq
      · subst hq; rw [ho] at h; cases h; omega
      · omega
    · intro s e hs hsD he hown
      by_cases hsD' : s = D
      · subst hsD'
        simp only [L', Function.update_self, Option.some.injEq] at he
        subst he
        rw [← hown, ho] at h
        cases h; rfl
      · simp only [L', Function.update_of_ne hsD'] at he
        exact entries s e hs (by omega) he hown
  · intro q K' p' h hpos'
    rw [cl] at h
    split_ifs at h with hqj
    have := claimLe q K' p' h
    omega
  · intro q op' K' h hc
    rw [ann] at h
    have ne : p.1 ≠ q := by
      rintro rfl
      rw [ho] at h; cases h
      rw [count', if_pos rfl] at hc; omega
    rw [count', if_neg ne, add_zero] at hc
    obtain ⟨k, hk, hD, hcl⟩ := inv.helped q op' K' h hc
    have kD : k ≠ D := by
      rintro rfl
      exact ne (by rw [hcl j K p (by rw [hj]; rfl) hpos])
    refine ⟨k, hk, by omega, fun r K'' p'' hr hpos'' => ?_⟩
    rw [cl] at hr
    split_ifs at hr with hrj
    exact hcl r K'' p'' hr hpos''

/-- **Learning a decided place keeps the invariant.** -/
theorem Inv.learn (inv : Inv s₀ L An D loc) {j : Fin n} {op : Y.Op} {K : Seen n Y}
    {p e : Entry n Y.Op} (hj : loc j = .busy (.learn op K p)) (he : L K.pos = some e) :
    Inv s₀ L An D (Function.update loc j (.busy (afterLearn j op K e))) := by
  set loc' := Function.update loc j (.busy (afterLearn j op K e))
  have annJ : announcedOf (loc j) = some (op, K) := by rw [hj]; rfl
  have seenJ : K = logSeen s₀ L K.pos := by
    have := inv.seen j; rw [hj] at this; exact this
  have lt : K.pos < D := inv.learnLt j op K p hj
  have hK' : K.add e = logSeen s₀ L (K.pos + 1) := by
    rw [logSeen_succ_some he, ← seenJ]
  obtain ⟨selfJ, aboveJ, leJ, entriesJ⟩ := inv.loud j op K annJ
  have keepOther : ∀ q, q ≠ j → loc' q = loc q := fun q h => Function.update_of_ne h _ _
  have clOther : ∀ q, claimOf (loc' q) = claimOf (loc q) := by
    intro q; by_cases h : q = j
    · subst h; simp only [loc', Function.update_self, hj, afterLearn]; split_ifs <;> rfl
    · rw [keepOther q h]
  have seenNew : seenOf (loc' j) = K.add e := by
    simp only [loc', Function.update_self, afterLearn]; split_ifs <;> rfl
  have seenLeNew : (K.add e).pos ≤ D := by simp [Seen.add]; omega
  by_cases owner : e.1 = j
  · -- its own operation: it will return
    have eop : e.2 = op := entriesJ K.pos e le_rfl lt he owner
    have countJ : logCount s₀ L D j = K.count j + 1 := by
      have := count_lt_of_owned (s₀ := s₀) (le_refl K.pos) lt he
      rw [owner, ← seenJ] at this
      have le' : (logSeen s₀ L D).count j ≤ K.count j + 1 := leJ
      show (logSeen s₀ L D).count j = K.count j + 1
      omega
    have annNew : announcedOf (loc' j) = none := by
      simp only [loc', Function.update_self, afterLearn, if_pos owner]; rfl
    have ann : ∀ q, announcedOf (loc' q) = if q = j then none else announcedOf (loc q) := by
      intro q; split_ifs with h
      · subst h; exact annNew
      · rw [keepOther q h]
    refine ⟨inv.decided, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro q; by_cases h : q = j
      · subst h; rw [seenNew, hK']; simp
      · rw [keepOther q h]; exact inv.seen q
    · intro q; by_cases h : q = j
      · subst h; rw [seenNew]; exact seenLeNew
      · rw [keepOther q h]; exact inv.seenLe q
    · intro q op' K' p' h
      by_cases hq : q = j
      · subst hq; simp [loc', afterLearn, owner] at h
      · rw [keepOther q hq] at h; exact inv.learnLt q op' K' p' h
    · intro q hq
      by_cases h : q = j
      · subst h
        rw [seenNew]
        have addCount : (K.add e).count q = K.count q + 1 := by rw [← owner, count_add_self]
        refine ⟨by rw [countJ, addCount], fun t ht => aboveJ t (by omega)⟩
      · rw [keepOther q h] at hq ⊢; exact inv.quiet q hq
    · intro q op' K' h
      rw [ann] at h
      split_ifs at h with hqj
      exact inv.loud q op' K' h
    · intro q K' p' h hpos
      rw [clOther] at h
      obtain ⟨K'', h1, h2⟩ := inv.proposal q K' p' h hpos
      refine ⟨K'', ?_, h2⟩
      rw [ann]
      split_ifs with hpj
      · rw [hpj, annJ] at h1; cases h1
        rw [hpj] at h2; omega
      · exact h1
    · intro q op' K' h hc
      rw [ann] at h
      split_ifs at h with hqj
      obtain ⟨k, hk, hD, hcl⟩ := inv.helped q op' K' h hc
      exact ⟨k, hk, hD, fun r K'' p'' hr hpos => hcl r K'' p'' (by rw [← clOther]; exact hr) hpos⟩
  · -- another's operation: read on
    have countSame : (K.add e).count j = K.count j := count_add_other _ owner
    have annNew : announcedOf (loc' j) = some (op, K.add e) := by
      simp only [loc', Function.update_self, afterLearn, if_neg owner]; rfl
    have ann : ∀ q, announcedOf (loc' q) =
        if q = j then some (op, K.add e) else announcedOf (loc q) := by
      intro q; split_ifs with h
      · subst h; exact annNew
      · rw [keepOther q h]
    refine ⟨inv.decided, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro q; by_cases h : q = j
      · subst h; rw [seenNew, hK']; simp
      · rw [keepOther q h]; exact inv.seen q
    · intro q; by_cases h : q = j
      · subst h; rw [seenNew]; exact seenLeNew
      · rw [keepOther q h]; exact inv.seenLe q
    · intro q op' K' p' h
      by_cases hq : q = j
      · subst hq; simp [loc', afterLearn, owner] at h
      · rw [keepOther q hq] at h; exact inv.learnLt q op' K' p' h
    · intro q hq
      by_cases h : q = j
      · subst h; rw [annNew] at hq; cases hq
      · rw [keepOther q h] at hq ⊢; exact inv.quiet q hq
    · intro q op' K' h
      rw [ann] at h
      split_ifs at h with hqj
      · subst hqj; cases h
        refine ⟨by rw [countSame]; exact selfJ, fun t ht => aboveJ t (by rw [countSame] at ht; exact ht),
          by rw [countSame]; exact leJ, fun s e' hs hsD he' hown => ?_⟩
        exact entriesJ s e' (by simp [Seen.add] at hs; omega) hsD he' hown
      · exact inv.loud q op' K' h
    · intro q K' p' h hpos
      rw [clOther] at h
      obtain ⟨K'', h1, h2⟩ := inv.proposal q K' p' h hpos
      by_cases hpj : p'.1 = j
      · rw [hpj, annJ] at h1; cases h1
        refine ⟨K.add e, by rw [ann, if_pos hpj], ?_⟩
        rw [hpj, countSame]; rw [hpj] at h2; exact h2
      · exact ⟨K'', by rw [ann, if_neg hpj]; exact h1, h2⟩
    · intro q op' K' h hc
      rw [ann] at h
      split_ifs at h with hqj
      · subst hqj; cases h
        obtain ⟨k, hk, hD, hcl⟩ := inv.helped q op K annJ (by rw [hc, countSame])
        exact ⟨k, hk, hD, fun r K'' p'' hr hpos => hcl r K'' p'' (by rw [← clOther]; exact hr) hpos⟩
      · obtain ⟨k, hk, hD, hcl⟩ := inv.helped q op' K' h hc
        exact ⟨k, hk, hD, fun r K'' p'' hr hpos => hcl r K'' p'' (by rw [← clOther]; exact hr) hpos⟩

/-- **Returning keeps the invariant.** -/
theorem Inv.ret (inv : Inv s₀ L An D loc) {j : Fin n} {r : Y.Res} {K : Seen n Y}
    (hj : loc j = .busy (.done r K)) : Inv s₀ L An D (Function.update loc j (.idle K)) := by
  set loc' := Function.update loc j (.idle K)
  have keep : ∀ q, seenOf (loc' q) = seenOf (loc q) := by
    intro q; by_cases h : q = j
    · subst h; simp [loc', hj, seenOf]
    · simp [loc', Function.update_of_ne h]
  have ann : ∀ q, announcedOf (loc' q) = announcedOf (loc q) := by
    intro q; by_cases h : q = j
    · subst h; simp [loc', hj, announcedOf]
    · simp [loc', Function.update_of_ne h]
  have cl : ∀ q, claimOf (loc' q) = claimOf (loc q) := by
    intro q; by_cases h : q = j
    · subst h; simp [loc', hj, claimOf]
    · simp [loc', Function.update_of_ne h]
  refine ⟨inv.decided, fun q => by rw [keep]; exact inv.seen q,
    fun q => by rw [keep]; exact inv.seenLe q, ?_, ?_, ?_, ?_, ?_⟩
  · intro q op' K' p' h
    by_cases hq : q = j
    · subst hq; simp [loc'] at h
    · simp only [loc', Function.update_of_ne hq] at h; exact inv.learnLt q op' K' p' h
  · intro q hq; rw [keep]; rw [ann] at hq; exact inv.quiet q hq
  · intro q op' K' h; rw [ann] at h; exact inv.loud q op' K' h
  · intro q K' p' h hpos
    rw [cl] at h
    obtain ⟨K'', h1, h2⟩ := inv.proposal q K' p' h hpos
    exact ⟨K'', by rw [ann]; exact h1, h2⟩
  · intro q op' K' h hc
    rw [ann] at h
    obtain ⟨k, hk, hD, hcl⟩ := inv.helped q op' K' h hc
    exact ⟨k, hk, hD, fun r' K'' p'' hr hpos => hcl r' K'' p'' (by rw [← cl]; exact hr) hpos⟩

/-- **The invariant holds at the start.** -/
theorem inv_start : Inv s₀ (fun _ => none) (fun _ _ => none) 0
    (fun _ => (UStatus.idle (Seen.start s₀) : UStatus n Y)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; simp
  · intro q; rfl
  · intro q; exact le_rfl
  · intro q op K p h; cases h
  · intro q _; exact ⟨rfl, fun _ _ => rfl⟩
  · intro q op K h; cases h
  · intro q K p h; cases h
  · intro q op K h; cases h

end Keep

/-! ## Linearizability -/

section Simulation

variable {s₀ : Y.State}

/-- The atomic status of an announced operation: pending while it is not placed; once placed, done
with the answer it has at its place. -/
def Linked (s₀ : Y.State) (L : ℕ → Option (Entry n Y.Op)) (D : ℕ) (j : Fin n) (op : Y.Op)
    (K : Seen n Y) (a : (atomic Y s₀ n).Status) : Prop :=
  (logCount s₀ L D j = K.count j ∧ a = .busy (.pending op)) ∨
    ∃ s, K.pos ≤ s ∧ s < D ∧ L s = some (j, op) ∧
      a = .busy (.done (Y.apply (logSeen s₀ L s).state op).2)

/-- How a process's status matches its status in the target used atomically. -/
def Matches (s₀ : Y.State) (L : ℕ → Option (Entry n Y.Op)) (D : ℕ) (j : Fin n) :
    UStatus n Y → (atomic Y s₀ n).Status → Prop
  | .idle _, a => a = .idle ()
  | .busy (.announce op _), a => a = .busy (.pending op)
  | .busy (.read op K), a => Linked s₀ L D j op K a
  | .busy (.claim op K _), a => Linked s₀ L D j op K a
  | .busy (.learn op K _), a => Linked s₀ L D j op K a
  | .busy (.done r _), a => a = .busy (.done r)

variable {L : ℕ → Option (Entry n Y.Op)} {An : Fin n → ℕ → Option Y.Op} {D : ℕ}
  {loc : Fin n → UStatus n Y}

theorem matches_announced {j : Fin n} {st : UStatus n Y} {op : Y.Op} {K : Seen n Y}
    (h : announcedOf st = some (op, K)) {a : (atomic Y s₀ n).Status} :
    Matches s₀ L D j st a ↔ Linked s₀ L D j op K a := by
  revert h; cases st with
  | idle K' => simp [announcedOf]
  | busy w =>
      cases w <;> simp only [announcedOf, reduceCtorEq, Option.some.injEq, Prod.mk.injEq,
        Matches, IsEmpty.forall_iff] <;> rintro ⟨rfl, rfl⟩ <;> exact Iff.rfl

/-- A pending operation not yet placed is pending in the target. -/
theorem Linked.pending_of_count {j : Fin n} {op : Y.Op} {K : Seen n Y}
    {a : (atomic Y s₀ n).Status} (link : Linked s₀ L D j op K a) (seen : K = logSeen s₀ L K.pos)
    (count : logCount s₀ L D j = K.count j) : a = .busy (.pending op) := by
  rcases link with ⟨-, h⟩ | ⟨s, hs, hsD, hL, -⟩
  · exact h
  · have := count_lt_of_owned (s₀ := s₀) hs hsD hL
    simp only at this
    rw [← seen] at this
    have : (logSeen s₀ L D).count j = K.count j := count
    omega

/-- Placing `p` at the first undecided place keeps the match of every process but `p`'s owner. -/
theorem Linked.extend {j : Fin n} {op : Y.Op} {K : Seen n Y} {a : (atomic Y s₀ n).Status}
    {p : Entry n Y.Op} (link : Linked s₀ L D j op K a) (ne : p.1 ≠ j) :
    Linked s₀ (Function.update L D (some p)) (D + 1) j op K a := by
  have below : ∀ k, k ≤ D → logSeen s₀ (Function.update L D (some p)) k = logSeen s₀ L k :=
    fun k hk => logSeen_congr fun i hi => by rw [Function.update_of_ne (by omega)]
  rcases link with ⟨hc, ha⟩ | ⟨s, hs, hsD, hL, ha⟩
  · refine Or.inl ⟨?_, ha⟩
    show (logSeen s₀ _ (D + 1)).count j = _
    rw [logSeen_succ_some (show Function.update L D (some p) D = some p by simp), below D le_rfl,
      count_add_other _ ne]
    exact hc
  · refine Or.inr ⟨s, hs, by omega, by rw [Function.update_of_ne (by omega)]; exact hL, ?_⟩
    rw [below s (by omega)]; exact ha

theorem Matches.extend {j : Fin n} {st : UStatus n Y} {a : (atomic Y s₀ n).Status}
    {p : Entry n Y.Op} (m : Matches s₀ L D j st a) (ne : p.1 ≠ j) :
    Matches s₀ (Function.update L D (some p)) (D + 1) j st a := by
  cases st with
  | idle K => exact m
  | busy w =>
      cases w with
      | announce op K => exact m
      | read op K => exact Linked.extend m ne
      | claim op K p' => exact Linked.extend m ne
      | learn op K p' => exact Linked.extend m ne
      | done r K => exact m

variable {X : DetObject} {B : Board X n Y.Op}

/-- A status of the universal construction, read without the board. -/
def toU : (universal B s₀).Status → UStatus n Y
  | .idle K => .idle K
  | .busy w => .busy w

/-- The statuses of a configuration, read without the board. -/
def uloc (C : (universal B s₀).Config) : Fin n → UStatus n Y := fun j => toU (C.loc j)

theorem uloc_update (C : (universal B s₀).Config) (obj : X.State) (j : Fin n)
    (st : (universal B s₀).Status) :
    uloc (B := B) (s₀ := s₀) ⟨obj, Function.update C.loc j st⟩ =
      Function.update (uloc C) j (toU st) := by
  funext q
  simp only [uloc]
  by_cases h : q = j
  · subst h; simp
  · simp [Function.update_of_ne h]; rfl

/-- **The simulation relation**: the invariant holds, the target's state is the state after the
decided places, and every process matches. -/
def Rel (C : (universal B s₀).Config) (A : (atomic Y s₀ n).Config) : Prop :=
  ∃ D, Inv s₀ (B.slot C.obj) (B.ann C.obj) D (uloc C) ∧
    A.obj = (logSeen s₀ (B.slot C.obj) D).state ∧
    ∀ j, Matches s₀ (B.slot C.obj) D j (uloc C j) (A.loc j)

theorem rel_initial : Rel (B := B) (s₀ := s₀) (universal B s₀).initial (atomic Y s₀ n).initial := by
  have slots : B.slot B.init = fun _ => none := funext B.init_slot
  have anns : B.ann B.init = fun _ _ => none := funext fun i => funext (B.init_ann i)
  refine ⟨0, ?_, rfl, fun j => rfl⟩
  show Inv s₀ (B.slot B.init) (B.ann B.init) 0 (fun _ => UStatus.idle (Seen.start s₀))
  rw [slots, anns]
  exact inv_start

theorem toU_busy (w : (universal B s₀).Work) : toU (B := B) (s₀ := s₀) (.busy w) = UStatus.busy w :=
  rfl

/-- **Each step of the universal construction is matched by at most one step of the target used
atomically.** A claim that decides a place is the instant the placed operation takes effect, even
when the claimer is helping another process. -/
theorem rel_step {C : (universal B s₀).Config} {A : (atomic Y s₀ n).Config}
    {ch : Choice n Y.Op} {e : Option (Event n Y.Op Y.Res)} {C' : (universal B s₀).Config}
    (rel : Rel C A) (step : (universal B s₀).Step C ch e C') :
    ∃ cs A', (atomic Y s₀ n).Run A cs e.toList A' ∧ Rel C' A' := by
  obtain ⟨D, inv, obj, mt⟩ := rel
  cases step with
  | @invoke j m op h =>
      have hU : uloc C j = .idle m := by simp [uloc, h, toU]
      have hA : A.loc j = .idle () := by have := mt j; rw [hU] at this; exact this
      refine ⟨[.invoke j op], ⟨A.obj, Function.update A.loc j (.busy (.pending op))⟩,
        Implementation.run_single (Implementation.Step.invoke (m := ()) op hA), D, ?_, obj, ?_⟩
      · rw [uloc_update]; exact inv.invoke op hU
      · intro q
        rw [uloc_update]
        by_cases hq : q = j
        · subst hq; simp only [Function.update_self]; rfl
        · simp only [Function.update_of_ne hq]; exact mt q
  | @call j w a s r h hm hf =>
      have hf' : X.apply C.obj a = (s, r) := hf
      have sEq : s = (X.apply C.obj a).1 := by rw [hf']
      have rEq : r = (X.apply C.obj a).2 := by rw [hf']
      have hU : uloc C j = .busy w := by simp [uloc, h, toU]
      cases w with
      | announce op K =>
          have ha : B.write j (K.count j) op = a := by simpa [universal] using hm
          subst ha
          have quietJ := inv.quiet j (by rw [hU]; rfl)
          rw [hU] at quietJ
          have pre : ∀ t', K.count j ≤ t' → B.ann C.obj j t' = none := quietJ.2
          have hA : A.loc j = .busy (.pending op) := by have := mt j; rw [hU] at this; exact this
          refine ⟨[], A, Implementation.run_nil A, D, ?_, ?_, ?_⟩
          · show Inv s₀ (B.slot s) (B.ann s) D _
            rw [uloc_update, sEq, B.write_slot]
            exact inv.announce hU (B.write_self _ _ _ _ pre) (B.write_above _ _ _ _ pre)
              (fun q hq => B.write_other _ _ _ _ q hq)
          · show A.obj = (logSeen s₀ (B.slot s) D).state
            rw [sEq, B.write_slot]; exact obj
          · intro q
            show Matches s₀ (B.slot s) D q _ _
            rw [uloc_update, sEq, B.write_slot]
            by_cases hq : q = j
            · subst hq
              simp only [Function.update_self]
              exact Or.inl ⟨quietJ.1, hA⟩
            · simp only [Function.update_of_ne hq]; exact mt q
      | read op K =>
          have ha : B.read (helpee j K.pos) (K.count (helpee j K.pos)) = a := by
            simpa [universal] using hm
          subst ha
          have slots : B.slot s = B.slot C.obj := by rw [sEq, B.read_slot]
          have anns : B.ann s = B.ann C.obj := by rw [sEq, B.read_ann]
          have out : B.readOut (helpee j K.pos) (K.count (helpee j K.pos)) r =
              B.ann C.obj (helpee j K.pos) (K.count (helpee j K.pos)) := by rw [rEq, B.read_out]
          have nxt : (universal B s₀).next j (.read op K) r =
              .claim op K (proposalOf (B.ann C.obj) j op K) := by
            simp only [universal, proposalOf, out]
          refine ⟨[], A, Implementation.run_nil A, D, ?_, ?_, ?_⟩
          · show Inv s₀ (B.slot s) (B.ann s) D _
            rw [uloc_update, slots, anns, toU_busy, nxt]
            exact inv.read hU
          · show A.obj = (logSeen s₀ (B.slot s) D).state
            rw [slots]; exact obj
          · intro q
            show Matches s₀ (B.slot s) D q _ _
            rw [uloc_update, slots, toU_busy, nxt]
            by_cases hq : q = j
            · subst hq
              simp only [Function.update_self]
              have := mt q; rw [hU] at this; exact this
            · simp only [Function.update_of_ne hq]; exact mt q
      | claim op K p =>
          have ha : B.claim K.pos p = a := by simpa [universal] using hm
          subst ha
          have anns : B.ann s = B.ann C.obj := by rw [sEq, B.claim_ann]
          have slots : B.slot s = Function.update (B.slot C.obj) K.pos
              (some ((B.slot C.obj K.pos).getD p)) := by rw [sEq, B.claim_slot]
          have nxt : (universal B s₀).next j (.claim op K p) r = .learn op K p := rfl
          have le : K.pos ≤ D := by have := inv.seenLe j; rw [hU] at this; exact this
          rcases Nat.lt_or_ge K.pos D with lt | ge
          · -- the place was decided: nothing changes but the claimer's stage
            obtain ⟨w, hw⟩ : ∃ w, B.slot C.obj K.pos = some w := by
              cases hk : B.slot C.obj K.pos with
              | none => have := (inv.decided K.pos).mpr lt; rw [hk] at this; cases this
              | some w => exact ⟨w, rfl⟩
            have slots' : B.slot s = B.slot C.obj := by
              rw [slots, hw]; simp only [Option.getD_some]; rw [← hw, Function.update_eq_self]
            refine ⟨[], A, Implementation.run_nil A, D, ?_, ?_, ?_⟩
            · show Inv s₀ (B.slot s) (B.ann s) D _
              rw [uloc_update, slots', anns, toU_busy, nxt]
              exact inv.claimOld hU lt
            · show A.obj = (logSeen s₀ (B.slot s) D).state
              rw [slots']; exact obj
            · intro q
              show Matches s₀ (B.slot s) D q _ _
              rw [uloc_update, slots', toU_busy, nxt]
              by_cases hq : q = j
              · subst hq
                simp only [Function.update_self]
                have := mt q; rw [hU] at this; exact this
              · simp only [Function.update_of_ne hq]; exact mt q
          · -- the first undecided place: the proposal is placed and takes effect
            have hpos : K.pos = D := by omega
            have hLD : B.slot C.obj D = none := by
              cases hk : B.slot C.obj D with
              | none => rfl
              | some w => have := (inv.decided D).mp (by rw [hk]; rfl); omega
            have slots' : B.slot s = Function.update (B.slot C.obj) D (some p) := by
              rw [slots, hpos, hLD]; rfl
            obtain ⟨Ko, ho, hco⟩ := inv.proposal j K p (by rw [hU]; rfl) hpos
            have seenO : Ko = logSeen s₀ (B.slot C.obj) Ko.pos := by
              have := inv.seen p.1; rwa [seenOf_of_announced ho] at this
            have hAo : A.loc p.1 = .busy (.pending p.2) :=
              ((matches_announced ho).mp (mt p.1)).pending_of_count seenO hco
            have lin := Implementation.Step.call (I := atomic Y s₀ n) (C := A) (i := p.1)
              (w := (AtomicWork.pending p.2 : AtomicWork Y.Op Y.Res)) (a := p.2)
              (s := (Y.apply A.obj p.2).1) (r := (Y.apply A.obj p.2).2) hAo rfl rfl
            have below : ∀ k, k ≤ D →
                logSeen s₀ (Function.update (B.slot C.obj) D (some p)) k = logSeen s₀ (B.slot C.obj) k :=
              fun k hk => logSeen_congr fun i hi => by rw [Function.update_of_ne (by omega)]
            have annNew : ∀ q, announcedOf (Function.update (uloc C) j (.busy (.learn op K p)) q) =
                announcedOf (uloc C q) := by
              intro q; by_cases hq : q = j
              · subst hq; simp [hU, announcedOf]
              · simp [Function.update_of_ne hq]
            refine ⟨[.move p.1], _, Implementation.run_single lin, D + 1, ?_, ?_, ?_⟩
            · show Inv s₀ (B.slot s) (B.ann s) (D + 1) _
              rw [uloc_update, slots', anns, toU_busy, nxt]
              exact inv.claimNew hU hpos
            · show (Y.apply A.obj p.2).1 = (logSeen s₀ (B.slot s) (D + 1)).state
              rw [slots', logSeen_succ_some (show Function.update (B.slot C.obj) D (some p) D = some p
                by simp), below D le_rfl, obj]
              rfl
            · intro q
              show Matches s₀ (B.slot s) (D + 1) q _ _
              rw [uloc_update, slots', toU_busy, nxt]
              by_cases hqo : q = p.1
              · subst hqo
                have ho' := ho; rw [← annNew] at ho'
                refine (matches_announced ho').mpr (Or.inr ⟨D, ?_, by omega, by simp, ?_⟩)
                · have := inv.seenLe p.1; rwa [seenOf_of_announced ho] at this
                · simp only [Function.update_self]
                  rw [below D le_rfl, ← obj]
                  rfl
              · have mq : Matches s₀ (B.slot C.obj) D q
                    (Function.update (uloc C) j (.busy (.learn op K p)) q) (A.loc q) := by
                  by_cases hq : q = j
                  · subst hq
                    simp only [Function.update_self]
                    have := mt q; rw [hU] at this; exact this
                  · simp only [Function.update_of_ne hq]; exact mt q
                simp only [Function.update_of_ne hqo]
                exact mq.extend (Ne.symm hqo)
      | learn op K p =>
          have ha : B.learn K.pos p = a := by simpa [universal] using hm
          subst ha
          have lt : K.pos < D := inv.learnLt j op K p hU
          obtain ⟨e', hw⟩ : ∃ e', B.slot C.obj K.pos = some e' := by
            cases hk : B.slot C.obj K.pos with
            | none => have := (inv.decided K.pos).mpr lt; rw [hk] at this; cases this
            | some w => exact ⟨w, rfl⟩
          have slots : B.slot s = B.slot C.obj := by rw [sEq]; exact B.learn_slot _ _ _ _ hw
          have anns : B.ann s = B.ann C.obj := by rw [sEq]; exact B.learn_ann _ _ _ _ hw
          have out : B.learned K.pos r p = e' := by rw [rEq]; exact B.learn_out _ _ _ _ hw
          have nxt : (universal B s₀).next j (.learn op K p) r = afterLearn j op K e' := by
            simp only [universal, out]
          have annJ : announcedOf (uloc C j) = some (op, K) := by rw [hU]; rfl
          have seenJ : K = logSeen s₀ (B.slot C.obj) K.pos := by
            have := inv.seen j; rw [hU] at this; exact this
          have linkJ : Linked s₀ (B.slot C.obj) D j op K (A.loc j) := by
            have := mt j; rw [hU] at this; exact this
          refine ⟨[], A, Implementation.run_nil A, D, ?_, ?_, ?_⟩
          · show Inv s₀ (B.slot s) (B.ann s) D _
            rw [uloc_update, slots, anns, toU_busy, nxt]
            exact inv.learn hU hw
          · show A.obj = (logSeen s₀ (B.slot s) D).state
            rw [slots]; exact obj
          · intro q
            show Matches s₀ (B.slot s) D q _ _
            rw [uloc_update, slots, toU_busy, nxt]
            by_cases hq : q = j
            · subst hq
              simp only [Function.update_self]
              obtain ⟨-, -, leJ, entriesJ⟩ := inv.loud q op K annJ
              by_cases owner : e'.1 = q
              · -- its own operation: the target has applied it at this place
                simp only [afterLearn, if_pos owner, Matches]
                have eop : e'.2 = op := entriesJ K.pos e' le_rfl lt hw owner
                rcases linkJ with ⟨hc, -⟩ | ⟨s', hs, hsD, hL, ha⟩
                · have := count_lt_of_owned (s₀ := s₀) (le_refl K.pos) lt hw
                  rw [owner, ← seenJ] at this
                  have : (logSeen s₀ (B.slot C.obj) D).count q = K.count q := hc
                  omega
                · have same : s' = K.pos := by
                    by_contra ne
                    have two := count_lt_of_two_owned (s₀ := s₀) (le_refl K.pos)
                      (show K.pos < s' by omega) hsD hw hL (by simp [owner])
                    rw [owner, ← seenJ] at two
                    have : (logSeen s₀ (B.slot C.obj) D).count q ≤ K.count q + 1 := leJ
                    omega
                  subst same
                  rw [ha, ← seenJ, eop]
              · simp only [afterLearn, if_neg owner, Matches]
                rcases linkJ with ⟨hc, ha⟩ | ⟨s', hs, hsD, hL, ha⟩
                · exact Or.inl ⟨by rw [count_add_other _ owner]; exact hc, ha⟩
                · refine Or.inr ⟨s', ?_, hsD, hL, ha⟩
                  have : s' ≠ K.pos := by
                    rintro rfl; rw [hw] at hL; cases hL; exact owner rfl
                  simp [Seen.add]; omega
            · simp only [Function.update_of_ne hq]; exact mt q
      | done r' K =>
          simp [universal] at hm
  | @wait j w a h hm never =>
      exact absurd rfl (never (X.apply C.obj a).1 (X.apply C.obj a).2)
  | @ret j w r m h hm =>
      have hU : uloc C j = .busy w := by simp [uloc, h, toU]
      cases w with
      | done r' K =>
          simp only [universal] at hm
          cases hm
          have hA : A.loc j = .busy (AtomicWork.done r) := by
            have := mt j; rw [hU] at this; exact this
          have retA : (atomic Y s₀ n).Step A (.move j) (some (.respond j r))
              ⟨A.obj, Function.update A.loc j (.idle ())⟩ :=
            Implementation.Step.ret (w := (AtomicWork.done r : AtomicWork Y.Op Y.Res)) hA rfl
          refine ⟨[.move j], _, Implementation.run_single retA, D, ?_, obj, ?_⟩
          · rw [uloc_update]; exact inv.ret hU
          · intro q
            rw [uloc_update]
            by_cases hq : q = j
            · subst hq; simp only [Function.update_self]; rfl
            · simp only [Function.update_of_ne hq]; exact mt q
      | announce op K => simp [universal] at hm
      | read op K => simp [universal] at hm
      | claim op K p => simp [universal] at hm
      | learn op K p => simp [universal] at hm
  | @rest j m h => exact ⟨[], A, Implementation.run_nil A, D, inv, obj, mt⟩

/-- **The universal construction is linearizable.** -/
theorem universal_linearizable (B : Board X n Y.Op) (s₀ : Y.State) :
    (universal B s₀).Linearizable s₀ :=
  Implementation.linearizable_of_simulation Rel rel_initial
    (fun _ _ _ _ _ rel step => rel_step rel step)

end Simulation

/-! ## Wait-freedom -/

section Abstract

variable {s₀ : Y.State}

/-- One step of the universal construction, seen without the board: how the views of the slots and
of the announcements, and the statuses, change. -/
inductive AStep : (ℕ → Option (Entry n Y.Op)) → (Fin n → ℕ → Option Y.Op) →
    (Fin n → UStatus n Y) → (ℕ → Option (Entry n Y.Op)) → (Fin n → ℕ → Option Y.Op) →
    (Fin n → UStatus n Y) → Prop
  | invoke {L An loc} {j : Fin n} {K : Seen n Y} (op : Y.Op) : loc j = .idle K →
      AStep L An loc L An (Function.update loc j (.busy (.announce op K)))
  | announce {L An An' loc} {j : Fin n} {op : Y.Op} {K : Seen n Y} :
      loc j = .busy (.announce op K) → An' j (K.count j) = some op →
      (∀ t, K.count j < t → An' j t = none) → (∀ q, q ≠ j → An' q = An q) →
      AStep L An loc L An' (Function.update loc j (.busy (.read op K)))
  | read {L An loc} {j : Fin n} {op : Y.Op} {K : Seen n Y} : loc j = .busy (.read op K) →
      AStep L An loc L An (Function.update loc j (.busy (.claim op K (proposalOf An j op K))))
  | claimOld {L An loc} {j : Fin n} {op : Y.Op} {K : Seen n Y} {p w : Entry n Y.Op} :
      loc j = .busy (.claim op K p) → L K.pos = some w →
      AStep L An loc L An (Function.update loc j (.busy (.learn op K p)))
  | claimNew {L An loc} {j : Fin n} {op : Y.Op} {K : Seen n Y} {p : Entry n Y.Op} :
      loc j = .busy (.claim op K p) → L K.pos = none →
      AStep L An loc (Function.update L K.pos (some p)) An
        (Function.update loc j (.busy (.learn op K p)))
  | learn {L An loc} {j : Fin n} {op : Y.Op} {K : Seen n Y} {p e : Entry n Y.Op} :
      loc j = .busy (.learn op K p) → L K.pos = some e →
      AStep L An loc L An (Function.update loc j (.busy (afterLearn j op K e)))
  | ret {L An loc} {j : Fin n} {r : Y.Res} {K : Seen n Y} : loc j = .busy (.done r K) →
      AStep L An loc L An (Function.update loc j (.idle K))
  | rest {L An loc} : AStep L An loc L An loc

theorem Inv.decided_eq {L : ℕ → Option (Entry n Y.Op)} {An An' : Fin n → ℕ → Option Y.Op}
    {D D' : ℕ} {loc loc' : Fin n → UStatus n Y} (inv : Inv s₀ L An D loc)
    (inv' : Inv s₀ L An' D' loc') : D = D' := by
  by_contra ne
  rcases Nat.lt_or_gt_of_ne ne with lt | lt
  · have := (inv'.decided D).mpr lt; rw [inv.decided D] at this; omega
  · have := (inv.decided D').mpr lt; rw [inv'.decided D'] at this; omega

/-- **Every abstract step keeps the invariant.** -/
theorem Inv.astep {L L' : ℕ → Option (Entry n Y.Op)} {An An' : Fin n → ℕ → Option Y.Op} {D : ℕ}
    {loc loc' : Fin n → UStatus n Y} (inv : Inv s₀ L An D loc)
    (step : AStep L An loc L' An' loc') : ∃ D', Inv s₀ L' An' D' loc' := by
  cases step with
  | invoke op h => exact ⟨D, inv.invoke op h⟩
  | announce h self above other => exact ⟨D, inv.announce h self above other⟩
  | read h => exact ⟨D, inv.read h⟩
  | claimOld h hw =>
      refine ⟨D, inv.claimOld h ?_⟩
      exact (inv.decided _).mp (by rw [hw]; rfl)
  | claimNew h hn =>
      rename_i j op K p
      have le : K.pos ≤ D := by have := inv.seenLe j; rw [h] at this; exact this
      have ge : D ≤ K.pos := by
        by_contra lt
        have := (inv.decided K.pos).mpr (by omega)
        rw [hn] at this; cases this
      have hpos : K.pos = D := by omega
      refine ⟨D + 1, ?_⟩
      rw [hpos]
      exact inv.claimNew h hpos
  | learn h he => exact ⟨D, inv.learn h he⟩
  | ret h => exact ⟨D, inv.ret h⟩
  | rest => exact ⟨D, inv⟩

end Abstract

section Concrete

variable {s₀ : Y.State} {X : DetObject} {B : Board X n Y.Op}

/-- **Every step of the universal construction is an abstract step.** -/
theorem concrete_astep {C C' : (universal B s₀).Config} {ch : Choice n Y.Op}
    {e : Option (Event n Y.Op Y.Res)} {D : ℕ}
    (inv : Inv s₀ (B.slot C.obj) (B.ann C.obj) D (uloc C)) (step : (universal B s₀).Step C ch e C') :
    AStep (B.slot C.obj) (B.ann C.obj) (uloc C) (B.slot C'.obj) (B.ann C'.obj) (uloc C') := by
  cases step with
  | @invoke j m op h =>
      have hU : uloc C j = .idle m := by simp [uloc, h, toU]
      rw [uloc_update]
      exact AStep.invoke op hU
  | @call j w a s r h hm hf =>
      have hf' : X.apply C.obj a = (s, r) := hf
      have sEq : s = (X.apply C.obj a).1 := by rw [hf']
      have rEq : r = (X.apply C.obj a).2 := by rw [hf']
      have hU : uloc C j = .busy w := by simp [uloc, h, toU]
      cases w with
      | announce op K =>
          have ha : B.write j (K.count j) op = a := by simpa [universal] using hm
          subst ha
          have quietJ := inv.quiet j (by rw [hU]; rfl)
          rw [hU] at quietJ
          have pre : ∀ t', K.count j ≤ t' → B.ann C.obj j t' = none := quietJ.2
          show AStep _ _ _ (B.slot s) (B.ann s) _
          rw [uloc_update, sEq, B.write_slot]
          exact AStep.announce hU (B.write_self _ _ _ _ pre) (B.write_above _ _ _ _ pre)
            (fun q hq => B.write_other _ _ _ _ q hq)
      | read op K =>
          have ha : B.read (helpee j K.pos) (K.count (helpee j K.pos)) = a := by
            simpa [universal] using hm
          subst ha
          have slots : B.slot s = B.slot C.obj := by rw [sEq, B.read_slot]
          have anns : B.ann s = B.ann C.obj := by rw [sEq, B.read_ann]
          have out : B.readOut (helpee j K.pos) (K.count (helpee j K.pos)) r =
              B.ann C.obj (helpee j K.pos) (K.count (helpee j K.pos)) := by rw [rEq, B.read_out]
          have nxt : (universal B s₀).next j (.read op K) r =
              .claim op K (proposalOf (B.ann C.obj) j op K) := by
            simp only [universal, proposalOf, out]
          show AStep _ _ _ (B.slot s) (B.ann s) _
          rw [uloc_update, slots, anns, toU_busy, nxt]
          exact AStep.read hU
      | claim op K p =>
          have ha : B.claim K.pos p = a := by simpa [universal] using hm
          subst ha
          have anns : B.ann s = B.ann C.obj := by rw [sEq, B.claim_ann]
          have slots : B.slot s = Function.update (B.slot C.obj) K.pos
              (some ((B.slot C.obj K.pos).getD p)) := by rw [sEq, B.claim_slot]
          have nxt : (universal B s₀).next j (.claim op K p) r = .learn op K p := rfl
          show AStep _ _ _ (B.slot s) (B.ann s) _
          rw [uloc_update, anns, toU_busy, nxt]
          cases hk : B.slot C.obj K.pos with
          | some w =>
              have slots' : B.slot s = B.slot C.obj := by
                rw [slots, hk]; simp only [Option.getD_some]; rw [← hk, Function.update_eq_self]
              rw [slots']
              exact AStep.claimOld hU hk
          | none =>
              have slots' : B.slot s = Function.update (B.slot C.obj) K.pos (some p) := by
                rw [slots, hk]; rfl
              rw [slots']
              exact AStep.claimNew hU hk
      | learn op K p =>
          have ha : B.learn K.pos p = a := by simpa [universal] using hm
          subst ha
          have lt : K.pos < D := inv.learnLt j op K p hU
          obtain ⟨e', hw⟩ : ∃ e', B.slot C.obj K.pos = some e' := by
            cases hk : B.slot C.obj K.pos with
            | none => have := (inv.decided K.pos).mpr lt; rw [hk] at this; cases this
            | some w => exact ⟨w, rfl⟩
          have slots : B.slot s = B.slot C.obj := by rw [sEq]; exact B.learn_slot _ _ _ _ hw
          have anns : B.ann s = B.ann C.obj := by rw [sEq]; exact B.learn_ann _ _ _ _ hw
          have out : B.learned K.pos r p = e' := by rw [rEq]; exact B.learn_out _ _ _ _ hw
          have nxt : (universal B s₀).next j (.learn op K p) r = afterLearn j op K e' := by
            simp only [universal, out]
          show AStep _ _ _ (B.slot s) (B.ann s) _
          rw [uloc_update, slots, anns, toU_busy, nxt]
          exact AStep.learn hU hw
      | done r' K => simp [universal] at hm
  | @wait j w a h hm never =>
      exact absurd rfl (never (X.apply C.obj a).1 (X.apply C.obj a).2)
  | @ret j w r m h hm =>
      have hU : uloc C j = .busy w := by simp [uloc, h, toU]
      cases w with
      | done r' K =>
          simp only [universal] at hm
          cases hm
          rw [uloc_update]
          exact AStep.ret hU
      | announce op K => simp [universal] at hm
      | read op K => simp [universal] at hm
      | claim op K p => simp [universal] at hm
      | learn op K p => simp [universal] at hm
  | @rest j m h => exact AStep.rest

end Concrete

section Track

variable {s₀ : Y.State}

/-- Process `j` is **on track** towards place `k₀`: it is about to return; or it has announced `op`
from a position at most `k₀`, and either `op` is placed between its position and `k₀`, or `op` is
not placed and `k₀` is safe for it. -/
def OnTrack (s₀ : Y.State) (L : ℕ → Option (Entry n Y.Op)) (D : ℕ) (loc : Fin n → UStatus n Y)
    (j : Fin n) (k₀ : ℕ) : Prop :=
  (∃ r K, loc j = .busy (.done r K)) ∨
    ∃ op K, announcedOf (loc j) = some (op, K) ∧ K.pos ≤ k₀ ∧
      ((∃ s, K.pos ≤ s ∧ s ≤ k₀ ∧ s < D ∧ L s = some (j, op)) ∨
        (logCount s₀ L D j = K.count j ∧ Safe D loc j op k₀))

variable {L L' : ℕ → Option (Entry n Y.Op)} {An An' : Fin n → ℕ → Option Y.Op} {D D' : ℕ}
  {loc loc' : Fin n → UStatus n Y} {j : Fin n} {k₀ : ℕ}

/-- Being on track survives a step that changes neither the log nor `j`'s announcement and adds no
proposer. -/
theorem OnTrack.frame (track : OnTrack s₀ L D loc j k₀)
    (ann : announcedOf (loc' j) = announcedOf (loc j))
    (done : ∀ r K, loc j = .busy (.done r K) → loc' j = loc j)
    (sub : ∀ r K p, claimOf (loc' r) = some (K, p) → claimOf (loc r) = some (K, p)) :
    OnTrack s₀ L D loc' j k₀ := by
  rcases track with ⟨r, K, h⟩ | ⟨op, K, ha, hk, (thr | ⟨hc, hm, hD, hcl⟩)⟩
  · exact Or.inl ⟨r, K, by rw [done r K h]; exact h⟩
  · exact Or.inr ⟨op, K, by rw [ann]; exact ha, hk, Or.inl thr⟩
  · exact Or.inr ⟨op, K, by rw [ann]; exact ha, hk,
      Or.inr ⟨hc, hm, hD, fun r K' p h hp => hcl r K' p (sub r K' p h) hp⟩⟩

theorem OnTrack.busy (track : OnTrack s₀ L D loc j k₀) : ∃ w, loc j = .busy w := by
  rcases track with ⟨r, K, h⟩ | ⟨op, K, ha, -⟩
  · exact ⟨_, h⟩
  · revert ha; cases loc j with
    | idle K' => simp [announcedOf]
    | busy w => intro _; exact ⟨w, rfl⟩

/-- **Being on track survives every step**, as long as `j` stays busy. This is where helping is
used: a proposer for the safe place reads `j`'s announcement and proposes `j`'s operation. -/
theorem OnTrack.astep (inv : Inv s₀ L An D loc) (inv' : Inv s₀ L' An' D' loc')
    (track : OnTrack s₀ L D loc j k₀) (step : AStep L An loc L' An' loc')
    (busy : ∃ w, loc' j = .busy w) : OnTrack s₀ L' D' loc' j k₀ := by
  obtain ⟨wj, hwj⟩ := track.busy
  cases step with
  | invoke op h =>
      rename_i q K
      obtain rfl := (inv.decided_eq inv')
      have ne : q ≠ j := by rintro rfl; rw [h] at hwj; cases hwj
      refine track.frame (by rw [Function.update_of_ne (Ne.symm ne)])
        (fun _ _ _ => Function.update_of_ne (Ne.symm ne) _ _) (fun r K' p hr => ?_)
      by_cases hrq : r = q
      · subst hrq; simp [claimOf] at hr
      · rwa [Function.update_of_ne hrq] at hr
  | announce h self above other =>
      rename_i q op K
      obtain rfl := (inv.decided_eq inv')
      have ne : q ≠ j := by
        rintro rfl
        rcases track with ⟨r, K', h'⟩ | ⟨op', K', ha, -⟩
        · rw [h] at h'; cases h'
        · rw [h] at ha; cases ha
      refine track.frame (by rw [Function.update_of_ne (Ne.symm ne)])
        (fun _ _ _ => Function.update_of_ne (Ne.symm ne) _ _) (fun r K' p hr => ?_)
      by_cases hrq : r = q
      · subst hrq; simp [claimOf] at hr
      · rwa [Function.update_of_ne hrq] at hr
  | read h =>
      rename_i q op K
      obtain rfl := (inv.decided_eq inv')
      have seenQ : K = logSeen s₀ L K.pos := by have := inv.seen q; rw [h] at this; exact this
      have leQ : K.pos ≤ D := by have := inv.seenLe q; rw [h] at this; exact this
      have annKeep : announcedOf (Function.update loc q (.busy (.claim op K (proposalOf An q op K))) j)
          = announcedOf (loc j) := by
        by_cases hjq : j = q
        · subst hjq; simp [h, announcedOf]
        · rw [Function.update_of_ne hjq]
      rcases track with ⟨r, K', h'⟩ | ⟨op', K', ha, hk, (thr | ⟨hc, hm, hD, hcl⟩)⟩
      · have ne : j ≠ q := by rintro rfl; rw [h] at h'; cases h'
        exact Or.inl ⟨r, K', by rw [Function.update_of_ne ne]; exact h'⟩
      · exact Or.inr ⟨op', K', by rw [annKeep]; exact ha, hk, Or.inl thr⟩
      · refine Or.inr ⟨op', K', by rw [annKeep]; exact ha, hk, Or.inr ⟨hc, hm, hD, ?_⟩⟩
        intro r K'' p'' hr hpos
        by_cases hrq : r = q
        · subst hrq
          simp only [Function.update_self, claimOf, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          -- the proposer reads `j`'s announcement for place `k₀ = D`
          have kD : K.pos = D := by omega
          have hK : K = logSeen s₀ L D := by rw [← kD]; exact seenQ
          have who : helpee r K.pos = j := Fin.ext (by rw [helpee_val, hpos, hm])
          have count : K.count j = K'.count j := by
            have : K.count j = logCount s₀ L D j := by rw [hK]
            rw [this, hc]
          have found : An j (K.count j) = some op' := by
            rw [count]; exact (inv.loud j op' K' ha).1
          simp only [proposalOf, who, found, propose]
        · rw [Function.update_of_ne hrq] at hr; exact hcl r K'' p'' hr hpos
  | claimOld h hw =>
      rename_i q op K p w
      obtain rfl := (inv.decided_eq inv')
      refine track.frame ?_ ?_ ?_
      · by_cases hjq : j = q
        · subst hjq; simp [h, announcedOf]
        · rw [Function.update_of_ne hjq]
      · intro r K' hd
        have ne : j ≠ q := by rintro rfl; rw [h] at hd; cases hd
        exact Function.update_of_ne ne _ _
      · intro r K' p' hr
        by_cases hrq : r = q
        · subst hrq; simp [claimOf] at hr
        · rwa [Function.update_of_ne hrq] at hr
  | claimNew h hn =>
      rename_i q op K p
      have leQ : K.pos ≤ D := by have := inv.seenLe q; rw [h] at this; exact this
      have hpos : K.pos = D := by
        by_contra ne
        have := (inv.decided K.pos).mpr (by omega)
        rw [hn] at this; cases this
      subst hpos
      have hD' : D' = K.pos + 1 := by
        have one := (inv'.decided K.pos).mp (by simp)
        have two : ¬ K.pos + 1 < D' := by
          intro lt
          have := (inv'.decided (K.pos + 1)).mpr lt
          rw [Function.update_of_ne (by omega)] at this
          rw [inv.decided] at this; omega
        omega
      subst hD'
      obtain ⟨Ko, ho, hco⟩ := inv.proposal q K p (by rw [h]; rfl) rfl
      have annKeep : announcedOf (Function.update loc q (.busy (.learn op K p)) j)
          = announcedOf (loc j) := by
        by_cases hjq : j = q
        · subst hjq; simp [h, announcedOf]
        · rw [Function.update_of_ne hjq]
      have claimSub : ∀ r K' p', claimOf (Function.update loc q (.busy (.learn op K p)) r) =
          some (K', p') → claimOf (loc r) = some (K', p') := by
        intro r K' p' hr
        by_cases hrq : r = q
        · subst hrq; simp [claimOf] at hr
        · rwa [Function.update_of_ne hrq] at hr
      rcases track with ⟨r, K', h'⟩ | ⟨op', K', ha, hk, (⟨s', hs, hsk, hsD, hL⟩ | ⟨hc, hm, hD, hcl⟩)⟩
      · have ne : j ≠ q := by rintro rfl; rw [h] at h'; cases h'
        exact Or.inl ⟨r, K', by rw [Function.update_of_ne ne]; exact h'⟩
      · refine Or.inr ⟨op', K', by rw [annKeep]; exact ha, hk, Or.inl ⟨s', hs, hsk, by omega, ?_⟩⟩
        rw [Function.update_of_ne (by omega)]; exact hL
      · by_cases own : p.1 = j
        · -- `j`'s operation is placed now, at place `D ≤ k₀`
          have pj : p = (j, op') := by
            rw [own, ha] at ho; cases ho
            exact Prod.ext own rfl
          have leJ : K'.pos ≤ K.pos := by
            have := inv.seenLe j; rwa [seenOf_of_announced ha] at this
          refine Or.inr ⟨op', K', by rw [annKeep]; exact ha, hk,
            Or.inl ⟨K.pos, leJ, hD, by omega, ?_⟩⟩
          rw [Function.update_self, pj]
        · have kD : K.pos ≠ k₀ := by
            intro eq
            exact own (by rw [hcl q K p (by rw [h]; rfl) eq])
          refine Or.inr ⟨op', K', by rw [annKeep]; exact ha, hk, Or.inr ⟨?_, hm, by omega,
            fun r K'' p'' hr hpos => hcl r K'' p'' (claimSub r K'' p'' hr) hpos⟩⟩
          show (logSeen s₀ (Function.update L K.pos (some p)) (K.pos + 1)).count j = K'.count j
          rw [logSeen_succ_some (e := p) (by simp), logSeen_congr (L' := L) (fun i hi => by
            rw [Function.update_of_ne (by omega)]), count_add_other _ own]
          exact hc
  | learn h he =>
      rename_i q op K p e
      obtain rfl := (inv.decided_eq inv')
      by_cases hjq : j = q
      · subst hjq
        have annJ : announcedOf (loc j) = some (op, K) := by rw [h]; rfl
        have seenJ : K = logSeen s₀ L K.pos := by have := inv.seen j; rw [h] at this; exact this
        have lt : K.pos < D := inv.learnLt j op K p h
        obtain ⟨-, -, leJ, entriesJ⟩ := inv.loud j op K annJ
        have claimSame : ∀ r K' p', claimOf (Function.update loc j
            (.busy (afterLearn j op K e)) r) = some (K', p') → claimOf (loc r) = some (K', p') := by
          intro r K' p' hr
          by_cases hrj : r = j
          · subst hrj
            simp only [Function.update_self, afterLearn] at hr
            split_ifs at hr <;> simp [claimOf] at hr
          · rwa [Function.update_of_ne hrj] at hr
        rcases track with ⟨r, K', h'⟩ | ⟨op', K', ha, hk, rest⟩
        · rw [h] at h'; cases h'
        · rw [annJ] at ha; cases ha
          by_cases owner : e.1 = j
          · left
            exact ⟨(Y.apply K.state e.2).2, K.add e,
              by simp only [Function.update_self, afterLearn, if_pos owner]⟩
          · have annNew : announcedOf (Function.update loc j (.busy (afterLearn j op K e)) j) =
                some (op, K.add e) := by
              simp only [Function.update_self, afterLearn, if_neg owner]; rfl
            right
            rcases rest with ⟨s', hs, hsk, hsD, hL⟩ | ⟨hc, hm, hD, hcl⟩
            · have ne : s' ≠ K.pos := by
                rintro rfl; rw [he] at hL; cases hL; exact owner rfl
              refine ⟨op, K.add e, annNew, by simp [Seen.add]; omega,
                Or.inl ⟨s', by simp [Seen.add]; omega, hsk, hsD, hL⟩⟩
            · refine ⟨op, K.add e, annNew, by simp [Seen.add]; omega,
                Or.inr ⟨by rw [count_add_other _ owner]; exact hc, hm, hD,
                  fun r K'' p'' hr hpos => hcl r K'' p'' (claimSame r K'' p'' hr) hpos⟩⟩
      · refine track.frame (by rw [Function.update_of_ne hjq])
          (fun _ _ _ => Function.update_of_ne hjq _ _) (fun r K' p' hr => ?_)
        by_cases hrq : r = q
        · subst hrq
          simp only [Function.update_self, afterLearn] at hr
          split_ifs at hr <;> simp [claimOf] at hr
        · rwa [Function.update_of_ne hrq] at hr
  | ret h =>
      rename_i q r K
      obtain rfl := (inv.decided_eq inv')
      have ne : j ≠ q := by
        rintro rfl
        obtain ⟨w, hw⟩ := busy
        simp at hw
      refine track.frame (by rw [Function.update_of_ne ne])
        (fun _ _ _ => Function.update_of_ne ne _ _) (fun r' K' p' hr => ?_)
      by_cases hrq : r' = q
      · subst hrq; simp [claimOf] at hr
      · rwa [Function.update_of_ne hrq] at hr
  | rest =>
      obtain rfl := (inv.decided_eq inv')
      exact track

/-- How far a process is from returning, counted towards place `k₀`. -/
def rank (k₀ : ℕ) : UStatus n Y → ℕ
  | .busy (.read _ K) => 4 * (k₀ + 1 - K.pos) + 3
  | .busy (.claim _ K _) => 4 * (k₀ + 1 - K.pos) + 2
  | .busy (.learn _ K _) => 4 * (k₀ + 1 - K.pos) + 1
  | _ => 0

end Track

/-- A busy process keeps its status until it is moved: no one else changes it, and it cannot be
called while busy. -/
theorem _root_.Mettapedia.GSLT.Coordination.ConsensusNumbers.Implementation.loc_until_move
    {X' : ObjectType} {I : Implementation X' Y n} {cs : ℕ → Choice n Y.Op} {c : ℕ → I.Config}
    (exec : I.Execution cs c) {j : Fin n} {m : ℕ} (busy : I.Busy (c m) j) :
    ∀ d, (∀ d', d' < d → cs (m + d') ≠ .move j) → (c (m + d)).loc j = (c m).loc j := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
      intro none
      have before := ih (fun d' lt => none d' (by omega))
      obtain ⟨e, step⟩ := exec (m + d)
      have notMove := none d (by omega)
      rw [← add_assoc]
      by_cases who : j = (cs (m + d)).who
      · cases hcs : cs (m + d) with
        | invoke i op =>
            rw [hcs] at step who
            simp only [Choice.who] at who
            subst who
            obtain ⟨mem, hmem⟩ := Implementation.Step.idle_of_invoke step
            obtain ⟨w, hw⟩ := busy
            rw [before, hw] at hmem; cases hmem
        | move i =>
            rw [hcs] at who notMove
            simp only [Choice.who] at who
            subst who
            exact absurd rfl notMove
      · rw [Implementation.Step.loc_of_ne step who, before]

section WaitFree

variable {s₀ : Y.State} {X : DetObject} {B : Board X n Y.Op}

theorem invariant_along {cs : ℕ → Choice n Y.Op} {c : ℕ → (universal B s₀).Config}
    (start : c 0 = (universal B s₀).initial) (exec : (universal B s₀).Execution cs c) :
    ∀ k, ∃ D, Inv s₀ (B.slot (c k).obj) (B.ann (c k).obj) D (uloc (c k)) := by
  intro k
  induction k with
  | zero =>
      obtain ⟨D₀, inv₀, -, -⟩ := (rel_initial : Rel (B := B) (s₀ := s₀) (universal B s₀).initial
        (atomic Y s₀ n).initial)
      exact ⟨D₀, by rw [start]; exact inv₀⟩
  | succ k ih =>
      obtain ⟨D, inv⟩ := ih
      obtain ⟨e, step⟩ := exec k
      exact inv.astep (concrete_astep inv step)

/-- An announced process is on track towards some place. -/
theorem Inv.exists_track {L : ℕ → Option (Entry n Y.Op)} {An : Fin n → ℕ → Option Y.Op} {D : ℕ}
    {loc : Fin n → UStatus n Y} (inv : Inv s₀ L An D loc) {j : Fin n} {op : Y.Op} {K : Seen n Y}
    (ha : announcedOf (loc j) = some (op, K)) : ∃ k₀, OnTrack s₀ L D loc j k₀ := by
  obtain ⟨-, -, le, entries⟩ := inv.loud j op K ha
  have ge := inv.count_ge ha
  have leJ : K.pos ≤ D := by have := inv.seenLe j; rwa [seenOf_of_announced ha] at this
  have seenJ : K = logSeen s₀ L K.pos := by
    have := inv.seen j; rwa [seenOf_of_announced ha] at this
  by_cases placed : ∃ s e, K.pos ≤ s ∧ s < D ∧ L s = some e ∧ e.1 = j
  · obtain ⟨s, e, hs, hsD, hL, hown⟩ := placed
    have eop : e.2 = op := entries s e hs hsD hL hown
    refine ⟨s, Or.inr ⟨op, K, ha, hs, Or.inl ⟨s, hs, le_rfl, hsD, ?_⟩⟩⟩
    rw [hL]; exact congrArg some (Prod.ext hown eop)
  · push Not at placed
    have eq := count_eq_of_not_owned (s₀ := s₀) leJ (fun s e h1 h2 h3 => placed s e h1 h2 h3)
    rw [← seenJ] at eq
    obtain ⟨k, hk⟩ := inv.helped j op K ha eq
    exact ⟨k, Or.inr ⟨op, K, ha, by have := hk.2.1; omega, Or.inr ⟨eq, hk⟩⟩⟩

/-- Each move of an announced process brings it nearer to returning. -/
theorem rank_next_lt {k₀ : ℕ} {j : Fin n} {w : Stage n Y} {op : Y.Op} {K : Seen n Y}
    (ha : announcedOf (UStatus.busy w) = some (op, K)) (hk : K.pos ≤ k₀) (r : X.Res) :
    rank k₀ (UStatus.busy ((universal B s₀).next j w r)) < rank k₀ (UStatus.busy w) := by
  cases w with
  | announce op' K' => simp [announcedOf] at ha
  | read op' K' =>
      show rank k₀ (.busy (.claim _ _ _)) < _
      simp [rank]
  | claim op' K' p =>
      show rank k₀ (.busy (.learn _ _ _)) < _
      simp [rank]
  | learn op' K' p =>
      simp only [announcedOf, Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      show rank k₀ (.busy (afterLearn j _ _ (B.learned _ r p))) < _
      unfold afterLearn
      split_ifs
      · simp [rank]
      · simp [rank, Seen.add]; omega
  | done r' K' => simp [announcedOf] at ha

/-- **The universal construction is wait-free.** -/
theorem universal_waitFree (B : Board X n Y.Op) (s₀ : Y.State) : (universal B s₀).WaitFree := by
  intro cs c start exec j m busy often
  have invs := invariant_along start exec
  -- a time `m₁ ≥ m` at which `j` is busy and has announced, or is about to return
  obtain ⟨m₁, hm₁, k₀, track₁⟩ : ∃ m₁, m ≤ m₁ ∧ ∃ k₀, ∃ D, Inv s₀ (B.slot (c m₁).obj)
      (B.ann (c m₁).obj) D (uloc (c m₁)) ∧ OnTrack s₀ (B.slot (c m₁).obj) D (uloc (c m₁)) j k₀ := by
    have fromTime : ∀ t, (∃ w, (c t).loc j = .busy w ∧ ∀ op K, w ≠ .announce op K) →
        ∃ k₀, ∃ D, Inv s₀ (B.slot (c t).obj) (B.ann (c t).obj) D (uloc (c t)) ∧
          OnTrack s₀ (B.slot (c t).obj) D (uloc (c t)) j k₀ := by
      rintro t ⟨w, hw, notAnn⟩
      obtain ⟨D, inv⟩ := invs t
      have hU : uloc (c t) j = .busy w := by simp [uloc, hw, toU]
      cases w with
      | announce op K => exact absurd rfl (notAnn op K)
      | read op K =>
          obtain ⟨k₀, tr⟩ := inv.exists_track (j := j) (op := op) (K := K) (by rw [hU]; rfl)
          exact ⟨k₀, D, inv, tr⟩
      | claim op K p =>
          obtain ⟨k₀, tr⟩ := inv.exists_track (j := j) (op := op) (K := K) (by rw [hU]; rfl)
          exact ⟨k₀, D, inv, tr⟩
      | learn op K p =>
          obtain ⟨k₀, tr⟩ := inv.exists_track (j := j) (op := op) (K := K) (by rw [hU]; rfl)
          exact ⟨k₀, D, inv, tr⟩
      | done r K => exact ⟨0, D, inv, Or.inl ⟨r, K, hU⟩⟩
    obtain ⟨w, hw⟩ := busy
    by_cases ann : ∃ op K, w = .announce op K
    · obtain ⟨op, K, rfl⟩ := ann
      -- wait for `j`'s next move: it announces
      classical
      have ex : ∃ d, cs (m + d) = .move j := by
        obtain ⟨k, hk, hc⟩ := often m
        exact ⟨k - m, by rw [Nat.add_sub_cancel' hk]; exact hc⟩
      have hd := Nat.find_spec ex
      have same := Implementation.loc_until_move exec ⟨_, hw⟩ (Nat.find ex)
        (fun d' lt => Nat.find_min ex lt)
      rw [hw] at same
      obtain ⟨e, step⟩ := exec (m + Nat.find ex)
      rw [hd] at step
      generalize hnext : c (m + Nat.find ex + 1) = C' at step
      have announced : C'.loc j = .busy (.read op K) := by
        cases step with
        | @call _ w a s r h hm hf =>
            rw [same] at h; cases h
            simp [universal]
        | @wait _ w a h hm never =>
            exact absurd rfl (never (X.apply _ a).1 (X.apply _ a).2)
        | @ret _ w r m' h hm =>
            rw [same] at h; cases h; simp [universal] at hm
        | @rest _ m' h => rw [same] at h; cases h
      exact ⟨m + Nat.find ex + 1, by omega,
        fromTime _ ⟨_, by rw [hnext]; exact announced, fun op' K' h => by cases h⟩⟩
    · push Not at ann
      exact ⟨m, le_rfl, fromTime m ⟨w, hw, ann⟩⟩
  obtain ⟨D₁, inv₁, tr₁⟩ := track₁
  have busyOf : ∀ C : (universal B s₀).Config, (universal B s₀).Busy C j →
      ∃ w, uloc C j = .busy w := by
    rintro C ⟨w, hw⟩; exact ⟨w, by simp [uloc, hw, toU]⟩
  obtain ⟨k, hk, idle⟩ := Implementation.returns_of_measure exec
    (fun C => ∃ D, Inv s₀ (B.slot C.obj) (B.ann C.obj) D (uloc C) ∧
      OnTrack s₀ (B.slot C.obj) D (uloc C) j k₀)
    (fun C => rank k₀ (uloc C j)) ⟨D₁, inv₁, tr₁⟩
    (by
      rintro C ch e C' ⟨D, inv, tr⟩ step busy'
      have astep := concrete_astep inv step
      obtain ⟨D', inv'⟩ := inv.astep astep
      exact ⟨D', inv', tr.astep inv inv' astep (busyOf C' busy')⟩)
    (by
      rintro C ch e C' ⟨D, inv, tr⟩ step busy'
      by_cases who : j = ch.who
      · obtain ⟨wj, hwj⟩ := tr.busy
        cases step with
        | @invoke i mem op h =>
            simp only [Choice.who] at who; subst who
            have : uloc C j = .idle mem := by simp [uloc, h, toU]
            rw [hwj] at this; cases this
        | @call i w a s r h hm hf =>
            simp only [Choice.who] at who; subst who
            have hU : uloc C j = .busy w := by simp [uloc, h, toU]
            rcases tr with ⟨r', K, hd⟩ | ⟨op, K, ha, hk, -⟩
            · rw [hU] at hd; cases hd; simp [universal] at hm
            · rw [hU] at ha
              show rank k₀ (uloc ⟨s, Function.update C.loc j _⟩ j) ≤ rank k₀ (uloc C j)
              rw [uloc_update, Function.update_self, toU_busy, hU]
              exact (rank_next_lt ha hk r).le
        | wait _ _ _ => exact le_rfl
        | @ret i w r m' h hm =>
            obtain ⟨w', hw'⟩ := busy'
            simp only [Choice.who] at who; subst who
            simp at hw'
        | rest _ => exact le_rfl
      · have := Implementation.Step.loc_of_ne step who
        simp only [uloc, this, le_refl])
    (by
      rintro C e C' ⟨D, inv, tr⟩ step busy'
      have hU' := busyOf C' busy'
      cases step with
      | @call i w a s r h hm hf =>
          have hU : uloc C j = .busy w := by simp [uloc, h, toU]
          rcases tr with ⟨r', K, hd⟩ | ⟨op, K, ha, hk, -⟩
          · rw [hU] at hd; cases hd; simp [universal] at hm
          · rw [hU] at ha
            show rank k₀ (uloc ⟨s, Function.update C.loc j _⟩ j) < rank k₀ (uloc C j)
            rw [uloc_update, Function.update_self, toU_busy, hU]
            exact rank_next_lt ha hk r
      | @wait i w a h hm never => exact absurd rfl (never (X.apply _ a).1 (X.apply _ a).2)
      | @ret i w r m' h hm =>
          obtain ⟨w', hw'⟩ := hU'
          simp [uloc, toU] at hw'
      | @rest i m' h =>
          obtain ⟨wj, hwj⟩ := tr.busy
          have : uloc C j = .idle m' := by simp [uloc, h, toU]
          rw [hwj] at this; cases this)
    often
  exact ⟨k, by omega, idle⟩

end WaitFree

end Universal

end Mettapedia.GSLT.Coordination.ConsensusNumbers
