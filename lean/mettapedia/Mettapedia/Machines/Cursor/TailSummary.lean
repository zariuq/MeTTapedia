import Mettapedia.Machines.Cursor.SuffixSummary

/-!
# The summary a retained tail inherits

An expression's summary is folded from its children.  Each flag bit is either
a disjunction over the children (a child's property the expression inherits)
or a conjunction (a property every child must have).  The variables are folded
by the join that keeps the one variable all occurrences share, if there is
one.  Some heads adjust the folded bits afterwards.

The tail of an expression drops its first child.  When that child is neutral,
holding every bit's unit and no variable, and is no adjusting head, the tail's
summary is the expression's, adjusted for the tail's own head: taking the tail
needs no pass over its children.  A child that is not neutral leaves the tail
undetermined by the expression (see the controls), and the tail then takes its
own fold, or its entry in a suffix cache prepared in one pass.

A summary bit that depends on where the expression is allocated, as the
arena-closure bit does, is folded at one allocation.  A tail allocated
elsewhere cannot inherit it (see the controls).  Sharing a parent's storage is
sound when the storage is released no earlier than the tail: in the tail's own
arena, where it was allocated first, or in storage that is never released.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.TailSummary

/-! ## One bit -/

/-- How a bit folds: `any` by disjunction from `false`, `all` by conjunction
from `true`. -/
inductive Mode
  | any
  | all
  deriving DecidableEq, Repr

namespace Mode

def unit : Mode → Bool
  | .any => false
  | .all => true

def step : Mode → Bool → Bool → Bool
  | .any, x, rest => x || rest
  | .all, x, rest => x && rest

theorem step_unit (m : Mode) (rest : Bool) : m.step m.unit rest = rest := by
  cases m <;> cases rest <;> rfl

end Mode

def bitFold (m : Mode) (xs : List Bool) : Bool := xs.foldr m.step m.unit

theorem bitFold_cons (m : Mode) (x : Bool) (xs : List Bool) :
    bitFold m (x :: xs) = m.step x (bitFold m xs) := rfl

/-- A child holding the bit's unit leaves the bit as the rest folds it. -/
theorem bitFold_neutral (m : Mode) (x : Bool) (xs : List Bool)
    (neutral : x = m.unit) :
    bitFold m (x :: xs) = bitFold m xs := by
  rw [bitFold_cons, neutral, Mode.step_unit]

/-- CeTTa folds a bit left to right; both operations are associative and
commutative, so the order does not change the bit. -/
theorem bitFold_eq_foldl (m : Mode) (xs : List Bool) :
    xs.foldl (fun rest x => m.step x rest) m.unit = bitFold m xs := by
  suffices general : ∀ (start : Bool),
      xs.foldl (fun rest x => m.step x rest) start = m.step start (bitFold m xs) by
    rw [general, Mode.step_unit]
  induction xs with
  | nil => intro start; cases m <;> cases start <;> rfl
  | cons x xs ih =>
      intro start
      rw [List.foldl_cons, ih, bitFold_cons]
      cases m <;> cases start <;> cases x <;> simp [Mode.step]

/-- A conjunction bit is false exactly when some child lacks it, so a scan may
stop at the first such child. -/
theorem bitFold_all_eq_false_iff (xs : List Bool) :
    bitFold .all xs = false ↔ false ∈ xs := by
  induction xs with
  | nil => simp [bitFold, Mode.unit]
  | cons x xs ih =>
      rw [bitFold_cons]
      cases x <;> simp [Mode.step, ih]

/-- A disjunction bit is true exactly when some child has it. -/
theorem bitFold_any_eq_true_iff (xs : List Bool) :
    bitFold .any xs = true ↔ true ∈ xs := by
  induction xs with
  | nil => simp [bitFold, Mode.unit]
  | cons x xs ih =>
      rw [bitFold_cons]
      cases x <;> simp [Mode.step, ih]

/-- A scan that stops at the first child lacking a conjunction bit computes
the bit: it answers `false` at the first counterexample and `true` when there
is none. -/
def scanAll : List Bool → Bool
  | [] => true
  | false :: _ => false
  | true :: rest => scanAll rest

theorem scanAll_eq_bitFold (xs : List Bool) : scanAll xs = bitFold .all xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [scanAll, bitFold_cons, Mode.step, ih]

/-- The scan examines the children up to and including the first
counterexample, or all of them. -/
def scanAllCost : List Bool → ℕ
  | [] => 0
  | false :: _ => 1
  | true :: rest => scanAllCost rest + 1

theorem scanAllCost_le_length (xs : List Bool) : scanAllCost xs ≤ xs.length := by
  induction xs with
  | nil => simp [scanAllCost]
  | cons x xs ih =>
      cases x
      · simp [scanAllCost]
      · simp only [scanAllCost, List.length_cons]
        omega

/-- A walk by suffixes rescans the bit only when a counterexample departs,
from the next child on. -/
def walkScanCost : List Bool → ℕ
  | [] => 0
  | false :: rest => scanAllCost rest + walkScanCost rest
  | true :: rest => walkScanCost rest

/-- Each rescan stops at the next counterexample, so the rescans of a whole
walk examine at most one child more than the list holds. -/
theorem walkScanCost_add_scan_le (xs : List Bool) :
    walkScanCost xs + scanAllCost xs ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [walkScanCost, scanAllCost]
  | cons x xs ih => cases x <;> simp [walkScanCost, scanAllCost] <;> omega

theorem walkScanCost_le (xs : List Bool) : walkScanCost xs ≤ xs.length + 1 := by
  have := walkScanCost_add_scan_le xs
  omega

/-! ## A word of bits -/

variable {n : ℕ}

/-- The fold of every bit of a word, each by its own mode. -/
def wordFold (modes : Fin n → Mode) (children : List (Fin n → Bool)) :
    Fin n → Bool :=
  fun b => bitFold (modes b) (children.map (· b))

/-- A child is neutral when it holds every bit's unit. -/
def Neutral (modes : Fin n → Mode) (child : Fin n → Bool) : Prop :=
  ∀ b, child b = (modes b).unit

theorem wordFold_neutral (modes : Fin n → Mode) (child : Fin n → Bool)
    (rest : List (Fin n → Bool)) (neutral : Neutral modes child) :
    wordFold modes (child :: rest) = wordFold modes rest := by
  funext b
  exact bitFold_neutral (modes b) (child b) (rest.map (· b)) (neutral b)

/-- The word fold is a right fold, so a suffix cache prepares every tail's
word in one pass. -/
def wordStep (modes : Fin n → Mode) (child : Fin n → Bool) (rest : Fin n → Bool) :
    Fin n → Bool :=
  fun b => (modes b).step (child b) (rest b)

def wordUnit (modes : Fin n → Mode) : Fin n → Bool := fun b => (modes b).unit

theorem wordFold_eq_foldr (modes : Fin n → Mode) (children : List (Fin n → Bool)) :
    wordFold modes children = children.foldr (wordStep modes) (wordUnit modes) := by
  induction children with
  | nil => rfl
  | cons child rest ih =>
      funext b
      rw [List.foldr_cons, ← ih]
      rfl

/-- The general case: every tail's word is its entry in the suffix cache. -/
theorem tail_word_from_cache (modes : Fin n → Mode) (children : List (Fin n → Bool))
    (offset : ℕ) (within : offset ≤ children.length) :
    (SuffixSummary.cache (wordStep modes) (wordUnit modes) children)[offset]? =
      some (wordFold modes (children.drop offset)) := by
  rw [SuffixSummary.cache_at (wordStep modes) (wordUnit modes) children offset within,
    wordFold_eq_foldr]

/-! ## Head adjustments -/

/-- An expression's summary: the fold of its children's words, adjusted by its
head.  The empty expression has no head. -/
def summary {Child : Type} (word : Child → Fin n → Bool)
    (adjust : Child → (Fin n → Bool) → (Fin n → Bool)) (modes : Fin n → Mode) :
    List Child → Fin n → Bool
  | [] => wordFold modes []
  | head :: rest => adjust head (wordFold modes ((head :: rest).map word))

/-- The tail's summary from the parent's: the departed child is neutral and
adjusts nothing, so the parent's summary is the tail's fold, which the tail's
own head then adjusts. -/
theorem summary_tail {Child : Type} (word : Child → Fin n → Bool)
    (adjust : Child → (Fin n → Bool) → (Fin n → Bool)) (modes : Fin n → Mode)
    (departed : Child) (rest : List Child)
    (neutral : Neutral modes (word departed))
    (plain : adjust departed = id) :
    summary word adjust modes rest =
      (match rest with
        | [] => id
        | head :: _ => adjust head)
        (summary word adjust modes (departed :: rest)) := by
  have parent : summary word adjust modes (departed :: rest) =
      wordFold modes (rest.map word) := by
    simp only [summary, plain, id, List.map_cons]
    exact wordFold_neutral modes (word departed) (rest.map word) neutral
  rw [parent]
  cases rest with
  | nil => rfl
  | cons head tail => rfl

/-- The summary of a list with one element prepended, from the list's own: when
the list's head adjusts nothing, its summary is its fold, the new element's
word steps onto that fold, and the new head adjusts the result.  A prepend
therefore needs no pass over the list. -/
theorem summary_prepend {Child : Type} (word : Child → Fin n → Bool)
    (adjust : Child → (Fin n → Bool) → (Fin n → Bool)) (modes : Fin n → Mode)
    (added : Child) (rest : List Child)
    (plain : ∀ first ∈ rest.head?, adjust first = id) :
    summary word adjust modes (added :: rest) =
      adjust added
        (wordStep modes (word added) (summary word adjust modes rest)) := by
  have folded : summary word adjust modes rest = wordFold modes (rest.map word) := by
    cases rest with
    | nil => rfl
    | cons first more =>
        simp only [summary, plain first rfl, id]
  rw [folded]
  simp only [summary, List.map_cons, wordFold_eq_foldr, List.foldr_cons]

/-! ## Variables -/

/-- The variables of an expression, as its summary keeps them: none, all
occurrences one variable, or more than one. -/
inductive Vars
  | none
  | one (v : ℕ)
  | many
  deriving DecidableEq, Repr

namespace Vars

def join : Vars → Vars → Vars
  | .none, y => y
  | .one v, .none => .one v
  | .one v, .one w => if v = w then .one v else .many
  | .one _, .many => .many
  | .many, _ => .many

theorem join_none (x : Vars) : join x .none = x := by
  cases x <;> rfl

end Vars

def varsFold (xs : List Vars) : Vars := xs.foldr Vars.join .none

/-- A child without variables leaves the tail's variables as the parent's. -/
theorem varsFold_neutral (xs : List Vars) :
    varsFold (.none :: xs) = varsFold xs := rfl

/-- A parent whose occurrences are one variable has a tail with that variable
or with none; which one is the tail's has-variables bit. -/
theorem varsFold_tail_of_one (x : Vars) (xs : List Vars) (v : ℕ)
    (parent : varsFold (x :: xs) = .one v) :
    varsFold xs = .none ∨ varsFold xs = .one v := by
  change Vars.join x (varsFold xs) = .one v at parent
  cases x with
  | none => exact Or.inr parent
  | one w =>
      cases rest : varsFold xs with
      | none => exact Or.inl rfl
      | one u =>
          rw [rest] at parent
          by_cases same : w = u
          · subst same
            simp [Vars.join] at parent
            exact Or.inr (by rw [parent])
          · simp [Vars.join, same] at parent
      | many =>
          rw [rest] at parent
          simp [Vars.join] at parent
  | many => simp [Vars.join] at parent

/-! ## Sharing a parent's storage -/

/-- Where storage lives: an arena, or storage that is never released. -/
inductive Home
  | arena (id : ℕ)
  | global
  deriving DecidableEq

/-- Releasing arena `r` releases storage at home `h`. -/
def releasedBy (r : ℕ) : Home → Prop
  | .arena id => id = r
  | .global => False

/-- A tail allocated in arena `here` may share storage at `storage` when the
storage is in that arena or never released. -/
def Shareable (here : ℕ) (storage : Home) : Prop :=
  storage = .arena here ∨ storage = .global

/-- Releasing the storage's arena releases the tail too. -/
theorem shared_storage_outlives (here r : ℕ) (storage : Home)
    (sharing : Shareable here storage) (released : releasedBy r storage) :
    releasedBy r (.arena here) := by
  rcases sharing with same | never
  · subst same; exact released
  · subst never; exact released.elim

/-- Within one arena, rolling back to a mark releases every allocation made at
or after it.  The parent's storage was allocated before the tail, so a
rollback that releases the storage releases the tail. -/
theorem rollback_releases_tail (mark storage tail : ℕ)
    (earlier : storage < tail) (released : mark ≤ storage) :
    mark ≤ tail :=
  le_of_lt (lt_of_le_of_lt released earlier)

/-! ## Controls -/

namespace Controls

/-- A departed child holding a disjunction bit leaves the tail's bit
undetermined: two parents with the bit set have tails that differ. -/
theorem departed_witness_leaves_tail_open :
    bitFold .any [true, true] = bitFold .any [true, false] ∧
      bitFold .any [true] ≠ bitFold .any [false] := by decide

/-- Likewise for a conjunction bit a departed child lacks. -/
theorem departed_counterexample_leaves_tail_open :
    bitFold .all [false, true] = bitFold .all [false, false] ∧
      bitFold .all [true] ≠ bitFold .all [false] := by decide

/-- A head's adjustment belongs to the expression it heads: the tail does not
inherit a bit the departed head set. -/
theorem departed_head_adjustment_is_not_inherited :
    let adjust : Bool → (Fin 1 → Bool) → (Fin 1 → Bool) :=
      fun head word => if head then (fun _ => true) else word
    summary (n := 1) (fun _ => fun _ => false) adjust (fun _ => .any) [true, false] 0 = true ∧
      summary (n := 1) (fun _ => fun _ => false) adjust (fun _ => .any) [false] 0 = false := by
  decide

/-- Two variables leave the tail open: the same parent summary, `many`, has
tails with one variable and with more than one. -/
theorem many_leaves_tail_open :
    varsFold [.one 1, .one 2] = varsFold [.one 1, .one 2, .one 3] ∧
      varsFold [.one 2] ≠ varsFold [.one 2, .one 3] := by decide

/-- A bit that depends on the allocation: a child is closed for an arena when
it lives there or is never released.  The same children fold differently at
two arenas, so a tail allocated in another arena cannot inherit the bit. -/
theorem allocation_bit_depends_on_the_arena :
    let closedAt : ℕ → Home → Bool := fun here home =>
      match home with
      | .arena id => id == here
      | .global => true
    bitFold .all ([Home.arena 1, .global].map (closedAt 1)) = true ∧
      bitFold .all ([Home.arena 1, .global].map (closedAt 2)) = false := by
  decide

/-- Storage in another arena is not shareable: releasing that arena releases
the storage and not the tail. -/
theorem other_arena_is_not_shareable :
    ¬ Shareable 1 (.arena 2) ∧ releasedBy 2 (.arena 2) ∧ ¬ releasedBy 2 (.arena 1) := by
  refine ⟨?_, rfl, ?_⟩
  · rintro (same | never)
    · exact absurd (Home.arena.inj same) (by decide)
    · exact Home.noConfusion never
  · intro same
    exact absurd (show (1 : ℕ) = 2 from same) (by decide)

end Controls

#print axioms bitFold_eq_foldl
#print axioms scanAll_eq_bitFold
#print axioms walkScanCost_le
#print axioms wordFold_neutral
#print axioms tail_word_from_cache
#print axioms summary_tail
#print axioms varsFold_tail_of_one
#print axioms shared_storage_outlives

end Mettapedia.Machines.Cursor.TailSummary
