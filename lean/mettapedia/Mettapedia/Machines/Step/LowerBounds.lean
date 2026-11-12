import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-!
# Lower bounds for the mechanisms of the step and the reader

Each bound is stated in a model that says what is counted, and each is met, up
to the constant given, by the mechanism the runtime uses.

**Questions.**  An algorithm that learns its input by yes/no questions about
single cells is a decision tree (`DTree`).  A cell whose flip changes the answer
is asked (`DTree.asks_of_sensitive`).

* `validation_asks_every_take`, `checkAll_asks`: to decide that every row a
  firing takes is still live, every one of those rows must be asked; one stamp
  comparison per take does it.  No validation is correct with fewer.
* `first_match_asks_prefix`: to answer the first matching row of an ordered
  store, every row up to and including it must be asked; a cursor that stops at
  its first match asks exactly those.
* `no_match_asks_every_row`: to answer that no row matches (an `absent` over
  rows that are not indexed by the condition), every row must be asked.
* `search_lower_bound`: an algorithm that may answer `N` different positions
  asks at least `log₂ N` questions on some input; a search in a balanced
  ordered index meets it up to the constant of its balance.

**States.**

* `resumable_states_card`: a state from which an enumeration of `n` answers
  resumes after any number of them takes at least `n + 1` values: one word
  wide.  The key reached is such a state.
* `visible_injective`, `card_life`, `stamps_information`: with `k` reader
  epochs a row's visibility to the readers is one of `k * (k + 1) / 2` lives
  (born at one epoch, dead at a later one), all distinguishable by the
  readers, so any representation keeps that many values per row; a birth and a
  death stamp in epochs take `(k + 1) * (k + 1)` values, at most four times as
  many: two bits above the minimum.  The stamps need the resolution of the
  reader epochs, not of the write clock.

**Writes.**

* `writes_lower_bound`: a sequence of single-cell writes changes at most as
  many cells as it is long; a firing that takes `t` rows changes `t` liveness
  cells and writes at least `t` times.
* `trail_pops_le_binds`: over any run of bindings, choice points and undos, a
  trail pops at most as many entries as were bound: undoing is paid for by the
  binding it undoes, so a trail costs at most twice the bindings themselves.

Positive and negative examples: `Controls`.

Each model leaves things out, and the bounds do not transfer to what is left
out: an index answers `no_match` and `first_match` with one search; a write
that covers a range of keys with one record changes many rows at once; a
representation that shares structure between versions undoes in constant time
at a logarithmic price per binding.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Step.LowerBounds

/-- An algorithm that asks about one cell at a time and answers at a leaf. -/
inductive DTree (ι α : Type*) where
  | leaf (a : α)
  | ask (i : ι) (no yes : DTree ι α)

namespace DTree

variable {ι α : Type*}

/-- The answer on an input. -/
def eval (x : ι → Bool) : DTree ι α → α
  | leaf a => a
  | ask i no yes => if x i then yes.eval x else no.eval x

/-- The cells asked on an input, in order. -/
def asked (x : ι → Bool) : DTree ι α → List ι
  | leaf _ => []
  | ask i no yes => i :: (if x i then yes.asked x else no.asked x)

/-- Two inputs that agree on the cells asked get the same answer. -/
theorem eval_congr (t : DTree ι α) (x y : ι → Bool) (agree : ∀ i ∈ t.asked x, x i = y i) :
    t.eval x = t.eval y := by
  induction t with
  | leaf a => rfl
  | ask i no yes ihn ihy =>
    have hi : x i = y i := agree i (by simp [asked])
    cases hx : x i with
    | true =>
      have sub : ∀ j ∈ yes.asked x, x j = y j := fun j hj => agree j (by simp [asked, hx, hj])
      simp only [eval, ← hi, hx, if_true]
      exact ihy sub
    | false =>
      have sub : ∀ j ∈ no.asked x, x j = y j := fun j hj => agree j (by simp [asked, hx, hj])
      simp only [eval, ← hi, hx, Bool.false_eq_true, if_false]
      exact ihn sub

/-- **A cell whose flip changes the answer is asked.** -/
theorem asks_of_sensitive [DecidableEq ι] (t : DTree ι α) (x : ι → Bool) (i : ι) (b : Bool)
    (changes : t.eval (Function.update x i b) ≠ t.eval x) : i ∈ t.asked x := by
  by_contra not
  apply changes
  symm
  apply eval_congr
  intro j hj
  have ne : j ≠ i := fun h => not (h ▸ hj)
  rw [Function.update_of_ne ne]

/-- An algorithm none of whose runs within a class of inputs asks more than
`w` questions gives at most `2 ^ w` different answers on that class. -/
theorem outputs_bound [DecidableEq α] (t : DTree ι α) (C : (ι → Bool) → Prop) (w : ℕ)
    (short : ∀ x, C x → (t.asked x).length ≤ w) :
    ∃ S : Finset α, S.card ≤ 2 ^ w ∧ ∀ x, C x → t.eval x ∈ S := by
  induction t generalizing C w with
  | leaf a => exact ⟨{a}, by simp [Nat.one_le_two_pow], fun x _ => by simp [eval]⟩
  | ask i no yes ihn ihy =>
    cases w with
    | zero => exact ⟨∅, by simp, fun x hx => absurd (short x hx) (by simp [asked])⟩
    | succ w =>
      obtain ⟨Sn, cn, mn⟩ := ihn (fun x => C x ∧ x i = false) w (fun x hx => by
        have := short x hx.1
        simp only [asked, hx.2, Bool.false_eq_true, if_false, List.length_cons] at this
        omega)
      obtain ⟨Sy, cy, my⟩ := ihy (fun x => C x ∧ x i = true) w (fun x hx => by
        have := short x hx.1
        simp only [asked, hx.2, if_true, List.length_cons] at this
        omega)
      refine ⟨Sn ∪ Sy, ?_, fun x hx => ?_⟩
      · calc (Sn ∪ Sy).card ≤ Sn.card + Sy.card := Finset.card_union_le _ _
          _ ≤ 2 ^ w + 2 ^ w := Nat.add_le_add cn cy
          _ = 2 ^ (w + 1) := by ring
      · cases hxi : x i with
        | true =>
          simp only [eval, hxi, if_true]
          exact Finset.mem_union_right _ (my x ⟨hx, hxi⟩)
        | false =>
          simp only [eval, hxi, Bool.false_eq_true, if_false]
          exact Finset.mem_union_left _ (mn x ⟨hx, hxi⟩)

end DTree

open DTree

/-! ## Validation -/

/-- **Every take must be asked.**  An algorithm that decides whether all the
rows of `T` are live asks every row of `T` on any input where they all are. -/
theorem validation_asks_every_take {ι : Type*} [DecidableEq ι] (t : DTree ι Bool) (T : Finset ι)
    (correct : ∀ x, t.eval x = decide (∀ i ∈ T, x i = true)) (x : ι → Bool)
    (alive : ∀ i ∈ T, x i = true) : ∀ i ∈ T, i ∈ t.asked x := by
  intro i hi
  apply asks_of_sensitive t x i false
  intro h
  rw [correct, correct, decide_eq_decide] at h
  have := h.mpr alive i hi
  simp at this

theorem validation_cost {ι : Type*} [DecidableEq ι] (t : DTree ι Bool) (T : Finset ι)
    (correct : ∀ x, t.eval x = decide (∀ i ∈ T, x i = true)) (x : ι → Bool)
    (alive : ∀ i ∈ T, x i = true) : T.card ≤ (t.asked x).length := by
  have sub : T ⊆ (t.asked x).toFinset := fun i hi =>
    List.mem_toFinset.mpr (validation_asks_every_take t T correct x alive i hi)
  exact (Finset.card_le_card sub).trans (List.toFinset_card_le _)

/-- The validator: one question per row, stopping at the first dead one. -/
def checkAll {ι : Type*} : List ι → DTree ι Bool
  | [] => .leaf true
  | i :: rest => .ask i (.leaf false) (checkAll rest)

theorem checkAll_eval {ι : Type*} (rows : List ι) (x : ι → Bool) :
    (checkAll rows).eval x = rows.all x := by
  induction rows with
  | nil => rfl
  | cons i rest ih =>
    cases hx : x i <;> simp [checkAll, DTree.eval, hx, ih]

/-- The validator asks at most one question per row: it meets the bound. -/
theorem checkAll_asks {ι : Type*} (rows : List ι) (x : ι → Bool) :
    ((checkAll rows).asked x).length ≤ rows.length := by
  induction rows with
  | nil => simp [checkAll, DTree.asked]
  | cons i rest ih =>
    cases hx : x i <;> simp [checkAll, DTree.asked, hx]
    exact ih

/-! ## The first answer -/

/-- **The first match costs its prefix.**  An algorithm that answers the first
matching row among `n` asks every row before which no row matches: all rows up
to and including the first match, and every row when none matches. -/
theorem first_match_asks_prefix (t : DTree ℕ (Option ℕ)) (n : ℕ)
    (correct : ∀ x, t.eval x = (List.range n).find? x) (x : ℕ → Bool) (i : ℕ) (hi : i < n)
    (before : ∀ j < i, x j = false) : i ∈ t.asked x := by
  apply asks_of_sensitive t x i (!x i)
  intro h
  rw [correct, correct] at h
  have first : ∀ z : ℕ → Bool, (∀ j < i, z j = false) →
      ((List.range n).find? z = some i ↔ z i = true) := by
    intro z hz
    rw [List.find?_range_eq_some]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, List.mem_range.mpr hi, fun j hj => by simp [hz j hj]⟩
  have flipped : ∀ j < i, Function.update x i (!x i) j = false := fun j hj => by
    rw [Function.update_of_ne (Nat.ne_of_lt hj)]
    exact before j hj
  have a := first x before
  have b := first _ flipped
  rw [h, a, Function.update_self] at b
  cases hx : x i <;> simp [hx] at b

/-- **Absence costs every row.**  An algorithm that answers whether some row
among `n` matches asks every row when none does. -/
theorem no_match_asks_every_row (t : DTree ℕ Bool) (n : ℕ)
    (correct : ∀ x, t.eval x = (List.range n).any x) (i : ℕ) (hi : i < n) :
    i ∈ t.asked fun _ => false := by
  apply asks_of_sensitive t _ i true
  intro h
  rw [correct, correct] at h
  have none : (List.range n).any (fun _ => false) = false := by simp
  have some : (List.range n).any (Function.update (fun _ => false) i true) = true :=
    List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, by simp⟩
  rw [none, some] at h
  cases h

/-- **Searching among `N` positions costs `log₂ N` questions.**  If every
position is the answer on some input and no run asks more than `w` questions,
then `N ≤ 2 ^ w`. -/
theorem search_lower_bound {ι : Type*} {N : ℕ} (t : DTree ι (Fin N))
    (onto : ∀ p : Fin N, ∃ x, t.eval x = p) (w : ℕ)
    (short : ∀ x, (t.asked x).length ≤ w) : N ≤ 2 ^ w := by
  obtain ⟨S, card, mem⟩ := DTree.outputs_bound t (fun _ => True) w (fun x _ => short x)
  have all : S = Finset.univ := by
    ext p
    obtain ⟨x, hx⟩ := onto p
    simpa using hx ▸ mem x trivial
  rw [all, Finset.card_univ, Fintype.card_fin] at card
  exact card

/-! ## Resumable states -/

/-- A state from which the rest of an enumeration is recovered distinguishes
every number of answers already given. -/
theorem resumable_states_injective {β S : Type*} (answers : List β)
    (save : Fin (answers.length + 1) → S) (resume : S → List β)
    (correct : ∀ k, resume (save k) = answers.drop k) : Function.Injective save := by
  intro a b h
  have len := congrArg List.length (congrArg resume h)
  rw [correct, correct, List.length_drop, List.length_drop] at len
  have ha := a.isLt
  have hb := b.isLt
  exact Fin.ext (by omega)

/-- **A resumable state takes at least `n + 1` values.** -/
theorem resumable_states_card {β S : Type*} [Fintype S] (answers : List β)
    (save : Fin (answers.length + 1) → S) (resume : S → List β)
    (correct : ∀ k, resume (save k) = answers.drop k) :
    answers.length + 1 ≤ Fintype.card S := by
  have := Fintype.card_le_of_injective save (resumable_states_injective answers save resume correct)
  rwa [Fintype.card_fin] at this

/-! ## Visibility by stamps -/

/-- A row's life in reader epochs: born at epoch `b`, dead at epoch `d`, with
`b < d`.  The reader of epoch `r` sees it when `b ≤ r < d`. -/
abbrev Life (k : ℕ) := {p : Fin (k + 1) × Fin (k + 1) // p.1 < p.2}

/-- The stamp comparison. -/
def Life.visible {k : ℕ} (l : Life k) (r : Fin k) : Bool :=
  decide (l.1.1.val ≤ r.val ∧ r.val < l.1.2.val)

/-- **The readers tell every two lives apart.** -/
theorem visible_injective (k : ℕ) : Function.Injective (fun l : Life k => l.visible) := by
  rintro ⟨⟨b, d⟩, hbd⟩ ⟨⟨b', d'⟩, hbd'⟩ h
  have lt : b.val < d.val := hbd
  have lt' : b'.val < d'.val := hbd'
  have hd := d.isLt
  have hd' := d'.isLt
  have e1 := congrFun h ⟨b.val, by omega⟩
  have e2 := congrFun h ⟨b'.val, by omega⟩
  have e3 := congrFun h ⟨d.val - 1, by omega⟩
  have e4 := congrFun h ⟨d'.val - 1, by omega⟩
  simp only [Life.visible, decide_eq_decide] at e1 e2 e3 e4
  have hb : b.val = b'.val := by omega
  have hdd : d.val = d'.val := by omega
  exact Subtype.ext (Prod.ext (Fin.ext hb) (Fin.ext hdd))

/-- The lives over `k` epochs number `k * (k + 1) / 2`. -/
theorem card_life (k : ℕ) : 2 * Fintype.card (Life k) = k * (k + 1) := by
  have count : Fintype.card (Life k) = ∑ d : Fin (k + 1), d.val := by
    rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.card_filter]
    have : (Finset.univ.filter fun b : Fin (k + 1) => b < d) = Finset.Iio d := by
      ext b
      simp
    rw [this, Fin.card_Iio]
  rw [count, Fin.sum_univ_eq_sum_range (fun i => i) (k + 1), mul_comm,
    Finset.sum_range_id_mul_two]
  simp [mul_comm]

/-- **What any snapshot representation keeps per row.**  A code from which
every reader's view of a row can be read takes at least `k * (k + 1) / 2`
values. -/
theorem stamps_information (k : ℕ) {Code : Type*} [Fintype Code] (enc : Life k → Code)
    (dec : Code → Fin k → Bool) (correct : ∀ l, dec (enc l) = l.visible) :
    k * (k + 1) ≤ 2 * Fintype.card Code := by
  have inj : Function.Injective enc := by
    intro l l' h
    apply visible_injective k
    change l.visible = l'.visible
    rw [← correct l, ← correct l', h]
  have := Fintype.card_le_of_injective enc inj
  rw [← card_life]
  omega

/-- **Two stamps are within two bits of the minimum**: the pairs of epochs are
at most four times the lives, for at least one epoch. -/
theorem stamp_pairs_le (k : ℕ) (pos : 1 ≤ k) :
    Fintype.card (Fin (k + 1) × Fin (k + 1)) ≤ 4 * Fintype.card (Life k) := by
  have h := card_life k
  rw [Fintype.card_prod, Fintype.card_fin]
  nlinarith

/-! ## Writes -/

/-- Single-cell writes, applied in order. -/
def applyWrites {ι β : Type*} [DecidableEq ι] (ws : List (ι × β)) (f : ι → β) : ι → β :=
  ws.foldl (fun g w => Function.update g w.1 w.2) f

theorem applyWrites_of_notMem {ι β : Type*} [DecidableEq ι] (ws : List (ι × β)) (f : ι → β)
    (i : ι) (untouched : i ∉ ws.map Prod.fst) : applyWrites ws f i = f i := by
  induction ws generalizing f with
  | nil => rfl
  | cons w ws ih =>
    have ne : i ≠ w.1 := fun h => untouched (by simp [h])
    have rest : i ∉ ws.map Prod.fst := fun h => untouched (by simp [List.mem_map.mp h])
    change applyWrites ws (Function.update f w.1 w.2) i = f i
    rw [ih _ rest, Function.update_of_ne ne]

/-- **A sequence of single-cell writes changes at most as many cells as it is
long.**  Taking `t` rows, which changes `t` liveness cells, takes `t` writes. -/
theorem writes_lower_bound {ι β : Type*} [DecidableEq ι] (ws : List (ι × β)) (f : ι → β)
    (S : Finset ι) (changed : ∀ i ∈ S, applyWrites ws f i ≠ f i) : S.card ≤ ws.length := by
  have sub : S ⊆ (ws.map Prod.fst).toFinset := by
    intro i hi
    by_contra not
    exact changed i hi (applyWrites_of_notMem ws f i (fun h => not (List.mem_toFinset.mpr h)))
  calc S.card ≤ (ws.map Prod.fst).toFinset.card := Finset.card_le_card sub
    _ ≤ (ws.map Prod.fst).length := List.toFinset_card_le _
    _ = ws.length := List.length_map _

/-! ## The trail -/

/-- What a search does to its bindings: bind a variable, leave a choice point,
or undo to the latest choice point. -/
inductive TrailOp where
  | bind
  | mark
  | undo

/-- The trail as the lengths of its segments, the current one first, with the
entries popped and the bindings made so far. -/
structure TrailState where
  segments : List ℕ
  pops : ℕ
  binds : ℕ

/-- A binding pushes one entry; a choice point opens a segment; an undo pops
the current segment, which is the bindings made since the choice point. -/
def TrailState.step (s : TrailState) : TrailOp → TrailState
  | .bind =>
    match s.segments with
    | [] => { s with segments := [1], binds := s.binds + 1 }
    | n :: rest => { s with segments := (n + 1) :: rest, binds := s.binds + 1 }
  | .mark => { s with segments := 0 :: s.segments }
  | .undo =>
    match s.segments with
    | [] => s
    | n :: rest => { s with segments := rest, pops := s.pops + n }

/-- Entries popped and entries still on the trail are the bindings made. -/
theorem trail_invariant (ops : List TrailOp) (s : TrailState)
    (inv : s.pops + s.segments.sum = s.binds) :
    (ops.foldl TrailState.step s).pops + (ops.foldl TrailState.step s).segments.sum =
      (ops.foldl TrailState.step s).binds := by
  induction ops generalizing s with
  | nil => exact inv
  | cons op ops ih =>
    apply ih
    cases op with
    | bind =>
      unfold TrailState.step
      cases h : s.segments with
      | nil => simp only [h, List.sum_nil, List.sum_cons] at inv ⊢; omega
      | cons n rest => simp only [h, List.sum_cons] at inv ⊢; omega
    | mark => simpa [TrailState.step] using inv
    | undo =>
      unfold TrailState.step
      cases h : s.segments with
      | nil => simpa [h] using inv
      | cons n rest => simp only [h, List.sum_cons] at inv ⊢; omega

/-- **Undoing is paid for by binding.**  Over any run from an empty trail the
entries popped are at most the bindings made, so the trail's writes are at
most twice the bindings. -/
theorem trail_pops_le_binds (ops : List TrailOp) :
    (ops.foldl TrailState.step ⟨[], 0, 0⟩).pops ≤ (ops.foldl TrailState.step ⟨[], 0, 0⟩).binds := by
  have := trail_invariant ops ⟨[], 0, 0⟩ rfl
  omega

namespace Controls

/-- Positive: the validator of two rows asks both when both are live. -/
example : ((checkAll [0, 1]).asked fun _ => true) = [0, 1] := rfl

/-- A validator that asks only the first of two rows. -/
def lazyValidator : DTree ℕ Bool := .ask 0 (.leaf false) (.leaf true)

/-- Negative: it accepts an input on which the second row is dead. -/
theorem lazy_validator_wrong :
    lazyValidator.eval (fun i => decide (i = 0)) = true ∧
      (fun i : ℕ => decide (i = 0)) 1 = false := by
  decide

/-- Positive: three lives over two epochs, and nine pairs of stamps. -/
example : 2 * Fintype.card (Life 2) = 6 := card_life 2

/-- Negative: one bit per row cannot serve two reader epochs, which need three
values. -/
theorem one_bit_is_not_enough (enc : Life 2 → Bool) (dec : Bool → Fin 2 → Bool) :
    ¬ ∀ l, dec (enc l) = l.visible := by
  intro correct
  have := stamps_information 2 enc dec correct
  simp at this

/-- Positive: bind twice, leave a choice point, bind three times, undo: three
entries are popped, five bindings were made. -/
example :
    ([TrailOp.bind, .bind, .mark, .bind, .bind, .bind, .undo].foldl TrailState.step ⟨[], 0, 0⟩).pops
      = 3 := rfl

/-- A search that saves its bindings by copying all of them at every choice
point, and undoes by going back to the copy: the cells copied. -/
def copyCost : List TrailOp → ℕ → List ℕ → ℕ
  | [], _, _ => 0
  | .bind :: ops, size, saved => copyCost ops (size + 1) saved
  | .mark :: ops, size, saved => size + copyCost ops size (size :: saved)
  | .undo :: ops, size, saved =>
    match saved with
    | [] => copyCost ops size []
    | s :: rest => copyCost ops s rest

/-- Negative: with three bindings and then three choice points, copying moves
nine cells, three times the bindings; the trail pops none.  Saving by copying
is not paid for by the bindings. -/
theorem copying_is_not_amortized :
    copyCost [.bind, .bind, .bind, .mark, .mark, .mark] 0 [] = 9 ∧
      ([TrailOp.bind, .bind, .bind, .mark, .mark, .mark].foldl TrailState.step ⟨[], 0, 0⟩).pops
        = 0 := by
  decide

end Controls

end Mettapedia.Machines.Step.LowerBounds
