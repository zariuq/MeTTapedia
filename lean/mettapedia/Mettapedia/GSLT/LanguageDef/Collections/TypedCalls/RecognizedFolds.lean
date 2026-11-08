import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TrustedVersions

/-!
# Recognized folds: one walk of the spine for two equations

A head whose only two equations are

* `(= (g nil) base)`, `nil` a symbol no equation matches and `base` a
  machine integer, and
* `(= (g (cons $v₁ … $vₘ)) (op a b))`, the `$vᵢ` distinct variables, `cons` a
  symbol no equation matches, `op` the grounded `+` or `*`, one of `a`, `b`
  the call `(g $vᵣ)` and the other a field `$vₖ` (`k ≠ r`) or an integer,

is answered by the machine in one walk of its argument's spine of cells.
This module states that walk and proves what it computes.

**The walk** (`readSpine`): follow the recursive field from cell to cell to
the first term that is not a cell (`Presentations.Family.spine`); the spine
qualifies when that term is `nil` and each cell's other operand is a machine
integer (a literal operand qualifies on every cell).

**The exact right fold** (`foldExact`) folds the operands from the right in
machine integers, as the equations compute them, and declines at the first
step whose exact value is not a machine integer. It declines **exactly**
where some right partial value leaves the machine integers
(`foldExact_eq_some_iff`, `foldExact_eq_none_iff`).

**The forward sum** (`runFold`): a sum over fields takes one pass from the
left, accumulating with two's-complement wrapping, and answers when
`|base| + n · max |field|` is a machine integer: every right partial sum is
then base plus some fields, so none leaves the machine integers
(`partial_bound`), and the wrapped total is the exact one
(`runFold_add_field`: the forward pass is the exact fold, decline included).
A sum of a literal step answers `base + n · c` when the product and the sum
are machine integers (`runFold_add_literal`); it may decline where the exact
fold answers (`Controls.literal_sum_declines_early`), which costs the
equations' run, never an answer. Products take the exact fold.

**The equations** are read by the expression model of `TrustedVersions`
(`Expr.eval`, `equationsBody`, `versionRun`): the untyped head's run. Where
the grounded operation computes in-range machine arithmetic exactly
(`PrimExact`), the equations answer on a qualifying spine the single value
of the exact fold, at every fuel past the spine's length
(`equations_spine`). So the machine's route, the fold where it answers and
the equations where it declines, has exactly the equations' answers on
every argument (`machine_eq_equations`), multiplicity included.

**A typed head** keeps its protocol's checks at every call to itself. Under
PeTTa's protocol (`protocolRun`) the fold is the protocol's answer when the
formal's fact passes from a cell to its recursive field (`Inversion`) and
the range types every integer once: the equations then meet the version
hypotheses (`fold_versionHyps`, `typed_fold_eq_protocol`). Without that
inversion the protocol checks a call to itself at a field the declarations
type otherwise, and the fold must decline: HE answers
`(Error (g Nil) (BadArgType 1 Foo Bar))` for `(g (Cons 1 Nil))` under
`(: Nil Bar)`, `(: Cons (-> Number Bar Foo))` and `(: g (-> Foo Number))`,
where the walk answers `1` (`Controls.typed_fold_without_inversion`).

**Controls.** An improper end, a field that is not a machine integer and an
overflowing step decline (`Controls.improper_end`, `Controls.string_field`,
`Controls.overflow_declines`); a sum whose bound fails is still answered by
the exact fold where its right partial sums fit
(`Controls.bound_fails_exact_answers`); a user equation for `+` makes the
equations answer otherwise, which is why recognition requires none
(`Controls.user_plus_breaks`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RecognizedFolds

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Presentations (Family Spine)

/-! ## Machine integers -/

/-- `INT64_MIN`. -/
def i64Min : ℤ := -9223372036854775808

/-- `INT64_MAX`. -/
def i64Max : ℤ := 9223372036854775807

/-- A machine integer: a value of `int64_t`. -/
def I64 (z : ℤ) : Prop := i64Min ≤ z ∧ z ≤ i64Max

instance (z : ℤ) : Decidable (I64 z) := by
  unfold I64
  infer_instance

/-- The `int64_t` a 64-bit unsigned sum converts to: two's-complement
wrapping. -/
def wrap (z : ℤ) : ℤ := (z + 9223372036854775808) % 18446744073709551616 - 9223372036854775808

theorem wrap_of_I64 {z : ℤ} (h : I64 z) : wrap z = z := by
  unfold wrap
  unfold I64 i64Min i64Max at h
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  omega

/-- A grounded integer. -/
def int (z : ℤ) : Atom := .grounded (.int z)

/-- The machine integer an atom is, where it is one. -/
def machineInt : Atom → Option ℤ
  | .grounded (.int z) => if I64 z then some z else none
  | _ => none

theorem machineInt_eq_some {a : Atom} {z : ℤ} : machineInt a = some z ↔ a = int z ∧ I64 z := by
  constructor
  · intro h
    match a, h with
    | .grounded (.int w), h =>
        simp only [machineInt] at h
        split_ifs at h with hw
        cases h
        exact ⟨rfl, hw⟩
  · rintro ⟨rfl, hz⟩
    simp [machineInt, int, hz]

/-! ## The recognized shape -/

/-- The grounded operation of the step. -/
inductive Op where
  | add
  | mul
  deriving DecidableEq

/-- Its value on integers. -/
def Op.apply : Op → ℤ → ℤ → ℤ
  | .add, a, b => a + b
  | .mul, a, b => a * b

/-- Its symbol. -/
def Op.name : Op → String
  | .add => "+"
  | .mul => "*"

theorem Op.apply_comm (op : Op) (a b : ℤ) : op.apply a b = op.apply b a := by
  cases op
  · exact add_comm a b
  · exact mul_comm a b

/-- A recognized fold: `(= (g nil) base)` and
`(= (g (cons $v₀ … $vₘ₋₁)) (op a b))` with `m = pre + 1 + post` fields, the
recursive one at index `pre`, and the other operand the field at `item` or,
for `item = none`, the integer `literal`; `callLeft` when the call is the
left operand. -/
structure Spec where
  nil : String
  cons : String
  pre : ℕ
  post : ℕ
  op : Op
  item : Option ℕ
  literal : ℤ
  callLeft : Bool
  base : ℤ

namespace Spec

variable (s : Spec)

/-- The number of fields of a cell. -/
def arity : ℕ := s.pre + 1 + s.post

/-- What recognition checks of the integers and the operand's position: the
base and the literal are machine integers, and the operand field is another
field than the recursive one. -/
structure WF : Prop where
  base : I64 s.base
  literal : I64 s.literal
  item : ∀ k, s.item = some k → k < s.arity ∧ k ≠ s.pre

/-- A cell's fields other than the recursive one: those before it and those
after it. -/
abbrev Fields : Type := {p : List Atom × List Atom // p.1.length = s.pre ∧ p.2.length = s.post}

/-- The cell with fields `f` and recursive field `r`. -/
def cell (f : s.Fields) (r : Atom) : Atom := .expression (.symbol s.cons :: (f.1.1 ++ r :: f.1.2))

/-- Recognize a cell. -/
def uncell : Atom → Option (s.Fields × Atom)
  | .expression (.symbol c :: xs) =>
      if h : c = s.cons ∧ xs.length = s.arity then
        some (⟨(xs.take s.pre, xs.drop (s.pre + 1)), by
            constructor
            · simp only [List.length_take, h.2, arity]; omega
            · simp only [List.length_drop, h.2, arity]; omega⟩,
          xs[s.pre]'(by rw [h.2]; unfold arity; omega))
      else none
  | _ => none

theorem uncell_eq_some {t : Atom} {f : s.Fields} {r : Atom} :
    s.uncell t = some (f, r) ↔ t = s.cell f r := by
  obtain ⟨⟨fs, gs⟩, hfs, hgs⟩ := f
  constructor
  · intro h
    match t, h with
    | .expression (.symbol c :: xs), h =>
        simp only [uncell] at h
        split_ifs at h with hc
        simp only [Option.some.injEq, Prod.mk.injEq, Subtype.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        obtain ⟨rfl, hlen⟩ := hc
        simp only [cell, Atom.expression.injEq, List.cons.injEq, true_and]
        have hlt : s.pre < xs.length := by rw [hlen]; unfold arity; omega
        rw [List.getElem_cons_drop hlt, List.take_append_drop]
  · intro h
    subst h
    dsimp only at hfs hgs
    have hlen : (fs ++ r :: gs).length = s.arity := by
      simp [hfs, hgs, arity]
      omega
    simp only [cell, uncell, hlen, and_true, dif_pos, Option.some.injEq, Prod.mk.injEq,
      Subtype.mk.injEq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    · rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
        show s.pre + 1 - fs.length = 1 by omega]
      rfl
    · rw [List.getElem_append_right (by omega)]
      simp [hfs]

theorem nodes_cell_lt (f : s.Fields) (r : Atom) :
    Presentations.nodes r < Presentations.nodes (s.cell f r) := by
  simp only [cell, Presentations.nodes, Presentations.nodesAll, Presentations.nodesAll_append]
  omega

/-- The cells of a recognized fold, as a constructor family. -/
def family : Family Atom s.Fields where
  cell := s.cell
  uncell := s.uncell
  uncell_cell f r := (s.uncell_eq_some).mpr rfl
  cell_uncell h := ((s.uncell_eq_some).mp h).symm
  rank := Presentations.nodes
  rank_lt {t f r} h := by
    rw [(s.uncell_eq_some).mp h]
    exact s.nodes_cell_lt f r

/-- The field at index `k` of a cell, the recursive one not counted out:
`k < pre` before it, `k > pre` after it. -/
def fieldAt (f : s.Fields) (k : ℕ) : Option Atom :=
  if k < s.pre then f.1.1[k]? else f.1.2[k - (s.pre + 1)]?

theorem getElem?_fields (f : s.Fields) (r : Atom) {k : ℕ} (hk : k ≠ s.pre) :
    (f.1.1 ++ r :: f.1.2)[k]? = s.fieldAt f k := by
  obtain ⟨⟨fs, gs⟩, hfs, hgs⟩ := f
  simp only [fieldAt]
  split_ifs with hlt
  · rw [List.getElem?_append_left (by simp [hfs]; omega)]
  · rw [List.getElem?_append_right (by simp [hfs]; omega)]
    simp only [hfs]
    rw [show k - s.pre = (k - (s.pre + 1)) + 1 by omega]
    rfl

/-- The step's other operand on a cell, where it is a machine integer: the
literal, or the field at `item`. -/
def operand (f : s.Fields) : Option ℤ :=
  match s.item with
  | none => some s.literal
  | some k => (s.fieldAt f k).bind machineInt

/-- **The walk**: the operands of the spine's cells, outermost first, where
the spine ends in `nil` and every operand is a machine integer. -/
def readSpine (t : Atom) : Option (List ℤ) :=
  if (s.family.spine t).stop = .symbol s.nil then (s.family.spine t).elems.mapM s.operand
  else none

/-- The number of cells the walk passes. -/
def cells (t : Atom) : ℕ := (s.family.spine t).elems.length

end Spec

/-! ## The right fold in machine integers -/

/-- The exact value of the fold of `xs` from the right, over the integers. -/
def exactFold (op : Op) (base : ℤ) (xs : List ℤ) : ℤ := xs.foldr op.apply base

/-- One step from the right in machine integers: `x op acc`, declined where
it leaves them. -/
def stepExact (op : Op) (x : ℤ) (acc : Option ℤ) : Option ℤ :=
  acc.bind fun a => if I64 (op.apply x a) then some (op.apply x a) else none

/-- **The exact right fold** (`prepared_pure_run_fold_exact`). -/
def foldExact (op : Op) (base : ℤ) (xs : List ℤ) : Option ℤ := xs.foldr (stepExact op) (some base)

/-- **The exact fold answers exactly where every right partial value is a
machine integer**, and then it answers the exact value. -/
theorem foldExact_eq_some_iff (op : Op) {base : ℤ} (hb : I64 base) :
    ∀ (xs : List ℤ) (v : ℤ), foldExact op base xs = some v ↔
      (∀ j ≤ xs.length, I64 (exactFold op base (xs.drop j))) ∧ v = exactFold op base xs
  | [], v => by
      simp only [foldExact, List.foldr_nil, Option.some.injEq, List.length_nil, Nat.le_zero,
        forall_eq, List.drop_zero, exactFold]
      constructor
      · rintro rfl
        exact ⟨hb, rfl⟩
      · rintro ⟨-, rfl⟩
        rfl
  | x :: xs, v => by
      have ih := foldExact_eq_some_iff op hb xs
      change stepExact op x (foldExact op base xs) = some v ↔ _
      constructor
      · intro h
        cases hrest : foldExact op base xs with
        | none => simp [hrest, stepExact] at h
        | some a =>
            obtain ⟨hall, rfl⟩ := (ih a).mp hrest
            simp only [hrest, stepExact, Option.bind_some] at h
            split_ifs at h with hin
            cases h
            refine ⟨fun j hj => ?_, rfl⟩
            cases j with
            | zero => simpa [exactFold] using hin
            | succ j => simpa using hall j (by simpa using hj)
      · rintro ⟨hall, rfl⟩
        have hrest : foldExact op base xs = some (exactFold op base xs) :=
          (ih _).mpr ⟨fun j hj => by simpa using hall (j + 1) (by simpa using hj), rfl⟩
        have hin : I64 (op.apply x (exactFold op base xs)) := by simpa [exactFold] using hall 0 (by simp)
        rw [hrest]
        simp only [stepExact, Option.bind_some, if_pos hin]
        rfl

/-- **The exact fold declines exactly where some step leaves the machine
integers.** -/
theorem foldExact_eq_none_iff (op : Op) {base : ℤ} (hb : I64 base) (xs : List ℤ) :
    foldExact op base xs = none ↔ ∃ j ≤ xs.length, ¬ I64 (exactFold op base (xs.drop j)) := by
  constructor
  · intro h
    by_contra hall
    have hall' : ∀ j ≤ xs.length, I64 (exactFold op base (xs.drop j)) := fun j hj => by
      by_contra hn
      exact hall ⟨j, hj, hn⟩
    have := (foldExact_eq_some_iff op hb xs (exactFold op base xs)).mpr ⟨hall', rfl⟩
    rw [h] at this
    cases this
  · rintro ⟨j, hj, hout⟩
    cases h : foldExact op base xs with
    | none => rfl
    | some v => exact absurd (((foldExact_eq_some_iff op hb xs v).mp h).1 j hj) hout

/-! ## The forward pass -/

/-- The largest magnitude of a list of integers. -/
def largest (xs : List ℤ) : ℕ := (xs.map Int.natAbs).foldr max 0

theorem natAbs_le_largest {xs : List ℤ} {x : ℤ} (hx : x ∈ xs) : x.natAbs ≤ largest xs := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
      simp only [largest, List.map_cons, List.foldr_cons] at ih ⊢
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_max_left _ _
      · exact le_trans (ih hx) (le_max_right _ _)

/-- **Every right partial sum of a short sum is bounded**: base plus `j`
fields is at most `|base| + j · L` in magnitude when every field is. -/
theorem partial_bound (base : ℤ) (L : ℕ) :
    ∀ xs : List ℤ, (∀ x ∈ xs, x.natAbs ≤ L) →
      (exactFold .add base xs).natAbs ≤ base.natAbs + xs.length * L
  | [], _ => by simp [exactFold]
  | x :: xs, hx => by
      have ih := partial_bound base L xs fun y hy => hx y (List.mem_cons_of_mem _ hy)
      have hxL := hx x List.mem_cons_self
      simp only [exactFold, List.foldr_cons, Op.apply, List.length_cons] at ih ⊢
      calc (x + List.foldr Op.add.apply base xs).natAbs
          ≤ x.natAbs + (List.foldr Op.add.apply base xs).natAbs := Int.natAbs_add_le _ _
        _ ≤ L + (base.natAbs + xs.length * L) := Nat.add_le_add hxL ih
        _ = base.natAbs + (xs.length + 1) * L := by ring

theorem exactFold_add (base : ℤ) (xs : List ℤ) : exactFold .add base xs = xs.sum + base := by
  induction xs with
  | nil => simp [exactFold]
  | cons x xs ih =>
      simp only [exactFold, List.foldr_cons, Op.apply, List.sum_cons] at ih ⊢
      rw [ih]
      ring

theorem I64_of_natAbs_le {z : ℤ} (h : z.natAbs ≤ 9223372036854775807) : I64 z := by
  unfold I64 i64Min i64Max
  omega

/-- **The forward bound gives every right partial sum**: when
`|base| + n · max |field|` is a machine integer, no partial sum the equations
form from the right leaves the machine integers. -/
theorem partials_of_bound (base : ℤ) (xs : List ℤ)
    (bound : base.natAbs + xs.length * largest xs ≤ 9223372036854775807) :
    ∀ j ≤ xs.length, I64 (exactFold .add base (xs.drop j)) := by
  intro j _
  apply I64_of_natAbs_le
  refine le_trans (partial_bound base (largest xs) (xs.drop j)
    fun x hx => natAbs_le_largest (List.mem_of_mem_drop hx)) (le_trans ?_ bound)
  have : (xs.drop j).length ≤ xs.length := by simp
  have := Nat.mul_le_mul_right (largest xs) this
  omega

/-- The machine's fold of a qualifying spine's operands
(`prepared_pure_run_fold`): a sum over fields forward with the bound, else
exactly; a sum of a literal step by its product; a product exactly. -/
def Spec.runOperands (s : Spec) (xs : List ℤ) : Option ℤ :=
  match s.op, s.item with
  | .add, some _ =>
      if s.base.natAbs + xs.length * largest xs ≤ 9223372036854775807 then
        some (wrap (xs.sum + s.base))
      else foldExact .add s.base xs
  | .add, none =>
      if (xs.length : ℤ) ≤ i64Max ∧ I64 (xs.length * s.literal) ∧ I64 (s.base + xs.length * s.literal) then
        some (s.base + xs.length * s.literal)
      else none
  | .mul, _ => foldExact .mul s.base xs

/-- **The recognized fold's value at an argument**, or nothing where it
declines. -/
def runFold (s : Spec) (t : Atom) : Option ℤ := (s.readSpine t).bind s.runOperands

/-- The exact fold at an argument. -/
def runExact (s : Spec) (t : Atom) : Option ℤ := (s.readSpine t).bind (foldExact s.op s.base)

/-- **A sum over fields: the forward pass is the exact fold**, decline
included. -/
theorem runOperands_add_field (s : Spec) (hb : I64 s.base) (hop : s.op = .add) {k : ℕ}
    (hk : s.item = some k) (xs : List ℤ) : s.runOperands xs = foldExact s.op s.base xs := by
  simp only [Spec.runOperands, hop, hk]
  split_ifs with bound
  · have hall := partials_of_bound s.base xs bound
    have hv : I64 (xs.sum + s.base) := by
      have := hall 0 (Nat.zero_le _)
      rwa [List.drop_zero, exactFold_add] at this
    rw [wrap_of_I64 hv]
    exact ((foldExact_eq_some_iff .add hb xs _).mpr ⟨hall, (exactFold_add _ _).symm⟩).symm
  · rfl

/-- The partial values of a literal step: base plus `j` literals. -/
theorem exactFold_literal (base c : ℤ) (n : ℕ) :
    exactFold .add base (List.replicate n c) = base + n * c := by
  induction n with
  | zero => simp [exactFold]
  | succ n ih =>
      simp only [exactFold, List.replicate_succ, List.foldr_cons, Op.apply] at ih ⊢
      rw [ih]
      push_cast
      ring

/-- **A sum of a literal step answers only what the exact fold answers.** -/
theorem runOperands_add_literal (s : Spec) (hb : I64 s.base) (hop : s.op = .add)
    (hk : s.item = none) (n : ℕ) {v : ℤ} (h : s.runOperands (List.replicate n s.literal) = some v) :
    foldExact s.op s.base (List.replicate n s.literal) = some v := by
  simp only [Spec.runOperands, hop, hk, List.length_replicate] at h
  split_ifs at h with hin
  cases h
  obtain ⟨-, -, hend⟩ := hin
  rw [hop, foldExact_eq_some_iff .add hb]
  refine ⟨fun j hj => ?_, by rw [exactFold_literal]⟩
  rw [List.drop_replicate, exactFold_literal]
  have hle : ((n - j : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.sub_le n j
  have hnn : (0 : ℤ) ≤ ((n - j : ℕ) : ℤ) := Int.natCast_nonneg _
  unfold I64 i64Min i64Max at hb hend ⊢
  rcases le_total 0 s.literal with hc | hc
  · have h1 : 0 ≤ ((n - j : ℕ) : ℤ) * s.literal := Int.mul_nonneg hnn hc
    have h2 : ((n - j : ℕ) : ℤ) * s.literal ≤ (n : ℤ) * s.literal := Int.mul_le_mul_of_nonneg_right hle hc
    generalize ((n - j : ℕ) : ℤ) * s.literal = P at *
    generalize (n : ℤ) * s.literal = N at *
    omega
  · have h1 : ((n - j : ℕ) : ℤ) * s.literal ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos hnn hc
    have h2 : (n : ℤ) * s.literal ≤ ((n - j : ℕ) : ℤ) * s.literal := Int.mul_le_mul_of_nonpos_right hle hc
    generalize ((n - j : ℕ) : ℤ) * s.literal = P at *
    generalize (n : ℤ) * s.literal = N at *
    omega

theorem mapM_const {α : Type} (g : α → Option ℤ) (c : ℤ) (hg : ∀ a, g a = some c) :
    ∀ fs : List α, fs.mapM g = some (List.replicate fs.length c)
  | [] => rfl
  | f :: fs => by simp [List.mapM_cons, hg, mapM_const g c hg fs, List.replicate_succ]

/-- The operands a literal step reads: the literal on every cell. -/
theorem readSpine_literal (s : Spec) (hk : s.item = none) {t : Atom} {xs : List ℤ}
    (h : s.readSpine t = some xs) : xs = List.replicate xs.length s.literal := by
  unfold Spec.readSpine at h
  split_ifs at h
  rw [mapM_const s.operand s.literal (fun f => by simp [Spec.operand, hk])] at h
  cases h
  rw [List.length_replicate]

/-- **The machine's fold answers only the exact fold's value.** -/
theorem runFold_sound (s : Spec) (wf : s.WF) {t : Atom} {v : ℤ} (h : runFold s t = some v) :
    runExact s t = some v := by
  unfold runFold at h
  unfold runExact
  cases hr : s.readSpine t with
  | none => simp [hr] at h
  | some xs =>
      simp only [hr, Option.bind_some] at h ⊢
      cases hop : s.op with
      | mul => simpa [Spec.runOperands, hop] using h
      | add =>
          cases hk : s.item with
          | some k => rwa [runOperands_add_field s wf.base hop hk, hop] at h
          | none =>
              rw [readSpine_literal s hk hr] at h ⊢
              have := runOperands_add_literal s wf.base hop hk _ h
              rwa [hop] at this

/-- **A sum over fields declines exactly where the exact fold does.** -/
theorem runFold_add_field (s : Spec) (wf : s.WF) (hop : s.op = .add) {k : ℕ} (hk : s.item = some k)
    (t : Atom) : runFold s t = runExact s t := by
  unfold runFold runExact
  cases s.readSpine t with
  | none => rfl
  | some xs => exact runOperands_add_field s wf.base hop hk xs

/-- **The exact fold at an argument declines exactly** where the argument is
not a qualifying spine or some right partial value leaves the machine
integers. -/
theorem runExact_eq_none_iff (s : Spec) (wf : s.WF) (t : Atom) :
    runExact s t = none ↔
      s.readSpine t = none ∨ ∃ xs, s.readSpine t = some xs ∧
        ∃ j ≤ xs.length, ¬ I64 (exactFold s.op s.base (xs.drop j)) := by
  unfold runExact
  cases s.readSpine t with
  | none => simp
  | some xs =>
      simp only [Option.bind_some, reduceCtorEq, false_or, Option.some.injEq, exists_eq_left']
      exact foldExact_eq_none_iff s.op wf.base xs

/-! ## The equations -/

/-- The name of the pattern variable of field `i`. -/
def vname (i : ℕ) : String := String.ofList (List.replicate (i + 1) 'v')

theorem vname_injective : Function.Injective vname := by
  intro i j h
  have := congrArg String.toList h
  simp only [vname, String.toList_ofList] at this
  have := congrArg List.length this
  simp only [List.length_replicate] at this
  omega

/-- Looking up the `k`-th of distinct names in their pairing with values
gives the `k`-th value. -/
theorem lookup_zip_getElem : ∀ (ns : List String), ns.Nodup → ∀ (vs : List Atom),
    vs.length = ns.length → ∀ k (hk : k < ns.length), (ns.zip vs).lookup ns[k] = vs[k]?
  | [], _, _, _, k, hk => absurd hk (by simp)
  | _ :: _, _, [], hlen, _, _ => by simp at hlen
  | n :: ns, _, v :: vs, _, 0, _ => by simp
  | n :: ns, hnd, v :: vs, hlen, k + 1, hk => by
      have hne : ns[k]'(by simpa using hk) ≠ n :=
        fun e => (List.nodup_cons.mp hnd).1 (e ▸ List.getElem_mem _)
      have hb : (ns[k]'(by simpa using hk) == n) = false := by simpa using hne
      simp only [List.zip_cons_cons, List.getElem_cons_succ, List.getElem?_cons_succ, List.lookup, hb]
      exact lookup_zip_getElem ns (List.nodup_cons.mp hnd).2 vs (by simpa using hlen) k (by simpa using hk)

theorem matchAll_vars (names : List String) :
    ∀ vs : List Atom, vs.length = names.length →
      Pat.matchAll (names.map Pat.var) vs = some (names.zip vs) := by
  induction names with
  | nil => intro vs h; cases vs <;> simp_all [Pat.matchAll]
  | cons x xs ih =>
      intro vs h
      cases vs with
      | nil => simp at h
      | cons v vs =>
          simp only [List.length_cons, add_left_inj] at h
          simp [Pat.matchAll, Pat.match, ih vs h]

theorem matchAll_vars_length (names : List String) (vs : List Atom) (h : vs.length ≠ names.length) :
    Pat.matchAll (names.map Pat.var) vs = none := by
  induction names generalizing vs with
  | nil => cases vs <;> simp_all [Pat.matchAll]
  | cons x xs ih =>
      cases vs with
      | nil => simp [Pat.matchAll]
      | cons v vs =>
          simp only [List.length_cons, ne_eq, add_left_inj] at h
          simp [Pat.matchAll, Pat.match, ih vs h]

namespace Spec

variable (s : Spec)

/-- The names of the pattern's variables. -/
def names : List String := (List.range s.arity).map vname

theorem names_nodup : s.names.Nodup := List.Nodup.map vname_injective List.nodup_range

theorem names_length : s.names.length = s.arity := by simp [names]

theorem lookup_names {vs : List Atom} (hvs : vs.length = s.arity) {k : ℕ} (hk : k < s.arity) :
    (s.names.zip vs).lookup (vname k) = vs[k]? := by
  have := lookup_zip_getElem s.names s.names_nodup vs (by rw [hvs, s.names_length]) k
    (by rw [s.names_length]; exact hk)
  simpa [names] using this

/-- The pattern `(cons $v₀ … $vₘ₋₁)`. -/
def consPat : Pat := .ctor s.cons (s.names.map Pat.var)

/-- The step's other operand as written. -/
def operandExpr : Expr :=
  match s.item with
  | some k => .var (vname k)
  | none => .const (int s.literal)

/-- The step's right-hand side `(op a b)`. -/
def stepRhs : Expr :=
  if s.callLeft then .prim s.op.name [.self [.var (vname s.pre)], s.operandExpr]
  else .prim s.op.name [s.operandExpr, .self [.var (vname s.pre)]]

/-- The two equations. -/
def eqs : List Equation :=
  [⟨[.const (.symbol s.nil)], .const (int s.base)⟩, ⟨[s.consPat], s.stepRhs⟩]

/-- The head's equations, reading its calls to itself through an oracle and
calling no other head. -/
def body (E : Env) : (List Atom → Multiset Atom) → List Atom → Multiset Atom :=
  fun o => equationsBody E s.eqs ⟨o, fun _ _ => 0⟩

theorem fields_length (f : s.Fields) (r : Atom) : (f.1.1 ++ r :: f.1.2).length = s.arity := by
  simp [f.2.1, f.2.2, arity]
  omega

theorem consPat_cell (f : s.Fields) (r : Atom) :
    Pat.matchAll [s.consPat] [s.cell f r] = some (s.names.zip (f.1.1 ++ r :: f.1.2)) := by
  have hm := matchAll_vars s.names (f.1.1 ++ r :: f.1.2) (by rw [s.fields_length, s.names_length])
  simp [Pat.matchAll, consPat, cell, Pat.match, hm]

theorem consPat_none {t : Atom} (h : s.uncell t = none) : Pat.matchAll [s.consPat] [t] = none := by
  match t, h with
  | .symbol _, _ => simp [Pat.matchAll, Pat.match, consPat]
  | .var _, _ => simp [Pat.matchAll, Pat.match, consPat]
  | .grounded _, _ => simp [Pat.matchAll, Pat.match, consPat]
  | .expression [], _ => simp [Pat.matchAll, Pat.match, consPat]
  | .expression (.var _ :: _), _ => simp [Pat.matchAll, Pat.match, consPat]
  | .expression (.grounded _ :: _), _ => simp [Pat.matchAll, Pat.match, consPat]
  | .expression (.expression _ :: _), _ => simp [Pat.matchAll, Pat.match, consPat]
  | .expression (.symbol c :: xs), h =>
      simp only [uncell] at h
      by_cases hc : c = s.cons
      · subst hc
        have hlen : xs.length ≠ s.arity := fun e => by simp [e] at h
        have hn := matchAll_vars_length s.names xs (by rw [s.names_length]; exact hlen)
        simp [Pat.matchAll, Pat.match, consPat, hn]
      · simp [Pat.matchAll, Pat.match, consPat, Ne.symm hc]

theorem eqs_coe : ((s.eqs : List Equation) : Multiset Equation) =
    (⟨[.const (.symbol s.nil)], .const (int s.base)⟩ : Equation) ::ₘ
      (⟨[s.consPat], s.stepRhs⟩ : Equation) ::ₘ 0 := rfl

/-- The equations at `nil`: the base. -/
theorem body_nil (E : Env) (o : List Atom → Multiset Atom) :
    s.body E o [.symbol s.nil] = {int s.base} := by
  have h1 : Pat.matchAll [.const (.symbol s.nil)] [.symbol s.nil] = some [] := by
    simp [Pat.matchAll, Pat.match]
  have h2 : Pat.matchAll [s.consPat] [.symbol s.nil] = none :=
    s.consPat_none (by simp [uncell])
  simp only [body, equationsBody, s.eqs_coe, Multiset.cons_bind, Multiset.zero_bind, h1, h2,
    Expr.eval, add_zero]

/-- The equations at a term that is neither `nil` nor a cell: nothing. -/
theorem body_other (E : Env) (o : List Atom → Multiset Atom) {t : Atom} (hu : s.uncell t = none)
    (hn : t ≠ .symbol s.nil) : s.body E o [t] = 0 := by
  have h1 : Pat.matchAll [.const (.symbol s.nil)] [t] = none := by
    simp [Pat.matchAll, Pat.match, hn]
  simp only [body, equationsBody, s.eqs_coe, Multiset.cons_bind, Multiset.zero_bind, h1,
    s.consPat_none hu, add_zero]

/-- The values of the step's other operand on a cell. -/
def operandVals (f : s.Fields) : Multiset Atom :=
  match s.item with
  | none => {int s.literal}
  | some k => match s.fieldAt f k with
    | some a => {a}
    | none => 0

/-- **The equations at a cell**: the step on each answer at the recursive
field, the calls to itself made there and nowhere else. -/
theorem body_cell (E : Env) (o : List Atom → Multiset Atom) (wf : s.WF) (f : s.Fields) (r : Atom) :
    s.body E o [s.cell f r] =
      if s.callLeft then (o [r]).bind fun acc => (s.operandVals f).bind fun x => E.prim s.op.name [acc, x]
      else (s.operandVals f).bind fun x => (o [r]).bind fun acc => E.prim s.op.name [x, acc] := by
  have hlen := s.fields_length f r
  have hr : (s.names.zip (f.1.1 ++ r :: f.1.2)).lookup (vname s.pre) = some r := by
    rw [s.lookup_names hlen (by unfold arity; omega)]
    simp [f.2.1]
  have hop : ∀ O : Oracle, s.operandExpr.eval E O (s.names.zip (f.1.1 ++ r :: f.1.2)) =
      s.operandVals f := by
    intro O
    unfold operandExpr operandVals
    cases hk : s.item with
    | none => simp [Expr.eval]
    | some k =>
        obtain ⟨hlt, hne⟩ := wf.item k hk
        simp only [Expr.eval]
        rw [s.lookup_names hlen hlt, s.getElem?_fields f r hne]
        cases s.fieldAt f k <;> rfl
  have h1 : Pat.matchAll [.const (.symbol s.nil)] [s.cell f r] = none := by
    simp [Pat.matchAll, Pat.match, cell]
  simp only [body, equationsBody, s.eqs_coe, Multiset.cons_bind, Multiset.zero_bind, h1,
    s.consPat_cell, zero_add, add_zero]
  unfold stepRhs
  split_ifs with hleft
  · simp only [Expr.eval, Expr.evalAll, hr, hop, Multiset.singleton_bind, Multiset.map_singleton,
      Multiset.map_bind, Multiset.bind_assoc]
  · simp only [Expr.eval, Expr.evalAll, hr, hop, Multiset.singleton_bind, Multiset.map_singleton,
      Multiset.map_bind, Multiset.bind_assoc]

theorem operandVals_of_operand {f : s.Fields} {x : ℤ} (hx : s.operand f = some x) :
    s.operandVals f = {int x} := by
  unfold operand at hx
  unfold operandVals
  cases hk : s.item with
  | none =>
      simp only [hk, Option.some.injEq] at hx
      subst hx
      rfl
  | some k =>
      simp only [hk] at hx
      cases hfa : s.fieldAt f k with
      | none => simp [hfa] at hx
      | some a =>
          simp only [hfa, Option.bind_some, machineInt_eq_some] at hx
          simp [hfa, hx.1]

theorem I64_of_operand (wf : s.WF) {f : s.Fields} {x : ℤ} (hx : s.operand f = some x) : I64 x := by
  unfold operand at hx
  cases hk : s.item with
  | none =>
      simp only [hk, Option.some.injEq] at hx
      subst hx
      exact wf.literal
  | some k =>
      simp only [hk] at hx
      cases hfa : s.fieldAt f k with
      | none => simp [hfa] at hx
      | some a =>
          simp only [hfa, Option.bind_some, machineInt_eq_some] at hx
          exact hx.2

end Spec

/-- **What recognition requires of the grounded operation**: on machine
integers whose exact result is a machine integer, it answers that result
once. -/
def PrimExact (E : Env) (op : Op) : Prop :=
  ∀ a b, I64 a → I64 b → I64 (op.apply a b) → E.prim op.name [int a, int b] = {int (op.apply a b)}

/-- **The equations answer the exact fold on a qualifying spine**: at every
fuel past the spine's length, the untyped head's run has exactly one answer,
the exact fold's value. -/
theorem equations_spine (s : Spec) (wf : s.WF) (E : Env) (hE : PrimExact E s.op) :
    ∀ (fs : List s.Fields) (xs : List ℤ), fs.mapM s.operand = some xs →
      ∀ v, foldExact s.op s.base xs = some v →
        ∀ n, fs.length < n →
          versionRun (s.body E) n [s.family.build ⟨fs, .symbol s.nil⟩] = {int v}
  | [], xs, hxs, v, hv, n, hn => by
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hxs
      subst hxs
      simp only [foldExact, List.foldr_nil, Option.some.injEq] at hv
      subst hv
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
      exact s.body_nil E _
  | f :: fs, xs, hxs, v, hv, n, hn => by
      cases hx : s.operand f with
      | none => simp [List.mapM_cons, hx] at hxs
      | some x =>
          cases hrest : fs.mapM s.operand with
          | none => simp [List.mapM_cons, hx, hrest] at hxs
          | some ys =>
              simp only [List.mapM_cons, hx, hrest, Option.bind_eq_bind, Option.bind_some,
                Option.pure_def, Option.some.injEq] at hxs
              subst hxs
              change stepExact s.op x (foldExact s.op s.base ys) = some v at hv
              cases hacc : foldExact s.op s.base ys with
              | none => simp [hacc, stepExact] at hv
              | some a =>
                  simp only [hacc, stepExact, Option.bind_some] at hv
                  split_ifs at hv with hin
                  cases hv
                  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
                  have ih := equations_spine s wf E hE fs ys hrest a hacc n (by simp at hn; omega)
                  have hxI := s.I64_of_operand wf hx
                  have haI : I64 a := by
                    have := ((foldExact_eq_some_iff s.op wf.base ys a).mp hacc)
                    rw [this.2]
                    simpa using this.1 0 (Nat.zero_le _)
                  simp only [versionRun, Family.build_cons]
                  change s.body E (versionRun (s.body E) n) [s.cell f _] = _
                  rw [s.body_cell E _ wf f _, ih, s.operandVals_of_operand hx]
                  split_ifs with hleft
                  · rw [Multiset.singleton_bind, Multiset.singleton_bind,
                      hE a x haI hxI (by rwa [Op.apply_comm]), Op.apply_comm]
                  · rw [Multiset.singleton_bind, Multiset.singleton_bind]
                    exact hE x a hxI haI hin

/-- **The equations' answer on a qualifying spine** is the exact fold's value
once, at every fuel past its number of cells. -/
theorem equations_eq_runExact (s : Spec) (wf : s.WF) (E : Env) (hE : PrimExact E s.op) {t : Atom}
    {v : ℤ} (h : runExact s t = some v) (n : ℕ) (hn : s.cells t < n) :
    versionRun (s.body E) n [t] = {int v} := by
  unfold runExact Spec.readSpine at h
  by_cases hstop : (s.family.spine t).stop = .symbol s.nil
  swap
  · rw [if_neg hstop] at h
    simp at h
  rw [if_pos hstop] at h
  cases hxs : (s.family.spine t).elems.mapM s.operand with
  | none => simp [hxs] at h
  | some xs =>
      simp only [hxs, Option.bind_some] at h
      have key := equations_spine s wf E hE _ xs hxs v h n hn
      rwa [show (⟨(s.family.spine t).elems, .symbol s.nil⟩ : Spine Atom s.Fields) = s.family.spine t by
        ext <;> simp [hstop], Family.build_spine] at key

/-- **The machine's route**: the recognized fold where it answers, the
equations where it declines. -/
def machine (s : Spec) (E : Env) (n : ℕ) (t : Atom) : Multiset Atom :=
  match runFold s t with
  | some v => {int v}
  | none => versionRun (s.body E) n [t]

/-- **The machine answers as the equations**, on every argument, at every
fuel past the argument's number of cells: a recognized fold changes no
answer and no multiplicity. -/
theorem machine_eq_equations (s : Spec) (wf : s.WF) (E : Env) (hE : PrimExact E s.op) (t : Atom)
    (n : ℕ) (hn : s.cells t < n) : machine s E n t = versionRun (s.body E) n [t] := by
  unfold machine
  cases h : runFold s t with
  | none => rfl
  | some v => exact (equations_eq_runExact s wf E hE (runFold_sound s wf h) n hn).symm

/-! ## Typed heads: the protocol checks every call to itself -/

section Typed

variable (Γ : Decls) (grounded : String → Bool)

/-- **The formal's fact passes from a cell to its recursive field**: what the
declarations must give for a typed fold's calls to themselves to meet their
formal. -/
def Inversion (s : Spec) (F : Ty Empty) : Prop :=
  ∀ f r, Holds Γ grounded (s.cell f r) F → Holds Γ grounded r F

theorem single_of_entryFacts {F : Ty Empty} {vs : List Atom}
    (h : EntryFacts Γ grounded [F] vs) : ∃ t, vs = [t] := by
  cases h with
  | cons _ rest => cases rest; exact ⟨_, rfl⟩

/-- **The fold's equations meet the version hypotheses** at a closed row
`(-> F R)` when the formal inverts through the cells, the range types every
integer once, and the grounded operation answers integers. -/
theorem fold_versionHyps (s : Spec) (wf : s.WF) (E : Env) (F R : Ty Empty)
    (inv : Inversion Γ grounded s F) (rg : ResultGuarded R.lift)
    (ints : ∀ z, Holds Γ grounded (int z) R)
    (primInts : ∀ vs w, w ∈ E.prim s.op.name vs → ∃ z, w = int z) :
    VersionHyps (Γ := Γ) (grounded := grounded) (s.body E) (s.body E) [F] R where
  resultGuarded := rg
  calls o o' agree _ vs hvs := by
    obtain ⟨t, rfl⟩ := single_of_entryFacts Γ grounded hvs
    cases hu : s.uncell t with
    | none =>
        by_cases hn : t = .symbol s.nil
        · subst hn
          rw [s.body_nil, s.body_nil]
        · rw [s.body_other E o hu hn, s.body_other E o' hu hn]
    | some p =>
        obtain ⟨f, r⟩ := p
        rw [(s.uncell_eq_some).mp hu] at hvs ⊢
        have hr : EntryFacts Γ grounded [F] [r] := by
          refine .cons (fun hg => ?_) .nil
          cases hvs with
          | cons hF _ => exact inv f r (hF hg)
        rw [s.body_cell E o wf f r, s.body_cell E o' wf f r, agree [r] hr]
  results o _ vs hvs w hw := by
    obtain ⟨t, rfl⟩ := single_of_entryFacts Γ grounded hvs
    cases hu : s.uncell t with
    | none =>
        by_cases hn : t = .symbol s.nil
        · subst hn
          rw [s.body_nil, Multiset.mem_singleton] at hw
          subst hw
          exact ints s.base
        · rw [s.body_other E o hu hn] at hw
          exact absurd hw (Multiset.notMem_zero w)
    | some p =>
        obtain ⟨f, r⟩ := p
        rw [(s.uncell_eq_some).mp hu, s.body_cell E o wf f r] at hw
        split_ifs at hw <;>
        · simp only [Multiset.mem_bind] at hw
          obtain ⟨_, _, _, _, hw⟩ := hw
          obtain ⟨z, rfl⟩ := primInts _ w hw
          exact ints z

/-- **A typed fold with an inversion certificate answers as its protocol**:
on an argument meeting the formal's fact, at every fuel past its number of
cells, the machine's route has exactly the answers of PeTTa's typed call,
every call to itself checked. -/
theorem typed_fold_eq_protocol (s : Spec) (wf : s.WF) (E : Env) (hE : PrimExact E s.op) (F R : Ty Empty)
    (inv : Inversion Γ grounded s F) (rg : ResultGuarded R.lift)
    (ints : ∀ z, Holds Γ grounded (int z) R)
    (primInts : ∀ vs w, w ∈ E.prim s.op.name vs → ∃ z, w = int z)
    (t : Atom) (ht : EntryFacts Γ grounded [F] [t]) (n : ℕ) (hn : s.cells t < n) :
    protocolRun Γ grounded (s.body E) (arrow ([F].map Ty.lift) R.lift) n [t] = machine s E n t := by
  rw [version_eq_protocol (fold_versionHyps Γ grounded s wf E F R inv rg ints primInts) n [t] ht,
    machine_eq_equations s wf E hE t n hn]

end Typed


/-! ## Reading built spines -/

/-- **The walk of a built spine** whose end is not a cell: its operands where
the end is `nil`. -/
theorem readSpine_build (s : Spec) (fs : List s.Fields) {e : Atom} (he : s.uncell e = none) :
    s.readSpine (s.family.build ⟨fs, e⟩) = if e = .symbol s.nil then fs.mapM s.operand else none := by
  unfold Spec.readSpine
  rw [Family.spine_build_of_canonical s.family (show s.family.Canonical ⟨fs, e⟩ from he)]

/-! ## Controls -/

namespace Controls

/-- `(= (sum Nil) 0)` and `(= (sum (Cons $x $xs)) (+ $x (sum $xs)))`. -/
def sumSpec : Spec := ⟨"Nil", "Cons", 1, 0, .add, some 0, 0, false, 0⟩

theorem sumSpec_wf : sumSpec.WF :=
  ⟨by decide, by decide, fun k hk => by
    simp only [sumSpec, Option.some.injEq] at hk
    subst hk
    decide⟩

/-- The cell fields of one element. -/
def one (x : Atom) : sumSpec.Fields := ⟨([x], []), rfl, rfl⟩

/-- A spine of `Cons` cells over `xs` ending in `e`. -/
def spineOf (xs : List Atom) (e : Atom) : Atom := sumSpec.family.build ⟨xs.map one, e⟩

/-- A string. -/
def str (text : String) : Atom := .grounded (.string text)

theorem foo_end : sumSpec.uncell (.symbol "Foo") = none := rfl

theorem nil_end : sumSpec.uncell (.symbol "Nil") = none := rfl

theorem spineOf_cons (x : Atom) (xs : List Atom) (e : Atom) :
    spineOf (x :: xs) e = .expression [.symbol "Cons", x, spineOf xs e] := rfl

/-- **An improper end declines**: `(Cons 1 (Cons 2 Foo))` is not walked. -/
theorem improper_end : runFold sumSpec (spineOf [int 1, int 2] (.symbol "Foo")) = none := by
  unfold runFold spineOf
  rw [readSpine_build sumSpec _ foo_end]
  rfl

/-- **A field that is not a machine integer declines**: `(Cons 1 (Cons "x" Nil))`. -/
theorem string_field : runFold sumSpec (spineOf [int 1, str "x"] (.symbol "Nil")) = none := by
  unfold runFold spineOf
  rw [readSpine_build sumSpec _ nil_end]
  rfl

/-- **An overflowing step declines**: `(Cons 9223372036854775807 (Cons 1 Nil))`,
whose last step leaves the machine integers. -/
theorem overflow_declines :
    runFold sumSpec (spineOf [int 9223372036854775807, int 1] (.symbol "Nil")) = none := by
  unfold runFold spineOf
  rw [readSpine_build sumSpec _ nil_end]
  decide

/-- **Where the forward bound fails, the exact fold answers**:
`(Cons 9223372036854775807 (Cons -1 (Cons 1 Nil)))` has right partial sums
`1`, `0` and `9223372036854775807`, all machine integers. -/
theorem bound_fails_exact_answers :
    runFold sumSpec (spineOf [int 9223372036854775807, int (-1), int 1] (.symbol "Nil")) =
      some 9223372036854775807 := by
  unfold runFold spineOf
  rw [readSpine_build sumSpec _ nil_end]
  decide

/-- The least machine integer is reached exactly:
`(Cons -9223372036854775807 (Cons -1 Nil))` answers `INT64_MIN`. -/
theorem least_answer :
    runFold sumSpec (spineOf [int (-9223372036854775807), int (-1)] (.symbol "Nil")) =
      some (-9223372036854775808) := by
  unfold runFold spineOf
  rw [readSpine_build sumSpec _ nil_end]
  decide

/-- `(= (step Nil) -10)` and `(= (step (Cons $x $xs)) (+ 4611686018427387904 (step $xs)))`:
a sum of a literal step. -/
def stepSpec : Spec := ⟨"Nil", "Cons", 1, 0, .add, none, 4611686018427387904, false, -10⟩

/-- **A literal sum may decline where the exact fold answers**: on two cells
the product `2 · 2⁶²` leaves the machine integers, while every right partial
sum, `-10`, `2⁶² - 10` and `2⁶³ - 10`, is one. The equations then run and
answer the same value: the decline costs time, not an answer. -/
theorem literal_sum_declines_early :
    runFold stepSpec (stepSpec.family.build ⟨[⟨([.symbol "a"], []), rfl, rfl⟩,
        ⟨([.symbol "b"], []), rfl, rfl⟩], .symbol "Nil"⟩) = none ∧
      runExact stepSpec (stepSpec.family.build ⟨[⟨([.symbol "a"], []), rfl, rfl⟩,
        ⟨([.symbol "b"], []), rfl, rfl⟩], .symbol "Nil"⟩) = some 9223372036854775798 := by
  unfold runFold runExact
  rw [readSpine_build stepSpec _ rfl]
  constructor <;> decide

/-- Addition with a user equation `(= (+ $a $b) 0)` beside the grounded one:
two answers. -/
def userPlus : Env :=
  ⟨fun op vs => if op = "+" then
      (match vs with
        | [.grounded (.int a), .grounded (.int b)] => {int (a + b), int 0}
        | _ => 0)
    else 0, fun _ _ => 0, fun _ => 0⟩

/-- **A user equation for `+` changes the equations' answers**: `(sum (Cons 1 Nil))`
answers `1` and `0`, where the walk would answer `1`; recognition requires
that no equation names the operation (`PrimExact` fails here). -/
theorem user_plus_breaks :
    versionRun (sumSpec.body userPlus) 2 [spineOf [int 1] (.symbol "Nil")] = {int 1, int 0} ∧
      runFold sumSpec (spineOf [int 1] (.symbol "Nil")) = some 1 ∧ ¬ PrimExact userPlus .add := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [versionRun, spineOf, List.map_cons, List.map_nil, Family.build_cons, Family.build_nil]
    change sumSpec.body userPlus _ [sumSpec.cell (one (int 1)) (.symbol "Nil")] = _
    rw [sumSpec.body_cell userPlus _ sumSpec_wf]
    change (sumSpec.operandVals (one (int 1))).bind
        (fun x => (sumSpec.body userPlus (fun _ => 0) [.symbol sumSpec.nil]).bind fun acc =>
          userPlus.prim "+" [x, acc]) = _
    rw [sumSpec.body_nil]
    decide
  · unfold runFold spineOf
    rw [readSpine_build sumSpec _ nil_end]
    decide
  · intro h
    have hc := congrArg Multiset.card (h 1 0 (by decide) (by decide) (by decide))
    simp [userPlus, Op.name, int] at hc

/-- The grounded addition of the models, exact on all integers, meets
recognition's requirement. -/
theorem plus_exact : PrimExact Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Controls.env .add := by
  intro a b _ _ _
  simp [Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Controls.env,
    Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Controls.ops, plus, Op.name, Op.apply, int]

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RecognizedFolds
