import Mettapedia.GSLT.LanguageDef.Collections.Presentations
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Type judgments as certificates

A type judgment of MeTTa data is **compositional**: the judgment of an
expression is one rule applied to the judgments of its elements, and the
program's declarations enter only at the leaves, as the declared types of a
symbol (`Judgment`, `Judgment.full`). The judgment of `(Cons x acc)` follows
from those of `Cons`, `x` and `acc`.

* **Recorded judgments.** A memo of judgments of immutable terms is valid
  when every recorded judgment is the full one (`Judgment.Valid`). Checking
  with a valid memo, stopping at every recorded subterm, gives the full
  judgment (`Judgment.check_eq`), and recording a computed judgment keeps the
  memo valid (`Judgment.valid_record`).
* **Linear against quadratic.** A loop that builds `(Cons n acc)` and checks
  each new argument visits `3k + 4` nodes at step `k` without a memo, `n`
  steps costing `(3n² + 5n) / 2` in all (`full_total`), and four nodes per
  step with the previous judgment recorded, `4n` in all
  (`incremental_total`). A recorded argument costs one lookup, what a value
  class such as `Number` costs (`Judgment.cost_hit`, `Judgment.cost_leaf`), so
  a structural parameter type is as cheap to test as a value class.
* **Revision.** Judgments are recorded with the program token they were
  computed under, and a lookup under another token misses, so checking under
  any token gives the full judgment of that token's declarations
  (`Judgment.check_scoped`). The judgment of a term depends only on the
  declarations of the symbols it contains (`Judgment.full_congr`), so a
  declaration change need drop only the judgments of the terms that mention
  the changed symbols.
* **The certificate discharges the representation obligations.** When a sort
  is closed at a revision, a judgment of that sort inverts into a cell with
  judged parts or one of the sort's stops (the inversion hypothesis of
  `spine_of_sort`). Then a judged term's maximal spine ends in a stop of the
  sort and its elements are judged (`spine_of_sort`), and every suffix is
  judged as well (`sort_suffix`), so a fold that replaces the recursive calls
  replaces their argument checks with it.

**The probe signature** (`constructors`): `Nil : (List Number)`,
`Cons : (-> Number (List Number) (List Number))`, `Z : Nat`, `S : (-> Nat Nat)`,
judged by `signatureJudgment`. Its list judgment inverts
(`list_inversion`), so a term judged `(List Number)` is the spine of its
numbers ending in `Nil` (`typed_list_spine`), and its numbers are grounded
integers (`number_inversion`): the flat unboxed layout is total on it. A term
judged `Nat` is a numeral, a count (`typed_nat_numeral`).

Controls: a `Cons` chain ending in a symbol other than `Nil` is a spine with
an improper end, and has no list judgment (`Controls.improper_has_no_judgment`);
a chain holding a symbol has no list judgment either
(`Controls.symbol_element_has_no_judgment`); the build loop's arguments are
pairwise distinct terms, so the recorded judgment that serves step `k + 1` is
the one recorded at step `k` and no other (`acc_injective`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCertificates

open Mettapedia.Languages.MeTTa.OSLFCore
open Presentations (nodes nodesAll Family binary unary numeral)

universe u v w

/-! ## Compositional judgments -/

/-- A compositional judgment: declarations `σ` enter at the leaves, and an
expression's judgment is one rule applied to its elements' judgments. -/
structure Judgment (Sig : Type u) (J : Type v) where
  leaf : Sig → Atom → J
  node : List J → J

namespace Judgment

variable {Sig : Type u} {J : Type v}

mutual
/-- The full judgment: every node is visited. -/
def full (R : Judgment Sig J) (σ : Sig) : Atom → J
  | .expression xs => R.node (fullAll R σ xs)
  | .symbol s => R.leaf σ (.symbol s)
  | .var x => R.leaf σ (.var x)
  | .grounded g => R.leaf σ (.grounded g)

def fullAll (R : Judgment Sig J) (σ : Sig) : List Atom → List J
  | [] => []
  | x :: xs => full R σ x :: fullAll R σ xs
end

theorem fullAll_eq_map (R : Judgment Sig J) (σ : Sig) (xs : List Atom) :
    fullAll R σ xs = xs.map (full R σ) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [fullAll, ih, List.map_cons]

theorem full_expression (R : Judgment Sig J) (σ : Sig) (xs : List Atom) :
    full R σ (.expression xs) = R.node (xs.map (full R σ)) := by
  rw [full, fullAll_eq_map]

/-- Judgments recorded for terms. -/
abbrev Memo (J : Type v) := Atom → Option J

/-- Every recorded judgment is the full judgment. -/
def Valid (R : Judgment Sig J) (σ : Sig) (m : Memo J) : Prop :=
  ∀ t j, m t = some j → j = full R σ t

mutual
/-- Check with recorded judgments: a recorded expression is not entered. -/
def check (R : Judgment Sig J) (σ : Sig) (m : Memo J) : Atom → J
  | .expression xs =>
      match m (.expression xs) with
      | some j => j
      | none => R.node (checkAll R σ m xs)
  | .symbol s => R.leaf σ (.symbol s)
  | .var x => R.leaf σ (.var x)
  | .grounded g => R.leaf σ (.grounded g)

def checkAll (R : Judgment Sig J) (σ : Sig) (m : Memo J) : List Atom → List J
  | [] => []
  | x :: xs => check R σ m x :: checkAll R σ m xs
end

mutual
/-- **The incremental check is the full check.** -/
theorem check_eq (R : Judgment Sig J) (σ : Sig) (m : Memo J) (valid : Valid R σ m) :
    ∀ t, check R σ m t = full R σ t
  | .expression xs => by
      cases h : m (.expression xs) with
      | some j => simp only [check, h]; exact valid _ _ h
      | none => simp only [check, h, full, checkAll_eq R σ m valid xs]
  | .symbol _ => rfl
  | .var _ => rfl
  | .grounded _ => rfl

theorem checkAll_eq (R : Judgment Sig J) (σ : Sig) (m : Memo J) (valid : Valid R σ m) :
    ∀ xs, checkAll R σ m xs = fullAll R σ xs
  | [] => rfl
  | x :: xs => by
      simp only [checkAll, fullAll, check_eq R σ m valid x, checkAll_eq R σ m valid xs]
end

/-- Record the full judgment of a term. -/
def record (R : Judgment Sig J) (σ : Sig) (m : Memo J) (t : Atom) : Memo J :=
  fun t' => if t' = t then some (full R σ t) else m t'

theorem valid_record (R : Judgment Sig J) (σ : Sig) {m : Memo J} (valid : Valid R σ m)
    (t : Atom) : Valid R σ (record R σ m t) := by
  intro t' j h
  unfold record at h
  split_ifs at h with same
  · cases h
    rw [same]
  · exact valid t' j h

/-- The empty memo is valid. -/
theorem valid_empty (R : Judgment Sig J) (σ : Sig) : Valid R σ (fun _ => none) := by
  intro t j h
  cases h

/-! ### Cost: nodes visited -/

mutual
/-- The nodes a check visits. -/
def cost (m : Memo J) : Atom → ℕ
  | .expression xs =>
      match m (.expression xs) with
      | some _ => 1
      | none => costAll m xs + 1
  | .symbol _ => 1
  | .var _ => 1
  | .grounded _ => 1

def costAll (m : Memo J) : List Atom → ℕ
  | [] => 0
  | x :: xs => cost m x + costAll m xs
end

mutual
/-- Without a memo a check visits every node. -/
theorem cost_empty : ∀ t : Atom, cost (fun _ => (none : Option J)) t = nodes t
  | .expression xs => by simp only [cost, nodes, costAll_empty xs]
  | .symbol _ => rfl
  | .var _ => rfl
  | .grounded _ => rfl

theorem costAll_empty : ∀ xs : List Atom, costAll (fun _ => (none : Option J)) xs = nodesAll xs
  | [] => rfl
  | x :: xs => by simp only [costAll, nodesAll, cost_empty x, costAll_empty xs]
end

/-- A recorded argument costs one lookup. -/
theorem cost_hit {m : Memo J} {xs : List Atom} {j : J} (h : m (.expression xs) = some j) :
    cost m (.expression xs) = 1 := by
  simp only [cost, h]

/-- A leaf, such as a number tested against a value class, costs one step. -/
theorem cost_leaf (m : Memo J) (g : GroundedValue) : cost m (.grounded g) = 1 := rfl

/-! ### Revision -/

/-- Judgments recorded with the program token under which they were computed. -/
abbrev ScopedMemo (Tok : Type w) (J : Type v) := Atom → Option (Tok × J)

/-- The recorded judgments that belong to one token. -/
def lookup {Tok : Type w} [DecidableEq Tok] (tok : Tok) (m : ScopedMemo Tok J) : Memo J :=
  fun t => match m t with
    | some (tok', j) => if tok' = tok then some j else none
    | none => none

/-- Every recorded judgment is the full judgment of its own token's
declarations. -/
def ScopedValid {Tok : Type w} (R : Judgment Sig J) (sig : Tok → Sig) (m : ScopedMemo Tok J) :
    Prop :=
  ∀ t tok j, m t = some (tok, j) → j = full R (sig tok) t

theorem lookup_valid {Tok : Type w} [DecidableEq Tok] (R : Judgment Sig J) (sig : Tok → Sig)
    {m : ScopedMemo Tok J} (valid : ScopedValid R sig m) (tok : Tok) :
    Valid R (sig tok) (lookup tok m) := by
  intro t j h
  cases found : m t with
  | none => simp [lookup, found] at h
  | some p =>
      obtain ⟨tok', j'⟩ := p
      simp only [lookup, found] at h
      split_ifs at h with same
      cases h
      subst same
      exact valid t _ _ found

/-- **Soundness under revision.** Checking under any token gives the full
judgment of that token's declarations: judgments recorded under another
token are not used. -/
theorem check_scoped {Tok : Type w} [DecidableEq Tok] (R : Judgment Sig J) (sig : Tok → Sig)
    {m : ScopedMemo Tok J} (valid : ScopedValid R sig m) (tok : Tok) (t : Atom) :
    check R (sig tok) (lookup tok m) t = full R (sig tok) t :=
  check_eq R (sig tok) _ (lookup_valid R sig valid tok) t

mutual
/-- The leaves of a term. -/
def leaves : Atom → List Atom
  | .expression xs => leavesAll xs
  | .symbol s => [.symbol s]
  | .var x => [.var x]
  | .grounded g => [.grounded g]

def leavesAll : List Atom → List Atom
  | [] => []
  | x :: xs => leaves x ++ leavesAll xs
end

mutual
/-- **A judgment depends only on the declarations of the symbols in its
term.** -/
theorem full_congr (R : Judgment Sig J) {σ σ' : Sig} :
    ∀ t, (∀ ℓ ∈ leaves t, R.leaf σ ℓ = R.leaf σ' ℓ) → full R σ t = full R σ' t
  | .expression xs, same => by
      simp only [full]
      rw [fullAll_congr R xs (by simpa [leaves] using same)]
  | .symbol s, same => same _ (by simp [leaves])
  | .var x, same => same _ (by simp [leaves])
  | .grounded g, same => same _ (by simp [leaves])

theorem fullAll_congr (R : Judgment Sig J) {σ σ' : Sig} :
    ∀ xs, (∀ ℓ ∈ leavesAll xs, R.leaf σ ℓ = R.leaf σ' ℓ) → fullAll R σ xs = fullAll R σ' xs
  | [], _ => rfl
  | x :: xs, same => by
      simp only [fullAll]
      rw [full_congr R x (fun ℓ h => same ℓ (by simp [leavesAll, h])),
        fullAll_congr R xs (fun ℓ h => same ℓ (by simp [leavesAll, h]))]
end

end Judgment

/-! ## The build loop: linear against quadratic -/

open Judgment

/-- `(Cons x r)`. -/
abbrev cell (x r : Atom) : Atom := .expression [.symbol "Cons", x, r]

/-- The accumulator after `k` steps of `(build $n $acc)`. -/
def acc : ℕ → Atom
  | 0 => .symbol "Nil"
  | k + 1 => cell (.grounded (.int (k + 1))) (acc k)

theorem nodes_cell (x r : Atom) : nodes (cell x r) = nodes x + nodes r + 2 := by
  simp only [nodes, nodesAll]
  omega

theorem nodes_acc : ∀ k, nodes (acc k) = 3 * k + 1
  | 0 => rfl
  | k + 1 => by
      rw [acc, nodes_cell, nodes_acc k]
      simp only [nodes]
      omega

/-- The accumulators are pairwise distinct terms. -/
theorem acc_injective : Function.Injective acc := by
  intro i k same
  have := congrArg nodes same
  rw [nodes_acc, nodes_acc] at this
  omega

variable {Sig : Type u} {J : Type v}

/-- The memo after step `k`: the judgments of the accumulators `0 … k`. -/
def memoUpTo (R : Judgment Sig J) (σ : Sig) : ℕ → Memo J
  | 0 => record R σ (fun _ => none) (acc 0)
  | k + 1 => record R σ (memoUpTo R σ k) (acc (k + 1))

theorem memoUpTo_valid (R : Judgment Sig J) (σ : Sig) : ∀ k, Valid R σ (memoUpTo R σ k)
  | 0 => valid_record R σ (valid_empty R σ) _
  | k + 1 => valid_record R σ (memoUpTo_valid R σ k) _

theorem memoUpTo_hit (R : Judgment Sig J) (σ : Sig) :
    ∀ k, ∃ j, memoUpTo R σ k (acc k) = some j
  | 0 => ⟨full R σ (acc 0), by simp [memoUpTo, record]⟩
  | k + 1 => ⟨full R σ (acc (k + 1)), by simp [memoUpTo, record]⟩

theorem memoUpTo_miss (R : Judgment Sig J) (σ : Sig) :
    ∀ k i, k < i → memoUpTo R σ k (acc i) = none
  | 0, i, lt => by
      simp only [memoUpTo, record]
      rw [if_neg (fun h => absurd (acc_injective h) (by omega))]
  | k + 1, i, lt => by
      simp only [memoUpTo, record]
      rw [if_neg (fun h => absurd (acc_injective h) (by omega))]
      exact memoUpTo_miss R σ k i (by omega)

/-- With the previous accumulator recorded, a step visits four nodes. -/
theorem cost_step (R : Judgment Sig J) (σ : Sig) (k : ℕ) :
    cost (memoUpTo R σ k) (acc (k + 1)) = 4 := by
  have miss := memoUpTo_miss R σ k (k + 1) (by omega)
  have previous : cost (memoUpTo R σ k) (acc k) = 1 := by
    cases k with
    | zero => rfl
    | succ k =>
        obtain ⟨j, hit⟩ := memoUpTo_hit R σ (k + 1)
        rw [show acc (k + 1) = cell (.grounded (.int (k + 1))) (acc k) from rfl] at hit ⊢
        exact cost_hit hit
  rw [show acc (k + 1) = cell (.grounded (.int (k + 1))) (acc k) from rfl] at miss ⊢
  simp only [cost, miss, costAll]
  omega

/-- Without a memo, step `k` visits `3k + 4` nodes. -/
theorem cost_full_step (k : ℕ) :
    cost (fun _ => (none : Option J)) (acc (k + 1)) = 3 * k + 4 := by
  rw [cost_empty, nodes_acc]
  omega

/-- **Linear**: four nodes per step with recorded judgments. -/
theorem incremental_total (R : Judgment Sig J) (σ : Sig) (n : ℕ) :
    ∑ k ∈ Finset.range n, cost (memoUpTo R σ k) (acc (k + 1)) = 4 * n := by
  simp [cost_step, mul_comm]

/-- **Quadratic**: `(3n² + 5n) / 2` nodes in all without them. -/
theorem full_total (n : ℕ) :
    2 * ∑ k ∈ Finset.range n, cost (fun _ => (none : Option J)) (acc (k + 1)) = 3 * n * n + 5 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, cost_full_step]
      ring

/-! ## The certificate discharges the representation obligations -/

section Certificate

variable {T : Type u} {F : Type v} (P : Family T F)

/-- **A judged term is a judged spine.** If every judged term is a cell with a
judged element and a judged rest, or a stop of the sort, then a judged
term's maximal spine ends in a stop of the sort and holds judged elements. -/
theorem spine_of_sort (HasSort : T → Prop) (HasElem : F → Prop) (Stop : T → Prop)
    (inversion : ∀ t, HasSort t →
      (∃ f r, P.uncell t = some (f, r) ∧ HasElem f ∧ HasSort r) ∨ (P.uncell t = none ∧ Stop t))
    (t : T) (sorted : HasSort t) :
    Stop (P.spine t).stop ∧ ∀ f ∈ (P.spine t).elems, HasElem f := by
  induction h : P.rank t using Nat.strong_induction_on generalizing t with
  | _ n ih =>
      rcases inversion t sorted with ⟨f, r, hu, hf, hr⟩ | ⟨hu, hs⟩
      · obtain ⟨stop, elems⟩ := ih (P.rank r) (h ▸ P.rank_lt hu) r hr rfl
        rw [P.spine_of_some hu]
        refine ⟨stop, fun g hg => ?_⟩
        rcases List.mem_cons.mp hg with rfl | hg
        · exact hf
        · exact elems g hg
      · rw [P.spine_of_none hu]
        exact ⟨hs, fun g hg => absurd hg (List.not_mem_nil)⟩

/-- **Every suffix of a judged spine is judged**: the checks of the
recursive calls that a fold replaces hold already. -/
theorem sort_suffix (HasSort : T → Prop) (HasElem : F → Prop) (Stop : T → Prop)
    (inversion : ∀ t, HasSort t →
      (∃ f r, P.uncell t = some (f, r) ∧ HasElem f ∧ HasSort r) ∨ (P.uncell t = none ∧ Stop t))
    (fs : List F) (e : T) (sorted : HasSort (P.build ⟨fs, e⟩)) (i : ℕ) :
    HasSort (P.build ⟨fs.drop i, e⟩) := by
  induction fs generalizing i with
  | nil => simpa using sorted
  | cons f fs ih =>
      cases i with
      | zero => simpa using sorted
      | succ i =>
          rw [List.drop_succ_cons]
          apply ih _ i
          rcases inversion _ sorted with ⟨f', r, hu, -, hr⟩ | ⟨hu, -⟩
          · rw [Family.build_cons, P.uncell_cell] at hu
            cases hu
            exact hr
          · rw [Family.build_cons, P.uncell_cell] at hu
            cases hu

end Certificate

/-! ## The probe signature -/

/-- The base types of the probes. -/
inductive Base
  | number
  | list
  | nat
  deriving DecidableEq, Repr

/-- A type: parameter sorts and a result sort; a value's type has no
parameters. -/
abbrev Ty := List Base × Base

/-- Whether arguments with these judgments fit these parameters. -/
def accepts : List Base → List (List Ty) → Bool
  | [], [] => true
  | p :: ps, j :: js => decide (([], p) ∈ j) && accepts ps js
  | _, _ => false

/-- The results of applying the arrow types among `types` to arguments with
these judgments. -/
def applyTypes (types : List Ty) (args : List (List Ty)) : List Ty :=
  (types.filter fun τ => !τ.1.isEmpty && accepts τ.1 args).map fun τ => ([], τ.2)

/-- First-order typing: a symbol has its declared types, an integer is a
`Number`, and an application has the results of its head's arrow types that
fit its arguments. -/
def signatureJudgment : Judgment (String → List Ty) (List Ty) where
  leaf σ
    | .symbol c => σ c
    | .grounded (.int _) => [([], .number)]
    | _ => []
  node
    | [] => []
    | head :: args => applyTypes head args

/-- The constructor declarations of the probes. -/
def constructors (c : String) : List Ty :=
  if c = "Nil" then [([], .list)]
  else if c = "Cons" then [([.number, .list], .list)]
  else if c = "Z" then [([], .nat)]
  else if c = "S" then [([.nat], .nat)]
  else []

/-- The judgment of the probes. -/
abbrev judge (t : Atom) : List Ty := full signatureJudgment constructors t

theorem judge_expression_cons (head : Atom) (args : List Atom) :
    judge (.expression (head :: args)) = applyTypes (judge head) (args.map judge) := by
  rw [judge, full_expression]
  rfl

/-- Only a declared symbol has an arrow type. -/
theorem arrow_source {h : Atom} {τ : Ty} (member : τ ∈ judge h) (arrow : τ.1 ≠ []) :
    ∃ c, h = .symbol c ∧ τ ∈ constructors c := by
  match h with
  | .symbol c => exact ⟨c, rfl, member⟩
  | .var _ => simp [judge, full, signatureJudgment] at member
  | .grounded g =>
      cases g <;> simp [judge, full, signatureJudgment] at member
      exact absurd (congrArg Prod.fst member) arrow
  | .expression [] => simp [judge, full, fullAll, signatureJudgment] at member
  | .expression (head :: args) =>
      rw [judge_expression_cons] at member
      simp only [applyTypes, List.mem_map] at member
      obtain ⟨σ, -, rfl⟩ := member
      exact absurd rfl arrow

theorem constructors_list {c : String} {τ : Ty} (member : τ ∈ constructors c)
    (result : τ.2 = .list) :
    (c = "Nil" ∧ τ = ([], .list)) ∨ (c = "Cons" ∧ τ = ([.number, .list], .list)) := by
  unfold constructors at member
  split_ifs at member with h₁ h₂ h₃ h₄ <;> simp_all

theorem constructors_nat {c : String} {τ : Ty} (member : τ ∈ constructors c)
    (result : τ.2 = .nat) :
    (c = "Z" ∧ τ = ([], .nat)) ∨ (c = "S" ∧ τ = ([.nat], .nat)) := by
  unfold constructors at member
  split_ifs at member with h₁ h₂ h₃ h₄ <;> simp_all

theorem constructors_number {c : String} {τ : Ty} (member : τ ∈ constructors c) :
    τ.2 ≠ .number := by
  unfold constructors at member
  split_ifs at member <;> simp_all

/-- An application judged with result `s` comes from a declared arrow of its
head that fits its arguments. -/
theorem application_source {head : Atom} {args : List Atom} {s : Base}
    (member : ([], s) ∈ judge (.expression (head :: args))) :
    ∃ c ps, head = .symbol c ∧ (ps, s) ∈ constructors c ∧ ps ≠ [] ∧
      accepts ps (args.map judge) = true := by
  rw [judge_expression_cons] at member
  simp only [applyTypes, List.mem_map, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, Prod.mk.injEq] at member
  obtain ⟨⟨ps, s'⟩, ⟨mem, nonempty, fits⟩, -, rfl⟩ := member
  obtain ⟨c, rfl, declared⟩ := arrow_source mem nonempty
  exact ⟨c, ps, rfl, declared, nonempty, fits⟩

/-- **The list judgment inverts**: `Nil`, or `Cons` of a number and a list. -/
theorem list_inversion (t : Atom) (judged : ([], Base.list) ∈ judge t) :
    t = .symbol "Nil" ∨ ∃ x r, t = cell x r ∧ ([], Base.number) ∈ judge x ∧
      ([], Base.list) ∈ judge r := by
  match t with
  | .symbol c =>
      left
      rcases constructors_list (τ := ([], .list)) judged rfl with ⟨rfl, -⟩ | ⟨-, h⟩
      · rfl
      · simp at h
  | .var _ => simp [judge, full, signatureJudgment] at judged
  | .grounded g => cases g <;> simp [judge, full, signatureJudgment] at judged
  | .expression [] => simp [judge, full, fullAll, signatureJudgment] at judged
  | .expression (head :: args) =>
      right
      obtain ⟨c, ps, rfl, declared, nonempty, fits⟩ := application_source judged
      rcases constructors_list declared rfl with ⟨-, h⟩ | ⟨rfl, h⟩
      · simp only [Prod.mk.injEq] at h
        exact absurd h.1 nonempty
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        match args, fits with
        | [x, r], fits =>
            simp only [accepts, List.map_cons, List.map_nil, Bool.and_eq_true,
              decide_eq_true_eq] at fits
            exact ⟨x, r, rfl, fits.1, fits.2.1⟩
        | [], fits | [_], fits | _ :: _ :: _ :: _, fits => simp [accepts] at fits

/-- **The `Nat` judgment inverts**: `Z`, or `S` of a `Nat`. -/
theorem nat_inversion (t : Atom) (judged : ([], Base.nat) ∈ judge t) :
    t = .symbol "Z" ∨ ∃ r, t = .expression [.symbol "S", r] ∧ ([], Base.nat) ∈ judge r := by
  match t with
  | .symbol c =>
      left
      rcases constructors_nat (τ := ([], .nat)) judged rfl with ⟨rfl, -⟩ | ⟨-, h⟩
      · rfl
      · simp at h
  | .var _ => simp [judge, full, signatureJudgment] at judged
  | .grounded g => cases g <;> simp [judge, full, signatureJudgment] at judged
  | .expression [] => simp [judge, full, fullAll, signatureJudgment] at judged
  | .expression (head :: args) =>
      right
      obtain ⟨c, ps, rfl, declared, nonempty, fits⟩ := application_source judged
      rcases constructors_nat declared rfl with ⟨-, h⟩ | ⟨rfl, h⟩
      · simp only [Prod.mk.injEq] at h
        exact absurd h.1 nonempty
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        match args, fits with
        | [r], fits =>
            simp only [accepts, List.map_cons, List.map_nil, Bool.and_eq_true,
              decide_eq_true_eq] at fits
            exact ⟨r, rfl, fits.1⟩
        | [], fits | _ :: _ :: _, fits => simp [accepts] at fits

/-- **Judged numbers are grounded integers**: the elements unbox. -/
theorem number_inversion (t : Atom) (judged : ([], Base.number) ∈ judge t) :
    ∃ n, t = .grounded (.int n) := by
  match t with
  | .symbol c => exact absurd rfl (constructors_number (τ := ([], .number)) judged)
  | .var _ => simp [judge, full, signatureJudgment] at judged
  | .grounded g =>
      cases g with
      | int n => exact ⟨n, rfl⟩
      | _ => simp [judge, full, signatureJudgment] at judged
  | .expression [] => simp [judge, full, fullAll, signatureJudgment] at judged
  | .expression (head :: args) =>
      obtain ⟨c, ps, -, declared, -, -⟩ := application_source judged
      exact absurd rfl (constructors_number declared)

/-- **A term judged `(List Number)` is the spine of its numbers ending in
`Nil`**: the declarations of `Nil` and `Cons` discharge the spine shape, the
recursive position, the terminal and the element class. -/
theorem typed_list_spine (t : Atom) (judged : ([], Base.list) ∈ judge t) :
    (binary "Cons").spine t = ⟨((binary "Cons").spine t).elems, .symbol "Nil"⟩ ∧
      ∀ x ∈ ((binary "Cons").spine t).elems, ∃ n, x = .grounded (.int n) := by
  have certified := spine_of_sort (binary "Cons") (fun t => ([], Base.list) ∈ judge t)
    (fun x => ([], Base.number) ∈ judge x) (fun t => t = .symbol "Nil")
    (fun t h => by
      rcases list_inversion t h with rfl | ⟨x, r, rfl, hx, hr⟩
      · exact .inr ⟨rfl, rfl⟩
      · exact .inl ⟨x, r, (binary "Cons").uncell_cell x r, hx, hr⟩)
    t judged
  refine ⟨?_, fun x hx => number_inversion x (certified.2 x hx)⟩
  rw [← certified.1]

/-- **A term judged `Nat` is a numeral**: its count represents it. -/
theorem typed_nat_numeral (t : Atom) (judged : ([], Base.nat) ∈ judge t) :
    ∃ k, t = numeral "S" (.symbol "Z") k := by
  have certified := spine_of_sort (unary "S") (fun t => ([], Base.nat) ∈ judge t)
    (fun _ => True) (fun t => t = .symbol "Z")
    (fun t h => by
      rcases nat_inversion t h with rfl | ⟨r, rfl, hr⟩
      · exact .inr ⟨rfl, rfl⟩
      · exact .inl ⟨(), r, (unary "S").uncell_cell () r, trivial, hr⟩)
    t judged
  refine ⟨((unary "S").spine t).elems.length, ?_⟩
  have units : ((unary "S").spine t).elems = List.replicate ((unary "S").spine t).elems.length () :=
    List.eq_replicate_iff.mpr ⟨rfl, fun _ _ => rfl⟩
  conv_lhs => rw [← (unary "S").build_spine t]
  unfold numeral
  rw [← certified.1, ← units]

/-! ## Controls -/

namespace Controls

/-- `(Cons 1 foo)` is a spine with the improper end `foo`, and it has no list
judgment. -/
theorem improper_has_no_judgment :
    (binary "Cons").spine (cell (.grounded (.int 1)) (.symbol "foo")) =
        ⟨[.grounded (.int 1)], .symbol "foo"⟩ ∧
      ([], Base.list) ∉ judge (cell (.grounded (.int 1)) (.symbol "foo")) := by
  refine ⟨?_, ?_⟩
  · rw [show cell (.grounded (.int 1)) (.symbol "foo") =
        (binary "Cons").cell (.grounded (.int 1)) (.symbol "foo") from rfl, Family.spine_cell,
      (binary "Cons").spine_of_none (t := .symbol "foo") rfl]
  · intro h
    rcases list_inversion _ h with h | ⟨x, r, same, -, hr⟩
    · cases h
    · simp only [cell, Atom.expression.injEq, List.cons.injEq] at same
      obtain ⟨-, -, rfl, -⟩ := same
      rcases list_inversion _ hr with h | ⟨_, _, h, -⟩ <;> simp at h

/-- `(Cons a Nil)` holds a symbol where a number is declared: no list
judgment. -/
theorem symbol_element_has_no_judgment :
    ([], Base.list) ∉ judge (cell (.symbol "a") (.symbol "Nil")) := by
  intro h
  rcases list_inversion _ h with h | ⟨x, r, same, hx, -⟩
  · cases h
  · simp only [cell, Atom.expression.injEq, List.cons.injEq] at same
    obtain ⟨-, rfl, -, -⟩ := same
    obtain ⟨n, h⟩ := number_inversion _ hx
    cases h

/-- The judgment of `(Cons 1 (Cons 2 Nil))` is `(List Number)`. -/
theorem two_numbers_judged :
    judge (cell (.grounded (.int 1)) (cell (.grounded (.int 2)) (.symbol "Nil"))) =
      [([], .list)] := by
  decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCertificates
