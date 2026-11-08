import Mettapedia.Logic.LP.Core
import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Finset.Max

/-!
# Ground superposition: literals, clauses, orderings and the inference rules

The ground layer of the superposition calculus (Bachmair–Ganzinger), over the ground terms of a
logic-programming signature.

## The ordering, a parameter with stated properties

The term ordering is any linear, well-founded order on ground terms that is compatible with
contexts and contains the strict subterm relation (`GroundSimplification`). The Knuth–Bendix and
lexicographic path orderings with a total precedence are such orderings on ground terms.

* **Literals** are equations or disequations, oriented with their larger side first (`Lit`). They
  are ordered lexicographically by larger side, then sign (a positive literal below a negative one
  with the same larger side), then smaller side. On oriented literals this is the multiset
  ordering of Bachmair and Ganzinger, which sends `s ≈ t` to `{s, t}` and `s ≉ t` to
  `{s, s, t, t}` (`Lit.lt_iff_multiset`, in `SuperpositionLiterals`).
* **Clauses** are multisets of literals, ordered by the Dershowitz–Manna multiset extension
  (`ClauseLT`). It is well founded (`clauseLT_wf`) and total (`dm_trichotomous`).

## Interpretations and the rules

* An **equality interpretation** is a congruence on ground terms (`Congruence`); a clause holds when
  one of its literals does (`Models`), and `Entails S C` quantifies over every congruence.
* **The rules** (`Inference`): positive and negative superposition, equality resolution and
  equality factoring, each with its ordering side conditions. Every inference has a main premise;
  superposition also has a side premise.
* Every inference is **sound** (`Inference.sound`) and **reductive**: its conclusion is smaller
  than its main premise (`Inference.concl_lt`).
* **Redundancy** (`Redundant`, `RedundantInference`, `Saturated`): a clause, or an inference's
  conclusion, follows from clauses of the set smaller than the clause, or than the main premise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition

open Mettapedia.Logic.LP

/-! ## The Dershowitz–Manna order over a linear order -/

section DershowitzManna

variable {α : Type*} [LinearOrder α]

/-- An element that the smaller side has more often lies below an element of the larger side. -/
theorem dm_count {M N : Multiset α} (lt : M.IsDershowitzMannaLT N) {a : α}
    (more : N.count a < M.count a) : ∃ z ∈ N, a < z := by
  obtain ⟨X, Y, Z, -, rfl, rfl, dominated⟩ := lt
  rw [Multiset.count_add, Multiset.count_add] at more
  obtain ⟨z, inZ, below⟩ := dominated a (Multiset.count_pos.mp (by omega))
  exact ⟨z, Multiset.mem_add.mpr (Or.inr inZ), below⟩

/-- Every element of the smaller side is at most an element of the larger side. -/
theorem dm_le {M N : Multiset α} (lt : M.IsDershowitzMannaLT N) {a : α} (member : a ∈ M) :
    ∃ z ∈ N, a ≤ z := by
  obtain ⟨X, Y, Z, -, rfl, rfl, dominated⟩ := lt
  rcases Multiset.mem_add.mp member with inX | inY
  · exact ⟨a, Multiset.mem_add.mpr (Or.inl inX), le_rfl⟩
  · obtain ⟨z, inZ, below⟩ := dominated a inY
    exact ⟨z, Multiset.mem_add.mpr (Or.inr inZ), below.le⟩

theorem dm_intro (X Y Z : Multiset α) (nonempty : Z ≠ 0) (dominated : ∀ y ∈ Y, ∃ z ∈ Z, y < z) :
    (X + Y).IsDershowitzMannaLT (X + Z) :=
  ⟨X, Y, Z, by simpa [Multiset.empty_eq_zero] using nonempty, rfl, rfl, dominated⟩

/-- **Replacing one element by finitely many smaller ones descends.** -/
theorem dm_replace (X Y : Multiset α) (a : α) (below : ∀ y ∈ Y, y < a) :
    (X + Y).IsDershowitzMannaLT (a ::ₘ X) := by
  have step := dm_intro X Y {a} (Multiset.singleton_ne_zero a)
    (fun y member => ⟨a, Multiset.mem_singleton_self a, below y member⟩)
  have same : X + {a} = a ::ₘ X := by rw [add_comm, Multiset.singleton_add]
  rwa [same] at step

/-- A multiset whose elements all lie below an element of another lies below it. -/
theorem dm_of_all_below (M N : Multiset α) (nonempty : N ≠ 0) (below : ∀ y ∈ M, ∃ z ∈ N, y < z) :
    M.IsDershowitzMannaLT N := by
  have step := dm_intro 0 M N nonempty below
  rwa [zero_add, zero_add] at step

/-- **The Dershowitz–Manna order of a linear order is total.** -/
theorem dm_trichotomous (M N : Multiset α) :
    M.IsDershowitzMannaLT N ∨ M = N ∨ N.IsDershowitzMannaLT M := by
  by_cases same : M = N
  · exact Or.inr (Or.inl same)
  have hM : M = M ∩ N + (M - N) := by rw [add_comm, Multiset.sub_add_inter]
  have hN : N = M ∩ N + (N - M) := by rw [Multiset.inter_comm, add_comm, Multiset.sub_add_inter]
  have nonempty : (M - N) + (N - M) ≠ 0 := by
    intro zero
    apply same
    refine Multiset.ext.mpr fun a => ?_
    have counts := congrArg (Multiset.count a) zero
    rw [Multiset.count_add, Multiset.count_sub, Multiset.count_sub, Multiset.count_zero] at counts
    omega
  have ne_zero_of_mem : ∀ {a : α} {W : Multiset α}, a ∈ W → W ≠ 0 := fun member zero => by
    rw [zero] at member
    exact Multiset.notMem_zero _ member
  obtain ⟨m, mem, top⟩ := Finset.exists_max_image ((M - N) + (N - M)).toFinset id
    (Multiset.toFinset_nonempty.mpr nonempty)
  rw [Multiset.mem_toFinset] at mem
  have apart : ∀ a, a ∈ M - N → a ∉ N - M := by
    intro a one two
    rw [← Multiset.count_pos, Multiset.count_sub] at one two
    omega
  have bounded : ∀ y ∈ (M - N) + (N - M), y ≤ m := fun y member =>
    top y (Multiset.mem_toFinset.mpr member)
  rcases Multiset.mem_add.mp mem with inMN | inNM
  · refine Or.inr (Or.inr ?_)
    have step := dm_intro (M ∩ N) (N - M) (M - N) (ne_zero_of_mem inMN)
      (fun y member => ⟨m, inMN, lt_of_le_of_ne (bounded y (Multiset.mem_add.mpr (Or.inr member)))
        (fun same => apart m inMN (same ▸ member))⟩)
    rwa [← hN, ← hM] at step
  · refine Or.inl ?_
    have step := dm_intro (M ∩ N) (M - N) (N - M) (ne_zero_of_mem inNM)
      (fun y member => ⟨m, inNM, lt_of_le_of_ne (bounded y (Multiset.mem_add.mpr (Or.inl member)))
        (fun same => apart m (same ▸ member) inNM)⟩)
    rwa [← hN, ← hM] at step

theorem dm_irrefl [WellFoundedLT α] (M : Multiset α) : ¬ M.IsDershowitzMannaLT M :=
  fun lt => (Multiset.wellFounded_isDershowitzMannaLT (α := α)).asymmetric M M lt lt

end DershowitzManna

/-! ## Literals -/

/-- **A ground literal**, an equation (`negative = false`) or a disequation, oriented with its
larger side first. -/
@[ext] structure Lit (T : Type*) [LinearOrder T] where
  lhs : T
  negative : Bool
  rhs : T
  oriented : rhs ≤ lhs

namespace Lit

variable {T : Type*} [LinearOrder T]

/-- The comparison key: larger side, then sign (positive first), then smaller side. -/
def key (L : Lit T) : T ×ₗ (Bool ×ₗ T) := toLex (L.lhs, toLex (L.negative, L.rhs))

theorem key_injective : Function.Injective (key : Lit T → T ×ₗ (Bool ×ₗ T)) := by
  intro L M same
  simp only [key, toLex_inj, Prod.mk.injEq] at same
  exact Lit.ext same.1 same.2.1 same.2.2

instance : LinearOrder (Lit T) := LinearOrder.lift' key key_injective

instance [WellFoundedLT T] : WellFoundedLT (Lit T) := ⟨InvImage.wf key wellFounded_lt⟩

theorem lt_iff {L M : Lit T} : L < M ↔ L.lhs < M.lhs ∨ L.lhs = M.lhs ∧
    (L.negative < M.negative ∨ L.negative = M.negative ∧ L.rhs < M.rhs) := by
  show key L < key M ↔ _
  simp only [key, Prod.Lex.toLex_lt_toLex]

theorem bool_lt_iff {a b : Bool} : a < b ↔ a = false ∧ b = true := by
  cases a <;> cases b <;> decide

/-- A literal with a smaller larger side is smaller. -/
theorem lt_of_lhs_lt {L M : Lit T} (lt : L.lhs < M.lhs) : L < M := lt_iff.mpr (Or.inl lt)

theorem lhs_le_of_le {L M : Lit T} (le : L ≤ M) : L.lhs ≤ M.lhs := by
  rcases le.lt_or_eq with lt | rfl
  · rcases lt_iff.mp lt with lt | ⟨same, -⟩
    · exact lt.le
    · exact same.le
  · exact le_rfl

/-- **The positive literal `l ≈ r`**, given `r ≤ l`. -/
def pos (l r : T) (h : r ≤ l) : Lit T := ⟨l, false, r, h⟩

/-- **A literal of the given sign on two terms in either order.** -/
def make (negative : Bool) (a b : T) : Lit T := ⟨max a b, negative, min a b, min_le_max⟩

@[simp] theorem make_lhs (negative : Bool) (a b : T) : (make negative a b).lhs = max a b := rfl
@[simp] theorem make_negative (negative : Bool) (a b : T) : (make negative a b).negative = negative := rfl

/-- Literals below a positive literal: smaller larger side, or the same larger side, positive, and
a smaller or equal smaller side. -/
theorem le_pos_iff {M : Lit T} {l r : T} {h : r ≤ l} :
    M ≤ pos l r h ↔ M.lhs < l ∨ (M.lhs = l ∧ M.negative = false ∧ M.rhs ≤ r) := by
  constructor
  · intro le
    rcases le.lt_or_eq with lt | rfl
    · rcases lt_iff.mp lt with lt | ⟨same, sign⟩
      · exact Or.inl lt
      · refine Or.inr ⟨same, ?_⟩
        rcases sign with sign | ⟨sign, small⟩
        · exact absurd (bool_lt_iff.mp sign).2 (by simp [pos])
        · exact ⟨sign, small.le⟩
    · exact Or.inr ⟨rfl, rfl, le_rfl⟩
  · rintro (lt | ⟨same, sign, small⟩)
    · exact (lt_of_lhs_lt lt).le
    · rcases small.lt_or_eq with small | small
      · exact (lt_iff.mpr (Or.inr ⟨same, Or.inr ⟨sign, small⟩⟩)).le
      · exact le_of_eq (Lit.ext same sign small)

/-- A negative literal below a positive one has a strictly smaller larger side. -/
theorem lhs_lt_of_negative_le_pos {M : Lit T} {l r : T} {h : r ≤ l} (le : M ≤ pos l r h)
    (negative : M.negative = true) : M.lhs < l := by
  rcases le_pos_iff.mp le with lt | ⟨-, sign, -⟩
  · exact lt
  · rw [negative] at sign
    exact absurd sign (by decide)

/-- A positive literal lies below a negative literal with an equal or larger larger side. -/
theorem pos_lt_of_negative {l r : T} {h : r ≤ l} {M : Lit T} (negative : M.negative = true)
    (le : l ≤ M.lhs) : pos l r h < M := by
  rcases le.lt_or_eq with lt | same
  · exact lt_of_lhs_lt lt
  · exact lt_iff.mpr (Or.inr ⟨same, Or.inl (bool_lt_iff.mpr ⟨rfl, negative⟩)⟩)

/-- Two literals with one larger side and one sign compare by their smaller sides. -/
theorem rhs_le_of_le {L M : Lit T} (le : L ≤ M) (same : L.lhs = M.lhs)
    (sign : L.negative = M.negative) : L.rhs ≤ M.rhs := by
  rcases le.lt_or_eq with lt | rfl
  · rcases lt_iff.mp lt with lt | ⟨-, sign' | ⟨-, small⟩⟩
    · exact absurd same lt.ne
    · exact absurd sign (ne_of_lt sign')
    · exact small.le
  · exact le_rfl

/-! ### Truth of a literal in a relation on terms -/

/-- **A literal holds** in a relation on terms: an equation when it relates the sides, a
disequation when it does not. -/
def Holds (R : T → T → Prop) (L : Lit T) : Prop :=
  if L.negative then ¬ R L.lhs L.rhs else R L.lhs L.rhs

theorem holds_of_negative {R : T → T → Prop} {L : Lit T} (negative : L.negative = true) :
    L.Holds R ↔ ¬ R L.lhs L.rhs := by
  simp [Holds, negative]

theorem holds_of_positive {R : T → T → Prop} {L : Lit T} (positive : L.negative = false) :
    L.Holds R ↔ R L.lhs L.rhs := by
  simp [Holds, positive]

/-- In a symmetric relation, a literal made on two terms holds as their equation or disequation. -/
theorem holds_make {R : T → T → Prop} (symm : ∀ a b, R a b → R b a) (negative : Bool) (a b : T) :
    (make negative a b).Holds R ↔ if negative then ¬ R a b else R a b := by
  have sides : R (max a b) (min a b) ↔ R a b := by
    rcases le_total b a with h | h
    · rw [max_eq_left h, min_eq_right h]
    · rw [max_eq_right h, min_eq_left h]
      exact ⟨symm _ _, symm _ _⟩
  cases negative <;> simp [Holds, make, sides]

end Lit

/-! ## Clauses -/

/-- **A ground clause**: a multiset of literals, read as their disjunction. -/
abbrev Clause (T : Type*) [LinearOrder T] := Multiset (Lit T)

section Clauses

variable {T : Type*} [LinearOrder T]

/-- **The clause ordering**: the multiset extension of the literal ordering. -/
def ClauseLT (C D : Clause T) : Prop := C.IsDershowitzMannaLT D

theorem clauseLT_wf [WellFoundedLT T] : WellFounded (ClauseLT (T := T)) :=
  Multiset.wellFounded_isDershowitzMannaLT

theorem clauseLT_trans {C D E : Clause T} (one : ClauseLT C D) (two : ClauseLT D E) : ClauseLT C E :=
  Multiset.IsDershowitzMannaLT.trans one two

theorem clauseLT_irrefl [WellFoundedLT T] (C : Clause T) : ¬ ClauseLT C C := dm_irrefl C

theorem clauseLT_trichotomous (C D : Clause T) : ClauseLT C D ∨ C = D ∨ ClauseLT D C :=
  dm_trichotomous C D

/-- Adding a literal makes a clause larger. -/
theorem clauseLT_cons (C : Clause T) (L : Lit T) : ClauseLT C (L ::ₘ C) := by
  have step := dm_replace C 0 L (fun y member => absurd member (Multiset.notMem_zero y))
  rwa [add_zero] at step

/-- A strict sub-multiset is smaller. -/
theorem clauseLT_of_lt {C D : Clause T} (sub : C ≤ D) (ne : C ≠ D) : ClauseLT C D := by
  obtain ⟨E, rfl⟩ := Multiset.le_iff_exists_add.mp sub
  have nonempty : E ≠ 0 := fun zero => ne (by rw [zero, add_zero])
  have step := dm_intro C 0 E nonempty (fun y member => absurd member (Multiset.notMem_zero y))
  rwa [add_zero] at step

/-- **A clause holds** in a relation on terms when one of its literals does. -/
def Models (R : T → T → Prop) (C : Clause T) : Prop := ∃ L ∈ C, L.Holds R

theorem models_cons {R : T → T → Prop} {L : Lit T} {C : Clause T} :
    Models R (L ::ₘ C) ↔ L.Holds R ∨ Models R C := by
  constructor
  · rintro ⟨M, member, holds⟩
    rcases Multiset.mem_cons.mp member with rfl | inC
    · exact Or.inl holds
    · exact Or.inr ⟨M, inC, holds⟩
  · rintro (holds | ⟨M, member, holds⟩)
    · exact ⟨L, Multiset.mem_cons_self L C, holds⟩
    · exact ⟨M, Multiset.mem_cons_of_mem member, holds⟩

theorem models_add {R : T → T → Prop} {C D : Clause T} :
    Models R (C + D) ↔ Models R C ∨ Models R D := by
  constructor
  · rintro ⟨M, member, holds⟩
    rcases Multiset.mem_add.mp member with inC | inD
    · exact Or.inl ⟨M, inC, holds⟩
    · exact Or.inr ⟨M, inD, holds⟩
  · rintro (⟨M, member, holds⟩ | ⟨M, member, holds⟩)
    · exact ⟨M, Multiset.mem_add.mpr (Or.inl member), holds⟩
    · exact ⟨M, Multiset.mem_add.mpr (Or.inr member), holds⟩

theorem models_of_le {R : T → T → Prop} {C D : Clause T} (sub : C ≤ D) (holds : Models R C) :
    Models R D := by
  obtain ⟨M, member, holds⟩ := holds
  exact ⟨M, Multiset.mem_of_le sub member, holds⟩

/-- The empty clause holds nowhere. -/
theorem not_models_zero (R : T → T → Prop) : ¬ Models R (0 : Clause T) := by
  rintro ⟨M, member, -⟩
  exact Multiset.notMem_zero M member

end Clauses

/-! ## Ground terms: contexts and the ordering -/

section Terms

variable {sig : LPSignature}

/-- **One-hole contexts** of ground terms. -/
inductive Ctx (sig : LPSignature) : Type _ where
  | hole : Ctx sig
  | app (f : sig.functionSymbols) (args : Fin (sig.functionArity f) → GroundTerm sig)
      (position : Fin (sig.functionArity f)) (inner : Ctx sig) : Ctx sig

/-- Fill the hole of a context. -/
def Ctx.fill : Ctx sig → GroundTerm sig → GroundTerm sig
  | .hole, t => t
  | .app f args i inner, t => .app f (Function.update args i (inner.fill t))

/-- Put a context into the hole of another. -/
def Ctx.comp : Ctx sig → Ctx sig → Ctx sig
  | .hole, d => d
  | .app f args i inner, d => .app f args i (inner.comp d)

@[simp] theorem Ctx.fill_hole (t : GroundTerm sig) : (Ctx.hole : Ctx sig).fill t = t := rfl

theorem Ctx.fill_comp (c d : Ctx sig) (t : GroundTerm sig) : (c.comp d).fill t = c.fill (d.fill t) := by
  induction c with
  | hole => rfl
  | app f args i inner ih => simp only [Ctx.comp, Ctx.fill, ih]

/-- **A ground simplification ordering**: compatible with contexts and containing the strict
subterm relation. Together with a linear, well-founded order on ground terms, this is the parameter
of the calculus. -/
class GroundSimplification (sig : LPSignature) [LinearOrder (GroundTerm sig)] : Prop where
  monotone : ∀ (f : sig.functionSymbols) (args : Fin (sig.functionArity f) → GroundTerm sig)
    (i : Fin (sig.functionArity f)) (a : GroundTerm sig), a < args i →
      GroundTerm.app f (Function.update args i a) < GroundTerm.app f args
  subterm : ∀ (f : sig.functionSymbols) (args : Fin (sig.functionArity f) → GroundTerm sig)
    (i : Fin (sig.functionArity f)), args i < GroundTerm.app f args

variable [LinearOrder (GroundTerm sig)] [GroundSimplification sig]

/-- **Compatibility with contexts.** -/
theorem Ctx.fill_lt_fill (c : Ctx sig) {a b : GroundTerm sig} (lt : a < b) : c.fill a < c.fill b := by
  induction c with
  | hole => exact lt
  | app f args i inner ih =>
      have step := GroundSimplification.monotone f (Function.update args i (inner.fill b)) i
        (inner.fill a) (by rw [Function.update_self]; exact ih)
      rw [Function.update_idem] at step
      exact step

/-- **The subterm property.** -/
theorem Ctx.le_fill (c : Ctx sig) (a : GroundTerm sig) : a ≤ c.fill a := by
  induction c with
  | hole => exact le_rfl
  | app f args i inner ih =>
      have step := GroundSimplification.subterm f (Function.update args i (inner.fill a)) i
      rw [Function.update_self] at step
      exact ih.trans step.le

theorem Ctx.lt_fill (c : Ctx sig) (proper : c ≠ .hole) (a : GroundTerm sig) : a < c.fill a := by
  cases c with
  | hole => exact absurd rfl proper
  | app f args i inner =>
      have step := GroundSimplification.subterm f (Function.update args i (inner.fill a)) i
      rw [Function.update_self] at step
      exact (inner.le_fill a).trans_lt step

/-- A context that fills a term back to itself is the hole. -/
theorem Ctx.eq_hole_of_fill_eq (c : Ctx sig) {a : GroundTerm sig} (same : c.fill a = a) :
    c = .hole := by
  by_contra proper
  exact absurd same (c.lt_fill proper a).ne'

end Terms

/-! ## Equality interpretations -/

section Interpretations

variable {sig : LPSignature} [LinearOrder (GroundTerm sig)]

/-- **An equality interpretation** of ground terms: a congruence. -/
structure Congruence (sig : LPSignature) where
  rel : GroundTerm sig → GroundTerm sig → Prop
  equivalence : Equivalence rel
  compatible : ∀ (c : Ctx sig) {a b : GroundTerm sig}, rel a b → rel (c.fill a) (c.fill b)

/-- **Semantic consequence**: every equality interpretation of `S` satisfies `C`. -/
def Entails (S : Set (Clause (GroundTerm sig))) (C : Clause (GroundTerm sig)) : Prop :=
  ∀ I : Congruence sig, (∀ D ∈ S, Models I.rel D) → Models I.rel C

theorem Entails.mono {S S' : Set (Clause (GroundTerm sig))} {C : Clause (GroundTerm sig)}
    (sub : S ⊆ S') (entails : Entails S C) : Entails S' C :=
  fun I holds => entails I fun D member => holds D (sub member)

theorem Entails.of_mem {S : Set (Clause (GroundTerm sig))} {C : Clause (GroundTerm sig)}
    (member : C ∈ S) : Entails S C :=
  fun _ holds => holds C member

end Interpretations

/-! ## The inference rules -/

section Rules

variable {sig : LPSignature} [LinearOrder (GroundTerm sig)]

/-- **The ground superposition calculus.** `Inference side main concl`: an inference with the
optional side premise, the main premise and the conclusion.

* `posSup`: superposition of `l ≈ r ∨ D` into the larger side `c[l]` of the strictly maximal
  positive literal `L` of `L ∨ C`, where `l ≈ r` is strictly maximal in its premise, `l ≻ r`,
  `c[l] ≻ L.rhs`, and `l ≈ r` is smaller than `L`.
* `negSup`: the same into a maximal negative literal.
* `eqRes`: equality resolution on a maximal `s ≉ s`.
* `eqFact`: equality factoring of two positive literals with one larger side, the first maximal. -/
inductive Inference :
    Option (Clause (GroundTerm sig)) → Clause (GroundTerm sig) → Clause (GroundTerm sig) → Prop
  | posSup {l r : GroundTerm sig} (D C : Clause (GroundTerm sig)) (L : Lit (GroundTerm sig))
      (c : Ctx sig) (decreasing : r < l) (sideMax : ∀ M ∈ D, M < Lit.pos l r decreasing.le)
      (positive : L.negative = false) (larger : L.lhs = c.fill l) (strict : L.rhs < L.lhs)
      (mainMax : ∀ M ∈ C, M < L) (smaller : Lit.pos l r decreasing.le < L) :
      Inference (some (Lit.pos l r decreasing.le ::ₘ D)) (L ::ₘ C)
        (Lit.make false (c.fill r) L.rhs ::ₘ (D + C))
  | negSup {l r : GroundTerm sig} (D C : Clause (GroundTerm sig)) (L : Lit (GroundTerm sig))
      (c : Ctx sig) (decreasing : r < l) (sideMax : ∀ M ∈ D, M < Lit.pos l r decreasing.le)
      (negative : L.negative = true) (larger : L.lhs = c.fill l) (strict : L.rhs < L.lhs)
      (mainMax : ∀ M ∈ C, M ≤ L) :
      Inference (some (Lit.pos l r decreasing.le ::ₘ D)) (L ::ₘ C)
        (Lit.make true (c.fill r) L.rhs ::ₘ (D + C))
  | eqRes (C : Clause (GroundTerm sig)) (L : Lit (GroundTerm sig)) (negative : L.negative = true)
      (trivial : L.rhs = L.lhs) (mainMax : ∀ M ∈ C, M ≤ L) :
      Inference none (L ::ₘ C) C
  | eqFact (C : Clause (GroundTerm sig)) (L L' : Lit (GroundTerm sig)) (positive : L.negative = false)
      (positive' : L'.negative = false) (same : L'.lhs = L.lhs) (strict : L.rhs < L.lhs)
      (mainMax : ∀ M ∈ L' ::ₘ C, M ≤ L) :
      Inference none (L ::ₘ L' ::ₘ C) (Lit.make true L.rhs L'.rhs ::ₘ L' ::ₘ C)

/-- **Every inference is sound** for equality interpretations. -/
theorem Inference.sound {side : Option (Clause (GroundTerm sig))} {main concl : Clause (GroundTerm sig)}
    (inference : Inference side main concl) (I : Congruence sig)
    (sideHolds : ∀ D ∈ side, Models I.rel D) (mainHolds : Models I.rel main) :
    Models I.rel concl := by
  have symm : ∀ a b, I.rel a b → I.rel b a := fun _ _ h => I.equivalence.symm h
  cases inference with
  | @posSup l r D C L c decreasing sideMax positive larger strict mainMax smaller =>
      rcases models_cons.mp (sideHolds _ (Option.mem_def.mpr rfl)) with rule | inD
      · rcases models_cons.mp mainHolds with literal | inC
        · rw [Lit.holds_of_positive positive, larger] at literal
          refine models_cons.mpr (Or.inl ?_)
          rw [Lit.holds_make symm]
          have step : I.rel (c.fill r) (c.fill l) :=
            I.compatible c (symm _ _ ((Lit.holds_of_positive rfl).mp rule))
          exact I.equivalence.trans step literal
        · exact models_cons.mpr (Or.inr (models_add.mpr (Or.inr inC)))
      · exact models_cons.mpr (Or.inr (models_add.mpr (Or.inl inD)))
  | @negSup l r D C L c decreasing sideMax negative larger strict mainMax =>
      rcases models_cons.mp (sideHolds _ (Option.mem_def.mpr rfl)) with rule | inD
      · rcases models_cons.mp mainHolds with literal | inC
        · rw [Lit.holds_of_negative negative, larger] at literal
          refine models_cons.mpr (Or.inl ?_)
          rw [Lit.holds_make symm]
          intro related
          have step : I.rel (c.fill l) (c.fill r) := I.compatible c ((Lit.holds_of_positive rfl).mp rule)
          exact literal (I.equivalence.trans step related)
        · exact models_cons.mpr (Or.inr (models_add.mpr (Or.inr inC)))
      · exact models_cons.mpr (Or.inr (models_add.mpr (Or.inl inD)))
  | eqRes C L negative trivial mainMax =>
      rcases models_cons.mp mainHolds with literal | inC
      · rw [Lit.holds_of_negative negative, trivial] at literal
        exact absurd (I.equivalence.refl _) literal
      · exact inC
  | eqFact C L L' positive positive' same strict mainMax =>
      rcases models_cons.mp mainHolds with literal | rest
      · rw [Lit.holds_of_positive positive] at literal
        by_cases sides : I.rel L.rhs L'.rhs
        · refine models_cons.mpr (Or.inr (models_cons.mpr (Or.inl ?_)))
          rw [Lit.holds_of_positive positive', same]
          exact I.equivalence.trans literal sides
        · refine models_cons.mpr (Or.inl ?_)
          rw [Lit.holds_make symm]
          exact sides
      · exact models_cons.mpr (Or.inr rest)

variable [GroundSimplification sig]

/-- **Every inference is reductive**: its conclusion is smaller than its main premise. -/
theorem Inference.concl_lt {side : Option (Clause (GroundTerm sig))} {main concl : Clause (GroundTerm sig)}
    (inference : Inference side main concl) : ClauseLT concl main := by
  cases inference with
  | @posSup l r D C L c decreasing sideMax positive larger strict mainMax smaller =>
      have below : ∀ y ∈ Lit.make false (c.fill r) L.rhs ::ₘ D, y < L := by
        intro y member
        rcases Multiset.mem_cons.mp member with rfl | inD
        · apply Lit.lt_of_lhs_lt
          rw [Lit.make_lhs, larger]
          exact max_lt (c.fill_lt_fill decreasing) (strict.trans_eq larger)
        · exact (sideMax y inD).trans smaller
      have step := dm_replace C _ L below
      rwa [Multiset.add_cons, add_comm C D] at step
  | @negSup l r D C L c decreasing sideMax negative larger strict mainMax =>
      have toL : Lit.pos l r decreasing.le < L :=
        Lit.pos_lt_of_negative negative ((c.le_fill l).trans_eq larger.symm)
      have below : ∀ y ∈ Lit.make true (c.fill r) L.rhs ::ₘ D, y < L := by
        intro y member
        rcases Multiset.mem_cons.mp member with rfl | inD
        · apply Lit.lt_of_lhs_lt
          rw [Lit.make_lhs, larger]
          exact max_lt (c.fill_lt_fill decreasing) (strict.trans_eq larger)
        · exact (sideMax y inD).trans toL
      have step := dm_replace C _ L below
      rwa [Multiset.add_cons, add_comm C D] at step
  | eqRes C L negative trivial mainMax => exact clauseLT_cons _ L
  | eqFact C L L' positive positive' same strict mainMax =>
      have small : L'.rhs ≤ L.rhs :=
        Lit.rhs_le_of_le (mainMax L' (Multiset.mem_cons_self L' C)) same (positive'.trans positive.symm)
      have below : ∀ y ∈ ({Lit.make true L.rhs L'.rhs} : Clause (GroundTerm sig)), y < L := by
        intro y member
        rw [Multiset.mem_singleton] at member
        subst member
        apply Lit.lt_of_lhs_lt
        rw [Lit.make_lhs, max_eq_left small]
        exact strict
      have step := dm_replace (L' ::ₘ C) _ L below
      rwa [add_comm, Multiset.singleton_add] at step

end Rules

/-! ## Redundancy and saturation -/

section Redundancy

variable {sig : LPSignature} [LinearOrder (GroundTerm sig)]

/-- The clauses of `N` smaller than `C`. -/
def lowerSet (N : Set (Clause (GroundTerm sig))) (C : Clause (GroundTerm sig)) :
    Set (Clause (GroundTerm sig)) :=
  {D | D ∈ N ∧ ClauseLT D C}

/-- **A redundant clause** (Bachmair–Ganzinger): it follows from smaller clauses of `N`. -/
def Redundant (N : Set (Clause (GroundTerm sig))) (C : Clause (GroundTerm sig)) : Prop :=
  Entails (lowerSet N C) C

/-- **A redundant inference**: its conclusion follows from clauses of `N` smaller than its main
premise. -/
def RedundantInference (N : Set (Clause (GroundTerm sig))) (main concl : Clause (GroundTerm sig)) :
    Prop :=
  Entails (lowerSet N main) concl

/-- **Saturated up to redundancy**: every inference from clauses of `N` is redundant. -/
def Saturated (N : Set (Clause (GroundTerm sig))) : Prop :=
  ∀ side main concl, Inference side main concl → (∀ D ∈ side, D ∈ N) → main ∈ N →
    RedundantInference N main concl

/-- An inference whose conclusion is in the set is redundant, because the calculus is reductive. -/
theorem RedundantInference.of_mem [GroundSimplification sig] {N : Set (Clause (GroundTerm sig))}
    {side : Option (Clause (GroundTerm sig))} {main concl : Clause (GroundTerm sig)}
    (inference : Inference side main concl) (member : concl ∈ N) : RedundantInference N main concl :=
  Entails.of_mem ⟨member, inference.concl_lt⟩

end Redundancy

#print axioms dm_count
#print axioms dm_le
#print axioms dm_replace
#print axioms dm_of_all_below
#print axioms dm_trichotomous
#print axioms dm_irrefl
#print axioms Lit.key_injective
#print axioms Lit.lt_iff
#print axioms Lit.le_pos_iff
#print axioms Lit.lhs_lt_of_negative_le_pos
#print axioms Lit.pos_lt_of_negative
#print axioms Lit.rhs_le_of_le
#print axioms Lit.holds_make
#print axioms clauseLT_wf
#print axioms clauseLT_trichotomous
#print axioms clauseLT_of_lt
#print axioms models_cons
#print axioms models_add
#print axioms Ctx.fill_comp
#print axioms Ctx.fill_lt_fill
#print axioms Ctx.le_fill
#print axioms Ctx.lt_fill
#print axioms Ctx.eq_hole_of_fill_eq
#print axioms Inference.sound
#print axioms Inference.concl_lt
#print axioms RedundantInference.of_mem

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition
