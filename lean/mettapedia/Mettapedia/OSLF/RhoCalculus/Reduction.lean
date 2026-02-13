import Mettapedia.OSLF.RhoCalculus.Types
import Mettapedia.OSLF.RhoCalculus.StructuralCongruence
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.CategoryTheory.LambdaTheory

/-!
# ρ-Calculus Reduction Semantics (Locally Nameless)

This file defines the reduction relation for the ρ-calculus, connecting
the MeTTaIL COMM rewrite rule to the categorical semantics.

## The COMM Rule

The fundamental reduction in ρ-calculus is communication:

  {n!(q) | for(<-n){p} | ...rest} ~> {p[@q/x] | ...rest}

In locally nameless: the input `for(<-n){p}` is `PInput [n, lambda p]` where
`p` has BVar 0 for the bound variable. The substitution replaces BVar 0
with `NQuote(q)` via `openBVar`.

## References

- Meredith & Stay, "Operational Semantics in Logical Form" Section 4
- Meredith & Radestock, "A Reflective Higher-Order Calculus"
- Aydemir et al., "Engineering Formal Metatheory" (POPL 2008)
-/

namespace Mettapedia.OSLF.RhoCalculus.Reduction

open Mettapedia.OSLF.RhoCalculus
open Mettapedia.OSLF.RhoCalculus.StructuralCongruence
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.CategoryTheory.LambdaTheories

/-! ## The Reduction Relation -/

/-- The one-step reduction relation on ρ-calculus processes.

    p ⇝ q means p reduces to q in one step via the COMM rule
    (or a structural congruence).

    **Design Decision (2026-02-04)**: Reduces is Type-valued, not Prop-valued.

    **Canonical vs Extension Policy (2026-02-13)**:
    This low-level relation intentionally keeps both bag and set congruence
    descent constructors. Canonical-vs-extension behavior is enforced at the
    `LanguageDef`/`langReduces` layer (`rhoCalc` vs `rhoCalcSetExt`) via
    `congruenceCollections`, with theorem-level comparison in
    `Framework/TypeSynthesis.lean`.

    **Locally nameless**: The COMM rule no longer carries a binder name.
    Lambda patterns are `lambda body` where BVar 0 is the bound variable.
    Substitution uses `commSubst` which calls `openBVar 0 (NQuote q) body`.
-/
inductive Reduces : Pattern → Pattern → Type where
  /-- COMM: {n!(q) | for(<-n){p} | ...rest} ⇝ {commSubst p q | ...rest}

      In locally nameless: the input pattern `PInput [n, lambda p]` binds
      BVar 0. The COMM rule substitutes `NQuote(q)` for BVar 0 in `p`.
      No binder name needed — de Bruijn indices handle binding.
  -/
  | comm {n q p : Pattern} {rest : List Pattern} :
      Reduces
        (.collection .hashBag ([.apply "POutput" [n, q],
                                .apply "PInput" [n, .lambda p]] ++ rest) none)
        (.collection .hashBag ([commSubst p q] ++ rest) none)

  /-- DROP: *(@p) ⇝ p -/
  | drop {p : Pattern} :
      Reduces (.apply "PDrop" [.apply "NQuote" [p]]) p

  /-- EQUIV: Reduction modulo structural congruence -/
  | equiv {p p' q q' : Pattern} :
      StructuralCongruence p p' →
      Reduces p' q' →
      StructuralCongruence q' q →
      Reduces p q

  /-- PAR: structural congruence under parallel composition -/
  | par {p q : Pattern} {rest : List Pattern} :
      Reduces p q →
      Reduces (.collection .hashBag (p :: rest) none)
              (.collection .hashBag (q :: rest) none)

  /-- PAR_ANY: reduction at any position in parallel (via permutation) -/
  | par_any {p q : Pattern} {before after : List Pattern} :
      Reduces p q →
      Reduces (.collection .hashBag (before ++ [p] ++ after) none)
              (.collection .hashBag (before ++ [q] ++ after) none)

  /-- PAR_SET: reduction inside set collections -/
  | par_set {p q : Pattern} {rest : List Pattern} :
      Reduces p q →
      Reduces (.collection .hashSet (p :: rest) none)
              (.collection .hashSet (q :: rest) none)

  /-- PAR_SET_ANY: reduction at any position in a set -/
  | par_set_any {p q : Pattern} {before after : List Pattern} :
      Reduces p q →
      Reduces (.collection .hashSet (before ++ [p] ++ after) none)
              (.collection .hashSet (before ++ [q] ++ after) none)

infix:50 " ⇝ " => Reduces

/-! ## Modal Operators via Reduction -/

/-- Possibly: ◇φ = { p | ∃q. p ⇝ q ∧ q ∈ φ } -/
def possiblyProp (φ : Pattern → Prop) : Pattern → Prop :=
  fun p => ∃ q, Nonempty (p ⇝ q) ∧ φ q

/-- Rely: ⧫φ = { p | ∀q. q ⇝ p → q ∈ φ } -/
def relyProp (φ : Pattern → Prop) : Pattern → Prop :=
  fun p => ∀ q, Nonempty (q ⇝ p) → φ q

/-! ## Galois Connection -/

/-- Galois connection: possibly ⊣ rely -/
theorem galois_connection (φ ψ : Pattern → Prop) :
    (∀ p, possiblyProp φ p → ψ p) ↔ (∀ p, φ p → relyProp ψ p) := by
  constructor
  · intro h p hp q hqp
    apply h
    exact ⟨p, hqp, hp⟩
  · intro h p ⟨q, hpq, hq⟩
    exact h q hq p hpq

/-! ## Connecting to Categorical Semantics -/

/-- A predicate on processes (as a Prop-valued function) -/
def ProcessPred := Pattern → Prop

theorem possibly_pointwise (φ : ProcessPred) (p : Pattern) :
    possiblyProp φ p → (∃ q, φ q) := by
  intro ⟨q, _, hq⟩
  exact ⟨q, hq⟩

theorem rely_pointwise (φ : ProcessPred) (p : Pattern) :
    (∀ q, φ q) → relyProp φ p := by
  intro hall q _
  exact hall q

/-! ## Properties of COMM -/

/-- COMM reduces synchronizable terms (constructive witness). -/
def comm_reduces {n q p : Pattern} :
    Σ r, (.collection .hashBag [.apply "POutput" [n, q],
                                .apply "PInput" [n, .lambda p]] none) ⇝ r := by
  use .collection .hashBag [commSubst p q] none
  have h := @Reduces.comm n q p []
  simp only [List.append_nil] at h
  exact h

/-! ## Semantic Value / Normal Form -/

/-- A pattern can step if there exists a one-step reduction from it. -/
def CanStep (p : Pattern) : Prop :=
  ∃ q, Nonempty (p ⇝ q)

/-- A pattern is in normal form if it cannot step (irreducible). -/
def NormalForm (p : Pattern) : Prop :=
  ¬ CanStep p

/-- Value = NormalForm. -/
abbrev Value : Pattern → Prop := NormalForm

theorem step_or_normalForm (p : Pattern) : CanStep p ∨ NormalForm p := by
  exact Classical.em (CanStep p)

/-- Normal forms cannot be DROP-redexes. -/
theorem normalForm_no_drop {q : Pattern}
    (hnf : NormalForm (.apply "PDrop" [.apply "NQuote" [q]])) : False :=
  hnf ⟨q, ⟨Reduces.drop⟩⟩

/-! ## IO Count: SC-Invariant Measure

`ioCount` counts POutput and PInput nodes in a pattern. It is preserved by
structural congruence and provides the key invariant for proving that the
empty bag (and its entire SC class) cannot reduce via COMM.
-/

/-- Count of POutput and PInput nodes in a pattern. -/
noncomputable def ioCount : Pattern → Nat
  | .bvar _ => 0
  | .fvar _ => 0
  | .apply "POutput" args => 1 + (args.map ioCount).sum
  | .apply "PInput" args => 1 + (args.map ioCount).sum
  | .apply _ args => (args.map ioCount).sum
  | .lambda b => ioCount b
  | .multiLambda _ b => ioCount b
  | .subst b r => ioCount b + ioCount r
  | .collection _ elems _ => (elems.map ioCount).sum

/-- Helper: pairwise SC on lists implies equal ioCount sums. -/
private theorem ioCount_list_SC {ps qs : List Pattern} (hlen : ps.length = qs.length)
    (hsc : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      ioCount (ps.get ⟨i, h₁⟩) = ioCount (qs.get ⟨i, h₂⟩)) :
    (ps.map ioCount).sum = (qs.map ioCount).sum := by
  induction ps generalizing qs with
  | nil =>
    cases qs with
    | nil => rfl
    | cons q qs' => simp at hlen
  | cons p ps' ih =>
    cases qs with
    | nil => simp at hlen
    | cons q qs' =>
      simp only [List.map_cons, List.sum_cons]
      simp only [List.length_cons] at hlen ⊢
      have h0 : ioCount p = ioCount q := hsc 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      have htl := ih (by omega) fun i h₁ h₂ =>
        hsc (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
      omega

/-- SC preserves ioCount. -/
theorem ioCount_SC {P Q : Pattern}
    (hsc : StructuralCongruence P Q) : ioCount P = ioCount Q := by
  induction hsc with
  | alpha _ _ h => subst h; rfl
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | par_singleton p =>
    simp [ioCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | par_nil_left p =>
    simp [ioCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | par_nil_right p =>
    simp [ioCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | par_comm p q =>
    simp [ioCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
  | par_assoc p q r =>
    simp [ioCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
  | par_cong ps qs hlen _ ih =>
    simp only [ioCount]; exact ioCount_list_SC hlen ih
  | par_flatten ps qs =>
    simp [ioCount, List.map_append, List.sum_append,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | par_perm _ _ hperm =>
    simp only [ioCount]; exact (hperm.map ioCount).sum_eq
  | set_perm _ _ hperm =>
    simp only [ioCount]; exact (hperm.map ioCount).sum_eq
  | set_cong es₁ es₂ hlen _ ih =>
    simp only [ioCount]; exact ioCount_list_SC hlen ih
  | lambda_cong _ _ _ ih => simp only [ioCount]; exact ih
  | apply_cong f args₁ args₂ hlen _ ih =>
    have hargs := ioCount_list_SC hlen ih
    -- ioCount (.apply f args) depends on whether f = "POutput"/"PInput"
    -- In all three cases, the (args.map ioCount).sum part is the same
    -- so the result follows from hargs
    show ioCount (.apply f args₁) = ioCount (.apply f args₂)
    unfold ioCount
    split <;> split <;> simp_all
  | collection_general_cong _ es₁ es₂ _ hlen _ ih =>
    simp only [ioCount]; exact ioCount_list_SC hlen ih
  | multiLambda_cong _ _ _ _ ih => simp only [ioCount]; exact ih
  | subst_cong _ _ _ _ _ _ ih₁ ih₂ => simp only [ioCount]; omega
  | quote_drop n =>
    -- ioCount(NQuote[PDrop[n]]) = ioCount(n)
    -- "NQuote" and "PDrop" are neither "POutput" nor "PInput"
    simp [ioCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

/-! ### SC-invariant weight for reduction sources

`redWeight` is designed so that:
- it is preserved by structural congruence;
- every `Reduces` source has strictly positive weight;
- the empty bag has weight `0`.

This gives a robust SC-quotiented irreducibility theorem for the empty bag.
-/

/-- A structural weight compatible with QUOTE-DROP (`NQuote (PDrop n) ≡ n`). -/
def redWeight : Pattern → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .apply f args =>
      let s := (args.map redWeight).sum
      -- Design rationale:
      -- - `PZero` must contribute 0 so empty-bag source weight is 0.
      -- - `NQuote` must decrease by one (`pred`) so `NQuote (PDrop n)` and `n`
      --   have equal weight under the SC rule `quote_drop`.
      -- - all other constructors contribute `+1` to enforce strict positivity
      --   on genuine redex sources (`comm`, `drop`, and contextual variants).
      if f = "PZero" then 0
      else if f = "NQuote" then Nat.pred s
      else s + 1
  | .lambda b => redWeight b
  | .multiLambda _ b => redWeight b
  | .subst b r => redWeight b + redWeight r
  | .collection _ elems _ => (elems.map redWeight).sum

/-- Helper: pairwise SC on lists implies equal `redWeight` sums. -/
private theorem redWeight_list_SC {ps qs : List Pattern} (hlen : ps.length = qs.length)
    (hsc : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      redWeight (ps.get ⟨i, h₁⟩) = redWeight (qs.get ⟨i, h₂⟩)) :
    (ps.map redWeight).sum = (qs.map redWeight).sum := by
  induction ps generalizing qs with
  | nil =>
    cases qs with
    | nil => rfl
    | cons q qs' => simp at hlen
  | cons p ps' ih =>
    cases qs with
    | nil => simp at hlen
    | cons q qs' =>
      simp only [List.map_cons, List.sum_cons]
      simp only [List.length_cons] at hlen ⊢
      have h0 : redWeight p = redWeight q := hsc 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      have htl := ih (by omega) fun i h₁ h₂ =>
        hsc (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
      omega

/-- SC preserves `redWeight`. -/
theorem redWeight_SC {P Q : Pattern}
    (hsc : StructuralCongruence P Q) : redWeight P = redWeight Q := by
  induction hsc with
  | alpha _ _ h => subst h; rfl
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | par_singleton p =>
    simp [redWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | par_nil_left p =>
    simp [redWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | par_nil_right p =>
    simp [redWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | par_comm p q =>
    simp [redWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
  | par_assoc p q r =>
    simp [redWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
  | par_cong ps qs hlen _ ih =>
    simp only [redWeight]
    exact redWeight_list_SC hlen ih
  | par_flatten ps qs =>
    simp [redWeight, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | par_perm _ _ hperm =>
    simp only [redWeight]
    exact (hperm.map redWeight).sum_eq
  | set_perm _ _ hperm =>
    simp only [redWeight]
    exact (hperm.map redWeight).sum_eq
  | set_cong es₁ es₂ hlen _ ih =>
    simp only [redWeight]
    exact redWeight_list_SC hlen ih
  | lambda_cong _ _ _ ih =>
    simpa [redWeight] using ih
  | apply_cong f args₁ args₂ hlen _ ih =>
    have hargs := redWeight_list_SC hlen ih
    show redWeight (.apply f args₁) = redWeight (.apply f args₂)
    simp [redWeight, hargs]
  | collection_general_cong _ es₁ es₂ _ hlen _ ih =>
    simp only [redWeight]
    exact redWeight_list_SC hlen ih
  | multiLambda_cong _ _ _ _ ih =>
    simpa [redWeight] using ih
  | subst_cong _ _ _ _ _ _ ih₁ ih₂ =>
    simp [redWeight, ih₁, ih₂]
  | quote_drop n =>
    simp [redWeight]

/-- Every one-step reduction source has strictly positive `redWeight`. -/
theorem redWeight_pos_of_reduces {P Q : Pattern} (hred : Reduces P Q) :
    0 < redWeight P := by
  induction hred with
  | comm =>
    simp [redWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | drop =>
    simp [redWeight]
  | @equiv p p' q q' hsc _ _ ih =>
    have hw : redWeight p = redWeight p' := redWeight_SC hsc
    omega
  | par _ ih =>
    simp [redWeight, List.map_cons, List.sum_cons]
    omega
  | par_any _ ih =>
    simp [redWeight, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    omega
  | par_set _ ih =>
    simp [redWeight, List.map_cons, List.sum_cons]
    omega
  | par_set_any _ ih =>
    simp [redWeight, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    omega

/-- Empty bag is irreducible modulo structural congruence (SC-quotiented). -/
theorem emptyBag_SC_irreducible {P Q : Pattern}
    (hsc : StructuralCongruence (.collection .hashBag [] none) P)
    (hred : Reduces P Q) : False := by
  have hscw : redWeight (.collection .hashBag [] none) = redWeight P := redWeight_SC hsc
  have hzero0 : 0 = redWeight P := by
    simpa [redWeight, List.map_nil, List.sum_nil] using hscw
  have hzero : redWeight P = 0 := hzero0.symm
  have hpos : 0 < redWeight P := redWeight_pos_of_reduces hred
  omega

/-! ### Empty-bag SC invariants (MVP surface)

These are the minimal SC-facing lemmas retained for current use: they expose
the canonical invariant (`ioCount = 0`) on the SC class of the empty bag.
-/

/-- `ioCount` of the syntactic empty parallel bag is zero. -/
theorem ioCount_emptyBag : ioCount (.collection .hashBag [] none) = 0 := by
  simp [ioCount]

/-- Any pattern SC-equivalent to the empty bag has `ioCount = 0`. -/
theorem ioCount_eq_zero_of_SC_emptyBag {p : Pattern}
    (hsc : StructuralCongruence p (.collection .hashBag [] none)) : ioCount p = 0 := by
  calc
    ioCount p = ioCount (.collection .hashBag [] none) := ioCount_SC hsc
    _ = 0 := ioCount_emptyBag

/-- Symmetric orientation of `ioCount_eq_zero_of_SC_emptyBag`. -/
theorem ioCount_eq_zero_of_emptyBag_SC {p : Pattern}
    (hsc : StructuralCongruence (.collection .hashBag [] none) p) : ioCount p = 0 := by
  exact ioCount_eq_zero_of_SC_emptyBag (hsc := StructuralCongruence.symm _ _ hsc)

/-! ## Empty Bag Irreducibility

This file now contains the SC-quotiented irreducibility theorem
`emptyBag_SC_irreducible` at the raw `Reduces` level.

For the executable OSLF pipeline, we also keep the operational counterparts:
- `RhoCalculus/Engine.lean` (`emptyBag_reduceStep_nil`)
- `Framework/TypeSynthesis.lean` (`rhoCalc_emptyBag_langReduces_irreducible`)
-/

end Mettapedia.OSLF.RhoCalculus.Reduction
