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
    split <;> split <;> simp_all <;> omega
  | collection_general_cong _ es₁ es₂ _ hlen _ ih =>
    simp only [ioCount]; exact ioCount_list_SC hlen ih
  | multiLambda_cong _ _ _ _ ih => simp only [ioCount]; exact ih
  | subst_cong _ _ _ _ _ _ ih₁ ih₂ => simp only [ioCount]; omega
  | quote_drop n =>
    -- ioCount(NQuote[PDrop[n]]) = ioCount(n)
    -- "NQuote" and "PDrop" are neither "POutput" nor "PInput"
    simp [ioCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]


/-! ## SC-Invariant: HashSet Count

`hashSetCount` counts hashSet collection nodes in a pattern. It is preserved
by structural congruence. Since `hashBag [] none` has `hashSetCount = 0`
but any `hashSet` pattern has `hashSetCount >= 1`, these can never be SC-equivalent.
-/

/-- Count of hashSet collection nodes in a pattern. -/
noncomputable def hashSetCount : Pattern → Nat
  | .bvar _ => 0
  | .fvar _ => 0
  | .apply _ args => (args.map hashSetCount).sum
  | .lambda b => hashSetCount b
  | .multiLambda _ b => hashSetCount b
  | .subst b r => hashSetCount b + hashSetCount r
  | .collection .hashSet elems _ => 1 + (elems.map hashSetCount).sum
  | .collection _ elems _ => (elems.map hashSetCount).sum

/-- Helper: pairwise SC on lists implies equal hashSetCount sums. -/
private theorem hashSetCount_list_SC {ps qs : List Pattern} (hlen : ps.length = qs.length)
    (hsc : ∀ i (h₁ : i < ps.length) (h₂ : i < qs.length),
      hashSetCount (ps.get ⟨i, h₁⟩) = hashSetCount (qs.get ⟨i, h₂⟩)) :
    (ps.map hashSetCount).sum = (qs.map hashSetCount).sum := by
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
      simp only [List.length_cons] at hlen
      have h0 : hashSetCount p = hashSetCount q := hsc 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      have htl := ih (by omega) fun i h₁ h₂ =>
        hsc (i + 1) (Nat.succ_lt_succ h₁) (Nat.succ_lt_succ h₂)
      omega

/-- SC preserves hashSetCount. -/
theorem hashSetCount_SC {P Q : Pattern}
    (hsc : StructuralCongruence P Q) : hashSetCount P = hashSetCount Q := by
  induction hsc with
  | alpha _ _ h => subst h; rfl
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | par_singleton p =>
    simp [hashSetCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | par_nil_left p =>
    simp [hashSetCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | par_nil_right p =>
    simp [hashSetCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | par_comm p q =>
    simp [hashSetCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
  | par_assoc p q r =>
    simp [hashSetCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
  | par_cong ps qs hlen _ ih =>
    simp only [hashSetCount]; exact hashSetCount_list_SC hlen ih
  | par_flatten ps qs =>
    simp [hashSetCount, List.map_append, List.sum_append,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  | par_perm _ _ hperm =>
    simp only [hashSetCount]; exact (hperm.map hashSetCount).sum_eq
  | set_perm _ _ hperm =>
    simp only [hashSetCount]
    have := (hperm.map hashSetCount).sum_eq
    omega
  | set_cong es₁ es₂ hlen _ ih =>
    simp only [hashSetCount]; exact congrArg (1 + ·) (hashSetCount_list_SC hlen ih)
  | lambda_cong _ _ _ ih => simp only [hashSetCount]; exact ih
  | apply_cong f args₁ args₂ hlen _ ih =>
    simp only [hashSetCount]; exact hashSetCount_list_SC hlen ih
  | collection_general_cong ct es₁ es₂ g hlen _ ih =>
    have hargs := hashSetCount_list_SC hlen ih
    cases ct <;> simp only [hashSetCount] <;> omega
  | multiLambda_cong _ _ _ _ ih => simp only [hashSetCount]; exact ih
  | subst_cong _ _ _ _ _ _ ih₁ ih₂ => simp only [hashSetCount]; omega
  | quote_drop n =>
    simp [hashSetCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

/-! ## Empty Bag Irreducibility

The empty bag `.collection .hashBag [] none` cannot reduce. The proof is
by induction on the `Reduces` derivation, generalized over SC.

- `equiv`: IH + SC transitivity
- `comm`: ioCount contradiction (COMM source has ioCount >= 2, but SC({}, P) => ioCount P = 0)
- `drop`/`par`/`par_any`/`par_set`/`par_set_any`: ioCount decomposition + IH
-/

/-- The empty bag is irreducible, even modulo SC.

    Proved via a generalized helper that works with ioCount = 0 + SC hypothesis.
    By induction on the Reduces derivation:
    - `equiv`: SC transitivity gives SC({}, p'), then IH
    - `comm`: ioCount >= 2, contradiction
    - `drop`: SC({}, PDrop[NQuote[x]]) is impossible (quote_drop asymmetry)
    - `par`/`par_any`: ioCount decomposition + IH
    - `par_set`/`par_set_any`: collection type mismatch via SC
-/
theorem emptyBag_SC_irreducible {P Q : Pattern}
    (hsc : StructuralCongruence (.collection .hashBag [] none) P)
    (hred : Reduces P Q) : False := by
  -- Generalize: suffices to show that for any P with SC({}, P), Reduces(P, Q) is impossible
  -- The key: induction on hred, generalizing over the SC hypothesis
  revert hsc
  induction hred with
  | comm =>
    intro hsc
    have hio := ioCount_SC hsc
    simp [ioCount, List.map_nil, List.sum_nil, List.map_cons, List.sum_cons,
          List.map_append, List.sum_append] at hio
    omega
  | drop =>
    -- Need: SC({}, PDrop[NQuote[x]]) -> False
    intro hsc
    sorry -- OPEN: SC(hashBag [] none, PDrop[NQuote[p]]) → False (needs InZeroClass predicate)
  | @equiv _ p' _ q' hsc₁ _ hsc₂ ih =>
    intro hsc
    exact ih (.trans _ _ _ hsc hsc₁)
  | @par p q rest _ ih =>
    -- OPEN: SC(hashBag [] none, hashBag (p :: rest) none) ∧ Reduces p q → False
    -- IH says SC(Z, p) → False. Need to extract SC(Z, p) from SC(Z, hashBag(p::rest)).
    -- Difficulty: not all elements of a zero-class bag are SC-equiv to Z.
    -- E.g., hashBag [PZero, Z] ≡ Z (par_nil_left) but SC(Z, PZero) might not hold
    -- (Z = hashBag [] and PZero = apply "PZero" [] are syntactically distinct,
    --  and no SC rule directly equates them).
    -- Possible fix: add SC rule `hashBag [] ≡ PZero` to match standard process algebra.
    -- Alternative: prove NormalForm(PZero) separately and handle PZero case directly.
    intro hsc
    sorry
  | @par_any p q before after _ ih =>
    -- OPEN: Same issue as par case but for arbitrary position in the bag.
    -- SC(Z, hashBag (before ++ [p] ++ after) none) ∧ Reduces p q → False
    intro hsc
    sorry
  | @par_set p q rest _ ih =>
    intro hsc
    have hsc_count := hashSetCount_SC hsc
    simp [hashSetCount, List.map_nil, List.sum_nil, List.map_cons, List.sum_cons] at hsc_count
    omega
  | @par_set_any p q before after _ ih =>
    intro hsc
    have hsc_count := hashSetCount_SC hsc
    simp [hashSetCount, List.map_nil, List.sum_nil, List.map_cons, List.sum_cons,
          List.map_append, List.sum_append] at hsc_count
    omega

end Mettapedia.OSLF.RhoCalculus.Reduction
