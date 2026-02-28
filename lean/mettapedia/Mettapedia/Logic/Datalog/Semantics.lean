import Mettapedia.Logic.Datalog.Substitution
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice

/-!
# Datalog Semantics: T_P Operator and Least Model

This file defines the model-theoretic semantics of Datalog:

- `T_P kb I` — the immediate consequence operator: applies all rules of `kb` to
  interpretation `I` and collects the resulting ground atoms (plus the EDB facts).
- `T_P_mono` — T_P is monotone on `Set (GroundAtom τ)`.
- `leastModel kb` — the least Herbrand model, defined as the least fixpoint of T_P
  via `OrderHom.lfp` (Mathlib's lattice fixpoint theorem).
- `leastModel_fixpoint` — leastModel is a fixpoint of T_P.
- `leastModel_least` — leastModel is contained in every pre-fixpoint.
- `leastModel_db` — EDB facts are in leastModel.
- `leastModel_rule` — rules with satisfied bodies contribute heads to leastModel.

## Fixpoint approach

`Set (GroundAtom τ)` is a `CompleteLattice` (via `Mathlib.Data.Set.Lattice`), so
`OrderHom.lfp` applies directly via Tarski's fixed-point theorem.
-/

namespace Mettapedia.Logic.Datalog

/-! ## Section 1: Immediate Consequence Operator -/

/-- The immediate consequence operator T_P.

    `T_P kb I` contains:
    1. Every EDB fact (ground atom in `kb.db`).
    2. Every ground head `g.applyAtom r.head` for rules `r ∈ kb.prog` and groundings `g`
       such that all grounded body atoms are in `I`. -/
noncomputable def T_P {τ : Signature} (kb : KnowledgeBase τ) (I : Interpretation τ) :
    Interpretation τ :=
  ↑kb.db ∪
  { a | ∃ (r : Rule τ) (g : Grounding τ),
        r ∈ kb.prog ∧
        g.applyAtom r.head = a ∧
        ∀ b ∈ r.body, g.applyAtom b ∈ I }

/-! ## Section 2: Monotonicity -/

/-- T_P is monotone: larger interpretations yield larger immediate consequences. -/
theorem T_P_mono {τ : Signature} (kb : KnowledgeBase τ) :
    Monotone (T_P kb) := by
  intro I J hIJ a ha
  simp only [T_P, Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq] at ha ⊢
  rcases ha with ha | ⟨r, g, hr, hhead, hbody⟩
  · exact Or.inl ha
  · exact Or.inr ⟨r, g, hr, hhead, fun b hb => hIJ (hbody b hb)⟩

/-! ## Section 3: Least Model via OrderHom.lfp -/

/-- Package T_P kb as an order homomorphism for use with `OrderHom.lfp`. -/
noncomputable def T_P_orderHom {τ : Signature} (kb : KnowledgeBase τ) :
    Interpretation τ →o Interpretation τ where
  toFun    := T_P kb
  monotone' := T_P_mono kb

/-- The least Herbrand model of a knowledge base, defined as the least fixpoint of T_P. -/
noncomputable def leastModel {τ : Signature} (kb : KnowledgeBase τ) :
    Interpretation τ :=
  OrderHom.lfp (T_P_orderHom kb)

/-! ## Section 4: Core Semantic Properties -/

/-- The least model is a fixpoint of T_P. -/
theorem leastModel_fixpoint {τ : Signature} (kb : KnowledgeBase τ) :
    T_P kb (leastModel kb) = leastModel kb :=
  OrderHom.isFixedPt_lfp (T_P_orderHom kb)

/-- The least model is contained in every pre-fixpoint (T_P kb I ⊆ I). -/
theorem leastModel_least {τ : Signature} (kb : KnowledgeBase τ)
    (I : Interpretation τ) (hI : T_P kb I ⊆ I) : leastModel kb ⊆ I :=
  OrderHom.lfp_le (T_P_orderHom kb) hI

/-- All EDB facts are in the least model. -/
theorem leastModel_db {τ : Signature} (kb : KnowledgeBase τ) (a : GroundAtom τ)
    (ha : a ∈ kb.db) : a ∈ leastModel kb := by
  have : a ∈ T_P kb (leastModel kb) :=
    Set.mem_union_left _ (Finset.mem_coe.mpr ha)
  rwa [leastModel_fixpoint] at this

/-- A rule with satisfied body contributes its head to the least model. -/
theorem leastModel_rule {τ : Signature} (kb : KnowledgeBase τ)
    (r : Rule τ) (hr : r ∈ kb.prog) (g : Grounding τ)
    (hbody : ∀ b ∈ r.body, g.applyAtom b ∈ leastModel kb) :
    g.applyAtom r.head ∈ leastModel kb := by
  have : g.applyAtom r.head ∈ T_P kb (leastModel kb) :=
    Set.mem_union_right _ ⟨r, g, hr, rfl, hbody⟩
  rwa [leastModel_fixpoint] at this

/-! ## Section 5: Pre-fixpoint Characterization -/

/-- T_P kb I ⊆ I iff I contains EDB and is closed under all groundings. -/
theorem T_P_le_iff {τ : Signature} (kb : KnowledgeBase τ) (I : Interpretation τ) :
    T_P kb I ⊆ I ↔
    (↑kb.db ⊆ I) ∧
    (∀ (r : Rule τ) (g : Grounding τ), r ∈ kb.prog →
      (∀ b ∈ r.body, g.applyAtom b ∈ I) → g.applyAtom r.head ∈ I) := by
  constructor
  · intro h
    constructor
    · intro a ha; exact h (Set.mem_union_left _ (Finset.mem_coe.mpr ha))
    · intro r g hr hbody
      exact h (Set.mem_union_right _ ⟨r, g, hr, rfl, hbody⟩)
  · intro ⟨hdb, hrules⟩ a ha
    simp only [T_P, Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq] at ha
    rcases ha with ha | ⟨r, g, hr, hhead, hbody⟩
    · exact hdb (Finset.mem_coe.mpr ha)
    · exact hhead ▸ hrules r g hr hbody

/-- An interpretation `I` is a model of `kb` iff T_P kb I ⊆ I. -/
def isModel {τ : Signature} (kb : KnowledgeBase τ) (I : Interpretation τ) : Prop :=
  T_P kb I ⊆ I

/-- The least model is a model. -/
theorem leastModel_isModel {τ : Signature} (kb : KnowledgeBase τ) :
    isModel kb (leastModel kb) := by
  simp only [isModel, leastModel_fixpoint]
  exact Set.Subset.rfl

/-- The least model is the smallest model. -/
theorem leastModel_is_least_model {τ : Signature} (kb : KnowledgeBase τ)
    (I : Interpretation τ) (hI : isModel kb I) : leastModel kb ⊆ I :=
  leastModel_least kb I hI

/-! ## Section 6: Iteration (groundwork for Evaluation.lean) -/

/-- The n-th iterate of T_P from the EDB. -/
noncomputable def T_P_iter {τ : Signature} (kb : KnowledgeBase τ) : ℕ → Interpretation τ
  | 0     => ↑kb.db
  | n + 1 => T_P kb (T_P_iter kb n)

/-- Each iterate is monotone (adding one step only adds atoms). -/
theorem T_P_iter_succ_le {τ : Signature} (kb : KnowledgeBase τ) (n : ℕ) :
    T_P_iter kb n ⊆ T_P_iter kb (n + 1) := by
  induction n with
  | zero =>
    simp only [T_P_iter]
    exact fun a ha => Set.mem_union_left _ ha
  | succ n ih =>
    simp only [T_P_iter]
    exact T_P_mono kb ih

/-- The iterate is monotone in the step count. -/
theorem T_P_iter_mono {τ : Signature} (kb : KnowledgeBase τ) (m n : ℕ) (h : m ≤ n) :
    T_P_iter kb m ⊆ T_P_iter kb n := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact ih.trans (T_P_iter_succ_le kb _)

/-- Each iterate is contained in the least model. -/
theorem T_P_iter_le_leastModel {τ : Signature} (kb : KnowledgeBase τ) (n : ℕ) :
    T_P_iter kb n ⊆ leastModel kb := by
  induction n with
  | zero =>
    simp only [T_P_iter]
    exact fun a ha => leastModel_db kb a (Finset.mem_coe.mp ha)
  | succ n ih =>
    simp only [T_P_iter]
    calc T_P kb (T_P_iter kb n)
        ⊆ T_P kb (leastModel kb) := T_P_mono kb ih
      _ = leastModel kb           := leastModel_fixpoint kb

end Mettapedia.Logic.Datalog
