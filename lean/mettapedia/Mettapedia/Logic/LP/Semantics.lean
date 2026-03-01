import Mettapedia.Logic.LP.Substitution
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice

/-!
# Logic Programming Kernel: T_P Operator and Least Herbrand Model

Model-theoretic semantics of logic programs with function symbols.

## Design

- `Grounding.groundTerm` / `groundAtom` — apply a grounding to produce
  `GroundTerm` / `GroundAtom` directly (not general `Term` / `Atom`).
- `T_P_LP kb I` — immediate consequence operator.
- `T_P_LP_mono` — monotonicity, enabling least fixpoint.
- `leastHerbrandModel` — via `OrderHom.lfp` (Tarski's theorem on `Set (GroundAtom σ)`).
- With function symbols, the Herbrand universe may be infinite. The semantics
  work uniformly; finiteness is an optional constraint (cf. mm-lean4 pattern).

## References

- van Emden & Kowalski, "Semantics of predicate logic as a programming language", 1976
- Lloyd, *Foundations of Logic Programming*, Ch. 2
-/

namespace Mettapedia.Logic.LP

/-! ## Section 1: Grounding to ground types -/

/-- Apply a grounding to a term, producing a ground term directly. -/
def Grounding.groundTerm {σ : LPSignature} (g : Grounding σ) : Term σ → GroundTerm σ
  | .var v    => g v
  | .const c  => .const c
  | .app f ts => .app f (fun i => g.groundTerm (ts i))

/-- Apply a grounding to an atom, producing a ground atom directly. -/
def Grounding.groundAtom {σ : LPSignature} (g : Grounding σ) (a : Atom σ) : GroundAtom σ where
  symbol := a.symbol
  args   := fun i => g.groundTerm (a.args i)

/-- Apply a grounding to a clause, producing a ground clause. -/
def Grounding.groundClause {σ : LPSignature} (g : Grounding σ) (c : Clause σ) :
    GroundClause σ where
  head := g.groundAtom c.head
  body := c.body.map g.groundAtom

/-- Grounding to GroundTerm then lifting to Term equals applying the grounding as a Subst. -/
theorem Grounding.groundTerm_toTerm {σ : LPSignature} (g : Grounding σ) (t : Term σ) :
    (g.groundTerm t).toTerm = g.toSubst.applyTerm t := by
  induction t with
  | var v => rfl
  | const _ => rfl
  | app f ts ih => simp [groundTerm, GroundTerm.toTerm, Subst.applyTerm, ih]

/-- Grounding to GroundAtom then lifting to Atom equals applying as a Subst. -/
theorem Grounding.groundAtom_toAtom {σ : LPSignature} (g : Grounding σ) (a : Atom σ) :
    (g.groundAtom a).toAtom = g.toSubst.applyAtom a := by
  ext
  · rfl
  · simp [groundAtom, GroundAtom.toAtom, Subst.applyAtom, groundTerm_toTerm]

/-! ## Section 2: Immediate Consequence Operator -/

/-- The immediate consequence operator T_P for logic programs.

    `T_P_LP kb I` contains:
    1. Every EDB fact (ground atom in `kb.db`).
    2. Every ground head `g.groundAtom c.head` for clauses `c ∈ kb.prog` and groundings `g`
       such that all grounded body atoms are in `I`. -/
noncomputable def T_P_LP {σ : LPSignature} (kb : KnowledgeBase σ) (I : Interpretation σ) :
    Interpretation σ :=
  kb.db ∪
  { a | ∃ (c : Clause σ) (g : Grounding σ),
        c ∈ kb.prog ∧
        g.groundAtom c.head = a ∧
        ∀ b ∈ c.body, g.groundAtom b ∈ I }

/-! ## Section 3: Monotonicity -/

/-- T_P_LP is monotone: larger interpretations yield larger immediate consequences. -/
theorem T_P_LP_mono {σ : LPSignature} (kb : KnowledgeBase σ) :
    Monotone (T_P_LP kb) := by
  intro I J hIJ a ha
  simp only [T_P_LP, Set.mem_union, Set.mem_setOf_eq] at ha ⊢
  rcases ha with ha | ⟨c, g, hc, hhead, hbody⟩
  · exact Or.inl ha
  · exact Or.inr ⟨c, g, hc, hhead, fun b hb => hIJ (hbody b hb)⟩

/-! ## Section 4: Least Herbrand Model via OrderHom.lfp -/

/-- Package T_P_LP as an order homomorphism. -/
noncomputable def T_P_LP_orderHom {σ : LPSignature} (kb : KnowledgeBase σ) :
    Interpretation σ →o Interpretation σ where
  toFun    := T_P_LP kb
  monotone' := T_P_LP_mono kb

/-- The least Herbrand model of a knowledge base. -/
noncomputable def leastHerbrandModel {σ : LPSignature} (kb : KnowledgeBase σ) :
    Interpretation σ :=
  OrderHom.lfp (T_P_LP_orderHom kb)

/-! ## Section 5: Core Semantic Properties -/

/-- The least Herbrand model is a fixpoint of T_P_LP. -/
theorem leastHerbrandModel_fixpoint {σ : LPSignature} (kb : KnowledgeBase σ) :
    T_P_LP kb (leastHerbrandModel kb) = leastHerbrandModel kb :=
  OrderHom.isFixedPt_lfp (T_P_LP_orderHom kb)

/-- The least Herbrand model is contained in every pre-fixpoint. -/
theorem leastHerbrandModel_least {σ : LPSignature} (kb : KnowledgeBase σ)
    (I : Interpretation σ) (hI : T_P_LP kb I ⊆ I) : leastHerbrandModel kb ⊆ I :=
  OrderHom.lfp_le (T_P_LP_orderHom kb) hI

/-- All EDB facts are in the least Herbrand model. -/
theorem leastHerbrandModel_db {σ : LPSignature} (kb : KnowledgeBase σ) (a : GroundAtom σ)
    (ha : a ∈ kb.db) : a ∈ leastHerbrandModel kb := by
  have : a ∈ T_P_LP kb (leastHerbrandModel kb) :=
    Set.mem_union_left _ ha
  rwa [leastHerbrandModel_fixpoint] at this

/-- A clause with satisfied body contributes its head to the least Herbrand model. -/
theorem leastHerbrandModel_clause {σ : LPSignature} (kb : KnowledgeBase σ)
    (c : Clause σ) (hc : c ∈ kb.prog) (g : Grounding σ)
    (hbody : ∀ b ∈ c.body, g.groundAtom b ∈ leastHerbrandModel kb) :
    g.groundAtom c.head ∈ leastHerbrandModel kb := by
  have : g.groundAtom c.head ∈ T_P_LP kb (leastHerbrandModel kb) :=
    Set.mem_union_right _ ⟨c, g, hc, rfl, hbody⟩
  rwa [leastHerbrandModel_fixpoint] at this

/-! ## Section 6: Pre-fixpoint Characterization -/

/-- An interpretation is a model iff it is a pre-fixpoint of T_P_LP. -/
def isModel {σ : LPSignature} (kb : KnowledgeBase σ) (I : Interpretation σ) : Prop :=
  T_P_LP kb I ⊆ I

/-- The least Herbrand model is a model. -/
theorem leastHerbrandModel_isModel {σ : LPSignature} (kb : KnowledgeBase σ) :
    isModel kb (leastHerbrandModel kb) := by
  simp only [isModel, leastHerbrandModel_fixpoint]
  exact Set.Subset.rfl

/-- The least Herbrand model is contained in every model. -/
theorem leastHerbrandModel_is_least {σ : LPSignature} (kb : KnowledgeBase σ)
    (I : Interpretation σ) (hI : isModel kb I) : leastHerbrandModel kb ⊆ I :=
  leastHerbrandModel_least kb I hI

/-- T_P_LP kb I ⊆ I iff I contains EDB and is closed under all groundings. -/
theorem T_P_LP_le_iff {σ : LPSignature} (kb : KnowledgeBase σ) (I : Interpretation σ) :
    T_P_LP kb I ⊆ I ↔
    (kb.db ⊆ I) ∧
    (∀ (c : Clause σ) (g : Grounding σ), c ∈ kb.prog →
      (∀ b ∈ c.body, g.groundAtom b ∈ I) → g.groundAtom c.head ∈ I) := by
  constructor
  · intro h
    constructor
    · intro a ha; exact h (Set.mem_union_left _ ha)
    · intro c g hc hbody
      exact h (Set.mem_union_right _ ⟨c, g, hc, rfl, hbody⟩)
  · intro ⟨hdb, hclauses⟩ a ha
    simp only [T_P_LP, Set.mem_union, Set.mem_setOf_eq] at ha
    rcases ha with ha | ⟨c, g, hc, hhead, hbody⟩
    · exact hdb ha
    · exact hhead ▸ hclauses c g hc hbody

/-! ## Section 7: Iteration -/

/-- The n-th iterate of T_P_LP from the EDB. -/
noncomputable def T_P_LP_iter {σ : LPSignature} (kb : KnowledgeBase σ) :
    ℕ → Interpretation σ
  | 0     => kb.db
  | n + 1 => T_P_LP kb (T_P_LP_iter kb n)

/-- Each iterate is contained in the next. -/
theorem T_P_LP_iter_succ_le {σ : LPSignature} (kb : KnowledgeBase σ) (n : ℕ) :
    T_P_LP_iter kb n ⊆ T_P_LP_iter kb (n + 1) := by
  induction n with
  | zero =>
    simp only [T_P_LP_iter]
    exact fun a ha => Set.mem_union_left _ ha
  | succ n ih =>
    simp only [T_P_LP_iter]
    exact T_P_LP_mono kb ih

/-- The iterate is monotone in the step count. -/
theorem T_P_LP_iter_mono {σ : LPSignature} (kb : KnowledgeBase σ) (m n : ℕ) (h : m ≤ n) :
    T_P_LP_iter kb m ⊆ T_P_LP_iter kb n := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact ih.trans (T_P_LP_iter_succ_le kb _)

/-- Each iterate is contained in the least Herbrand model. -/
theorem T_P_LP_iter_le_leastHerbrandModel {σ : LPSignature} (kb : KnowledgeBase σ) (n : ℕ) :
    T_P_LP_iter kb n ⊆ leastHerbrandModel kb := by
  induction n with
  | zero =>
    simp only [T_P_LP_iter]
    exact fun a ha => leastHerbrandModel_db kb a ha
  | succ n ih =>
    simp only [T_P_LP_iter]
    calc T_P_LP kb (T_P_LP_iter kb n)
        ⊆ T_P_LP kb (leastHerbrandModel kb) := T_P_LP_mono kb ih
      _ = leastHerbrandModel kb              := leastHerbrandModel_fixpoint kb

end Mettapedia.Logic.LP
