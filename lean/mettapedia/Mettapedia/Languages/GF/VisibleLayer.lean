import Mettapedia.Languages.GF.OSLFBridge_handcrafted
import Mettapedia.Languages.GF.WorldModelSemantics
import Mettapedia.OSLF.Formula
import Mathlib.Data.Multiset.Basic

/-!
# TUG Visible Semantic Layer

Implements the "visible rule layer" from the TUG paper (Goertzel 2026, Section 7):
meaning-bearing grammatical actions that operate on **state = term + semantic store**.

## Architecture

The GF→OSLF pipeline has three layers of reduction:
1. **Internal** (τ): Syntax rewrites (`langReduces gfRGLLanguageDef`) — wrapper
   elimination, canonicalization. Silent; no semantic choices.
2. **Temporal**: Policy-based evolution of `⊛temporal` nodes (reuses `TemporalPolicy`
   from WorldModelSemantics.lean).
3. **Visible** (V1-V4): Meaning-bearing actions — scope ordering, referent
   introduction, pronoun binding. Modify a **semantic store** of typed atoms.

The combined relation `gfReducesFull` composes all three.

## References

- Goertzel, "TUG: Universal Grammar via TyLAA" (2026), Section 7
- Rules V1 (quantifier intro), V2 (scope choice), V3 (referent intro), V4 (pronoun bind)
-/

namespace Mettapedia.Languages.GF.VisibleLayer

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.Languages.GF.WorldModelSemantics

/-! ## Store Atoms -/

/-- Typed semantic store atoms (TUG Section 7, V1-V4).

    Each constructor records one meaning-bearing decision:
    - `quant q det restr`: Quantifier `q` with determiner `det` and restrictor `restr` (V1)
    - `scope q1 q2`: Quantifier `q1` scopes over `q2` (V2)
    - `ref r pos`: Discourse referent `r` introduced at position `pos` (V3)
    - `bind pr r`: Pronoun `pr` resolved to antecedent referent `r` (V4) -/
inductive StoreAtom where
  | quant (q : String) (det : Pattern) (restr : Pattern)
  | scope (q1 q2 : String)
  | ref (r : String) (pos : Pattern)
  | bind (pr r : String)
  deriving Repr, DecidableEq

/-! ## Grammar State -/

/-- Grammar state: term + semantic store.

    The term is the GF pattern tree (subject to syntax rewrites).
    The store is a multiset of semantic atoms recording scope, binding, etc.
    Multiset is resource-sensitive and order-independent. -/
structure GrammarState where
  term : Pattern
  store : Multiset StoreAtom

/-! ## State ↔ Pattern Encoding

    Encode `GrammarState` into `Pattern` so the existing `sem`/`semE` pipeline
    (which operates on `Pattern → Pattern → Prop`) can be reused without refactor. -/

/-- Encode a store atom as a Pattern for embedding in the existing pipeline. -/
def encodeStoreAtom : StoreAtom → Pattern
  | .quant q det restr => .apply "⊛quant" [.apply q [], det, restr]
  | .scope q1 q2 => .apply "⊛scope" [.apply q1 [], .apply q2 []]
  | .ref r pos => .apply "⊛ref" [.apply r [], pos]
  | .bind pr r => .apply "⊛bind" [.apply pr [], .apply r []]

/-- Encode a grammar state as a single Pattern.

    The term and store atoms are bundled under `⊛state(term, store...)`. -/
noncomputable def encodeState (s : GrammarState) : Pattern :=
  .apply "⊛state" (s.term :: s.store.toList.map encodeStoreAtom)

/-! ## Resources and Rely Footprints (TUG Section 6.4) -/

/-- Semantic resources — the "slots" that visible rules read/write. -/
inductive Resource where
  | Q (q : String)    -- quantifier resource
  | R (r : String)    -- referent resource
  | P (pr : String)   -- pronoun resource
  deriving DecidableEq

/-- Rely footprint of a store atom: which resources it touches.

    Two atoms with disjoint footprints are independent (can commute). -/
def relyFootprint : StoreAtom → Finset Resource
  | .quant q _ _ => {.Q q}
  | .scope q1 q2 => {.Q q1, .Q q2}
  | .ref r _     => {.R r}
  | .bind pr r   => {.P pr, .R r}

/-! ## Abstract NP Replacement Interface -/

/-- Abstract interface for replacing NP subtrees with quantifier variables.

    Grammar-independent: the core visible layer doesn't know GF constructor names.
    A concrete instance (`gfNPReplacer`) is provided in `VisibleLayerGFInstance.lean`. -/
structure NPReplacer where
  /-- Replace an NP subtree in `term` with a quantifier variable for handle `q`.
      Returns the modified term, or `none` if no suitable NP is found. -/
  replaceNPWithVar : Pattern → String → Option Pattern

/-- Configuration bundle for the visible layer. -/
structure VisibleCfg where
  npReplacer : NPReplacer

/-! ## Visible Step Relation (V1-V4)

The four meaning-bearing rules from TUG Section 7, parameterized by `VisibleCfg`.
Each rule specifies preconditions on the store and the resulting state. -/

/-- Visible step: one meaning-bearing grammatical action.

    Parameterized by `cfg : VisibleCfg` which provides the NP replacement strategy. -/
inductive VisibleStep (cfg : VisibleCfg) : GrammarState → GrammarState → Prop where
  /-- **V1: Quantifier Introduction** (TUG §7.1)

      At an NP position, introduce quantifier handle `q`, replace the NP subtree
      with `NPVar(q)`, and record `Quant(q, det, restr)` in the store. -/
  | quantIntro (q : String) (det restr : Pattern)
      (s : GrammarState)
      (hfresh : ∀ d r, StoreAtom.quant q d r ∉ s.store)
      (t' : Pattern)
      (hterm : cfg.npReplacer.replaceNPWithVar s.term q = some t') :
      VisibleStep cfg s ⟨t', s.store + {.quant q det restr}⟩

  /-- **V2: Scope Constraint Choice** (TUG §7.1)

      Given two distinct quantifiers `q1 ≠ q2` in the store with no relative
      ordering, commit to `q1` scoping over `q2`. The alternative `Scope(q2, q1)`
      is a separate nondeterministic step — this is where scope ambiguity lives. -/
  | scopeChoice (q1 q2 : String)
      (s : GrammarState)
      (hne : q1 ≠ q2)
      (hq1 : ∃ d1 r1, StoreAtom.quant q1 d1 r1 ∈ s.store)
      (hq2 : ∃ d2 r2, StoreAtom.quant q2 d2 r2 ∈ s.store)
      (hno : StoreAtom.scope q1 q2 ∉ s.store ∧ StoreAtom.scope q2 q1 ∉ s.store) :
      VisibleStep cfg s ⟨s.term, s.store + {.scope q1 q2}⟩

  /-- **V3: Referent Introduction** (TUG §7.2)

      At an NP position `pos`, introduce discourse referent `r`, making it
      available as a potential antecedent for pronouns. -/
  | refIntro (r : String) (pos : Pattern)
      (s : GrammarState)
      (hfresh : ∀ p, StoreAtom.ref r p ∉ s.store) :
      VisibleStep cfg s ⟨s.term, s.store + {.ref r pos}⟩

  /-- **V4: Pronoun Resolution** (TUG §7.2)

      Resolve pronoun `pr` to accessible antecedent referent `r`.
      Precondition: `r` must have been introduced (V3) in the store. -/
  | pronounBind (pr r : String)
      (s : GrammarState)
      (href : ∃ p, StoreAtom.ref r p ∈ s.store)
      (hfresh : ∀ r', StoreAtom.bind pr r' ∉ s.store) :
      VisibleStep cfg s ⟨s.term, s.store + {.bind pr r}⟩

/-! ## Combined Relation -/

/-- Combined reduction: internal (syntax) + temporal + visible.

    Three-layer composition following TUG's label partition `Lab = Labᵥ ⊔ Labτ`.
    Reuses `TemporalPolicy` from WorldModelSemantics.lean. -/
def gfReducesFull (cfg : VisibleCfg) (π : TemporalPolicy) :
    GrammarState → GrammarState → Prop :=
  fun s1 s2 =>
    -- Layer 1: internal syntax rewrites (store unchanged)
    (langReduces gfRGLLanguageDef s1.term s2.term ∧ s1.store = s2.store)
    -- Layer 2: temporal policy steps (store unchanged)
    ∨ (temporalStep π s1.term s2.term ∧ s1.store = s2.store)
    -- Layer 3: visible semantic steps (V1-V4)
    ∨ VisibleStep cfg s1 s2

/-! ## Structural Theorems -/

/-- Visible steps only add atoms — the store grows monotonically. -/
theorem visible_store_monotone {cfg : VisibleCfg} {s1 s2 : GrammarState}
    (h : VisibleStep cfg s1 s2) : s1.store ≤ s2.store := by
  cases h <;> exact Multiset.le_add_right s1.store _

/-- Pronoun binding requires a prior referent introduction (V4 needs V3). -/
theorem bind_requires_ref {cfg : VisibleCfg} {pr r : String}
    {s : GrammarState}
    (href : ∃ p, StoreAtom.ref r p ∈ s.store)
    (hfresh : ∀ r', StoreAtom.bind pr r' ∉ s.store) :
    VisibleStep cfg s ⟨s.term, s.store + {.bind pr r}⟩ ∧
    (∃ p, StoreAtom.ref r p ∈ s.store) :=
  ⟨.pronounBind pr r s href hfresh, href⟩

/-- Scope choice is nondeterministic: given two unordered distinct quantifiers,
    both orderings are reachable from the same state. -/
theorem scope_choice_nondet {cfg : VisibleCfg}
    (q1 q2 : String) (s : GrammarState)
    (hne : q1 ≠ q2)
    (hq1 : ∃ d1 r1, StoreAtom.quant q1 d1 r1 ∈ s.store)
    (hq2 : ∃ d2 r2, StoreAtom.quant q2 d2 r2 ∈ s.store)
    (hno12 : StoreAtom.scope q1 q2 ∉ s.store)
    (hno21 : StoreAtom.scope q2 q1 ∉ s.store) :
    VisibleStep cfg s ⟨s.term, s.store + {.scope q1 q2}⟩ ∧
    VisibleStep cfg s ⟨s.term, s.store + {.scope q2 q1}⟩ :=
  ⟨.scopeChoice q1 q2 s hne hq1 hq2 ⟨hno12, hno21⟩,
   .scopeChoice q2 q1 s (Ne.symm hne) hq2 hq1 ⟨hno21, hno12⟩⟩

/-- Syntax reduction lifts to the full combined relation (store unchanged). -/
theorem syntax_in_gfReducesFull (cfg : VisibleCfg) (π : TemporalPolicy)
    {t1 t2 : Pattern} (σ : Multiset StoreAtom)
    (h : langReduces gfRGLLanguageDef t1 t2) :
    gfReducesFull cfg π ⟨t1, σ⟩ ⟨t2, σ⟩ :=
  Or.inl ⟨h, rfl⟩

/-! ## Base Relation (syntax + temporal, no V1–V4) -/

/-- Base reduction: syntax rewrites + temporal policy, but NO visible steps (V1–V4).

    This captures the "non-semantic" fragment: grammar derivation and temporal
    transitions that preserve the store unchanged. -/
def gfReducesBase (π : TemporalPolicy) : GrammarState → GrammarState → Prop :=
  fun s1 s2 =>
    (langReduces gfRGLLanguageDef s1.term s2.term ∧ s1.store = s2.store)
    ∨ (temporalStep π s1.term s2.term ∧ s1.store = s2.store)

/-- Base reduction preserves the store: no base step can change the store. -/
theorem gfReducesBase_preserves_store {π : TemporalPolicy} {s1 s2 : GrammarState}
    (h : gfReducesBase π s1 s2) : s1.store = s2.store := by
  cases h with
  | inl h => exact h.2
  | inr h => exact h.2

/-- Base reduction lifts to the full combined relation. -/
theorem gfReducesBase_sub_gfReducesFull (cfg : VisibleCfg) (π : TemporalPolicy)
    {s1 s2 : GrammarState} (h : gfReducesBase π s1 s2) :
    gfReducesFull cfg π s1 s2 := by
  cases h with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr (Or.inl h)

/-- Any store-changing transition is NOT a base step.
    Generic lemma: derives `scopeChoice_not_base`, `binding_not_base`,
    `refIntro_not_base` as special cases. -/
theorem store_change_not_base {π : TemporalPolicy}
    {s : GrammarState} {a : StoreAtom}
    (hno : a ∉ s.store) :
    ¬ gfReducesBase π s ⟨s.term, s.store + {a}⟩ := by
  intro hbase
  have heq : s.store = s.store + ({a} : Multiset StoreAtom) :=
    gfReducesBase_preserves_store hbase
  have hmem : a ∈ s.store + ({a} : Multiset StoreAtom) :=
    Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _))
  rw [← heq] at hmem
  exact hno hmem

/-- Scope choice is a visible step that changes the store (D.2 separation witness).

    Since `gfReducesBase_preserves_store` shows base steps never change the store,
    any store-changing transition (like scope choice) is NOT a base reduction.
    This cleanly separates the visible layer from the base relation. -/
theorem scopeChoice_not_base {π : TemporalPolicy}
    {q1 q2 : String} {s : GrammarState}
    (hno : StoreAtom.scope q1 q2 ∉ s.store) :
    ¬ gfReducesBase π s ⟨s.term, s.store + {.scope q1 q2}⟩ :=
  store_change_not_base hno

/-- Pronoun binding is NOT a base step (store changes). -/
theorem binding_not_base {π : TemporalPolicy}
    {pr r : String} {s : GrammarState}
    (hno : StoreAtom.bind pr r ∉ s.store) :
    ¬ gfReducesBase π s ⟨s.term, s.store + {.bind pr r}⟩ :=
  store_change_not_base hno

/-- Referent introduction is NOT a base step (store changes). -/
theorem refIntro_not_base {π : TemporalPolicy}
    {r : String} {pos : Pattern} {s : GrammarState}
    (hno : StoreAtom.ref r pos ∉ s.store) :
    ¬ gfReducesBase π s ⟨s.term, s.store + {.ref r pos}⟩ :=
  store_change_not_base hno

/-! ## Independence Relation (TUG Section 6.4, Definition 4) -/

/-- Two store atoms are independent if their rely footprints are disjoint.

    Independent atoms can be applied in either order with the same result. -/
def independent (a1 a2 : StoreAtom) : Prop :=
  Disjoint (relyFootprint a1) (relyFootprint a2)

/-- Independent store insertions commute (Multiset is commutative). -/
theorem independent_store_commute (σ : Multiset StoreAtom)
    (a1 a2 : StoreAtom) :
    σ + ({a1} : Multiset StoreAtom) + {a2} =
    σ + ({a2} : Multiset StoreAtom) + {a1} := by
  rw [add_assoc, add_assoc]
  congr 1
  exact add_comm ({a1} : Multiset StoreAtom) {a2}

/-- Positive example: a quantifier atom and a referent atom for different
    variables are independent (disjoint rely footprints). -/
example : independent
    (.quant "q1" (.apply "every" []) (.apply "student" []))
    (.ref "r1" (.apply "john" [])) := by
  unfold independent relyFootprint
  decide

/-- Negative example: a scope atom and a quantifier atom sharing a handle
    are NOT independent. -/
example : ¬ independent (.scope "q1" "q2")
    (.quant "q1" (.apply "a" []) (.apply "book" [])) := by
  unfold independent relyFootprint
  decide

end Mettapedia.Languages.GF.VisibleLayer
