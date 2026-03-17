import Mettapedia.Logic.EvidenceClass
import Mettapedia.Logic.EvidenceQuantale

/-!
# PLN World Models (Posterior-State Interface)

This module defines a minimal interface for the **complete** (“distribution-passing”) PLN layer:

- A *world-model posterior state* `State` that can be revised by combining independent evidence
  sources (an `EvidenceType`, i.e. an additive commutative monoid).
- Query projections that extract **binary BinaryEvidence** (`n⁺, n⁻`) for arbitrary queries.

All truth-value notions (strength/weight/confidence/interval bounds) are **views** computed from
the extracted `BinaryEvidence`.  They are intentionally not part of the core interface.

This is the “WM judgment + query judgment” split:

- build/revise posterior states in `State`;
- answer queries by extracting evidence from the state.
-/

namespace Mettapedia.Logic.PLNWorldModel

open scoped ENNReal

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale

/-! ## Queries -/

/-- Standard PLN queries over a set of atoms: events/propositions and links/conditionals. -/
inductive AtomQuery (Atom : Type*) where
  /-- BinaryEvidence for an event/proposition. -/
  | prop : Atom → AtomQuery Atom
  /-- BinaryEvidence for a link/conditional. -/
  | link : Atom → Atom → AtomQuery Atom
  /-- BinaryEvidence for a conditional with multiple antecedents (conjunction). -/
  | linkCond : List Atom → Atom → AtomQuery Atom

/-! ## Interface -/

/-- A revisable posterior state supporting **additive** evidence-valued query extraction.

`State` is an `EvidenceType` (so revision is `+`), and queries extract `BinaryEvidence`.

The `evidence_add` law is the key commutation property:
extracting from revised states is the same as revising extracted evidence. -/
class BinaryWorldModel (State : Type*) (Query : Type*) [EvidenceType State] where
  /-- Extract binary evidence for a query. -/
  evidence : State → Query → BinaryEvidence
  /-- Extraction commutes with revision (`+`) in the world-model state. -/
  evidence_add : ∀ W₁ W₂ q, evidence (W₁ + W₂) q = evidence W₁ q + evidence W₂ q
  /-- Zero state has zero evidence for every query. -/
  evidence_zero : ∀ q, evidence 0 q = 0

namespace BinaryWorldModel

variable {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]

/-! ## Generic views (derived, not stored) -/

/-- Posterior-mean probability view of a query (improper-prior strength). -/
noncomputable def queryStrength (W : State) (q : Query) : ℝ≥0∞ :=
  BinaryEvidence.toStrength (BinaryWorldModel.evidence (State := State) (Query := Query) W q)

/-- Context-aware posterior-mean strength view of a query. -/
noncomputable def queryStrengthWith
    (ctx : BinaryContext) (W : State) (q : Query) : ℝ≥0∞ :=
  BinaryEvidence.strengthWith ctx (BinaryWorldModel.evidence (State := State) (Query := Query) W q)

/-- Confidence view of a query (with prior/context size parameter `κ`). -/
noncomputable def queryConfidence (κ : ℝ≥0∞) (W : State) (q : Query) : ℝ≥0∞ :=
  BinaryEvidence.toConfidence κ (BinaryWorldModel.evidence (State := State) (Query := Query) W q)

/-- WTV view for a query, using the canonical `BinaryEvidence → WTV` map with prior size `κ`.
This is operational plumbing; the core state remains `BinaryEvidence`. -/
noncomputable def queryWTV (κ : ℝ≥0∞) (W : State) (q : Query) : PLNWeightTV.WTV :=
  BinaryEvidence.toWTV κ (BinaryWorldModel.evidence (State := State) (Query := Query) W q)

/-- Generic context-dependent interpretation view of a query. -/
def queryInterpret
    {Ctx Val : Type*}
    [InterpretableEvidence Ctx BinaryEvidence Val]
    (ctx : Ctx) (W : State) (q : Query) : Val :=
  InterpretableEvidence.interpret ctx
    (BinaryWorldModel.evidence (State := State) (Query := Query) W q)

theorem evidence_add' (W₁ W₂ : State) (q : Query) :
    BinaryWorldModel.evidence (State := State) (Query := Query) (W₁ + W₂) q =
      BinaryWorldModel.evidence (State := State) (Query := Query) W₁ q +
        BinaryWorldModel.evidence (State := State) (Query := Query) W₂ q :=
  BinaryWorldModel.evidence_add (State := State) (Query := Query) W₁ W₂ q

/-- **Universal property**: for each query `q`, evidence extraction is an
    `AddMonoidHom` from revision states to the evidence monoid.

    This is the categorical content of the BinaryWorldModel interface:
    `fun W => evidence W q` is a morphism of additive commutative monoids.
    All five core calculus rules (additivity, commutativity, associativity,
    combine-commutativity, combine-identity) derive from this single
    algebraic condition. -/
noncomputable def evidenceHomAt (q : Query) : AddMonoidHom State BinaryEvidence where
  toFun W := BinaryWorldModel.evidence (State := State) (Query := Query) W q
  map_zero' := BinaryWorldModel.evidence_zero q
  map_add' W₁ W₂ := evidence_add' W₁ W₂ q

/-- **The bundled universal property**: evidence extraction is a single
    `AddMonoidHom` from states to evidence profiles `Query → BinaryEvidence`.

    This is the core categorical content of the BinaryWorldModel interface:
    `BinaryWorldModel State Query ≃ AddMonoidHom State (Query → BinaryEvidence)`.
    All individual `evidenceHomAt q` are projections of this one arrow. -/
noncomputable def evidenceProfileHom :
    AddMonoidHom State (Query → BinaryEvidence) where
  toFun W q := BinaryWorldModel.evidence (State := State) (Query := Query) W q
  map_zero' := funext (BinaryWorldModel.evidence_zero (State := State) (Query := Query))
  map_add' W₁ W₂ := funext (BinaryWorldModel.evidence_add W₁ W₂)

/-- Construct a `BinaryWorldModel` from a profile homomorphism (inverse direction). -/
def ofProfileHom (F : AddMonoidHom State (Query → BinaryEvidence)) :
    BinaryWorldModel State Query where
  evidence W q := F W q
  evidence_add W₁ W₂ q := congrFun (F.map_add W₁ W₂) q
  evidence_zero q := congrFun F.map_zero q

/-- `evidenceHomAt q` is evaluation-at-`q` composed with `evidenceProfileHom`. -/
theorem evidenceHomAt_eq_eval_comp (q : Query) :
    ∀ W, evidenceHomAt (State := State) (Query := Query) q W =
      (Pi.evalAddMonoidHom (fun _ : Query => BinaryEvidence) q).comp
        (evidenceProfileHom (State := State) (Query := Query)) W := by
  intro W; rfl

end BinaryWorldModel

/-! ## WM calculus judgments (sequent-style spine) -/

/-- World-model judgment: a posterior state is derivable by revision. -/
inductive WMJudgment {State : Type*} [EvidenceType State] : State → Prop
  | axiom (W : State) : WMJudgment W
  | revise {W₁ W₂ : State} : WMJudgment W₁ → WMJudgment W₂ → WMJudgment (W₁ + W₂)

notation:50 "⊢wm " W => WMJudgment W

/-- Query judgment: extracted evidence for a query from a derivable state. -/
def WMQueryJudgment {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    (W : State) (q : Query) (e : BinaryEvidence) : Prop :=
  WMJudgment W ∧ e = BinaryWorldModel.evidence (State := State) (Query := Query) W q

notation:50 "⊢q " W " ⇓ " q " ↦ " e => WMQueryJudgment W q e

namespace WMJudgment

variable {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]

/-- Context-free WM derivability is intentionally permissive: every posterior
state is available as an axiom. Nontrivial source control enters in `WMJudgmentCtx`
and `WMJudgmentMulti`. -/
theorem trivial (W : State) : ⊢wm W :=
  WMJudgment.axiom W

theorem query_of_axiom (W : State) (q : Query) :
    ⊢q W ⇓ q ↦ (BinaryWorldModel.evidence (State := State) (Query := Query) W q) := by
  exact ⟨WMJudgment.axiom W, rfl⟩

theorem query_revise {W₁ W₂ : State} {q : Query} {e₁ e₂ : BinaryEvidence} :
    (⊢q W₁ ⇓ q ↦ e₁) → (⊢q W₂ ⇓ q ↦ e₂) →
      (⊢q (W₁ + W₂) ⇓ q ↦ (e₁ + e₂)) := by
  intro h₁ h₂
  rcases h₁ with ⟨hW₁, rfl⟩
  rcases h₂ with ⟨hW₂, rfl⟩
  refine ⟨WMJudgment.revise hW₁ hW₂, ?_⟩
  simpa using
    (BinaryWorldModel.evidence_add' (State := State) (Query := Query) W₁ W₂ q).symm

/-- Query judgments are deterministic for fixed state/query: extracted evidence
is uniquely determined by `BinaryWorldModel.evidence`. -/
theorem query_deterministic {W : State} {q : Query} {e₁ e₂ : BinaryEvidence}
    (h₁ : ⊢q W ⇓ q ↦ e₁) (h₂ : ⊢q W ⇓ q ↦ e₂) :
    e₁ = e₂ := by
  rcases h₁ with ⟨_, he₁⟩
  rcases h₂ with ⟨_, he₂⟩
  calc
    e₁ = BinaryWorldModel.evidence (State := State) (Query := Query) W q := he₁
    _ = e₂ := he₂.symm

end WMJudgment

/-! ## Context-indexed WM judgments -/

/-- Context-indexed WM judgment: a posterior state is derivable from a set of axiom states.

Unlike `WMJudgment` (where any state is derivable via `axiom`), `WMJudgmentCtx Γ W`
asserts that `W` is built only from states in `Γ` (via revision). This tightens the
trust boundary: only evidence from approved sources contributes to conclusions.

Use cases:
- **Provenance**: track which data sources contributed to a posterior
- **Trust boundaries**: restrict inferences to trusted evidence pools
- **Composition**: combine independently derived posteriors with `revise` -/
inductive WMJudgmentCtx {State : Type*} [EvidenceType State]
    (Γ : Set State) : State → Prop
  | base (W : State) (hW : W ∈ Γ) : WMJudgmentCtx Γ W
  | revise {W₁ W₂ : State} :
      WMJudgmentCtx Γ W₁ → WMJudgmentCtx Γ W₂ → WMJudgmentCtx Γ (W₁ + W₂)

notation:50 "⊢wm[" Γ "] " W => WMJudgmentCtx Γ W

/-- Query judgment under a context: extracted evidence from a state derivable in Γ. -/
def WMQueryJudgmentCtx {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]
    (Γ : Set State) (W : State) (q : Query) (e : BinaryEvidence) : Prop :=
  WMJudgmentCtx Γ W ∧ e = BinaryWorldModel.evidence (State := State) (Query := Query) W q

notation:50 "⊢q[" Γ "] " W " ⇓ " q " ↦ " e => WMQueryJudgmentCtx Γ W q e

namespace WMJudgmentCtx

variable {State : Type*} [EvidenceType State]

/-- Monotonicity: enlarging the context preserves derivability. -/
theorem mono {Γ Δ : Set State} {W : State} (hSub : Γ ⊆ Δ)
    (h : ⊢wm[Γ] W) : ⊢wm[Δ] W := by
  induction h with
  | base W hW => exact .base W (hSub hW)
  | revise _ _ ih₁ ih₂ => exact .revise ih₁ ih₂

/-- The universal context recovers the original (context-free) judgment. -/
theorem of_univ {W : State} (h : ⊢wm W) : ⊢wm[Set.univ] W := by
  induction h with
  | «axiom» W => exact .base W (Set.mem_univ W)
  | revise _ _ ih₁ ih₂ => exact .revise ih₁ ih₂

/-- Every context-indexed derivation is also a context-free derivation. -/
theorem toWMJudgment {Γ : Set State} {W : State} (h : ⊢wm[Γ] W) : ⊢wm W := by
  induction h with
  | base W _ => exact .axiom W
  | revise _ _ ih₁ ih₂ => exact .revise ih₁ ih₂

/-- Context composition: revising states from different contexts yields a state
derivable from the union of contexts. -/
theorem union_revise {Γ₁ Γ₂ : Set State} {W₁ W₂ : State}
    (h₁ : ⊢wm[Γ₁] W₁) (h₂ : ⊢wm[Γ₂] W₂) :
    ⊢wm[Γ₁ ∪ Γ₂] (W₁ + W₂) :=
  .revise (mono Set.subset_union_left h₁) (mono Set.subset_union_right h₂)

variable {Query : Type*} [BinaryWorldModel State Query]

/-- Query from a context-indexed base state. -/
theorem query_of_base (Γ : Set State) (W : State) (hW : W ∈ Γ) (q : Query) :
    ⊢q[Γ] W ⇓ q ↦ (BinaryWorldModel.evidence (State := State) (Query := Query) W q) :=
  ⟨.base W hW, rfl⟩

/-- Query revision under contexts. -/
theorem query_revise {Γ : Set State} {W₁ W₂ : State} {q : Query} {e₁ e₂ : BinaryEvidence}
    (h₁ : ⊢q[Γ] W₁ ⇓ q ↦ e₁) (h₂ : ⊢q[Γ] W₂ ⇓ q ↦ e₂) :
    ⊢q[Γ] (W₁ + W₂) ⇓ q ↦ (e₁ + e₂) := by
  rcases h₁ with ⟨hW₁, rfl⟩
  rcases h₂ with ⟨hW₂, rfl⟩
  refine ⟨.revise hW₁ hW₂, ?_⟩
  simpa using
    (BinaryWorldModel.evidence_add' (State := State) (Query := Query) W₁ W₂ q).symm

/-- Context-indexed query judgments are deterministic for fixed state/query. -/
theorem query_deterministic {Γ : Set State} {W : State} {q : Query}
    {e₁ e₂ : BinaryEvidence}
    (h₁ : ⊢q[Γ] W ⇓ q ↦ e₁) (h₂ : ⊢q[Γ] W ⇓ q ↦ e₂) :
    e₁ = e₂ := by
  rcases h₁ with ⟨_, he₁⟩
  rcases h₂ with ⟨_, he₂⟩
  calc
    e₁ = BinaryWorldModel.evidence (State := State) (Query := Query) W q := he₁
    _ = e₂ := he₂.symm

end WMJudgmentCtx

/-! ## Multiset-indexed WM judgments (provenance-multiplicity-aware)

`WMJudgmentMulti` parallels `WMJudgmentCtx` but uses `Multiset State` instead of
`Set State`. This preserves provenance multiplicity: if the same CPT observation
is used twice (independently), the multiset `{|cpt, cpt|}` records both uses,
whereas `Set` would collapse to `{cpt}`.

Key design choices:
- `base` checks `W ∈ Γ` where `∈` is multiset membership
- `≤` (submultiset) replaces `⊆` for monotonicity
- `+` (multiset sum) replaces `∪` for composition
-/

/-- Multiset-indexed WM judgment: tracks provenance with multiplicity. -/
inductive WMJudgmentMulti {State : Type*} [EvidenceType State]
    (Γ : Multiset State) : State → Prop
  | base (W : State) (hW : W ∈ Γ) : WMJudgmentMulti Γ W
  | revise {W₁ W₂ : State} :
      WMJudgmentMulti Γ W₁ → WMJudgmentMulti Γ W₂ → WMJudgmentMulti Γ (W₁ + W₂)

notation:50 "⊢wmm[" Γ "] " W => WMJudgmentMulti Γ W

namespace WMJudgmentMulti

variable {State : Type*} [EvidenceType State]

/-- Monotonicity: enlarging the multiset (submultiset) preserves derivability. -/
theorem mono {Γ Δ : Multiset State} {W : State} (hSub : Γ ≤ Δ)
    (h : ⊢wmm[Γ] W) : ⊢wmm[Δ] W := by
  induction h with
  | base W hW => exact .base W (Multiset.mem_of_le hSub hW)
  | revise _ _ ih₁ ih₂ => exact .revise ih₁ ih₂

/-- Bridge to Set-based context: forget multiplicity. -/
theorem toCtx {Γ : Multiset State} {W : State} (h : ⊢wmm[Γ] W) :
    ⊢wm[{x | x ∈ Γ}] W := by
  induction h with
  | base W hW => exact .base W hW
  | revise _ _ ih₁ ih₂ => exact .revise ih₁ ih₂

/-- Every context-indexed (Multiset) derivation is also context-free. -/
theorem toWMJudgment {Γ : Multiset State} {W : State} (h : ⊢wmm[Γ] W) : ⊢wm W := by
  induction h with
  | base W _ => exact .axiom W
  | revise _ _ ih₁ ih₂ => exact .revise ih₁ ih₂

/-- Composition: revising states from different multiset contexts yields a state
derivable from the combined multiset. -/
theorem add_revise {Γ₁ Γ₂ : Multiset State} {W₁ W₂ : State}
    (h₁ : ⊢wmm[Γ₁] W₁) (h₂ : ⊢wmm[Γ₂] W₂) :
    ⊢wmm[Γ₁ + Γ₂] (W₁ + W₂) :=
  .revise (mono (Multiset.le_add_right Γ₁ Γ₂) h₁)
    (mono (Multiset.le_add_left Γ₂ Γ₁) h₂)

/-- A singleton multiset derives its sole element. -/
theorem singleton_derivable (W : State) : ⊢wmm[{W}] W :=
  .base W (Multiset.mem_singleton_self W)

/-- The sum of a nonempty multiset is derivable from it. -/
theorem sum_derivable (Γ : Multiset State) (hne : Γ ≠ 0) :
    ⊢wmm[Γ] Γ.sum := by
  induction Γ using Multiset.induction_on with
  | empty => exact absurd rfl hne
  | cons a s ih =>
    rw [Multiset.sum_cons]
    by_cases hs : s = 0
    · subst hs; simp; exact singleton_derivable a
    · exact .revise (.base a (Multiset.mem_cons_self a s))
        (mono (Multiset.le_cons_self s a) (ih hs))

end WMJudgmentMulti

/-! ## Standard prop/link wrappers (when `Query = AtomQuery Atom`) -/

namespace AtomQuery

variable {State Atom : Type*} [EvidenceType State] [BinaryWorldModel State (AtomQuery Atom)]

def propEvidence (W : State) (a : Atom) : BinaryEvidence :=
  BinaryWorldModel.evidence (State := State) (Query := AtomQuery Atom) W (.prop a)

def linkEvidence (W : State) (a b : Atom) : BinaryEvidence :=
  BinaryWorldModel.evidence (State := State) (Query := AtomQuery Atom) W (.link a b)

def linkCondEvidence (W : State) (as : List Atom) (b : Atom) : BinaryEvidence :=
  BinaryWorldModel.evidence (State := State) (Query := AtomQuery Atom) W (.linkCond as b)

noncomputable def propStrength (W : State) (a : Atom) : ℝ≥0∞ :=
  BinaryEvidence.toStrength (propEvidence (State := State) (Atom := Atom) W a)

noncomputable def linkStrength (W : State) (a b : Atom) : ℝ≥0∞ :=
  BinaryEvidence.toStrength (linkEvidence (State := State) (Atom := Atom) W a b)

noncomputable def propWTV (κ : ℝ≥0∞) (W : State) (a : Atom) : PLNWeightTV.WTV :=
  BinaryEvidence.toWTV κ (propEvidence (State := State) (Atom := Atom) W a)

noncomputable def linkWTV (κ : ℝ≥0∞) (W : State) (a b : Atom) : PLNWeightTV.WTV :=
  BinaryEvidence.toWTV κ (linkEvidence (State := State) (Atom := Atom) W a b)

theorem propEvidence_add (W₁ W₂ : State) (a : Atom) :
    propEvidence (State := State) (Atom := Atom) (W₁ + W₂) a =
      propEvidence (State := State) (Atom := Atom) W₁ a +
        propEvidence (State := State) (Atom := Atom) W₂ a := by
  simpa [propEvidence] using BinaryWorldModel.evidence_add' (State := State) (Query := AtomQuery Atom) W₁ W₂
    (.prop a)

theorem linkEvidence_add (W₁ W₂ : State) (a b : Atom) :
    linkEvidence (State := State) (Atom := Atom) (W₁ + W₂) a b =
      linkEvidence (State := State) (Atom := Atom) W₁ a b +
        linkEvidence (State := State) (Atom := Atom) W₂ a b := by
  simpa [linkEvidence] using BinaryWorldModel.evidence_add' (State := State) (Query := AtomQuery Atom) W₁ W₂
    (.link a b)

end AtomQuery

/-! ## Sort-Indexed / Typed Query Layer

Adds a sort-indexed WM interface aligned with the OSLF/NTT style:
queries are typed by a sort index `Srt` via a family `Query : Srt → Type`.

The evidence carrier and revision algebra are unchanged (`EvidenceType State`).
Only the query layer is typed.
-/

/-! ## Typed Interface -/

/-- Sort-indexed WM interface.

`Query` is a dependent family over sorts. For interoperability with untyped APIs,
queries are packaged as `Sigma Query`.
-/
class WorldModelSigma (State : Type*) (Srt : Type*) (Query : Srt → Type*)
    [EvidenceType State] where
  /-- Extract binary evidence for a typed query. -/
  evidence : State → Sigma Query → BinaryEvidence
  /-- Extraction commutes with WM revision (`+`). -/
  evidence_add : ∀ W₁ W₂ q, evidence (W₁ + W₂) q = evidence W₁ q + evidence W₂ q
  /-- Zero state has zero evidence for every query. -/
  evidence_zero : ∀ q, evidence 0 q = 0

namespace WorldModelSigma

variable {State Srt : Type*} {Query : Srt → Type*}
variable [EvidenceType State] [WorldModelSigma State Srt Query]

/-- Extract evidence using an explicit sort index. -/
def evidenceAt (W : State) {s : Srt} (q : Query s) : BinaryEvidence :=
  WorldModelSigma.evidence W ⟨s, q⟩

/-! ## Generic views -/

/-- Posterior-mean strength view for a typed query. -/
noncomputable def queryStrength (W : State) (q : Sigma Query) : ℝ≥0∞ :=
  BinaryEvidence.toStrength (WorldModelSigma.evidence W q)

/-- Context-aware posterior-mean strength view for a typed query. -/
noncomputable def queryStrengthWith
    (ctx : BinaryContext) (W : State) (q : Sigma Query) : ℝ≥0∞ :=
  BinaryEvidence.strengthWith ctx (WorldModelSigma.evidence W q)

/-- Posterior-mean strength view with explicit sort index. -/
noncomputable def queryStrengthAt (W : State) {s : Srt} (q : Query s) : ℝ≥0∞ :=
  queryStrength W ⟨s, q⟩

/-- Context-aware posterior-mean strength view with explicit sort index. -/
noncomputable def queryStrengthWithAt
    (ctx : BinaryContext) (W : State) {s : Srt} (q : Query s) : ℝ≥0∞ :=
  queryStrengthWith ctx W ⟨s, q⟩

/-- Confidence view for a typed query (with prior/context size parameter `κ`). -/
noncomputable def queryConfidence (κ : ℝ≥0∞) (W : State) (q : Sigma Query) : ℝ≥0∞ :=
  BinaryEvidence.toConfidence κ (WorldModelSigma.evidence W q)

/-- Confidence view with explicit sort index. -/
noncomputable def queryConfidenceAt
    (κ : ℝ≥0∞) (W : State) {s : Srt} (q : Query s) : ℝ≥0∞ :=
  queryConfidence κ W ⟨s, q⟩

/-- WTV view for a typed query. -/
noncomputable def queryWTV (κ : ℝ≥0∞) (W : State) (q : Sigma Query) : PLNWeightTV.WTV :=
  BinaryEvidence.toWTV κ (WorldModelSigma.evidence W q)

/-- WTV view with explicit sort index. -/
noncomputable def queryWTVAt (κ : ℝ≥0∞) (W : State) {s : Srt} (q : Query s) :
    PLNWeightTV.WTV :=
  queryWTV κ W ⟨s, q⟩

/-- Generic context-dependent interpretation view of a typed query. -/
def queryInterpret
    {Ctx Val : Type*}
    [InterpretableEvidence Ctx BinaryEvidence Val]
    (ctx : Ctx) (W : State) (q : Sigma Query) : Val :=
  InterpretableEvidence.interpret ctx (WorldModelSigma.evidence W q)

/-- Generic context-dependent interpretation view with explicit sort index. -/
def queryInterpretAt
    {Ctx Val : Type*}
    [InterpretableEvidence Ctx BinaryEvidence Val]
    (ctx : Ctx) (W : State) {s : Srt} (q : Query s) : Val :=
  queryInterpret (Query := Query) (Ctx := Ctx) (Val := Val) ctx W ⟨s, q⟩

theorem evidence_add' (W₁ W₂ : State) (q : Sigma Query) :
    WorldModelSigma.evidence (W₁ + W₂) q =
      WorldModelSigma.evidence W₁ q + WorldModelSigma.evidence W₂ q :=
  WorldModelSigma.evidence_add W₁ W₂ q

theorem evidenceAt_add (W₁ W₂ : State) {s : Srt} (q : Query s) :
    evidenceAt (W₁ + W₂) q = evidenceAt W₁ q + evidenceAt W₂ q := by
  simpa [evidenceAt] using (evidence_add' W₁ W₂ ⟨s, q⟩)

/-! ## Typed judgments -/

/-- Typed query judgment from a derivable WM state. -/
def WMQueryJudgmentSigma
    (W : State) (q : Sigma Query) (e : BinaryEvidence) : Prop :=
  WMJudgment W ∧ e = WorldModelSigma.evidence W q

notation:50 "⊢qΣ " W " ⇓ " q " ↦ " e => WMQueryJudgmentSigma W q e

/-- Typed query judgment under a context-indexed WM derivation. -/
def WMQueryJudgmentCtxSigma
    (Γ : Set State) (W : State) (q : Sigma Query) (e : BinaryEvidence) : Prop :=
  WMJudgmentCtx Γ W ∧ e = WorldModelSigma.evidence W q

notation:50 "⊢qΣ[" Γ "] " W " ⇓ " q " ↦ " e => WMQueryJudgmentCtxSigma Γ W q e

/-- Typed strength judgment from a derivable WM state. -/
def WMStrengthJudgmentSigma
    (W : State) (q : Sigma Query) (s : ℝ≥0∞) : Prop :=
  WMJudgment W ∧ s = queryStrength W q

notation:50 "⊢sΣ " W " ⇓ " q " ↦ " s => WMStrengthJudgmentSigma W q s

/-- Typed strength judgment under a context-indexed WM derivation. -/
def WMStrengthJudgmentCtxSigma
    (Γ : Set State) (W : State) (q : Sigma Query) (s : ℝ≥0∞) : Prop :=
  WMJudgmentCtx Γ W ∧ s = queryStrength W q

notation:50 "⊢sΣ[" Γ "] " W " ⇓ " q " ↦ " s => WMStrengthJudgmentCtxSigma Γ W q s

/-- Typed query judgments are deterministic for fixed state/query. -/
theorem querySigma_deterministic {W : State} {q : Sigma Query} {e₁ e₂ : BinaryEvidence}
    (h₁ : ⊢qΣ W ⇓ q ↦ e₁) (h₂ : ⊢qΣ W ⇓ q ↦ e₂) :
    e₁ = e₂ := by
  rcases h₁ with ⟨_, he₁⟩
  rcases h₂ with ⟨_, he₂⟩
  calc
    e₁ = WorldModelSigma.evidence W q := he₁
    _ = e₂ := he₂.symm

/-- Context-indexed typed query judgments are deterministic for fixed state/query. -/
theorem queryCtxSigma_deterministic {Γ : Set State} {W : State} {q : Sigma Query}
    {e₁ e₂ : BinaryEvidence}
    (h₁ : ⊢qΣ[Γ] W ⇓ q ↦ e₁) (h₂ : ⊢qΣ[Γ] W ⇓ q ↦ e₂) :
    e₁ = e₂ := by
  rcases h₁ with ⟨_, he₁⟩
  rcases h₂ with ⟨_, he₂⟩
  calc
    e₁ = WorldModelSigma.evidence W q := he₁
    _ = e₂ := he₂.symm

/-- Typed strength judgments are deterministic for fixed state/query. -/
theorem strengthSigma_deterministic {W : State} {q : Sigma Query} {s₁ s₂ : ℝ≥0∞}
    (h₁ : ⊢sΣ W ⇓ q ↦ s₁) (h₂ : ⊢sΣ W ⇓ q ↦ s₂) :
    s₁ = s₂ := by
  rcases h₁ with ⟨_, hs₁⟩
  rcases h₂ with ⟨_, hs₂⟩
  calc
    s₁ = queryStrength W q := hs₁
    _ = s₂ := hs₂.symm

/-- Context-indexed typed strength judgments are deterministic for fixed
state/query. -/
theorem strengthCtxSigma_deterministic
    {Γ : Set State} {W : State} {q : Sigma Query} {s₁ s₂ : ℝ≥0∞}
    (h₁ : ⊢sΣ[Γ] W ⇓ q ↦ s₁) (h₂ : ⊢sΣ[Γ] W ⇓ q ↦ s₂) :
    s₁ = s₂ := by
  rcases h₁ with ⟨_, hs₁⟩
  rcases h₂ with ⟨_, hs₂⟩
  calc
    s₁ = queryStrength W q := hs₁
    _ = s₂ := hs₂.symm

/-! ## Typed Rewrite Rules -/

/-- Typed evidence-level rewrite rule over sort-indexed queries. -/
structure WMRewriteRuleSigma (State : Type*) (Srt : Type*) (Query : Srt → Type*)
    [EvidenceType State] [WorldModelSigma State Srt Query] where
  /-- Side conditions (Σ). -/
  side : Prop
  /-- The conclusion query. -/
  conclusion : Sigma Query
  /-- Derived evidence term from the WM state. -/
  derive : State → BinaryEvidence
  /-- Soundness under side conditions. -/
  sound : side → ∀ W : State, derive W = WorldModelSigma.evidence W conclusion

/-- Typed strength-level rewrite rule over sort-indexed queries. -/
structure WMStrengthRuleSigma (State : Type*) (Srt : Type*) (Query : Srt → Type*)
    [EvidenceType State] [WorldModelSigma State Srt Query] where
  side : Prop
  conclusion : Sigma Query
  derive : State → ℝ≥0∞
  sound : side → ∀ W : State, derive W = queryStrength W conclusion

namespace WMRewriteRuleSigma

variable {State Srt : Type*} {Query : Srt → Type*}
variable [EvidenceType State] [WorldModelSigma State Srt Query]

theorem apply {r : WMRewriteRuleSigma State Srt Query} {W : State} :
    r.side → (⊢wm W) → (⊢qΣ W ⇓ r.conclusion ↦ r.derive W) := by
  intro hSide hW
  exact ⟨hW, r.sound hSide W⟩

theorem applyCtx {r : WMRewriteRuleSigma State Srt Query} {Γ : Set State} {W : State} :
    r.side → (⊢wm[Γ] W) → (⊢qΣ[Γ] W ⇓ r.conclusion ↦ r.derive W) := by
  intro hSide hW
  exact ⟨hW, r.sound hSide W⟩

end WMRewriteRuleSigma

namespace WMStrengthRuleSigma

variable {State Srt : Type*} {Query : Srt → Type*}
variable [EvidenceType State] [WorldModelSigma State Srt Query]

theorem apply {r : WMStrengthRuleSigma State Srt Query} {W : State} :
    r.side → (⊢wm W) → (⊢sΣ W ⇓ r.conclusion ↦ r.derive W) := by
  intro hSide hW
  exact ⟨hW, r.sound hSide W⟩

theorem applyCtx {r : WMStrengthRuleSigma State Srt Query} {Γ : Set State} {W : State} :
    r.side → (⊢wm[Γ] W) → (⊢sΣ[Γ] W ⇓ r.conclusion ↦ r.derive W) := by
  intro hSide hW
  exact ⟨hW, r.sound hSide W⟩

end WMStrengthRuleSigma

/-! ## Interop Adapters -/

/-- Every typed WM induces an untyped WM over `Sigma Query`. -/
def toWorldModelSigma
    (State : Type*) (Srt : Type*) (Query : Srt → Type*)
    [EvidenceType State] [WorldModelSigma State Srt Query] :
    BinaryWorldModel State (Sigma Query) where
  evidence := WorldModelSigma.evidence
  evidence_add := WorldModelSigma.evidence_add
  evidence_zero := WorldModelSigma.evidence_zero

/-- Any untyped WM over `Sigma Query` can be viewed as a typed WM. -/
def ofWorldModelSigma
    (State : Type*) (Srt : Type*) (Query : Srt → Type*)
    [EvidenceType State] [BinaryWorldModel State (Sigma Query)] :
    WorldModelSigma State Srt Query where
  evidence := BinaryWorldModel.evidence
  evidence_add := BinaryWorldModel.evidence_add
  evidence_zero := BinaryWorldModel.evidence_zero

/-- Any untyped WM can be trivially typed with one sort (`PUnit`). -/
def ofWorldModelUnit
    (State : Type*) (Query : Type*)
    [EvidenceType State] [BinaryWorldModel State Query] :
    WorldModelSigma State PUnit (fun _ => Query) where
  evidence W q := BinaryWorldModel.evidence W q.2
  evidence_add W₁ W₂ q := BinaryWorldModel.evidence_add W₁ W₂ q.2
  evidence_zero q := BinaryWorldModel.evidence_zero q.2

end WorldModelSigma

end Mettapedia.Logic.PLNWorldModel
