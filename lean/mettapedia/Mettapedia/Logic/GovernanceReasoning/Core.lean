import Mettapedia.Logic.ModalMuCalculus
import Mettapedia.Logic.EvidenceQuantale

/-!
# Governance Reasoning: Core Types and Deontic Traditional Scheme

Formalization of Hobbs-style eventuality reification with ISO 24617-4 thematic roles
and the Deontic Traditional Scheme (DTS), based on the governance-reasoning-engine
(Formal-Methods-Group).

## Architecture

- §1 Thematic roles (ISO 24617-4 subset)
- §2 Eventuality, ct-triple, meta-triple data structures
- §3 DTS algebra: `ob` is primitive; `pe` and `op` are derived; all 12
    interdefinability axioms are **theorems** (not axioms)
- §4 Modal μ-calculus embedding with `DeonticAct`

## References

- Hobbs, J. (1985). "Ontological Promiscuity"
- ISO 24617-4:2014, Semantic annotation framework — Part 4: Semantic roles
- von Wright, G.H. (1951). "Deontic Logic"
- governance-reasoning-engine (Formal-Methods-Group)
-/

namespace Mettapedia.Logic.GovernanceReasoning.Core

open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.Logic.EvidenceQuantale

/-! ## §1 Thematic Roles (ISO 24617-4)

Subset of the 30+ roles from ISO 24617-4:2014, covering the most common semantic
scenarios.  Matches `governance-reasoning-engine/knowledge/role.metta`. -/

/-- Thematic/semantic role: mode of involvement of a participant in an eventuality.
    ISO 24617-4:2014, §4. -/
inductive ThematicRole where
  | agent       -- Volitional causer
  | patient     -- Entity undergoing change
  | theme       -- Entity moved / located
  | experiencer -- Sentient entity experiencing
  | beneficiary -- Entity for whose benefit
  | instrument  -- Means used
  | location    -- Spatial setting
  | time        -- Temporal setting
  | source      -- Origin / starting point
  | goal        -- Destination / endpoint
  | cause       -- Non-volitional causer
  | result      -- Outcome entity
  | manner      -- How the eventuality occurs
  | purpose     -- Intended objective
  | condition   -- Precondition or constraint
  deriving DecidableEq, Repr, Inhabited

/-! ## §2 Eventuality, ct-triple, meta-triple

### Eventualities

An eventuality (Hobbs 1985) is an event, state, process, or action that can have
participants and is being referred to by a predicate argument structure.

### ct-triple / meta-triple

- `CTTriple` = ground fact (subject, predicate, object)
- `MetaTriple` = reified fact with identity for reasoning about statements -/

/-- An eventuality with typed thematic role assignments.

    `Entity` = type of participants (agents, objects, locations, …)
    `Pred`   = type of eventuality predicates (soaMoor, soaPay, …) -/
structure Eventuality (Entity Pred : Type*) where
  /-- The eventuality predicate (e.g., soaMoor, soaPay). -/
  predicate : Pred
  /-- Thematic role assignments (partial function). -/
  roles : ThematicRole → Option Entity
  /-- Polarity: `true` = positive, `false` = negated eventuality. -/
  polarity : Bool := true
namespace Eventuality

variable {Entity Pred : Type*}

/-- Negate an eventuality (flip polarity). -/
def negate (e : Eventuality Entity Pred) : Eventuality Entity Pred :=
  { e with polarity := !e.polarity }

theorem negate_negate (e : Eventuality Entity Pred) : e.negate.negate = e := by
  simp [negate, Bool.not_not]

theorem negate_polarity (e : Eventuality Entity Pred) :
    e.negate.polarity = !e.polarity := rfl

theorem negate_predicate (e : Eventuality Entity Pred) :
    e.negate.predicate = e.predicate := rfl

theorem negate_roles (e : Eventuality Entity Pred) :
    e.negate.roles = e.roles := rfl

end Eventuality

/-- Core triple: subject–predicate–object (ground assertion).
    Matches `(ct-triple $a $b $c)` from `governance-reasoning-engine/base/triple.metta`. -/
structure CTTriple (Entity Pred : Type*) where
  subject : Entity
  predicate : Pred
  object : Entity
  deriving Repr

/-- Meta-triple: reified assertion with an identity tag for higher-order reasoning.
    Matches `(meta-triple $id $a $b $c)` from `governance-reasoning-engine/base/triple.metta`. -/
structure MetaTriple (Id Entity Pred : Type*) where
  id : Id
  subject : Entity
  predicate : Pred
  object : Entity
  deriving Repr

namespace MetaTriple

/-- Drop the identity to get the underlying ground triple. -/
def toCTTriple {Id Entity Pred : Type*} (m : MetaTriple Id Entity Pred) :
    CTTriple Entity Pred :=
  ⟨m.subject, m.predicate, m.object⟩

end MetaTriple

/-! ## §3 Deontic Traditional Scheme

The DTS provides four modalities with algebraic interdefinabilities.
We take `ob` (obligation) as primitive and **derive** `pe` (permission) and
`op` (optionality) as abbreviations.  All DTS axioms become **theorems**. -/

/-- The four deontic modalities used in the governance-reasoning-engine.
    - `rexist`: alethic modality ("really exists", Hobbs)
    - `obligatory`: deontic obligation
    - `permitted`: deontic permission
    - `optional`: deontic optionality
    Matches `governance-reasoning-engine/base/modality.metta`. -/
inductive DeonticModality where
  | rexist
  | obligatory
  | permitted
  | optional
  deriving DecidableEq, Repr, Inhabited

/-- The Deontic Traditional Scheme over a proposition type `P`.

    `ob` is the single primitive.  `pe` and `op` are derived.
    The `neg` operation must be involutive.
    The `consistent` hypothesis prevents OB(p) ∧ OB(¬p). -/
structure DTS (P : Type*) where
  /-- Obligation predicate. -/
  ob : P → Prop
  /-- Negation on propositions (involutive). -/
  neg : P → P
  /-- Negation is involutive: ¬¬p = p. -/
  neg_neg : ∀ p, neg (neg p) = p
  /-- Consistency: OB(p) and OB(¬p) cannot both hold. -/
  consistent : ∀ p, ob p → ¬ ob (neg p)

namespace DTS

variable {P : Type*} (d : DTS P)

/-! ### Derived modalities -/

/-- Permission: PE(p) ≡ ¬OB(¬p).
    Matches `governance-reasoning-engine/reason/DTS.metta` lines 14–31. -/
def pe (p : P) : Prop := ¬ d.ob (d.neg p)

/-- Optionality: OP(p) ≡ ¬OB(p) ∧ ¬OB(¬p).
    Matches `governance-reasoning-engine/reason/DTS.metta` lines 48–62. -/
def op (p : P) : Prop := ¬ d.ob p ∧ ¬ d.ob (d.neg p)

/-! ### DTS Interdefinability Theorems -/

/-- DTS Theorem 1: OB(p) ⇒ PE(p).
    Matches `(= (ct-triple-for-add $e type permitted) (ct-triple $e type obligatory))`. -/
theorem ob_implies_pe (p : P) : d.ob p → d.pe p := by
  intro hob
  exact d.consistent p hob

/-- DTS Theorem 2: PE(p) ⇔ ¬OB(¬p).  (Definitional.) -/
theorem pe_iff_not_ob_neg (p : P) : d.pe p ↔ ¬ d.ob (d.neg p) :=
  Iff.rfl

/-- DTS Theorem 3: OP(p) ⇔ ¬OB(p) ∧ ¬OB(¬p).  (Definitional.) -/
theorem op_iff (p : P) : d.op p ↔ ¬ d.ob p ∧ ¬ d.ob (d.neg p) :=
  Iff.rfl

/-- DTS Theorem 4: ¬PE(p) ⇒ OB(¬p).
    Matches `governance-reasoning-engine/reason/DTS.metta` lines 33–45. -/
theorem not_pe_implies_ob_neg (p : P) : ¬ d.pe p → d.ob (d.neg p) := by
  intro h
  exact Classical.byContradiction (fun hc => h hc)

/-- DTS Theorem 5: ¬OP(p) ⇔ OB(p) ∨ OB(¬p).
    Matches `governance-reasoning-engine/reason/DTS.metta` lines 84–106. -/
theorem not_op_iff (p : P) : ¬ d.op p ↔ d.ob p ∨ d.ob (d.neg p) := by
  simp only [op, not_and_or, Classical.not_not]

/-- DTS Theorem 6: PE(p) ∧ PE(¬p) ⇔ OP(p). -/
theorem pe_and_pe_neg_iff_op (p : P) : d.pe p ∧ d.pe (d.neg p) ↔ d.op p := by
  simp only [pe, d.neg_neg]
  exact And.comm

/-- DTS Theorem 7: OB(p) ⇒ ¬OP(p). -/
theorem ob_implies_not_op (p : P) : d.ob p → ¬ d.op p := by
  intro hob ⟨hnob, _⟩
  exact hnob hob

/-- DTS Theorem 8: OP(p) ⇒ PE(p). -/
theorem pe_of_op (p : P) : d.op p → d.pe p := by
  intro ⟨_, h2⟩
  exact h2

/-- DTS Theorem 9: OP(p) ⇒ PE(¬p). -/
theorem pe_neg_of_op (p : P) : d.op p → d.pe (d.neg p) := by
  intro ⟨h1, _⟩
  simp only [pe, d.neg_neg]
  exact h1

/-- DTS Theorem 10: Trichotomy — exactly one of OB(p), OP(p), OB(¬p) holds.
    (At-least-one direction.) -/
theorem dts_trichotomy (p : P) : d.ob p ∨ d.op p ∨ d.ob (d.neg p) := by
  by_cases hob : d.ob p
  · exact Or.inl hob
  · by_cases hob_neg : d.ob (d.neg p)
    · exact Or.inr (Or.inr hob_neg)
    · exact Or.inr (Or.inl ⟨hob, hob_neg⟩)

/-- DTS Theorem 11: At most one of OB(p), OP(p), OB(¬p) holds. -/
theorem dts_exclusive (p : P) :
    ¬ (d.ob p ∧ d.op p) ∧
    ¬ (d.ob p ∧ d.ob (d.neg p)) ∧
    ¬ (d.op p ∧ d.ob (d.neg p)) := by
  refine ⟨fun ⟨hob, hop⟩ => hop.1 hob,
          fun ⟨hob, hob_neg⟩ => d.consistent p hob hob_neg,
          fun ⟨hop, hob_neg⟩ => hop.2 hob_neg⟩

/-- DTS Theorem 12: OB(¬p) ⇒ ¬PE(p). -/
theorem ob_neg_implies_not_pe (p : P) : d.ob (d.neg p) → ¬ d.pe p := by
  intro hob_neg hpe
  exact hpe hob_neg

/-! ### Classifying propositions via DTS -/

/-- Classify a proposition into its deontic status. -/
noncomputable def classify (d : DTS P) (p : P) : DeonticModality :=
  @ite _ (d.ob p) (Classical.propDecidable _) .obligatory
    (@ite _ (d.ob (d.neg p)) (Classical.propDecidable _) .optional .permitted)

/-- Interpret an `Eventuality` under a DTS:
    the modality is determined by the obligation status and polarity. -/
noncomputable def interpretModality {Entity Pred : Type*}
    (d : DTS (Eventuality Entity Pred))
    (e : Eventuality Entity Pred) : DeonticModality :=
  classify d e

end DTS

/-! ## §4 Modal μ-Calculus Embedding

Embed the four deontic modalities as actions in the modal μ-calculus
from `ModalMuCalculus.lean`.  The deontic box/diamond operators
recover the DTS axioms under appropriate accessibility constraints. -/

/-- Actions for a deontic Kripke frame.
    Each modality has its own accessibility relation. -/
inductive DeonticAct where
  | rexist
  | obligatory
  | permitted
  | optional
  deriving DecidableEq, Repr, Inhabited

/-- Obligation formula: □_OB φ ("in all deontically ideal worlds, φ holds"). -/
def obFormula (φ : Formula DeonticAct 0) : Formula DeonticAct 0 :=
  Formula.box .obligatory φ

/-- Permission formula: ◇_PE φ ("there exists a deontically accessible world where φ holds"). -/
def peFormula (φ : Formula DeonticAct 0) : Formula DeonticAct 0 :=
  Formula.diamond .permitted φ

/-- Rexist formula: □_R φ ("φ really exists / holds in actuality"). -/
def rexistFormula (φ : Formula DeonticAct 0) : Formula DeonticAct 0 :=
  Formula.box .rexist φ

/-- Seriality condition: obligation-accessible worlds are permission-accessible.
    This is the Kripke-frame condition that makes OB(p) ⇒ PE(p) valid. -/
def DeonticSeriality (lts : LTS S DeonticAct) : Prop :=
  ∀ s, (∀ s', lts.trans s .obligatory s' → lts.trans s .permitted s')

/-- Under deontic seriality, □_OB φ ⇒ ◇_PE φ
    (i.e., obligation implies permission).

    This is the Kripke-semantic counterpart of DTS Theorem 1. -/
theorem dts_ob_pe_modal {S : Type*} (lts : LTS S DeonticAct)
    (hser : DeonticSeriality lts)
    (htotal : ∀ s, ∃ s', lts.trans s .obligatory s')
    (ρ : Env S 0) (φ : Formula DeonticAct 0) (s : S) :
    satisfies lts ρ (obFormula φ) s →
    satisfies lts ρ (peFormula φ) s := by
  intro hbox
  simp only [obFormula, peFormula, satisfies, LTS.successors, Set.mem_setOf_eq] at *
  obtain ⟨s', hs'⟩ := htotal s
  exact ⟨s', hser s s' hs', hbox s' hs'⟩

/-- The Hobbs bridge in Kripke semantics: □_R φ ⇒ φ.
    (Rexist is reflexive: what really exists, actually holds.)

    This requires the rexist accessibility relation to be reflexive. -/
theorem rexist_reflexive_bridge {S : Type*} (lts : LTS S DeonticAct)
    (hrefl : ∀ s, lts.trans s .rexist s)
    (ρ : Env S 0) (φ : Formula DeonticAct 0) (s : S) :
    satisfies lts ρ (rexistFormula φ) s →
    satisfies lts ρ φ s := by
  intro hbox
  simp only [rexistFormula, satisfies, LTS.successors, Set.mem_setOf_eq] at hbox
  exact hbox s (hrefl s)

/-- Diamond-box duality instantiated for the obligatory action. -/
theorem ob_diamond_box_dual {S : Type*} (lts : LTS S DeonticAct)
    (ρ : Env S 0) (φ : Formula DeonticAct 0) (s : S) :
    satisfies lts ρ (Formula.diamond DeonticAct.obligatory φ) s ↔
    ¬ satisfies lts ρ (Formula.box DeonticAct.obligatory (Formula.neg φ)) s :=
  diamond_box_dual lts ρ .obligatory φ s

/-- Diamond-box duality instantiated for the permitted action. -/
theorem pe_diamond_box_dual {S : Type*} (lts : LTS S DeonticAct)
    (ρ : Env S 0) (φ : Formula DeonticAct 0) (s : S) :
    satisfies lts ρ (Formula.diamond DeonticAct.permitted φ) s ↔
    ¬ satisfies lts ρ (Formula.box DeonticAct.permitted (Formula.neg φ)) s :=
  diamond_box_dual lts ρ .permitted φ s

end Mettapedia.Logic.GovernanceReasoning.Core
