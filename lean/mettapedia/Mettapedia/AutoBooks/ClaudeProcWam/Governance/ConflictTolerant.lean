/-
# Conflict-Tolerant Deontic Logic

Formalization of conflict-tolerant approaches to deontic reasoning,
following Robaldo (2024) and the LogiKey workbench.

## Motivation

Standard deontic logic has issues with conflicting norms. For example,
if we have both O(φ) and O(¬φ), classical SDL collapses (everything
becomes obligatory). Conflict-tolerant approaches handle such cases
gracefully.

## Key Ideas

1. **Defeasibility**: Norms can be overridden by more specific ones
2. **Prioritization**: Conflicting norms are resolved by priority ordering
3. **Non-monotonicity**: Adding new information can retract obligations

## References

- Robaldo (2024): Conflict-Tolerant Deontic RDF
- Benzmüller (2020): LogiKey Workbench
- Horty (2012): Reasons as Defaults
-/

import Mathlib.Data.Set.Basic
import Mathlib.Order.RelClasses

namespace Mettapedia.AutoBooks.ClaudeProcWam.Governance

/-! ## Defeasible Deontic Logic

A variant where obligations can be overridden.
-/

/-- Propositional variables -/
abbrev DefVar := String

/-- Defeasible deontic formulas -/
inductive DefFormula where
  | var : DefVar → DefFormula
  | tt : DefFormula
  | ff : DefFormula
  | neg : DefFormula → DefFormula
  | conj : DefFormula → DefFormula → DefFormula
  | disj : DefFormula → DefFormula → DefFormula
  | impl : DefFormula → DefFormula → DefFormula
  /-- Defeasible obligation: Ought(φ) -/
  | ought : DefFormula → DefFormula
  /-- Strict obligation: O(φ) (cannot be overridden) -/
  | strictOught : DefFormula → DefFormula
  deriving DecidableEq, Repr, Inhabited

namespace DefFormula

instance : ToString DefFormula where
  toString f := go f
where
  go : DefFormula → String
    | .var v => v
    | .tt => "⊤"
    | .ff => "⊥"
    | .neg p => s!"¬{go p}"
    | .conj p q => s!"({go p} ∧ {go q})"
    | .disj p q => s!"({go p} ∨ {go q})"
    | .impl p q => s!"({go p} → {go q})"
    | .ought p => s!"Ought({go p})"
    | .strictOught p => s!"O({go p})"

end DefFormula

/-! ## Normative Systems

A normative system consists of:
- A set of norms
- A priority ordering on norms
- Rules for conflict resolution
-/

/-- A norm: condition → obligation -/
structure CTNorm where
  id : Nat
  condition : DefFormula
  obligation : DefFormula
  deriving DecidableEq, Repr

/-- Priority relation between norms (reflexive partial order) -/
structure NormPriority where
  /-- n1 has priority over n2 -/
  priority : CTNorm → CTNorm → Prop

/-- A normative system -/
structure NormativeSystem where
  norms : List CTNorm
  priority : NormPriority
  /-- Priority is transitive -/
  trans : ∀ n1 n2 n3, priority.priority n1 n2 → priority.priority n2 n3 →
          priority.priority n1 n3

/-! ## Triggered Norms

A norm is triggered when its condition holds.
-/

/-- A world/state -/
abbrev CTWorld := Nat

/-- Valuation of propositional variables -/
abbrev CTValuation := DefVar → Bool

/-- Truth of a formula at a world (simplified, ignoring modal operators) -/
def DefFormula.holds (v : CTValuation) : DefFormula → Prop
  | .var x => v x = true
  | .tt => True
  | .ff => False
  | .neg φ => ¬φ.holds v
  | .conj φ ψ => φ.holds v ∧ ψ.holds v
  | .disj φ ψ => φ.holds v ∨ ψ.holds v
  | .impl φ ψ => φ.holds v → ψ.holds v
  | .ought _ => True  -- Simplified: obligations don't affect truth here
  | .strictOught _ => True

/-- A norm is triggered at a valuation if its condition holds -/
def CTNorm.triggered (n : CTNorm) (v : CTValuation) : Prop :=
  n.condition.holds v

/-- Set of triggered norms -/
def NormativeSystem.triggeredNorms (ns : NormativeSystem) (v : CTValuation) : Set CTNorm :=
  { n | n ∈ ns.norms ∧ n.triggered v }

/-! ## Conflict Detection and Resolution -/

/-- Two norms conflict if their obligations are contradictory -/
def CTNorm.conflicts (n1 n2 : CTNorm) : Prop :=
  n1.obligation = .neg n2.obligation ∨ n2.obligation = .neg n1.obligation

/-- A norm is defeated by higher-priority conflicting norm -/
def CTNorm.defeated (n : CTNorm) (ns : NormativeSystem) (v : CTValuation) : Prop :=
  ∃ n' ∈ ns.triggeredNorms v, n.conflicts n' ∧ ns.priority.priority n' n

/-- Undefeated obligations -/
def NormativeSystem.undefeatedObligations (ns : NormativeSystem) (v : CTValuation) : Set DefFormula :=
  { φ | ∃ n ∈ ns.triggeredNorms v, ¬n.defeated ns v ∧ φ = n.obligation }

/-! ## Properties -/

/-- A normative system is conflict-free if no two undefeated norms conflict -/
def NormativeSystem.conflictFree (ns : NormativeSystem) (v : CTValuation) : Prop :=
  ∀ n1 n2, n1 ∈ ns.triggeredNorms v → n2 ∈ ns.triggeredNorms v →
    ¬n1.defeated ns v → ¬n2.defeated ns v →
    ¬n1.conflicts n2

/-- Priority-based resolution makes systems conflict-free (when priority is total on conflicts) -/
theorem NormativeSystem.priority_resolves_conflicts
    (ns : NormativeSystem) (v : CTValuation)
    (htotal : ∀ n1 n2, n1 ∈ ns.triggeredNorms v → n2 ∈ ns.triggeredNorms v →
              n1.conflicts n2 → ns.priority.priority n1 n2 ∨ ns.priority.priority n2 n1) :
    ns.conflictFree v := by
  unfold conflictFree
  intro n1 n2 hn1_trig hn2_trig hn1_ndef hn2_ndef hconfl
  -- If n1 and n2 conflict and both are triggered, one must defeat the other
  cases htotal n1 n2 hn1_trig hn2_trig hconfl with
  | inl hp1 =>
    -- n1 has priority over n2, so n2 should be defeated
    apply hn2_ndef
    unfold CTNorm.defeated
    exact ⟨n1, hn1_trig, hconfl.symm, hp1⟩
  | inr hp2 =>
    -- n2 has priority over n1, so n1 should be defeated
    apply hn1_ndef
    unfold CTNorm.defeated
    exact ⟨n2, hn2_trig, hconfl, hp2⟩

/-! ## Specificity-Based Priority

A common approach: more specific norms override general ones.
-/

/-- A formula is more specific than another (simplified: longer condition) -/
def moreSpecific : DefFormula → DefFormula → Prop
  | .conj _ _, .var _ => True
  | .conj _ _, .tt => True
  | .conj φ1 φ2, .conj ψ1 ψ2 =>
      moreSpecific φ1 ψ1 ∨ moreSpecific φ2 ψ2
  | _, _ => False

/-- Norm n1 is more specific than n2 if its condition is more specific -/
def CTNorm.moreSpecificThan (n1 n2 : CTNorm) : Prop :=
  moreSpecific n1.condition n2.condition

/-! ## Examples -/

/-- Example: "Don't kill" vs "Kill in self-defense" -/
def exampleNorms : List CTNorm :=
  [ { id := 1, condition := .tt, obligation := .neg (.var "kill") }  -- Don't kill (general)
  , { id := 2, condition := .var "selfDefense", obligation := .var "kill" }  -- Self-defense exception
  ]

/-- Example showing moreSpecific for conjunction vs atom -/
example : moreSpecific (.conj (.var "a") (.var "b")) (.var "a") := by
  unfold moreSpecific
  trivial

end Mettapedia.AutoBooks.ClaudeProcWam.Governance
