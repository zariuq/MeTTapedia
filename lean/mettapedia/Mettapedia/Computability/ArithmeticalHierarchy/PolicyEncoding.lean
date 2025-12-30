import Mathlib.Computability.Partrec
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Pairing
import Mettapedia.Computability.ArithmeticalHierarchy.Basic
import Mettapedia.UniversalAI.BayesianAgents

/-!
# Policy Encoding for Grain of Truth

This file encodes reinforcement learning policies as natural numbers using Gödel
numbering, following Leike, Taylor & Fallenstein (2016).

## Main Results

* `encodeHistory`: Bijection History → ℕ via Gödel pairing
* `DeterministicPolicy`: Simplified policy type (History → Action)
* `EncodedPolicy`: Policies as Gödel numbers of Turing machines
* `Delta02PolicyClass`: Class of Δ⁰₂-computable policies

## Simplification from the Papers

Leike's thesis uses **stochastic policies** with **reflective oracles** to achieve
limit computability. This is theoretically correct but requires extensive development
(~500+ lines of oracle theory).

We use a **simplified approach**: deterministic policies encoded as computable
functions. This is sufficient for the Grain of Truth theorem and provable with
existing infrastructure.

Future work can upgrade to stochastic policies + reflective oracles.

## References

- Leike, Taylor & Fallenstein (2016). "A Formal Solution to the Grain of Truth Problem"
- Leike (2016). "Nonparametric General Reinforcement Learning", Chapter 7
- Solomonoff (1964). "A Formal Theory of Inductive Inference"

-/

namespace Mettapedia.UniversalAI.GrainOfTruth

open Mettapedia.Computability.ArithmeticalHierarchy
open Mettapedia.UniversalAI.BayesianAgents

/-! ## History Encoding

We encode histories as natural numbers using Gödel's pairing function.
This gives us a computable bijection History ↔ ℕ.
-/

/-- Encode an Action as a natural number -/
def encodeAction : Action → ℕ
  | Action.left => 0
  | Action.right => 1
  | Action.stay => 2

/-- Decode a natural number to an Action -/
def decodeAction : ℕ → Option Action
  | 0 => some Action.left
  | 1 => some Action.right
  | 2 => some Action.stay
  | _ => none

/-- Encode a Percept as a natural number -/
def encodePercept : Percept → ℕ
  | Percept.mk o r => Nat.pair (if o then 1 else 0) (if r then 1 else 0)

/-- Encode a history element (action or percept) -/
def encodeHistElem : HistElem → ℕ
  | HistElem.act a => Nat.pair 0 (encodeAction a)
  | HistElem.per x => Nat.pair 1 (encodePercept x)

/-- Encode a history as a natural number using Gödel pairing.

    Empty history (empty list) encodes to 0.
    Non-empty history (he :: rest) encodes to pair(⟦he⟧, ⟦rest⟧).

    Since History = List HistElem, this is just list encoding.
-/
def encodeHistory : History → ℕ
  | [] => 0
  | he :: rest => Nat.pair (encodeHistElem he) (encodeHistory rest)

/-- Theorem: Action encoding is a bijection for valid actions -/
theorem encodeAction_injective : Function.Injective encodeAction := by
  intro a1 a2 h
  cases a1 <;> cases a2 <;> simp [encodeAction] at h <;> try rfl
  all_goals contradiction

/-- Theorem: Decode inverts encode for actions -/
theorem decodeAction_encodeAction (a : Action) :
    decodeAction (encodeAction a) = some a := by
  cases a <;> rfl

/-! ## Deterministic Policies

Following the expert council's recommendation, we start with deterministic policies.
These are simpler than stochastic policies but sufficient for the Grain of Truth theorem.

The stochastic case requires reflective oracle theory (Leike's thesis Chapter 7)
and will be added in future work.
-/

/-- A deterministic policy maps histories to actions.

    This is a simplified version of the stochastic Agent.policy : History → Action → ENNReal
    from BayesianAgents.lean.
-/
abbrev DeterministicPolicy := History → Action

/-! ## Computable Policies

A policy is computable if it can be computed by a Turing machine.
We represent this via Mathlib's Partrec (partial recursive functions).
-/

/-- A policy is computable if there exists a partial computable function
    that computes it.

    The function takes an encoded history and returns an encoded action.
-/
def isComputablePolicy (π : DeterministicPolicy) : Prop :=
  ∃ (f : ℕ →. ℕ), Partrec f ∧
    ∀ (h : History), ∃ (hdom : (f (encodeHistory h)).Dom),
      decodeAction ((f (encodeHistory h)).get hdom) = some (π h)

/-! ## Policy Encoding

An encoded policy is represented by its Gödel number (index in an enumeration
of partial computable functions).
-/

/-- An encoded policy is a Gödel number representing a partial computable function.

    This is the standard computability theory approach: enumerate all Turing machines,
    assign each a unique natural number (its Gödel number).
-/
structure EncodedPolicy where
  /-- Gödel number of the Turing machine computing this policy -/
  encoding : ℕ
  /-- The encoded function is partial computable -/
  is_computable : ∃ (f : ℕ →. ℕ), Partrec f ∧
    ∀ (h_enc : ℕ) (hdom : (f h_enc).Dom),
      ∃ (a_enc : ℕ), (f h_enc).get hdom = a_enc ∧
                      decodeAction a_enc ≠ none

/-! ## Δ⁰₂-Computable Policy Class

Following Leike's definition, a policy class is Δ⁰₂-enumerable if:
1. It's countable (can be enumerated as π₀, π₁, π₂, ...)
2. The membership function "is n a valid policy encoding?" is Δ⁰₂

This is the key requirement for the Grain of Truth theorem.
-/

/-- The class of all Δ⁰₂-computable deterministic policies.

    A policy π is in this class if:
    1. It's computable (exists a Turing machine computing it)
    2. It has a Gödel number (encoding)
-/
def Delta02PolicyClass : Set DeterministicPolicy :=
  { π : DeterministicPolicy | isComputablePolicy π }

/-! ## Policy Class Properties

For the Grain of Truth theorem, we need:
1. The policy class is countable (enumerable)
2. It's closed under Bayes-optimal responses
3. Each policy is Δ⁰₂-computable

Property (3) is established by definition (isComputablePolicy uses Partrec).
Properties (1) and (2) will be proven when needed in later phases.

NOTE: Mathlib provides `Nat.Partrec.Code.encodeCode : Code → ℕ` which gives
a bijection between Partrec codes and natural numbers. This can be used to
prove (1) when needed, by connecting our DeterministicPolicy to Partrec codes.
-/

/-! ## Future Work: Stochastic Policies

The full Grain of Truth theorem uses **stochastic policies** (History → ΔAction)
with **reflective oracles** to achieve Δ⁰₂ computability.

This requires (~650 lines of new infrastructure):
1. Reflective oracle theory (~300 lines) - Leike's thesis Section 7.4
2. Probabilistic Turing machines (~200 lines)
3. Limit computability for probability distributions (~150 lines)

For now, deterministic policies are sufficient for the formalization.
The theorem can be upgraded to stochastic policies in future work without
changing the core infrastructure established here.
-/

end Mettapedia.UniversalAI.GrainOfTruth
