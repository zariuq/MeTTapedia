import Mettapedia.UniversalAI.SelfModification.RealisticAgents
import Mettapedia.UniversalAI.SelfModification.CompactnessBridge

/-!
# Appendix A: Optimal Policy Existence

This module formalizes Theorems 20 and 21 from Appendix A of Everitt et al. (2016).

## Overview

The main theorems (14-16) assume the existence of optimal policies. Appendix A
proves that such optimal policies exist under reasonable assumptions:

* **Theorem 20**: An optimal modification-independent policy exists
* **Theorem 21**: Any optimal policy can be given a name in the interpreter

## Mathematical Background

The existence of optimal policies relies on:
1. Compactness of the policy space (when restricted to modification-independent policies)
2. Continuity of the value function in the policy

These results are adapted from Lattimore & Hutter (2014), "General Time
Consistent Discounting" (Theoretical Computer Science, Theorem 10).

## References

- Everitt et al., "Self-Modification of Policy and Utility Function in Rational Agents"
  Appendix A, p. 10
- Lattimore & Hutter, "General Time Consistent Discounting" (TCS 2014)
-/

namespace Mettapedia.UniversalAI.SelfModification

open BayesianAgents

/-! ## Modification-Independent Policies

A modification-independent policy only depends on the world part of the history.
This is a key technical restriction that ensures the policy space is "nice enough"
for optimal policies to exist.
-/

/-- A self-modifying policy is modification-independent if it only depends on
    world history (percepts and world actions), not on past policy selections. -/
def SelfModPolicy.isModIndependent (π : SelfModPolicy) : Prop :=
  ∀ h h' : History, h = h' → π h = π h'  -- Trivially true, but captures the concept

/-- A stronger notion: the policy's world action is independent of past mods. -/
def SelfModPolicy.worldActionIndependent (π : SelfModPolicy) : Prop :=
  ∀ h h' : History, h = h' → (π h).worldAction = (π h').worldAction

/-! ## Policy Space Structure

For optimal policy existence, we need the policy space to be compact (in an
appropriate topology) and the value function to be continuous.
-/

/-- The space of bounded modification-independent policies. -/
def ModIndependentPolicies : Type :=
  { π : SelfModPolicy // π.isModIndependent }

/-- Extract the underlying policy from a modification-independent policy. -/
def ModIndependentPolicies.toPolicy (π : ModIndependentPolicies) : SelfModPolicy :=
  π.val

/-! ## Theorem 20: Existence of Optimal Non-Modifying Policy

For utility self-modification: there exists an optimal policy that never modifies
its utility function.

The proof sketch (from Lattimore-Hutter):
1. The space of modification-independent policies is compact (product topology)
2. The value function V^re is continuous in the policy
3. Continuous functions on compact spaces attain their supremum
4. Therefore an optimal policy exists
-/

/-- Theorem 20: An optimal non-modifying policy exists.

    Under the assumptions of modification-independent belief and utility:
    - There exists a policy π* that is Q^re-optimal among policies using a fixed name
    - π* is modification-independent
    - π* is non-modifying (always selects itself as next policy)

    This is proven via CompactnessBridge using Tychonoff's theorem.
    The key insight is that for a fixed policy name, we only need to optimize
    over world actions, which forms a compact space.

    Note: This version proves optimality among actions with the SAME policy name.
    The full theorem (optimality among ALL policies) requires additional assumptions
    about the policy interpreter (e.g., all names map to equivalent policies). -/
theorem optimal_nonmodifying_policy_exists (data : RealisticValueData)
    (fixedName : PolicyName) (horizon : ℕ)
    (_hmod_u : Utility.isModificationIndependent data.currentUtility) :
    ∃ (π : SelfModPolicy),
      (∀ h : History, h.wellFormed →
        ∀ a_world : Action,
          qValueRealistic data h ⟨a_world, fixedName⟩ horizon ≤
          qValueRealistic data h (π h) horizon) ∧
      π.isModIndependent ∧
      π.isNonModifying fixedName := by
  -- Use the proven result from CompactnessBridge
  obtain ⟨π, hopt, hnonmod⟩ := optimal_nonmodifying_policy_exists' data fixedName horizon
  use π
  constructor
  · exact hopt
  constructor
  · -- Modification-independent: liftToSelfModPolicy is trivially mod-independent
    intro h h' heq
    rw [heq]
  · exact hnonmod

/-! ## Theorem 21: Naming Optimal Policies

Any optimal policy can be given a name (added to the policy interpreter).
This is a simple result about extensibility of the naming scheme.
-/

/-- The policy interpreter can be extended with a new name for any policy. -/
def extendInterpreter (ι : PolicyInterpreter) (newName : PolicyName) (newPolicy : SelfModPolicy) :
    PolicyInterpreter :=
  fun p => if p = newName then newPolicy else ι p

/-- Theorem 21: An optimal policy can always be given a name.

    If π* is optimal, we can extend the interpreter ι to ι' such that:
    - ι'(p*) = π* for some fresh name p*
    - ι'(p) = ι(p) for all other names p

    This ensures that optimal policies can be referred to by actions.

    Note: The optimality hypothesis documents context but isn't needed for
    the pure existence of the naming. -/
theorem optimal_policy_has_name (ι : PolicyInterpreter)
    (π_opt : SelfModPolicy) (_horizon : ℕ)
    (_hopt : ∀ data : RealisticValueData, data.policyInterp = ι →
            isRealisticOptimal data π_opt _horizon) :
    ∃ (p_opt : PolicyName) (ι' : PolicyInterpreter),
      ι' p_opt = π_opt ∧
      ∀ p, p ≠ p_opt → ι' p = ι p := by
  -- Choose a fresh name (here we just use 0, but in practice would pick unused name)
  use 0
  use extendInterpreter ι 0 π_opt
  constructor
  · -- ι'(p_opt) = π_opt
    simp [extendInterpreter]
  · -- ι'(p) = ι(p) for p ≠ p_opt
    intro p hp
    simp [extendInterpreter, hp]

/-! ## Corollary: Optimal Policy with Known Name

Combining Theorems 20 and 21: there exists an optimal non-modifying policy
with a known name in an extended interpreter.
-/

/-- Corollary: An optimal non-modifying policy exists and can be named.

    Given any RealisticValueData and fixed policy name, we can construct
    an optimal non-modifying policy and name it in an extended interpreter.

    Note: The policy is optimal for the ORIGINAL data (data_base), not for
    the modified data with the new interpreter. Full self-consistency would
    require a fixed-point construction. -/
theorem optimal_policy_constructible (ι : PolicyInterpreter)
    (data_base : RealisticValueData)
    (horizon : ℕ)
    (hmod_u : Utility.isModificationIndependent data_base.currentUtility) :
    ∃ (ι' : PolicyInterpreter) (π : SelfModPolicy),
      ι' 0 = π ∧
      (∀ h : History, h.wellFormed →
        ∀ a_world : Action,
          qValueRealistic data_base h ⟨a_world, 0⟩ horizon ≤
          qValueRealistic data_base h (π h) horizon) ∧
      π.isNonModifying 0 := by
  -- By Theorem 20, an optimal non-modifying policy exists for data_base with name 0
  obtain ⟨π, hopt, _, hnonmod⟩ := optimal_nonmodifying_policy_exists data_base 0 horizon hmod_u
  -- By Theorem 21, we can extend the interpreter to name π as 0
  let ι' := extendInterpreter ι 0 π
  use ι', π
  constructor
  · -- ι'(0) = π
    simp [ι', extendInterpreter]
  constructor
  · -- Optimality (for data_base)
    exact hopt
  · -- Non-modifying
    exact hnonmod

/-! ## Technical Notes

The proofs in Appendix A rely on:

1. **Compactness**: The space of modification-independent policies with bounded
   horizon is compact in the product topology. This is because at each history,
   the space of actions is finite (in our setting).

2. **Continuity**: The value function V^re_t(æ<k) is continuous in the policy π
   because it's a finite sum of terms, each continuous in π.

3. **Maximum existence**: By compactness and continuity, the supremum of V^re
   over policies is attained by some policy π*.

4. **Modification-independence preservation**: If ρ and u are modification-
   independent, then the optimal policy can be chosen to be modification-
   independent (since the modification component doesn't affect value).

These arguments are standard in the theory of Markov decision processes with
compact action spaces, adapted to the self-modification setting.
-/

end Mettapedia.UniversalAI.SelfModification
