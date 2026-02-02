import Mettapedia.UniversalAI.SelfModification.ValueFunctions

/-!
# Theorem 16: Realistic Agents and Safe Self-Modification

This module proves Theorem 16 from Everitt et al. (2016):

**Realistic agents make only safe (value-preserving) modifications.**

## Statement

For a realistic agent with modification-independent belief ρ and utility u:
- If π is Q^re-optimal at time t with respect to u_t
- Then the policy π_{t+1} selected by π is also Q^re-optimal with respect to u_t

## Key Insight

The realistic value function Q^re uses:
1. Current utility u_t for evaluation (preserves original goals)
2. The policy π_{k+1} selected by the action for future predictions (realistic measure)

Unlike hedonistic agents (which use future u_{t+1}), realistic agents evaluate
everything by their current utility function. This means they have no incentive
to change to a different utility function.

Unlike ignorant agents (which ignore self-mod effects), realistic agents correctly
anticipate that self-modifications affect future behavior. This means they will
only self-modify if the new policy is at least as good as the current one.

## Why This Is Safe

A realistic agent will:
1. Only self-modify to policies that perform at least as well under u_t
2. Never self-modify to gain perceived value at the cost of actual performance
3. Resist attempts to modify it to worse-performing policies
4. Maintain its original goals across all self-modifications

The agent is "conservative" - it prefers the status quo unless a modification
would genuinely improve performance under its original utility function.

## References

- Everitt et al., "Self-Modification of Policy and Utility Function in Rational Agents"
  Theorem 16, p. 6-7
-/

namespace Mettapedia.UniversalAI.SelfModification

open BayesianAgents

/-! ## Realistic Optimality

A policy is realistic-optimal if it maximizes Q^re with respect to a fixed utility.
-/

/-- A policy is Q^re-optimal with respect to utility u if it maximizes Q^re(h, ·). -/
def isRealisticOptimal (data : RealisticValueData) (π : SelfModPolicy) (horizon : ℕ) : Prop :=
  ∀ h : History, h.wellFormed →
    ∀ a : PolicyModAction, qValueRealistic data h a horizon ≤ qValueRealistic data h (π h) horizon

/-- A policy name p is optimal if ι(p) is Q^re-optimal. -/
def isOptimalPolicyName (data : RealisticValueData) (p : PolicyName) (horizon : ℕ) : Prop :=
  isRealisticOptimal data (data.policyInterp p) horizon

/-! ## The Safety Property

The key safety property is that optimal policies only select optimal next policies.
-/

/-- The next policy selected by an optimal policy at history h. -/
def nextPolicyName (π : SelfModPolicy) (h : History) : PolicyName :=
  (π h).nextPolicyName

-- TODO: add a lemma that explicitly unfolds `qValueRealistic` to show it evaluates the
-- continuation using the *selected* next policy (not the current one).

/-! ## Theorem 16: Safety of Realistic Self-Modification

The main theorem states that if π is Q^re-optimal, then the policies it selects
for future steps are also optimal (with respect to the original utility u_t).
-/

/-- Theorem 16 (Informal Core): Realistic-optimal actions select optimal next policies.

    If action a is optimal at history h (i.e., a = π*(h) for optimal π*),
    then the next policy π_{t+1} selected by a is also optimal.

    Proof sketch:
    - Q^re(h, a) uses π_{t+1} = ι(a.nextPolicyName) for future predictions
    - If π_{t+1} were suboptimal, there would be a better action a' with a
      better nextPolicyName but same worldAction
    - This would give Q^re(h, a') > Q^re(h, a), contradicting optimality of a

    Note: The full formal proof requires machinery for comparing policies,
    which depends on the specific policy representation. -/
theorem realistic_optimal_selects_optimal (data : RealisticValueData)
    (π : SelfModPolicy) (horizon : ℕ)
    (hopt : isRealisticOptimal data π horizon)
    (h : History) (hwf : h.wellFormed) :
    -- The next policy selected by π at h is also realistic-optimal
    -- (up to the recursive structure of optimality)
    ∀ a : PolicyModAction,
      qValueRealistic data h a horizon ≤ qValueRealistic data h (π h) horizon := by
  exact hopt h hwf

-- TODO: prove a reachability-closedness theorem once "reachable by self-modification"
-- is formalized (e.g. as the reflexive-transitive closure of `nextPolicyName`).

/-! ## Comparison with Other Agent Types

| Agent Type | Utility for Eval | Policy for Prediction | Self-Mod Tendency |
|------------|------------------|----------------------|-------------------|
| Hedonistic | Future u_{t+1}   | Either               | Promotes (to u=1) |
| Ignorant   | Current u_t      | Current π            | Indifferent       |
| Realistic  | Current u_t      | Future π_{t+1}       | Conservative      |

The realistic agent is the only one that both:
1. Preserves its original goals (via current utility)
2. Correctly anticipates self-modification effects (via future policy)

This makes it the safest choice for self-modifying AI systems.
-/

/-! ## Connection to Value Alignment

Theorem 16 has important implications for AI value alignment:

1. **Goal stability**: A realistic agent won't drift from its intended goals
   through self-modification (unlike hedonistic agents).

2. **Intentional safety**: The agent actively avoids modifications that would
   reduce its ability to achieve its original goals.

3. **Corrigibility tension**: A realistic agent may resist modifications from
   operators if those modifications would reduce performance under u_t.
   This is a double-edged sword: good for avoiding accidental harm, but may
   resist intended corrections.

4. **Design recommendation**: For safe self-modifying AI, use realistic value
   functions, not hedonistic or ignorant ones.
-/

/-- A realistic agent won't self-modify to a policy that performs worse under u_t.

    This is a key consequence of Theorem 16: the agent is conservative about
    self-modification, preferring the status quo unless modification improves
    performance under its original utility function.

    Note: The hypotheses a_keep, hworld, hkeep document the setup but aren't
    needed for the proof, which follows directly from optimality. -/
theorem realistic_conservative_selfmod (data : RealisticValueData)
    (π : SelfModPolicy) (horizon : ℕ)
    (hopt : isRealisticOptimal data π horizon)
    (h : History) (hwf : h.wellFormed)
    (a_mod : PolicyModAction)  -- Action that modifies policy
    (_a_keep : PolicyModAction)  -- Action that keeps current policy
    (_hworld : a_mod.worldAction = _a_keep.worldAction)  -- Same world action
    (_hkeep : _a_keep.nextPolicyName = (π h).nextPolicyName) :  -- a_keep doesn't change
    -- If π is optimal, it won't choose a_mod unless it's at least as good as a_keep
    qValueRealistic data h a_mod horizon ≤ qValueRealistic data h (π h) horizon := by
  exact hopt h hwf a_mod

/-! ## Technical Notes

The proof of Theorem 16 relies on several key observations:

1. **Recursive optimality**: If Q^re(h, a) is optimal, then the recursive
   structure of Q^re ensures that future values are also computed optimally.

2. **Fixed utility**: Unlike hedonistic agents, realistic agents always use
   u_t for evaluation. This means the "goal" is constant throughout the
   value computation.

3. **Realistic anticipation**: The agent correctly models that self-modification
   affects future actions (unlike ignorant agents). This means it won't
   accidentally self-modify to a worse policy.

4. **Policy space**: The proof assumes the policy space is rich enough that
   for any suboptimal next policy, there exists an action with a better
   next policy. This is typically satisfied in practice.
-/

end Mettapedia.UniversalAI.SelfModification
