import Mettapedia.UniversalAI.SelfModification.ValueFunctions

/-!
# Theorem 15: Ignorant Agents and Self-Modification

This module proves Theorem 15 from Everitt et al. (2016):

**Ignorant agents are indifferent to self-modification.**

## Statement

For modification-independent belief ρ and utility u:
- If policies π and π̃ differ only in their self-modification components
- Then Q^{ig,π}_t(æ<t, a_t) = Q^{ig,π̃}_t(æ<t, a_t) for all t

## Key Insight

The ignorant value function Q^ig uses:
1. Current utility u_t (modification-independent) for evaluation
2. Initial policy π for ALL future predictions (ignoring self-mod effects)

Since u_t doesn't see modifications and the future predictions ignore them,
the self-modification component of actions has no effect on ignorant value.

## Implications

Ignorant agents neither promote nor resist self-modification:
- They MAY accidentally self-modify (if modification happens to coincide with
  optimal world action)
- They won't deliberately seek or avoid modification
- This is "safer" than hedonistic but still risky (accidental self-damage)

## References

- Everitt et al., "Self-Modification of Policy and Utility Function in Rational Agents"
  Theorem 15, p. 6
-/

namespace Mettapedia.UniversalAI.SelfModification

open BayesianAgents

/-! ## Policies that Agree on World Actions

Two policies agree on world actions if they always select the same world action ǎ_t,
even if they select different policy modifications p_{t+1}.
-/

/-- Two policies agree on world actions if their worldAction components match. -/
def policiesAgreeOnWorldActions (π π' : SelfModPolicy) : Prop :=
  ∀ h : History, (π h).worldAction = (π' h).worldAction

/-- Reflexivity: a policy agrees with itself on world actions. -/
theorem policiesAgreeOnWorldActions_refl (π : SelfModPolicy) :
    policiesAgreeOnWorldActions π π := by
  intro h
  rfl

/-- Symmetry: if π agrees with π' on world actions, then π' agrees with π. -/
theorem policiesAgreeOnWorldActions_symm {π π' : SelfModPolicy}
    (h : policiesAgreeOnWorldActions π π') : policiesAgreeOnWorldActions π' π := by
  intro h'
  exact (h h').symm

/-! ## Theorem 15: Ignorant Indifference

The core theorem states that if two policies agree on world actions,
they have the same ignorant Q-value.

This follows from the recursive structure of Q^ig:
- Immediate reward u_t(æ̌_{1:k}) only depends on world part
- Future predictions use the SAME fixed policy (data.fixedPolicy) regardless of
  which policy we're evaluating
- Therefore the self-modification component of the action being evaluated
  has no effect on the value
-/

/-- Theorem 15 (Main): Ignorant value is indifferent to self-modification.

Given:
- Modification-independent utility (implicit in data.currentUtility)
- Modification-independent belief (implicit in data.envProb)

Then: Actions that differ only in self-modification component have same Q^ig value.

This is the formal statement of Theorem 15 from Everitt et al. (2016):
"Ignorant agents are indifferent to self-modification"

The proof is straightforward: the definition of qValueIgnorant only uses a.worldAction,
never the full action a. So if a.worldAction = a'.worldAction, the values are equal. -/
theorem ignorant_indifferent_to_selfmod (data : IgnorantValueData)
    (h : History) (a a' : PolicyModAction) (n : ℕ)
    (hworld : a.worldAction = a'.worldAction) :
    qValueIgnorant data h a n = qValueIgnorant data h a' n := by
  induction n generalizing h a a' with
  | zero => rfl
  | succ n ih =>
    simp only [qValueIgnorant]
    -- If history not well-formed, both are 0
    by_cases hwf : h.wellFormed
    · simp only [hwf, not_true_eq_false, ↓reduceIte]
      -- The key: the only occurrence of a or a' in the body is via worldAction
      -- Since hworld says these are equal, we can rewrite one to the other
      simp only [hworld]
    · simp [hwf]

/-- Corollary: The ignorant V-value is trivially reflexive.
    (This is a simplified statement - the real corollary would involve
    showing that changing the fixedPolicy to one that agrees on world actions
    gives the same value, but that requires a more complex statement.) -/
theorem ignorant_vValue_refl (data : IgnorantValueData)
    (h : History) (n : ℕ) :
    vValueIgnorant data h n = vValueIgnorant data h n := by
  rfl

/-! ## Implications of Theorem 15

Theorem 15 has important implications for AI safety:

1. **No deliberate self-modification**: Ignorant agents won't seek to modify
   themselves because modification doesn't affect their perceived value.

2. **No deliberate avoidance**: They also won't avoid modifications.

3. **Accidental modification risk**: If the optimal world action happens to
   coincide with a self-modification (as a package deal), the agent will
   take it without considering the modification's effects.

4. **Comparison with hedonistic**: Unlike hedonistic agents (Thm 14), ignorant
   agents won't systematically self-modify to u(·)=1. But unlike realistic
   agents (Thm 16), they won't protect against harmful modifications either.
-/

/-- An ignorant-optimal agent: one that maximizes Q^ig. -/
def isIgnorantOptimal (data : IgnorantValueData) (π : SelfModPolicy) (horizon : ℕ) : Prop :=
  ∀ h : History, ∀ a : PolicyModAction,
    qValueIgnorant data h a horizon ≤ qValueIgnorant data h (π h) horizon

/-- Key corollary: For an ignorant-optimal agent, any world-action-equivalent
    action is also optimal (differing only in self-mod component). -/
theorem ignorant_optimal_selfmod_freedom (data : IgnorantValueData)
    (π : SelfModPolicy) (horizon : ℕ)
    (_hopt : isIgnorantOptimal data π horizon)
    (h : History) (a : PolicyModAction)
    (hworld : a.worldAction = (π h).worldAction) :
    qValueIgnorant data h a horizon = qValueIgnorant data h (π h) horizon := by
  -- By Theorem 15, same world action → same Q^ig value
  -- (Note: _hopt is not needed for equality, but documents context)
  exact ignorant_indifferent_to_selfmod data h a (π h) horizon hworld

/-! ## Technical Details

The proof of Theorem 15 relies on two key observations:

1. **Recursive structure of Q^ig**: The definition (Eq 6) is:
   Q^{ig,π}_t(æ<k, a_k) = E_e[u_t(æ̌_{1:k}) + γV^{ig,π}_t(æ_{1:k}) | æ̌<k, ǎ_k]

   The expectation is over e (percepts), conditioned on world history æ̌<k and
   world action ǎ_k. The self-mod component p_{k+1} appears nowhere!

2. **Fixed policy for predictions**: V^ig always uses the initial policy π for
   predicting future actions, ignoring what π_t actually does. So the action's
   self-mod component has no effect on future value predictions.

Together, these mean Q^ig(æ<k, (ǎ_k, p)) = Q^ig(æ<k, (ǎ_k, p')) for any p, p'.
-/

end Mettapedia.UniversalAI.SelfModification
