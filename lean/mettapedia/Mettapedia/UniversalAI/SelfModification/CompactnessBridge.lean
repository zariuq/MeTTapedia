import Mettapedia.UniversalAI.SelfModification.ValueFunctions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Basic

/-!
# Compactness Bridge for Optimal Policy Existence

This module bridges the compactness machinery from ValueUnderIgnorance.lean
to prove optimal policy existence (Theorem 20) for self-modifying agents.

## Key Insight

The paper's Theorem 20 restricts to modification-independent policies.
For such policies, only the world action affects value - the policy name
component is irrelevant. So we can work with the space `History → Action`
which is compact by Tychonoff's theorem when Action is finite.

## Mathematical Structure

1. **Policy Space**: For finite Action, `ℕ → Action` is compact (Tychonoff)
2. **Value Function**: V^re is continuous in the policy (product topology)
3. **Extreme Value Theorem**: Continuous functions on compact sets achieve max

## Connection to Existing Work

We build on the compactness results in ValueUnderIgnorance.lean:
- `cantorSpace_compactSpace : CompactSpace (ℕ → Bool)` (Tychonoff for Bool)
- Generalize to `CompactSpace (ℕ → A)` for any finite A
- Apply to policy space `History → Action`

## References

- Lattimore & Hutter (2014), "General Time Consistent Discounting", Theorem 10
- Everitt et al. (2016), Appendix A
-/

namespace Mettapedia.UniversalAI.SelfModification

open BayesianAgents Topology

/-! ## Compactness of Product Spaces over Finite Types

Generalize Cantor space compactness to arbitrary finite types.
We use the discrete topology on finite types.
-/

-- Give Action the discrete topology
instance Action.topologicalSpace : TopologicalSpace Action := ⊥
instance Action.discreteTopology : DiscreteTopology Action := ⟨rfl⟩
instance Action.compactSpace : CompactSpace Action := Finite.compactSpace

-- Give History the discrete topology
instance History.topologicalSpace : TopologicalSpace History := ⊥
instance History.discreteTopology : DiscreteTopology History := ⟨rfl⟩

/-! ## World-Action Policies

For modification-independent analysis, we only care about the world action
component of policies. This gives a simpler, compact policy space.
-/

/-- A world-action policy maps histories to world actions (ignoring policy modification). -/
abbrev WorldActionPolicy := History → Action

-- Give WorldActionPolicy the product topology
instance WorldActionPolicy.topologicalSpace : TopologicalSpace WorldActionPolicy :=
  Pi.topologicalSpace

/-- The space of world-action policies is compact (finite actions, product topology).

    This follows from Tychonoff's theorem: the product of compact spaces is compact.
    Action is finite (hence compact in discrete topology), and the product over
    any index set of compact spaces is compact. -/
instance worldActionPolicy_compactSpace : CompactSpace WorldActionPolicy := by
  -- Action is compact (finite with discrete topology)
  -- Pi type of compact spaces is compact (Tychonoff)
  exact Pi.compactSpace

/-! ## Lifting World-Action Policies to Self-Mod Policies

Given a world-action policy and a fixed policy name, construct a self-mod policy.
-/

/-- Lift a world-action policy to a self-mod policy with fixed next policy name. -/
def liftToSelfModPolicy (π_world : WorldActionPolicy) (fixedName : PolicyName) :
    SelfModPolicy :=
  fun h => ⟨π_world h, fixedName⟩

/-- The lifted policy is non-modifying (always selects the fixed name). -/
theorem liftToSelfModPolicy_isNonModifying (π_world : WorldActionPolicy) (p : PolicyName) :
    (liftToSelfModPolicy π_world p).isNonModifying p := by
  intro h
  rfl

/-- The lifted policy has the same world action as the original. -/
theorem liftToSelfModPolicy_worldAction (π_world : WorldActionPolicy) (p : PolicyName)
    (h : History) : (liftToSelfModPolicy π_world p h).worldAction = π_world h := by
  rfl

/-! ## Value Function on World-Action Policies

For modification-independent utilities, the value only depends on world actions.
We can define value directly on world-action policies.
-/

/-- The realistic Q-value restricted to a fixed policy name.
    This only depends on world actions when utility is modification-independent. -/
noncomputable def qValueRealistic_worldAction (data : RealisticValueData)
    (fixedName : PolicyName) (h : History) (a_world : Action) (horizon : ℕ) : ℝ :=
  let a : PolicyModAction := ⟨a_world, fixedName⟩
  qValueRealistic data h a horizon

/-- Value function on world-action policies (for fixed policy name). -/
noncomputable def vValue_worldAction (data : RealisticValueData)
    (fixedName : PolicyName) (π_world : WorldActionPolicy) (h : History) (horizon : ℕ) : ℝ :=
  qValueRealistic_worldAction data fixedName h (π_world h) horizon

/-! ## Continuity of Value Function

The value function is continuous in the policy (in product topology).
This is because it only depends on finitely many policy values (up to horizon).
-/

/-- Value at horizon 0 is constant (hence continuous). -/
theorem vValue_worldAction_zero_continuous (data : RealisticValueData)
    (fixedName : PolicyName) (h : History) :
    Continuous (fun π_world => vValue_worldAction data fixedName π_world h 0) := by
  simp only [vValue_worldAction, qValueRealistic_worldAction, qValueRealistic]
  exact continuous_const

/-- The value function depends only on finitely many policy values.

    Key insight: vValue_worldAction only queries π at history h itself!
    The recursive calls in qValueRealistic use data.policyInterp fixedName,
    not the π_world argument. So S = {h} suffices for any horizon. -/
theorem vValue_depends_on_finite_prefix (data : RealisticValueData)
    (fixedName : PolicyName) (h : History) (horizon : ℕ) :
    ∃ (S : Finset History), ∀ π₁ π₂ : WorldActionPolicy,
      (∀ h' ∈ S, π₁ h' = π₂ h') →
      vValue_worldAction data fixedName π₁ h horizon =
      vValue_worldAction data fixedName π₂ h horizon := by
  -- vValue_worldAction only uses π at h, so S = {h} works
  use {h}
  intro π₁ π₂ heq
  -- vValue_worldAction π = qValueRealistic_worldAction ... (π h) ...
  simp only [vValue_worldAction, qValueRealistic_worldAction]
  -- If π₁ h = π₂ h, the Q-values are equal
  have hh : π₁ h = π₂ h := heq h (Finset.mem_singleton_self h)
  rw [hh]

/-- Continuity of value function in the product topology.

    The key insight: vValue_worldAction at any horizon n only depends on π_world
    at the single history h. The recursive computation uses data.policyInterp fixedName,
    not π_world. So the function factors as:

    π_world ↦ π_world h ↦ qValueRealistic_worldAction ... (π_world h) ...

    This is composition of:
    1. Projection at h: continuous (definition of product topology)
    2. Any function from Action (discrete) to ℝ: continuous

    Composition of continuous functions is continuous. -/
theorem vValue_worldAction_continuous (data : RealisticValueData)
    (fixedName : PolicyName) (h : History) (horizon : ℕ) :
    Continuous (fun π_world => vValue_worldAction data fixedName π_world h horizon) := by
  -- vValue_worldAction π_world = qValueRealistic_worldAction data fixedName h (π_world h) horizon
  -- This is composition: projection at h, then a function from Action
  simp only [vValue_worldAction]
  -- Factor as composition: π_world ↦ π_world h ↦ qValueRealistic_worldAction ... (π_world h) ...
  have h_proj : Continuous (fun π_world : WorldActionPolicy => π_world h) := continuous_apply h
  -- Any function from a discrete space is continuous
  have h_discrete : Continuous (fun a_world => qValueRealistic_worldAction data fixedName h a_world horizon) :=
    continuous_of_discreteTopology
  -- Composition
  exact h_discrete.comp h_proj

/-! ## Extreme Value Theorem for Policies

The value function achieves its maximum on the compact policy space.
-/

/-- **Key Theorem**: On the compact space of world-action policies,
    the continuous value function achieves its maximum.

    We use that:
    1. WorldActionPolicy is compact (Tychonoff)
    2. vValue is continuous (depends on finitely many coordinates)
    3. Continuous real-valued functions on nonempty compact sets achieve max -/
theorem exists_optimal_worldAction_policy (data : RealisticValueData)
    (fixedName : PolicyName) (h : History) (horizon : ℕ) :
    ∃ π_opt : WorldActionPolicy,
      ∀ π : WorldActionPolicy,
        vValue_worldAction data fixedName π h horizon ≤
        vValue_worldAction data fixedName π_opt h horizon := by
  -- The policy space is compact
  haveI : CompactSpace WorldActionPolicy := worldActionPolicy_compactSpace
  -- The value function is continuous
  have h_cont := vValue_worldAction_continuous data fixedName h horizon
  -- The space is nonempty
  have h_nonempty : (Set.univ : Set WorldActionPolicy).Nonempty := ⟨fun _ => Action.stay, trivial⟩
  -- Apply extreme value theorem: IsCompact.exists_isMaxOn
  have h_isCompact : IsCompact (Set.univ : Set WorldActionPolicy) := isCompact_univ
  obtain ⟨π_opt, _, hmax⟩ := h_isCompact.exists_isMaxOn h_nonempty h_cont.continuousOn
  exact ⟨π_opt, fun π => hmax (Set.mem_univ π)⟩

/-! ## Completing Theorem 20

We use backward induction (dynamic programming) to construct the optimal policy.
At each history h, we choose the action that maximizes Q-value.
-/

/-- Find the action with maximum Q-value (argmax over finite Action type). -/
noncomputable def argmaxAction (f : Action → ℝ) : Action :=
  -- Enumerate all actions and find the one with max value
  -- Action has 3 elements: left, right, stay
  if f Action.left ≥ f Action.right ∧ f Action.left ≥ f Action.stay then Action.left
  else if f Action.right ≥ f Action.stay then Action.right
  else Action.stay

/-- The argmax achieves the maximum.

    Proof: By case analysis on the three actions and the if-then-else conditions.
    Each case follows from the definition of argmaxAction choosing the maximum.
    - If argmax is left: h1 ensures f left ≥ f right and f left ≥ f stay
    - If argmax is right: ¬h1 ∧ h2 ensures f right ≥ max of remaining
    - If argmax is stay: ¬h1 ∧ ¬h2 ensures f stay ≥ max of remaining

    This is a finite case analysis (3 actions × 3 conditions = 9 cases),
    each being a simple inequality check. -/
theorem argmaxAction_isMax (f : Action → ℝ) (a : Action) :
    f a ≤ f (argmaxAction f) := by
  unfold argmaxAction
  split_ifs with h1 h2
  · -- argmax = left: h1 gives f left ≥ f right ∧ f left ≥ f stay
    cases a with
    | left => exact le_refl _
    | right => exact h1.1
    | stay => exact h1.2
  · -- argmax = right: ¬h1 and h2 (f right ≥ f stay)
    cases a with
    | left => -- need f left ≤ f right from ¬h1 ∧ h2
      -- h1 : ¬(f left ≥ f right ∧ f left ≥ f stay) means f left < f right ∨ f left < f stay
      -- h2 : f right ≥ f stay
      simp only [not_and_or, not_le] at h1
      cases h1 with
      | inl hlt => exact le_of_lt hlt
      | inr hlt => exact le_trans (le_of_lt hlt) h2
    | right => exact le_refl _
    | stay => exact h2
  · -- argmax = stay: ¬h1 and ¬h2
    cases a with
    | left => -- need f left ≤ f stay from ¬h1 ∧ ¬h2
      -- h1 : ¬(f left ≥ f right ∧ f left ≥ f stay) means f left < f right ∨ f left < f stay
      -- h2 : ¬(f right ≥ f stay) means f right < f stay
      simp only [not_and_or, not_le] at h1 h2
      cases h1 with
      | inl hlt => exact le_trans (le_of_lt hlt) (le_of_lt h2)
      | inr hlt => exact le_of_lt hlt
    | right => -- need f right ≤ f stay from ¬h2
      simp only [not_le] at h2
      exact le_of_lt h2
    | stay => exact le_refl _

/-- The optimal action at history h with remaining horizon n.
    Since Action is finite, we can compute the argmax. -/
noncomputable def optimalAction (data : RealisticValueData) (fixedName : PolicyName)
    (h : History) (horizon : ℕ) : Action :=
  argmaxAction (fun a => qValueRealistic_worldAction data fixedName h a horizon)

/-- The optimal world-action policy constructed by backward induction. -/
noncomputable def optimalWorldActionPolicy (data : RealisticValueData) (fixedName : PolicyName)
    (horizon : ℕ) : WorldActionPolicy :=
  fun h => optimalAction data fixedName h horizon

/-- The optimal world-action policy achieves maximum Q-value at every history. -/
theorem optimalWorldActionPolicy_isOptimal (data : RealisticValueData)
    (fixedName : PolicyName) (horizon : ℕ) (h : History) (a : Action) :
    qValueRealistic_worldAction data fixedName h a horizon ≤
    qValueRealistic_worldAction data fixedName h (optimalWorldActionPolicy data fixedName horizon h) horizon := by
  -- By construction, optimalAction chooses the maximizing action via argmax
  simp only [optimalWorldActionPolicy, optimalAction]
  -- Apply argmaxAction_isMax with the Q-value function
  exact argmaxAction_isMax (fun a' => qValueRealistic_worldAction data fixedName h a' horizon) a

/-- Theorem 20 (Correct Form): An optimal non-modifying policy exists.

    This states that among all non-modifying policies that use a fixed policy name p,
    there exists one that is optimal. The optimization is over world actions only,
    since the policy name is fixed.

    Proof by backward induction:
    1. At each history, choose the action maximizing Q-value (finite Action)
    2. This defines optimalWorldActionPolicy
    3. Lift to self-mod policy with fixed policy name
    4. The lifted policy is optimal among policies using that name, and non-modifying -/
theorem optimal_nonmodifying_policy_exists' (data : RealisticValueData)
    (fixedName : PolicyName) (horizon : ℕ) :
    ∃ (π : SelfModPolicy),
      -- Optimal among all actions with the same nextPolicyName
      (∀ h : History, h.wellFormed →
        ∀ a_world : Action,
          qValueRealistic data h ⟨a_world, fixedName⟩ horizon ≤
          qValueRealistic data h (π h) horizon) ∧
      π.isNonModifying fixedName := by
  -- Construct the optimal world-action policy
  let π_world := optimalWorldActionPolicy data fixedName horizon
  -- Lift to self-mod policy
  use liftToSelfModPolicy π_world fixedName
  constructor
  · -- Optimality among actions with same policy name
    intro h _hwf a_world
    -- The lifted policy's action is ⟨π_world h, fixedName⟩
    simp only [liftToSelfModPolicy]
    -- Apply optimalWorldActionPolicy_isOptimal
    have hopt := optimalWorldActionPolicy_isOptimal data fixedName horizon h a_world
    -- qValueRealistic_worldAction data fixedName h a_world horizon =
    -- qValueRealistic data h ⟨a_world, fixedName⟩ horizon by definition
    simp only [qValueRealistic_worldAction] at hopt
    exact hopt
  · -- Non-modifying
    exact liftToSelfModPolicy_isNonModifying π_world fixedName

end Mettapedia.UniversalAI.SelfModification
