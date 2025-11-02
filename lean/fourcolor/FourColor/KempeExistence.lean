import FourColor.KempeAPI
import FourColor.Triangulation
import FourColor.Geometry.Disk
import Mathlib.Data.Finset.Card
import Mathlib.Order.WellFounded

/-!
# Kempe Chain Reachability - Existence of Proper Zero-Boundary Chains

This module proves the key lemma `exists_proper_zero_boundary`: among all zero-boundary
chains (which by Lemma 4.5 are spanned by face boundaries), at least one encodes a
proper 3-edge-coloring.

## Main Result

`exists_proper_zero_boundary`: Given any nontrivial zero-boundary chain, we can reach
a proper one via Kempe switches.

## Proof Strategy (Solution A: Lexicographic Descent)

We use well-founded induction on the lexicographic measure `(#bad, #supp)` where:
- `#bad` = number of vertices where properness fails
- `#supp` = size of the support (edges with nonzero color)

At each step, we perform a Kempe switch at a bad vertex. Either:
1. The number of bad vertices strictly decreases, or
2. The number of bad vertices stays the same, but H2+H3 give us a toggle that
   strictly decreases support while preserving zero-boundary.

## References

- Goertzel (2025), Section 4: Disk Kempe-Closure Spanning
- Strategic Roadmap: `STRATEGIC_ROADMAP_2025-11-01.md`
- User guidance: Solution A from final user message

-/

namespace FourColor

open Classical Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (G : DiskGeometry V E)

/-- Lexicographic measure for well-founded descent -/
noncomputable def measurePair (incident : V → Finset E) (x : E → Color) : ℕ × ℕ :=
  ((badVerts incident x).card, (supp x).card)

/-- The lexicographic ordering on ℕ × ℕ is well-founded -/
lemma wf_measurePair (incident : V → Finset E) :
    WellFounded (fun x y : E → Color => measurePair incident x < measurePair incident y) := by
  exact InvImage.wf (measurePair incident) (wellFounded_lt (α := ℕ × ℕ))

/-- If not proper, there exists a bad vertex -/
lemma exists_bad {incident : V → Finset E} {x : E → Color} (hn : ¬taitProper incident x) :
    ∃ v, v ∈ badVerts incident x := by
  classical
  unfold taitProper at hn
  push_neg at hn
  obtain ⟨v, hv⟩ := hn
  use v
  simp [mem_badVerts]
  exact hv

/-! ## Helper lemmas for support descent -/

/-- support₁ is a subset of supp -/
lemma support₁_subset_supp {E : Type*} [Fintype E] [DecidableEq E] (x : E → Color) :
    support₁ x ⊆ supp x := by
  intro e he
  rw [mem_support₁] at he
  simp [supp]
  intro h
  rw [h] at he
  simp at he

/-- Decomposition: e ∈ supp → e ∈ support₁ ∨ e ∈ support₂ -/
lemma supp_eq_support₁_union_support₂ {E : Type*} [Fintype E] [DecidableEq E]
    (x : E → Color) (e : E) :
    e ∈ supp x ↔ e ∈ support₁ x ∨ e ∈ support₂ x := by
  constructor
  · intro h
    simp [supp] at h
    rw [mem_support₁, mem_support₂]
    by_contra hneg
    push_neg at hneg
    have : x e = (0, 0) := by
      ext <;> simp [hneg.1, hneg.2]
    contradiction
  · intro h
    simp [supp]
    cases h with
    | inl h =>
      rw [mem_support₁] at h
      intro heq
      rw [heq] at h
      simp at h
    | inr h =>
      rw [mem_support₂] at h
      intro heq
      rw [heq] at h
      simp at h

/-- Core descent lemma: Kempe switch either decreases bad-count or support -/
lemma kempe_or_support_descent
    (hNoDigons : NoDigons G)
    {x : E → Color}
    (hx : x ∈ G.asZeroBoundary.zeroBoundarySet)
    (hnz : (supp x).Nonempty)
    {v : V}
    (hbad : v ∈ badVerts G.asZeroBoundary.incident x) :
    let x' := kempeFix G.asZeroBoundary x v
    (badVerts G.asZeroBoundary.incident x').card < (badVerts G.asZeroBoundary.incident x).card
    ∨ ((badVerts G.asZeroBoundary.incident x').card = (badVerts G.asZeroBoundary.incident x).card
        ∧ (supp x').card < (supp x).card) := by
  classical
  -- Perform Kempe switch
  let x' := kempeFix G.asZeroBoundary x v

  -- Analyze the result
  by_cases h_bad_drop : (badVerts G.asZeroBoundary.incident x').card < (badVerts G.asZeroBoundary.incident x).card
  · -- Case 1: Bad-count dropped
    left
    exact h_bad_drop
  · -- Case 2: Bad-count didn't drop, need to use H2+H3 for support descent
    right
    push_neg at h_bad_drop

    -- Get an edge in the support (we have hnz : supp x nonempty)
    obtain ⟨e0, he0⟩ := hnz
    unfold supp at he0
    simp at he0

    -- supp x = support₁ x ∪ support₂ x (since x e ≠ 0 ⟺ fst ≠ 0 ∨ snd ≠ 0)
    -- Case split: is e0 in support₁ or support₂?
    by_cases h_e0_supp1 : e0 ∈ support₁ x
    · -- e0 ∈ support₁ x, apply H2+H3 for first coordinate
      -- Need to check if e0 is interior (not boundary)
      by_cases h_e0_int : e0 ∉ G.toRotationSystem.boundaryEdges
      · -- e0 is interior, can apply H2+H3
        -- Get toggle sequence from H2+H3
        obtain ⟨S₀, h_descent⟩ :=
          support₁_strict_descent_via_leaf_toggle (G := G) hNoDigons hx h_e0_supp1 h_e0_int

        -- The toggle preserves bad-count and strictly decreases support
        constructor
        · -- Bad-count preserved: toggleSum preserves zero-boundary,
          -- and doesn't change the properness structure
          sorry  -- TODO: prove toggleSum preserves or improves bad-count
        · -- Support strictly decreases
          -- We have strict descent in support₁, which implies strict descent in supp
          sorry  -- TODO: prove (supp (x + toggleSum ...)).card < (supp x).card from support₁ descent
      · -- e0 is on boundary, cannot use H2+H3 directly
        -- This case should not happen for interior-only Kempe descent
        sorry  -- TODO: handle boundary case or prove it doesn't occur
    · -- e0 ∉ support₁ x, so must be in support₂ x (since e0 ∈ supp x)
      have h_e0_in_supp : e0 ∈ supp x := by
        simp [supp]
        exact he0
      have h_e0_supp2 : e0 ∈ support₂ x := by
        -- Use the decomposition lemma
        have := (supp_eq_support₁_union_support₂ x e0).mp h_e0_in_supp
        cases this with
        | inl h1 => contradiction  -- e0 ∈ support₁ x contradicts h_e0_supp1
        | inr h2 => exact h2

      -- Apply H2+H3 for second coordinate (symmetric to first case)
      by_cases h_e0_int : e0 ∉ G.toRotationSystem.boundaryEdges
      · sorry  -- TODO: apply support₂ version of H2+H3 (exists in Disk.lean)
      · sorry  -- TODO: handle boundary case

/-- Main existence theorem via well-founded recursion -/
theorem exists_proper_zero_boundary
    (hNoDigons : NoDigons G)
    (x₀ : E → Color)
    (hx₀ : x₀ ∈ G.asZeroBoundary.zeroBoundarySet)
    (hnz : (supp x₀).Nonempty) :
    ∃ x : E → Color, x ∈ G.asZeroBoundary.zeroBoundarySet ∧ taitProper G.asZeroBoundary.incident x := by
  classical
  -- Use well-founded recursion on the SUBTYPE of zero-boundary colorings
  let incident := G.asZeroBoundary.incident

  -- Define the measure on the subtype (with nonempty support invariant)
  let ZBColorings := { x : E → Color // x ∈ G.asZeroBoundary.zeroBoundarySet ∧ (supp x).Nonempty }
  let measure : ZBColorings → ℕ × ℕ := fun ⟨x, _⟩ => measurePair incident x

  -- Lift well-foundedness to the subtype
  have wf_subtype : WellFounded (fun (a b : ZBColorings) => measure a < measure b) := by
    apply InvImage.wf measure (wellFounded_lt (α := ℕ × ℕ))

  -- Define the step function on the subtype
  have step : ∀ (xh : ZBColorings),
    (∀ yh : ZBColorings, measure yh < measure xh →
      { y : E → Color // y ∈ G.asZeroBoundary.zeroBoundarySet ∧ taitProper incident y }) →
    { y : E → Color // y ∈ G.asZeroBoundary.zeroBoundarySet ∧ taitProper incident y } := by
    intro ⟨x, hx, hnz_x⟩ IH
    -- Check if x is already proper
    by_cases hp : taitProper incident x
    · -- Base case: x is proper
      exact ⟨x, hx, hp⟩
    · -- Recursive case: x is not proper
      -- Find a bad vertex
      have hbad := exists_bad (x := x) hp
      let v := Classical.choose hbad
      have hv := Classical.choose_spec hbad
      -- Perform Kempe switch
      let x' := kempeFix G.asZeroBoundary x v
      -- x' preserves zero-boundary (THE CRUX + Patch B in action!)
      have hx'_zero : x' ∈ G.asZeroBoundary.zeroBoundarySet := by
        -- Patch B: properties now proven by kempeChain construction!
        have := kempeFix_preserves_zero G.asZeroBoundary x v (InZero.mk hx)
        exact InZero.mem this
      -- Support nonemptiness: need to prove x' also has nonempty support
      have hnz_x' : (supp x').Nonempty := by
        -- TODO: Kempe switch preserves or reduces support, never makes it empty from nonempty
        sorry
      -- Measure decreases
      have hlt : measure ⟨x', hx'_zero, hnz_x'⟩ < measure ⟨x, hx, hnz_x⟩ := by
        -- Use descent lemma
        have hdesc := kempe_or_support_descent G hNoDigons hx hnz_x hv
        -- hdesc gives: bad↓ ∨ (bad= ∧ supp↓) about kempeFix G.asZeroBoundary.incident x (Classical.choose hbad)
        -- We need: measurePair incident x' < measurePair incident x
        simp only [measure, measurePair]
        -- The goal is now: ((badVerts incident x').card, (supp x').card) < ...
        -- Need to convert from the disjunctive form to Prod.Lex
        -- First, note that incident = G.asZeroBoundary.incident and v = Classical.choose hbad
        -- so x' = kempeFix G.asZeroBoundary.incident x v definitionally
        sorry -- TODO: Convert disjunction to Prod.Lex, accounting for let bindings
      -- Apply inductive hypothesis
      exact IH ⟨x', hx'_zero, hnz_x'⟩ hlt

  -- Apply well-founded recursion
  have result := WellFounded.fix wf_subtype step ⟨x₀, hx₀, hnz⟩
  exact ⟨result.val, result.property⟩

/-
TODO: Fill the remaining sorries by:

1. **kempe_or_support_descent** (lines 110, 113, 116, 126, 130, 131):
   - Prove toggleSum preserves or improves bad-count
   - Prove support₁ descent implies supp descent
   - Handle boundary case (or prove it doesn't occur)
   - Formalize coordinate logic for support₁/support₂ decomposition
   - Apply support₂ version of H2+H3

2. **exists_proper_zero_boundary** (lines 155, 163, 166):
   - Thread zero-boundary membership through recursion context
   - Adapt kempeFix_preserves_zero to DiskGeometry setting
   - Thread hypothesis context into kempe_or_support_descent call

REFACTORING DONE:
- ✅ Changed from ZeroBoundaryData to DiskGeometry
- ✅ Added NoDigons assumption
- ✅ Integrated H2+H3 infrastructure via support₁_strict_descent_via_leaf_toggle
- ✅ Structured case analysis for support₁/support₂ descent paths
-/

end FourColor
