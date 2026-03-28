import Mettapedia.Computability.PNP.PostSwitchInputObstruction
import Mettapedia.Computability.PNP.ResolutionDemandObstruction
import Mettapedia.Computability.PNP.InvariantScoreObstruction
import Mathlib.Tactic

/-!
# P vs NP crux: the exact post-switch input forces a sharp fork

The paper's exact local input is `u_i = (z, a_i, b)` and its involution acts by
`b ↦ b ⊕ a_i`.  Combined with the earlier symmetry-budget files, this gives a
clean specialized fork:

* if we keep only the invariant projection `(z, a_i)`, every symmetry-respecting
  soft score has zero signed correlation with the flipped target;
* if we also keep `b` as a side channel, then any success advantage over chance
  is bounded by the mass on nonzero VV columns, because those are exactly the
  points where `b` separates an involution pair.

This file packages that exact manuscript bridge in Lean.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {k : ℕ}

noncomputable instance instFintypePostSwitchInput [Fintype Z] :
    Fintype (PostSwitchInput Z k) := by
  classical
  let e : PostSwitchInput Z k ≃ ((Z × BitVec k) × BitVec k) := by
    refine
      { toFun := fun u => ((PostSwitchInput.z u, PostSwitchInput.a u), PostSwitchInput.b u)
        invFun := fun t => ⟨t.1.1, t.1.2, t.2⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro u
      cases u
      rfl
    · intro t
      cases t
      rfl
  exact Fintype.ofEquiv ((Z × BitVec k) × BitVec k) e.symm

instance instDecidablePredNonzeroColumn :
    DecidablePred (fun u : PostSwitchInput Z k => nonzeroColumn u.a) := by
  intro u
  classical
  unfold nonzeroColumn
  infer_instance

@[simp] theorem vvToggle_vvToggle (a b : BitVec k) :
    vvToggle a (vvToggle a b) = b := by
  funext i
  cases hai : a i <;> cases hbi : b i <;> simp [vvToggle, Bool.xor, hai, hbi]

theorem tiInputMap_involutive : Function.Involutive (@tiInputMap Z k) := by
  intro u
  cases u
  simp [tiInputMap, vvToggle_vvToggle]

theorem unresolvedBySideChannel_tiInputMap_b_iff_zeroColumn
    (u : PostSwitchInput Z k) :
    unresolvedBySideChannel tiInputMap (fun x => x.b) u ↔ u.a = zeroVec := by
  cases u
  simp [unresolvedBySideChannel, tiInputMap, vvToggle_eq_self_iff_zero]

theorem resolvedBySideChannel_tiInputMap_b_iff_nonzeroColumn
    (u : PostSwitchInput Z k) :
    ¬ unresolvedBySideChannel tiInputMap (fun x => x.b) u ↔ nonzeroColumn u.a := by
  rw [unresolvedBySideChannel_tiInputMap_b_iff_zeroColumn]
  simpa using (nonzeroColumn_iff_ne_zero u.a).symm

theorem weighted_signedScore_sum_eq_zero_on_invariantProjection
    [Fintype Z]
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (score : Z × BitVec k → ℤ)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u) :
    ∑ u : PostSwitchInput Z k,
      (w u : ℤ) * score (invariantProjection u) * targetSign (y u) = 0 := by
  simpa using
    (weighted_signedScore_sum_eq_zero
      (τ := tiInputMap)
      (u := invariantProjection)
      (y := y)
      (w := w)
      (score := score)
      tiInputMap_involutive
      invariantProjection_tiInputMap
      hy
      hw)

theorem doubledAdvantage_invariantProjection_with_b_le_nonzeroColumnMass
    [Fintype Z]
    (y : PostSwitchInput Z k → Bool) (w : PostSwitchInput Z k → ℕ)
    (h : (Z × BitVec k) × BitVec k → Bool)
    (hy : ∀ u, y (tiInputMap u) = !(y u))
    (hw : ∀ u, w (tiInputMap u) = w u) :
    doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h ≤
      sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w := by
  have hbound :
      doubledAdvantage (fun u => (invariantProjection u, u.b)) y w h ≤
        resolvedMass tiInputMap (fun u => u.b) w :=
    doubledAdvantage_pair_le_resolvedMass
      (τ := tiInputMap)
      (u := invariantProjection)
      (v := fun u => u.b)
      (y := y)
      (w := w)
      (h := h)
      tiInputMap_involutive
      invariantProjection_tiInputMap
      hy
      hw
  have hresolved :
      resolvedMass tiInputMap (fun u => u.b) w =
        sliceMass (fun u : PostSwitchInput Z k => nonzeroColumn u.a) w := by
    classical
    have hp :
        (fun u : PostSwitchInput Z k =>
          ¬ unresolvedBySideChannel tiInputMap (fun x => x.b) u) =
          (fun u : PostSwitchInput Z k => nonzeroColumn u.a) := by
      funext u
      exact propext (resolvedBySideChannel_tiInputMap_b_iff_nonzeroColumn u)
    unfold resolvedMass outsideMass
    simp [hp]
  rwa [hresolved] at hbound

end

end Mettapedia.Computability.PNP
