import Mettapedia.SetTheory.Surreal.PositiveFloor
import Mettapedia.SetTheory.Surreal.AddGroup

/-!
# The halving ladder

```
ladder k = mk (dyadicPre k) = 1 / 2^k
```

and the one theorem that matters:

```
ladder (k+1) + ladder (k+1) = ladder k
```

**This is the whole of the dyadic interpretation.** Once halving works, the
embedding of `m / 2^k` is `m • ladder k` — an integer multiple in the additive
group assembled in `AddGroup.lean` — and then additivity of the embedding is
`add_zsmul`, free, rather than a second induction. Well-definedness is free
too: `m • ladder k = 2m • ladder (k+1)` is immediate from the theorem above.

## Why it can be proved without enumerating options

`ladder (k+1) + ladder (k+1)` is the cut of its option families, and those are
built from the *canonical* options of `ladder (k+1)` — every younger number
above or below it. There are infinitely many and no term-by-term description.
What `PositiveFloor.lean` supplies instead are two bounds that are enough:

```
u ∈ leftOptions  (ladder (k+1))  →  u ≤ 0
v ∈ rightOptions (ladder (k+1))  →  ladder k ≤ v
```

so every left option of the sum is at most `ladder (k+1) + 0 = ladder (k+1)`,
which is below `ladder k`, and every right option is at least
`ladder k + ladder (k+1)`, which is above it. That places `ladder k` strictly
inside the sum's families.

For the other direction the left options of `ladder k` are `≤ 0` and the sum is
positive; the right options need `ladder (k+1) + ladder (k+1) < ladder (j)` for
the rung `j` below, and that is the induction hypothesis together with strict
monotonicity. At the bottom rung there are no right options at all, which is
why the base case needs nothing.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace Surreal

/-- The `k`-th rung: `1 / 2^k`, as the expansion `+` followed by `k` minuses. -/
noncomputable def ladder (k : ℕ) : Surreal := mk (dyadicPre k)

theorem ladder_def (k : ℕ) : ladder k = mk (dyadicPre k) := rfl

theorem ladder_pos (k : ℕ) : 0 < ladder k := dyadic_pos k

theorem ladder_anti (k : ℕ) : ladder (k + 1) < ladder k := dyadic_anti k

/-- The bottom rung is `1`. -/
theorem ladder_zero : ladder 0 = ofNat 1 :=
  mk_eq_mk.mpr dyadicPre_zero_equiv_one

/-! ## Bounds on the sum's options, from the floor -/

private theorem sum_pos (k : ℕ) : 0 < add (ladder (k + 1)) (ladder (k + 1)) := by
  have h : add 0 (ladder (k + 1)) < add (ladder (k + 1)) (ladder (k + 1)) :=
    add_lt_add_right (ladder_pos (k + 1)) _
  rw [zero_add'] at h
  exact lt_trans (ladder_pos (k + 1)) h

private theorem leftSum_lt (k : ℕ) {p : Surreal}
    (hp : p ∈ leftSum (ladder (k + 1)) (ladder (k + 1))) : p < ladder k := by
  have hstep : p ≤ ladder (k + 1) := by
    rcases mem_leftSum_cases hp with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · have h := add_le_add_right (leftOptions_dyadicPre_nonpos hu) (ladder (k + 1))
      rwa [zero_add'] at h
    · have h := add_le_add_left (leftOptions_dyadicPre_nonpos hu) (ladder (k + 1))
      rwa [add_zero'] at h
  exact lt_of_le_of_lt hstep (ladder_anti k)

private theorem lt_rightSum (k : ℕ) {p : Surreal}
    (hp : p ∈ rightSum (ladder (k + 1)) (ladder (k + 1))) : ladder k < p := by
  have hstep : add (ladder k) (ladder (k + 1)) ≤ p := by
    rcases mem_rightSum_cases hp with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · exact add_le_add_right (rightOptions_dyadicPre_ge hv) (ladder (k + 1))
    · rw [add_comm' (ladder (k + 1)) v]
      exact add_le_add_right (rightOptions_dyadicPre_ge hv) (ladder (k + 1))
  refine lt_of_lt_of_le ?_ hstep
  have h : add (ladder k) 0 < add (ladder k) (ladder (k + 1)) :=
    add_lt_add_left (ladder_pos (k + 1)) _
  rwa [add_zero'] at h

/-! ## Halving -/

/-- **Each rung is twice the next.**  This is the theorem the dyadic
interpretation is built on. -/
theorem ladder_add_self : ∀ k : ℕ,
    add (ladder (k + 1)) (ladder (k + 1)) = ladder k
  | 0 => by
      refine (isCut_add' _ _).eq_of_between (isCut_self _)
        ⟨fun p hp => leftSum_lt 0 hp, fun p hp => lt_rightSum 0 hp⟩
        ⟨fun w hw => ?_, fun v hv => ?_⟩
      · exact lt_of_le_of_lt (leftOptions_dyadicPre_nonpos hw) (sum_pos 0)
      · exact absurd hv (by rw [ladder_def, rightOptions_dyadicPre_zero_empty]; simp)
  | (j + 1) => by
      have ih : add (ladder (j + 1)) (ladder (j + 1)) = ladder j := ladder_add_self j
      refine (isCut_add' _ _).eq_of_between (isCut_self _)
        ⟨fun p hp => leftSum_lt (j + 1) hp, fun p hp => lt_rightSum (j + 1) hp⟩
        ⟨fun w hw => ?_, fun v hv => ?_⟩
      · exact lt_of_le_of_lt (leftOptions_dyadicPre_nonpos hw) (sum_pos (j + 1))
      · -- The sum is below the rung `ladder j`, which every right option clears.
        have hshrink : add (ladder (j + 2)) (ladder (j + 2)) < ladder j := by
          rw [← ih]
          exact lt_trans (add_lt_add_right (ladder_anti (j + 1)) _)
            (add_lt_add_left (ladder_anti (j + 1)) _)
        exact lt_of_lt_of_le hshrink (rightOptions_dyadicPre_ge hv)

theorem ladder_two_nsmul (k : ℕ) : (2 : ℕ) • ladder (k + 1) = ladder k := by
  rw [two_nsmul, ← add_eq]
  exact ladder_add_self k

/-! ## Controls -/

namespace HalvingLadderControls

/-- The first rung really is a half: `1/2 + 1/2 = 1`. -/
theorem half_add_half : add (ladder 1) (ladder 1) = ofNat 1 := by
  rw [ladder_add_self 0, ladder_zero]

/-- And the second: `1/4 + 1/4 = 1/2`. -/
theorem quarter_add_quarter : add (ladder 2) (ladder 2) = ladder 1 :=
  ladder_add_self 1

/-- **Negative control**: the rungs are distinct, so halving is not collapsing
everything to one number. -/
theorem ladder_ne : ladder 1 ≠ ladder 0 := ne_of_lt (ladder_anti 0)

/-- **Negative control**: a rung is *not* the sum of the next two rungs down —
`1/4 + 1/8 ≠ 1/2`. So the law is about equal halves, not about any two
smaller rungs. -/
theorem mixed_rungs_ne : add (ladder 2) (ladder 3) ≠ ladder 1 := by
  rw [← ladder_add_self 1]
  intro h
  exact absurd (add_left_cancel h) (ne_of_lt (ladder_anti 2))

/-- Every rung is strictly positive and strictly decreasing, so the ladder does
not stabilise. -/
theorem ladder_strictAnti (k : ℕ) : 0 < ladder (k + 1) ∧ ladder (k + 1) < ladder k :=
  ⟨ladder_pos (k + 1), ladder_anti k⟩

end HalvingLadderControls

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.ladder_add_self
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.ladder_zero
