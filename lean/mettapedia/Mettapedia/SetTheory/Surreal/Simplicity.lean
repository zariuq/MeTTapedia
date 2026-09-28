import Mettapedia.SetTheory.Surreal.SignExpansion

/-!
# The simplicity theorem, on sign expansions

Every operation on surreal numbers — addition, multiplication, everything
Conway defines — is a recursion of the form "the simplest number lying strictly
between these two families".  So the construction that has to come first is the
one that says *which* number that is, and that it is unique.

On sign expansions it is concrete.  If `x < y`, take the position `β` where
their expansions first differ.  Everything they agree on before `β` is their
**common prefix**, and the claim of this file is that the prefix is exactly the
simplicity content of the interval:

* `agree_below_of_between` — anything strictly between `x` and `y` reproduces
  their common prefix, sign for sign;
* `length_ge_of_between` — hence it is born no earlier than the prefix ends;
* `prefixOf_lt` / `lt_prefixOf` — when the deciding signs are `−` and `+`, the
  prefix itself lies strictly between;
* `prefixOf_simplest` and `eq_prefixOf_of_length_le` — so in that case it is
  *the* number of least birthday there, and it is unique.

The `−`/`+` case is the one Conway's recursions land in: a left option is below
and a right option is above, and the number being defined is what sits between.

The proof of the first is the whole idea.  Suppose some `z` between `x` and `y`
first disagreed with `x` at a position `δ` before `β`.  Below `δ` the three
expansions all agree.  At `δ` the value `z` takes is either above `x`'s — and
then, since `y` still agrees with `x` there, `z` is above `y` as well — or
below `x`'s, and then `z` is below `x`.  Either way `z` is not between them.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.SignExpansion

namespace PreSurreal

/-! ## A first difference sits below both levels -/

/-- **The first difference is never past either level.**  If it were, both
expansions would already have run out there, and they would agree. -/
theorem le_length_of_first_diff {x y : PreSurreal} {β : Ordinal}
    (hagree : ∀ γ : Ordinal, γ < β → x.signAt γ = y.signAt γ)
    (hne : x.signAt β ≠ y.signAt β) : β ≤ x.length ∧ β ≤ y.length := by
  constructor
  · by_contra h
    have hlt : x.length < β := not_le.mp h
    have hzero : x.signAt x.length = Sign.zero := signAt_of_ge (le_refl _)
    have hy : y.signAt x.length = Sign.zero := (hagree _ hlt).symm.trans hzero
    have hylen : y.length ≤ x.length := signAt_eq_zero_iff.mp hy
    exact hne ((signAt_of_ge (le_of_lt hlt)).trans
      (signAt_of_ge (le_of_lt (lt_of_le_of_lt hylen hlt))).symm)
  · by_contra h
    have hlt : y.length < β := not_le.mp h
    have hzero : y.signAt y.length = Sign.zero := signAt_of_ge (le_refl _)
    have hx : x.signAt y.length = Sign.zero := (hagree _ hlt).trans hzero
    have hxlen : x.length ≤ y.length := signAt_eq_zero_iff.mp hx
    exact hne ((signAt_of_ge (le_of_lt (lt_of_le_of_lt hxlen hlt))).trans
      (signAt_of_ge (le_of_lt hlt)).symm)

/-! ## Anything between reproduces the common prefix -/

/-- **The common prefix is forced.**  If `x < z < y` and `x` and `y` agree
below `β`, then `z` agrees with them below `β` too. -/
theorem agree_below_of_between {x y z : PreSurreal} (hxz : Lt x z) (hzy : Lt z y)
    {β : Ordinal} (hagree : ∀ γ : Ordinal, γ < β → x.signAt γ = y.signAt γ) :
    ∀ γ : Ordinal, γ < β → z.signAt γ = x.signAt γ := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨γ₀, hγ₀β, hγ₀ne⟩ := hcon
  -- Take the *first* position below `β` at which `z` parts from `x`.
  obtain ⟨δ, ⟨hδβ, hδne⟩, hmin⟩ :=
    Ordinal.lt_wf.has_min {d : Ordinal | d < β ∧ z.signAt d ≠ x.signAt d} ⟨γ₀, hγ₀β, hγ₀ne⟩
  have hbelow : ∀ ε : Ordinal, ε < δ → z.signAt ε = x.signAt ε := by
    intro ε hε
    by_contra hεne
    exact hmin ε ⟨hε.trans hδβ, hεne⟩ hε
  rcases lt_trichotomy (z.signAt δ) (x.signAt δ) with hlt | heq | hgt
  · -- `z` dips below `x` at `δ`, so `z < x`, contradicting `x < z`.
    exact not_lt_self x (lt_trans hxz ⟨δ, fun ε hε => hbelow ε hε, hlt⟩)
  · exact hδne heq
  · -- `z` rises above `x` at `δ`, where `y` still agrees with `x`, so `y < z`.
    have hzy' : Lt y z := by
      refine ⟨δ, fun ε hε => ?_, ?_⟩
      · exact ((hagree ε (hε.trans hδβ)).symm.trans (hbelow ε hε).symm)
      · rwa [← hagree δ hδβ]
    exact not_lt_self y (lt_trans hzy' hzy)

/-- **Birthday lower bound.**  Anything strictly between `x` and `y` is born no
earlier than their common prefix ends. -/
theorem length_ge_of_between {x y z : PreSurreal} (hxz : Lt x z) (hzy : Lt z y)
    {β : Ordinal} (hagree : ∀ γ : Ordinal, γ < β → x.signAt γ = y.signAt γ)
    (hne : x.signAt β ≠ y.signAt β) : β ≤ z.length := by
  have hβx : β ≤ x.length := (le_length_of_first_diff hagree hne).1
  have hz := agree_below_of_between hxz hzy hagree
  by_contra hcon
  have hlt : z.length < β := not_le.mp hcon
  have h1 : z.signAt z.length = x.signAt z.length := hz _ hlt
  have h2 : x.signAt z.length ≠ Sign.zero :=
    signAt_ne_zero_of_lt (lt_of_lt_of_le hlt hβx)
  exact h2 (h1 ▸ signAt_of_ge (le_refl _))

/-! ## The prefix itself, and when it is the answer -/

/-- The initial segment of `x` of length `β`. -/
def prefixOf (x : PreSurreal) (β : Ordinal) : PreSurreal := ⟨β, x.sign⟩

@[simp] theorem prefixOf_length (x : PreSurreal) (β : Ordinal) :
    (prefixOf x β).length = β := rfl

theorem prefixOf_signAt_lt {x : PreSurreal} {β γ : Ordinal} (hγ : γ < β)
    (hβ : β ≤ x.length) : (prefixOf x β).signAt γ = x.signAt γ := by
  rw [signAt_of_lt (by rwa [prefixOf_length]),
    signAt_of_lt (lt_of_lt_of_le hγ hβ)]
  rfl

theorem prefixOf_signAt_ge {x : PreSurreal} {β γ : Ordinal} (hγ : β ≤ γ) :
    (prefixOf x β).signAt γ = Sign.zero :=
  signAt_of_ge (by rwa [prefixOf_length])

/-- If `x` carries `−` at the deciding position, the prefix is above `x`:
they agree up to `β`, where `x` has `−` and the prefix has run out. -/
theorem prefixOf_lt {x : PreSurreal} {β : Ordinal} (hβ : β ≤ x.length)
    (hx : x.signAt β = Sign.neg) : Lt x (prefixOf x β) := by
  refine ⟨β, fun γ hγ => (prefixOf_signAt_lt hγ hβ).symm, ?_⟩
  rw [hx, prefixOf_signAt_ge (le_refl _)]
  exact Sign.neg_lt_zero

/-- And if `y` carries `+` there, the prefix is below `y`. -/
theorem lt_prefixOf {x y : PreSurreal} {β : Ordinal} (hβ : β ≤ x.length)
    (hagree : ∀ γ : Ordinal, γ < β → x.signAt γ = y.signAt γ)
    (hy : y.signAt β = Sign.pos) : Lt (prefixOf x β) y := by
  refine ⟨β, fun γ hγ => (prefixOf_signAt_lt hγ hβ).trans (hagree γ hγ), ?_⟩
  rw [hy, prefixOf_signAt_ge (le_refl _)]
  exact Sign.zero_lt_pos

/-! ## The simplicity theorem for the deciding case `−` / `+` -/

/-- **The prefix lies strictly between, and nothing simpler does.**  This is
the case Conway's recursions land in: the left family ends in `−` and the right
family ends in `+`. -/
theorem prefixOf_between {x y : PreSurreal} {β : Ordinal}
    (hagree : ∀ γ : Ordinal, γ < β → x.signAt γ = y.signAt γ)
    (hx : x.signAt β = Sign.neg) (hy : y.signAt β = Sign.pos) :
    Lt x (prefixOf x β) ∧ Lt (prefixOf x β) y := by
  have hne : x.signAt β ≠ y.signAt β := by rw [hx, hy]; exact (by decide)
  have hβ : β ≤ x.length := (le_length_of_first_diff hagree hne).1
  exact ⟨prefixOf_lt hβ hx, lt_prefixOf hβ hagree hy⟩

theorem prefixOf_simplest {x y z : PreSurreal} {β : Ordinal}
    (hagree : ∀ γ : Ordinal, γ < β → x.signAt γ = y.signAt γ)
    (hx : x.signAt β = Sign.neg) (hy : y.signAt β = Sign.pos)
    (hxz : Lt x z) (hzy : Lt z y) : (prefixOf x β).length ≤ z.length := by
  have hne : x.signAt β ≠ y.signAt β := by rw [hx, hy]; exact (by decide)
  rw [prefixOf_length]
  exact length_ge_of_between hxz hzy hagree hne

/-- **And it is the only one born that early.**  A `z` strictly between whose
level is no later than the prefix's *is* the prefix. -/
theorem eq_prefixOf_of_length_le {x y z : PreSurreal} {β : Ordinal}
    (hagree : ∀ γ : Ordinal, γ < β → x.signAt γ = y.signAt γ)
    (hx : x.signAt β = Sign.neg) (hy : y.signAt β = Sign.pos)
    (hxz : Lt x z) (hzy : Lt z y) (hlen : z.length ≤ β) :
    Equiv z (prefixOf x β) := by
  have hne : x.signAt β ≠ y.signAt β := by rw [hx, hy]; exact (by decide)
  have hβ : β ≤ x.length := (le_length_of_first_diff hagree hne).1
  have hzβ : z.length = β := le_antisymm hlen (length_ge_of_between hxz hzy hagree hne)
  funext γ
  rcases lt_or_ge γ β with hγ | hγ
  · rw [agree_below_of_between hxz hzy hagree γ hγ, prefixOf_signAt_lt hγ hβ]
  · rw [signAt_of_ge (by rw [hzβ]; exact hγ), prefixOf_signAt_ge hγ]

/-! ## Why the theorem is stated for `−` / `+`, and not in general

The deciding signs can also be `−`/`zero` or `zero`/`+`, and those are the
cases where one of the two numbers *is* the common prefix.  There the prefix is
not an answer, and — less obviously — neither is the natural repair of
extending it by a couple of signs.  Both failures are recorded here, because
they are the reason the statement above carries its hypotheses rather than
being stated for every pair. -/

namespace SimplicityControls

/-- **The prefix is not strictly between when the deciding sign is the middle
one.**  If `x` has run out at `β` then `x` *is* the prefix, so it cannot be
strictly below it. -/
theorem prefixOf_not_between_of_zero {x y : PreSurreal} {β : Ordinal}
    (hagree : ∀ γ : Ordinal, γ < β → x.signAt γ = y.signAt γ)
    (hne : x.signAt β ≠ y.signAt β) (hx : x.signAt β = Sign.zero) :
    ¬ Lt x (prefixOf x β) := by
  have hβ : β ≤ x.length := (le_length_of_first_diff hagree hne).1
  have hlen : x.length = β := le_antisymm (signAt_eq_zero_iff.mp hx) hβ
  have hequiv : Equiv x (prefixOf x β) := by
    funext γ
    rcases lt_or_ge γ β with hγ | hγ
    · exact (prefixOf_signAt_lt hγ hβ).symm
    · rw [signAt_of_ge (by rw [hlen]; exact hγ), prefixOf_signAt_ge hγ]
  intro hlt
  exact not_lt_self (prefixOf x β) (lt_of_equiv_of_lt (equiv_symm hequiv) hlt)

/-- `0`, as the empty expansion. -/
def lowB : PreSurreal := ⟨0, fun _ => false⟩

/-- `+ − −`. -/
noncomputable def highB : PreSurreal := ⟨((3 : ℕ) : Ordinal), fun γ => decide (γ = 0)⟩

/-- `+ −`: the common prefix of `lowB` and `highB` extended by two signs, which
is the shape that answers the `−`/`+` case. -/
noncomputable def candB : PreSurreal := ⟨((2 : ℕ) : Ordinal), fun γ => decide (γ = 0)⟩

theorem lowB_lt_highB : Lt lowB highB := by
  refine ⟨0, fun γ hγ => absurd hγ (by simp), ?_⟩
  rw [signAt_of_ge (by simp [lowB]), signAt_of_lt (show (0 : Ordinal) < highB.length by
    rw [show highB.length = ((3 : ℕ) : Ordinal) from rfl]; exact_mod_cast Nat.zero_lt_succ 2)]
  simp only [highB, decide_true]
  exact Sign.zero_lt_pos

/-- **The two-sign repair overshoots.**  `candB` is not between `lowB` and
`highB`: it is strictly *above* `highB`, because `highB` keeps going with `−`
past the point where `candB` stops. -/
theorem highB_lt_candB : Lt highB candB := by
  refine ⟨((2 : ℕ) : Ordinal), fun γ hγ => ?_, ?_⟩
  · have h3 : γ < ((3 : ℕ) : Ordinal) := hγ.trans (by exact_mod_cast Nat.lt_succ_self 2)
    rw [signAt_of_lt (show γ < highB.length from h3),
      signAt_of_lt (show γ < candB.length from hγ)]
    rfl
  · have hsign : highB.sign ((2 : ℕ) : Ordinal) = false := by simp [highB]
    rw [signAt_of_lt (show ((2 : ℕ) : Ordinal) < highB.length by
        rw [show highB.length = ((3 : ℕ) : Ordinal) from rfl]
        exact_mod_cast Nat.lt_succ_self 2),
      signAt_of_ge (show candB.length ≤ ((2 : ℕ) : Ordinal) from le_refl _), hsign]
    exact Sign.neg_lt_zero

/-- So the candidate genuinely fails to lie in the interval. -/
theorem candB_not_between : ¬ Lt candB highB := fun h =>
  not_lt_self highB (lt_trans highB_lt_candB h)

end SimplicityControls

/-! ## The same statements about surreal numbers -/

end PreSurreal

namespace Surreal

open PreSurreal

/-- **The simplest number in an interval, as a surreal.**  Between `x` and `y`
sits `prefixOf x β`, and every surreal strictly between is born no earlier. -/
theorem mk_prefixOf_between {x y : PreSurreal} {β : Ordinal}
    (hagree : ∀ γ : Ordinal, γ < β → x.signAt γ = y.signAt γ)
    (hx : x.signAt β = Sign.neg) (hy : y.signAt β = Sign.pos) :
    mk x < mk (prefixOf x β) ∧ mk (prefixOf x β) < mk y :=
  prefixOf_between hagree hx hy

/-- **Uniqueness, as a surreal equation.** -/
theorem mk_eq_prefixOf {x y z : PreSurreal} {β : Ordinal}
    (hagree : ∀ γ : Ordinal, γ < β → x.signAt γ = y.signAt γ)
    (hx : x.signAt β = Sign.neg) (hy : y.signAt β = Sign.pos)
    (hxz : mk x < mk z) (hzy : mk z < mk y) (hlen : z.length ≤ β) :
    mk z = mk (prefixOf x β) :=
  Quotient.sound (eq_prefixOf_of_length_le hagree hx hy hxz hzy hlen)

end Surreal

end Mettapedia.SetTheory.SignExpansion

#print axioms Mettapedia.SetTheory.SignExpansion.PreSurreal.agree_below_of_between
#print axioms Mettapedia.SetTheory.SignExpansion.PreSurreal.length_ge_of_between
#print axioms Mettapedia.SetTheory.SignExpansion.PreSurreal.prefixOf_between
#print axioms Mettapedia.SetTheory.SignExpansion.PreSurreal.eq_prefixOf_of_length_le
#print axioms Mettapedia.SetTheory.SignExpansion.Surreal.mk_eq_prefixOf
