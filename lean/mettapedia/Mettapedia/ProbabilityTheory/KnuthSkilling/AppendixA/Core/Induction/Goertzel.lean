import Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.Core.Induction.ThetaPrime

set_option linter.unnecessarySimpa false

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA

open Classical KnuthSkillingAlgebra

variable {α : Type*} [KnuthSkillingAlgebra α]

/-!
## Goertzel’s v2 Lemma‑7 framing, in our vocabulary

Goertzel (Foundations-of-inference-new-proofs_v2, Lemma 7) reframes the global `B = ∅` difficulty
as an *order-invariance inside an admissible gap* statement:

If a B-empty extension step admits multiple admissible choices for the new “slope”/parameter `δ`,
then the relative order between any two newly-formed expressions should be independent of which
admissible `δ` is used; otherwise some “critical value” would force an equality, contradicting
the `B = ∅` assumption.

### What this file does
This file packages that idea as:
- `RealizesThetaRaw` / `RealizesThetaRaw_pair`: a strictly monotone evaluator on (part of) the
  extended μ-grid that agrees with the “raw extension formula” `ThetaRaw`.
- `bEmptyStrictGapSpec_of_realizesThetaRaw_chooseδ`: Goertzel’s “flip/boundary-collision” argument
  formalized as `RealizesThetaRaw chooseδ → BEmptyStrictGapSpec`.
- `realizesThetaRaw_chooseδ_iff_chooseδBaseAdmissible`: under a *global* `B = ∅` regime,
  `RealizesThetaRaw chooseδ` is equivalent to the single explicit extension blocker
  `ChooseδBaseAdmissible` from `ThetaPrime.lean`.

### What remains open (the actual Appendix A.3.4 gap)
Proving `ChooseδBaseAdmissible` from the current K&S `Core/` axioms is still the main remaining
mathematical step for Appendix A.3.4 (“fixdelta → fixm” / base-invariance). This file isolates
smaller sufficient packages (e.g. `AppendixA34Extra`) to make that dependency explicit.

### Important: a known invalid inference in the v2 sketch
Goertzel’s Lemma 7 proof sketch uses the inference
“`X ⊕ d^n = Y` (old `X,Y`) ⇒ some old-grid value equals `d^n`” (a B-witness for `n`).
This is not valid in a general associative ordered monoid: it would require extra structure
(e.g. cancellation or unique decomposition). See the concrete counterexample
`Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA/Counterexamples/GoertzelLemma7.lean`.
-/

/-!
### Suggested Reading Order (for review)
1. `ChooseδBaseAdmissible` and `extend_grid_rep_with_atom` in
   `Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA/Core/Induction/ThetaPrime.lean`
2. `realizesThetaRaw_chooseδ_iff_chooseδBaseAdmissible` (this file): the cleaned-up “circularity”
3. `AppendixA34Extra` (this file): a small sufficient package for proving base admissibility
4. Counterexamples in `Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA/Counterexamples/`
-/

section
variable {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
variable (IH : GridBridge F) (H : GridComm F)
variable (d : α) (hd : ident < d)

noncomputable def ThetaRaw (δ : ℝ) (r_old : Multi k) (t : ℕ) : ℝ :=
  R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * δ

/-- The extended μ-value of a join-multiplicity witness, packaged as an element of the extended k-grid. -/
noncomputable def joinPoint (r_old : Multi k) (t : ℕ) :
    {x // x ∈ kGrid (extendAtomFamily F d hd)} :=
  ⟨mu (extendAtomFamily F d hd) (joinMulti r_old t),
    mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old t)⟩

/-- The (finite) “two-point slice” of the extended k-grid used by the Ben/Goertzel Lemma‑7 flip argument. -/
def joinPairSet (r_old_x r_old_y : Multi k) (t_x t_y : ℕ) :
    Set {x // x ∈ kGrid (extendAtomFamily F d hd)} :=
  {p | p = joinPoint (F := F) (d := d) (hd := hd) r_old_x t_x ∨
        p = joinPoint (F := F) (d := d) (hd := hd) r_old_y t_y}

/-- A *realization* of the Ben/Goertzel `ThetaRaw` formula on the extended μ-grid.

This packages the missing link in Goertzel/Ben Lemma 7: to turn a *numeric* equality
`ThetaRaw δ … = ThetaRaw δ …` into an *algebraic* equality on the extended grid, one needs an
actual evaluator on `kGrid (extendAtomFamily F d hd)` that is strictly monotone (hence injective)
and agrees with `ThetaRaw` on the `joinMulti` witnesses. -/
def RealizesThetaRaw (δ : ℝ) : Prop :=
  ∃ Θ' : {x // x ∈ kGrid (extendAtomFamily F d hd)} → ℝ,
    StrictMono Θ' ∧
      (∀ (r_old : Multi k) (t : ℕ),
          Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_old t),
                mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old t)⟩ =
            ThetaRaw (R := R) (F := F) δ r_old t)

/-- A *local* realization of `ThetaRaw` on just two join-multiplicity points.

This is the minimal hypothesis needed to turn a single numeric equality
`ThetaRaw δ r_old_x t_x = ThetaRaw δ r_old_y t_y` into an equality of the corresponding μ-values.
It is strictly weaker than `RealizesThetaRaw` (which provides a strictly monotone evaluator on the
entire extended k-grid). -/
def RealizesThetaRaw_pair (δ : ℝ) (r_old_x r_old_y : Multi k) (t_x t_y : ℕ) : Prop :=
  ∃ Θ' : {p // p ∈ joinPairSet (F := F) (d := d) (hd := hd) r_old_x r_old_y t_x t_y} → ℝ,
    StrictMono Θ' ∧
      Θ' ⟨joinPoint (F := F) (d := d) (hd := hd) r_old_x t_x, Or.inl rfl⟩ =
          ThetaRaw (R := R) (F := F) δ r_old_x t_x ∧
      Θ' ⟨joinPoint (F := F) (d := d) (hd := hd) r_old_y t_y, Or.inr rfl⟩ =
          ThetaRaw (R := R) (F := F) δ r_old_y t_y

lemma realizesThetaRaw_pair_of_realizesThetaRaw
    {δ : ℝ} (hδ : RealizesThetaRaw (R := R) (F := F) (d := d) (hd := hd) δ)
    (r_old_x r_old_y : Multi k) (t_x t_y : ℕ) :
    RealizesThetaRaw_pair (R := R) (F := F) (d := d) (hd := hd) δ r_old_x r_old_y t_x t_y := by
  classical
  rcases hδ with ⟨Θ', hΘ'_mono, hΘ'_on_join⟩
  refine ⟨fun p => Θ' p.1, ?_, ?_, ?_⟩
  · intro a b hab
    exact hΘ'_mono hab
  · -- left point
    simp [joinPoint, hΘ'_on_join]
  · -- right point
    simp [joinPoint, hΘ'_on_join]

lemma ThetaRaw_eq_implies_mu_joinMulti_eq
    {δ : ℝ} (hδ : RealizesThetaRaw (R := R) (F := F) (d := d) (hd := hd) δ)
    (r_old_x r_old_y : Multi k) (t_x t_y : ℕ)
    (hEq :
      ThetaRaw (R := R) (F := F) δ r_old_x t_x =
        ThetaRaw (R := R) (F := F) δ r_old_y t_y) :
    mu (extendAtomFamily F d hd) (joinMulti r_old_x t_x) =
      mu (extendAtomFamily F d hd) (joinMulti r_old_y t_y) := by
  classical
  rcases hδ with ⟨Θ', hΘ'_mono, hΘ'_on_join⟩
  have hEq' :
      Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_old_x t_x),
            mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old_x t_x)⟩ =
        Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_old_y t_y),
              mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old_y t_y)⟩ := by
    simpa [hΘ'_on_join] using hEq
  have hxy :
      (⟨mu (extendAtomFamily F d hd) (joinMulti r_old_x t_x),
            mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old_x t_x)⟩ :
          {x // x ∈ kGrid (extendAtomFamily F d hd)}) =
        ⟨mu (extendAtomFamily F d hd) (joinMulti r_old_y t_y),
          mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old_y t_y)⟩ :=
    hΘ'_mono.injective hEq'
  simpa using congrArg Subtype.val hxy

lemma ThetaRaw_eq_implies_mu_joinMulti_eq_of_pair
    {δ : ℝ} {r_old_x r_old_y : Multi k} {t_x t_y : ℕ}
    (hδ :
      RealizesThetaRaw_pair (R := R) (F := F) (d := d) (hd := hd) δ r_old_x r_old_y t_x t_y)
    (hEq :
      ThetaRaw (R := R) (F := F) δ r_old_x t_x =
        ThetaRaw (R := R) (F := F) δ r_old_y t_y) :
    mu (extendAtomFamily F d hd) (joinMulti r_old_x t_x) =
      mu (extendAtomFamily F d hd) (joinMulti r_old_y t_y) := by
  classical
  rcases hδ with ⟨Θ', hΘ'_mono, hx, hy⟩
  -- Evaluate the local Θ' at the two designated points.
  let px :
      {p // p ∈ joinPairSet (F := F) (d := d) (hd := hd) r_old_x r_old_y t_x t_y} :=
    ⟨joinPoint (F := F) (d := d) (hd := hd) r_old_x t_x, Or.inl rfl⟩
  let py :
      {p // p ∈ joinPairSet (F := F) (d := d) (hd := hd) r_old_x r_old_y t_x t_y} :=
    ⟨joinPoint (F := F) (d := d) (hd := hd) r_old_y t_y, Or.inr rfl⟩
  have hEq' : Θ' px = Θ' py := by
    -- Rewrite both sides to the common `ThetaRaw` value.
    calc
      Θ' px = ThetaRaw (R := R) (F := F) δ r_old_x t_x := by simpa [px] using hx
      _ = ThetaRaw (R := R) (F := F) δ r_old_y t_y := hEq
      _ = Θ' py := by simpa [py] using hy.symm
  have hxy : px = py := hΘ'_mono.injective hEq'
  -- Project back to underlying α-values.
  have : (joinPoint (F := F) (d := d) (hd := hd) r_old_x t_x : {x // x ∈ kGrid (extendAtomFamily F d hd)}) =
      joinPoint (F := F) (d := d) (hd := hd) r_old_y t_y := by
    simpa [px, py] using congrArg Subtype.val hxy
  simpa [joinPoint] using congrArg Subtype.val this

/-!
`AdmissibleDelta` is a deliberately *local* notion: it says δ lies strictly between A- and C-side
statistics at *every* witness level u.

This matches the informal “δ is in the open gap” reading needed for Goertzel’s “invariance inside
the gap” proof outline.

Note: the current `chooseδ` definition in the B-empty branch uses `sSup` of A-statistics, which
does not automatically provide strict inequalities on the C-side. As a result, proving
`AdmissibleDelta (chooseδ …)` from the current Core library is a nontrivial task (and may require
strengthening hypotheses).
-/
def AdmissibleDelta (δ : ℝ) : Prop :=
  (∀ (r : Multi k) (u : ℕ) (hu : 0 < u),
      r ∈ extensionSetA F d u → separationStatistic R r u hu < δ) ∧
  (∀ (r : Multi k) (u : ℕ) (hu : 0 < u),
      r ∈ extensionSetC F d u → δ < separationStatistic R r u hu)

/-!
## Ben/Goertzel v2 Lemma 6 interface (base-indexed)

In Ben Goertzel’s v2 notes (and K&S Appendix A.3.4), the “B = ∅” regime is treated *relative to a
fixed base* `X0 := μ(F,r0)` and a fixed level `u`. The relevant constraints compare *old-grid*
values to the “target family” boundary `X0 ⊕ d^u`, and therefore the natural “slope candidates” are
the base-indexed statistics

`(Θ(μ(F,r)) - Θ(μ(F,r0))) / u`.

Lemma 6 asserts that in the base-indexed `B = ∅` case, these constraints carve out a **nonempty
open interval** of admissible slopes.

Rather than baking this into the core construction via `sSup`/`sInf`, we record the existence of
such an interval as an explicit interface. This keeps the dependency clear and avoids forcing a
singleton “global admissibility” notion (which is incompatible with the “interval freedom” reading).
-/

/-- Base-indexed admissibility at a fixed base `r0` and level `u`.

Note: `R` and `d` are explicit parameters in this file’s surrounding `section`, so we keep them
explicit here as well to make elaboration predictable. -/
def AdmissibleDelta_base (R₀ : MultiGridRep F) (d₀ : α)
    (δ : ℝ) (r0 : Multi k) (u : ℕ) (hu : 0 < u) : Prop :=
  (∀ r : Multi k, r ∈ extensionSetA_base F d₀ r0 u →
      separationStatistic_base R₀ r0 r u hu < δ) ∧
  (∀ r : Multi k, r ∈ extensionSetC_base F d₀ r0 u →
      δ < separationStatistic_base R₀ r0 r u hu)

/-- Base-indexed admissibility for *all* levels `u > 0` at a fixed base `r0`.

This matches the quantification in Ben Goertzel’s v2 Lemma 7: once a base `X0 := μ(F,r0)` is
fixed, comparisons against the entire “target family” `X0 ⊕ d^u` for all `u` constrain a single
choice of slope/parameter.

In the current Lean development, this “for all u” admissibility is strong enough to imply the
global (base `ident`) admissibility predicate `AdmissibleDelta`, hence the chosen δ must be the
canonical `chooseδ`. -/
def AdmissibleDelta_base_all (R₀ : MultiGridRep F) (d₀ : α) (δ : ℝ) (r0 : Multi k) : Prop :=
  ∀ u : ℕ, ∀ hu : 0 < u, AdmissibleDelta_base (k := k) (F := F) R₀ d₀ δ r0 u hu

/-- A nonempty open interval of base-indexed admissible deltas.

This is **data** (it carries explicit endpoints `L,U : ℝ`), so it lives in `Type`, not `Prop`. -/
structure AdmissibleInterval_base (R₀ : MultiGridRep F) (d₀ : α)
    (r0 : Multi k) (u : ℕ) (hu : 0 < u) where
  L : ℝ
  U : ℝ
  hLU : L < U
  admissible :
    ∀ δ : ℝ, L < δ → δ < U → AdmissibleDelta_base R₀ d₀ δ r0 u hu

lemma admissibleInterval_base_nonempty
    {r0 : Multi k} {u : ℕ} {hu : 0 < u}
    (hI : AdmissibleInterval_base R d r0 u hu) :
    ∃ δ : ℝ, hI.L < δ ∧ δ < hI.U := by
  classical
  refine ⟨(hI.L + hI.U) / 2, ?_, ?_⟩ <;> linarith [hI.hLU]

/-!
### Existence of a base-indexed admissible interval (Goertzel v2 Lemma 6, fixed `u`)

For a fixed base `r0` and level `u>0`, the “old-grid comparisons against the target family”
`μ(F,r0) ⊕ d^u` only constrain finitely many old-grid points below a fixed bound, so we can pick:
- a **maximal** old-grid point strictly below the boundary (A-side), and
- a **minimal** old-grid point strictly above the boundary (C-side),

and take the corresponding strict inequality window of base-indexed statistics.

This yields an *open interval* of δ choices that separate all base-indexed A and C statistics at
this fixed `u`.
-/

theorem admissibleInterval_base_exists
    (hk : k ≥ 1) (hd' : ident < d) (r0 : Multi k) (u : ℕ) (hu : 0 < u) :
    Nonempty (AdmissibleInterval_base (k := k) (F := F) (R₀ := R) (d₀ := d) r0 u hu) := by
  classical
  -- Boundary value in `α` we compare old-grid points against.
  let boundary : α := op (mu F r0) (iterate_op d u)

  -- A-base set is finite under the fixed threshold `boundary`.
  have hA_fin : (extensionSetA_base F d r0 u).Finite := by
    -- `extensionSetA_base` is defined by the strict bound `mu F r < boundary`.
    simpa [extensionSetA_base, boundary] using (finite_set_mu_lt (F := F) boundary)

  -- C-base has a concrete witness `rC0` above the boundary, hence is nonempty.
  have hk_pos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  let i₀ : Fin k := ⟨0, hk_pos⟩
  let a₀ : α := F.atoms i₀
  have ha₀ : ident < a₀ := F.pos i₀
  obtain ⟨N, hN⟩ := bounded_by_iterate a₀ ha₀ boundary
  let rC0 : Multi k := unitMulti i₀ N
  have hrC0C : rC0 ∈ extensionSetC_base F d r0 u := by
    -- `boundary < μ(F, rC0) = a₀^N`.
    have : boundary < mu F rC0 := by
      simpa [rC0, a₀, mu_unitMulti] using hN
    simpa [extensionSetC_base, boundary, Set.mem_setOf_eq] using this

  -- Restrict the C-side to a finite “below μ(F,rC0)” set to extract a global minimal C-witness.
  let C_bdd : Set (Multi k) := {r : Multi k | mu F r ≤ mu F rC0}
  have hC_bdd_fin : C_bdd.Finite := by
    simpa [C_bdd] using (finite_set_mu_le (F := F) (mu F rC0))
  let Cset : Set (Multi k) := extensionSetC_base F d r0 u
  let C' : Set (Multi k) := Cset ∩ C_bdd
  have hC'_fin : C'.Finite := hC_bdd_fin.inter_of_right Cset
  have hC'_nonempty : C'.Nonempty := by
    refine ⟨rC0, ?_, le_rfl⟩
    exact hrC0C

  obtain ⟨rC, hrC_min⟩ :=
    Set.Finite.exists_minimalFor (f := fun r : Multi k => mu F r) C' hC'_fin hC'_nonempty
  have hrC_mem : rC ∈ C' := hrC_min.1
  have hrC_Cset : rC ∈ Cset := hrC_mem.1
  have hrC_le_rC0 : mu F rC ≤ mu F rC0 := hrC_mem.2

  -- Extract a maximal A-witness by finiteness (nonempty since `r0 ∈ A_base`).
  have hr0A : r0 ∈ extensionSetA_base F d r0 u := by
    have hdu : ident < iterate_op d u := iterate_op_pos d hd' u hu
    have : mu F r0 < op (mu F r0) (iterate_op d u) := by
      simpa [op_ident_right] using (op_strictMono_right (mu F r0) hdu)
    simpa [extensionSetA_base, boundary, Set.mem_setOf_eq] using this
  have hA_nonempty : (extensionSetA_base F d r0 u).Nonempty := ⟨r0, hr0A⟩
  obtain ⟨rA, hrA_max⟩ :=
    Set.Finite.exists_maximalFor (f := fun r : Multi k => mu F r) (extensionSetA_base F d r0 u)
      hA_fin hA_nonempty
  have hrA_mem : rA ∈ extensionSetA_base F d r0 u := hrA_max.1

  -- Define the interval endpoints from the extremal base-indexed statistics.
  let L : ℝ := separationStatistic_base R r0 rA u hu
  let U : ℝ := separationStatistic_base R r0 rC u hu

  -- Show `L < U` using `μ(F,rA) < boundary < μ(F,rC)`.
  have hμ_rA_lt : mu F rA < boundary := by
    simpa [extensionSetA_base, boundary, Set.mem_setOf_eq] using hrA_mem
  have hμ_rC_gt : boundary < mu F rC := by
    simpa [extensionSetC_base, boundary, Set.mem_setOf_eq] using hrC_Cset
  have hμ_rA_lt_rC : mu F rA < mu F rC := lt_trans hμ_rA_lt hμ_rC_gt
  have hθ_rA_lt_rC :
      R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ <
        R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ := R.strictMono hμ_rA_lt_rC
  have hu_pos_real : (0 : ℝ) < (u : ℝ) := Nat.cast_pos.mpr hu
  have hLU : L < U := by
    -- Divide by `u>0` after subtracting the common base term.
    have :
        (R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ -
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩) / (u : ℝ) <
          (R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ -
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩) / (u : ℝ) := by
      have hsub :
          R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ -
              R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ <
            R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ -
              R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := by
        -- Subtracting the same value preserves strict inequality.
        simpa [sub_eq_add_neg] using
          add_lt_add_right hθ_rA_lt_rC (-R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩)
      have hu_inv_pos : 0 < (u : ℝ)⁻¹ := inv_pos.mpr hu_pos_real
      have := mul_lt_mul_of_pos_right hsub hu_inv_pos
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    simpa [L, U, separationStatistic_base] using this

  -- Show `L` is an upper bound for all A-statistics.
  have hA_stat_le_L :
      ∀ r : Multi k, r ∈ extensionSetA_base F d r0 u →
        separationStatistic_base R r0 r u hu ≤ L := by
    intro r hrA
    have hμ_le : mu F r ≤ mu F rA := by
      -- `rA` is maximal for `mu` on the finite A-set.
      rcases le_total (mu F rA) (mu F r) with hle | hge
      · -- If `mu rA ≤ mu r`, maximality gives `mu r ≤ mu rA`.
        exact hrA_max.2 hrA hle
      · exact hge
    have hθ_mono : Monotone R.Θ_grid := R.strictMono.monotone
    have hθ_le :
        R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ ≤
          R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ := hθ_mono hμ_le
    have :
        (R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ -
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩) / (u : ℝ) ≤
          (R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ -
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩) / (u : ℝ) := by
      have hsub :
          R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ ≤
            R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := by
        -- Subtracting preserves `≤`.
        exact sub_le_sub_right hθ_le _
      have hu_inv_nonneg : 0 ≤ (u : ℝ)⁻¹ := le_of_lt (inv_pos.mpr hu_pos_real)
      have := mul_le_mul_of_nonneg_right hsub hu_inv_nonneg
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    simpa [L, separationStatistic_base] using this

  -- Show `U` is a lower bound for all C-statistics.
  have hU_le_C_stat :
      ∀ r : Multi k, r ∈ Cset →
        U ≤ separationStatistic_base R r0 r u hu := by
    intro r hrC
    have hμ_le : mu F rC ≤ mu F r := by
      -- Either `mu r ≤ mu rC0` and minimality applies, or `mu rC0 < mu r` and transitivity applies.
      by_cases hle : mu F r ≤ mu F rC0
      · have hrC' : r ∈ C' := ⟨hrC, hle⟩
        -- `rC` is minimal for `mu` on `C'`.
        have : mu F rC ≤ mu F r := by
          -- If `mu r ≤ mu rC`, we'd contradict minimality (swap roles).
          rcases le_total (mu F r) (mu F rC) with hrc | hcr
          · exact hrC_min.2 hrC' hrc
          · exact hcr
        exact this
      · have hgt : mu F rC0 < mu F r := lt_of_not_ge hle
        exact le_trans hrC_le_rC0 (le_of_lt hgt)
    have hθ_mono : Monotone R.Θ_grid := R.strictMono.monotone
    have hθ_le :
        R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ ≤
          R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := hθ_mono hμ_le
    have :
        (R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ -
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩) / (u : ℝ) ≤
          (R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ -
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩) / (u : ℝ) := by
      have hsub :
          R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ ≤
            R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ :=
        sub_le_sub_right hθ_le _
      have hu_inv_nonneg : 0 ≤ (u : ℝ)⁻¹ := le_of_lt (inv_pos.mpr hu_pos_real)
      have := mul_le_mul_of_nonneg_right hsub hu_inv_nonneg
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    -- Flip sides to get the desired `U ≤ stat r`.
    simpa [U, separationStatistic_base] using this

  refine ⟨{ L := L
            U := U
            hLU := hLU
            admissible := ?_ }⟩
  intro δ hLδ hδU
  refine ⟨?_, ?_⟩
  · intro r hrA
    have hle : separationStatistic_base R r0 r u hu ≤ L := hA_stat_le_L r hrA
    exact lt_of_le_of_lt hle hLδ
  · intro r hrC
    have hle : U ≤ separationStatistic_base R r0 r u hu := hU_le_C_stat r hrC
    exact lt_of_lt_of_le hδU hle

/-- A convenient extraction: for any fixed base `r0` and level `u>0`, there exists at least one
δ satisfying the base-indexed strict A/C inequalities at that level. -/
theorem exists_admissibleDelta_base
    (hk : k ≥ 1) (hd' : ident < d) (r0 : Multi k) (u : ℕ) (hu : 0 < u) :
    ∃ δ : ℝ, AdmissibleDelta_base (k := k) (F := F) (R₀ := R) (d₀ := d) δ r0 u hu := by
  classical
  rcases admissibleInterval_base_exists (hk := hk) (R := R) (d := d) (hd' := hd') r0 u hu with ⟨hI⟩
  rcases admissibleInterval_base_nonempty (R := R) (d := d) (r0 := r0) (u := u) (hu := hu) hI with
    ⟨δ, hLδ, hδU⟩
  exact ⟨δ, hI.admissible δ hLδ hδU⟩

/-!
### Internal base case: if a base-indexed B-witness exists, `chooseδ` is admissible at that base

When the boundary value `μ(r0) ⊕ d^u` already lies on the old `k`-grid, we have a *trade equality*
`μ(rB) = μ(r0) ⊕ d^u` for some old witness `rB`.  In that situation, the δ‑shift lemma
`delta_shift_equiv` pins down the Θ-gap exactly as `u·δ`, and strict monotonicity on the old grid
immediately yields strict A/C inequalities at level `u` for `δ := chooseδ …`.

This isolates the genuinely hard “external” case: when there is **no** such base-indexed B-witness.
-/

lemma admissibleDelta_base_chooseδ_of_B_base_witness
    (hk : k ≥ 1) (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparation α]
    (r0 : Multi k) (u : ℕ) (hu : 0 < u)
    (hB_base : ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 u) :
    AdmissibleDelta_base (k := k) (F := F) (R₀ := R) (d₀ := d) (chooseδ hk R d hd) r0 u hu := by
  classical
  set δ : ℝ := chooseδ hk R d hd
  rcases hB_base with ⟨rB, hrB⟩
  have htrade : mu F rB = op (mu F r0) (iterate_op d u) := by
    simpa [extensionSetB_base, Set.mem_setOf_eq] using hrB
  have hδ_pos : 0 < δ := by
    simpa [δ] using delta_pos hk R IH H d hd
  have hδA := chooseδ_A_bound hk R IH H d hd
  have hδC := chooseδ_C_bound hk R IH H d hd
  have hδB := chooseδ_B_bound hk R IH d hd

  have h_gap_eq :
      R.Θ_grid ⟨mu F rB, mu_mem_kGrid F rB⟩ -
          R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ = (u : ℝ) * δ := by
    have :=
      delta_shift_equiv (R := R) (H := H) (IH := IH) (d := d) (hd := hd)
        (δ := δ) (hδ_pos := hδ_pos) (hδA := hδA) (hδC := hδC) (hδB := hδB) (hΔ := hu)
        (htrade := htrade)
    simpa [mul_comm, δ] using this

  refine ⟨?_, ?_⟩
  · intro r hrA
    have hμ_lt : mu F r < mu F rB := by
      have : mu F r < op (mu F r0) (iterate_op d u) := by
        simpa [extensionSetA_base, Set.mem_setOf_eq] using hrA
      simpa [htrade] using this
    have hθ_lt :
        R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ <
          R.Θ_grid ⟨mu F rB, mu_mem_kGrid F rB⟩ :=
      R.strictMono hμ_lt
    have hu_pos_real : (0 : ℝ) < (u : ℝ) := Nat.cast_pos.mpr hu
    have h_u_ne : (u : ℝ) ≠ 0 := ne_of_gt hu_pos_real
    have hsub :
        R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ <
          R.Θ_grid ⟨mu F rB, mu_mem_kGrid F rB⟩ - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := by
      simpa [sub_eq_add_neg] using
        add_lt_add_right hθ_lt (-R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩)
    have hdiv :
        (R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩) / (u : ℝ) <
          ((u : ℝ) * δ) / (u : ℝ) := by
      have := div_lt_div_of_pos_right hsub hu_pos_real
      simpa [h_gap_eq] using this
    have hcancel : ((u : ℝ) * δ) / (u : ℝ) = δ := by
      have hu0 : (u : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_zero_of_lt hu)
      simpa using (mul_div_cancel_left₀ δ hu0)
    have : separationStatistic_base R r0 r u hu < δ := by
      -- `(u*δ)/u = δ`.
      simpa [separationStatistic_base, hcancel] using hdiv
    simpa [δ] using this
  · intro r hrC
    have hμ_gt : mu F rB < mu F r := by
      have : op (mu F r0) (iterate_op d u) < mu F r := by
        simpa [extensionSetC_base, Set.mem_setOf_eq] using hrC
      simpa [htrade] using this
    have hθ_gt :
        R.Θ_grid ⟨mu F rB, mu_mem_kGrid F rB⟩ <
          R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ :=
      R.strictMono hμ_gt
    have hu_pos_real : (0 : ℝ) < (u : ℝ) := Nat.cast_pos.mpr hu
    have h_u_ne : (u : ℝ) ≠ 0 := ne_of_gt hu_pos_real
    have hsub :
        R.Θ_grid ⟨mu F rB, mu_mem_kGrid F rB⟩ - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ <
          R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := by
      simpa [sub_eq_add_neg] using
        add_lt_add_right hθ_gt (-R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩)
    have hdiv :
        ((u : ℝ) * δ) / (u : ℝ) <
          (R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩) / (u : ℝ) := by
      have := div_lt_div_of_pos_right (by simpa [h_gap_eq] using hsub) hu_pos_real
      simpa using this
    have hcancel : ((u : ℝ) * δ) / (u : ℝ) = δ := by
      have hu0 : (u : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_zero_of_lt hu)
      simpa using (mul_div_cancel_left₀ δ hu0)
    have : δ < separationStatistic_base R r0 r u hu := by
      -- `(u*δ)/u = δ`.
      simpa [separationStatistic_base, hcancel] using hdiv
    simpa [δ] using this

lemma separationStatistic_base_eq_chooseδ_of_B_base_witness
    (hk : k ≥ 1) (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparation α]
    (r0 rB : Multi k) (u : ℕ) (hu : 0 < u)
    (hrB : rB ∈ extensionSetB_base F d r0 u) :
    separationStatistic_base R r0 rB u hu = chooseδ hk R d hd := by
  classical
  set δ : ℝ := chooseδ hk R d hd
  have htrade : mu F rB = op (mu F r0) (iterate_op d u) := by
    simpa [extensionSetB_base, Set.mem_setOf_eq] using hrB
  have hδ_pos : 0 < δ := by
    simpa [δ] using delta_pos hk R IH H d hd
  have hδA := chooseδ_A_bound hk R IH H d hd
  have hδC := chooseδ_C_bound hk R IH H d hd
  have hδB := chooseδ_B_bound hk R IH d hd
  have h_gap_eq :
      R.Θ_grid ⟨mu F rB, mu_mem_kGrid F rB⟩ -
          R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ = (u : ℝ) * δ := by
    have :=
      delta_shift_equiv (R := R) (H := H) (IH := IH) (d := d) (hd := hd)
        (δ := δ) (hδ_pos := hδ_pos) (hδA := hδA) (hδC := hδC) (hδB := hδB) (hΔ := hu)
        (htrade := htrade)
    simpa [mul_comm, δ] using this
  have hu0 : (u : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt hu)
  calc
    separationStatistic_base R r0 rB u hu
        = ((u : ℝ) * δ) / (u : ℝ) := by
            simp [separationStatistic_base, h_gap_eq]
    _ = δ := by simpa using (mul_div_cancel_left₀ δ hu0)
    _ = chooseδ hk R d hd := by simp [δ]

/-!
### Base-indexed accuracy (lifting `accuracy_lemma` by translation)

K&S’s “accuracy” argument (Appendix A.3.4) constructs A/C witnesses with statistics whose gap can
be made arbitrarily small by allowing sufficiently large multiplicities.

The core `accuracy_lemma` in
`Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA/Core/MultiGrid.lean`
is phrased in the absolute (`r0 = 0`) form.
Since the k-grid representation is additive on μ-values, translating both witnesses by a fixed base
`r0` preserves the statistics gap, yielding the corresponding base-indexed statement.
-/

/-- Base-indexed analogue of `accuracy_lemma`: for any base `r0`, there exist level-`u` witnesses
on both sides of the boundary `μ(r0) ⊕ d^u` whose base-indexed statistics differ by less than `ε`. -/
theorem accuracy_lemma_base
    (hk : k ≥ 1) (IH : GridBridge F) (H : GridComm F) (hd : ident < d)
    (r0 : Multi k)
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (rA : Multi k) (u : ℕ) (hu : 0 < u) (_hrA : rA ∈ extensionSetA_base F d r0 u)
      (rC : Multi k) (_hrC : rC ∈ extensionSetC_base F d r0 u),
      separationStatistic_base R r0 rC u hu - separationStatistic_base R r0 rA u hu < ε := by
  classical
  have hA_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetA F d u :=
    extensionSetA_nonempty_of_B_empty F d hd hB_empty
  have hC_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetC F d u :=
    extensionSetC_nonempty_of_B_empty F hk d hd hB_empty
  obtain ⟨rA, uA, huA, hrA, rC, uC, huC, hrC, hgap⟩ :=
    accuracy_lemma (R := R) (d := d) (hd := hd) hB_empty hA_nonempty hC_nonempty ε hε

  -- Scale to a common denominator `u := uA * uC` so both witnesses live at the same level.
  let u : ℕ := uA * uC
  have hu : 0 < u := Nat.mul_pos huA huC
  let rA' : Multi k := scaleMult uC rA
  let rC' : Multi k := scaleMult uA rC
  have hA' : rA' ∈ extensionSetA F d u := by
    have hμA : mu F rA < iterate_op d uA := by
      simpa [extensionSetA, Set.mem_setOf_eq] using hrA
    have h_iter : iterate_op (mu F rA) uC < iterate_op d (uA * uC) := by
      have : iterate_op (mu F rA) (1 * uC) < iterate_op d (uA * uC) :=
        repetition_lemma_lt (mu F rA) d 1 uA uC huC (by simpa [iterate_op_one] using hμA)
      simpa [Nat.one_mul] using this
    have hbridge : mu F (scaleMult uC rA) = iterate_op (mu F rA) uC := IH.bridge rA uC
    have : mu F rA' < iterate_op d u := by
      simpa [rA', u, hbridge] using h_iter
    simpa [extensionSetA, Set.mem_setOf_eq, rA', u] using this

  have hC' : rC' ∈ extensionSetC F d u := by
    have hμC : iterate_op d uC < mu F rC := by
      simpa [extensionSetC, Set.mem_setOf_eq] using hrC
    have h_iter : iterate_op d (uC * uA) < iterate_op (mu F rC) uA := by
      have : iterate_op d (uC * uA) < iterate_op (mu F rC) (1 * uA) :=
        repetition_lemma_lt d (mu F rC) uC 1 uA huA (by simpa [iterate_op_one] using hμC)
      simpa [Nat.one_mul] using this
    have hbridge : mu F (scaleMult uA rC) = iterate_op (mu F rC) uA := IH.bridge rC uA
    have : iterate_op d u < mu F rC' := by
      have : iterate_op d (uC * uA) < mu F (scaleMult uA rC) := by
        simpa [hbridge] using h_iter
      simpa [u, Nat.mul_comm uA uC, rC'] using this
    simpa [extensionSetC, Set.mem_setOf_eq, rC', u] using this

  have hstatA : separationStatistic R rA' u hu = separationStatistic R rA uA huA := by
    have hθ :
        R.Θ_grid ⟨mu F (scaleMult uC rA), mu_mem_kGrid F _⟩ =
          uC * R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ :=
      Theta_scaleMult (R := R) (r := rA) uC
    have huA0 : (uA : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt huA)
    have huC0 : (uC : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt huC)
    have hcancel :
        (uC : ℝ) * R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ /
            ((uA : ℝ) * (uC : ℝ)) =
          R.Θ_grid ⟨mu F rA, mu_mem_kGrid F rA⟩ / (uA : ℝ) := by
      field_simp [huA0, huC0]
    simpa [separationStatistic, rA', u, hθ, Nat.cast_mul, hcancel]

  have hstatC : separationStatistic R rC' u hu = separationStatistic R rC uC huC := by
    have hθ :
        R.Θ_grid ⟨mu F (scaleMult uA rC), mu_mem_kGrid F _⟩ =
          uA * R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ :=
      Theta_scaleMult (R := R) (r := rC) uA
    have huA0 : (uA : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt huA)
    have huC0 : (uC : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt huC)
    have hcancel :
        (uA : ℝ) * R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ /
            ((uA : ℝ) * (uC : ℝ)) =
          R.Θ_grid ⟨mu F rC, mu_mem_kGrid F rC⟩ / (uC : ℝ) := by
      field_simp [huA0, huC0]
    simpa [separationStatistic, rC', u, hθ, Nat.cast_mul, hcancel]

  have hgap' :
      separationStatistic R rC' u hu - separationStatistic R rA' u hu < ε := by
    -- Rewrite the original gap inequality through the scaled statistics.
    simpa [hstatA, hstatC] using hgap

  have hrA_base : (r0 + rA') ∈ extensionSetA_base F d r0 u := by
    have hμA : mu F rA' < iterate_op d u := by
      simpa [extensionSetA, Set.mem_setOf_eq] using hA'
    have hμadd : mu F (r0 + rA') = op (mu F r0) (mu F rA') := by
      simpa using (mu_add_of_comm (F := F) H r0 rA')
    have h :
        op (mu F r0) (mu F rA') < op (mu F r0) (iterate_op d u) :=
      op_strictMono_right (mu F r0) hμA
    have : mu F (r0 + rA') < op (mu F r0) (iterate_op d u) :=
      lt_of_eq_of_lt hμadd h
    simpa [extensionSetA_base, Set.mem_setOf_eq] using this

  have hrC_base : (r0 + rC') ∈ extensionSetC_base F d r0 u := by
    have hμC : iterate_op d u < mu F rC' := by
      simpa [extensionSetC, Set.mem_setOf_eq] using hC'
    have hμadd : mu F (r0 + rC') = op (mu F r0) (mu F rC') := by
      simpa using (mu_add_of_comm (F := F) H r0 rC')
    have h :
        op (mu F r0) (iterate_op d u) < op (mu F r0) (mu F rC') :=
      op_strictMono_right (mu F r0) hμC
    have : op (mu F r0) (iterate_op d u) < mu F (r0 + rC') :=
      lt_of_lt_of_eq h hμadd.symm
    simpa [extensionSetC_base, Set.mem_setOf_eq] using this

  have hstatA :
      separationStatistic_base R r0 (r0 + rA') u hu = separationStatistic R rA' u hu := by
    have hθ_add :
        R.Θ_grid ⟨mu F (r0 + rA'), mu_mem_kGrid F (r0 + rA')⟩ =
          R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ +
            R.Θ_grid ⟨mu F rA', mu_mem_kGrid F rA'⟩ := by
      simpa [Pi.add_apply, add_comm, add_left_comm, add_assoc] using (R.add r0 rA')
    simp [separationStatistic_base, separationStatistic, hθ_add]

  have hstatC :
      separationStatistic_base R r0 (r0 + rC') u hu = separationStatistic R rC' u hu := by
    have hθ_add :
        R.Θ_grid ⟨mu F (r0 + rC'), mu_mem_kGrid F (r0 + rC')⟩ =
          R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ +
            R.Θ_grid ⟨mu F rC', mu_mem_kGrid F rC'⟩ := by
      simpa [Pi.add_apply, add_comm, add_left_comm, add_assoc] using (R.add r0 rC')
    simp [separationStatistic_base, separationStatistic, hθ_add]

  refine ⟨r0 + rA', u, hu, hrA_base, r0 + rC', hrC_base, ?_⟩
  simpa [hstatA, hstatC] using hgap'

/-- Base-indexed cut tightness at a common denominator: translating the absolute `δ`-approximants
from `delta_cut_tight_common_den` preserves statistics gaps. -/
theorem delta_cut_tight_common_den_base
    (hk : k ≥ 1) (IH : GridBridge F) (H : GridComm F) (hd : ident < d)
    (r0 : Multi k)
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (u : ℕ) (hu : 0 < u) (rA rC : Multi k),
      rA ∈ extensionSetA_base F d r0 u ∧ rC ∈ extensionSetC_base F d r0 u ∧
      |separationStatistic_base R r0 rC u hu - chooseδ hk R d hd| < ε ∧
      |chooseδ hk R d hd - separationStatistic_base R r0 rA u hu| < ε := by
  classical
  obtain ⟨u, hu, rA', rC', hrA', hrC', hC_close, hA_close⟩ :=
    delta_cut_tight_common_den (hk := hk) (R := R) (IH := IH) (H := H) (d := d) (hd := hd)
      (hB_empty := hB_empty) ε hε

  have hrA_base : (r0 + rA') ∈ extensionSetA_base F d r0 u := by
    have hμA : mu F rA' < iterate_op d u := by
      simpa [extensionSetA, Set.mem_setOf_eq] using hrA'
    have hμadd : mu F (r0 + rA') = op (mu F r0) (mu F rA') := by
      simpa using (mu_add_of_comm (F := F) H r0 rA')
    have h :
        op (mu F r0) (mu F rA') < op (mu F r0) (iterate_op d u) :=
      op_strictMono_right (mu F r0) hμA
    have : mu F (r0 + rA') < op (mu F r0) (iterate_op d u) :=
      lt_of_eq_of_lt hμadd h
    simpa [extensionSetA_base, Set.mem_setOf_eq] using this

  have hrC_base : (r0 + rC') ∈ extensionSetC_base F d r0 u := by
    have hμC : iterate_op d u < mu F rC' := by
      simpa [extensionSetC, Set.mem_setOf_eq] using hrC'
    have hμadd : mu F (r0 + rC') = op (mu F r0) (mu F rC') := by
      simpa using (mu_add_of_comm (F := F) H r0 rC')
    have h :
        op (mu F r0) (iterate_op d u) < op (mu F r0) (mu F rC') :=
      op_strictMono_right (mu F r0) hμC
    have : op (mu F r0) (iterate_op d u) < mu F (r0 + rC') :=
      lt_of_lt_of_eq h hμadd.symm
    simpa [extensionSetC_base, Set.mem_setOf_eq] using this

  have hstatA :
      separationStatistic_base R r0 (r0 + rA') u hu = separationStatistic R rA' u hu := by
    have hθ_add :
        R.Θ_grid ⟨mu F (r0 + rA'), mu_mem_kGrid F (r0 + rA')⟩ =
          R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ +
            R.Θ_grid ⟨mu F rA', mu_mem_kGrid F rA'⟩ := by
      simpa [Pi.add_apply, add_comm, add_left_comm, add_assoc] using (R.add r0 rA')
    simp [separationStatistic_base, separationStatistic, hθ_add]

  have hstatC :
      separationStatistic_base R r0 (r0 + rC') u hu = separationStatistic R rC' u hu := by
    have hθ_add :
        R.Θ_grid ⟨mu F (r0 + rC'), mu_mem_kGrid F (r0 + rC')⟩ =
          R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ +
            R.Θ_grid ⟨mu F rC', mu_mem_kGrid F rC'⟩ := by
      simpa [Pi.add_apply, add_comm, add_left_comm, add_assoc] using (R.add r0 rC')
    simp [separationStatistic_base, separationStatistic, hθ_add]

  refine ⟨u, hu, r0 + rA', r0 + rC', hrA_base, hrC_base, ?_, ?_⟩
  · simpa [hstatC] using hC_close
  · simpa [hstatA] using hA_close

/-- Variant of `delta_cut_tight_common_den_base` that forces the common denominator to be a
multiple of a prescribed `m > 0`.

This is often convenient when one wants to compare against a fixed target level `Δ` and therefore
work at denominators divisible by `Δ` (K&S Appendix A.3.4 style). -/
theorem delta_cut_tight_common_den_base_mul
    (hk : k ≥ 1) (IH : GridBridge F) (H : GridComm F) (hd : ident < d)
    (r0 : Multi k)
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u)
    (m : ℕ) (hm : 0 < m)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (u : ℕ) (hu : 0 < u) (_hmul : m ∣ u) (rA rC : Multi k),
      rA ∈ extensionSetA_base F d r0 u ∧ rC ∈ extensionSetC_base F d r0 u ∧
      |separationStatistic_base R r0 rC u hu - chooseδ hk R d hd| < ε ∧
      |chooseδ hk R d hd - separationStatistic_base R r0 rA u hu| < ε := by
  classical
  obtain ⟨u0, hu0, rA0, rC0, hrA0, hrC0, hC_close0, hA_close0⟩ :=
    delta_cut_tight_common_den (hk := hk) (R := R) (IH := IH) (H := H) (d := d) (hd := hd)
      (hB_empty := hB_empty) ε hε
  -- Scale to a denominator divisible by `m`.
  let u : ℕ := u0 * m
  have hu : 0 < u := Nat.mul_pos hu0 hm
  have hmul : m ∣ u := by
    refine ⟨u0, ?_⟩
    simp [u, Nat.mul_comm]
  let rA1 : Multi k := scaleMult m rA0
  let rC1 : Multi k := scaleMult m rC0

  have hrA1 : rA1 ∈ extensionSetA F d u := by
    have hμA : mu F rA0 < iterate_op d u0 := by
      simpa [extensionSetA, Set.mem_setOf_eq] using hrA0
    have h_iter : iterate_op (mu F rA0) m < iterate_op d (u0 * m) := by
      have : iterate_op (mu F rA0) (1 * m) < iterate_op d (u0 * m) :=
        repetition_lemma_lt (mu F rA0) d 1 u0 m hm (by simpa [iterate_op_one] using hμA)
      simpa [Nat.one_mul] using this
    have hbridge : mu F (scaleMult m rA0) = iterate_op (mu F rA0) m := IH.bridge rA0 m
    have : mu F rA1 < iterate_op d u := by
      simpa [rA1, u, hbridge] using h_iter
    simpa [extensionSetA, Set.mem_setOf_eq, rA1, u] using this

  have hrC1 : rC1 ∈ extensionSetC F d u := by
    have hμC : iterate_op d u0 < mu F rC0 := by
      simpa [extensionSetC, Set.mem_setOf_eq] using hrC0
    have h_iter : iterate_op d (u0 * m) < iterate_op (mu F rC0) m := by
      have : iterate_op d (u0 * m) < iterate_op (mu F rC0) (1 * m) :=
        repetition_lemma_lt d (mu F rC0) u0 1 m hm (by simpa [iterate_op_one] using hμC)
      simpa [Nat.one_mul] using this
    have hbridge : mu F (scaleMult m rC0) = iterate_op (mu F rC0) m := IH.bridge rC0 m
    have : iterate_op d u < mu F rC1 := by
      have : iterate_op d (u0 * m) < mu F (scaleMult m rC0) := by simpa [hbridge] using h_iter
      simpa [rC1, u] using this
    simpa [extensionSetC, Set.mem_setOf_eq, rC1, u] using this

  -- Scaling preserves the separation statistics.
  have hstatA_scale : separationStatistic R rA1 u hu = separationStatistic R rA0 u0 hu0 := by
    have hθ :
        R.Θ_grid ⟨mu F (scaleMult m rA0), mu_mem_kGrid F _⟩ =
          m * R.Θ_grid ⟨mu F rA0, mu_mem_kGrid F rA0⟩ :=
      Theta_scaleMult (R := R) (r := rA0) m
    have hu0_0 : (u0 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hu0)
    have hm_0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hm)
    have hcancel :
        (m : ℝ) * R.Θ_grid ⟨mu F rA0, mu_mem_kGrid F rA0⟩ / ((m : ℝ) * (u0 : ℝ)) =
          R.Θ_grid ⟨mu F rA0, mu_mem_kGrid F rA0⟩ / (u0 : ℝ) := by
      field_simp [hu0_0, hm_0]
    -- Rewrite `/ u` as `/ (u0*m)` and cancel the common `m`.
    simpa [separationStatistic, rA1, u, hθ, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm, hcancel]

  have hstatC_scale : separationStatistic R rC1 u hu = separationStatistic R rC0 u0 hu0 := by
    have hθ :
        R.Θ_grid ⟨mu F (scaleMult m rC0), mu_mem_kGrid F _⟩ =
          m * R.Θ_grid ⟨mu F rC0, mu_mem_kGrid F rC0⟩ :=
      Theta_scaleMult (R := R) (r := rC0) m
    have hu0_0 : (u0 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hu0)
    have hm_0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hm)
    have hcancel :
        (m : ℝ) * R.Θ_grid ⟨mu F rC0, mu_mem_kGrid F rC0⟩ / ((m : ℝ) * (u0 : ℝ)) =
          R.Θ_grid ⟨mu F rC0, mu_mem_kGrid F rC0⟩ / (u0 : ℝ) := by
      field_simp [hu0_0, hm_0]
    simpa [separationStatistic, rC1, u, hθ, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm, hcancel]

  have hrA_base : (r0 + rA1) ∈ extensionSetA_base F d r0 u := by
    have hμA : mu F rA1 < iterate_op d u := by
      simpa [extensionSetA, Set.mem_setOf_eq] using hrA1
    have hμadd : mu F (r0 + rA1) = op (mu F r0) (mu F rA1) := by
      simpa using (mu_add_of_comm (F := F) H r0 rA1)
    have h :
        op (mu F r0) (mu F rA1) < op (mu F r0) (iterate_op d u) :=
      op_strictMono_right (mu F r0) hμA
    have : mu F (r0 + rA1) < op (mu F r0) (iterate_op d u) := lt_of_eq_of_lt hμadd h
    simpa [extensionSetA_base, Set.mem_setOf_eq] using this

  have hrC_base : (r0 + rC1) ∈ extensionSetC_base F d r0 u := by
    have hμC : iterate_op d u < mu F rC1 := by
      simpa [extensionSetC, Set.mem_setOf_eq] using hrC1
    have hμadd : mu F (r0 + rC1) = op (mu F r0) (mu F rC1) := by
      simpa using (mu_add_of_comm (F := F) H r0 rC1)
    have h :
        op (mu F r0) (iterate_op d u) < op (mu F r0) (mu F rC1) :=
      op_strictMono_right (mu F r0) hμC
    have : op (mu F r0) (iterate_op d u) < mu F (r0 + rC1) := lt_of_lt_of_eq h hμadd.symm
    simpa [extensionSetC_base, Set.mem_setOf_eq] using this

  have hstatA_base :
      separationStatistic_base R r0 (r0 + rA1) u hu = separationStatistic R rA1 u hu := by
    have hθ_add :
        R.Θ_grid ⟨mu F (r0 + rA1), mu_mem_kGrid F (r0 + rA1)⟩ =
          R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ +
            R.Θ_grid ⟨mu F rA1, mu_mem_kGrid F rA1⟩ := by
      simpa [Pi.add_apply, add_comm, add_left_comm, add_assoc] using (R.add r0 rA1)
    simp [separationStatistic_base, separationStatistic, hθ_add]

  have hstatC_base :
      separationStatistic_base R r0 (r0 + rC1) u hu = separationStatistic R rC1 u hu := by
    have hθ_add :
        R.Θ_grid ⟨mu F (r0 + rC1), mu_mem_kGrid F (r0 + rC1)⟩ =
          R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ +
            R.Θ_grid ⟨mu F rC1, mu_mem_kGrid F rC1⟩ := by
      simpa [Pi.add_apply, add_comm, add_left_comm, add_assoc] using (R.add r0 rC1)
    simp [separationStatistic_base, separationStatistic, hθ_add]

  have hC_close :
      |separationStatistic_base R r0 (r0 + rC1) u hu - chooseδ hk R d hd| < ε := by
    simpa [hstatC_base, hstatC_scale] using hC_close0
  have hA_close :
      |chooseδ hk R d hd - separationStatistic_base R r0 (r0 + rA1) u hu| < ε := by
    simpa [hstatA_base, hstatA_scale] using hA_close0

  refine ⟨u, hu, hmul, r0 + rA1, r0 + rC1, hrA_base, hrC_base, hC_close, hA_close⟩

/-!
### Local realizability from base-indexed admissibility (Ben/Goertzel v2 helper)

Ben’s Lemma 7 (“order-invariance inside an admissible gap”) needs an intermediate hypothesis:
for each δ in an admissible interval, there is a strictly monotone evaluator on the *relevant*
join-multiplicity points that agrees with the affine `ThetaRaw` formula.

In this file, the minimal such hypothesis is `RealizesThetaRaw_pair`, which lives only on the
two-point slice `{joinPoint r0 u, joinPoint ry v}`.

The lemma below shows how to build this local realization from a base-indexed admissibility
assumption at the *difference level* `u - v` (together with “no base-indexed B-witness” to rule
out the degenerate equality case).
-/

lemma realizesThetaRaw_pair_of_admissibleDelta_base
    {δ : ℝ} (r0 ry : Multi k) (u v : ℕ) (huv : v < u)
    (hδ :
      AdmissibleDelta_base (k := k) (F := F) (R₀ := R) (d₀ := d) δ r0 (u - v)
        (Nat.sub_pos_of_lt huv))
    (hB_base : ¬ ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 (u - v)) :
    RealizesThetaRaw_pair (R := R) (F := F) (d := d) (hd := hd) δ r0 ry u v := by
  classical
  -- Name the two designated points in the extended grid.
  let pL := joinPoint (F := F) (d := d) (hd := hd) r0 u
  let pR := joinPoint (F := F) (d := d) (hd := hd) ry v

  have pR_ne_pL : (pR : {x // x ∈ kGrid (extendAtomFamily F d hd)}) ≠ pL := by
    intro hEq
    -- Equality of join-points yields a base-indexed B-witness at level (u - v).
    have huv_le : v ≤ u := le_of_lt huv
    have hμEq :
        mu (extendAtomFamily F d hd) (joinMulti r0 u) =
          mu (extendAtomFamily F d hd) (joinMulti ry v) := by
      -- `joinPoint` is the underlying `mu`-value packaged as a grid element.
      simpa [pL, pR, joinPoint] using (congrArg Subtype.val hEq).symm
    have hB : ry ∈ extensionSetB_base F d r0 (u - v) :=
      extensionSetB_base_of_mu_joinMulti_eq (F := F) d hd r0 ry u v huv_le hμEq
    exact hB_base ⟨ry, hB⟩

  -- Define the evaluator by case-splitting on which of the two points we have.
  refine
    ⟨fun p =>
        if p.1 = pL then ThetaRaw (R := R) (F := F) δ r0 u
        else ThetaRaw (R := R) (F := F) δ ry v,
      ?_, ?_, ?_⟩

  · -- StrictMono on the two-point slice.
    intro a b hab
    have hab' :
        (a : {x // x ∈ kGrid (extendAtomFamily F d hd)}) <
          (b : {x // x ∈ kGrid (extendAtomFamily F d hd)}) := hab
    -- Reduce to cases for the underlying points.
    rcases a.property with ha | ha <;> rcases b.property with hb | hb
    · -- a.val = pL, b.val = pL: impossible
      have hab'' : pL < pL := by
        simpa [ha, hb] using hab'
      exact (lt_irrefl _ hab'').elim
    · -- a.val = pL, b.val = pR
        -- Determine which base-indexed side `ry` lies on, by cancelling the common `d^v` tail.
        have hμ : (pL : {x // x ∈ kGrid (extendAtomFamily F d hd)}) <
            (pR : {x // x ∈ kGrid (extendAtomFamily F d hd)}) := by
          simpa [ha, hb] using hab'
        have hμL :
            (pL : {x // x ∈ kGrid (extendAtomFamily F d hd)}).1 =
              op (mu F r0) (iterate_op d u) := by
          simpa [pL, joinPoint] using (mu_extend_last F d hd r0 u)
        have hμR :
            (pR : {x // x ∈ kGrid (extendAtomFamily F d hd)}).1 =
              op (mu F ry) (iterate_op d v) := by
          simpa [pR, joinPoint] using (mu_extend_last F d hd ry v)
        have hsplt : iterate_op d u = op (iterate_op d (u - v)) (iterate_op d v) := by
          have huv_le : v ≤ u := le_of_lt huv
          have huv_eq : u - v + v = u := Nat.sub_add_cancel huv_le
          have h :
              iterate_op d (u - v + v) = op (iterate_op d (u - v)) (iterate_op d v) :=
            (iterate_op_add d (u - v) v).symm
          -- `h` is `iterate_op d (u - v + v) = ...`; rewrite the LHS to `iterate_op d u`.
          simpa [huv_eq] using h
        have hμ' :
            op (op (mu F r0) (iterate_op d (u - v))) (iterate_op d v) <
              op (mu F ry) (iterate_op d v) := by
          have : op (mu F r0) (iterate_op d u) < op (mu F ry) (iterate_op d v) := by
            simpa [hμL, hμR] using (show (pL : {x // x ∈ kGrid (extendAtomFamily F d hd)}).1 <
              (pR : {x // x ∈ kGrid (extendAtomFamily F d hd)}).1 from hμ)
          simpa [hsplt, op_assoc] using this
        have hmono : Monotone (fun z : α => op z (iterate_op d v)) :=
          (op_strictMono_left (iterate_op d v)).monotone
        have h_base_lt : op (mu F r0) (iterate_op d (u - v)) < mu F ry :=
          hmono.reflect_lt hμ'
        have hryC : ry ∈ extensionSetC_base F d r0 (u - v) := by
          simpa [extensionSetC_base, Set.mem_setOf_eq] using h_base_lt
        have hstat : δ < separationStatistic_base R r0 ry (u - v) (Nat.sub_pos_of_lt huv) :=
          (hδ.2 ry hryC)
        -- Convert δ < statistic into a ΘRaw inequality.
        have hu_pos_real : (0 : ℝ) < (u - v : ℕ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt huv)
        have hgap :
            δ * ((u : ℝ) - (v : ℝ)) <
              R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩ -
                R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := by
          have h :=
            (lt_div_iff₀ hu_pos_real).1 (by simpa [separationStatistic_base] using hstat)
          have huv_le : v ≤ u := le_of_lt huv
          -- Rewrite the casted subtraction as a difference of casts.
          have h' :
              δ * ((u : ℝ) - (v : ℝ)) <
                R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩ -
                  R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := by
            simpa [Nat.cast_sub huv_le, mul_assoc, mul_left_comm, mul_comm] using h
          exact h'
        have huv_cast : (u : ℝ) = (v : ℝ) + (u - v : ℕ) := by
          have : u = v + (u - v) := by omega
          simpa [Nat.cast_add] using congrArg (fun n : ℕ => (n : ℝ)) this
        have hΘraw : ThetaRaw (R := R) (F := F) δ r0 u < ThetaRaw (R := R) (F := F) δ ry v := by
          -- Θ(r0)+uδ = Θ(r0)+vδ+(u-v)δ < Θ(ry)+vδ
          have : R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ + (u : ℝ) * δ <
              R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩ + (v : ℝ) * δ := by
            calc
              R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ + (u : ℝ) * δ
                  = R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ + ((v : ℝ) + (u - v : ℕ)) * δ := by
                      simp [huv_cast]
              _ = R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ + (v : ℝ) * δ + δ * ((u : ℝ) - (v : ℝ)) := by
                      -- Expand `(v + (u-v)) * δ` and rewrite the casted subtraction as `u - v`.
                      have huv_le : v ≤ u := le_of_lt huv
                      -- `((u - v : ℕ) : ℝ) = (u : ℝ) - (v : ℝ)`
                      have hsub : ((u - v : ℕ) : ℝ) = (u : ℝ) - (v : ℝ) := by
                        simpa using (Nat.cast_sub huv_le : ((u - v : ℕ) : ℝ) = (u : ℝ) - (v : ℝ))
                      -- Distribute and commute into the target shape.
                      -- `ring_nf` is robust once casts are normalized.
                      -- (The goal is pure ℝ arithmetic.)
                      -- First rewrite the casted subtraction, then normalize.
                      simp [hsub]
                      ring_nf
              _ < R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩ + (v : ℝ) * δ := by
                      linarith [hgap]
              _ = R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩ + (v : ℝ) * δ := rfl
          simpa [ThetaRaw, add_comm, add_left_comm, add_assoc] using this
        -- Finish this StrictMono case.
        -- `pL` picks the left branch; `pR` picks the right branch using `pR_ne_pL`.
        simpa [ha, hb, pL, pR, pR_ne_pL] using hΘraw
    · -- a.val = pR, b.val = pL
      -- Cancel the common tail as above, but in the opposite direction.
      have hμ : (pR : {x // x ∈ kGrid (extendAtomFamily F d hd)}) <
          (pL : {x // x ∈ kGrid (extendAtomFamily F d hd)}) := by
        simpa [ha, hb] using hab'
      have hμL :
          (pL : {x // x ∈ kGrid (extendAtomFamily F d hd)}).1 =
            op (mu F r0) (iterate_op d u) := by
        simpa [pL, joinPoint] using (mu_extend_last F d hd r0 u)
      have hμR :
          (pR : {x // x ∈ kGrid (extendAtomFamily F d hd)}).1 =
            op (mu F ry) (iterate_op d v) := by
        simpa [pR, joinPoint] using (mu_extend_last F d hd ry v)
      have hsplt : iterate_op d u = op (iterate_op d (u - v)) (iterate_op d v) := by
        have huv_le : v ≤ u := le_of_lt huv
        have huv_eq : u - v + v = u := Nat.sub_add_cancel huv_le
        have h :
            iterate_op d (u - v + v) = op (iterate_op d (u - v)) (iterate_op d v) :=
          (iterate_op_add d (u - v) v).symm
        simpa [huv_eq] using h
      have hμ' :
          op (mu F ry) (iterate_op d v) <
            op (op (mu F r0) (iterate_op d (u - v))) (iterate_op d v) := by
        have : op (mu F ry) (iterate_op d v) < op (mu F r0) (iterate_op d u) := by
          simpa [hμL, hμR] using (show (pR : {x // x ∈ kGrid (extendAtomFamily F d hd)}).1 <
            (pL : {x // x ∈ kGrid (extendAtomFamily F d hd)}).1 from hμ)
        simpa [hsplt, op_assoc] using this
      have h_base_lt : mu F ry < op (mu F r0) (iterate_op d (u - v)) :=
        (by
          have hmono : Monotone (fun z : α => op z (iterate_op d v)) :=
            (op_strictMono_left (iterate_op d v)).monotone
          exact hmono.reflect_lt hμ')
      have hryA : ry ∈ extensionSetA_base F d r0 (u - v) := by
        simpa [extensionSetA_base, Set.mem_setOf_eq] using h_base_lt
      have hstat : separationStatistic_base R r0 ry (u - v) (Nat.sub_pos_of_lt huv) < δ :=
        (hδ.1 ry hryA)
      have hu_pos_real : (0 : ℝ) < (u - v : ℕ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt huv)
      have hgap :
          R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩ -
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ < δ * ((u : ℝ) - (v : ℝ)) := by
        have h :=
          (div_lt_iff₀ hu_pos_real).1 (by simpa [separationStatistic_base] using hstat)
        have huv_le : v ≤ u := le_of_lt huv
        simpa [Nat.cast_sub huv_le, mul_comm, mul_left_comm, mul_assoc] using h
      have huv_cast : (u : ℝ) = (v : ℝ) + (u - v : ℕ) := by
        have : u = v + (u - v) := by omega
        simpa [Nat.cast_add] using congrArg (fun n : ℕ => (n : ℝ)) this
      have hΘraw :
          ThetaRaw (R := R) (F := F) δ ry v < ThetaRaw (R := R) (F := F) δ r0 u := by
        have : R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩ + (v : ℝ) * δ <
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ + (u : ℝ) * δ := by
          -- Θ(ry) - Θ(r0) < (u-v)δ
          have : R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩ <
              R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ + δ * ((u : ℝ) - (v : ℝ)) := by
            linarith [hgap]
          calc
            R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩ + (v : ℝ) * δ
                < (R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ + δ * ((u : ℝ) - (v : ℝ))) + (v : ℝ) * δ := by
                    linarith
            _ = R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ + (u : ℝ) * δ := by
                  simp [huv_cast]; ring_nf
        simpa [ThetaRaw, add_comm, add_left_comm, add_assoc] using this
      -- Rewrite evaluator values at the two points.
      simpa [ha, hb, pL, pR, pR_ne_pL] using hΘraw
    · -- a.val = pR, b.val = pR: impossible
      have hab'' : pR < pR := by
        simpa [ha, hb] using hab'
      exact (lt_irrefl _ hab'').elim
  · -- left point equation
    simp [pL, joinPoint]
  · -- right point equation
    -- Keep `joinPoint` folded so the `if_neg pR_ne_pL` rewrite can fire.
    simp [pR, pL, pR_ne_pL]

/-!
### Base-indexed “interval freedom” cannot be global in this development

Ben/Goertzel v2 Lemma 6 is phrased as an “open interval of admissible slopes” in the (base-indexed)
`B = ∅` case.  In the current Lean development, the cut-tightness lemma `delta_cut_tight` (proved
from K&S’s repetition/accuracy arguments) makes the *global* admissibility predicate rigid: there
can be at most one δ satisfying *all* A/C constraints simultaneously.

The lemma below makes a related point for the base-indexed, all-levels predicate
`AdmissibleDelta_base_all`: if some δ works for *all* levels `u` relative to a base `r0`, then δ is
already globally admissible (relative to `ident`), hence δ must equal `chooseδ`.

This does not rule out “interval freedom” for *finite* sets of constraints (or for a fixed `u`);
it only rules out a nontrivial open interval of δ’s satisfying *all* constraints at once.
-/

lemma admissibleDelta_base_all_implies_admissibleDelta
    (H : GridComm F) (r0 : Multi k) {δ : ℝ}
    (hδ : AdmissibleDelta_base_all (k := k) (F := F) (R₀ := R) (d₀ := d) δ r0) :
    AdmissibleDelta (R := R) (F := F) (d := d) δ := by
  classical
  refine ⟨?_, ?_⟩
  · intro r u hu hrA
    -- Translate an absolute A-witness by the base `r0`.
    have hrA_base : (r0 + r) ∈ extensionSetA_base F d r0 u := by
      have hμr : mu F r < iterate_op d u := by
        simpa [extensionSetA, Set.mem_setOf_eq] using hrA
      have hμadd : mu F (r0 + r) = op (mu F r0) (mu F r) := by
        simpa using (mu_add_of_comm (H := H) r0 r)
      have : mu F (r0 + r) < op (mu F r0) (iterate_op d u) := by
        -- Strict monotone translation on the right.
        simpa [hμadd] using (op_strictMono_right (mu F r0) hμr)
      simpa [extensionSetA_base, Set.mem_setOf_eq] using this
    have hstat_base_lt : separationStatistic_base R r0 (r0 + r) u hu < δ :=
      (hδ u hu).1 (r0 + r) hrA_base
    -- Cancel the common Θ(r0) using additivity.
    have hθ_add :
        R.Θ_grid ⟨mu F (r0 + r), mu_mem_kGrid F (r0 + r)⟩ =
          R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ +
            R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := by
      simpa [Pi.add_apply, add_comm, add_left_comm, add_assoc] using (R.add r0 r)
    have hstat_eq :
        separationStatistic_base R r0 (r0 + r) u hu = separationStatistic R r u hu := by
      -- (Θ(r0+r) - Θ(r0))/u = Θ(r)/u by additivity
      simp [separationStatistic_base, separationStatistic, hθ_add]
    simpa [hstat_eq] using hstat_base_lt
  · intro r u hu hrC
    have hrC_base : (r0 + r) ∈ extensionSetC_base F d r0 u := by
      have hμr : iterate_op d u < mu F r := by
        simpa [extensionSetC, Set.mem_setOf_eq] using hrC
      have hμadd : mu F (r0 + r) = op (mu F r0) (mu F r) := by
        simpa using (mu_add_of_comm (H := H) r0 r)
      have : op (mu F r0) (iterate_op d u) < mu F (r0 + r) := by
        simpa [hμadd] using (op_strictMono_right (mu F r0) hμr)
      simpa [extensionSetC_base, Set.mem_setOf_eq] using this
    have hstat_base_gt : δ < separationStatistic_base R r0 (r0 + r) u hu :=
      (hδ u hu).2 (r0 + r) hrC_base
    have hθ_add :
        R.Θ_grid ⟨mu F (r0 + r), mu_mem_kGrid F (r0 + r)⟩ =
          R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ +
            R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := by
      simpa [Pi.add_apply, add_comm, add_left_comm, add_assoc] using (R.add r0 r)
    have hstat_eq :
        separationStatistic_base R r0 (r0 + r) u hu = separationStatistic R r u hu := by
      simp [separationStatistic_base, separationStatistic, hθ_add]
    simpa [hstat_eq] using hstat_base_gt

/-!
### Uniqueness of an admissible δ (global, absolute A/B/C)

Ben/Goertzel v2 (Lemma 6) informally speaks of an *open interval* of admissible “slopes” in the
`B = ∅` regime. In the current Lean formalization, an “admissible δ” for a fixed `(F,d)` is the
predicate `AdmissibleDelta` above: δ lies strictly between *all* A- and C-side statistics for
every `u > 0`.

Under the existing `delta_cut_tight` lemma (K&S “accuracy”/Dedekind-cut tightness), this *global*
notion of admissibility is rigid: there can be **at most one** such δ, namely `chooseδ`.

This does not refute K&S Appendix A; it clarifies that any “interval of freedom” must come from a
weaker (e.g. finite‑constraint and/or base‑indexed) admissibility notion than `AdmissibleDelta`.
-/

lemma admissibleDelta_eq_chooseδ
    (IH : GridBridge F) (H : GridComm F)
    (hB_empty : ∀ (r : Multi k) (u : ℕ), 0 < u → r ∉ extensionSetB F d u)
    {δ : ℝ} (hδ : AdmissibleDelta (R := R) (F := F) (d := d) δ) :
    δ = chooseδ hk R d hd := by
  classical
  set δ₀ : ℝ := chooseδ hk R d hd
  by_contra hne
  have hε : 0 < |δ - δ₀| / 2 := by
    have : 0 < |δ - δ₀| := abs_pos.mpr (sub_ne_zero.mpr hne)
    linarith
  obtain ⟨rA, uA, rC, uC, huA, huC, hrA, hrC, hC_close, hA_close⟩ :=
    delta_cut_tight (hk := hk) (R := R) (IH := IH) (H := H) (d := d) (hd := hd)
      (hB_empty := hB_empty) (ε := |δ - δ₀| / 2) hε
  have hA_bound : separationStatistic R rA uA huA ≤ δ₀ :=
    by simpa [δ₀] using chooseδ_A_bound hk R IH H d hd rA uA huA hrA
  have hC_bound : δ₀ ≤ separationStatistic R rC uC huC :=
    by simpa [δ₀] using chooseδ_C_bound hk R IH H d hd rC uC huC hrC
  have hA_lt : separationStatistic R rA uA huA < δ := hδ.1 rA uA huA hrA
  have hC_gt : δ < separationStatistic R rC uC huC := hδ.2 rC uC huC hrC
  have hδ₀_minus : δ₀ - (|δ - δ₀| / 2) < δ := by
    -- From `|δ₀ - statA| < ε` and `statA ≤ δ₀`, get `δ₀ - ε < statA < δ`.
    have hpos : 0 ≤ δ₀ - separationStatistic R rA uA huA := by linarith [hA_bound]
    have hδ₀_lt : δ₀ - separationStatistic R rA uA huA < |δ - δ₀| / 2 := by
      -- `|δ₀ - statA| < ε` and `δ₀ ≥ statA` ⇒ `δ₀ - statA < ε`.
      simpa [abs_of_nonneg hpos, δ₀] using hA_close
    have : δ₀ - (|δ - δ₀| / 2) < separationStatistic R rA uA huA := by linarith
    exact lt_trans this hA_lt
  have hδ₀_plus : δ < δ₀ + (|δ - δ₀| / 2) := by
    -- From `|statC - δ₀| < ε` and `δ₀ ≤ statC`, get `δ < statC < δ₀ + ε`.
    have hpos : 0 ≤ separationStatistic R rC uC huC - δ₀ := by linarith [hC_bound]
    have hδ₀_lt : separationStatistic R rC uC huC - δ₀ < |δ - δ₀| / 2 := by
      simpa [abs_of_nonneg hpos, δ₀] using hC_close
    have hC_lt : separationStatistic R rC uC huC < δ₀ + (|δ - δ₀| / 2) := by linarith
    exact lt_trans hC_gt hC_lt
  -- Now δ lies strictly inside the interval (δ₀ - ε, δ₀ + ε), contradicting ε = |δ-δ₀|/2.
  have habs : |δ - δ₀| < |δ - δ₀| / 2 := by
    have h1 : -( |δ - δ₀| / 2) < δ - δ₀ := by linarith [hδ₀_minus]
    have h2 : δ - δ₀ < (|δ - δ₀| / 2) := by linarith [hδ₀_plus]
    simpa [abs_lt] using And.intro h1 h2
  linarith

lemma admissibleDelta_base_all_eq_chooseδ
    (IH : GridBridge F) (H : GridComm F)
    (hB_empty : ∀ (r : Multi k) (u : ℕ), 0 < u → r ∉ extensionSetB F d u)
    (r0 : Multi k) {δ : ℝ}
    (hδ : AdmissibleDelta_base_all (k := k) (F := F) (R₀ := R) (d₀ := d) δ r0) :
    δ = chooseδ hk R d hd :=
  admissibleDelta_eq_chooseδ (hk := hk) (R := R) (IH := IH) (H := H) (d := d) (hd := hd)
    (hB_empty := hB_empty) (δ := δ)
    (admissibleDelta_base_all_implies_admissibleDelta (R := R) (F := F) (d := d) (H := H) r0 hδ)

/-!
### A concrete “false lead” that can be ruled out

Ben/Goertzel v2 Lemma 6 speaks of an *open interval* of admissible “slopes” in the `B = ∅` case.
For the **global** admissibility notion `AdmissibleDelta` (which quantifies over *all* A/C witnesses
at every level), this cannot happen: under `delta_cut_tight`, any globally admissible δ is forced to
equal `chooseδ`, so there is at most one such δ.

This does not refute the v2 strategy: it clarifies that any “interval of freedom” must be a weaker,
more local admissibility notion (e.g. finite-constraint and/or base-indexed), not `AdmissibleDelta`.
-/

theorem no_open_interval_of_global_admissibleDelta
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F)
    (d : α) (hd : ident < d)
    (hB_empty : ∀ (r : Multi k) (u : ℕ), 0 < u → r ∉ extensionSetB F d u) :
    ¬ ∃ L U : ℝ, L < U ∧
        ∀ δ : ℝ, L < δ → δ < U → AdmissibleDelta (R := R) (F := F) (d := d) δ := by
  classical
  intro h
  rcases h with ⟨L, U, hLU, hAdm⟩
  -- Pick two distinct points in the open interval.
  set δ₁ : ℝ := (L + U) / 2
  set δ₂ : ℝ := (L + δ₁) / 2
  have hδ₁_in : L < δ₁ ∧ δ₁ < U := by
    have h1 : L < (L + U) / 2 := by linarith [hLU]
    have h2 : (L + U) / 2 < U := by linarith [hLU]
    simpa [δ₁] using And.intro h1 h2
  have hδ₂_in : L < δ₂ ∧ δ₂ < U := by
    have hLδ₁ : L < δ₁ := hδ₁_in.1
    have hδ₁U : δ₁ < U := hδ₁_in.2
    have h1 : L < (L + δ₁) / 2 := by linarith [hLδ₁]
    have h2 : (L + δ₁) / 2 < U := by linarith [hδ₁U]
    simpa [δ₂] using And.intro h1 h2
  have hδ₁ : AdmissibleDelta (R := R) (F := F) (d := d) δ₁ := hAdm δ₁ hδ₁_in.1 hδ₁_in.2
  have hδ₂ : AdmissibleDelta (R := R) (F := F) (d := d) δ₂ := hAdm δ₂ hδ₂_in.1 hδ₂_in.2
  -- Global admissibility is rigid: both must equal chooseδ.
  have hEq₁ :
      δ₁ = chooseδ hk R d hd :=
    admissibleDelta_eq_chooseδ (hk := hk) (R := R) (F := F) (d := d) (hd := hd)
      (IH := IH) (H := H) (hB_empty := hB_empty) hδ₁
  have hEq₂ :
      δ₂ = chooseδ hk R d hd :=
    admissibleDelta_eq_chooseδ (hk := hk) (R := R) (F := F) (d := d) (hd := hd)
      (IH := IH) (H := H) (hB_empty := hB_empty) hδ₂
  -- But δ₂ < δ₁ by construction.
  have hδ₂_lt_δ₁ : δ₂ < δ₁ := by
    have : (L + δ₁) / 2 < δ₁ := by linarith [hδ₁_in.1]
    simpa [δ₂] using this
  -- Contradiction: δ₂ < δ₁ but both equal chooseδ.
  have hcontra' : chooseδ hk R d hd < chooseδ hk R d hd := by
    have h' : δ₂ < δ₁ := hδ₂_lt_δ₁
    -- Replace δ₂ and δ₁ by `chooseδ` using the two rigidity equalities.
    rw [hEq₂, hEq₁] at h'
    exact h'
  exact lt_irrefl _ hcontra'

/-!
Goertzel Lemma 7 (invariance inside the admissible gap), specialized to the current
`ThetaRaw` expression family: if two admissible δ choices are both valid, then the sign of the
difference between two “new expressions” is invariant.

This is *exactly* the qualitative ingredient needed to rule out boundary equalities in the B-empty
strict-gap lemmas: if a boundary equality held for δ, then small admissible perturbations of δ
would flip the inequality, contradicting invariance.
-/
class GoertzelInvarianceSpec : Prop where
  invariant :
    ∀ {δ₁ δ₂ : ℝ},
      AdmissibleDelta (R := R) (F := F) (d := d) δ₁ →
      AdmissibleDelta (R := R) (F := F) (d := d) δ₂ →
      ∀ (r_old_x r_old_y : Multi k) (t_x t_y : ℕ),
        (ThetaRaw (R := R) (F := F) δ₁ r_old_x t_x < ThetaRaw (R := R) (F := F) δ₁ r_old_y t_y) ↔
        (ThetaRaw (R := R) (F := F) δ₂ r_old_x t_x < ThetaRaw (R := R) (F := F) δ₂ r_old_y t_y)

end

/-!
## Base-indexed A/B/C sets (as in K&S A.3.4 and Goertzel v2)

One recurring source of confusion is the meaning of “B is empty”.

In the Appendix-A *extension step*, K&S define A/B/C **relative to a fixed base old-grid element**
`X0` (their `µ(r0,…,t0)`), by comparing *old-grid values* to the “new family” value
`X0 ⊕ d^u`. In that base-indexed sense:
- `B` consists of old-grid values that land *exactly on* `X0 ⊕ d^u` for some `u>0`.

This is **not** the same as the absolute set
`extensionSetB F d u := {r | mu F r = d^u}` used in parts of the current codebase
(which corresponds to the special base `X0 = ident`).

Ben/Goertzel Lemma 7’s cancellation step produces an equality of the form `X0 ⊕ d^w = Y`
with `Y` an old-grid value; this is a *base-indexed* B-witness for base `X0`, but it need not
produce an absolute witness `mu F r = d^w`.

The counterexample
`Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA/Counterexamples/GoertzelLemma7.lean`
demonstrates this mismatch
in a concrete additive model: global “absolute B-empty” can hold while there exist old-grid
values `X0, Y` with `X0 ⊕ d = Y`.
-/

section BaseIndexed

variable {k : ℕ} {F : AtomFamily α k}

open scoped BigOperators

noncomputable def baseTarget (r0 : Multi k) (d : α) (u : ℕ) : α :=
  op (mu F r0) (iterate_op d u)

def baseSetA (r0 : Multi k) (d : α) (u : ℕ) : Set (Multi k) :=
  extensionSetA_base F d r0 u

def baseSetB (r0 : Multi k) (d : α) (u : ℕ) : Set (Multi k) :=
  extensionSetB_base F d r0 u

def baseSetC (r0 : Multi k) (d : α) (u : ℕ) : Set (Multi k) :=
  extensionSetC_base F d r0 u

lemma mem_baseSetB_iff
    (r0 r : Multi k) (d : α) (u : ℕ) :
    r ∈ baseSetB (F := F) r0 d u ↔ mu F r = op (mu F r0) (iterate_op d u) := by
  rfl

lemma baseSetB_witness_of_eq
    (r0 r : Multi k) (d : α) (u : ℕ)
    (h : mu F r = op (mu F r0) (iterate_op d u)) :
    r ∈ baseSetB (F := F) r0 d u := by
  exact h

lemma baseIndexed_cancel_eq
    (r0 ry : Multi k) (d : α) (u v : ℕ) (huv : v ≤ u)
    (hEq :
      op (mu F r0) (iterate_op d u) =
        op (mu F ry) (iterate_op d v)) :
    mu F ry = op (mu F r0) (iterate_op d (u - v)) := by
  simpa using cancel_right_iterate_eq (F := F) (d := d) r0 ry u v huv hEq

end BaseIndexed

/-!
## Algebraic core of Goertzel Lemma 7 (affine “flip ⇒ equality”)

In the refactored codebase, the would-be extended evaluator on join-multiplicity witnesses is

`ThetaRaw δ r_old t = Θ(old) + t·δ`.

For fixed `(r_old_x,t_x)` and `(r_old_y,t_y)`, the difference is affine in `δ`.  Therefore, if
the strict inequality flips between two parameters `δ₁ < δ₂`, then there is an explicit “critical
value” `δ₀` where equality holds.  This step is *pure algebra* (no topology, no IVT).

Turning that equality into a contradiction in the B-empty case requires an *additional* link
between “numeric equality” and “algebraic equality” (injectivity of the extension map), which is
exactly where circularity can enter.
-/

section
variable {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)

lemma ThetaRaw_sub
    (δ : ℝ) (r_old_x r_old_y : Multi k) (t_x t_y : ℕ) :
    ThetaRaw (R := R) (F := F) δ r_old_x t_x - ThetaRaw (R := R) (F := F) δ r_old_y t_y =
      (R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩) +
        ((t_x : ℝ) - (t_y : ℝ)) * δ := by
  simp [ThetaRaw, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, mul_comm]

theorem ThetaRaw_flip_implies_eq_between
    {δ₁ δ₂ : ℝ} (_hδ : δ₁ < δ₂)
    (r_old_x r_old_y : Multi k) (t_x t_y : ℕ)
    (ht : t_y < t_x)
    (h1 : ThetaRaw (R := R) (F := F) δ₁ r_old_x t_x <
          ThetaRaw (R := R) (F := F) δ₁ r_old_y t_y)
    (h2 : ThetaRaw (R := R) (F := F) δ₂ r_old_y t_y <
          ThetaRaw (R := R) (F := F) δ₂ r_old_x t_x) :
    ∃ δ₀ : ℝ, δ₁ < δ₀ ∧ δ₀ < δ₂ ∧
      ThetaRaw (R := R) (F := F) δ₀ r_old_x t_x =
        ThetaRaw (R := R) (F := F) δ₀ r_old_y t_y := by
  classical
  set a : ℝ :=
    (R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
        R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩) with ha
  set b : ℝ := (t_x : ℝ) - (t_y : ℝ) with hb
  have hb_pos : 0 < b := by
    have : (t_y : ℝ) < (t_x : ℝ) := by exact_mod_cast ht
    simpa [b] using sub_pos.mpr this
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  set δ₀ : ℝ := (-a) / b with hδ₀
  refine ⟨δ₀, ?_, ?_, ?_⟩
  · -- δ₁ < δ₀ from `a + b*δ₁ < 0`
    have hdiff₁ : a + b * δ₁ < 0 := by
      have : ThetaRaw (R := R) (F := F) δ₁ r_old_x t_x -
            ThetaRaw (R := R) (F := F) δ₁ r_old_y t_y < 0 := sub_neg.mpr h1
      simpa [ThetaRaw_sub (R := R) (F := F), a, b, ha, hb, add_assoc, add_left_comm, add_comm] using this
    have hmul : δ₁ * b < -a := by
      have : b * δ₁ < -a := by linarith [hdiff₁]
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have : δ₁ < (-a) / b := (lt_div_iff₀ hb_pos).2 hmul
    simpa [hδ₀] using this
  · -- δ₀ < δ₂ from `0 < a + b*δ₂`
    have hdiff₂ : 0 < a + b * δ₂ := by
      have : 0 < ThetaRaw (R := R) (F := F) δ₂ r_old_x t_x -
            ThetaRaw (R := R) (F := F) δ₂ r_old_y t_y := sub_pos.mpr h2
      simpa [ThetaRaw_sub (R := R) (F := F), a, b, ha, hb, add_assoc, add_left_comm, add_comm] using this
    have hmul : -a < δ₂ * b := by
      have : -a < b * δ₂ := by linarith [hdiff₂]
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have : (-a) / b < δ₂ := (div_lt_iff₀ hb_pos).2 hmul
    simpa [hδ₀] using this
  · -- equality at δ₀
    have hdiff0 : ThetaRaw (R := R) (F := F) δ₀ r_old_x t_x -
          ThetaRaw (R := R) (F := F) δ₀ r_old_y t_y = 0 := by
      have hab : a + b * δ₀ = 0 := by
        have hb_mul : b * ((-a) / b) = -a := by
          field_simp [hb_ne]
        have : a + b * ((-a) / b) = 0 := by linarith [hb_mul]
        simpa [δ₀, hδ₀] using this
      have hdiff :
          ThetaRaw (R := R) (F := F) δ₀ r_old_x t_x -
              ThetaRaw (R := R) (F := F) δ₀ r_old_y t_y = a + b * δ₀ := by
        simp [ThetaRaw_sub (R := R) (F := F), a, b]
      simp [hdiff, hab]
    exact sub_eq_zero.mp hdiff0

end

section BenV2

variable {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
variable (IH : GridBridge F) (H : GridComm F)
variable (d : α) (hd : ident < d)

/-! Ben/Goertzel v2 Lemma 7, extracted as a *conditional* Lean lemma:

If a comparison between two `ThetaRaw` expressions flips between `δ₁ < δ₂`, then there is an
intermediate `δ₀` with equality (pure affine algebra). If every intermediate `δ` realizes the
`ThetaRaw` formula via a strictly monotone evaluator on the extended μ-grid, then that numeric
equality forces an *algebraic* equality on the extended grid, hence a **base-indexed B-witness**
by right-cancellation. -/
/-- Pair-realization version of Ben/Goertzel v2 Lemma 7.

This is strictly weaker than `flip_implies_baseIndexed_B_witness`: it only assumes realizability
of `ThetaRaw` on the **specific two join-multiplicity points** involved in the flip. -/
lemma flip_implies_baseIndexed_B_witness_pair
    {δ₁ δ₂ : ℝ} (hδ : δ₁ < δ₂)
    (r0 ry : Multi k) (u v : ℕ) (huv : v < u)
    (hRealize :
      ∀ δ, δ₁ < δ → δ < δ₂ →
        RealizesThetaRaw_pair (R := R) (F := F) (d := d) (hd := hd) δ r0 ry u v)
    (h1 : ThetaRaw (R := R) (F := F) δ₁ r0 u < ThetaRaw (R := R) (F := F) δ₁ ry v)
    (h2 : ThetaRaw (R := R) (F := F) δ₂ ry v < ThetaRaw (R := R) (F := F) δ₂ r0 u) :
    ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 (u - v) := by
  classical
  have huv_le : v ≤ u := le_of_lt huv
  obtain ⟨δ₀, hδ₁, hδ₂, hEq⟩ :=
    ThetaRaw_flip_implies_eq_between (R := R) (F := F) (δ₁ := δ₁) (δ₂ := δ₂) hδ
      r0 ry u v huv h1 h2
  have hμEq :
      mu (extendAtomFamily F d hd) (joinMulti r0 u) =
        mu (extendAtomFamily F d hd) (joinMulti ry v) :=
    ThetaRaw_eq_implies_mu_joinMulti_eq_of_pair (R := R) (F := F) (d := d) (hd := hd)
      (hδ := hRealize δ₀ hδ₁ hδ₂) hEq
  have hB : ry ∈ extensionSetB_base F d r0 (u - v) :=
    extensionSetB_base_of_mu_joinMulti_eq (F := F) d hd r0 ry u v huv_le hμEq
  exact ⟨ry, hB⟩

/-!
### Ben/Goertzel v2 Lemma 7 “wiring” (from admissible intervals)

The flip lemma above is purely algebraic: it turns a sign flip into an intermediate equality, and
then requires `RealizesThetaRaw_pair` on that intermediate point to convert a `ThetaRaw`-equality
into an equality of the corresponding μ-values.

The helper `realizesThetaRaw_pair_of_admissibleDelta_base` (proved earlier in this file) shows how
to build `RealizesThetaRaw_pair` from a **base-indexed admissibility** hypothesis at the
difference-level `u - v`, together with the **absence** of base-indexed B-witnesses at that level.

The two lemmas below package that wiring so it can be used directly in Goertzel-v2 style proofs.
-/

lemma realizesThetaRaw_pair_of_admissibleInterval_base
    {δ : ℝ} (r0 ry : Multi k) (u v : ℕ) (huv : v < u)
    (hI :
      AdmissibleInterval_base (k := k) (F := F) (R₀ := R) (d₀ := d) r0 (u - v)
        (Nat.sub_pos_of_lt huv))
    (hB_base : ¬ ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 (u - v))
    (hδL : hI.L < δ) (hδU : δ < hI.U) :
    RealizesThetaRaw_pair (R := R) (F := F) (d := d) (hd := hd) δ r0 ry u v := by
  have hδ :
      AdmissibleDelta_base (k := k) (F := F) (R₀ := R) (d₀ := d) δ r0 (u - v)
        (Nat.sub_pos_of_lt huv) :=
    hI.admissible δ hδL hδU
  exact
    realizesThetaRaw_pair_of_admissibleDelta_base (R := R) (F := F) (d := d) (hd := hd) (r0 := r0)
      (ry := ry) (u := u) (v := v) huv hδ hB_base

lemma flip_implies_baseIndexed_B_witness_pair_of_admissibleInterval_base
    {δ₁ δ₂ : ℝ} (hδ : δ₁ < δ₂)
    (r0 ry : Multi k) (u v : ℕ) (huv : v < u)
    (hd' : ident < d)
    (hI :
      AdmissibleInterval_base (k := k) (F := F) (R₀ := R) (d₀ := d) r0 (u - v)
        (Nat.sub_pos_of_lt huv))
    (hB_base : ¬ ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 (u - v))
    (hδ₁I : hI.L < δ₁) (_hδ₁U : δ₁ < hI.U) (_hδ₂I : hI.L < δ₂) (hδ₂U : δ₂ < hI.U)
    (h1 : ThetaRaw (R := R) (F := F) δ₁ r0 u < ThetaRaw (R := R) (F := F) δ₁ ry v)
    (h2 : ThetaRaw (R := R) (F := F) δ₂ ry v < ThetaRaw (R := R) (F := F) δ₂ r0 u) :
    ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 (u - v) := by
  have hRealize :
      ∀ δ, δ₁ < δ → δ < δ₂ →
        RealizesThetaRaw_pair (R := R) (F := F) (d := d) (hd := hd') δ r0 ry u v := by
    intro δ hδ₁ hδ₂
    have hδL : hI.L < δ := lt_trans hδ₁I hδ₁
    have hδU : δ < hI.U := lt_trans hδ₂ hδ₂U
    exact
      realizesThetaRaw_pair_of_admissibleInterval_base (R := R) (F := F) (d := d) (hd := hd')
        (r0 := r0) (ry := ry) (u := u) (v := v) huv hI hB_base hδL hδU
  exact
    flip_implies_baseIndexed_B_witness_pair (R := R) (F := F) (d := d) (hd := hd') hδ r0 ry u v
      huv hRealize h1 h2

/-- **Goertzel v2 Lemma 7 (order-invariance, base-indexed)**.

Within a fixed admissible interval `I` (for the base `r0` at the difference level `u - v`),
the truth value of `ThetaRaw δ r0 u < ThetaRaw δ ry v` cannot depend on the particular choice
`δ ∈ I`, provided there is no base-indexed `B`-witness at that difference level.

This matches Lemma 7 in `claude/literature/Foundations-of-inference-new-proofs_v2.pdf`
(§4.3.3), specialized to the Lean `ThetaRaw` encoding. -/
theorem ThetaRaw_order_invariant_inside_admissibleInterval_base
    {δ₁ δ₂ : ℝ}
    (r0 ry : Multi k) (u v : ℕ) (huv : v < u)
    (hd' : ident < d)
    (hI :
      AdmissibleInterval_base (k := k) (F := F) (R₀ := R) (d₀ := d) r0 (u - v)
        (Nat.sub_pos_of_lt huv))
    (hB_base : ¬ ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 (u - v))
    (hδ₁L : hI.L < δ₁) (hδ₁U : δ₁ < hI.U)
    (hδ₂L : hI.L < δ₂) (hδ₂U : δ₂ < hI.U) :
    (ThetaRaw (R := R) (F := F) δ₁ r0 u < ThetaRaw (R := R) (F := F) δ₁ ry v) ↔
      (ThetaRaw (R := R) (F := F) δ₂ r0 u < ThetaRaw (R := R) (F := F) δ₂ ry v) := by
  classical
  -- Trichotomy on the two choices.
  rcases lt_trichotomy δ₁ δ₂ with hδ | rfl | hδ
  · -- Case δ₁ < δ₂: show both directions.
    have huv_le : v ≤ u := le_of_lt huv
    have hReal2 :
        RealizesThetaRaw_pair (R := R) (F := F) (d := d) (hd := hd') δ₂ r0 ry u v :=
      realizesThetaRaw_pair_of_admissibleInterval_base (R := R) (F := F) (d := d) (hd := hd')
        (r0 := r0) (ry := ry) (u := u) (v := v) huv hI hB_base hδ₂L hδ₂U
    constructor
    · intro h1
      -- If the inequality failed at δ₂, we’d get either an equality or a strict reversal; both
      -- imply a base-indexed B-witness at (u - v), contradicting `hB_base`.
      by_contra h2
      have h2le :
          ThetaRaw (R := R) (F := F) δ₂ ry v ≤ ThetaRaw (R := R) (F := F) δ₂ r0 u :=
        le_of_not_gt h2
      have h2' : ThetaRaw (R := R) (F := F) δ₂ ry v < ThetaRaw (R := R) (F := F) δ₂ r0 u ∨
          ThetaRaw (R := R) (F := F) δ₂ ry v = ThetaRaw (R := R) (F := F) δ₂ r0 u :=
        lt_or_eq_of_le h2le
      cases h2' with
      | inl hrev =>
          rcases
              flip_implies_baseIndexed_B_witness_pair_of_admissibleInterval_base (R := R) (F := F)
                (d := d) (hd' := hd') (r0 := r0) (ry := ry)
                (u := u) (v := v) hδ huv hI hB_base hδ₁L hδ₁U hδ₂L hδ₂U h1 hrev
            with ⟨rB, hrB⟩
          exact hB_base ⟨rB, hrB⟩
      | inr hEq =>
          have hμEq :
              mu (extendAtomFamily F d hd') (joinMulti r0 u) =
                mu (extendAtomFamily F d hd') (joinMulti ry v) :=
            ThetaRaw_eq_implies_mu_joinMulti_eq_of_pair (R := R) (F := F) (d := d) (hd := hd')
              (hδ := hReal2) (hEq := hEq.symm)
          have hB : ry ∈ extensionSetB_base F d r0 (u - v) :=
            extensionSetB_base_of_mu_joinMulti_eq (F := F) d hd' r0 ry u v huv_le hμEq
          exact hB_base ⟨ry, hB⟩
    · -- The converse direction (δ₂ inequality ⇒ δ₁ inequality) holds unconditionally because
      -- `v < u` makes the comparison affine-decreasing in δ.
      intro h2
      -- Work with the difference `ThetaRaw … - ThetaRaw …`.
      have hdiff2 :
          ThetaRaw (R := R) (F := F) δ₂ r0 u - ThetaRaw (R := R) (F := F) δ₂ ry v < 0 :=
        sub_neg.mpr h2
      set a : ℝ :=
        (R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ -
            R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩) with ha
      set b : ℝ := (u : ℝ) - (v : ℝ) with hb
      have hb_pos : 0 < b := by
        have : (v : ℝ) < (u : ℝ) := by exact_mod_cast huv
        simpa [b] using sub_pos.mpr this
      have hdiff2' : a + b * δ₂ < 0 := by
        -- Rewrite the δ₂ difference using `ThetaRaw_sub`.
        simpa [ThetaRaw_sub (R := R) (F := F), a, b, ha, hb, add_assoc, add_left_comm, add_comm]
          using hdiff2
      have hmul : b * δ₁ < b * δ₂ := mul_lt_mul_of_pos_left hδ hb_pos
      -- Avoid a convoluted inequality chain by using `linarith`.
      have hdiff1' : a + b * δ₁ < 0 := by
        linarith [hdiff2', hmul]
      have hdiff1 :
          ThetaRaw (R := R) (F := F) δ₁ r0 u - ThetaRaw (R := R) (F := F) δ₁ ry v < 0 := by
        simpa [ThetaRaw_sub (R := R) (F := F), a, b, ha, hb, add_assoc, add_left_comm, add_comm]
          using hdiff1'
      exact sub_neg.mp hdiff1
  · -- Case δ₁ = δ₂.
    simp
  · -- Case δ₂ < δ₁: apply the δ₂<δ₁ result and then symmetrize.
    have huv_le : v ≤ u := le_of_lt huv
    have hReal1 :
        RealizesThetaRaw_pair (R := R) (F := F) (d := d) (hd := hd') δ₁ r0 ry u v :=
      realizesThetaRaw_pair_of_admissibleInterval_base (R := R) (F := F) (d := d) (hd := hd')
        (r0 := r0) (ry := ry) (u := u) (v := v) huv hI hB_base hδ₁L hδ₁U
    constructor
    · intro h1
      -- The direction δ₁-inequality ⇒ δ₂-inequality holds unconditionally (smaller δ strengthens the `<`).
      have hdiff1 :
          ThetaRaw (R := R) (F := F) δ₁ r0 u - ThetaRaw (R := R) (F := F) δ₁ ry v < 0 :=
        sub_neg.mpr h1
      set a : ℝ :=
        (R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ -
            R.Θ_grid ⟨mu F ry, mu_mem_kGrid F ry⟩) with ha
      set b : ℝ := (u : ℝ) - (v : ℝ) with hb
      have hb_pos : 0 < b := by
        have : (v : ℝ) < (u : ℝ) := by exact_mod_cast huv
        simpa [b] using sub_pos.mpr this
      have hdiff1' : a + b * δ₁ < 0 := by
        simpa [ThetaRaw_sub (R := R) (F := F), a, b, ha, hb, add_assoc, add_left_comm, add_comm]
          using hdiff1
      have hmul : b * δ₂ < b * δ₁ := mul_lt_mul_of_pos_left hδ hb_pos
      have hdiff2' : a + b * δ₂ < 0 := by
        linarith [hdiff1', hmul]
      have hdiff2 :
          ThetaRaw (R := R) (F := F) δ₂ r0 u - ThetaRaw (R := R) (F := F) δ₂ ry v < 0 := by
        simpa [ThetaRaw_sub (R := R) (F := F), a, b, ha, hb, add_assoc, add_left_comm, add_comm]
          using hdiff2'
      exact sub_neg.mp hdiff2
    · intro h2
      -- If the inequality failed at δ₁, we’d get either an equality or a strict reversal; both
      -- imply a base-indexed B-witness at (u - v), contradicting `hB_base`.
      by_contra h1
      have h1le :
          ThetaRaw (R := R) (F := F) δ₁ ry v ≤ ThetaRaw (R := R) (F := F) δ₁ r0 u :=
        le_of_not_gt h1
      have h1' : ThetaRaw (R := R) (F := F) δ₁ ry v < ThetaRaw (R := R) (F := F) δ₁ r0 u ∨
          ThetaRaw (R := R) (F := F) δ₁ ry v = ThetaRaw (R := R) (F := F) δ₁ r0 u :=
        lt_or_eq_of_le h1le
      cases h1' with
      | inl hrev =>
          rcases
              flip_implies_baseIndexed_B_witness_pair_of_admissibleInterval_base (R := R) (F := F)
                (d := d) (hd' := hd') (r0 := r0) (ry := ry)
                (u := u) (v := v) hδ huv hI hB_base hδ₂L hδ₂U hδ₁L hδ₁U h2 hrev
            with ⟨rB, hrB⟩
          exact hB_base ⟨rB, hrB⟩
      | inr hEq =>
          have hμEq :
              mu (extendAtomFamily F d hd') (joinMulti r0 u) =
                mu (extendAtomFamily F d hd') (joinMulti ry v) :=
            ThetaRaw_eq_implies_mu_joinMulti_eq_of_pair (R := R) (F := F) (d := d) (hd := hd')
              (hδ := hReal1) (hEq := hEq.symm)
          have hB : ry ∈ extensionSetB_base F d r0 (u - v) :=
            extensionSetB_base_of_mu_joinMulti_eq (F := F) d hd' r0 ry u v huv_le hμEq
          exact hB_base ⟨ry, hB⟩

/-- **Goertzel v2 Lemma 8 (finite truncation, base-indexed)**.

For a fixed base `r0` and a finite set of positive “new levels” `U`, consider the set of formal
symbols consisting of:
- old-grid witnesses `r : Multi k` (interpreted as `ThetaRaw δ r 0`), and
- base-family witnesses `(r0,u)` for `u ∈ U` (interpreted as `ThetaRaw δ r0 u`).

If two choices `δ₁, δ₂` lie inside the base-indexed admissible interval at **each** `u ∈ U`, and
there are no base-indexed `B` witnesses at those levels, then every pairwise strict comparison in
this finite “old ∪ base-family” set is independent of whether one uses `δ₁` or `δ₂`.

This is the Lean analogue of Lemma 8 in
`claude/literature/Foundations-of-inference-new-proofs_v2.pdf` (where the argument is
presented for the coordinate-host picture; here we express it directly in terms of `ThetaRaw`). -/
theorem ThetaRaw_order_invariant_oldGrid_with_baseFamily_finset
    {δ₁ δ₂ : ℝ} (r0 : Multi k) (U : Finset ℕ)
    (hUpos : ∀ u ∈ U, 0 < u)
    (hd' : ident < d)
    (hI :
      ∀ u (huU : u ∈ U),
        AdmissibleInterval_base (k := k) (F := F) (R₀ := R) (d₀ := d) r0 u (hUpos u huU))
    (hB :
      ∀ u ∈ U, ¬ ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 u)
    (hδ₁ :
      ∀ u (huU : u ∈ U), (hI u huU).L < δ₁ ∧ δ₁ < (hI u huU).U)
    (hδ₂ :
      ∀ u (huU : u ∈ U), (hI u huU).L < δ₂ ∧ δ₂ < (hI u huU).U) :
    ∀ a b : Sum (Multi k) {u : ℕ // u ∈ U},
      ((match a with
          | Sum.inl r => ThetaRaw (R := R) (F := F) δ₁ r 0
          | Sum.inr u => ThetaRaw (R := R) (F := F) δ₁ r0 u.1) <
          (match b with
            | Sum.inl r => ThetaRaw (R := R) (F := F) δ₁ r 0
            | Sum.inr u => ThetaRaw (R := R) (F := F) δ₁ r0 u.1)) ↔
        ((match a with
          | Sum.inl r => ThetaRaw (R := R) (F := F) δ₂ r 0
          | Sum.inr u => ThetaRaw (R := R) (F := F) δ₂ r0 u.1) <
          (match b with
            | Sum.inl r => ThetaRaw (R := R) (F := F) δ₂ r 0
            | Sum.inr u => ThetaRaw (R := R) (F := F) δ₂ r0 u.1)) := by
  classical
  intro a b
  -- Name the evaluation function to keep the cases readable.
  let val : ℝ → Sum (Multi k) {u : ℕ // u ∈ U} → ℝ := fun δ p =>
    match p with
    | Sum.inl r => ThetaRaw (R := R) (F := F) δ r 0
    | Sum.inr u => ThetaRaw (R := R) (F := F) δ r0 u.1
  -- Helper: any δ in the admissible interval at level `u` is positive (since `r0 ∈ A_base`).
  have delta_pos_of_mem {δ : ℝ} {u : ℕ} (huU : u ∈ U)
      (hL : (hI u huU).L < δ) (hU : δ < (hI u huU).U) : 0 < δ := by
    have hu : 0 < u := hUpos u huU
    have hAd : AdmissibleDelta_base (k := k) (F := F) (R₀ := R) (d₀ := d) δ r0 u hu :=
      (hI u huU).admissible δ hL hU
    have hr0A : r0 ∈ extensionSetA_base F d r0 u := by
      have hdu : ident < iterate_op d u := iterate_op_pos d hd' u hu
      have : mu F r0 < op (mu F r0) (iterate_op d u) := by
        simpa [op_ident_right] using (op_strictMono_right (mu F r0) hdu)
      simpa [extensionSetA_base, Set.mem_setOf_eq] using this
    have h0lt : separationStatistic_base R r0 r0 u hu < δ := (hAd.1 r0 hr0A)
    simpa [separationStatistic_base] using h0lt
  -- Helper: old/new equality at an admissible δ creates a base-indexed B-witness, hence is impossible under `hB`.
  have no_old_new_eq {δ : ℝ} {u : ℕ} (huU : u ∈ U)
      (hL : (hI u huU).L < δ) (hU : δ < (hI u huU).U)
      (r : Multi k) :
      ThetaRaw (R := R) (F := F) δ r0 u ≠ ThetaRaw (R := R) (F := F) δ r 0 := by
    intro hEq
    have hu : 0 < u := hUpos u huU
    have hReal :
        RealizesThetaRaw_pair (R := R) (F := F) (d := d) (hd := hd') δ r0 r u 0 :=
      realizesThetaRaw_pair_of_admissibleInterval_base (R := R) (F := F) (d := d) (hd := hd')
        (r0 := r0) (ry := r) (u := u) (v := 0) hu
        (hI := by simpa [Nat.sub_zero] using (hI u huU))
        (hB_base := by
          -- `u - 0 = u`, so the hypothesis `hB` applies directly.
          simpa [Nat.sub_zero] using (hB u huU))
        (hδL := hL) (hδU := hU)
    have hμEq :
        mu (extendAtomFamily F d hd') (joinMulti r0 u) =
          mu (extendAtomFamily F d hd') (joinMulti r 0) :=
      ThetaRaw_eq_implies_mu_joinMulti_eq_of_pair (R := R) (F := F) (d := d) (hd := hd')
        (hδ := hReal) (hEq := hEq)
    have hBmem : r ∈ extensionSetB_base F d r0 (u - 0) :=
      extensionSetB_base_of_mu_joinMulti_eq (F := F) d hd' r0 r u 0 (Nat.zero_le _) hμEq
    have : ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 u := by
      refine ⟨r, ?_⟩
      simpa [Nat.sub_zero] using hBmem
    exact (hB u huU) this
  -- Case analysis on the two formal symbols.
  cases a with
  | inl ra =>
      cases b with
      | inl rb =>
          -- old-old: δ disappears since `t = 0`.
          simp [ThetaRaw]
      | inr ub =>
          -- old-new: reduce to invariance of the opposite comparison (new-old) plus exclusion of equality.
          have huU : ub.1 ∈ U := ub.2
          have hδ₁b := hδ₁ ub.1 huU
          have hδ₂b := hδ₂ ub.1 huU
          have hneq1 :
              ThetaRaw (R := R) (F := F) δ₁ r0 ub.1 ≠ ThetaRaw (R := R) (F := F) δ₁ ra 0 :=
            no_old_new_eq (u := ub.1) huU hδ₁b.1 hδ₁b.2 ra
          have hneq2 :
              ThetaRaw (R := R) (F := F) δ₂ r0 ub.1 ≠ ThetaRaw (R := R) (F := F) δ₂ ra 0 :=
            no_old_new_eq (u := ub.1) huU hδ₂b.1 hδ₂b.2 ra
          have hflip :
              (ThetaRaw (R := R) (F := F) δ₁ r0 ub.1 < ThetaRaw (R := R) (F := F) δ₁ ra 0) ↔
                (ThetaRaw (R := R) (F := F) δ₂ r0 ub.1 < ThetaRaw (R := R) (F := F) δ₂ ra 0) :=
            ThetaRaw_order_invariant_inside_admissibleInterval_base (R := R) (F := F) (d := d)
              (r0 := r0) (ry := ra) (u := ub.1) (v := 0) (huv := hUpos ub.1 huU) (hd' := hd')
              (hI := by simpa [Nat.sub_zero] using (hI ub.1 huU))
              (hB_base := by simpa [Nat.sub_zero] using (hB ub.1 huU))
              (hδ₁L := hδ₁b.1) (hδ₁U := hδ₁b.2) (hδ₂L := hδ₂b.1) (hδ₂U := hδ₂b.2)
          -- Convert `<` by trichotomy using `hneq1`/`hneq2`.
          have hold1 :
              ThetaRaw (R := R) (F := F) δ₁ ra 0 < ThetaRaw (R := R) (F := F) δ₁ r0 ub.1 ↔
                ¬ ThetaRaw (R := R) (F := F) δ₁ r0 ub.1 < ThetaRaw (R := R) (F := F) δ₁ ra 0 := by
            constructor
            · intro hlt
              exact not_lt_of_gt hlt
            · intro hn
              rcases lt_trichotomy (ThetaRaw (R := R) (F := F) δ₁ r0 ub.1)
                  (ThetaRaw (R := R) (F := F) δ₁ ra 0) with hlt | heq | hgt
              · exact (hn hlt).elim
              · exact (hneq1 heq).elim
              · exact hgt
          have hold2 :
              ThetaRaw (R := R) (F := F) δ₂ ra 0 < ThetaRaw (R := R) (F := F) δ₂ r0 ub.1 ↔
                ¬ ThetaRaw (R := R) (F := F) δ₂ r0 ub.1 < ThetaRaw (R := R) (F := F) δ₂ ra 0 := by
            constructor
            · intro hlt
              exact not_lt_of_gt hlt
            · intro hn
              rcases lt_trichotomy (ThetaRaw (R := R) (F := F) δ₂ r0 ub.1)
                  (ThetaRaw (R := R) (F := F) δ₂ ra 0) with hlt | heq | hgt
              · exact (hn hlt).elim
              · exact (hneq2 heq).elim
              · exact hgt
          -- Put it together.
          have :
              (ThetaRaw (R := R) (F := F) δ₁ ra 0 < ThetaRaw (R := R) (F := F) δ₁ r0 ub.1) ↔
                (ThetaRaw (R := R) (F := F) δ₂ ra 0 < ThetaRaw (R := R) (F := F) δ₂ r0 ub.1) := by
            -- `old<new` is the negation of `new<old` on each side.
            simpa [hold1, hold2] using (not_congr hflip)
          simpa [val] using this
  | inr ua =>
      cases b with
      | inl rb =>
          -- new-old: direct use of Lemma 7.
          have huU : ua.1 ∈ U := ua.2
          have hδ₁a := hδ₁ ua.1 huU
          have hδ₂a := hδ₂ ua.1 huU
          have :
              (ThetaRaw (R := R) (F := F) δ₁ r0 ua.1 < ThetaRaw (R := R) (F := F) δ₁ rb 0) ↔
                (ThetaRaw (R := R) (F := F) δ₂ r0 ua.1 < ThetaRaw (R := R) (F := F) δ₂ rb 0) :=
            ThetaRaw_order_invariant_inside_admissibleInterval_base (R := R) (F := F) (d := d)
              (r0 := r0) (ry := rb) (u := ua.1) (v := 0) (huv := hUpos ua.1 huU) (hd' := hd')
              (hI := by simpa [Nat.sub_zero] using (hI ua.1 huU))
              (hB_base := by simpa [Nat.sub_zero] using (hB ua.1 huU))
              (hδ₁L := hδ₁a.1) (hδ₁U := hδ₁a.2) (hδ₂L := hδ₂a.1) (hδ₂U := hδ₂a.2)
          simpa [val] using this
        | inr ub =>
            -- new-new: comparisons depend only on the nat levels since admissible δ's are positive.
            have huU : ua.1 ∈ U := ua.2
            have hδ₁u := hδ₁ ua.1 huU
            have hδ₂u := hδ₂ ua.1 huU
            have hδ₁_pos : 0 < δ₁ := delta_pos_of_mem (u := ua.1) huU hδ₁u.1 hδ₁u.2
            have hδ₂_pos : 0 < δ₂ := delta_pos_of_mem (u := ua.1) huU hδ₂u.1 hδ₂u.2
            have hcmp₁ :
                (ThetaRaw (R := R) (F := F) δ₁ r0 ua.1 <
                      ThetaRaw (R := R) (F := F) δ₁ r0 ub.1) ↔ ua.1 < ub.1 := by
              have hmul :
                  (ThetaRaw (R := R) (F := F) δ₁ r0 ua.1 <
                        ThetaRaw (R := R) (F := F) δ₁ r0 ub.1) ↔
                    ((ua.1 : ℝ) * δ₁ < (ub.1 : ℝ) * δ₁) := by
                simpa [ThetaRaw] using
                  (add_lt_add_iff_left (R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩))
              constructor
              · intro hlt
                have hmul_lt : (ua.1 : ℝ) * δ₁ < (ub.1 : ℝ) * δ₁ := (hmul.mp hlt)
                have hmul_lt' : δ₁ * (ua.1 : ℝ) < δ₁ * (ub.1 : ℝ) := by
                  simpa [mul_comm] using hmul_lt
                have hcast : (ua.1 : ℝ) < (ub.1 : ℝ) :=
                  (mul_lt_mul_iff_right₀ hδ₁_pos).1 hmul_lt'
                exact_mod_cast hcast
              · intro hlt
                have hcast : (ua.1 : ℝ) < (ub.1 : ℝ) := by exact_mod_cast hlt
                have hmul_lt' : δ₁ * (ua.1 : ℝ) < δ₁ * (ub.1 : ℝ) :=
                  (mul_lt_mul_iff_right₀ hδ₁_pos).2 hcast
                have hmul_lt : (ua.1 : ℝ) * δ₁ < (ub.1 : ℝ) * δ₁ := by
                  simpa [mul_comm] using hmul_lt'
                exact hmul.mpr hmul_lt
            have hcmp₂ :
                (ThetaRaw (R := R) (F := F) δ₂ r0 ua.1 <
                      ThetaRaw (R := R) (F := F) δ₂ r0 ub.1) ↔ ua.1 < ub.1 := by
              have hmul :
                  (ThetaRaw (R := R) (F := F) δ₂ r0 ua.1 <
                        ThetaRaw (R := R) (F := F) δ₂ r0 ub.1) ↔
                    ((ua.1 : ℝ) * δ₂ < (ub.1 : ℝ) * δ₂) := by
                simpa [ThetaRaw] using
                  (add_lt_add_iff_left (R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩))
              constructor
              · intro hlt
                have hmul_lt : (ua.1 : ℝ) * δ₂ < (ub.1 : ℝ) * δ₂ := (hmul.mp hlt)
                have hmul_lt' : δ₂ * (ua.1 : ℝ) < δ₂ * (ub.1 : ℝ) := by
                  simpa [mul_comm] using hmul_lt
                have hcast : (ua.1 : ℝ) < (ub.1 : ℝ) :=
                  (mul_lt_mul_iff_right₀ hδ₂_pos).1 hmul_lt'
                exact_mod_cast hcast
              · intro hlt
                have hcast : (ua.1 : ℝ) < (ub.1 : ℝ) := by exact_mod_cast hlt
                have hmul_lt' : δ₂ * (ua.1 : ℝ) < δ₂ * (ub.1 : ℝ) :=
                  (mul_lt_mul_iff_right₀ hδ₂_pos).2 hcast
                have hmul_lt : (ua.1 : ℝ) * δ₂ < (ub.1 : ℝ) * δ₂ := by
                  simpa [mul_comm] using hmul_lt'
                exact hmul.mpr hmul_lt
            simpa [val] using (hcmp₁.trans hcmp₂.symm)
lemma flip_implies_baseIndexed_B_witness
    {δ₁ δ₂ : ℝ} (hδ : δ₁ < δ₂)
    (hRealize :
      ∀ δ, δ₁ < δ → δ < δ₂ → RealizesThetaRaw (R := R) (F := F) (d := d) (hd := hd) δ)
    (r0 ry : Multi k) (u v : ℕ) (huv : v < u)
    (h1 : ThetaRaw (R := R) (F := F) δ₁ r0 u < ThetaRaw (R := R) (F := F) δ₁ ry v)
    (h2 : ThetaRaw (R := R) (F := F) δ₂ ry v < ThetaRaw (R := R) (F := F) δ₂ r0 u) :
    ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 (u - v) := by
  classical
  have hRealize_pair :
      ∀ δ, δ₁ < δ → δ < δ₂ →
        RealizesThetaRaw_pair (R := R) (F := F) (d := d) (hd := hd) δ r0 ry u v := by
    intro δ hδ₁ hδ₂
    exact realizesThetaRaw_pair_of_realizesThetaRaw (R := R) (F := F) (d := d) (hd := hd)
      (hRealize δ hδ₁ hδ₂) r0 ry u v
  exact
    flip_implies_baseIndexed_B_witness_pair (R := R) (F := F) (d := d)
      (hd := hd) hδ r0 ry u v huv hRealize_pair h1 h2

end BenV2

/-!
## Circularity made explicit (Ben-v2 vs `BEmptyStrictGapSpec`)

The hypercube/Ben-v2 “boundary collision” argument shows:

`(strictly monotone Θ' realizing ThetaRaw at δ)` ⇒ `BEmptyStrictGapSpec` at δ.

In the main Appendix-A development, the *forward* direction is what one uses to rule out
boundary equalities, but the *reverse* direction is exactly where the k→k+1 step gets stuck:
to build such a strictly monotone Θ' in the mixed-`t` cases, the strict gap spec is assumed.

This lemma does **not** resolve the circularity; it records the implication cleanly so that any
attempted proof can be checked against it.
-/

section Circularity

variable {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
variable (IH : GridBridge F) (H : GridComm F)
variable (d : α) (hd : ident < d) [KSSeparation α]

lemma bEmptyStrictGapSpec_of_realizesThetaRaw_chooseδ
    (hReal :
      RealizesThetaRaw (R := R) (F := F) (d := d) (hd := hd) (chooseδ hk R d hd)) :
    BEmptyStrictGapSpec hk R IH H d hd := by
  classical
  set δ : ℝ := chooseδ hk R d hd
  rcases hReal with ⟨Θ', hΘ'_strict, hΘ'_on_join⟩
  refine
    { A := ?_
      C := ?_ }
  · intro _hB_empty r_old_x r_old_y Δ hΔ hμ_gt hA_base _hB_base
    -- Compare the two extended μ-values: (r_old_x,0) and (r_old_y,Δ).
    have h_between :
        mu (extendAtomFamily F d hd) (joinMulti r_old_x 0) <
          mu (extendAtomFamily F d hd) (joinMulti r_old_y Δ) := by
      have hx0 :
          mu (extendAtomFamily F d hd) (joinMulti r_old_x 0) = mu F r_old_x := by
        simpa [iterate_op_zero, op_ident_right] using (mu_extend_last F d hd r_old_x 0)
      have hyΔ :
          mu (extendAtomFamily F d hd) (joinMulti r_old_y Δ) =
            op (mu F r_old_y) (iterate_op d Δ) := by
        simpa using (mu_extend_last F d hd r_old_y Δ)
      have : mu F r_old_x < op (mu F r_old_y) (iterate_op d Δ) := by
        simpa [extensionSetA_base, Set.mem_setOf_eq] using hA_base
      simpa [hx0, hyΔ] using this
    have hΘ_lt :
        Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_old_x 0),
              mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old_x 0)⟩ <
          Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_old_y Δ),
                mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old_y Δ)⟩ :=
      hΘ'_strict h_between
    -- Rewrite with ThetaRaw and divide by Δ.
    have hRaw_lt :
        ThetaRaw (R := R) (F := F) δ r_old_x 0 <
          ThetaRaw (R := R) (F := F) δ r_old_y Δ := by
      simpa [hΘ'_on_join] using hΘ_lt
    -- Unfold ThetaRaw and rearrange.
    have hΔ_pos_real : (0 : ℝ) < (Δ : ℝ) := Nat.cast_pos.mpr hΔ
    have :
        (R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
            R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩) / Δ < δ := by
      -- From: Θx < Θy + Δ*δ
      have : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ <
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ + (Δ : ℝ) * δ := by
        simpa [ThetaRaw] using hRaw_lt
      have : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ < (Δ : ℝ) * δ := by
        linarith
      -- Divide by Δ>0 (note `div_lt_iff₀` expects `… < δ * Δ`).
      have hgap' :
          R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ -
              R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ < δ * (Δ : ℝ) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      exact (div_lt_iff₀ hΔ_pos_real).2 hgap'
    simpa [separationStatistic_base, δ] using this
  · intro _hB_empty r_old_x r_old_y Δ hΔ hμ_lt hC_base _hB_base
    -- Compare the two extended μ-values: (r_old_x,Δ) and (r_old_y,0).
    have h_between :
        mu (extendAtomFamily F d hd) (joinMulti r_old_x Δ) <
          mu (extendAtomFamily F d hd) (joinMulti r_old_y 0) := by
      have hxΔ :
          mu (extendAtomFamily F d hd) (joinMulti r_old_x Δ) =
            op (mu F r_old_x) (iterate_op d Δ) := by
        simpa using (mu_extend_last F d hd r_old_x Δ)
      have hy0 :
          mu (extendAtomFamily F d hd) (joinMulti r_old_y 0) = mu F r_old_y := by
        simpa [iterate_op_zero, op_ident_right] using (mu_extend_last F d hd r_old_y 0)
      have : op (mu F r_old_x) (iterate_op d Δ) < mu F r_old_y := by
        simpa [extensionSetC_base, Set.mem_setOf_eq] using hC_base
      simpa [hxΔ, hy0] using this
    have hΘ_lt :
        Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_old_x Δ),
              mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old_x Δ)⟩ <
          Θ' ⟨mu (extendAtomFamily F d hd) (joinMulti r_old_y 0),
                mu_mem_kGrid (extendAtomFamily F d hd) (joinMulti r_old_y 0)⟩ :=
      hΘ'_strict h_between
    have hRaw_lt :
        ThetaRaw (R := R) (F := F) δ r_old_x Δ <
          ThetaRaw (R := R) (F := F) δ r_old_y 0 := by
      simpa [hΘ'_on_join] using hΘ_lt
    have hΔ_pos_real : (0 : ℝ) < (Δ : ℝ) := Nat.cast_pos.mpr hΔ
    have :
        δ < (R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
              R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩) / Δ := by
      -- From: Θx + Δ*δ < Θy
      have : R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ + (Δ : ℝ) * δ <
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ := by
        simpa [ThetaRaw] using hRaw_lt
      have : (Δ : ℝ) * δ <
          R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
            R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := by
        linarith
      -- Divide by Δ>0 and rearrange (note `lt_div_iff₀` expects `δ * Δ < …`).
      have hgap' :
          δ * (Δ : ℝ) <
            R.Θ_grid ⟨mu F r_old_y, mu_mem_kGrid F r_old_y⟩ -
              R.Θ_grid ⟨mu F r_old_x, mu_mem_kGrid F r_old_x⟩ := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      exact (lt_div_iff₀ hΔ_pos_real).2 hgap'
    simpa [separationStatistic_base, δ] using this

lemma realizesThetaRaw_chooseδ_of_chooseδBaseAdmissible
    (H : GridComm F) (hBase : ChooseδBaseAdmissible (α := α) hk R d hd) :
    RealizesThetaRaw (R := R) (F := F) (d := d) (hd := hd) (chooseδ hk R d hd) := by
  classical
  rcases
      extend_grid_rep_with_atom_of_gridComm (α := α) (hk := hk) (R := R) (H := H) (d := d) (hd := hd)
        (hBase := hBase) with
    ⟨F', hF'_old, hF'_new, R', hExt⟩
  have hF' : F' = extendAtomFamily F d hd :=
    AtomFamily.eq_extendAtomFamily_of_old_new (F := F) (d := d) (hd := hd) F' hF'_old hF'_new
  cases hF'
  refine ⟨R'.Θ_grid, R'.strictMono, ?_⟩
  intro r_old t
  -- `ThetaRaw` is exactly the `Θ`-extension formula produced by `extend_grid_rep_with_atom`.
  simpa [ThetaRaw] using (hExt r_old t)

end Circularity

/-!
## A “strong-but-clean” interface that would discharge `BEmptyStrictGapSpec`

`BEmptyStrictGapSpec` asks for **strict** base-indexed A/C inequalities at the specific choice
`δ := chooseδ hk R d hd` in the globally `B = ∅` regime (K&S Appendix A.3.4).

A conceptually simpler sufficient condition is that this same `δ` is *already* admissible for **all**
base-indexed comparisons at every base `r0` and level `u>0`:

`AdmissibleDelta_base R d δ r0 u`.

This is stronger than what Appendix A needs, but it cleanly isolates the missing ingredient:
if one can prove `ChooseδBaseAdmissible` from the current `Core/` development, then the strict-gap
blocker disappears immediately.

This “base invariance / diagonal crosses all relevant intervals” claim is exactly the informal move
in K&S A.3.4 where, for a fixed base `r0` and target level `u`, they assert that the *global* choice
`δ` (picked from the full A/C families over all levels) may be used as the representative slope for
the **single‑u** “relevant constraints” interval. See:
- `claude/literature/Knuth_Skilling/Knuth_Skilling_Foundations_of_Inference/knuth-skilling-2012---foundations-of-inference----arxiv.tex`
  (A.3.4, around eqs. (fixdelta)–(fixm), especially the step “Accordingly, it is legitimate to assign … = δ”).
- `claude/literature/Foundations-of-inference-new-proofs_v2.pdf` (Lemma 6 framing of the base‑indexed gap).
-/

/-!
## NewAtomCommutes: The Weakest Assumption for B-Empty Extension

The B-empty extension step requires decomposing `(μ(F,r0) ⊕ d^u)^m` into `μ(F,r0)^m ⊕ d^{um}`.
This requires commutativity between the new atom `d` and existing grid elements.

The **weakest sufficient assumption** is that `d` commutes with all atoms in `F`. This implies
`d` commutes with all grid elements (since they are built from atoms via `op`).
Equivalently, one may assume `NewAtomCommutesGrid F d`; see `newAtomCommutes_iff_newAtomCommutesGrid`.

This assumption is strictly weaker than global commutativity of `α`. It only constrains the
relationship between the new atom and the existing grid.
For convenience, the A-side scaling argument is phrased below as the “shifted-boundary
power decomposition” law `NewAtomDecompose`.  Despite looking narrower, it already forces
commutation (it implies `NewAtomCommutes` by specializing to `u=1, m=2`), so it is equivalent in
strength; see `newAtomCommutes_of_newAtomDecompose` and `newAtomDecompose_of_newAtomCommutes`.
-/

/-- The new atom `d` commutes with all atoms in the current family `F`.
This is the weakest assumption needed for the B-empty extension step. -/
def NewAtomCommutes {k : ℕ} (F : AtomFamily α k) (d : α) : Prop :=
  ∀ i : Fin k, op (F.atoms i) d = op d (F.atoms i)

/-- If `op` is globally commutative, then any candidate `d` satisfies `NewAtomCommutes F d`. -/
lemma newAtomCommutes_of_op_comm {k : ℕ} {F : AtomFamily α k} {d : α}
    (hcomm : ∀ x y : α, op x y = op y x) :
    NewAtomCommutes F d := by
  intro i
  simpa [NewAtomCommutes] using hcomm (F.atoms i) d

/-- Equivalent formulation of `NewAtomCommutes`: `d` commutes with every old-grid element `μ(F,r)`. -/
def NewAtomCommutesGrid {k : ℕ} (F : AtomFamily α k) (d : α) : Prop :=
  ∀ r : Multi k, op (mu F r) d = op d (mu F r)

/-- If the whole `(k+1)`-grid is commutative after adjoining `d`, then `d` commutes with the old
atoms (hence the B-empty decomposition step is available). -/
lemma newAtomCommutes_of_gridComm_extendAtomFamily {k : ℕ} {F : AtomFamily α k} {d : α}
    (hd : ident < d) (H' : GridComm (extendAtomFamily F d hd)) :
    NewAtomCommutes F d := by
  intro i
  classical
  let i' : Fin (k + 1) := ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
  let last : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  have hcomm := H'.comm (unitMulti i' 1) (unitMulti last 1)
  have hμi : mu (extendAtomFamily F d hd) (unitMulti i' 1) = (extendAtomFamily F d hd).atoms i' := by
    simpa [KnuthSkillingAlgebra.iterate_op_one] using (mu_unitMulti (extendAtomFamily F d hd) i' 1)
  have hμlast :
      mu (extendAtomFamily F d hd) (unitMulti last 1) =
        (extendAtomFamily F d hd).atoms last := by
    simpa [KnuthSkillingAlgebra.iterate_op_one] using (mu_unitMulti (extendAtomFamily F d hd) last 1)
  have hi : (extendAtomFamily F d hd).atoms i' = F.atoms i := by
    simpa [i'] using (extendAtomFamily_old (F := F) (d := d) (hd := hd) i)
  have hlast : (extendAtomFamily F d hd).atoms last = d := by
    simpa [last] using (extendAtomFamily_new (F := F) (d := d) (hd := hd))
  simpa [NewAtomCommutes, hμi, hμlast, hi, hlast] using hcomm

/-- If `d` is already on the old grid and the old grid is commutative, then `d` commutes with all
old atoms (a degenerate “extension”). -/
lemma newAtomCommutes_of_mem_kGrid {k : ℕ} {F : AtomFamily α k} (H : GridComm F) {d : α}
    (hd : d ∈ kGrid F) : NewAtomCommutes F d := by
  rcases hd with ⟨r_d, rfl⟩
  intro i
  have hcomm := H.comm (unitMulti i 1) r_d
  have hμi : mu F (unitMulti i 1) = F.atoms i := by
    simpa [KnuthSkillingAlgebra.iterate_op_one] using (mu_unitMulti F i 1)
  simpa [NewAtomCommutes, hμi] using hcomm

/-!
### Sanity check: “NewAtomCommutes for all singletons” is global commutativity

For a *fixed* family `F` and candidate new atom `d`, `NewAtomCommutes F d` is much weaker than
global commutativity of `α`.

However, if one could prove `NewAtomCommutes` **uniformly** for every singleton family
`{x}` and every `d`, then `op` would be commutative on all of `α`.  This makes the remaining
“emptiness” question very explicit:

> Does `[KSSeparation α]` imply `NewAtomCommutes (singletonAtomFamily x hx) d` for all `x>ident`?

Equivalently: does `KSSeparation` rule out any noncommutative `KnuthSkillingAlgebra`?
-/

theorem newAtomCommutes_singleton_of_op_comm (hcomm : ∀ x y : α, op x y = op y x)
    (x : α) (hx : ident < x) (d : α) :
    NewAtomCommutes (singletonAtomFamily (α := α) x hx) d := by
  intro i
  simpa [NewAtomCommutes, singletonAtomFamily] using hcomm x d

theorem op_comm_of_newAtomCommutes_singleton
    (h :
      ∀ (x : α) (hx : ident < x) (d : α),
        NewAtomCommutes (singletonAtomFamily (α := α) x hx) d) :
    ∀ x y : α, op x y = op y x := by
  classical
  intro x y
  by_cases hx0 : x = ident
  · subst hx0
    simpa [op_ident_left, op_ident_right]
  by_cases hy0 : y = ident
  · subst hy0
    simpa [op_ident_left, op_ident_right]
  have hx : ident < x := lt_of_le_of_ne (ident_le x) (Ne.symm hx0)
  have hxy : NewAtomCommutes (singletonAtomFamily (α := α) x hx) y := h x hx y
  have hi := hxy ⟨0, by decide⟩
  simpa [NewAtomCommutes, singletonAtomFamily] using hi

theorem op_comm_iff_newAtomCommutes_singleton :
    (∀ x y : α, op x y = op y x) ↔
      (∀ (x : α) (hx : ident < x) (d : α),
        NewAtomCommutes (singletonAtomFamily (α := α) x hx) d) := by
  constructor
  · intro hcomm x hx d
    exact newAtomCommutes_singleton_of_op_comm (α := α) hcomm x hx d
  · intro h
    exact op_comm_of_newAtomCommutes_singleton (α := α) h

/-- If the extended `(k+1)`-grid is commutative, then the original `k`-grid is commutative. -/
lemma gridComm_of_gridComm_extendAtomFamily {k : ℕ} {F : AtomFamily α k} {d : α}
    (hd : ident < d) (H' : GridComm (extendAtomFamily F d hd)) : GridComm F := by
  refine ⟨?_⟩
  intro r s
  -- Compare `joinMulti r 0` and `joinMulti s 0` in the extended grid.
  have hcomm' := H'.comm (joinMulti r 0) (joinMulti s 0)
  -- `μ` on the extended family reduces to the old `μ` when the new coordinate is `0`.
  have hμr : mu (extendAtomFamily F d hd) (joinMulti r 0) = mu F r := by
    simpa [KnuthSkillingAlgebra.iterate_op_zero, op_ident_right] using
      (mu_extend_last (F := F) (d := d) (hd := hd) r 0)
  have hμs : mu (extendAtomFamily F d hd) (joinMulti s 0) = mu F s := by
    simpa [KnuthSkillingAlgebra.iterate_op_zero, op_ident_right] using
      (mu_extend_last (F := F) (d := d) (hd := hd) s 0)
  simpa [hμr, hμs] using hcomm'

/-- If d commutes with all atoms, then d commutes with iterate_op of any atom. -/
lemma d_comm_iterate_atom {k : ℕ} {F : AtomFamily α k} {d : α}
    (hcomm : NewAtomCommutes F d) (i : Fin k) (n : ℕ) :
    op (iterate_op (F.atoms i) n) d = op d (iterate_op (F.atoms i) n) := by
  induction n with
  | zero => simp [iterate_op_zero, op_ident_left, op_ident_right]
  | succ n ih =>
    calc op (iterate_op (F.atoms i) (n + 1)) d
        = op (op (F.atoms i) (iterate_op (F.atoms i) n)) d := by rfl
      _ = op (F.atoms i) (op (iterate_op (F.atoms i) n) d) := by rw [op_assoc]
      _ = op (F.atoms i) (op d (iterate_op (F.atoms i) n)) := by rw [ih]
      _ = op (op (F.atoms i) d) (iterate_op (F.atoms i) n) := by rw [← op_assoc]
      _ = op (op d (F.atoms i)) (iterate_op (F.atoms i) n) := by rw [hcomm i]
      _ = op d (op (F.atoms i) (iterate_op (F.atoms i) n)) := by rw [op_assoc]
      _ = op d (iterate_op (F.atoms i) (n + 1)) := by rfl

/-- If d commutes with all atoms, then d^m commutes with all atoms. -/
lemma iterate_d_comm_atom {k : ℕ} {F : AtomFamily α k} {d : α}
    (hcomm : NewAtomCommutes F d) (i : Fin k) (m : ℕ) :
    op (F.atoms i) (iterate_op d m) = op (iterate_op d m) (F.atoms i) := by
  induction m with
  | zero => simp [iterate_op_zero, op_ident_left, op_ident_right]
  | succ m ih =>
    calc op (F.atoms i) (iterate_op d (m + 1))
        = op (F.atoms i) (op d (iterate_op d m)) := by rfl
      _ = op (op (F.atoms i) d) (iterate_op d m) := by rw [← op_assoc]
      _ = op (op d (F.atoms i)) (iterate_op d m) := by rw [hcomm i]
      _ = op d (op (F.atoms i) (iterate_op d m)) := by rw [op_assoc]
      _ = op d (op (iterate_op d m) (F.atoms i)) := by rw [ih]
      _ = op (op d (iterate_op d m)) (F.atoms i) := by rw [← op_assoc]
      _ = op (iterate_op d (m + 1)) (F.atoms i) := by rfl

/-- If d commutes with all atoms, then a^n commutes with d^m. -/
lemma iterate_atom_comm_iterate_d {k : ℕ} {F : AtomFamily α k} {d : α}
    (hcomm : NewAtomCommutes F d) (i : Fin k) (n m : ℕ) :
    op (iterate_op (F.atoms i) n) (iterate_op d m) =
    op (iterate_op d m) (iterate_op (F.atoms i) n) := by
  induction n with
  | zero => simp [iterate_op_zero, op_ident_left, op_ident_right]
  | succ n ihn =>
    calc op (iterate_op (F.atoms i) (n + 1)) (iterate_op d m)
        = op (op (F.atoms i) (iterate_op (F.atoms i) n)) (iterate_op d m) := by rfl
      _ = op (F.atoms i) (op (iterate_op (F.atoms i) n) (iterate_op d m)) := by rw [op_assoc]
      _ = op (F.atoms i) (op (iterate_op d m) (iterate_op (F.atoms i) n)) := by rw [ihn]
      _ = op (op (F.atoms i) (iterate_op d m)) (iterate_op (F.atoms i) n) := by rw [← op_assoc]
      _ = op (op (iterate_op d m) (F.atoms i)) (iterate_op (F.atoms i) n) := by
          rw [iterate_d_comm_atom hcomm i m]
      _ = op (iterate_op d m) (op (F.atoms i) (iterate_op (F.atoms i) n)) := by rw [op_assoc]
      _ = op (iterate_op d m) (iterate_op (F.atoms i) (n + 1)) := by rfl

/-- If d commutes with all atoms in F, then d^m commutes with all grid elements μ(F,r).

The key insight: μ(F,r) = a_0^{r_0} ⊕ a_1^{r_1} ⊕ ... ⊕ a_{k-1}^{r_{k-1}}
Each a_i^{r_i} commutes with d^m by iterate_d_comm_atom, and products of
commuting elements commute with d^m. -/
lemma iterate_d_comm_mu {k : ℕ} {F : AtomFamily α k} {d : α}
    (hcomm : NewAtomCommutes F d) (r : Multi k) (m : ℕ) :
    op (mu F r) (iterate_op d m) = op (iterate_op d m) (mu F r) := by
  -- We prove a stronger statement: for any list of indices,
  -- the foldl of atom powers commutes with d^m
  unfold mu
  -- Induction on the list structure
  have h_list : ∀ (L : List (Fin k)) (acc : α),
      (∀ i ∈ L, op (iterate_op (F.atoms i) (r i)) (iterate_op d m) =
                op (iterate_op d m) (iterate_op (F.atoms i) (r i))) →
      op acc (iterate_op d m) = op (iterate_op d m) acc →
      op (List.foldl (fun acc i => op acc (iterate_op (F.atoms i) (r i))) acc L)
         (iterate_op d m) =
      op (iterate_op d m)
         (List.foldl (fun acc i => op acc (iterate_op (F.atoms i) (r i))) acc L) := by
    intro L
    induction L with
    | nil =>
      intro acc _ hacc
      simp only [List.foldl_nil]
      exact hacc
    | cons i rest ih =>
      intro acc hcomm_list hacc
      simp only [List.foldl_cons]
      apply ih
      · intro j hj
        exact hcomm_list j (List.mem_cons_of_mem i hj)
      · -- Show op (op acc (iterate_op (F.atoms i) (r i))) (iterate_op d m) = ...
        have h1 : op (iterate_op (F.atoms i) (r i)) (iterate_op d m) =
                  op (iterate_op d m) (iterate_op (F.atoms i) (r i)) :=
          hcomm_list i (List.mem_cons.mpr (Or.inl rfl))
        calc op (op acc (iterate_op (F.atoms i) (r i))) (iterate_op d m)
            = op acc (op (iterate_op (F.atoms i) (r i)) (iterate_op d m)) := by rw [op_assoc]
          _ = op acc (op (iterate_op d m) (iterate_op (F.atoms i) (r i))) := by rw [h1]
          _ = op (op acc (iterate_op d m)) (iterate_op (F.atoms i) (r i)) := by rw [← op_assoc]
          _ = op (op (iterate_op d m) acc) (iterate_op (F.atoms i) (r i)) := by rw [hacc]
          _ = op (iterate_op d m) (op acc (iterate_op (F.atoms i) (r i))) := by rw [op_assoc]
  apply h_list
  · -- All atoms commute with d^m
    intro i _
    exact iterate_atom_comm_iterate_d hcomm i (r i) m
  · -- ident commutes with everything
    simp [op_ident_left, op_ident_right]

lemma newAtomCommutesGrid_of_newAtomCommutes {k : ℕ} {F : AtomFamily α k} {d : α}
    (hcomm : NewAtomCommutes F d) : NewAtomCommutesGrid F d := by
  intro r
  have := iterate_d_comm_mu (F := F) (d := d) hcomm r 1
  simpa [NewAtomCommutesGrid, KnuthSkillingAlgebra.iterate_op_one] using this

lemma newAtomCommutes_of_newAtomCommutesGrid {k : ℕ} {F : AtomFamily α k} {d : α}
    (hcomm : NewAtomCommutesGrid F d) : NewAtomCommutes F d := by
  intro i
  have h := hcomm (unitMulti i 1)
  -- `μ(F, unitMulti i 1) = a_i`
  have hμ : mu F (unitMulti i 1) = F.atoms i := by
    simpa [KnuthSkillingAlgebra.iterate_op_one] using (mu_unitMulti F i 1)
  simpa [NewAtomCommutesGrid, hμ] using h

theorem newAtomCommutes_iff_newAtomCommutesGrid {k : ℕ} {F : AtomFamily α k} {d : α} :
    NewAtomCommutes F d ↔ NewAtomCommutesGrid F d := by
  constructor
  · intro h
    exact newAtomCommutesGrid_of_newAtomCommutes (F := F) (d := d) h
  · intro h
    exact newAtomCommutes_of_newAtomCommutesGrid (F := F) (d := d) h

/-- If the old `k`-grid is commutative and the new atom commutes with the old grid, then the
extended `(k+1)`-grid is commutative. -/
lemma gridComm_extendAtomFamily_of_gridComm_of_newAtomCommutesGrid {k : ℕ} {F : AtomFamily α k}
    (H : GridComm F) {d : α} (hd : ident < d) (hcomm : NewAtomCommutesGrid F d) :
    GridComm (extendAtomFamily F d hd) := by
  classical
  let F' := extendAtomFamily F d hd
  refine ⟨?_⟩
  intro r s
  -- Split multiplicities into old/new parts and use `mu_extend_last` to normalize.
  rcases hsr : splitMulti r with ⟨r_old, r_new⟩
  rcases hss : splitMulti s with ⟨s_old, s_new⟩
  have hr : joinMulti r_old r_new = r := by
    simpa [hsr] using (joinMulti_splitMulti (r := r))
  have hs : joinMulti s_old s_new = s := by
    simpa [hss] using (joinMulti_splitMulti (r := s))
  have hμr :
      mu F' r = op (mu F r_old) (iterate_op d r_new) := by
    -- `mu_extend_last` expects `joinMulti`; rewrite `r` into that form.
    simpa [F', hr] using (mu_extend_last (F := F) (d := d) (hd := hd) r_old r_new)
  have hμs :
      mu F' s = op (mu F s_old) (iterate_op d s_new) := by
    simpa [F', hs] using (mu_extend_last (F := F) (d := d) (hd := hd) s_old s_new)

  -- Notation for readability.
  set A : α := mu F r_old
  set B : α := iterate_op d r_new
  set C : α := mu F s_old
  set D : α := iterate_op d s_new

  -- Pairwise commutations we need.
  have hAC : op A C = op C A := by simpa [A, C] using H.comm r_old s_old
  have hBC : op B C = op C B := by
    -- `d` commutes with every old-grid element, hence so does `d^r_new`.
    have hCB : op C B = op B C := by
      -- `iterate_d_comm_mu` gives `mu` ⋆ `d^m` commutation in the opposite order.
      simpa [A, B, C] using (iterate_d_comm_mu (F := F) (d := d)
        (newAtomCommutes_of_newAtomCommutesGrid (F := F) (d := d) hcomm) s_old r_new)
    exact hCB.symm
  have hAD : op A D = op D A := by
    simpa [A, D] using (iterate_d_comm_mu (F := F) (d := d)
      (newAtomCommutes_of_newAtomCommutesGrid (F := F) (d := d) hcomm) r_old s_new)
  have hBD : op B D = op D B := by
    -- Powers of a single element commute.
    -- `B ⊕ D = d^(r_new+s_new) = D ⊕ B`.
    have h1 : op B D = iterate_op d (r_new + s_new) := by
      simpa [B, D] using (iterate_op_add (a := d) (m := r_new) (n := s_new))
    have h2 : op D B = iterate_op d (s_new + r_new) := by
      simpa [B, D] using (iterate_op_add (a := d) (m := s_new) (n := r_new))
    calc
      op B D = iterate_op d (r_new + s_new) := h1
      _ = iterate_op d (s_new + r_new) := by simpa [Nat.add_comm]
      _ = op D B := h2.symm

  -- Now show `(A ⊕ B) ⊕ (C ⊕ D) = (C ⊕ D) ⊕ (A ⊕ B)`.
  -- First normalize both sides via associativity.
  calc
    op (mu F' r) (mu F' s)
        = op (op A B) (op C D) := by
            simpa [hμr, hμs, A, B, C, D]
    _ = op A (op B (op C D)) := by rw [op_assoc]
    _ = op A (op C (op B D)) := by
          -- rewrite `B ⊕ (C ⊕ D)` to `C ⊕ (B ⊕ D)` using `B` commuting with `C`
          have h_swap : op B (op C D) = op C (op B D) := by
            calc
              op B (op C D) = op (op B C) D := by
                simpa using (op_assoc B C D).symm
              _ = op (op C B) D := by simpa [hBC]
              _ = op C (op B D) := by
                simpa using (op_assoc C B D)
          simpa using congrArg (fun t => op A t) h_swap
    _ = op (op A C) (op B D) := by rw [← op_assoc]
    _ = op (op C A) (op D B) := by simpa [hAC, hBD]
    _ = op C (op A (op D B)) := by rw [op_assoc]
    _ = op C (op D (op A B)) := by
          have h_inner : op A (op D B) = op D (op A B) := by
            calc
              op A (op D B) = op (op A D) B := by
                simpa using (op_assoc A D B).symm
              _ = op (op D A) B := by simpa [hAD]
              _ = op D (op A B) := by
                simpa using (op_assoc D A B)
          simpa [h_inner]
    _ = op (op C D) (op A B) := by rw [← op_assoc]
    _ = op (mu F' s) (mu F' r) := by
          simpa [hμr, hμs, A, B, C, D]

/-- `GridComm (extendAtomFamily F d hd)` is equivalent to “old grid commutative + new atom commutes
with the old atoms”. -/
theorem gridComm_extendAtomFamily_iff {k : ℕ} {F : AtomFamily α k} {d : α} (hd : ident < d) :
    GridComm (extendAtomFamily F d hd) ↔ (GridComm F ∧ NewAtomCommutes F d) := by
  constructor
  · intro H'
    refine ⟨gridComm_of_gridComm_extendAtomFamily (F := F) (d := d) hd H', ?_⟩
    exact newAtomCommutes_of_gridComm_extendAtomFamily (F := F) (d := d) (hd := hd) H'
  · rintro ⟨H, hcomm⟩
    have hcommGrid : NewAtomCommutesGrid F d :=
      newAtomCommutesGrid_of_newAtomCommutes (F := F) (d := d) hcomm
    exact gridComm_extendAtomFamily_of_gridComm_of_newAtomCommutesGrid (F := F) (d := d)
      H hd hcommGrid

/-!
## `AppendixA34Extra`: Two explicit hypotheses that complete the B-empty step

In the current `Core/` development, the remaining Appendix A.3.4 gap can be isolated to:
- **Commutation with the new atom**: `NewAtomCommutes F d`, needed to rewrite powers of the shifted
  boundary `(μ(F,r0) ⊕ d^u)^m`.
- **C-side inaccessibility**: no absolute C-statistic hits the cut value `δ := chooseδ hk R d hd`.

This structure packages exactly these two assumptions, so downstream theorems can state cleanly
which extra “vertex” of the assumptions-hypercube they inhabit.

Notes:
- `NewAtomCommutes` is not derivable from the base `KnuthSkillingAlgebra` axioms; see
  `Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA/Counterexamples/NewAtomCommutesNotDerivable.lean`.
- `C_strict0` is also not derivable from the “B-empty accuracy” core alone: there is a concrete
  `KnuthSkillingAlgebra` model where `chooseδ` is attained as a C-statistic; see
  `Mettapedia/ProbabilityTheory/KnuthSkilling/AppendixA/Counterexamples/CStrict0Fails.lean`.
- However, `C_strict0` *is* implied by the strict separation strengthening `KSSeparationStrict`;
  see `chooseδ_C_strict0_of_KSSeparationStrict`.
-/

structure AppendixA34Extra {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (d : α) (hd : ident < d) : Prop where
  /-- The new atom commutes with the existing atom family. -/
  newAtomCommutes : NewAtomCommutes F d
  /-- C-side strictness at base `0`: no absolute C-statistic equals `δ := chooseδ …`. -/
  C_strict0 :
    ∀ (r : Multi k) (u : ℕ) (hu : 0 < u),
      r ∈ extensionSetC F d u → chooseδ hk R d hd < separationStatistic R r u hu

/-- `AppendixA34Extra.C_strict0` follows from the strict separation strengthening
`KSSeparationStrict` (it provides a strictly smaller C-statistic below any given C-statistic). -/
theorem chooseδ_C_strict0_of_KSSeparationStrict
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparationStrict α] :
    ∀ (r : Multi k) (u : ℕ) (hu : 0 < u),
      r ∈ extensionSetC F d u → chooseδ hk R d hd < separationStatistic R r u hu := by
  classical
  intro r u hu hrC
  -- If B is nonempty, `chooseδ` is the B-statistic and strictness is immediate.
  by_cases hB : ∃ rB uB, 0 < uB ∧ rB ∈ extensionSetB F d uB
  · rcases hB with ⟨rB, uB, huB, hrB⟩
    have hB_nonempty : ∃ r u, 0 < u ∧ r ∈ extensionSetB F d u := ⟨rB, uB, huB, hrB⟩
    have hδ_eq :
        chooseδ hk R d hd = separationStatistic R rB uB huB := by
      unfold chooseδ
      simp [hB_nonempty,
        B_common_statistic_eq_any_witness (R := R) (IH := IH) (d := d) (hd := hd)
          (hB_nonempty := hB_nonempty) (r := rB) (u := uB) (hu := huB) hrB]
    -- In the B≠∅ regime, the B-statistic is strictly below any C-statistic.
    simpa [hδ_eq] using (separation_property_B_C (R := R) (H := H) (hd := hd)
      (huB := huB) (hrB := hrB) (huC := hu) (hrC := hrC))
  ·
    -- In the B-empty branch, use strict separation to manufacture a strictly smaller C-statistic
    -- below `separationStatistic R r u` and then squeeze `chooseδ` below it.
    -- First get a concrete old atom `a`.
    have hk_pos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
    let i₀ : Fin k := ⟨0, hk_pos⟩
    let a : α := F.atoms i₀
    have ha : ident < a := F.pos i₀

    have hx : ident < iterate_op d u := iterate_op_pos d hd u hu
    have hxy : iterate_op d u < mu F r := by
      simpa [extensionSetC, Set.mem_setOf_eq] using hrC
    have hy : ident < mu F r := lt_trans hx hxy

    -- Strict separation: find an a-power strictly between (d^u)^m and (μ r)^m.
    obtain ⟨n, m, hm_pos, h_gap, h_in_y⟩ :=
      KSSeparationStrict.separation_strict (a := a) (x := iterate_op d u) (y := mu F r) ha hx hy hxy
    have huM_pos : 0 < u * m := Nat.mul_pos hu hm_pos

    -- Interpret the separator as a C-witness at level `u*m` on the old grid.
    have hrC' : unitMulti i₀ n ∈ extensionSetC F d (u * m) := by
      have hμ_right : mu F (unitMulti i₀ n) = iterate_op a n := by
        simpa [a] using (mu_unitMulti F i₀ n)
      have hleft : iterate_op d (u * m) < iterate_op a n := by
        -- (d^u)^m < a^n  ⇒  d^(u*m) < a^n
        simpa [iterate_op_mul] using h_gap
      simpa [extensionSetC, Set.mem_setOf_eq, hμ_right] using hleft

    -- `δ ≤ stat(r',u*m)` by the general C-bound.
    have hδ_le :
        chooseδ hk R d hd ≤ separationStatistic R (unitMulti i₀ n) (u * m) huM_pos :=
      chooseδ_C_bound hk R IH H d hd (unitMulti i₀ n) (u * m) huM_pos hrC'

    -- And `stat(r',u*m) < stat(r,u)` by strict monotonicity on the grid.
    have hstat_lt :
        separationStatistic R (unitMulti i₀ n) (u * m) huM_pos < separationStatistic R r u hu := by
      have hμ_left : mu F (unitMulti i₀ n) = iterate_op a n := by
        simpa [a] using (mu_unitMulti F i₀ n)
      have hμ_right : mu F (scaleMult m r) = iterate_op (mu F r) m := IH.bridge r m
      have hμ_grid_lt : mu F (unitMulti i₀ n) < mu F (scaleMult m r) := by
        -- a^n < (μ r)^m
        simpa [hμ_left, hμ_right] using h_in_y
      have hθ_grid_lt :
          R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ <
            R.Θ_grid ⟨mu F (scaleMult m r), mu_mem_kGrid F (scaleMult m r)⟩ :=
        R.strictMono hμ_grid_lt
      have hθ_scale :
          R.Θ_grid ⟨mu F (scaleMult m r), mu_mem_kGrid F (scaleMult m r)⟩ =
            m * R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ :=
        Theta_scaleMult (R := R) (r := r) m
      have hθ_lt :
          R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ <
            (m : ℝ) * R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := by
        simpa [hθ_scale] using hθ_grid_lt
      have huM_real : 0 < ((u * m : ℕ) : ℝ) := Nat.cast_pos.mpr huM_pos
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm_pos)
      have hu_real : 0 < (u : ℝ) := Nat.cast_pos.mpr hu
      have hdiv :
          R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ / ((u * m : ℕ) : ℝ) <
            ((m : ℝ) * R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩) / ((u * m : ℕ) : ℝ) :=
        (div_lt_div_of_pos_right hθ_lt huM_real)
      have hcancel :
          ((m : ℝ) * R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩) / ((u * m : ℕ) : ℝ) =
            R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / (u : ℝ) := by
        -- Cancel `m` after rewriting the denominator as `(u : ℝ) * (m : ℝ)`.
        calc
          ((m : ℝ) * R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩) / ((u * m : ℕ) : ℝ)
              = (R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ * (m : ℝ)) / ((u : ℝ) * (m : ℝ)) := by
                  simp [Nat.cast_mul, mul_comm]
          _ = R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / (u : ℝ) := by
                  simp [mul_div_mul_right, hm0]
      -- Wrap up.
      simpa [separationStatistic, Nat.cast_mul, hcancel] using (hdiv.trans_eq hcancel)

    exact lt_of_le_of_lt hδ_le hstat_lt

/-- `chooseδ_C_strict0_of_KSSeparationStrict`, but deriving strict separation from `KSSeparation`
in a dense order. -/
theorem chooseδ_C_strict0_of_KSSeparation_of_denselyOrdered
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparation α] [DenselyOrdered α] :
    ∀ (r : Multi k) (u : ℕ) (hu : 0 < u),
      r ∈ extensionSetC F d u → chooseδ hk R d hd < separationStatistic R r u hu := by
  letI : KSSeparationStrict α :=
    KSSeparation.toKSSeparationStrict_of_denselyOrdered (α := α)
  simpa using
    (chooseδ_C_strict0_of_KSSeparationStrict (α := α) (hk := hk) (R := R) (IH := IH) (H := H)
      (d := d) (hd := hd))

/-- Build `AppendixA34Extra` from `NewAtomCommutes` and the strict separation strengthening.

This is a convenience: the only additional field `C_strict0` is discharged by
`chooseδ_C_strict0_of_KSSeparationStrict`. -/
theorem appendixA34Extra_of_newAtomCommutes_of_KSSeparationStrict
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparationStrict α] (hcomm : NewAtomCommutes F d) :
    AppendixA34Extra (α := α) hk (R := R) (F := F) d hd :=
  ⟨hcomm, chooseδ_C_strict0_of_KSSeparationStrict (α := α) (hk := hk) (R := R)
    (IH := IH) (H := H) (d := d) (hd := hd)⟩

/-- Build `AppendixA34Extra` from `NewAtomCommutes`, using dense-order separation so we don't
assume `KSSeparationStrict` explicitly. -/
theorem appendixA34Extra_of_newAtomCommutes_of_KSSeparation_of_denselyOrdered
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparation α] [DenselyOrdered α] (hcomm : NewAtomCommutes F d) :
    AppendixA34Extra (α := α) hk (R := R) (F := F) d hd := by
  letI : KSSeparationStrict α :=
    KSSeparation.toKSSeparationStrict_of_denselyOrdered (α := α)
  exact
    appendixA34Extra_of_newAtomCommutes_of_KSSeparationStrict (α := α) (hk := hk) (R := R)
      (IH := IH) (H := H) (d := d) (hd := hd) hcomm

/-- The key decomposition: with NewAtomCommutes, we can decompose (μ(F,r) ⊕ d^u)^m. -/
lemma iterate_op_mu_d_decompose {k : ℕ} {F : AtomFamily α k}
    {d : α} (hcomm : NewAtomCommutes F d)
    (r : Multi k) (u m : ℕ) :
    iterate_op (op (mu F r) (iterate_op d u)) m =
    op (iterate_op (mu F r) m) (iterate_op d (u * m)) := by
  have h_comm : op (mu F r) (iterate_op d u) = op (iterate_op d u) (mu F r) :=
    iterate_d_comm_mu hcomm r u
  rw [iterate_op_op_of_comm h_comm]
  congr 1
  -- Show iterate_op (iterate_op d u) m = iterate_op d (u * m)
  exact iterate_op_mul d u m

/-- Minimal form of the “shifted-boundary power decomposition” needed for the base-indexed
scaling argument in A.3.4.

This identity is what the hard A-side proofs use.  It is equivalent to `NewAtomCommutes F d`
(specialize to `u=1, m=2` and cancel), but it is often more convenient to assume exactly the
shape needed for the scaling lemmas. -/
def NewAtomDecompose {k : ℕ} (F : AtomFamily α k) (d : α) : Prop :=
  ∀ (r : Multi k) (u m : ℕ),
    iterate_op (op (mu F r) (iterate_op d u)) m =
      op (iterate_op (mu F r) m) (iterate_op d (u * m))

lemma newAtomDecompose_of_newAtomCommutes {k : ℕ} {F : AtomFamily α k} {d : α}
    (hcomm : NewAtomCommutes F d) :
    NewAtomDecompose (F := F) d := by
  intro r u m
  simpa using (iterate_op_mu_d_decompose (F := F) (d := d) hcomm r u m)

private lemma op_comm_of_iter2_decompose {α : Type*} [KnuthSkillingAlgebra α] (a d : α)
    (h : iterate_op (op a d) 2 = op (iterate_op a 2) (iterate_op d 2)) :
    op a d = op d a := by
  -- Expand the `2`-fold iterates and cancel using strict monotonicity.
  have h0 : op (op a d) (op a d) = op (op a a) (op d d) := by
    simpa [KnuthSkillingAlgebra.iterate_op, op_ident_right] using h
  have h1 : op a (op d (op a d)) = op a (op a (op d d)) := by
    calc
      op a (op d (op a d)) = op (op a d) (op a d) := by
        simpa using (op_assoc a d (op a d)).symm
      _ = op (op a a) (op d d) := h0
      _ = op a (op a (op d d)) := by
        simpa using (op_assoc a a (op d d))
  have h2 : op d (op a d) = op a (op d d) := (op_strictMono_right a).injective h1
  have h3 : op (op d a) d = op (op a d) d := by
    calc
      op (op d a) d = op d (op a d) := by simpa using (op_assoc d a d)
      _ = op a (op d d) := h2
      _ = op (op a d) d := by simpa using (op_assoc a d d).symm
  exact (op_strictMono_left d).injective h3.symm

lemma newAtomCommutes_of_newAtomDecompose {k : ℕ} {F : AtomFamily α k} {d : α}
    (hdec : NewAtomDecompose (F := F) d) :
    NewAtomCommutes F d := by
  intro i
  have hdec' := hdec (unitMulti i 1) 1 2
  have hμ : mu F (unitMulti i 1) = F.atoms i := by
    simpa [KnuthSkillingAlgebra.iterate_op_one] using (mu_unitMulti F i 1)
  have hiter :
      iterate_op (op (F.atoms i) d) 2 =
        op (iterate_op (F.atoms i) 2) (iterate_op d 2) := by
    simpa [NewAtomDecompose, hμ, KnuthSkillingAlgebra.iterate_op_one, Nat.one_mul] using hdec'
  simpa using (op_comm_of_iter2_decompose (a := F.atoms i) (d := d) hiter)

theorem newAtomDecompose_iff_newAtomCommutes {k : ℕ} {F : AtomFamily α k} {d : α} :
    NewAtomDecompose (F := F) d ↔ NewAtomCommutes F d := by
  constructor
  · exact newAtomCommutes_of_newAtomDecompose (F := F) (d := d)
  · exact newAtomDecompose_of_newAtomCommutes (F := F) (d := d)

/-- Scaling preserves base-indexed A-membership when the new atom commutes with the old grid. -/
lemma extensionSetA_base_scaleMult_of_newAtomCommutes {k : ℕ} {F : AtomFamily α k}
    (IH : GridBridge F) {d : α} (hcomm : NewAtomCommutes F d)
    (r0 r : Multi k) (u m : ℕ) (hm : 0 < m)
    (hrA : r ∈ extensionSetA_base F d r0 u) :
    scaleMult m r ∈ extensionSetA_base F d (scaleMult m r0) (u * m) := by
  have hμ : mu F r < op (mu F r0) (iterate_op d u) := by
    simpa [extensionSetA_base, Set.mem_setOf_eq] using hrA
  have h_iter :
      iterate_op (mu F r) m < iterate_op (op (mu F r0) (iterate_op d u)) m := by
    have h1 : iterate_op (mu F r) 1 < iterate_op (op (mu F r0) (iterate_op d u)) 1 := by
      simpa [iterate_op_one] using hμ
    have :=
      repetition_lemma_lt (a := mu F r) (x := op (mu F r0) (iterate_op d u))
        (n := 1) (m := 1) (k := m) hm h1
    simpa [Nat.one_mul] using this
  have h_bridge_r : iterate_op (mu F r) m = mu F (scaleMult m r) := (IH.bridge r m).symm
  have h_bridge_r0 : iterate_op (mu F r0) m = mu F (scaleMult m r0) := (IH.bridge r0 m).symm
  have h_decomp :
      iterate_op (op (mu F r0) (iterate_op d u)) m =
        op (iterate_op (mu F r0) m) (iterate_op d (u * m)) :=
    iterate_op_mu_d_decompose (F := F) (d := d) hcomm r0 u m
  have : mu F (scaleMult m r) < op (mu F (scaleMult m r0)) (iterate_op d (u * m)) := by
    have h' : iterate_op (mu F r) m < op (iterate_op (mu F r0) m) (iterate_op d (u * m)) := by
      simpa [h_decomp] using h_iter
    simpa [h_bridge_r, h_bridge_r0] using h'
  simpa [extensionSetA_base, Set.mem_setOf_eq] using this

/-- Scaling preserves base-indexed A-membership assuming only the shifted-boundary power
decomposition law (`NewAtomDecompose`), without requiring full commutation with all atoms. -/
lemma extensionSetA_base_scaleMult_of_newAtomDecompose {k : ℕ} {F : AtomFamily α k}
    (IH : GridBridge F) {d : α} (hdec : NewAtomDecompose F d)
    (r0 r : Multi k) (u m : ℕ) (hm : 0 < m)
    (hrA : r ∈ extensionSetA_base F d r0 u) :
    scaleMult m r ∈ extensionSetA_base F d (scaleMult m r0) (u * m) := by
  have hμ : mu F r < op (mu F r0) (iterate_op d u) := by
    simpa [extensionSetA_base, Set.mem_setOf_eq] using hrA
  have h_iter :
      iterate_op (mu F r) m < iterate_op (op (mu F r0) (iterate_op d u)) m := by
    have h1 : iterate_op (mu F r) 1 < iterate_op (op (mu F r0) (iterate_op d u)) 1 := by
      simpa [iterate_op_one] using hμ
    have :=
      repetition_lemma_lt (a := mu F r) (x := op (mu F r0) (iterate_op d u))
        (n := 1) (m := 1) (k := m) hm h1
    simpa [Nat.one_mul] using this
  have h_bridge_r : iterate_op (mu F r) m = mu F (scaleMult m r) := (IH.bridge r m).symm
  have h_bridge_r0 : iterate_op (mu F r0) m = mu F (scaleMult m r0) := (IH.bridge r0 m).symm
  have h_decomp :
      iterate_op (op (mu F r0) (iterate_op d u)) m =
        op (iterate_op (mu F r0) m) (iterate_op d (u * m)) :=
    hdec r0 u m
  have : mu F (scaleMult m r) < op (mu F (scaleMult m r0)) (iterate_op d (u * m)) := by
    have h' : iterate_op (mu F r) m < op (iterate_op (mu F r0) m) (iterate_op d (u * m)) := by
      simpa [h_decomp] using h_iter
    simpa [h_bridge_r, h_bridge_r0] using h'
  simpa [extensionSetA_base, Set.mem_setOf_eq] using this

/-- Scaling preserves base-indexed C-membership when the new atom commutes with the old grid. -/
lemma extensionSetC_base_scaleMult_of_newAtomCommutes {k : ℕ} {F : AtomFamily α k}
    (IH : GridBridge F) {d : α} (hcomm : NewAtomCommutes F d)
    (r0 r : Multi k) (u m : ℕ) (hm : 0 < m)
    (hrC : r ∈ extensionSetC_base F d r0 u) :
    scaleMult m r ∈ extensionSetC_base F d (scaleMult m r0) (u * m) := by
  have hμ : op (mu F r0) (iterate_op d u) < mu F r := by
    simpa [extensionSetC_base, Set.mem_setOf_eq] using hrC
  have h_iter :
      iterate_op (op (mu F r0) (iterate_op d u)) m < iterate_op (mu F r) m := by
    have h1 : iterate_op (op (mu F r0) (iterate_op d u)) 1 < iterate_op (mu F r) 1 := by
      simpa [iterate_op_one] using hμ
    have :=
      repetition_lemma_lt (a := op (mu F r0) (iterate_op d u)) (x := mu F r)
        (n := 1) (m := 1) (k := m) hm h1
    simpa [Nat.one_mul] using this
  have h_bridge_r : iterate_op (mu F r) m = mu F (scaleMult m r) := (IH.bridge r m).symm
  have h_bridge_r0 : iterate_op (mu F r0) m = mu F (scaleMult m r0) := (IH.bridge r0 m).symm
  have h_decomp :
      iterate_op (op (mu F r0) (iterate_op d u)) m =
        op (iterate_op (mu F r0) m) (iterate_op d (u * m)) :=
    iterate_op_mu_d_decompose (F := F) (d := d) hcomm r0 u m
  have : op (mu F (scaleMult m r0)) (iterate_op d (u * m)) < mu F (scaleMult m r) := by
    have h' : op (iterate_op (mu F r0) m) (iterate_op d (u * m)) < iterate_op (mu F r) m := by
      simpa [h_decomp] using h_iter
    simpa [h_bridge_r, h_bridge_r0] using h'
  simpa [extensionSetC_base, Set.mem_setOf_eq] using this

/-- Scaling preserves base-indexed C-membership assuming only `NewAtomDecompose`. -/
lemma extensionSetC_base_scaleMult_of_newAtomDecompose {k : ℕ} {F : AtomFamily α k}
    (IH : GridBridge F) {d : α} (hdec : NewAtomDecompose F d)
    (r0 r : Multi k) (u m : ℕ) (hm : 0 < m)
    (hrC : r ∈ extensionSetC_base F d r0 u) :
    scaleMult m r ∈ extensionSetC_base F d (scaleMult m r0) (u * m) := by
  have hμ : op (mu F r0) (iterate_op d u) < mu F r := by
    simpa [extensionSetC_base, Set.mem_setOf_eq] using hrC
  have h_iter :
      iterate_op (op (mu F r0) (iterate_op d u)) m < iterate_op (mu F r) m := by
    have h1 : iterate_op (op (mu F r0) (iterate_op d u)) 1 < iterate_op (mu F r) 1 := by
      simpa [iterate_op_one] using hμ
    have :=
      repetition_lemma_lt (a := op (mu F r0) (iterate_op d u)) (x := mu F r)
        (n := 1) (m := 1) (k := m) hm h1
    simpa [Nat.one_mul] using this
  have h_bridge_r : iterate_op (mu F r) m = mu F (scaleMult m r) := (IH.bridge r m).symm
  have h_bridge_r0 : iterate_op (mu F r0) m = mu F (scaleMult m r0) := (IH.bridge r0 m).symm
  have h_decomp :
      iterate_op (op (mu F r0) (iterate_op d u)) m =
        op (iterate_op (mu F r0) m) (iterate_op d (u * m)) :=
    hdec r0 u m
  have : op (mu F (scaleMult m r0)) (iterate_op d (u * m)) < mu F (scaleMult m r) := by
    have h' : op (iterate_op (mu F r0) m) (iterate_op d (u * m)) < iterate_op (mu F r) m := by
      simpa [h_decomp] using h_iter
    simpa [h_bridge_r, h_bridge_r0] using h'
  simpa [extensionSetC_base, Set.mem_setOf_eq] using this

/-- Scaling preserves base-indexed B-membership when the new atom commutes with the old grid. -/
lemma extensionSetB_base_scaleMult_of_newAtomCommutes {k : ℕ} {F : AtomFamily α k}
    (IH : GridBridge F) {d : α} (hcomm : NewAtomCommutes F d)
    (r0 r : Multi k) (u m : ℕ)
    (hrB : r ∈ extensionSetB_base F d r0 u) :
    scaleMult m r ∈ extensionSetB_base F d (scaleMult m r0) (u * m) := by
  have hμ : mu F r = op (mu F r0) (iterate_op d u) := by
    simpa [extensionSetB_base, Set.mem_setOf_eq] using hrB
  have h_iter : iterate_op (mu F r) m = iterate_op (op (mu F r0) (iterate_op d u)) m := by
    simpa using congrArg (fun x => iterate_op x m) hμ
  have h_bridge_r : mu F (scaleMult m r) = iterate_op (mu F r) m := IH.bridge r m
  have h_bridge_r0 : mu F (scaleMult m r0) = iterate_op (mu F r0) m := IH.bridge r0 m
  have h_decomp :
      iterate_op (op (mu F r0) (iterate_op d u)) m =
        op (iterate_op (mu F r0) m) (iterate_op d (u * m)) :=
    iterate_op_mu_d_decompose (F := F) (d := d) hcomm r0 u m
  have : mu F (scaleMult m r) = op (mu F (scaleMult m r0)) (iterate_op d (u * m)) := by
    calc
      mu F (scaleMult m r) = iterate_op (mu F r) m := h_bridge_r
      _ = iterate_op (op (mu F r0) (iterate_op d u)) m := h_iter
      _ = op (iterate_op (mu F r0) m) (iterate_op d (u * m)) := h_decomp
      _ = op (mu F (scaleMult m r0)) (iterate_op d (u * m)) := by
          simpa [h_bridge_r0]
  simpa [extensionSetB_base, Set.mem_setOf_eq] using this

/-- Scaling preserves base-indexed B-membership assuming only `NewAtomDecompose`. -/
lemma extensionSetB_base_scaleMult_of_newAtomDecompose {k : ℕ} {F : AtomFamily α k}
    (IH : GridBridge F) {d : α} (hdec : NewAtomDecompose F d)
    (r0 r : Multi k) (u m : ℕ)
    (hrB : r ∈ extensionSetB_base F d r0 u) :
    scaleMult m r ∈ extensionSetB_base F d (scaleMult m r0) (u * m) := by
  have hμ : mu F r = op (mu F r0) (iterate_op d u) := by
    simpa [extensionSetB_base, Set.mem_setOf_eq] using hrB
  have h_iter : iterate_op (mu F r) m = iterate_op (op (mu F r0) (iterate_op d u)) m := by
    simpa using congrArg (fun x => iterate_op x m) hμ
  have h_bridge_r : mu F (scaleMult m r) = iterate_op (mu F r) m := IH.bridge r m
  have h_bridge_r0 : mu F (scaleMult m r0) = iterate_op (mu F r0) m := IH.bridge r0 m
  have h_decomp :
      iterate_op (op (mu F r0) (iterate_op d u)) m =
        op (iterate_op (mu F r0) m) (iterate_op d (u * m)) :=
    hdec r0 u m
  have : mu F (scaleMult m r) = op (mu F (scaleMult m r0)) (iterate_op d (u * m)) := by
    -- Rewrite everything in terms of iterates, then apply the decomposition law.
    calc
      mu F (scaleMult m r) = iterate_op (mu F r) m := by simpa [h_bridge_r]
      _ = iterate_op (op (mu F r0) (iterate_op d u)) m := by simpa [h_iter]
      _ = op (iterate_op (mu F r0) m) (iterate_op d (u * m)) := by simpa [h_decomp]
      _ = op (mu F (scaleMult m r0)) (iterate_op d (u * m)) := by simpa [h_bridge_r0]
  simpa [extensionSetB_base, Set.mem_setOf_eq] using this

/-- Scaling lemma for base-indexed admissibility: if a slope `δ` separates A/C at the scaled
instance `(scaleMult m r0, u*m)`, it also separates A/C at `(r0, u)`.

This is the key “descent step” one would use in a base-gap strong-induction strategy; the genuine
remaining difficulty is producing a well-founded measure that guarantees termination. -/
lemma admissibleDelta_base_of_scaleMult_of_newAtomCommutes
    {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) {d : α} (hcomm : NewAtomCommutes F d)
    {δ : ℝ} (r0 : Multi k) (u : ℕ) (hu : 0 < u)
    (m : ℕ) (hm : 0 < m)
    (hAd :
      AdmissibleDelta_base (k := k) (F := F) (R₀ := R) (d₀ := d) δ (scaleMult m r0) (u * m)
        (Nat.mul_pos hu hm)) :
    AdmissibleDelta_base (k := k) (F := F) (R₀ := R) (d₀ := d) δ r0 u hu := by
  classical
  refine ⟨?_, ?_⟩
  · intro r hrA
    have hrA' :
        scaleMult m r ∈ extensionSetA_base F d (scaleMult m r0) (u * m) :=
      extensionSetA_base_scaleMult_of_newAtomCommutes (IH := IH) (d := d) hcomm r0 r u m hm hrA
    have hlt :
        separationStatistic_base R (scaleMult m r0) (scaleMult m r) (u * m) (Nat.mul_pos hu hm) < δ :=
      hAd.1 (scaleMult m r) hrA'
    simpa [separationStatistic_base_scaleMult (R := R) (r0 := r0) (r := r) (u := u) (m := m) hu hm] using hlt
  · intro r hrC
    have hrC' :
        scaleMult m r ∈ extensionSetC_base F d (scaleMult m r0) (u * m) :=
      extensionSetC_base_scaleMult_of_newAtomCommutes (IH := IH) (d := d) hcomm r0 r u m hm hrC
    have hlt :
        δ < separationStatistic_base R (scaleMult m r0) (scaleMult m r) (u * m) (Nat.mul_pos hu hm) :=
      hAd.2 (scaleMult m r) hrC'
    -- Rewrite the scaled statistic back to the original one.
    have hstat :
        separationStatistic_base R (scaleMult m r0) (scaleMult m r) (u * m) (Nat.mul_pos hu hm) =
          separationStatistic_base R r0 r u hu :=
      separationStatistic_base_scaleMult (R := R) (r0 := r0) (r := r) (u := u) (m := m) hu hm
    simpa [hstat] using hlt

/-- If a base-indexed B-witness exists after scaling `(r0,u) ↦ (m·r0, u*m)`, then `chooseδ` is
already admissible at the original `(r0,u)`.

This packages a common “commensurability” pattern: internal (B-witness) admissibility at a scaled
instance implies admissibility at the unscaled instance, provided the new atom commutes with the
old grid (so scaling preserves base-indexed membership and statistics). -/
lemma admissibleDelta_base_chooseδ_of_scaled_B_base_witness
    {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
    (IH : GridBridge F) (H : GridComm F) (d : α) (hd : ident < d)
    [KSSeparation α]
    (hcomm : NewAtomCommutes F d)
    (r0 : Multi k) (u : ℕ) (hu : 0 < u)
    (m : ℕ) (hm : 0 < m)
    (hB_scaled : ∃ rB : Multi k, rB ∈ extensionSetB_base F d (scaleMult m r0) (u * m)) :
    AdmissibleDelta_base (k := k) (F := F) (R₀ := R) (d₀ := d) (chooseδ hk R d hd) r0 u hu := by
  have hAd_scaled :
      AdmissibleDelta_base (k := k) (F := F) (R₀ := R) (d₀ := d) (chooseδ hk R d hd) (scaleMult m r0)
        (u * m) (Nat.mul_pos hu hm) :=
    admissibleDelta_base_chooseδ_of_B_base_witness (R := R) (hk := hk) (IH := IH) (H := H) (d := d)
      (hd := hd) (r0 := scaleMult m r0) (u := u * m) (hu := Nat.mul_pos hu hm) hB_scaled
  exact
    admissibleDelta_base_of_scaleMult_of_newAtomCommutes (R := R) (IH := IH) (d := d) hcomm
      (r0 := r0) (u := u) (hu := hu) (m := m) (hm := hm) hAd_scaled

/-- **Equality case helper**: When a^n = (μ(F,r0) ⊕ d^u)^m (equality), we can derive
the exact Θ' relationship using well-definedness, which gives the needed bound.

This uses:
1. `iterate_op_mu_d_decompose` (requires NewAtomCommutes) to decompose RHS
2. GridBridge to convert μ(F,r0)^m = mu F (scaleMult m r0)
3. `mu_extend_last` to express both sides as extended grid elements
4. `Theta'_well_defined` to conclude equal Θ'-values imply equal formula values
-/
lemma theta_bound_of_separation_equality
    {k : ℕ} {F : AtomFamily α k} (R : MultiGridRep F)
    (H : GridComm F) (IH : GridBridge F) {d : α} (hd : ident < d)
    (hcomm : NewAtomCommutes F d)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (hδA : ∀ r u (hu : 0 < u), r ∈ extensionSetA F d u → separationStatistic R r u hu ≤ δ)
    (hδC : ∀ r u (hu : 0 < u), r ∈ extensionSetC F d u → δ ≤ separationStatistic R r u hu)
    (hδB : ∀ r u (hu : 0 < u), r ∈ extensionSetB F d u → separationStatistic R r u hu = δ)
    (i₀ : Fin k) (r0 : Multi k) (n m u : ℕ)
    (heq : iterate_op (F.atoms i₀) n = iterate_op (op (mu F r0) (iterate_op d u)) m) :
    n * thetaAtom (F := F) R i₀ =
      m * R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ + (u * m : ℕ) * δ := by
  -- Step 1: Decompose RHS using iterate_op_mu_d_decompose
  have h_decomp : iterate_op (op (mu F r0) (iterate_op d u)) m =
      op (iterate_op (mu F r0) m) (iterate_op d (u * m)) :=
    iterate_op_mu_d_decompose hcomm r0 u m

  -- Step 2: Use GridBridge to get μ(F,r0)^m = mu F (scaleMult m r0)
  have h_bridge : iterate_op (mu F r0) m = mu F (scaleMult m r0) :=
    (IH.bridge r0 m).symm

  -- Step 3: Combine to get a^n = op (mu F (scaleMult m r0)) (iterate_op d (u*m))
  have h_an_eq : iterate_op (F.atoms i₀) n =
      op (mu F (scaleMult m r0)) (iterate_op d (u * m)) := by
    rw [heq, h_decomp, h_bridge]

  -- Step 4: Express LHS as extended grid element
  -- a^n = mu F (unitMulti i₀ n) by mu_unitMulti
  have h_an_mu : iterate_op (F.atoms i₀) n = mu F (unitMulti i₀ n) := by
    rw [mu_unitMulti]

  -- Step 5: Use mu_extend_last for both sides
  let F' := extendAtomFamily F d hd

  -- LHS: mu F' (joinMulti (unitMulti i₀ n) 0) = a^n
  have h_lhs : mu F' (joinMulti (unitMulti i₀ n) 0) = iterate_op (F.atoms i₀) n := by
    rw [mu_extend_last]
    simp [iterate_op_zero, op_ident_right, mu_unitMulti]

  -- RHS: mu F' (joinMulti (scaleMult m r0) (u*m)) = op (mu F (scaleMult m r0)) (iterate_op d (u*m))
  have h_rhs : mu F' (joinMulti (scaleMult m r0) (u * m)) =
      op (mu F (scaleMult m r0)) (iterate_op d (u * m)) := by
    exact mu_extend_last F d hd (scaleMult m r0) (u * m)

  -- Step 6: The extended grid elements are equal
  have h_mu_eq : mu F' (joinMulti (unitMulti i₀ n) 0) =
      mu F' (joinMulti (scaleMult m r0) (u * m)) := by
    rw [h_lhs, h_an_eq, ← h_rhs]

  -- Step 7: Apply Theta'_well_defined
  have h_theta_eq :=
    Theta'_well_defined R H IH d hd δ hδ_pos hδA hδC hδB h_mu_eq

  -- Step 8: Simplify using splitMulti_joinMulti
  -- Theta'_raw (unitMulti i₀ n) 0 = Theta'_raw (scaleMult m r0) (u*m)
  simp only [splitMulti_joinMulti] at h_theta_eq

  -- Step 9: Expand Theta'_raw
  -- Theta'_raw r_old t = Θ(r_old) + t * δ
  simp only [Theta'_raw] at h_theta_eq

  -- Step 10: Use Theta_unitMulti and Theta_scaleMult
  have h_θ_unit : R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ =
      n * thetaAtom (F := F) R i₀ := Theta_unitMulti R i₀ n

  have h_θ_scale : R.Θ_grid ⟨mu F (scaleMult m r0), mu_mem_kGrid F (scaleMult m r0)⟩ =
      m * R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := Theta_scaleMult R r0 m

  -- Substitute into h_theta_eq
  -- LHS of h_theta_eq: n * θ_a + 0 * δ = n * θ_a
  -- RHS of h_theta_eq: m * Θ(r0) + (u*m) * δ
  simp only [h_θ_unit, h_θ_scale, Nat.cast_zero, zero_mul, add_zero, Nat.cast_mul] at h_theta_eq
  -- Convert ↑u * ↑m * δ to ↑(u * m) * δ
  have h_cast : (u : ℝ) * (m : ℝ) * δ = ((u * m : ℕ) : ℝ) * δ := by simp [Nat.cast_mul]
  rw [h_cast] at h_theta_eq
  exact h_theta_eq

section ChooseδBase

variable {k : ℕ} (hk : k ≥ 1) {F : AtomFamily α k} (R : MultiGridRep F)
variable (IH : GridBridge F) (H : GridComm F)
variable (d : α) (hd : ident < d)
variable [KSSeparation α]

/-!
### Non-circular “old-part dominates” helper

In the (base-indexed) KSSeparation bump proof attempt for the hard A-case, one key subcase is:
`a^n ≤ μ(F,r0)^m`.  In this situation, the Θ-value of the separator `a^n` is bounded purely by the
old-grid Θ-value of `r0`, and the additional `u*m` term contributes nonnegatively.

This lemma is independent of any strict-gap / Θ′ monotonicity arguments; it only uses the
existing k-grid representation (`MultiGridRep`) and the bridge lemma (`GridBridge`).
-/

omit [KSSeparation α] in
/-- If `a^n ≤ μ(F,r0)^m`, then `n·θ(a) ≤ m·Θ(r0) + (u*m)·chooseδ`. -/
private lemma thetaAtom_mul_le_Theta_base_mul_of_iterate_atom_le_iterate_mu
    (IH : GridBridge F) (H : GridComm F)
    (i₀ : Fin k) (r0 : Multi k) (n m u : ℕ)
    (hold : iterate_op (F.atoms i₀) n ≤ iterate_op (mu F r0) m) :
    n * thetaAtom (F := F) R i₀ ≤
        m * R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ +
          (u * m : ℕ) * chooseδ hk R d hd := by
  -- Rewrite the α-inequality in terms of μ-values on the k-grid.
  have hμ_left : iterate_op (F.atoms i₀) n = mu F (unitMulti i₀ n) := by
    simpa using (mu_unitMulti (F := F) i₀ n).symm
  have hμ_right : iterate_op (mu F r0) m = mu F (scaleMult m r0) := by
    simpa using (IH.bridge r0 m).symm
  have hμ_le : mu F (unitMulti i₀ n) ≤ mu F (scaleMult m r0) := by
    simpa [hμ_left, hμ_right] using hold
  -- Apply monotonicity of Θ on the grid.
  have hθ_le :
      R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ ≤
        R.Θ_grid ⟨mu F (scaleMult m r0), mu_mem_kGrid F (scaleMult m r0)⟩ :=
    R.strictMono.monotone hμ_le
  -- Rewrite both sides using unit/scaling lemmas.
  have hθ_unit :
      R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ =
        n * thetaAtom (F := F) R i₀ := by
    simpa [thetaAtom] using (Theta_unitMulti (R := R) (F := F) i₀ n)
  have hθ_scale :
      R.Θ_grid ⟨mu F (scaleMult m r0), mu_mem_kGrid F (scaleMult m r0)⟩ =
        m * R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := by
    simpa using (Theta_scaleMult (R := R) (r := r0) m)
  have h_main :
      n * thetaAtom (F := F) R i₀ ≤ m * R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := by
    simpa [hθ_unit, hθ_scale] using hθ_le
  -- Add the nonnegative `u*m` term.
  have hδ_nonneg : 0 ≤ (chooseδ hk R d hd) := le_of_lt (delta_pos hk R IH H d hd)
  have hterm_nonneg : 0 ≤ (u * m : ℕ) * chooseδ hk R d hd := by
    exact mul_nonneg (by exact_mod_cast (Nat.zero_le (u * m))) hδ_nonneg
  linarith

/-!
`ChooseδBaseAdmissible` is defined in `AppendixA/Core/Induction/ThetaPrime.lean` and imported at
the top of this file.
-/

/-- Equivalent “no-common-prefix” form of `ChooseδBaseAdmissible`.

Using `commonMulti`/`remMultiLeft`/`remMultiRight`, any base-indexed comparison can be reduced
to the case where the base `r0` and witness `r` share **no** coordinatewise common part. -/
class ChooseδBaseAdmissible_noCommon : Prop where
  base_noCommon :
    ∀ (r0 : Multi k) (u : ℕ) (hu : 0 < u),
      (∀ r : Multi k,
          commonMulti r0 r = 0 →
            r ∈ extensionSetA_base F d r0 u →
              separationStatistic_base R r0 r u hu < chooseδ hk R d hd) ∧
        (∀ r : Multi k,
          commonMulti r0 r = 0 →
            r ∈ extensionSetC_base F d r0 u →
              chooseδ hk R d hd < separationStatistic_base R r0 r u hu)

omit [KSSeparation α] in
theorem chooseδBaseAdmissible_noCommon_of_chooseδBaseAdmissible
    (h : ChooseδBaseAdmissible (hk := hk) (R := R) (F := F) (d := d) (hd := hd)) :
    ChooseδBaseAdmissible_noCommon (hk := hk) (R := R) (F := F) (d := d) (hd := hd) := by
  refine ⟨?_⟩
  intro r0 u hu
  refine ⟨?_, ?_⟩
  · intro r _hcommon hrA
    exact (h.base r0 u hu).1 r hrA
  · intro r _hcommon hrC
    exact (h.base r0 u hu).2 r hrC

omit [KSSeparation α] in
theorem chooseδBaseAdmissible_of_chooseδBaseAdmissible_noCommon
    (H : GridComm F)
    (h : ChooseδBaseAdmissible_noCommon (hk := hk) (R := R) (F := F) (d := d) (hd := hd)) :
    ChooseδBaseAdmissible (hk := hk) (R := R) (F := F) (d := d) (hd := hd) := by
  refine ⟨?_⟩
  intro r0 u hu
  refine ⟨?_, ?_⟩
  · intro r hrA
    let r0' : Multi k := remMultiLeft r0 r
    let r' : Multi k := remMultiRight r0 r
    have hrA' : r' ∈ extensionSetA_base F d r0' u := by
      exact (extensionSetA_base_iff_remMulti (H := H) d r0 r u).1 hrA
    have hcommon : commonMulti r0' r' = (0 : Multi k) := by
      simpa [r0', r'] using commonMulti_remMultiLeft_remMultiRight_eq_zero (r := r0) (s := r)
    have hlt :
        separationStatistic_base R r0' r' u hu < chooseδ hk R d hd :=
      (h.base_noCommon r0' u hu).1 r' (by simpa [hcommon]) hrA'
    simpa [separationStatistic_base_eq_remMulti (R := R) r0 r u hu, r0', r'] using hlt
  · intro r hrC
    let r0' : Multi k := remMultiLeft r0 r
    let r' : Multi k := remMultiRight r0 r
    have hrC' : r' ∈ extensionSetC_base F d r0' u := by
      exact (extensionSetC_base_iff_remMulti (H := H) d r0 r u).1 hrC
    have hcommon : commonMulti r0' r' = (0 : Multi k) := by
      simpa [r0', r'] using commonMulti_remMultiLeft_remMultiRight_eq_zero (r := r0) (s := r)
    have hlt :
        chooseδ hk R d hd < separationStatistic_base R r0' r' u hu :=
      (h.base_noCommon r0' u hu).2 r' (by simpa [hcommon]) hrC'
    simpa [separationStatistic_base_eq_remMulti (R := R) r0 r u hu, r0', r'] using hlt

omit [KSSeparation α] in
theorem chooseδBaseAdmissible_iff_chooseδBaseAdmissible_noCommon
    (H : GridComm F) :
    ChooseδBaseAdmissible (hk := hk) (R := R) (F := F) (d := d) (hd := hd) ↔
      ChooseδBaseAdmissible_noCommon (hk := hk) (R := R) (F := F) (d := d) (hd := hd) := by
  constructor
  · intro hBase
    exact
      chooseδBaseAdmissible_noCommon_of_chooseδBaseAdmissible (hk := hk) (R := R) (d := d) (hd := hd) hBase
  · intro hNoCommon
    exact
      chooseδBaseAdmissible_of_chooseδBaseAdmissible_noCommon (hk := hk) (R := R) (d := d) (hd := hd) H hNoCommon

theorem bEmptyStrictGapSpec_of_chooseδBaseAdmissible
    (h : ChooseδBaseAdmissible (hk := hk) (R := R) (F := F) (d := d) (hd := hd)) :
    BEmptyStrictGapSpec hk R IH H d hd := by
  classical
  refine ⟨?_, ?_⟩
  · intro _hB_empty r_old_x r_old_y Δ hΔ _hμ hA_base _hB_base
    exact (h.base r_old_y Δ hΔ).1 r_old_x hA_base
  · intro _hB_empty r_old_x r_old_y Δ hΔ _hμ hC_base _hB_base
    exact (h.base r_old_x Δ hΔ).2 r_old_y hC_base

/-- In the globally `B = ∅` regime, the strict-gap interface is strong enough to recover full
base-indexed admissibility of `δ := chooseδ …`.

The proof splits on whether the base boundary `μ(r0) ⊕ d^u` is itself already on the old grid:
the internal (B-witness) branch follows from `delta_shift_equiv`, while the genuinely external
branch is exactly the content of `BEmptyStrictGapSpec`. -/
theorem chooseδBaseAdmissible_of_BEmptyStrictGapSpec
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u)
    (hStrict : BEmptyStrictGapSpec (α := α) hk R IH H d hd) :
    ChooseδBaseAdmissible (hk := hk) (R := R) (F := F) (d := d) (hd := hd) := by
  classical
  refine ⟨?_⟩
  intro r0 u hu
  by_cases hB_base : ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 u
  · -- Internal case: the boundary is on the old grid.
    exact
      admissibleDelta_base_chooseδ_of_B_base_witness (R := R) (F := F) (hk := hk) (d := d) (hd := hd)
        (IH := IH) (H := H) r0 u hu hB_base
  · -- External case: no base-indexed B-witness at level u.
    refine ⟨?_, ?_⟩
    · intro r hrA
      by_cases hμ_le : mu F r ≤ mu F r0
      · -- If `μ(r) ≤ μ(r0)`, the statistic is non-positive, hence < δ.
        have hδ_pos : 0 < chooseδ hk R d hd := delta_pos hk R IH H d hd
        have hθ_le :
            R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ ≤
              R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ :=
          R.strictMono.monotone hμ_le
        have hstat_le : separationStatistic_base R r0 r u hu ≤ 0 := by
          simp only [separationStatistic_base]
          exact
            div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hθ_le) (Nat.cast_pos.mpr hu).le
        linarith
      · -- If `μ(r0) < μ(r)`, invoke the strict-gap interface.
        have hμ_lt : mu F r0 < mu F r := lt_of_not_ge hμ_le
        exact hStrict.A hB_empty r r0 u hu hμ_lt hrA hB_base
    · intro r hrC
      -- `μ(r0) < μ(r0) ⊕ d^u < μ(r)` gives the needed base inequality.
      have hμ_r0_lt_bd : mu F r0 < op (mu F r0) (iterate_op d u) := by
        have hdu : ident < iterate_op d u := iterate_op_pos d hd u hu
        simpa [op_ident_right] using (op_strictMono_right (mu F r0) hdu)
      have hμ_bd_lt : op (mu F r0) (iterate_op d u) < mu F r := by
        simpa [extensionSetC_base, Set.mem_setOf_eq] using hrC
      have hμ_lt : mu F r0 < mu F r := lt_trans hμ_r0_lt_bd hμ_bd_lt
      exact hStrict.C hB_empty r0 r u hu hμ_lt hrC hB_base

theorem chooseδBaseAdmissible_iff_bEmptyStrictGapSpec
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u) :
    ChooseδBaseAdmissible (hk := hk) (R := R) (F := F) (d := d) (hd := hd) ↔
      BEmptyStrictGapSpec (α := α) hk R IH H d hd := by
  constructor
  · intro h
    exact bEmptyStrictGapSpec_of_chooseδBaseAdmissible (hk := hk) (R := R) (IH := IH) (H := H)
      (d := d) (hd := hd) h
  · intro h
    exact chooseδBaseAdmissible_of_BEmptyStrictGapSpec (hk := hk) (R := R) (IH := IH) (H := H)
      (d := d) (hd := hd) (hB_empty := hB_empty) h

/-- Goertzel’s “realizer” interface at `δ := chooseδ …` is equivalent to base-indexed admissibility
once we assume the global B-empty regime (`∀ r u>0, r ∉ extensionSetB …`).

This repackages the circularity cleanly:
- `RealizesThetaRaw` gives strict gaps (`BEmptyStrictGapSpec`) by the flip/boundary-collision argument, and
- strict gaps plus global B-emptiness give full base admissibility (`ChooseδBaseAdmissible`).
-/
theorem realizesThetaRaw_chooseδ_iff_chooseδBaseAdmissible
    (IH : GridBridge F) (H : GridComm F)
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u) :
    RealizesThetaRaw (R := R) (F := F) (d := d) (hd := hd) (chooseδ hk R d hd) ↔
      ChooseδBaseAdmissible (hk := hk) (R := R) (F := F) (d := d) (hd := hd) := by
  constructor
  · intro hReal
    have hStrict : BEmptyStrictGapSpec hk R IH H d hd :=
      bEmptyStrictGapSpec_of_realizesThetaRaw_chooseδ (hk := hk) (R := R) (IH := IH) (H := H)
        (d := d) (hd := hd) hReal
    exact
      chooseδBaseAdmissible_of_BEmptyStrictGapSpec (hk := hk) (R := R) (IH := IH) (H := H) (d := d)
        (hd := hd) (hB_empty := hB_empty) hStrict
  · intro hBase
    exact
      realizesThetaRaw_chooseδ_of_chooseδBaseAdmissible (hk := hk) (R := R) (H := H) (d := d)
        (hd := hd) hBase

/-- Variant of `bEmptyStrictGapSpec_of_chooseδBaseAdmissible` that produces the
no-common-prefix strict-gap interface (`BEmptyStrictGapSpec_noCommon`).

This is a convenient target because the strict-gap blocker in `ThetaPrime.lean` is now proven
equivalent to its no-common-prefix form. -/
theorem bEmptyStrictGapSpec_noCommon_of_chooseδBaseAdmissible_noCommon
    (h :
      ChooseδBaseAdmissible_noCommon (hk := hk) (R := R) (F := F) (d := d) (hd := hd)) :
    BEmptyStrictGapSpec_noCommon hk R IH H d hd := by
  have hBase : ChooseδBaseAdmissible (hk := hk) (R := R) (F := F) (d := d) (hd := hd) :=
    chooseδBaseAdmissible_of_chooseδBaseAdmissible_noCommon
      (hk := hk) (R := R) (F := F) (d := d) (hd := hd) H h
  have hStrict : BEmptyStrictGapSpec hk R IH H d hd :=
    bEmptyStrictGapSpec_of_chooseδBaseAdmissible (hk := hk) (R := R) (IH := IH) (H := H)
      (d := d) (hd := hd) hBase
  exact bEmptyStrictGapSpec_noCommon_of_bEmptyStrictGapSpec (hk := hk) (R := R) (IH := IH) (H := H)
    (d := d) (hd := hd) hStrict

theorem chooseδBaseAdmissible_noCommon_iff_bEmptyStrictGapSpec_noCommon
    (hB_empty : ∀ r u, 0 < u → r ∉ extensionSetB F d u) :
    ChooseδBaseAdmissible_noCommon (hk := hk) (R := R) (F := F) (d := d) (hd := hd) ↔
      BEmptyStrictGapSpec_noCommon (α := α) hk R IH H d hd := by
  constructor
  · intro hNoCommon
    exact bEmptyStrictGapSpec_noCommon_of_chooseδBaseAdmissible_noCommon
      (hk := hk) (R := R) (IH := IH) (H := H) (d := d) (hd := hd) hNoCommon
  · intro hStrictNoCommon
    have hStrict : BEmptyStrictGapSpec (α := α) hk R IH H d hd :=
      (bEmptyStrictGapSpec_iff_bEmptyStrictGapSpec_noCommon (α := α) hk R IH H d hd).2
        hStrictNoCommon
    have hBase : ChooseδBaseAdmissible (hk := hk) (R := R) (F := F) (d := d) (hd := hd) :=
      (chooseδBaseAdmissible_iff_bEmptyStrictGapSpec (hk := hk) (R := R) (IH := IH) (H := H)
        (d := d) (hd := hd) (hB_empty := hB_empty)).2 hStrict
    exact
      (chooseδBaseAdmissible_iff_chooseδBaseAdmissible_noCommon (hk := hk) (R := R) (F := F)
        (d := d) (hd := hd) (H := H)).1 hBase

/-- Convenience wrapper: no-common-prefix variant of `realizesThetaRaw_chooseδ_of_chooseδBaseAdmissible`. -/
theorem realizesThetaRaw_chooseδ_of_chooseδBaseAdmissible_noCommon
    (H : GridComm F)
    (hBase :
      ChooseδBaseAdmissible_noCommon (hk := hk) (R := R) (F := F) (d := d) (hd := hd)) :
    RealizesThetaRaw (R := R) (F := F) (d := d) (hd := hd) (chooseδ hk R d hd) := by
  have hBase' : ChooseδBaseAdmissible (hk := hk) (R := R) (F := F) (d := d) (hd := hd) :=
    chooseδBaseAdmissible_of_chooseδBaseAdmissible_noCommon
      (hk := hk) (R := R) (F := F) (d := d) (hd := hd) H hBase
  exact
    realizesThetaRaw_chooseδ_of_chooseδBaseAdmissible (hk := hk) (R := R) (H := H) (d := d)
      (hd := hd) hBase'

/-- Convenience wrapper: the inductive extension step follows from the stronger
`ChooseδBaseAdmissible` hypothesis. -/
theorem extend_grid_rep_with_atom_of_chooseδBaseAdmissible
    (H : GridComm F) (hBase : ChooseδBaseAdmissible (hk := hk) (R := R) (F := F) (d := d) (hd := hd)) :
      ∃ (F' : AtomFamily α (k + 1)),
      (∀ i : Fin k, F'.atoms ⟨i, Nat.lt_succ_of_lt i.is_lt⟩ = F.atoms i) ∧
      F'.atoms ⟨k, Nat.lt_succ_self k⟩ = d ∧
      ∃ (R' : MultiGridRep F'),
        (∀ r_old : Multi k, ∀ t : ℕ,
          R'.Θ_grid ⟨mu F' (joinMulti r_old t), mu_mem_kGrid F' (joinMulti r_old t)⟩ =
          R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * chooseδ hk R d hd) := by
  exact extend_grid_rep_with_atom_of_gridComm (α := α) (hk := hk) (R := R) (H := H) (d := d)
    (hd := hd) hBase

/-!
### Proof attempt for ChooseδBaseAdmissible_noCommon

The key insight is to decompose based on whether μ(F,r) falls below or above d^u:
- If μ(F,r) < d^u: r is also an absolute A-witness, and we can bound the base-indexed
  statistic by the absolute statistic (since Θ(μ(F,r0)) ≥ 0).
- If d^u ≤ μ(F,r): This is the harder case requiring KSSeparation bump.
-/

omit [KSSeparation α] in
/-- Helper: when μ(F,r) = ident, the base-indexed A-statistic is non-positive, hence < δ. -/
private lemma A_base_statistic_lt_chooseδ_of_mu_eq_ident
    (IH : GridBridge F) (H : GridComm F)
    (r0 r : Multi k) (u : ℕ) (hu : 0 < u)
    (hμr : mu F r = ident) :
    separationStatistic_base R r0 r u hu < chooseδ hk R d hd := by
  have hδ_pos : 0 < chooseδ hk R d hd := delta_pos hk R IH H d hd
  have hθr : R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ = 0 := by
    have hsub : (⟨mu F r, mu_mem_kGrid F r⟩ : {x // x ∈ kGrid F}) = ⟨ident, ident_mem_kGrid F⟩ := by
      ext; simpa [hμr]
    simpa [hsub] using R.ident_eq_zero
  have hθ_r0_nonneg : 0 ≤ R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := by
    have h_ident_le : ident ≤ mu F r0 := ident_le _
    rcases h_ident_le.eq_or_lt with h_eq | h_lt
    · have hsub :
          (⟨mu F r0, mu_mem_kGrid F r0⟩ : {x // x ∈ kGrid F}) = ⟨ident, ident_mem_kGrid F⟩ := by
        ext; exact h_eq.symm
      simp [hsub, R.ident_eq_zero]
    · have hθ_pos : R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ <
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := R.strictMono h_lt
      simpa [R.ident_eq_zero] using (le_of_lt hθ_pos)
  have hstat_le : separationStatistic_base R r0 r u hu ≤ 0 := by
    simp only [separationStatistic_base, hθr, zero_sub]
    have h_neg_nonneg : -(R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩) ≤ 0 :=
      neg_nonpos.mpr hθ_r0_nonneg
    have h_u_pos : (0 : ℝ) < u := Nat.cast_pos.mpr hu
    exact div_nonpos_of_nonpos_of_nonneg h_neg_nonneg h_u_pos.le
  linarith

omit [KSSeparation α] in
/-- Helper: if `μ(F,r) ≤ μ(F,r0)`, the base-indexed statistic is non-positive, hence `< chooseδ`. -/
private lemma A_base_statistic_lt_chooseδ_of_mu_le
    (IH : GridBridge F) (H : GridComm F)
    (r0 r : Multi k) (u : ℕ) (hu : 0 < u)
    (hμ_le : mu F r ≤ mu F r0) :
    separationStatistic_base R r0 r u hu < chooseδ hk R d hd := by
  have hδ_pos : 0 < chooseδ hk R d hd := delta_pos hk R IH H d hd
  have hθ_le :
      R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ ≤ R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ :=
    R.strictMono.monotone hμ_le
  have hstat_le : separationStatistic_base R r0 r u hu ≤ 0 := by
    simp only [separationStatistic_base]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hθ_le) (Nat.cast_pos.mpr hu).le
  linarith

/-- Helper: if `r ∈ extensionSetA F d u` (absolute A), then any base-indexed statistic at level `u`
is bounded by the absolute statistic, hence `< chooseδ`. -/
private lemma A_base_statistic_lt_chooseδ_of_absolute
    (IH : GridBridge F) (H : GridComm F)
    (r0 r : Multi k) (u : ℕ) (hu : 0 < u)
    (hrA_abs : r ∈ extensionSetA F d u) :
    separationStatistic_base R r0 r u hu < chooseδ hk R d hd := by
  have hθ_r0_nonneg : 0 ≤ R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := by
    have h_ident_le : ident ≤ mu F r0 := ident_le _
    rcases h_ident_le.eq_or_lt with h_eq | h_lt
    · have hsub :
          (⟨mu F r0, mu_mem_kGrid F r0⟩ : {x // x ∈ kGrid F}) = ⟨ident, ident_mem_kGrid F⟩ := by
        ext; exact h_eq.symm
      simp [hsub, R.ident_eq_zero]
    · have hθ_pos :
          R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ <
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := R.strictMono h_lt
      simpa [R.ident_eq_zero] using (le_of_lt hθ_pos)
  have hstat_le : separationStatistic_base R r0 r u hu ≤ separationStatistic R r u hu := by
    simp only [separationStatistic_base, separationStatistic]
    have hsub :
        R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ ≤
          R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := by
      linarith
    exact div_le_div_of_nonneg_right hsub (Nat.cast_pos.mpr hu).le
  have habs_lt : separationStatistic R r u hu < chooseδ hk R d hd :=
    A_statistic_lt_chooseδ (α := α) (hk := hk) (R := R) (H := H) (IH := IH) (d := d) (hd := hd)
      r u hu hrA_abs
  linarith

/-- Helper: the A-side of `ChooseδBaseAdmissible_noCommon` reduces to a single remaining hard case.

The already-proven subcases are:
- `μ(F,r) ≤ μ(F,r0)` (statistic is non-positive), and
- `μ(F,r) < d^u` (reduce to the absolute strict A-bound).

So it suffices to handle the “hard” regime `μ(F,r0) < μ(F,r)` and `d^u ≤ μ(F,r)`. -/
private theorem chooseδBaseAdmissible_noCommon_A_of_hardCase
    (IH : GridBridge F) (H : GridComm F)
    (hardA :
      ∀ (r0 : Multi k) (u : ℕ) (hu : 0 < u) (r : Multi k),
        commonMulti r0 r = 0 →
          r ∈ extensionSetA_base F d r0 u →
            mu F r0 < mu F r →
              iterate_op d u ≤ mu F r →
                separationStatistic_base R r0 r u hu < chooseδ hk R d hd) :
    ∀ (r0 : Multi k) (u : ℕ) (hu : 0 < u) (r : Multi k),
      commonMulti r0 r = 0 →
        r ∈ extensionSetA_base F d r0 u →
          separationStatistic_base R r0 r u hu < chooseδ hk R d hd := by
  intro r0 u hu r hcommon hrA
  by_cases hμ_le : mu F r ≤ mu F r0
  · exact
      A_base_statistic_lt_chooseδ_of_mu_le (hk := hk) (R := R) (d := d) (hd := hd) IH H r0 r u hu
        hμ_le
  · have hμ_lt : mu F r0 < mu F r := lt_of_not_ge hμ_le
    by_cases hμ_abs : mu F r < iterate_op d u
    · have hrA_abs : r ∈ extensionSetA F d u := by
        simpa [extensionSetA, Set.mem_setOf_eq] using hμ_abs
      exact
        A_base_statistic_lt_chooseδ_of_absolute (hk := hk) (R := R) (d := d) (hd := hd) IH H r0 r u hu
          hrA_abs
    · have hdu_le : iterate_op d u ≤ mu F r := le_of_not_gt hμ_abs
      exact hardA r0 u hu r hcommon hrA hμ_lt hdu_le

/-!
### RemMulti algebra for the “single-atom separator” bump

When the KSSeparation bump produces a witness of the form `unitMulti i₀ n`, it is useful to cancel
the coordinatewise common prefix between a scaled base `scaleMult m r0` and this single-atom witness.

In the strict regime `m * r0 i₀ < n`, this cancellation removes the entire `i₀`-coordinate from the
scaled base and leaves a remainder witness `unitMulti i₀ (n - m * r0 i₀)`.
-/

private lemma remMultiLeft_scaleMult_unitMulti_of_lt
    (r0 : Multi k) (i₀ : Fin k) (m n : ℕ)
    (hn : m * r0 i₀ < n) :
    remMultiLeft (scaleMult m r0) (unitMulti i₀ n) = scaleMult m (updateMulti r0 i₀ 0) := by
  funext j
  by_cases hj : j = i₀
  · subst j
    simp [remMultiLeft, commonMulti, scaleMult, unitMulti, updateMulti, Nat.min_eq_left (le_of_lt hn)]
  · simp [remMultiLeft, commonMulti, scaleMult, unitMulti, updateMulti, hj]

private lemma remMultiRight_scaleMult_unitMulti_of_lt
    (r0 : Multi k) (i₀ : Fin k) (m n : ℕ)
    (hn : m * r0 i₀ < n) :
    remMultiRight (scaleMult m r0) (unitMulti i₀ n) = unitMulti i₀ (n - m * r0 i₀) := by
  funext j
  by_cases hj : j = i₀
  · subst j
    simp [remMultiRight, commonMulti, scaleMult, unitMulti, Nat.min_eq_left (le_of_lt hn)]
  · simp [remMultiRight, commonMulti, scaleMult, unitMulti, hj]

omit [KSSeparation α] in
private lemma extensionSetA_base_and_statistic_reduce_scaleMult_unitMulti_of_lt
    (H : GridComm F)
    (r0 : Multi k) (i₀ : Fin k) (m n u : ℕ) (hu : 0 < u)
    (hn : m * r0 i₀ < n)
    (hrA : unitMulti i₀ n ∈ extensionSetA_base F d (scaleMult m r0) u) :
    let r0' : Multi k := updateMulti r0 i₀ 0
    let r' : Multi k := unitMulti i₀ (n - m * r0 i₀)
    r' ∈ extensionSetA_base F d (scaleMult m r0') u ∧
      separationStatistic_base R (scaleMult m r0) (unitMulti i₀ n) u hu =
        separationStatistic_base R (scaleMult m r0') r' u hu := by
  intro r0' r'
  have hrA' :
      remMultiRight (scaleMult m r0) (unitMulti i₀ n) ∈
        extensionSetA_base F d (remMultiLeft (scaleMult m r0) (unitMulti i₀ n)) u :=
    (extensionSetA_base_iff_remMulti (H := H) d (scaleMult m r0) (unitMulti i₀ n) u).1 hrA
  have hleft :
      remMultiLeft (scaleMult m r0) (unitMulti i₀ n) = scaleMult m r0' := by
    simpa [r0'] using remMultiLeft_scaleMult_unitMulti_of_lt (k := k) (r0 := r0) (i₀ := i₀) (m := m) (n := n) hn
  have hright :
      remMultiRight (scaleMult m r0) (unitMulti i₀ n) = r' := by
    simpa [r'] using remMultiRight_scaleMult_unitMulti_of_lt (k := k) (r0 := r0) (i₀ := i₀) (m := m) (n := n) hn
  have hrA_reduced : r' ∈ extensionSetA_base F d (scaleMult m r0') u := by
    simpa [hleft, hright] using hrA'
  have hstat :
      separationStatistic_base R (scaleMult m r0) (unitMulti i₀ n) u hu =
        separationStatistic_base R (remMultiLeft (scaleMult m r0) (unitMulti i₀ n))
          (remMultiRight (scaleMult m r0) (unitMulti i₀ n)) u hu := by
    simpa [separationStatistic_base_eq_remMulti (R := R) (r0 := scaleMult m r0) (r := unitMulti i₀ n) (u := u) hu]
  refine ⟨hrA_reduced, ?_⟩
  simpa [hleft, hright] using hstat

omit [KSSeparation α] in
private lemma extensionSetC_base_and_statistic_reduce_scaleMult_unitMulti_of_lt
    (H : GridComm F)
    (r0 : Multi k) (i₀ : Fin k) (m n u : ℕ) (hu : 0 < u)
    (hn : m * r0 i₀ < n)
    (hrC : unitMulti i₀ n ∈ extensionSetC_base F d (scaleMult m r0) u) :
    let r0' : Multi k := updateMulti r0 i₀ 0
    let r' : Multi k := unitMulti i₀ (n - m * r0 i₀)
    r' ∈ extensionSetC_base F d (scaleMult m r0') u ∧
      separationStatistic_base R (scaleMult m r0) (unitMulti i₀ n) u hu =
        separationStatistic_base R (scaleMult m r0') r' u hu := by
  intro r0' r'
  have hrC' :
      remMultiRight (scaleMult m r0) (unitMulti i₀ n) ∈
        extensionSetC_base F d (remMultiLeft (scaleMult m r0) (unitMulti i₀ n)) u :=
    (extensionSetC_base_iff_remMulti (H := H) d (scaleMult m r0) (unitMulti i₀ n) u).1 hrC
  have hleft :
      remMultiLeft (scaleMult m r0) (unitMulti i₀ n) = scaleMult m r0' := by
    simpa [r0'] using remMultiLeft_scaleMult_unitMulti_of_lt (k := k) (r0 := r0) (i₀ := i₀) (m := m) (n := n) hn
  have hright :
      remMultiRight (scaleMult m r0) (unitMulti i₀ n) = r' := by
    simpa [r'] using remMultiRight_scaleMult_unitMulti_of_lt (k := k) (r0 := r0) (i₀ := i₀) (m := m) (n := n) hn
  have hrC_reduced : r' ∈ extensionSetC_base F d (scaleMult m r0') u := by
    simpa [hleft, hright] using hrC'
  have hstat :
      separationStatistic_base R (scaleMult m r0) (unitMulti i₀ n) u hu =
        separationStatistic_base R (remMultiLeft (scaleMult m r0) (unitMulti i₀ n))
          (remMultiRight (scaleMult m r0) (unitMulti i₀ n)) u hu := by
    simpa [separationStatistic_base_eq_remMulti (R := R) (r0 := scaleMult m r0) (r := unitMulti i₀ n) (u := u) hu]
  refine ⟨hrC_reduced, ?_⟩
  simpa [hleft, hright] using hstat

/-!
### Minimal remaining goal (no-common-prefix, “hard regime”)

The helper lemma `chooseδBaseAdmissible_noCommon_A_of_hardCase` shows that the A-side of
`ChooseδBaseAdmissible_noCommon` is already reduced to a single genuinely hard regime:

- `μ(F,r0) < μ(F,r)` (so the base-indexed statistic is positive), and
- `d^u ≤ μ(F,r)` (so `r` is *not* an absolute A-witness at level `u`).

This class packages exactly the two remaining nontrivial inequalities needed to finish the
no-common-prefix base-admissibility proof, without the already-solved easy cases.
-/

/-- **Hard-core interface** for finishing `ChooseδBaseAdmissible_noCommon`.

Providing these two fields is enough to recover full no-common-prefix base admissibility:
- the A-side follows from `hardA` via `chooseδBaseAdmissible_noCommon_A_of_hardCase`;
- the C-side is exactly `hardC` (there are no additional easy subcases on the C-side). -/
class ChooseδBaseAdmissible_noCommon_hard : Prop where
  /-- A-side, restricted to the hard regime `μ(r0) < μ(r)` and `d^u ≤ μ(r)`. -/
  hardA :
    ∀ (r0 : Multi k) (u : ℕ) (hu : 0 < u) (r : Multi k),
      commonMulti r0 r = 0 →
        r ∈ extensionSetA_base F d r0 u →
          mu F r0 < mu F r →
            iterate_op d u ≤ mu F r →
              separationStatistic_base R r0 r u hu < chooseδ hk R d hd
  /-- C-side (already inherently “external”): `μ(r0) ⊕ d^u < μ(r)` implies the strict lower bound. -/
  hardC :
    ∀ (r0 : Multi k) (u : ℕ) (hu : 0 < u) (r : Multi k),
      commonMulti r0 r = 0 →
        r ∈ extensionSetC_base F d r0 u →
          chooseδ hk R d hd < separationStatistic_base R r0 r u hu

/-!
### Progress: the A-side hard regime follows from `NewAtomCommutes` by induction on base support

The remaining A-side goal is genuinely “relative”: it compares an old-grid point `μ(F,r)` to a
shifted boundary `μ(F,r0) ⊕ d^u`.  To connect this to the absolute `chooseδ` bounds (which are
formulated relative to `d^u` alone), we need to compare powers of the boundary:

`(μ(F,r0) ⊕ d^u)^m = μ(F,r0)^m ⊕ d^(u*m)`.

This is exactly `iterate_op_mu_d_decompose`, which requires `NewAtomCommutes F d`.

Under this hypothesis, we can prove the **hard A-side** by a terminating “single-atom separator”
argument: use `KSSeparation` to find a separator `a^n` above `μ(F,r)^m`, then cancel the common
prefix between `scaleMult m r0` and `unitMulti i₀ n`, which strictly decreases the base support.

The C-side strictness remains open (it is the real base-invariance / boundary-exclusion content of
K&S A.3.4).  The lemma below is therefore a **partial** discharge of
`ChooseδBaseAdmissible_noCommon_hard`: it provides the `hardA` field.
-/

private def supportMulti (r : Multi k) : Finset (Fin k) :=
  Finset.univ.filter fun i => r i ≠ 0

private def supportCard (r : Multi k) : ℕ :=
  (supportMulti (k := k) r).card

private lemma supportMulti_scaleMult_of_pos (r : Multi k) (m : ℕ) (hm : 0 < m) :
    supportMulti (k := k) (scaleMult m r) = supportMulti (k := k) r := by
  classical
  ext i
  simp [supportMulti, scaleMult, hm.ne']

private lemma supportCard_scaleMult_of_pos (r : Multi k) (m : ℕ) (hm : 0 < m) :
    supportCard (k := k) (scaleMult m r) = supportCard (k := k) r := by
  simpa [supportCard, supportMulti_scaleMult_of_pos (k := k) (r := r) (m := m) hm]

private lemma supportMulti_updateMulti_zero_subset (r : Multi k) (i : Fin k) :
    supportMulti (k := k) (updateMulti r i 0) ⊆ supportMulti (k := k) r := by
  intro j hj
  have hj' : updateMulti r i 0 j ≠ 0 := by
    simpa [supportMulti] using hj
  by_cases hji : j = i
  · subst hji
    simpa [updateMulti] using hj'
  · have : r j ≠ 0 := by simpa [updateMulti, hji] using hj'
    simp [supportMulti, this]

private lemma supportCard_updateMulti_zero_lt (r : Multi k) (i : Fin k) (hi : r i ≠ 0) :
    supportCard (k := k) (updateMulti r i 0) < supportCard (k := k) r := by
  classical
  have hsubset :
      supportMulti (k := k) (updateMulti r i 0) ⊆ supportMulti (k := k) r :=
    supportMulti_updateMulti_zero_subset (k := k) r i
  have hi_mem : i ∈ supportMulti (k := k) r := by
    simp [supportMulti, hi]
  have hi_not_mem : i ∉ supportMulti (k := k) (updateMulti r i 0) := by
    simp [supportMulti, updateMulti]
  have hne : supportMulti (k := k) (updateMulti r i 0) ≠ supportMulti (k := k) r := by
    intro hEq
    exact hi_not_mem (hEq ▸ hi_mem)
  have hssub : supportMulti (k := k) (updateMulti r i 0) ⊂ supportMulti (k := k) r :=
    ssubset_of_subset_of_ne hsubset hne
  simpa [supportCard] using Finset.card_lt_card hssub

theorem chooseδBaseAdmissible_noCommon_hardA_of_newAtomCommutes
    (IH : GridBridge F) (H : GridComm F) (hcomm : NewAtomCommutes F d) :
    ∀ (r0 : Multi k) (u : ℕ) (hu : 0 < u) (r : Multi k),
      commonMulti r0 r = 0 →
        r ∈ extensionSetA_base F d r0 u →
          mu F r0 < mu F r →
            iterate_op d u ≤ mu F r →
              separationStatistic_base R r0 r u hu < chooseδ hk R d hd := by
  classical
  -- Strong induction on the number of nonzero coordinates in the base `r0`.
  let P : ℕ → Prop := fun n =>
    ∀ (r0 : Multi k), supportCard (k := k) r0 = n →
      ∀ (u : ℕ) (hu : 0 < u) (r : Multi k),
        commonMulti r0 r = 0 →
          r ∈ extensionSetA_base F d r0 u →
            mu F r0 < mu F r →
              iterate_op d u ≤ mu F r →
                separationStatistic_base R r0 r u hu < chooseδ hk R d hd
  have hP : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih r0 hr0_card u hu r hcommon hrA hμ_lt hdu_le
    cases n with
    | zero =>
      -- If the base has empty support, then `r0 = 0`, contradicting `d^u ≤ μ(F,r)` and `r ∈ A_base`.
      have hsupp_empty : supportMulti (k := k) r0 = ∅ := by
        simpa [supportCard] using (Finset.card_eq_zero.mp hr0_card)
      have hr0_zero : r0 = 0 := by
        funext i
        by_contra hi
        have hi' : r0 i ≠ 0 := by simpa using hi
        have : i ∈ supportMulti (k := k) r0 := by
          simp [supportMulti, hi']
        exact (by simpa [hsupp_empty] using this)
      have hμA : mu F r < op (mu F r0) (iterate_op d u) := by
        simpa [extensionSetA_base, Set.mem_setOf_eq] using hrA
      -- With `r0 = 0`, the boundary is `d^u`, so we get `μ(F,r) < d^u`, contradicting `d^u ≤ μ(F,r)`.
      have hμ0 : mu F r0 = ident := by
        -- `r0 = 0` implies `μ(F,r0) = ident`.
        have h0 : (0 : Multi k) = (fun _ : Fin k => 0) := rfl
        simpa [hr0_zero, h0] using (mu_zero (F := F))
      have hμ_lt_du : mu F r < iterate_op d u := by
        simpa [hμ0, op_ident_left] using hμA
      exact (lt_irrefl _ (lt_of_le_of_lt hdu_le hμ_lt_du)).elim
    | succ n =>
      -- Pick a coordinate in the base support.
      have hsupp_pos : 0 < supportCard (k := k) r0 := by
        simpa [hr0_card] using Nat.succ_pos n
      have hsupp_nonempty : (supportMulti (k := k) r0).Nonempty := Finset.card_pos.mp hsupp_pos
      obtain ⟨i₀, hi₀_mem⟩ := hsupp_nonempty
      have hi₀ : r0 i₀ ≠ 0 := by
        simpa [supportMulti] using hi₀_mem
      let a : α := F.atoms i₀
      have ha : ident < a := F.pos i₀

      -- Apply KSSeparation between `μ(F,r)` and the base boundary `μ(F,r0) ⊕ d^u`.
      have hμ_bound : mu F r < op (mu F r0) (iterate_op d u) := by
        simpa [extensionSetA_base, Set.mem_setOf_eq] using hrA
      have hμ_r_pos : ident < mu F r :=
        lt_of_le_of_lt (ident_le (mu F r0)) hμ_lt
      have hd_pow_pos : ident < iterate_op d u := iterate_op_pos d hd u hu
      have hop_pos : ident < op (mu F r0) (iterate_op d u) := by
        have h1 : op (mu F r0) ident < op (mu F r0) (iterate_op d u) :=
          op_strictMono_right (mu F r0) hd_pow_pos
        have h2 : mu F r0 < op (mu F r0) (iterate_op d u) := by
          rwa [op_ident_right] at h1
        exact lt_of_le_of_lt (ident_le (mu F r0)) h2
      obtain ⟨n_sep, m, hm_pos, h_gap, h_in_bound⟩ :=
        KSSeparation.separation (a := a) (x := mu F r) (y := op (mu F r0) (iterate_op d u))
          ha hμ_r_pos hop_pos hμ_bound
      have huM_pos : 0 < u * m := Nat.mul_pos hu hm_pos

      -- Convert the separator inequality to the k-grid via `GridBridge`.
      have hμ_gap_grid : mu F (scaleMult m r) < mu F (unitMulti i₀ n_sep) := by
        have hμ_left : mu F (scaleMult m r) = iterate_op (mu F r) m := IH.bridge r m
        have hμ_right : mu F (unitMulti i₀ n_sep) = iterate_op a n_sep := by
          simpa [a] using (mu_unitMulti F i₀ n_sep)
        simpa [hμ_left, hμ_right] using h_gap
      have hμ_scaled_base_lt_scaled_r : mu F (scaleMult m r0) < mu F (scaleMult m r) := by
        have hiter :
            iterate_op (mu F r0) m < iterate_op (mu F r) m :=
          iterate_op_strictMono_base m hm_pos (mu F r0) (mu F r) hμ_lt
        have hμ_left : mu F (scaleMult m r0) = iterate_op (mu F r0) m := IH.bridge r0 m
        have hμ_right : mu F (scaleMult m r) = iterate_op (mu F r) m := IH.bridge r m
        simpa [hμ_left, hμ_right] using hiter
      have hμ_scaled_base_lt_sep :
          mu F (scaleMult m r0) < mu F (unitMulti i₀ n_sep) :=
        lt_trans hμ_scaled_base_lt_scaled_r hμ_gap_grid

      -- The original base statistic equals the scaled one.
      have hstat_scale :
          separationStatistic_base R (scaleMult m r0) (scaleMult m r) (u * m) huM_pos =
            separationStatistic_base R r0 r u hu :=
        separationStatistic_base_scaleMult (R := R) (r0 := r0) (r := r) (u := u) (m := m) hu hm_pos

      -- The scaled statistic is strictly below the separator statistic.
      have hθ_lt :
          R.Θ_grid ⟨mu F (scaleMult m r), mu_mem_kGrid F (scaleMult m r)⟩ <
            R.Θ_grid ⟨mu F (unitMulti i₀ n_sep), mu_mem_kGrid F (unitMulti i₀ n_sep)⟩ :=
        R.strictMono hμ_gap_grid
      have hstat_lt_sep :
          separationStatistic_base R (scaleMult m r0) (scaleMult m r) (u * m) huM_pos <
            separationStatistic_base R (scaleMult m r0) (unitMulti i₀ n_sep) (u * m) huM_pos := by
        have huM_pos_real : (0 : ℝ) < (u * m : ℕ) := Nat.cast_pos.mpr huM_pos
        -- Subtract the same base value and divide by the positive denominator.
        have hnum_lt :
            (R.Θ_grid ⟨mu F (scaleMult m r), mu_mem_kGrid F (scaleMult m r)⟩ -
                R.Θ_grid ⟨mu F (scaleMult m r0), mu_mem_kGrid F (scaleMult m r0)⟩) <
              (R.Θ_grid ⟨mu F (unitMulti i₀ n_sep), mu_mem_kGrid F (unitMulti i₀ n_sep)⟩ -
                R.Θ_grid ⟨mu F (scaleMult m r0), mu_mem_kGrid F (scaleMult m r0)⟩) := by
          linarith
        have := div_lt_div_of_pos_right hnum_lt huM_pos_real
        simpa [separationStatistic_base] using this

      -- Use `NewAtomCommutes` to interpret the upper bound `a^n ≤ (μ(r0) ⊕ d^u)^m` as a base-indexed bound
      -- at `(scaleMult m r0, u*m)`.
      have hμ_sep_le_boundary :
          mu F (unitMulti i₀ n_sep) ≤ op (mu F (scaleMult m r0)) (iterate_op d (u * m)) := by
        -- Rewrite the RHS `(μ(r0) ⊕ d^u)^m` using `iterate_op_mu_d_decompose`.
        have hμ_unit : mu F (unitMulti i₀ n_sep) = iterate_op a n_sep := by
          simpa [a] using (mu_unitMulti F i₀ n_sep)
        have h_decomp :
            iterate_op (op (mu F r0) (iterate_op d u)) m =
              op (iterate_op (mu F r0) m) (iterate_op d (u * m)) :=
          iterate_op_mu_d_decompose (F := F) (d := d) hcomm r0 u m
        have h_bridge : iterate_op (mu F r0) m = mu F (scaleMult m r0) :=
          (IH.bridge r0 m).symm
        -- Now assemble.
        have : iterate_op a n_sep ≤ op (mu F (scaleMult m r0)) (iterate_op d (u * m)) := by
          -- `h_in_bound : a^n ≤ (μ(r0) ⊕ d^u)^m`
          -- and `(μ(r0) ⊕ d^u)^m = μ(r0)^m ⊕ d^(u*m)`.
          simpa [h_decomp, h_bridge] using h_in_bound
        simpa [hμ_unit] using this

      -- If we have an exact base-indexed B-witness at the scaled level, the separator statistic is exactly `chooseδ`.
      by_cases hEq :
          mu F (unitMulti i₀ n_sep) = op (mu F (scaleMult m r0)) (iterate_op d (u * m))
      · have hrB_scaled : unitMulti i₀ n_sep ∈ extensionSetB_base F d (scaleMult m r0) (u * m) := by
          simpa [extensionSetB_base, Set.mem_setOf_eq] using hEq
        have hsep_eq :
            separationStatistic_base R (scaleMult m r0) (unitMulti i₀ n_sep) (u * m) huM_pos =
              chooseδ hk R d hd :=
          separationStatistic_base_eq_chooseδ_of_B_base_witness (R := R) (hk := hk) (IH := IH) (H := H) (d := d)
            (hd := hd) (r0 := scaleMult m r0) (rB := unitMulti i₀ n_sep) (u := u * m) (hu := huM_pos) hrB_scaled
        have hscaled_lt :
            separationStatistic_base R (scaleMult m r0) (scaleMult m r) (u * m) huM_pos <
              chooseδ hk R d hd := by
          simpa [hsep_eq] using hstat_lt_sep
        -- Translate back to the original statistic.
        simpa [hstat_scale] using hscaled_lt
      · -- Otherwise the separator lies strictly in `A_base` at the scaled instance.
        have hμ_sep_lt_boundary :
            mu F (unitMulti i₀ n_sep) < op (mu F (scaleMult m r0)) (iterate_op d (u * m)) :=
          lt_of_le_of_ne hμ_sep_le_boundary hEq
        have hrA_sep :
            unitMulti i₀ n_sep ∈ extensionSetA_base F d (scaleMult m r0) (u * m) := by
          simpa [extensionSetA_base, Set.mem_setOf_eq] using hμ_sep_lt_boundary
        -- Establish the strict overlap `m*r0[i₀] < n` needed for the `remMulti` reduction.
        have hn : m * r0 i₀ < n_sep := by
          -- `a^(m*r0[i₀]) ≤ μ(scaleMult m r0) < a^n`.
          have hiter_le : iterate_op (F.atoms i₀) ((scaleMult m r0) i₀) ≤ mu F (scaleMult m r0) :=
            iterate_le_mu F (scaleMult m r0) i₀
          have hiter_lt : iterate_op (F.atoms i₀) ((scaleMult m r0) i₀) <
              mu F (unitMulti i₀ n_sep) :=
            lt_of_le_of_lt hiter_le hμ_scaled_base_lt_sep
          have hμ_unit : mu F (unitMulti i₀ n_sep) = iterate_op (F.atoms i₀) n_sep := by
            simpa using (mu_unitMulti F i₀ n_sep)
          have hpow_lt :
              iterate_op (F.atoms i₀) ((scaleMult m r0) i₀) < iterate_op (F.atoms i₀) n_sep := by
            simpa [hμ_unit] using hiter_lt
          -- Convert the exponent inequality via strict monotonicity of iterates of `a`.
          by_contra hnot
          have hle : n_sep ≤ (scaleMult m r0) i₀ := Nat.le_of_not_gt hnot
          have hmono : Monotone (iterate_op (F.atoms i₀)) := (iterate_op_strictMono (F.atoms i₀) (F.pos i₀)).monotone
          have : iterate_op (F.atoms i₀) n_sep ≤ iterate_op (F.atoms i₀) ((scaleMult m r0) i₀) :=
            hmono hle
          exact (not_lt_of_ge this) hpow_lt

        -- Reduce the separator to a smaller base by cancelling the common prefix.
        let r0' : Multi k := updateMulti r0 i₀ 0
        let r' : Multi k := unitMulti i₀ (n_sep - m * r0 i₀)
        have hred :
            r' ∈ extensionSetA_base F d (scaleMult m r0') (u * m) ∧
              separationStatistic_base R (scaleMult m r0) (unitMulti i₀ n_sep) (u * m) huM_pos =
                separationStatistic_base R (scaleMult m r0') r' (u * m) huM_pos := by
          simpa [r0', r'] using
            extensionSetA_base_and_statistic_reduce_scaleMult_unitMulti_of_lt (R := R) (F := F) (d := d) (H := H)
              (r0 := r0) (i₀ := i₀) (m := m) (n := n_sep) (u := u * m) (hu := huM_pos) hn hrA_sep
        rcases hred with ⟨hrA_reduced, hstat_reduced⟩
        have hcommon' : commonMulti (scaleMult m r0') r' = 0 := by
          funext j
          by_cases hj : j = i₀
          · subst hj
            simp [r0', r', commonMulti, scaleMult, unitMulti, updateMulti]
          · simp [r0', r', commonMulti, scaleMult, unitMulti, updateMulti, hj]
        -- Bound the reduced separator statistic using the induction hypothesis (or easy cases).
        have hsep_lt :
            separationStatistic_base R (scaleMult m r0') r' (u * m) huM_pos < chooseδ hk R d hd := by
          by_cases hμ_le' : mu F r' ≤ mu F (scaleMult m r0')
          · -- Statistic is non-positive.
            exact
              A_base_statistic_lt_chooseδ_of_mu_le (hk := hk) (R := R) (d := d) (hd := hd) IH H
                (r0 := scaleMult m r0') (r := r') (u := u * m) (hu := huM_pos) hμ_le'
          · have hμ_lt' : mu F (scaleMult m r0') < mu F r' := lt_of_not_ge hμ_le'
            by_cases hμ_abs' : mu F r' < iterate_op d (u * m)
            · have hrA_abs' : r' ∈ extensionSetA F d (u * m) := by
                simpa [extensionSetA, Set.mem_setOf_eq] using hμ_abs'
              exact
                A_base_statistic_lt_chooseδ_of_absolute (hk := hk) (R := R) (d := d) (hd := hd) IH H
                  (r0 := scaleMult m r0') (r := r') (u := u * m) (hu := huM_pos) hrA_abs'
            · have hdu_le' : iterate_op d (u * m) ≤ mu F r' := le_of_not_gt hμ_abs'
              -- Apply the strong-induction hypothesis at the smaller base.
              have hsupport_lt :
                  supportCard (k := k) (scaleMult m r0') < supportCard (k := k) r0 := by
                -- `updateMulti` removes a nonzero coordinate, and positive scaling preserves support.
                have hcard_update : supportCard (k := k) r0' < supportCard (k := k) r0 :=
                  supportCard_updateMulti_zero_lt (k := k) (r := r0) (i := i₀) hi₀
                have hcard_scale :
                    supportCard (k := k) (scaleMult m r0') = supportCard (k := k) r0' :=
                  supportCard_scaleMult_of_pos (k := k) (r := r0') (m := m) hm_pos
                simpa [hcard_scale] using hcard_update
              have hP_small : P (supportCard (k := k) (scaleMult m r0')) :=
                ih (supportCard (k := k) (scaleMult m r0')) (by
                  simpa [hr0_card] using hsupport_lt)
              exact
                hP_small (scaleMult m r0') rfl (u * m) huM_pos r' hcommon' hrA_reduced hμ_lt' hdu_le'
        -- Now the scaled witness is strictly below the reduced separator, hence below `chooseδ`.
        have hscaled_lt :
            separationStatistic_base R (scaleMult m r0) (scaleMult m r) (u * m) huM_pos < chooseδ hk R d hd :=
          lt_trans hstat_lt_sep (by simpa [hstat_reduced.symm] using hsep_lt)
        simpa [hstat_scale] using hscaled_lt

  intro r0 u hu r hcommon hrA hμ_lt hdu_le
  exact hP (supportCard (k := k) r0) r0 rfl u hu r hcommon hrA hμ_lt hdu_le

theorem chooseδBaseAdmissible_noCommon_hardC_of_newAtomCommutes_of_C_strict0
    (IH : GridBridge F) (H : GridComm F) (hcomm : NewAtomCommutes F d)
    (hC_strict0 :
      ∀ (r : Multi k) (u : ℕ) (hu : 0 < u),
        r ∈ extensionSetC F d u → chooseδ hk R d hd < separationStatistic R r u hu) :
    ∀ (r0 : Multi k) (u : ℕ) (hu : 0 < u) (r : Multi k),
      commonMulti r0 r = 0 →
        r ∈ extensionSetC_base F d r0 u →
          chooseδ hk R d hd < separationStatistic_base R r0 r u hu := by
  classical
  -- Strong induction on the number of nonzero coordinates in the base `r0`.
  let P : ℕ → Prop := fun n =>
    ∀ (r0 : Multi k), supportCard (k := k) r0 = n →
      ∀ (u : ℕ) (hu : 0 < u) (r : Multi k),
        commonMulti r0 r = 0 →
          r ∈ extensionSetC_base F d r0 u →
            chooseδ hk R d hd < separationStatistic_base R r0 r u hu
  have hP : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih r0 hr0_card u hu r hcommon hrC
    cases n with
    | zero =>
      -- `supportCard r0 = 0` implies `r0 = 0`, so this is the absolute C-side strictness hypothesis.
      have hsupp_empty : supportMulti (k := k) r0 = ∅ := by
        simpa [supportCard] using (Finset.card_eq_zero.mp hr0_card)
      have hr0_zero : r0 = 0 := by
        funext i
        by_contra hi
        have hi' : r0 i ≠ 0 := by simpa using hi
        have : i ∈ supportMulti (k := k) r0 := by
          simp [supportMulti, hi']
        exact (by simpa [hsupp_empty] using this)
      have hrC0 : r ∈ extensionSetC_base F d (0 : Multi k) u := by
        simpa [hr0_zero] using hrC
      have hrC_abs : r ∈ extensionSetC F d u := by
        -- `C_base(0,u) = C(u)`.
        simpa [extensionSetC_base_zero] using hrC0
      have hδ_lt_abs : chooseδ hk R d hd < separationStatistic R r u hu :=
        hC_strict0 r u hu hrC_abs
      -- `separationStatistic_base` agrees with `separationStatistic` at base `0`.
      have hθ0 : R.Θ_grid ⟨mu F (0 : Multi k), mu_mem_kGrid F (0 : Multi k)⟩ = 0 := by
        have h0 : (0 : Multi k) = (fun _ : Fin k => 0) := rfl
        have hμ0 : mu F (0 : Multi k) = ident := by
          simpa [h0] using (mu_zero (F := F))
        have hsub :
            (⟨mu F (0 : Multi k), mu_mem_kGrid F (0 : Multi k)⟩ : {x // x ∈ kGrid F}) =
              ⟨ident, ident_mem_kGrid F⟩ := by
          ext; simpa [hμ0]
        simpa [hsub] using R.ident_eq_zero
      have hstat0 :
          separationStatistic_base R (0 : Multi k) r u hu = separationStatistic R r u hu := by
        simp [separationStatistic_base, separationStatistic, hθ0]
      simpa [hr0_zero, hstat0] using hδ_lt_abs
    | succ n =>
      -- If the boundary is on the old grid (a base-indexed B-witness exists), strictness is immediate.
      by_cases hB_base : ∃ rB : Multi k, rB ∈ extensionSetB_base F d r0 u
      · have hAd :
            AdmissibleDelta_base (k := k) (F := F) (R₀ := R) (d₀ := d) (chooseδ hk R d hd) r0 u hu :=
          admissibleDelta_base_chooseδ_of_B_base_witness (R := R) (F := F) (hk := hk) (IH := IH) (H := H)
            (d := d) (hd := hd) (r0 := r0) (u := u) (hu := hu) hB_base
        exact hAd.2 r hrC
      · -- External case: use a separator at the scaled instance and cancel a base coordinate.
        -- Pick a coordinate in the base support.
        have hsupp_pos : 0 < supportCard (k := k) r0 := by
          simpa [hr0_card] using Nat.succ_pos n
        have hsupp_nonempty : (supportMulti (k := k) r0).Nonempty := Finset.card_pos.mp hsupp_pos
        obtain ⟨i₀, hi₀_mem⟩ := hsupp_nonempty
        have hi₀ : r0 i₀ ≠ 0 := by
          simpa [supportMulti] using hi₀_mem
        let a : α := F.atoms i₀
        have ha : ident < a := F.pos i₀

        have hμ_bound_lt : op (mu F r0) (iterate_op d u) < mu F r := by
          simpa [extensionSetC_base, Set.mem_setOf_eq] using hrC
        have hd_pow_pos : ident < iterate_op d u := iterate_op_pos d hd u hu
        have hop_pos : ident < op (mu F r0) (iterate_op d u) := by
          have h1 : op (mu F r0) ident < op (mu F r0) (iterate_op d u) :=
            op_strictMono_right (mu F r0) hd_pow_pos
          have h2 : mu F r0 < op (mu F r0) (iterate_op d u) := by
            rwa [op_ident_right] at h1
          exact lt_of_le_of_lt (ident_le (mu F r0)) h2
        have hμ_r_pos : ident < mu F r :=
          lt_trans hop_pos hμ_bound_lt

        obtain ⟨n_sep, m, hm_pos, h_gap, h_in_y⟩ :=
          KSSeparation.separation (a := a) (x := op (mu F r0) (iterate_op d u)) (y := mu F r)
            ha hop_pos hμ_r_pos hμ_bound_lt
        have huM_pos : 0 < u * m := Nat.mul_pos hu hm_pos

        -- Convert the separator inequalities to the k-grid via `GridBridge` and `NewAtomCommutes`.
        have h_decomp :
            iterate_op (op (mu F r0) (iterate_op d u)) m =
              op (iterate_op (mu F r0) m) (iterate_op d (u * m)) :=
          iterate_op_mu_d_decompose (F := F) (d := d) hcomm r0 u m
        have h_bridge_r0 : iterate_op (mu F r0) m = mu F (scaleMult m r0) :=
          (IH.bridge r0 m).symm
        have hμ_boundary_scaled :
            op (mu F (scaleMult m r0)) (iterate_op d (u * m)) = iterate_op (op (mu F r0) (iterate_op d u)) m := by
          simp [h_decomp, h_bridge_r0]

        have hμ_sep_gt_boundary :
            op (mu F (scaleMult m r0)) (iterate_op d (u * m)) < mu F (unitMulti i₀ n_sep) := by
          have hμ_unit : mu F (unitMulti i₀ n_sep) = iterate_op a n_sep := by
            simpa [a] using (mu_unitMulti F i₀ n_sep)
          -- `boundary^m < a^n`
          have : iterate_op (op (mu F r0) (iterate_op d u)) m < iterate_op a n_sep := h_gap
          simpa [hμ_boundary_scaled, hμ_unit]
        have hrC_sep :
            unitMulti i₀ n_sep ∈ extensionSetC_base F d (scaleMult m r0) (u * m) := by
          simpa [extensionSetC_base, Set.mem_setOf_eq] using hμ_sep_gt_boundary

        -- The separator lies below `μ(F,r)^m` (possibly equal), so its statistic is ≤ the scaled statistic of `r`.
        have hμ_sep_le_scaled_r : mu F (unitMulti i₀ n_sep) ≤ mu F (scaleMult m r) := by
          have hμ_unit : mu F (unitMulti i₀ n_sep) = iterate_op a n_sep := by
            simpa [a] using (mu_unitMulti F i₀ n_sep)
          have hμ_scaled : mu F (scaleMult m r) = iterate_op (mu F r) m := IH.bridge r m
          -- `a^n ≤ (μr)^m`
          have : iterate_op a n_sep ≤ iterate_op (mu F r) m := h_in_y
          simpa [hμ_unit, hμ_scaled] using this
        have hθ_sep_le_scaled_r :
            R.Θ_grid ⟨mu F (unitMulti i₀ n_sep), mu_mem_kGrid F (unitMulti i₀ n_sep)⟩ ≤
              R.Θ_grid ⟨mu F (scaleMult m r), mu_mem_kGrid F (scaleMult m r)⟩ :=
          R.strictMono.monotone hμ_sep_le_scaled_r
        have hstat_sep_le_scaled_r :
            separationStatistic_base R (scaleMult m r0) (unitMulti i₀ n_sep) (u * m) huM_pos ≤
              separationStatistic_base R (scaleMult m r0) (scaleMult m r) (u * m) huM_pos := by
          have huM_pos_real : (0 : ℝ) < (u * m : ℕ) := Nat.cast_pos.mpr huM_pos
          have hnum_le :
              (R.Θ_grid ⟨mu F (unitMulti i₀ n_sep), mu_mem_kGrid F (unitMulti i₀ n_sep)⟩ -
                    R.Θ_grid ⟨mu F (scaleMult m r0), mu_mem_kGrid F (scaleMult m r0)⟩) ≤
                (R.Θ_grid ⟨mu F (scaleMult m r), mu_mem_kGrid F (scaleMult m r)⟩ -
                    R.Θ_grid ⟨mu F (scaleMult m r0), mu_mem_kGrid F (scaleMult m r0)⟩) := by
            linarith
          have := div_le_div_of_nonneg_right hnum_le huM_pos_real.le
          simpa [separationStatistic_base] using this

        -- Establish the strict overlap `m*r0[i₀] < n` needed for the `remMulti` reduction.
        have hn : m * r0 i₀ < n_sep := by
          have hd_pow_posM : ident < iterate_op d (u * m) := iterate_op_pos d hd (u * m) huM_pos
          have hμ_lt_boundary :
              mu F (scaleMult m r0) < op (mu F (scaleMult m r0)) (iterate_op d (u * m)) := by
            have h :=
              op_strictMono_right (mu F (scaleMult m r0)) (show ident < iterate_op d (u * m) from hd_pow_posM)
            simpa [op_ident_right] using h
          have hboundary_lt_unit :
              op (mu F (scaleMult m r0)) (iterate_op d (u * m)) < mu F (unitMulti i₀ n_sep) := by
            simpa [extensionSetC_base, Set.mem_setOf_eq] using hrC_sep
          have hμ_scale_lt_unit : mu F (scaleMult m r0) < mu F (unitMulti i₀ n_sep) :=
            lt_trans hμ_lt_boundary hboundary_lt_unit
          have hiter_le :
              iterate_op (F.atoms i₀) ((scaleMult m r0) i₀) ≤ mu F (scaleMult m r0) :=
            iterate_le_mu F (scaleMult m r0) i₀
          have hiter_lt_unit :
              iterate_op (F.atoms i₀) ((scaleMult m r0) i₀) < mu F (unitMulti i₀ n_sep) :=
            lt_of_le_of_lt hiter_le hμ_scale_lt_unit
          have hμ_unit : mu F (unitMulti i₀ n_sep) = iterate_op (F.atoms i₀) n_sep := by
            simpa using (mu_unitMulti F i₀ n_sep)
          have hpow_lt :
              iterate_op (F.atoms i₀) ((scaleMult m r0) i₀) < iterate_op (F.atoms i₀) n_sep := by
            simpa [hμ_unit] using hiter_lt_unit
          have hn' : (scaleMult m r0) i₀ < n_sep := by
            by_contra hnot
            have hle : n_sep ≤ (scaleMult m r0) i₀ := Nat.le_of_not_gt hnot
            have hmono : Monotone (iterate_op (F.atoms i₀)) :=
              (iterate_op_strictMono (F.atoms i₀) (F.pos i₀)).monotone
            have : iterate_op (F.atoms i₀) n_sep ≤ iterate_op (F.atoms i₀) ((scaleMult m r0) i₀) :=
              hmono hle
            exact (not_lt_of_ge this) hpow_lt
          simpa [scaleMult] using hn'

        -- Reduce the separator to a smaller base by cancelling the common prefix.
        let r0' : Multi k := updateMulti r0 i₀ 0
        let r' : Multi k := unitMulti i₀ (n_sep - m * r0 i₀)
        have hred :
            r' ∈ extensionSetC_base F d (scaleMult m r0') (u * m) ∧
              separationStatistic_base R (scaleMult m r0) (unitMulti i₀ n_sep) (u * m) huM_pos =
                separationStatistic_base R (scaleMult m r0') r' (u * m) huM_pos := by
          simpa [r0', r'] using
            extensionSetC_base_and_statistic_reduce_scaleMult_unitMulti_of_lt (R := R) (F := F) (d := d) (H := H)
              (r0 := r0) (i₀ := i₀) (m := m) (n := n_sep) (u := u * m) (hu := huM_pos) hn hrC_sep
        rcases hred with ⟨hrC_reduced, hstat_reduced⟩
        have hcommon' : commonMulti (scaleMult m r0') r' = 0 := by
          funext j
          by_cases hj : j = i₀
          · subst hj
            simp [r0', r', commonMulti, scaleMult, unitMulti, updateMulti]
          · simp [r0', r', commonMulti, scaleMult, unitMulti, updateMulti, hj]

        -- Apply the strong-induction hypothesis at the smaller base.
        have hsupport_lt :
            supportCard (k := k) (scaleMult m r0') < supportCard (k := k) r0 := by
          have hcard_update : supportCard (k := k) r0' < supportCard (k := k) r0 :=
            supportCard_updateMulti_zero_lt (k := k) (r := r0) (i := i₀) hi₀
          have hcard_scale :
              supportCard (k := k) (scaleMult m r0') = supportCard (k := k) r0' :=
            supportCard_scaleMult_of_pos (k := k) (r := r0') (m := m) hm_pos
          simpa [hcard_scale] using hcard_update
        have hP_small : P (supportCard (k := k) (scaleMult m r0')) :=
          ih (supportCard (k := k) (scaleMult m r0')) (by
            simpa [hr0_card] using hsupport_lt)
        have hδ_lt_sep_reduced :
            chooseδ hk R d hd < separationStatistic_base R (scaleMult m r0') r' (u * m) huM_pos :=
          hP_small (scaleMult m r0') rfl (u * m) huM_pos r' hcommon' hrC_reduced
        have hδ_lt_sep :
            chooseδ hk R d hd < separationStatistic_base R (scaleMult m r0) (unitMulti i₀ n_sep) (u * m) huM_pos := by
          simpa [hstat_reduced] using hδ_lt_sep_reduced
        have hδ_lt_scaled_r :
            chooseδ hk R d hd < separationStatistic_base R (scaleMult m r0) (scaleMult m r) (u * m) huM_pos :=
          lt_of_lt_of_le hδ_lt_sep hstat_sep_le_scaled_r

        -- Translate back to the original statistic via scaling.
        have hstat_scale :
            separationStatistic_base R (scaleMult m r0) (scaleMult m r) (u * m) huM_pos =
              separationStatistic_base R r0 r u hu :=
          separationStatistic_base_scaleMult (R := R) (r0 := r0) (r := r) (u := u) (m := m) hu hm_pos
        simpa [hstat_scale] using hδ_lt_scaled_r

  intro r0 u hu r hcommon hrC
  exact hP (supportCard (k := k) r0) r0 rfl u hu r hcommon hrC

theorem chooseδBaseAdmissible_noCommon_hard_of_newAtomCommutes_of_C_strict0
    (IH : GridBridge F) (H : GridComm F) (hcomm : NewAtomCommutes F d)
    (hC_strict0 :
      ∀ (r : Multi k) (u : ℕ) (hu : 0 < u),
        r ∈ extensionSetC F d u → chooseδ hk R d hd < separationStatistic R r u hu) :
    ChooseδBaseAdmissible_noCommon_hard (α := α) (hk := hk) (R := R) (F := F) (d := d)
      (hd := hd) := by
  refine ⟨?_, ?_⟩
  · exact
      chooseδBaseAdmissible_noCommon_hardA_of_newAtomCommutes (α := α) (hk := hk) (R := R) (F := F)
        (d := d) (hd := hd) (IH := IH) (H := H) (hcomm := hcomm)
  · exact
      chooseδBaseAdmissible_noCommon_hardC_of_newAtomCommutes_of_C_strict0 (α := α) (hk := hk) (R := R)
        (F := F) (d := d) (hd := hd) (IH := IH) (H := H) (hcomm := hcomm) (hC_strict0 := hC_strict0)

omit [KSSeparation α] in
theorem chooseδBaseAdmissible_noCommon_hard_of_chooseδBaseAdmissible_noCommon
    (h :
      ChooseδBaseAdmissible_noCommon (hk := hk) (R := R) (F := F) (d := d) (hd := hd)) :
    ChooseδBaseAdmissible_noCommon_hard (α := α) (hk := hk) (R := R) (F := F) (d := d) (hd := hd) := by
  refine ⟨?_, ?_⟩
  · intro r0 u hu r hcommon hrA _hμ_lt _hdu_le
    exact (h.base_noCommon r0 u hu).1 r hcommon hrA
  · intro r0 u hu r hcommon hrC
    exact (h.base_noCommon r0 u hu).2 r hcommon hrC

theorem chooseδBaseAdmissible_noCommon_of_chooseδBaseAdmissible_noCommon_hard
    (IH : GridBridge F) (H : GridComm F)
    (h :
      ChooseδBaseAdmissible_noCommon_hard (α := α) (hk := hk) (R := R) (F := F) (d := d)
        (hd := hd)) :
    ChooseδBaseAdmissible_noCommon (hk := hk) (R := R) (F := F) (d := d) (hd := hd) := by
  refine ⟨?_⟩
  intro r0 u hu
  refine ⟨?_, ?_⟩
  · -- A-side: reduce to the hard regime.
    exact
      chooseδBaseAdmissible_noCommon_A_of_hardCase (α := α) (hk := hk) (R := R) (d := d) (hd := hd)
        (IH := IH) (H := H) (hardA := h.hardA) r0 u hu
  · -- C-side: exactly the hardC field.
    intro r hcommon hrC
    exact h.hardC r0 u hu r hcommon hrC

theorem chooseδBaseAdmissible_noCommon_iff_chooseδBaseAdmissible_noCommon_hard
    (IH : GridBridge F) (H : GridComm F) :
    ChooseδBaseAdmissible_noCommon (hk := hk) (R := R) (F := F) (d := d) (hd := hd) ↔
      ChooseδBaseAdmissible_noCommon_hard (α := α) (hk := hk) (R := R) (F := F) (d := d)
        (hd := hd) := by
  constructor
  · intro hNoCommon
    exact
      chooseδBaseAdmissible_noCommon_hard_of_chooseδBaseAdmissible_noCommon
        (α := α) (hk := hk) (R := R) (F := F) (d := d) (hd := hd) hNoCommon
  · intro hHard
    exact
      chooseδBaseAdmissible_noCommon_of_chooseδBaseAdmissible_noCommon_hard
        (α := α) (hk := hk) (R := R) (F := F) (d := d) (hd := hd) (IH := IH) (H := H) hHard

theorem chooseδBaseAdmissible_of_newAtomCommutes_of_C_strict0
    (IH : GridBridge F) (H : GridComm F) (hcomm : NewAtomCommutes F d)
    (hC_strict0 :
      ∀ (r : Multi k) (u : ℕ) (hu : 0 < u),
        r ∈ extensionSetC F d u → chooseδ hk R d hd < separationStatistic R r u hu) :
    ChooseδBaseAdmissible (hk := hk) (R := R) (F := F) (d := d) (hd := hd) := by
  have hHard :
      ChooseδBaseAdmissible_noCommon_hard (α := α) (hk := hk) (R := R) (F := F) (d := d)
        (hd := hd) :=
    chooseδBaseAdmissible_noCommon_hard_of_newAtomCommutes_of_C_strict0 (α := α) (hk := hk) (R := R)
      (F := F) (d := d) (hd := hd) (IH := IH) (H := H) (hcomm := hcomm) (hC_strict0 := hC_strict0)
  have hNoCommon :
      ChooseδBaseAdmissible_noCommon (hk := hk) (R := R) (F := F) (d := d) (hd := hd) :=
    chooseδBaseAdmissible_noCommon_of_chooseδBaseAdmissible_noCommon_hard (α := α) (hk := hk) (R := R)
      (F := F) (d := d) (hd := hd) (IH := IH) (H := H) hHard
  exact chooseδBaseAdmissible_of_chooseδBaseAdmissible_noCommon (hk := hk) (R := R) (F := F) (d := d)
    (hd := hd) (H := H) hNoCommon

/-- Convenience wrapper: if you assume `NewAtomCommutes` and the **strict** separation strengthening
`KSSeparationStrict`, then the C-side strictness hypothesis `AppendixA34Extra.C_strict0` is automatic. -/
theorem chooseδBaseAdmissible_of_newAtomCommutes_of_KSSeparationStrict
    (IH : GridBridge F) (H : GridComm F) (hcomm : NewAtomCommutes F d)
    [KSSeparationStrict α] :
    ChooseδBaseAdmissible (hk := hk) (R := R) (F := F) (d := d) (hd := hd) := by
  have hC_strict0 :=
    chooseδ_C_strict0_of_KSSeparationStrict (α := α) (hk := hk) (R := R) (IH := IH) (H := H)
      (d := d) (hd := hd)
  exact
    chooseδBaseAdmissible_of_newAtomCommutes_of_C_strict0 (α := α) (hk := hk) (R := R) (F := F)
      (d := d) (hd := hd) (IH := IH) (H := H) (hcomm := hcomm) (hC_strict0 := hC_strict0)

omit [KSSeparation α] in
/-- Convenience wrapper: if you assume `NewAtomCommutes`, `KSSeparation`, and `DenselyOrdered α`,
then the strict separation used on the C-side is automatic. -/
theorem chooseδBaseAdmissible_of_newAtomCommutes_of_KSSeparation_of_denselyOrdered
    (IH : GridBridge F) (H : GridComm F) (hcomm : NewAtomCommutes F d)
    [KSSeparation α] [DenselyOrdered α] :
    ChooseδBaseAdmissible (hk := hk) (R := R) (F := F) (d := d) (hd := hd) := by
  letI : KSSeparationStrict α :=
    KSSeparation.toKSSeparationStrict_of_denselyOrdered (α := α)
  exact
    chooseδBaseAdmissible_of_newAtomCommutes_of_KSSeparationStrict (α := α) (hk := hk) (R := R)
      (F := F) (d := d) (hd := hd) (IH := IH) (H := H) hcomm

theorem chooseδBaseAdmissible_of_appendixA34Extra
    (IH : GridBridge F) (H : GridComm F)
    (hExtra : AppendixA34Extra (α := α) hk (R := R) (F := F) d hd) :
    ChooseδBaseAdmissible (hk := hk) (R := R) (F := F) (d := d) (hd := hd) := by
  exact
    chooseδBaseAdmissible_of_newAtomCommutes_of_C_strict0 (α := α) (hk := hk) (R := R) (F := F)
      (d := d) (hd := hd) (IH := IH) (H := H) (hcomm := hExtra.newAtomCommutes)
      (hC_strict0 := hExtra.C_strict0)

theorem extend_grid_rep_with_atom_of_appendixA34Extra
    (IH : GridBridge F) (H : GridComm F)
    (hExtra : AppendixA34Extra (α := α) hk (R := R) (F := F) d hd) :
      ∃ (F' : AtomFamily α (k + 1)),
      (∀ i : Fin k, F'.atoms ⟨i, Nat.lt_succ_of_lt i.is_lt⟩ = F.atoms i) ∧
      F'.atoms ⟨k, Nat.lt_succ_self k⟩ = d ∧
      ∃ (R' : MultiGridRep F'),
        (∀ r_old : Multi k, ∀ t : ℕ,
          R'.Θ_grid ⟨mu F' (joinMulti r_old t), mu_mem_kGrid F' (joinMulti r_old t)⟩ =
          R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * chooseδ hk R d hd) := by
  have hBase :
      ChooseδBaseAdmissible (hk := hk) (R := R) (F := F) (d := d) (hd := hd) :=
    chooseδBaseAdmissible_of_appendixA34Extra (α := α) (hk := hk) (R := R) (F := F) (d := d)
      (hd := hd) (IH := IH) (H := H) hExtra
  exact
    extend_grid_rep_with_atom_of_chooseδBaseAdmissible (α := α) (hk := hk) (R := R) (F := F)
      (d := d) (hd := hd) (H := H) hBase

omit [KSSeparation α] in
/-- Convenience wrapper: in the B-empty extension step, it suffices to assume
`NewAtomCommutes` plus the strict separation strengthening `KSSeparationStrict`. -/
theorem extend_grid_rep_with_atom_of_newAtomCommutes_of_KSSeparationStrict
    (IH : GridBridge F) (H : GridComm F)
    [KSSeparationStrict α] (hcomm : NewAtomCommutes F d) :
      ∃ (F' : AtomFamily α (k + 1)),
      (∀ i : Fin k, F'.atoms ⟨i, Nat.lt_succ_of_lt i.is_lt⟩ = F.atoms i) ∧
      F'.atoms ⟨k, Nat.lt_succ_self k⟩ = d ∧
      ∃ (R' : MultiGridRep F'),
        (∀ r_old : Multi k, ∀ t : ℕ,
          R'.Θ_grid ⟨mu F' (joinMulti r_old t), mu_mem_kGrid F' (joinMulti r_old t)⟩ =
          R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * chooseδ hk R d hd) := by
  -- `KSSeparationStrict` implies the weaker `KSSeparation` used throughout the Core development.
  letI : KSSeparation α := KSSeparationStrict.toKSSeparation (α := α)
  have hExtra :
      AppendixA34Extra (α := α) hk (R := R) (F := F) d hd :=
    appendixA34Extra_of_newAtomCommutes_of_KSSeparationStrict (α := α) (hk := hk) (R := R)
      (IH := IH) (H := H) (d := d) (hd := hd) hcomm
  exact
    extend_grid_rep_with_atom_of_appendixA34Extra (α := α) (hk := hk) (R := R) (F := F) (d := d)
      (hd := hd) (IH := IH) (H := H) (hExtra := hExtra)

omit [KSSeparation α] in
/-- Goertzel v4-style wrapper: if `op` is globally commutative, then the remaining B-empty extension
step needs only `KSSeparationStrict` (since `NewAtomCommutes` is automatic). -/
theorem extend_grid_rep_with_atom_of_op_comm_of_KSSeparationStrict
    (IH : GridBridge F) (H : GridComm F)
    [KSSeparationStrict α] (hcomm : ∀ x y : α, op x y = op y x) :
      ∃ (F' : AtomFamily α (k + 1)),
      (∀ i : Fin k, F'.atoms ⟨i, Nat.lt_succ_of_lt i.is_lt⟩ = F.atoms i) ∧
      F'.atoms ⟨k, Nat.lt_succ_self k⟩ = d ∧
      ∃ (R' : MultiGridRep F'),
        (∀ r_old : Multi k, ∀ t : ℕ,
          R'.Θ_grid ⟨mu F' (joinMulti r_old t), mu_mem_kGrid F' (joinMulti r_old t)⟩ =
          R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * chooseδ hk R d hd) := by
  have hNew : NewAtomCommutes F d := newAtomCommutes_of_op_comm (α := α) (F := F) (d := d) hcomm
  exact
    extend_grid_rep_with_atom_of_newAtomCommutes_of_KSSeparationStrict (α := α) (hk := hk) (R := R)
      (F := F) (d := d) (hd := hd) (IH := IH) (H := H) (hcomm := hNew)

omit [KSSeparation α] in
/-- Full B-empty extension wrapper: `NewAtomCommutes` + `KSSeparation` + `DenselyOrdered α` suffice
to run the extension step (strict separation is derived from density). -/
theorem extend_grid_rep_with_atom_of_newAtomCommutes_of_KSSeparation_of_denselyOrdered
    (IH : GridBridge F) (H : GridComm F)
    [KSSeparation α] [DenselyOrdered α] (hcomm : NewAtomCommutes F d) :
      ∃ (F' : AtomFamily α (k + 1)),
      (∀ i : Fin k, F'.atoms ⟨i, Nat.lt_succ_of_lt i.is_lt⟩ = F.atoms i) ∧
      F'.atoms ⟨k, Nat.lt_succ_self k⟩ = d ∧
      ∃ (R' : MultiGridRep F'),
        (∀ r_old : Multi k, ∀ t : ℕ,
          R'.Θ_grid ⟨mu F' (joinMulti r_old t), mu_mem_kGrid F' (joinMulti r_old t)⟩ =
          R.Θ_grid ⟨mu F r_old, mu_mem_kGrid F r_old⟩ + (t : ℝ) * chooseδ hk R d hd) := by
  letI : KSSeparationStrict α :=
    KSSeparation.toKSSeparationStrict_of_denselyOrdered (α := α)
  exact
    extend_grid_rep_with_atom_of_newAtomCommutes_of_KSSeparationStrict (α := α) (hk := hk) (R := R)
      (F := F) (d := d) (hd := hd) (IH := IH) (H := H) hcomm

/-!
## Archived attempt: `A_base_statistic_lt_chooseδ_noCommon`

Opus 4.5 made real progress on a direct proof of a no-common-prefix A-side base inequality
(`separationStatistic_base … < chooseδ …`) by a KSSeparation “bump” argument.

However, the remaining “sub-case 2” (where the separator `a^n` lies strictly above the “old-part”
`μ(F,r0)^m`) appears to require a genuinely *relative* A-bound / base-invariance principle, i.e.
exactly the missing Appendix A.3.4 ingredient already isolated as the explicit interfaces:
- `ChooseδBaseAdmissible` / `ChooseδBaseAdmissible_noCommon`
- `BEmptyStrictGapSpec` / `BEmptyStrictGapSpec_noCommon`

To keep `AppendixA` building warning-free, the work-in-progress proof is commented out here.
It can be revived once the missing base-invariance lemma is proven (or replaced by an explicit
assumption/axiom, if a countermodel is found).
-/

/-  -- BEGIN WIP (2025-12-26, Opus 4.5)
/-- Helper: when μ(F,r) ≤ μ(F,r0), the base-indexed A-statistic is non-positive, hence < δ. -/
private lemma A_base_statistic_lt_chooseδ_of_mu_le
    (IH : GridBridge F) (H : GridComm F)
    (r0 r : Multi k) (u : ℕ) (hu : 0 < u)
    (hμ_le : mu F r ≤ mu F r0) :
    separationStatistic_base R r0 r u hu < chooseδ hk R d hd := by
  have hδ_pos : 0 < chooseδ hk R d hd := delta_pos hk R IH H d hd
  have hθ_le : R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ ≤ R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ :=
    R.strictMono.monotone hμ_le
  have hstat_le : separationStatistic_base R r0 r u hu ≤ 0 := by
    simp only [separationStatistic_base]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hθ_le) (Nat.cast_pos.mpr hu).le
  linarith

/-- Helper: when r is also an absolute A-witness (μ(F,r) < d^u), the base-indexed statistic
is bounded by the absolute statistic, which is strictly < chooseδ. -/
private lemma A_base_statistic_lt_chooseδ_of_absolute
    (IH : GridBridge F) (H : GridComm F)
    (r0 r : Multi k) (u : ℕ) (hu : 0 < u)
    (hrA_abs : r ∈ extensionSetA F d u) :
    separationStatistic_base R r0 r u hu < chooseδ hk R d hd := by
  have hθ_r0_nonneg : 0 ≤ R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := by
    have h_ident_le : ident ≤ mu F r0 := ident_le _
    rcases h_ident_le.eq_or_lt with h_eq | h_lt
    · have hsub :
          (⟨mu F r0, mu_mem_kGrid F r0⟩ : {x // x ∈ kGrid F}) = ⟨ident, ident_mem_kGrid F⟩ := by
        ext; exact h_eq.symm
      simp [hsub, R.ident_eq_zero]
    · have hθ_pos : R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ <
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := R.strictMono h_lt
      simpa [R.ident_eq_zero] using (le_of_lt hθ_pos)
  have hstat_le : separationStatistic_base R r0 r u hu ≤ separationStatistic R r u hu := by
    simp only [separationStatistic_base, separationStatistic]
    have : R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ ≤
           R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := by linarith
    exact div_le_div_of_nonneg_right this (Nat.cast_pos.mpr hu).le
  have habs_lt : separationStatistic R r u hu < chooseδ hk R d hd :=
    A_statistic_lt_chooseδ hk R H IH d hd r u hu hrA_abs
  linarith

/-- **Main theorem (A-side)**: For any base-indexed A-witness r with no common prefix with r0,
the base-indexed statistic is strictly less than chooseδ.

The proof proceeds by case analysis:
1. If μ(F,r) ≤ μ(F,r0): statistic ≤ 0 < δ
2. If μ(F,r) > μ(F,r0) and μ(F,r) < d^u: use absolute bound
3. If d^u ≤ μ(F,r) < μ(F,r0) ⊕ d^u: use KSSeparation bump (the hard case)
-/
theorem A_base_statistic_lt_chooseδ_noCommon
    (IH : GridBridge F) (H : GridComm F)
    (r0 r : Multi k) (u : ℕ) (hu : 0 < u)
    (_hcommon : commonMulti r0 r = 0)
    (hrA : r ∈ extensionSetA_base F d r0 u) :
    separationStatistic_base R r0 r u hu < chooseδ hk R d hd := by
  classical
  -- The constraint: μ(F,r) < μ(F,r0) ⊕ d^u
  have hμ_bound : mu F r < op (mu F r0) (iterate_op d u) := by
    simpa [extensionSetA_base, Set.mem_setOf_eq] using hrA

  -- Case split: is μ(F,r) ≤ μ(F,r0)?
  by_cases hμ_le : mu F r ≤ mu F r0
  · -- Case 1: μ(F,r) ≤ μ(F,r0) → statistic ≤ 0 < δ
    exact A_base_statistic_lt_chooseδ_of_mu_le (hk := hk) (R := R) (d := d) (hd := hd) IH H r0 r u hu hμ_le

  -- Now μ(F,r) > μ(F,r0)
  push_neg at hμ_le
  have hμ_r_pos : ident < mu F r := lt_of_le_of_lt (ident_le (mu F r0)) hμ_le

  -- Case split: is μ(F,r) < d^u (absolute A-witness)?
  by_cases hμ_abs : mu F r < iterate_op d u
  · -- Case 2: μ(F,r) < d^u → r is absolute A-witness
    have hrA_abs : r ∈ extensionSetA F d u := by
      simpa [extensionSetA, Set.mem_setOf_eq] using hμ_abs
    exact A_base_statistic_lt_chooseδ_of_absolute (hk := hk) (R := R) (d := d) (hd := hd) IH H r0 r u hu hrA_abs

  -- Case 3: d^u ≤ μ(F,r) < μ(F,r0) ⊕ d^u (the hard case)
  push_neg at hμ_abs
  -- We have: d^u ≤ μ(F,r) < μ(F,r0) ⊕ d^u

  -- Strategy: Use KSSeparation to find (n, m) that provides a bump witness.
  -- The bumped witness will be at a higher level and will give us the strict bound.

  -- First, note that μ(F,r) > ident, so we can apply Archimedean reasoning.
  have _hd_pos : ident < d := hd
  have hd_pow_pos : ident < iterate_op d u := iterate_op_pos d hd u hu

  -- Get a fixed atom for KSSeparation
  have hk_pos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  let i₀ : Fin k := ⟨0, hk_pos⟩
  let a : α := F.atoms i₀
  have ha : ident < a := F.pos i₀

  -- Derive positivity for op (mu F r0) (iterate_op d u)
  have hop_pos : ident < op (mu F r0) (iterate_op d u) := by
    have h1 : op (mu F r0) ident < op (mu F r0) (iterate_op d u) :=
      op_strictMono_right (mu F r0) hd_pow_pos
    have h2 : mu F r0 < op (mu F r0) (iterate_op d u) := by
      rwa [op_ident_right] at h1
    exact lt_of_le_of_lt (ident_le (mu F r0)) h2

  -- Apply KSSeparation: find (n, m) such that μ(F,r)^m < a^n ≤ (μ(F,r0) ⊕ d^u)^m
  -- Note: We use the bound μ(F,r0) ⊕ d^u rather than d^u since that's our constraint
  obtain ⟨n, m, hm_pos, h_gap, h_in_bound⟩ :=
    KSSeparation.separation (a := a) (x := mu F r) (y := op (mu F r0) (iterate_op d u))
      ha hμ_r_pos hop_pos hμ_bound

  -- The separation gives us: μ(F,r)^m < a^n ≤ (μ(F,r0) ⊕ d^u)^m
  -- This means μ(F, scaleMult m r) < μ(F, unitMulti i₀ n)

  have hμ_gap_grid : mu F (scaleMult m r) < mu F (unitMulti i₀ n) := by
    have hμ_left : mu F (scaleMult m r) = iterate_op (mu F r) m := IH.bridge r m
    have hμ_right : mu F (unitMulti i₀ n) = iterate_op a n := by
      simpa [a] using (mu_unitMulti F i₀ n)
    simpa [hμ_left, hμ_right] using h_gap

  -- Convert to Θ-inequality using strict monotonicity
  have hθ_gap_grid :
      R.Θ_grid ⟨mu F (scaleMult m r), mu_mem_kGrid F (scaleMult m r)⟩ <
        R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ :=
    R.strictMono hμ_gap_grid

  -- Use Θ_scaleMult to relate the scaled Θ-value to the original
  have hθ_scale :
      R.Θ_grid ⟨mu F (scaleMult m r), mu_mem_kGrid F (scaleMult m r)⟩ =
        m * R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ :=
    Theta_scaleMult (R := R) (r := r) m

  -- Now we need to bound the base-indexed statistic.
  -- The key insight: the bumped witness (unitMulti i₀ n) at level (u * m) gives us a bound.

  have huM_pos : 0 < u * m := Nat.mul_pos hu hm_pos

  -- The bumped witness a^n satisfies a^n ≤ (μ(F,r0) ⊕ d^u)^m
  -- We need to determine if a^n is in the absolute A set at some level.

  -- By the inequality a^n ≤ (μ(F,r0) ⊕ d^u)^m and the Archimedean property,
  -- there exists a level v such that a^n < d^v.

  -- For now, we use a direct arithmetic argument.
  -- The base-indexed statistic is (Θ(r) - Θ(r0)) / u.
  -- We want to show this is < chooseδ.

  -- From the Θ-gap: m * Θ(r) < Θ(unitMulti i₀ n)
  -- So: Θ(r) < Θ(unitMulti i₀ n) / m

  have hm_pos_real : 0 < (m : ℝ) := Nat.cast_pos.mpr hm_pos
  have hθ_lt : R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ <
      R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ / (m : ℝ) := by
    have hmul : R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ * (m : ℝ) <
        R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ := by
      simpa [mul_comm, hθ_scale] using hθ_gap_grid
    exact (lt_div_iff₀ hm_pos_real).2 hmul

  -- Now we need to bound Θ(unitMulti i₀ n) / m in terms of chooseδ.
  -- The key is that by the separation bound a^n ≤ (μ(F,r0) ⊕ d^u)^m, and the Archimedean
  -- property, we can find a level at which unitMulti i₀ n is an A or B witness.

  -- For simplicity, use that Θ(unitMulti i₀ n) = n * Θ(atom i₀) = n * thetaAtom R i₀
  have hθ_unit : R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ =
      n * thetaAtom (F := F) R i₀ := Theta_unitMulti R i₀ n

  -- The thetaAtom is the Θ-value of a single atom power.
  -- Since a = F.atoms i₀, we have thetaAtom R i₀ = Θ(a).

  -- Now the bound becomes: Θ(r) < n * Θ(a) / m

  -- To complete the proof, we need to show:
  -- (Θ(r) - Θ(r0)) / u < chooseδ

  -- Using: Θ(r) < n * Θ(a) / m and Θ(r0) ≥ 0:
  -- (Θ(r) - Θ(r0)) / u < Θ(r) / u < n * Θ(a) / (m * u)

  -- The question is whether n * Θ(a) / (m * u) ≤ chooseδ.
  -- This depends on whether unitMulti i₀ n is an A, B, or C witness at level m * u.

  -- From h_in_bound: a^n ≤ (μ(F,r0) ⊕ d^u)^m
  -- We need to relate this to the absolute extension sets.

  -- For the A-side bound, we need a^n ≤ d^(u*m).
  -- This is NOT directly implied by our constraint!

  -- However, we can observe that if a^n ≤ d^(u*m), then unitMulti i₀ n ∈ A at level u*m,
  -- and the statistic n * Θ(a) / (u*m) ≤ chooseδ.

  -- If a^n > d^(u*m), then we need a different argument.

  -- For now, let's handle the case where a^n ≤ d^(u*m):
  -- Derive Θ(r0) ≥ 0 (used in the calc blocks below)
  have hθ_r0_nonneg : 0 ≤ R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := by
    have h_ident_le : ident ≤ mu F r0 := ident_le _
    rcases h_ident_le.eq_or_lt with h_eq | h_lt
    · have hsub :
          (⟨mu F r0, mu_mem_kGrid F r0⟩ : {x // x ∈ kGrid F}) = ⟨ident, ident_mem_kGrid F⟩ := by
        ext; exact h_eq.symm
      simp [hsub, R.ident_eq_zero]
    · have hθ_pos : R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ <
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := R.strictMono h_lt
      simpa [R.ident_eq_zero] using (le_of_lt hθ_pos)

  by_cases h_an_le : iterate_op a n ≤ iterate_op d (u * m)
  · -- Case: a^n ≤ d^(u*m)
    rcases lt_or_eq_of_le h_an_le with hlt | heq
    · -- a^n < d^(u*m): unitMulti i₀ n is an absolute A-witness at level u*m
      have hA : unitMulti i₀ n ∈ extensionSetA F d (u * m) := by
        have hμ_right : mu F (unitMulti i₀ n) = iterate_op a n := by
          simpa [a] using (mu_unitMulti F i₀ n)
        simp [extensionSetA, Set.mem_setOf_eq, hμ_right, hlt]
      have hA_bound : separationStatistic R (unitMulti i₀ n) (u * m) huM_pos ≤ chooseδ hk R d hd :=
        chooseδ_A_bound hk R IH H d hd (unitMulti i₀ n) (u * m) huM_pos hA
      -- Now relate base-indexed statistic to this bound
      have hu_pos_real : 0 < (u : ℝ) := Nat.cast_pos.mpr hu
      -- The absolute statistic at level u*m
      have _hstat_unit : separationStatistic R (unitMulti i₀ n) (u * m) huM_pos =
          R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ / (u * m : ℕ) := by
        simp [separationStatistic]
      -- Chain the inequalities
      calc separationStatistic_base R r0 r u hu
          = (R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩) / u := rfl
        _ ≤ R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / u := by
            apply div_le_div_of_nonneg_right _ hu_pos_real.le
            linarith
        _ < (R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ / m) / u := by
            apply div_lt_div_of_pos_right hθ_lt hu_pos_real
        _ = R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ / (u * m) := by
            rw [div_div, mul_comm]
        _ = separationStatistic R (unitMulti i₀ n) (u * m) huM_pos := by
            simp [separationStatistic, Nat.cast_mul]
        _ ≤ chooseδ hk R d hd := hA_bound

    · -- a^n = d^(u*m): unitMulti i₀ n is a B-witness at level u*m
      have hB : unitMulti i₀ n ∈ extensionSetB F d (u * m) := by
        have hμ_right : mu F (unitMulti i₀ n) = iterate_op a n := by
          simpa [a] using (mu_unitMulti F i₀ n)
        simp [extensionSetB, Set.mem_setOf_eq, hμ_right, heq]
      have hB_eq : separationStatistic R (unitMulti i₀ n) (u * m) huM_pos = chooseδ hk R d hd :=
        chooseδ_B_bound hk R IH d hd (unitMulti i₀ n) (u * m) huM_pos hB
      -- Same argument as above, but strict inequality comes from the Θ-gap
      have hu_pos_real : 0 < (u : ℝ) := Nat.cast_pos.mpr hu
      calc separationStatistic_base R r0 r u hu
          = (R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩) / u := rfl
        _ ≤ R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / u := by
            apply div_le_div_of_nonneg_right _ hu_pos_real.le
            linarith
        _ < (R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ / m) / u := by
            apply div_lt_div_of_pos_right hθ_lt hu_pos_real
        _ = R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ / (u * m) := by
            rw [div_div, mul_comm]
        _ = separationStatistic R (unitMulti i₀ n) (u * m) huM_pos := by
            simp [separationStatistic, Nat.cast_mul]
        _ = chooseδ hk R d hd := hB_eq

  · -- Case: a^n > d^(u*m) (C-side at level u*m)
    -- This is the key case. We use:
    -- 1. The constraint a^n ≤ (μ(F,r0) ⊕ d^u)^m gives an upper bound
    -- 2. The gap m * Θ(r) < n * Θ(a) bounds Θ(r)
    -- 3. The C-side condition gives chooseδ ≤ n * Θ(a) / (u*m)
    --
    -- Strategy: Show that either Θ(r0) > 0 (allowing the bound to work)
    -- or the case reduces to an earlier case.

    -- Push the negation to get: d^(u*m) < a^n
    push_neg at h_an_le
    have han_gt : iterate_op d (u * m) < iterate_op a n := h_an_le

    -- Key: unitMulti i₀ n is a C-witness at level u*m
    have hC : unitMulti i₀ n ∈ extensionSetC F d (u * m) := by
      have hμ_unit : mu F (unitMulti i₀ n) = iterate_op a n := by
        simpa [a] using (mu_unitMulti F i₀ n)
      simp [extensionSetC, Set.mem_setOf_eq, hμ_unit, han_gt]

    -- Apply C-bound: chooseδ ≤ n * Θ(a) / (u*m)
    have hC_bound : chooseδ hk R d hd ≤ separationStatistic R (unitMulti i₀ n) (u * m) huM_pos :=
      chooseδ_C_bound hk R IH H d hd (unitMulti i₀ n) (u * m) huM_pos hC

    -- The C-bound gives: chooseδ ≤ n * Θ(a) / (u*m)
    have hC_stat : separationStatistic R (unitMulti i₀ n) (u * m) huM_pos =
        R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ / (u * m : ℕ) := by
      simp [separationStatistic]

    -- Rewrite using Θ(unitMulti i₀ n) = n * thetaAtom R i₀
    rw [hC_stat, hθ_unit] at hC_bound

    -- We have: Θ(r) < n * θ_a / m and chooseδ ≤ n * θ_a / (u*m)
    -- Need to show: (Θ(r) - Θ(r0)) / u < chooseδ
    --
    -- Key insight: From strict inequality Θ(r) < n*θ_a/m and Θ(r0) ≥ 0:
    -- (Θ(r) - Θ(r0))/u < Θ(r)/u < n*θ_a/(m*u)
    --
    -- But we need strict comparison with chooseδ. The gap comes from Θ(r0) > 0
    -- when the C-side case applies (since a^n > d^(u*m) requires μ(F,r0) > ident).

    have hu_pos_real : 0 < (u : ℝ) := Nat.cast_pos.mpr hu
    have huM_pos_real : 0 < ((u * m : ℕ) : ℝ) := Nat.cast_pos.mpr huM_pos

    -- Case split on whether Θ(r0) > 0 or Θ(r0) = 0
    by_cases hθr0_pos : 0 < R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩
    · -- Case: Θ(r0) > 0
      -- The base-indexed statistic is strictly less than the absolute statistic
      have hstat_strict :
          separationStatistic_base R r0 r u hu <
            R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / u := by
        simp only [separationStatistic_base]
        have hnum_strict :
            R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ <
              R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ := by linarith
        exact div_lt_div_of_pos_right hnum_strict hu_pos_real

      -- Θ(r)/u < n*θ_a/(m*u)
      have hθr_bound : R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / u <
          n * thetaAtom (F := F) R i₀ / ((m : ℝ) * u) := by
        calc R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / u
            < (R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ / m) / u := by
              apply div_lt_div_of_pos_right hθ_lt hu_pos_real
          _ = R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F (unitMulti i₀ n)⟩ / ((m : ℝ) * u) := by
              rw [div_div]
          _ = n * thetaAtom (F := F) R i₀ / ((m : ℝ) * u) := by rw [hθ_unit]

      -- Show that m*u = u*m as reals
      have hmu_eq_um : ((m : ℝ) * u) = ((u * m : ℕ) : ℝ) := by
        simp only [Nat.cast_mul]
        ring

      /-
      **Key Insight** (Goertzel/K&S):

      The constraint h_in_bound: a^n ≤ (μ(F,r0) ⊕ d^u)^m bounds n*θ_a from ABOVE.

      In the K&S extended grid with Θ' additivity:
        Θ'((μ(F,r0) ⊕ d^u)^m) = m * Θ'(μ(F,r0) ⊕ d^u)
                                = m * (Θ(r0) + u * chooseδ)
                                = m * Θ(r0) + (u*m) * chooseδ

      From h_in_bound and Θ' monotonicity:
        n * θ_a ≤ m * Θ(r0) + (u*m) * chooseδ

      Rearranging:
        n * θ_a / (m * u) ≤ Θ(r0) / u + chooseδ
        n * θ_a / (m * u) - Θ(r0) / u ≤ chooseδ

      From hθr_bound: Θ(r) / u < n * θ_a / (m * u)
      From hstat_strict: stat_base < Θ(r) / u

      Therefore:
        stat_base < Θ(r) / u < n * θ_a / (m * u)

      And since Θ(r0) > 0:
        stat_base = (Θ(r) - Θ(r0)) / u < Θ(r) / u - Θ(r0) / u < n * θ_a / (m * u) - Θ(r0) / u ≤ chooseδ

      This requires Θ' monotonicity on the extended grid (chooseδ ∈ [δ_A, δ_C]).
      -/

      -- The critical bound from h_in_bound and Θ' monotonicity:
      -- n * θ_a ≤ m * Θ(r0) + (u*m) * chooseδ
      --
      -- This follows from the K&S extended Θ' construction:
      -- 1. Θ'(a^n) = n * θ_a (a is on the k-grid, d-component 0)
      -- 2. Θ'((μ(F,r0) ⊕ d^u)^m) = m * (Θ(r0) + u * chooseδ) by additivity
      -- 3. From h_in_bound and monotonicity: Θ'(a^n) ≤ Θ'((μ(F,r0) ⊕ d^u)^m)
      --
      -- **CIRCULARITY ANALYSIS**:
      -- This step requires Θ' weak monotonicity for δ = chooseδ. The proof
      -- structure has a circular dependency:
      --   ChooseδBaseAdmissible → BEmptyStrictGapSpec → extend_grid_rep_with_atom
      --   → Θ' strict monotonicity → theta_gap_lt_of_mu_lt_op → relative A-bound
      --   → ChooseδBaseAdmissible (circular!)
      --
      -- **CASE SPLIT** on h_in_bound (equality vs strict):
      --
      -- **EQUALITY CASE**: a^n = (μ(F,r0) ⊕ d^u)^m
      --   - By Θ' well-definedness (proven from absolute bounds): n*θ_a = m*Θ(r0) + um*chooseδ ✓
      --   - This case requires NO Θ' monotonicity!
      --
      -- **STRICT CASE**: a^n < (μ(F,r0) ⊕ d^u)^m = μ(F,r0)^m ⊕ d^{um}
      --   - Subcase a^n ≤ μ(F,r0)^m: old-part favors RHS, t-component (0 < um) decides.
      --     This case follows from Θ monotonicity on k-grid + t*δ contribution.
      --   - Subcase a^n > μ(F,r0)^m: "relative A-region" case, requires theta_gap_lt_of_mu_lt_op.
      --     This is the GENUINE CIRCULAR DEPENDENCY.
      --
      -- **RESOLUTION PATH** (strong induction on Θ(base)/level²):
      -- Define measure M(r0, u) = Θ(r0) / u². For the relative A-bound at (r0, u),
      -- we need the bound at (scaleMult m r0, um). Since
      --   M(scaleMult m r0, um) = m*Θ(r0)/(um)² = Θ(r0)/(u²m) < M(r0, u) when m > 1,
      -- strong induction on M could work. The base case (M → 0) reduces to
      -- the absolute A-bound (when base ≈ ident).
      --
      -- **ALTERNATIVE**: Prove Θ' weak monotonicity directly from absolute A/C/B bounds
      -- using the accuracy_lemma, without requiring BEmptyStrictGapSpec first.
      have hθa_bound : n * thetaAtom (F := F) R i₀ ≤
          m * R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ + (u * m : ℕ) * chooseδ hk R d hd := by
        -- Key hypotheses:
        -- h_in_bound : a^n ≤ (μ(F,r0) ⊕ d^u)^m
        -- hC_bound : chooseδ ≤ n * θ_a / (u*m)  (C-side bound)
        -- hθr0_pos : 0 < Θ(r0)  (positive base)
        -- han_gt : a^n > d^{um}  (C-side condition)
        --
        -- Case split: equality vs strict in h_in_bound
        rcases h_in_bound.eq_or_lt with heq | hlt
        · -- EQUALITY CASE: a^n = (μ(F,r0) ⊕ d^u)^m
          -- By Θ' well-definedness, the bound is an equality.
          --
          -- **Implementation sketch** (no circularity):
          -- 1. Let F' := extendAtomFamily F d hd
          -- 2. a^n = mu F' (joinMulti (unitMulti i₀ n) 0) [by mu_extend_last + iterate_op_zero]
          -- 3. (μ(F,r0) ⊕ d^u)^m = mu F' (joinMulti (scaleMult m r0) (u*m)) [needs aux lemma]
          -- 4. From heq: these two extended-grid elements are equal
          -- 5. Apply Theta'_well_defined (proven from absolute A/C/B bounds)
          -- 6. Conclude: n*θ_a + 0*chooseδ = m*Θ(r0) + um*chooseδ
          --
          -- **Required auxiliary lemmas**:
          -- - scaleMult_joinMulti : scaleMult m (joinMulti r t) = joinMulti (scaleMult m r) (m*t)
          -- - GridBridge for extended family: iterate_op (mu F' r) m = mu F' (scaleMult m r)
          by
            -- TODO: complete equality-case extraction (requires a scaling lemma for `joinMulti`,
            -- plus threading `GridBridge` through the extended family).
        · -- STRICT CASE: a^n < (μ(F,r0) ⊕ d^u)^m
          -- Sub-case split on old-part comparison: a^n vs μ(F,r0)^m
          -- Key insight: The d-component contributes um*chooseδ > 0, so if the
          -- old-part comparison a^n ≤ μ(F,r0)^m holds, we get the bound with slack.
          by_cases hold : iterate_op a n ≤ iterate_op (mu F r0) m
          · -- **SUB-CASE 1: a^n ≤ μ(F,r0)^m** (NO circularity!)
            -- By Θ monotonicity on k-grid: n*θ_a ≤ m*Θ(r0)
            -- Since chooseδ > 0 and u*m ≥ 1: n*θ_a ≤ m*Θ(r0) < m*Θ(r0) + um*chooseδ ✓
            --
            -- Step 1: Express both sides as μ-values on k-grid
            -- a^n = mu F (unitMulti i₀ n)
            have ha_eq : iterate_op a n = mu F (unitMulti i₀ n) := by
              rw [mu_unitMulti]
            -- μ(F,r0)^m = mu F (scaleMult m r0) via GridBridge
            have hμr0m_eq : iterate_op (mu F r0) m = mu F (scaleMult m r0) := by
              exact (IH.bridge r0 m).symm
            -- Step 2: Get Θ inequality from μ inequality
            have hμ_ineq : mu F (unitMulti i₀ n) ≤ mu F (scaleMult m r0) := by
              rw [← ha_eq, ← hμr0m_eq]; exact hold
            -- Step 3: By R.strictMono (or mono for equality), Θ preserves ≤
            have hθ_ineq : R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F _⟩ ≤
                R.Θ_grid ⟨mu F (scaleMult m r0), mu_mem_kGrid F _⟩ := by
              rcases hμ_ineq.eq_or_lt with h_eq | h_lt
              · -- Equality case: Θ-values equal
                have hsub : (⟨mu F (unitMulti i₀ n), mu_mem_kGrid F _⟩ : {x // x ∈ kGrid F}) =
                    ⟨mu F (scaleMult m r0), mu_mem_kGrid F _⟩ := by ext; exact h_eq
                simp [hsub]
              · -- Strict case: use strictMono
                exact le_of_lt (R.strictMono h_lt)
            -- Step 4: Rewrite using Theta_unitMulti and Theta_scaleMult
            have hθ_lhs : R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F _⟩ =
                n * thetaAtom (F := F) R i₀ := Theta_unitMulti R i₀ n
            have hθ_rhs : R.Θ_grid ⟨mu F (scaleMult m r0), mu_mem_kGrid F _⟩ =
                m * R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := Theta_scaleMult R r0 m
            -- Step 5: Chain the inequalities
            have hθ_bound : n * thetaAtom (F := F) R i₀ ≤
                m * R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := by
              calc n * thetaAtom (F := F) R i₀
                  = R.Θ_grid ⟨mu F (unitMulti i₀ n), mu_mem_kGrid F _⟩ := hθ_lhs.symm
                _ ≤ R.Θ_grid ⟨mu F (scaleMult m r0), mu_mem_kGrid F _⟩ := hθ_ineq
                _ = m * R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := hθ_rhs
            -- Step 6: Add positive contribution from d-component
            have hpos : 0 < (u * m : ℕ) * chooseδ hk R d hd := by
              apply mul_pos
              · exact Nat.cast_pos.mpr huM_pos
              · exact delta_pos hk R IH H d hd
            linarith
          · -- **SUB-CASE 2: a^n > μ(F,r0)^m** (requires careful analysis)
            -- This is the harder case. Push negation.
            push_neg at hold
            have ha_gt_μr0m : iterate_op (mu F r0) m < iterate_op a n := hold
            -- Key observation: The constraint a^n < (μ(F,r0) ⊕ d^u)^m with a^n > μ(F,r0)^m
            -- means the d^u component must "make up the difference".
            --
            -- By iterate_op_op_of_comm (if we have commutativity):
            --   (μ(F,r0) ⊕ d^u)^m = μ(F,r0)^m ⊕ d^{um}
            -- So: μ(F,r0)^m < a^n < μ(F,r0)^m ⊕ d^{um}
            --
            -- This means a^n is in the "gap" between μ(F,r0)^m and μ(F,r0)^m ⊕ d^{um}.
            -- Applying Θ' monotonicity (which requires BEmptyStrictGapSpec):
            --   m*Θ(r0) < n*θ_a < m*Θ(r0) + um*chooseδ
            --
            -- For now, we use the bound from iterate_op_op_of_comm.
            -- TODO: Complete this case using the induction structure or
            --       proving weak Θ' monotonicity directly.
            by
              -- TODO: this is the genuinely circular subcase (needs a relative/base-indexed gap lemma).

      -- Derive the key inequality from the bound
      have h_bound_rearranged :
          n * thetaAtom (F := F) R i₀ / ((m : ℝ) * u) - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ / u ≤
            chooseδ hk R d hd := by
        have hm_pos_r : (0 : ℝ) < m := Nat.cast_pos.mpr hm_pos
        have hmu_pos_r : (0 : ℝ) < (m : ℝ) * u := mul_pos hm_pos_r hu_pos_real
        have h1 : n * thetaAtom (F := F) R i₀ / ((m : ℝ) * u) ≤
            (m * R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ + (u * m : ℕ) * chooseδ hk R d hd) /
              ((m : ℝ) * u) :=
          div_le_div_of_nonneg_right hθa_bound (le_of_lt hmu_pos_r)
        have h2 : (m * R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ + (u * m : ℕ) * chooseδ hk R d hd) /
            ((m : ℝ) * u) =
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ / u + chooseδ hk R d hd := by
          have hmu_ne : (m : ℝ) * u ≠ 0 := ne_of_gt hmu_pos_r
          simp only [Nat.cast_mul]
          field_simp
        linarith

      -- Chain the inequalities to complete the proof
      calc separationStatistic_base R r0 r u hu
          = (R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩) / u := rfl
        _ = R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / u - R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ / u := by
            rw [sub_div]
        _ < n * thetaAtom (F := F) R i₀ / ((m : ℝ) * u) -
              R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ / u := by
            have hθr_u : R.Θ_grid ⟨mu F r, mu_mem_kGrid F r⟩ / u <
                n * thetaAtom (F := F) R i₀ / ((m : ℝ) * u) := hθr_bound
            linarith
        _ ≤ chooseδ hk R d hd := h_bound_rearranged

    · -- Case: Θ(r0) = 0, i.e., μ(F,r0) = ident
      -- When μ(F,r0) = ident, the base-indexed A-set equals the absolute A-set:
      -- extensionSetA_base F d r0 u = {r | μ(F,r) < ident ⊕ d^u} = {r | μ(F,r) < d^u}
      -- So this case reduces to Case 2 (absolute A-witness).
      push_neg at hθr0_pos
      have hθr0_eq : R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ = 0 :=
        le_antisymm hθr0_pos hθ_r0_nonneg

      -- μ(F,r0) = ident since Θ is strictly monotone and Θ(ident) = 0
      have hμr0_eq : mu F r0 = ident := by
        by_contra h_ne
        have h_pos : ident < mu F r0 := (ident_le (mu F r0)).lt_of_ne' h_ne
        have hθ_pos : R.Θ_grid ⟨ident, ident_mem_kGrid F⟩ <
            R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := R.strictMono h_pos
        have : 0 < R.Θ_grid ⟨mu F r0, mu_mem_kGrid F r0⟩ := by
          simpa [R.ident_eq_zero] using hθ_pos
        linarith

      -- The base-indexed constraint simplifies: μ(F,r) < ident ⊕ d^u = d^u
      have hμ_abs : mu F r < iterate_op d u := by
        have : op (mu F r0) (iterate_op d u) = op ident (iterate_op d u) := by
          rw [hμr0_eq]
        rw [this, op_ident_left] at hμ_bound
        exact hμ_bound

      -- So r is an absolute A-witness
      have hrA_abs : r ∈ extensionSetA F d u := by
        simpa [extensionSetA, Set.mem_setOf_eq] using hμ_abs

      -- Apply Case 2 logic
      exact A_base_statistic_lt_chooseδ_of_absolute (hk := hk) (R := R) (d := d) (hd := hd)
        IH H r0 r u hu hrA_abs

-- END WIP
-/

end ChooseδBase

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA
