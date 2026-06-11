import Mathlib.Order.Atoms
import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Gunky (atomless) mereology — an infinite-native foundation

A bounded order is *gunky* when every non-bottom individual has a proper, non-bottom
part: there is no minimal positive individual, no foundational atom, and (in a
Boolean reading) no empty individual is forced as the support of any part. This is the
mereological form of the phenomenological observation that "you can always look
deeper": every region is properly divisible.

Gunk is the natural foundation for ultrainfinitism (only the infinite is real): we prove
that **a non-trivial gunky order is infinite** (`infinite_of_isGunky`) — the finite
cannot be gunky — and we connect gunk to the principal/free ultrafilter dial via the
fact that the *atoms* of a powerset are exactly its singletons, i.e. the supports of
*principal* ultrafilters (`isAtom_set_singleton`, `not_isGunky_set`). The non-negative
reals are the paradigm gunky individual (`isGunky_nnreal`); a two-valued algebra is the
paradigm non-gunky one (`not_isGunky_bool`).
-/

namespace Mettapedia.Foundations.Gunk

open scoped NNReal

universe u

/-- A bounded order is **gunky** (atomless) if every non-bottom element has a proper,
non-bottom part. Mereologically: every individual is properly divisible; there is no
foundational atom. -/
def IsGunky (α : Type u) [PartialOrder α] [OrderBot α] : Prop :=
  ∀ a : α, a ≠ ⊥ → ∃ b, b ≠ ⊥ ∧ b < a

section Order
variable {α : Type u} [PartialOrder α] [OrderBot α]

/-- Gunk is exactly atomlessness: no element is an atom. -/
theorem isGunky_iff_no_isAtom : IsGunky α ↔ ∀ a : α, ¬ IsAtom a := by
  constructor
  · intro hg a hatom
    obtain ⟨b, hb0, hba⟩ := hg a hatom.1
    exact hb0 (hatom.2 b hba)
  · intro h a ha
    have hna := h a
    simp only [IsAtom, not_and, not_forall] at hna
    obtain ⟨b, hba, hb0⟩ := by simpa using hna ha
    exact ⟨b, hb0, hba⟩

/-- **Gunk forces the infinite.** A gunky order with more than one element is infinite:
iterating the "take a proper non-bottom part" operation produces a strictly descending
sequence, so the carrier contains a copy of `ℕ`. The finite cannot be gunky — this is the
load-bearing fact of an infinite-native foundation. -/
theorem infinite_of_isGunky [Nontrivial α] (hg : IsGunky α) : Infinite α := by
  classical
  -- a starting non-bottom element
  obtain ⟨a₀, ha₀⟩ : ∃ a : α, a ≠ ⊥ := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne α
    rcases eq_or_ne x ⊥ with hx | hx
    · exact ⟨y, fun hy => hxy (hx.trans hy.symm)⟩
    · exact ⟨x, hx⟩
  -- "take a proper non-bottom part" as an endo on non-bottom individuals
  let next : {x : α // x ≠ ⊥} → {x : α // x ≠ ⊥} := fun a =>
    ⟨(hg a.1 a.2).choose, (hg a.1 a.2).choose_spec.1⟩
  have hnext : ∀ a : {x : α // x ≠ ⊥}, (next a).1 < a.1 := fun a =>
    (hg a.1 a.2).choose_spec.2
  let seq : ℕ → {x : α // x ≠ ⊥} := fun n => next^[n] ⟨a₀, ha₀⟩
  have hanti : StrictAnti (fun n => (seq n).1) := by
    apply strictAnti_nat_of_succ_lt
    intro n
    have : seq (n + 1) = next (seq n) := Function.iterate_succ_apply' next n _
    rw [this]
    exact hnext (seq n)
  exact Infinite.of_injective (fun n => (seq n).1) hanti.injective

/-- A finite nontrivial carrier cannot be gunky. This is the contrapositive of
`infinite_of_isGunky`, packaged for use on finite-stage approximations and
frontier objects. -/
theorem not_isGunky_of_finite [Finite α] [Nontrivial α] : ¬ IsGunky α := by
  intro hg
  exact Infinite.false (infinite_of_isGunky hg)

end Order

/-! ## The paradigm gunky individual: the continuum -/

/-- The non-negative reals are gunky: every positive quantity is halvable, so there is no
smallest positive magnitude. The continuum is the gunky individual par excellence. -/
theorem isGunky_nnreal : IsGunky ℝ≥0 := by
  intro a ha
  rw [bot_eq_zero] at ha
  refine ⟨a / 2, ?_, NNReal.half_lt_self ha⟩
  rw [bot_eq_zero]
  exact div_ne_zero ha (by norm_num)

/-- Corollary: the continuum is infinite, *because* it is gunky. -/
theorem infinite_nnreal : Infinite ℝ≥0 := infinite_of_isGunky isGunky_nnreal

/-! ## The paradigm non-gunky individual: a two-valued algebra -/

/-- `Bool` is not gunky: `true` is an atom — it has no proper non-`⊥` part. A two-valued
algebra has a smallest positive individual, exactly the finitary case gunk excludes. -/
theorem not_isGunky_bool : ¬ IsGunky Bool := by
  intro hg
  obtain ⟨b, hb0, hb⟩ := hg true (by decide)
  cases b <;> revert hb0 hb <;> decide

/-! ## The Stone weld: atoms are the principal-ultrafilter points

In the powerset Boolean algebra the atoms are exactly the singletons, and a singleton
`{x}` is the support of the principal ultrafilter `pure x`. So the finitary "atoms" of
`Set α` are precisely the principal-ultrafilter points; the powerset is never gunky for an
inhabited carrier (`not_isGunky_set`). Passing to a genuinely gunky algebra means
quotienting these principal atoms away — the mereological echo of moving from principal to
free ultrafilters (the One). -/

theorem isAtom_set_singleton {α : Type u} (x : α) : IsAtom ({x} : Set α) := by
  refine ⟨Set.singleton_ne_empty x, ?_⟩
  intro b hb
  rcases Set.subset_singleton_iff_eq.mp hb.le with h | h
  · exact h
  · exact absurd h hb.ne

/-- The powerset is never gunky over an inhabited carrier: every point `x` gives a
singleton atom `{x}` — the support of the *principal* ultrafilter `pure x`. So the
finitary atoms of `Set α` are exactly the principal-ultrafilter points; a genuinely gunky
algebra is obtained only by quotienting these away (the move from principal to free
ultrafilters). -/
theorem not_isGunky_set {α : Type u} [Nonempty α] : ¬ IsGunky (Set α) := by
  rw [isGunky_iff_no_isAtom]
  push_neg
  obtain ⟨x⟩ := (inferInstance : Nonempty α)
  exact ⟨{x}, isAtom_set_singleton x⟩

/-! ## A Heyting-algebra gunky witness: open regions of the line

The open sets of `ℝ` form a frame — a complete Heyting algebra — that is gunky: every
non-empty open region properly contains a smaller non-empty open region (shrink the
radius). Spatial regions of the continuum are the paradigm gunky Heyting algebra. -/

section HeytingWitness
open TopologicalSpace Metric

/-- The frame `Opens ℝ` of open regions of the line is gunky. -/
theorem isGunky_opens_real : IsGunky (Opens ℝ) := by
  intro U hU
  -- `U ≠ ⊥` gives a point of `U`
  obtain ⟨x, hx⟩ : (U : Set ℝ).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hU (SetLike.ext' (h.trans (TopologicalSpace.Opens.coe_bot).symm))
  -- an open ball around `x` inside `U`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  -- the half-radius ball is a strictly smaller non-empty open region
  refine ⟨⟨ball x (ε / 2), isOpen_ball⟩, ?_, ?_⟩
  · -- ≠ ⊥ : it contains `x`
    intro h
    have hxin : x ∈ ball x (ε / 2) := mem_ball_self (by positivity)
    have hcoe : ball x (ε / 2) = (∅ : Set ℝ) :=
      (SetLike.ext'_iff.mp h).trans (TopologicalSpace.Opens.coe_bot)
    rw [hcoe] at hxin
    exact (Set.mem_empty_iff_false x).mp hxin
  · -- < U : the point `x + 3ε/4` is in `U` but not in the half-ball
    have hpt : x + 3 * ε / 4 ∈ (U : Set ℝ) :=
      hball (by rw [mem_ball, Real.dist_eq, show x + 3 * ε / 4 - x = 3 * ε / 4 by ring,
        abs_of_pos (by linarith)]; linarith)
    have hle : (⟨ball x (ε / 2), isOpen_ball⟩ : Opens ℝ) ≤ U := by
      rw [← SetLike.coe_subset_coe]
      exact fun y hy => hball (ball_subset_ball (by linarith) hy)
    refine lt_of_le_of_ne hle ?_
    intro h
    have hcoe : ball x (ε / 2) = (U : Set ℝ) :=
      congrArg (fun W : Opens ℝ => (W : Set ℝ)) h
    have hin : x + 3 * ε / 4 ∈ ball x (ε / 2) := by rw [hcoe]; exact hpt
    rw [mem_ball, Real.dist_eq, show x + 3 * ε / 4 - x = 3 * ε / 4 by ring,
      abs_of_pos (by linarith)] at hin
    linarith

end HeytingWitness

/-! ## A Boolean-algebra gunky witness: clopens of Cantor space

The clopen subsets of Cantor space `ℕ → Bool` form a Boolean algebra that is gunky: a
non-empty clopen always splits — fix one more coordinate and you get a proper non-empty
clopen part. This is the canonical countable atomless Boolean algebra. -/

section BooleanWitness
open TopologicalSpace

local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := ⟨rfl⟩

/-- The Boolean algebra `Clopens (ℕ → Bool)` of clopen subsets of Cantor space is gunky. -/
theorem isGunky_clopens_cantor : IsGunky (Clopens (ℕ → Bool)) := by
  intro U hU
  -- a point of `U`
  obtain ⟨f, hf⟩ : (U : Set (ℕ → Bool)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hU (SetLike.ext' (h.trans (TopologicalSpace.Clopens.coe_bot).symm))
  -- `U` open, so a finite cylinder around `f` lies inside `U`
  have hmem : (U : Set (ℕ → Bool)) ∈ nhds f := U.isClopen.isOpen.mem_nhds hf
  rw [nhds_pi, Filter.mem_pi] at hmem
  obtain ⟨I, hIfin, t, htnhds, htsub⟩ := hmem
  have hcyl : ∀ g : ℕ → Bool, (∀ i ∈ I, g i = f i) → g ∈ (U : Set (ℕ → Bool)) := by
    intro g hg
    refine htsub fun i hi => ?_
    rw [hg i hi]
    exact mem_of_mem_nhds (htnhds i)
  -- a coordinate `n` not fixed by the cylinder
  obtain ⟨n, hn⟩ : ∃ n, n ∉ I := by
    by_contra hcon
    push_neg at hcon
    exact Set.infinite_univ (hIfin.subset fun n _ => hcon n)
  -- the clopen "coordinate `n` equals `f n`"
  have hCclopen : IsClopen {g : ℕ → Bool | g n = f n} := by
    have he : {g : ℕ → Bool | g n = f n} = (fun g => g n) ⁻¹' {f n} := by
      ext g; simp [Set.mem_preimage, Set.mem_singleton_iff]
    rw [he]
    exact (isClopen_discrete _).preimage (continuous_apply n)
  set C : Clopens (ℕ → Bool) := ⟨{g | g n = f n}, hCclopen⟩ with hCdef
  refine ⟨U ⊓ C, ?_, ?_⟩
  · -- `U ⊓ C ≠ ⊥` : it contains `f`
    intro h
    have : f ∈ ((U ⊓ C : Clopens (ℕ → Bool)) : Set (ℕ → Bool)) := by
      rw [TopologicalSpace.Clopens.coe_inf]
      exact ⟨hf, rfl⟩
    rw [h, TopologicalSpace.Clopens.coe_bot] at this
    exact (Set.mem_empty_iff_false f).mp this
  · -- `U ⊓ C < U` : `≤` by `inf_le_left`, and `≠` via the flipped point at `n`
    refine lt_of_le_of_ne inf_le_left ?_
    intro h
    -- the point agreeing with `f` except at `n`
    set g : ℕ → Bool := Function.update f n (!f n) with hgdef
    have hgU : g ∈ (U : Set (ℕ → Bool)) := by
      refine hcyl g fun i hi => ?_
      have hine : i ≠ n := fun hin => hn (hin ▸ hi)
      rw [hgdef]
      exact Function.update_of_ne hine _ _
    have hgnotC : g ∉ ({x | x n = f n} : Set (ℕ → Bool)) := by
      simp only [Set.mem_setOf_eq, hgdef, Function.update_self]
      exact Bool.not_ne_self (f n)
    have hgV : g ∈ ((U ⊓ C : Clopens (ℕ → Bool)) : Set (ℕ → Bool)) := by
      rw [h]; exact hgU
    rw [TopologicalSpace.Clopens.coe_inf] at hgV
    exact hgnotC hgV.2

end BooleanWitness

end Mettapedia.Foundations.Gunk
