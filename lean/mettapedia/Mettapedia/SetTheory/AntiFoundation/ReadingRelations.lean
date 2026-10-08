import Mettapedia.SetTheory.AntiFoundation.ReadingFixedPoints

/-!
# The child-class step on every relation

On an arbitrary relation the same step has least fixed point the pairs of nodes that are
bisimilar and accessible along children. Every reading agrees with that relation on
accessible nodes. A graph whose child relation is well-founded has one reading.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.AntiFoundation

open Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

variable {α : Type u}

/-- Bisimilarity of nodes from which every child-chain is finite. -/
def accessibleBisimilar (edge : Edge α) (a b : α) : Prop :=
  Acc (flip edge) a ∧ Acc (flip edge) b ∧ Bisimilar edge edge a b

theorem relStep_gfp_eq_bisimilar (edge : Edge α) :
    (relStep edge).gfp = Bisimilar edge edge := by
  apply le_antisymm
  · intro a b hab
    have hbis : IsBisimulation edge edge (relStep edge).gfp := by
      intro x y hxy
      rw [← (relStep edge).map_gfp] at hxy
      exact hxy
    exact hbis.bisimilar hab
  · apply OrderHom.le_gfp
    intro a b hab
    exact isBisimulation_bisimilar hab

theorem relStep_accessible_le (edge : Edge α) :
    relStep edge (accessibleBisimilar edge) ≤ accessibleBisimilar edge := by
  intro a b hab
  refine ⟨?_, ?_, ?_⟩
  · refine Acc.intro a fun c hc => ?_
    obtain ⟨_, _, hT⟩ := hab.1 c hc
    exact hT.1
  · refine Acc.intro b fun c hc => ?_
    obtain ⟨_, _, hT⟩ := hab.2 c hc
    exact hT.2.1
  · have hsc : SameChildren edge (Bisimilar edge edge) a b :=
      sameChildren_mono (fun _ _ h => h.2.2) hab
    have hbis : IsBisimulation edge edge (relStep edge (Bisimilar edge edge)) := by
      intro x y hxy
      constructor
      · intro x' hx
        obtain ⟨y', hy, hb⟩ := hxy.1 x' hx
        exact ⟨y', hy, isBisimulation_bisimilar hb⟩
      · intro y' hy
        obtain ⟨x', hx, hb⟩ := hxy.2 y' hy
        exact ⟨x', hx, isBisimulation_bisimilar hb⟩
    exact hbis.bisimilar hsc

/-- A reading, seen as a relation, is a fixed point of the relation step. -/
theorem relStep_coe_of_fixed (edge : Edge α) {R : Setoid α} (hR : step edge R = R) :
    relStep edge (⇑R) = ⇑R := by
  ext x y
  simp only [relStep_apply]
  exact (step_apply edge R x y).symm.trans (Iff.of_eq
    (congrFun (congrFun (congrArg (fun S : Setoid α => (⇑S : α → α → Prop)) hR) x) y))

theorem accessibleBisimilar_le_of_preFixed (edge : Edge α) {S : α → α → Prop}
    (hS : relStep edge S ≤ S) {a b : α} (h : accessibleBisimilar edge a b) : S a b := by
  have key : ∀ a, Acc (flip edge) a → ∀ b, Acc (flip edge) b →
      Bisimilar edge edge a b → S a b := by
    intro a ha
    induction ha with
    | intro a _ ih =>
      intro b hb hab
      apply hS
      constructor
      · intro a' ha'
        obtain ⟨b', hb', hab'⟩ := hab.exists_child_left ha'
        exact ⟨b', hb', ih a' ha' b' (hb.inv hb') hab'⟩
      · intro b' hb'
        obtain ⟨a', ha', hab'⟩ := hab.exists_child_right hb'
        exact ⟨a', ha', ih a' ha' b' (hb.inv hb') hab'⟩
  exact key a h.1 b h.2.1 h.2.2

theorem relStep_lfp_eq_accessibleBisimilar (edge : Edge α) :
    (relStep edge).lfp = accessibleBisimilar edge := by
  apply le_antisymm
  · exact (relStep edge).lfp_le (relStep_accessible_le edge)
  · apply OrderHom.le_lfp
    intro S hS _ _ h
    exact accessibleBisimilar_le_of_preFixed edge hS h

theorem reading_agrees_accessible (edge : Edge α) (R : Setoid α) (hR : step edge R = R)
    {a b : α} (ha : Acc (flip edge) a) (hb : Acc (flip edge) b) :
    R a b ↔ (relStep edge).lfp a b := by
  have hrel : relStep edge (⇑R) = ⇑R := relStep_coe_of_fixed edge hR
  constructor
  · intro hab
    rw [relStep_lfp_eq_accessibleBisimilar]
    refine ⟨ha, hb, ?_⟩
    have hhigh : ⇑R ≤ (relStep edge).gfp := (relStep edge).le_gfp hrel.symm.le
    rw [relStep_gfp_eq_bisimilar] at hhigh
    exact hhigh a b hab
  · intro hab
    exact ((relStep edge).lfp_le hrel.le) a b hab

theorem unique_reading_of_wellFounded (edge : Edge α) (hwf : WellFounded (flip edge)) :
    ∃! R : Setoid α, step edge R = R := by
  refine ⟨bisimilarSetoid edge, ?_, ?_⟩
  · rw [← gfp_eq_bisimilar]
    exact (step edge).isFixedPt_gfp
  · intro R hR
    have hrel : relStep edge (⇑R) = ⇑R := relStep_coe_of_fixed edge hR
    have hlow : (relStep edge).lfp ≤ ⇑R := (relStep edge).lfp_le hrel.le
    have hhigh : ⇑R ≤ (relStep edge).gfp := (relStep edge).le_gfp hrel.symm.le
    apply Setoid.ext
    intro a b
    constructor
    · intro hab
      have hbis : Bisimilar edge edge a b := by
        rw [relStep_gfp_eq_bisimilar] at hhigh
        exact hhigh a b hab
      simpa [bisimilarSetoid_iff] using hbis
    · intro hab
      have hacc : accessibleBisimilar edge a b :=
        ⟨WellFounded.apply hwf a, WellFounded.apply hwf b, (bisimilarSetoid_iff edge).mp hab⟩
      rw [← relStep_lfp_eq_accessibleBisimilar] at hacc
      exact hlow a b hacc

end Mettapedia.SetTheory.AntiFoundation
