import Mettapedia.Logic.Metaphysics.UltrainfiniteShadows
import Mettapedia.Logic.Metaphysics.UltrainfiniteShadowsDistinction

/-!
# A finite shadow is a finite quotient of the Stone space

For any Boolean algebra `B` and any finite subalgebra `L` (a shadow), the clopens of the shadow
atoms partition the Stone space: every Stone point lies in exactly one of them
(`existsUnique_shadowAtom_mem`). The **shadow map** `shadowMap L` sends a point to its piece.

* It is surjective (`shadowMap_surjective`), and its fibres are the clopens of the shadow atoms
  (`shadowMap_fibre`), so the shadow is a finite quotient of the whole, with clopen classes.
* **A piece is genuine exactly when its class is a single point**
  (`isAtom_iff_fibre_eq_singleton`).
* **On a gunky algebra every class is infinite** (`shadowMap_fibre_infinite`), and so is every
  class of the observer that reports the piece (`shadowObserver_class_infinite`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

open Set Function TopologicalSpace Mettapedia.Foundations.Gunk
  Mettapedia.Cybernetics.DistinctionCalculus

universe u

variable {B : Type u} [BooleanAlgebra B]

/-- **The pieces of a shadow partition the Stone space.** -/
theorem existsUnique_shadowAtom_mem (L : BooleanSubalgebra B) [Finite L] (p : StoneSpace B) :
    ∃! a, a ∈ shadowAtoms L ∧ p ∈ (stoneRepr B a : Set (StoneSpace B)) := by
  set T := (shadowAtoms_finite L).toFinset
  have h1 : stoneRepr B (T.sup id) = ⊤ := by
    rw [show T.sup id = ⊤ from sup_shadowAtoms L]
    exact (stoneRepr B).map_top
  rw [map_finset_sup] at h1
  have h2 : p ∈ ((T.sup (stoneRepr B ∘ id) : Clopens (StoneSpace B)) : Set (StoneSpace B)) := by
    rw [h1, Clopens.coe_top]
    exact Set.mem_univ p
  rw [Clopens.coe_finset_sup] at h2
  obtain ⟨a, haT, hpa⟩ := Set.mem_iUnion₂.1 h2
  have ha : a ∈ shadowAtoms L := (shadowAtoms_finite L).mem_toFinset.1 haT
  refine ⟨a, ⟨ha, hpa⟩, fun b ⟨hb, hpb⟩ => ?_⟩
  by_contra hba
  have hd : b ⊓ a = ⊥ :=
    disjoint_iff.1 (shadowAtoms_pairwiseDisjoint L hb ha hba : Disjoint b a)
  have hmem : p ∈ (stoneRepr B (b ⊓ a) : Set (StoneSpace B)) := by
    rw [OrderIso.map_inf, Clopens.coe_inf]
    exact ⟨hpb, hpa⟩
  rw [hd, OrderIso.map_bot, Clopens.coe_bot] at hmem
  exact (Set.mem_empty_iff_false p).1 hmem

/-- The **shadow map** of a finite subalgebra: a Stone point goes to the piece containing it. -/
noncomputable def shadowMap (L : BooleanSubalgebra B) [Finite L] (p : StoneSpace B) :
    shadowAtoms L :=
  ⟨(existsUnique_shadowAtom_mem L p).exists.choose,
    (existsUnique_shadowAtom_mem L p).exists.choose_spec.1⟩

variable (L : BooleanSubalgebra B) [Finite L]

theorem mem_stoneRepr_shadowMap (p : StoneSpace B) :
    p ∈ (stoneRepr B (shadowMap L p) : Set (StoneSpace B)) :=
  (existsUnique_shadowAtom_mem L p).exists.choose_spec.2

theorem shadowMap_eq_iff {p : StoneSpace B} {a : shadowAtoms L} :
    shadowMap L p = a ↔ p ∈ (stoneRepr B a : Set (StoneSpace B)) := by
  refine ⟨fun h => by rw [← h]; exact mem_stoneRepr_shadowMap L p, fun h => Subtype.ext ?_⟩
  exact (existsUnique_shadowAtom_mem L p).unique
    ⟨(shadowMap L p).2, mem_stoneRepr_shadowMap L p⟩ ⟨a.2, h⟩

/-- **The classes of the shadow are the clopens of its pieces.** -/
theorem shadowMap_fibre (a : shadowAtoms L) :
    shadowMap L ⁻¹' {a} = (stoneRepr B a : Set (StoneSpace B)) :=
  Set.ext fun _ => shadowMap_eq_iff L

theorem isClopen_shadowMap_fibre (a : shadowAtoms L) : IsClopen (shadowMap L ⁻¹' {a}) := by
  rw [shadowMap_fibre]
  exact (stoneRepr B a).isClopen

/-- **Every piece is seen**: the shadow map is onto. -/
theorem shadowMap_surjective : Surjective (shadowMap L) := by
  intro a
  have hne : (stoneRepr B a : Set (StoneSpace B)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    apply ne_bot_of_mem_shadowAtoms a.2
    apply (stoneRepr B).injective
    rw [OrderIso.map_bot]
    exact SetLike.coe_injective (h.trans Clopens.coe_bot.symm)
  obtain ⟨p, hp⟩ := hne
  exact ⟨p, (shadowMap_eq_iff L).2 hp⟩

/-- **A piece is genuine exactly when its class is a single point.** -/
theorem isAtom_iff_fibre_eq_singleton (a : shadowAtoms L) :
    IsAtom (a : B) ↔ ∃ p, shadowMap L ⁻¹' {a} = {p} := by
  rw [shadowMap_fibre, ← OrderIso.isAtom_iff (stoneRepr B) (a : B)]
  refine ⟨isAtom_clopens_isSingleton, fun ⟨p, hp⟩ => ?_⟩
  have hcl : IsClopen ({p} : Set (StoneSpace B)) := by
    rw [← hp]
    exact (stoneRepr B a).isClopen
  have heq : stoneRepr B a = ⟨{p}, hcl⟩ := SetLike.coe_injective hp
  rw [heq]
  exact isAtom_clopens_of_singleton hcl

/-- **On a gunky algebra every class of every shadow is infinite.** -/
theorem shadowMap_fibre_infinite (hg : IsGunky B) (a : shadowAtoms L) :
    (shadowMap L ⁻¹' {a}).Infinite := by
  obtain ⟨p, hp⟩ := shadowMap_surjective L a
  have hperf := isGunky_iff_perfect_stoneSpace.1 hg
  rw [perfectSpace_iff_forall_not_isolated] at hperf
  have := hperf p
  rw [shadowMap_fibre]
  exact infinite_of_mem_nhds p
    ((stoneRepr B a).isClopen.isOpen.mem_nhds ((shadowMap_eq_iff L).1 hp))

open Classical in
/-- **The observer that reports the piece** is metric, has a finite quotient, and, on a gunky
algebra, only infinite classes. -/
theorem shadowObserver_class_infinite {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    (Tolerance.ofReport (shadowMap L) R).Metric ∧
      Finite (Quotient ((Tolerance.ofReport (shadowMap L) R).zeroSetoid
        (Tolerance.ofReport_metric _))) ∧
      (IsGunky B → ∀ p,
        {q | (Tolerance.ofReport (shadowMap L) R).Indistinguishable p q}.Infinite) := by
  refine ⟨Tolerance.ofReport_metric _, ?_, fun hg p => ?_⟩
  · have : Finite (shadowAtoms L) := shadowAtoms_finite L
    refine Finite.of_injective (fun q => Quotient.lift (shadowMap L)
      (fun x y (h : (Tolerance.ofReport (shadowMap L) R).Indistinguishable x y) =>
        (Tolerance.ofReport_indistinguishable (R := R) _ x y).1 h) q) ?_
    intro q₁ q₂ h
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q₁
    obtain ⟨y, rfl⟩ := Quotient.exists_rep q₂
    exact Quotient.sound ((Tolerance.ofReport_indistinguishable (R := R) _ x y).2 h)
  · refine (shadowMap_fibre_infinite L hg (shadowMap L p)).mono
      fun q (hq : shadowMap L q = shadowMap L p) => ?_
    exact (Tolerance.ofReport_indistinguishable (R := R) _ p q).2 hq.symm

end Mettapedia.Logic.Metaphysics.Ultrainfinite
