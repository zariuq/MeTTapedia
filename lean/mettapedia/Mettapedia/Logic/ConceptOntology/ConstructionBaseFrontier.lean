import Mettapedia.Logic.ConceptOntology.ConstructionBase
import Mettapedia.Logic.StoneGunkDuality

/-!
# Construction-Base Frontier Order

This module isolates the order-theoretic "frontier object" of a concept's credal
state. The key design choice is to avoid forcing a Boolean algebra on a finite
gate family or finite concept frontier, since those carriers are typically
atomic for accidental reasons.

Instead, for a concept `A` we take the **frontier shadow order**

`Set.Iic (conceptCredalFrontierHeight Γ M A) ⊆ ℝ≥0`

where the height is the actual width verdict of the concept-formation gamble,
collapsed to the only values the current theory permits (`0` or `1`).

This yields the honest theoremic separation:

* `openWorldConcept` iff the frontier shadow order is **nontrivial**;
* `openWorldConcept` also gives the frontier shadow a **gunky face** by placing it
  inside the ambient gunky interval `[0,1] ⊆ NNReal`;
* `thatsAllConcept` forces the frontier shadow order to collapse to a singleton.

So the open/closed-world dial lands on a real frontier object, but at the right
abstraction layer: the **credal state of the concept**, not the raw predictive
sample-space algebra.
-/

namespace Mettapedia.Logic.ConceptOntology

open Mettapedia.Foundations.Gunk

universe u v

section FrontierShadow

variable {Obj : Type u} {Attr : Type v} {Q : Type} {Gate : Type}
variable [Preorder Q]
variable [Fintype Gate] [Nonempty Gate]
variable [Fintype Obj] [Fintype Attr]

attribute [local instance] Classical.propDecidable

/-- The `0/1` shadow of a concept's credal-width verdict, read as a frontier
height in `NNReal`. `1` means the concept sits in the lower/upper gap; `0` means
the frontier has collapsed. -/
noncomputable def conceptCredalFrontierHeight
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : AbstractInheritance.DualConcept Obj Attr) : NNReal :=
  if openWorldConcept (Obj := Obj) (Attr := Attr) (Q := Q) (Gate := Gate) Γ M A
    then (1 : NNReal) else 0

/-- The frontier object of a concept's credal state: the order interval under
its `0/1` frontier height shadow. Open-world concepts get a nontrivial interval;
collapsed concepts get the singleton interval `{0}`. -/
abbrev conceptCredalFrontierOrder
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : AbstractInheritance.DualConcept Obj Attr) : Type _ :=
  ↥(Set.Iic (conceptCredalFrontierHeight Γ M A))

omit [Fintype Gate] [Nonempty Gate] in
theorem conceptCredalFrontierHeight_eq_one_iff_openWorldConcept
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : AbstractInheritance.DualConcept Obj Attr) :
    conceptCredalFrontierHeight Γ M A = 1 ↔
      openWorldConcept (Obj := Obj) (Attr := Attr) (Q := Q) (Gate := Gate) Γ M A := by
  by_cases hOpen :
      openWorldConcept (Obj := Obj) (Attr := Attr) (Q := Q) (Gate := Gate) Γ M A
  · simp [conceptCredalFrontierHeight, hOpen]
  · simp [conceptCredalFrontierHeight, hOpen]

omit [Fintype Gate] [Nonempty Gate] in
theorem conceptCredalFrontierHeight_eq_zero_iff_not_openWorldConcept
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : AbstractInheritance.DualConcept Obj Attr) :
    conceptCredalFrontierHeight Γ M A = 0 ↔
      ¬ openWorldConcept (Obj := Obj) (Attr := Attr) (Q := Q) (Gate := Gate) Γ M A := by
  by_cases hOpen :
      openWorldConcept (Obj := Obj) (Attr := Attr) (Q := Q) (Gate := Gate) Γ M A
  · simp [conceptCredalFrontierHeight, hOpen]
  · simp [conceptCredalFrontierHeight, hOpen]

omit [Fintype Gate] [Nonempty Gate] in
theorem conceptCredalFrontierHeight_eq_zero_of_thatsAllConcept
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : AbstractInheritance.DualConcept Obj Attr)
    (hAll : thatsAllConcept (Obj := Obj) (Attr := Attr) (Q := Q) (Gate := Gate) Γ M A) :
    conceptCredalFrontierHeight Γ M A = 0 := by
  have hNotOpen :
      ¬ openWorldConcept (Obj := Obj) (Attr := Attr) (Q := Q) (Gate := Gate) Γ M A := by
    simpa [thatsAllConcept, openWorldConcept] using hAll
  exact (conceptCredalFrontierHeight_eq_zero_iff_not_openWorldConcept
    (Γ := Γ) (M := M) (A := A)).2 hNotOpen

theorem subsingleton_iic_zero_nnreal : Subsingleton ↥(Set.Iic (0 : NNReal)) := by
  refine ⟨?_⟩
  intro x y
  apply Subtype.ext
  have hx : (x : NNReal) = 0 := le_antisymm x.2 bot_le
  have hy : (y : NNReal) = 0 := le_antisymm y.2 bot_le
  simp [hx, hy]

theorem nontrivial_iic_one_nnreal : Nontrivial ↥(Set.Iic (1 : NNReal)) := by
  refine ⟨⟨0, by simp⟩, ⟨1, by simp⟩, ?_⟩
  intro h
  have hval := congrArg Subtype.val h
  simp at hval

omit [Fintype Gate] [Nonempty Gate] in
theorem openWorldConcept_iff_nontrivial_frontierOrder
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : AbstractInheritance.DualConcept Obj Attr) :
    openWorldConcept (Obj := Obj) (Attr := Attr) (Q := Q) (Gate := Gate) Γ M A ↔
      Nontrivial (conceptCredalFrontierOrder Γ M A) := by
  constructor
  · intro hOpen
    have hHeight :
        conceptCredalFrontierHeight Γ M A = 1 :=
      (conceptCredalFrontierHeight_eq_one_iff_openWorldConcept (Γ := Γ) (M := M) (A := A)).2 hOpen
    simpa [conceptCredalFrontierOrder, hHeight] using nontrivial_iic_one_nnreal
  · intro hNontriv
    by_contra hNotOpen
    have hHeight :
        conceptCredalFrontierHeight Γ M A = 0 :=
      (conceptCredalFrontierHeight_eq_zero_iff_not_openWorldConcept (Γ := Γ) (M := M) (A := A)).2 hNotOpen
    have hSub :
        Subsingleton (conceptCredalFrontierOrder Γ M A) := by
      simpa [conceptCredalFrontierOrder, hHeight] using subsingleton_iic_zero_nnreal
    letI : Subsingleton (conceptCredalFrontierOrder Γ M A) := hSub
    haveI : Nontrivial (conceptCredalFrontierOrder Γ M A) := hNontriv
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (conceptCredalFrontierOrder Γ M A)
    exact hxy (Subsingleton.elim x y)

omit [Fintype Gate] [Nonempty Gate] in
theorem isGunky_frontierOrder_of_openWorldConcept
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : AbstractInheritance.DualConcept Obj Attr)
    (hOpen : openWorldConcept (Obj := Obj) (Attr := Attr) (Q := Q) (Gate := Gate) Γ M A) :
    IsGunky (conceptCredalFrontierOrder Γ M A) := by
  have hHeight : conceptCredalFrontierHeight Γ M A = 1 :=
    (conceptCredalFrontierHeight_eq_one_iff_openWorldConcept
      (Γ := Γ) (M := M) (A := A)).2 hOpen
  change IsGunky ↥(Set.Iic (conceptCredalFrontierHeight Γ M A))
  rw [hHeight]
  exact isGunky_Iic (α := NNReal) isGunky_nnreal (1 : NNReal)

omit [Fintype Gate] [Nonempty Gate] in
theorem openWorldConcept_frontierOrder_nontrivial_with_gunkyFace
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : AbstractInheritance.DualConcept Obj Attr) :
    openWorldConcept (Obj := Obj) (Attr := Attr) (Q := Q) (Gate := Gate) Γ M A →
      Nontrivial (conceptCredalFrontierOrder Γ M A) ∧
        IsGunky (conceptCredalFrontierOrder Γ M A) := by
  intro hOpen
  exact ⟨
    (openWorldConcept_iff_nontrivial_frontierOrder (Γ := Γ) (M := M) (A := A)).1 hOpen,
    isGunky_frontierOrder_of_openWorldConcept (Γ := Γ) (M := M) (A := A) hOpen⟩

omit [Fintype Gate] [Nonempty Gate] in
theorem subsingleton_frontierOrder_of_thatsAllConcept
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : AbstractInheritance.DualConcept Obj Attr)
    (hAll : thatsAllConcept (Obj := Obj) (Attr := Attr) (Q := Q) (Gate := Gate) Γ M A) :
    Subsingleton (conceptCredalFrontierOrder Γ M A) := by
  have hHeight : conceptCredalFrontierHeight Γ M A = 0 :=
    conceptCredalFrontierHeight_eq_zero_of_thatsAllConcept (Γ := Γ) (M := M) (A := A) hAll
  simpa [conceptCredalFrontierOrder, hHeight] using subsingleton_iic_zero_nnreal

-- A genuinely open-world frontier shadow cannot be finite: finite nontrivial
-- carriers are never gunky, so any finite-stage frontier approximation
-- collapses the dial.
omit [Fintype Gate] [Nonempty Gate] in
theorem not_openWorldConcept_of_finite_frontierOrder
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : AbstractInheritance.DualConcept Obj Attr)
    [Finite (conceptCredalFrontierOrder Γ M A)] :
    ¬ openWorldConcept (Obj := Obj) (Attr := Attr) (Q := Q) (Gate := Gate) Γ M A := by
  intro hOpen
  have hFrontier :=
    openWorldConcept_frontierOrder_nontrivial_with_gunkyFace
      (Γ := Γ) (M := M) (A := A) hOpen
  letI : Nontrivial (conceptCredalFrontierOrder Γ M A) := hFrontier.1
  exact not_isGunky_of_finite hFrontier.2

-- Any finite frontier carrier forces the concept-state dial to collapse to the
-- `That’s All` side. The genuine atomless/perfect identification cannot live at
-- a finite stage.
omit [Fintype Gate] [Nonempty Gate] in
theorem thatsAllConcept_of_finite_frontierOrder
    (Γ : Gate → EvidenceGate Q) (M : Obj → Attr → Q)
    (A : AbstractInheritance.DualConcept Obj Attr)
    [Finite (conceptCredalFrontierOrder Γ M A)] :
    thatsAllConcept (Obj := Obj) (Attr := Attr) (Q := Q) (Gate := Gate) Γ M A := by
  have hNotOpen :
      ¬ openWorldConcept (Obj := Obj) (Attr := Attr) (Q := Q) (Gate := Gate) Γ M A :=
    not_openWorldConcept_of_finite_frontierOrder (Γ := Γ) (M := M) (A := A)
  simpa [thatsAllConcept, openWorldConcept] using hNotOpen

end FrontierShadow

namespace ControlExample

open ControlCredalExample

theorem flyingFamilyConcept_frontierOrder_nontrivial_with_gunkyFace :
    Nontrivial (conceptCredalFrontierOrder gateFamily context.evidence flyingFamilyConcept) ∧
      IsGunky (conceptCredalFrontierOrder gateFamily context.evidence flyingFamilyConcept) := by
  exact openWorldConcept_frontierOrder_nontrivial_with_gunkyFace
    gateFamily context.evidence flyingFamilyConcept
    flyingFamilyConcept_openWorldConcept

theorem batOnlyFlyingConcept_frontierOrder_subsingleton :
    Subsingleton (conceptCredalFrontierOrder gateFamily context.evidence batOnlyFlyingConcept) := by
  exact
    subsingleton_frontierOrder_of_thatsAllConcept
      gateFamily context.evidence batOnlyFlyingConcept
      batOnlyFlyingConcept_thatsAllConcept

end ControlExample

end Mettapedia.Logic.ConceptOntology
