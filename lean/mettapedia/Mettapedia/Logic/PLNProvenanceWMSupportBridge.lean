import Mettapedia.Logic.LP.Provenance
import Mettapedia.Logic.PLNWorldModelGeneric
import Mettapedia.Logic.PLNWorldModelSupportForgetting
import Provenance.Semirings.Which

/-!
# Provenance→WM Support Bridge

Bridge the LP provenance surface (`KRelation`, `Which`) to WM support-tracked
forgetting interfaces without changing core WM semantics.
-/

namespace Mettapedia.Logic

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelGeneric
open Mettapedia.Logic.LP

variable {σ : LPSignature} {n : ℕ}

noncomputable instance : EvidenceType (KRelation σ (Which (Fin n))) where
  toAddCommMonoid := inferInstance

/-- Identity evidence extraction for `Which`-valued K-relations. -/
noncomputable instance : GenericWorldModel
    (KRelation σ (Which (Fin n))) (GroundAtom σ) (Which (Fin n)) where
  evidence := fun I q => I q
  evidence_add := by
    intro I₁ I₂ q
    simp [Pi.add_apply]

/-- Finite support footprint of provenance sources for a query annotation. -/
def whichSupport (I : KRelation σ (Which (Fin n))) (q : GroundAtom σ) : Finset (Fin n) :=
  match I q with
  | Which.wset s => s
  | Which.wbot => ∅

theorem whichSupport_eq_empty_of_zero
    (I : KRelation σ (Which (Fin n))) (q : GroundAtom σ)
    (hq : I q = (0 : Which (Fin n))) :
    whichSupport I q = ∅ := by
  unfold whichSupport
  rw [hq]

/-- `Which` support under additive state revision is set union. -/
theorem whichSupport_add_union
    (I₁ I₂ : KRelation σ (Which (Fin n))) (q : GroundAtom σ) :
    whichSupport (I₁ + I₂) q = whichSupport I₁ q ∪ whichSupport I₂ q := by
  unfold whichSupport
  cases h₁ : I₁ q <;> cases h₂ : I₂ q <;> simp [h₁, h₂]

theorem whichSupport_add_subset
    {S : Finset (Fin n)}
    (Δ₁ Δ₂ : KRelation σ (Which (Fin n))) (q : GroundAtom σ)
    (h₁ : whichSupport Δ₁ q ⊆ S)
    (h₂ : whichSupport Δ₂ q ⊆ S) :
    whichSupport (Δ₁ + Δ₂) q ⊆ S := by
  rw [whichSupport_add_union]
  exact Finset.union_subset h₁ h₂

/-- Typed transport wrapper from `whichSupport` containment into the existing
outside-scope zero consequence theorem. -/
theorem exactInverse_supported_outside_zero_of_whichSupport
    {Scope : Type*}
    (F : SupportTrackedForgettingLayer
      (KRelation σ (Which (Fin n))) Scope (GroundAtom σ) (Which (Fin n)) (Fin n))
    (hzero : GenericWorldModelZeroPreserving
      (State := KRelation σ (Which (Fin n)))
      (Query := GroundAtom σ) (Ev := Which (Fin n)))
    (hsupport : ∀ I q, F.support I q = whichSupport (σ := σ) (n := n) I q)
    {S : Scope} {Δ : KRelation σ (Which (Fin n))}
    (hsupp : ∀ q, whichSupport (σ := σ) (n := n) Δ q ⊆ F.scopeFootprint S) :
    ∀ q, ¬ F.inScope S q →
      GenericWorldModel.evidence
        (State := KRelation σ (Which (Fin n)))
        (Query := GroundAtom σ) (Ev := Which (Fin n)) Δ q = 0 := by
  have hsupp' : ∀ q, F.support Δ q ⊆ F.scopeFootprint S := by
    intro q
    simpa [hsupport Δ q] using hsupp q
  exact SupportTrackedForgettingLayer.exactInverse_revision_supported_outside_zero
    F hzero hsupp'

/-- Tagged `Which` support: `none` marks nonzero lineage, while `some i` carries
source-level provenance indices. This avoids conflating `wbot` with `wset ∅`. -/
def whichSupportTagged
    (I : KRelation σ (Which (Fin n))) (q : GroundAtom σ) : Finset (Option (Fin n)) :=
  match I q with
  | Which.wbot => ∅
  | Which.wset s => insert none (Finset.image some s)

theorem which_eq_zero_of_supportTagged_subset_empty
    (I : KRelation σ (Which (Fin n))) (q : GroundAtom σ)
    (hsub : whichSupportTagged (σ := σ) (n := n) I q ⊆ (∅ : Finset (Option (Fin n)))) :
    I q = 0 := by
  cases hI : I q with
  | wbot =>
      rfl
  | wset s =>
      have hnone :
          (none : Option (Fin n)) ∈ whichSupportTagged (σ := σ) (n := n) I q := by
        simp [whichSupportTagged, hI]
      have hempty : (none : Option (Fin n)) ∈ (∅ : Finset (Option (Fin n))) := hsub hnone
      simp at hempty

theorem krelationWhich_zeroPreserving :
    GenericWorldModelZeroPreserving
      (State := KRelation σ (Which (Fin n)))
      (Query := GroundAtom σ) (Ev := Which (Fin n)) := by
  intro q
  rfl

/-- Concrete support-tracked forgetting instance over `Which` K-relations with an
empty scope footprint. The only revisions admitted by support containment are
zero revisions, making exact inverse forgetting theorem-complete. -/
noncomputable def whichEmptyScopeForgettingLayer :
    SupportTrackedForgettingLayer
      (KRelation σ (Which (Fin n))) Unit (GroundAtom σ) (Which (Fin n)) (Option (Fin n)) where
  inScope := fun _ _ => False
  forget := fun _ W => W
  idempotent := by
    intro S W
    rfl
  outsideInvariant := by
    intro S W q hout
    rfl
  scopeFootprint := fun _ => ∅
  support := whichSupportTagged (σ := σ) (n := n)
  exactInverse_of_supported := by
    intro S Δ hsupp W
    funext q
    have hΔq : Δ q = 0 := by
      exact which_eq_zero_of_supportTagged_subset_empty
        (σ := σ) (n := n) Δ q (by simpa using hsupp q)
    simp [Pi.add_apply, hΔq]

theorem whichEmptyScope_exactInverse_of_supported
    {Δ : KRelation σ (Which (Fin n))}
    (hsupp :
      ∀ q, whichSupportTagged (σ := σ) (n := n) Δ q ⊆ (∅ : Finset (Option (Fin n)))) :
    ∀ W : KRelation σ (Which (Fin n)),
      (whichEmptyScopeForgettingLayer (σ := σ) (n := n)).forget () (W + Δ) = W := by
  exact SupportTrackedForgettingLayer.exactInverse_revision_of_support_subset
    (F := whichEmptyScopeForgettingLayer (σ := σ) (n := n))
    (S := ()) (Δ := Δ)
    (by
      intro q
      exact hsupp q)

theorem whichEmptyScope_revision_zero_of_supported
    {Δ : KRelation σ (Which (Fin n))}
    (hsupp :
      ∀ q, whichSupportTagged (σ := σ) (n := n) Δ q ⊆ (∅ : Finset (Option (Fin n)))) :
    ∀ q,
      GenericWorldModel.evidence
        (State := KRelation σ (Which (Fin n)))
        (Query := GroundAtom σ) (Ev := Which (Fin n)) Δ q = 0 := by
  intro q
  have hout :
      ¬ (whichEmptyScopeForgettingLayer (σ := σ) (n := n)).inScope () q := by
    simp [whichEmptyScopeForgettingLayer]
  exact SupportTrackedForgettingLayer.exactInverse_revision_supported_outside_zero
    (F := whichEmptyScopeForgettingLayer (σ := σ) (n := n))
    (hzero := krelationWhich_zeroPreserving (σ := σ) (n := n))
    (S := ()) (Δ := Δ)
    (hsupp := by
      intro q'
      exact hsupp q')
    q hout

end Mettapedia.Logic
