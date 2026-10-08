import Mettapedia.OSLF.Framework.FundedNuReceiptPresheaves

/-!
# Complete observation classes, resource changes and certificate controls

Three available instruction cells distinguish finite chain lengths zero,
one and two. Length three shares the persistent loop's complete profile;
one more cell separates them. A visible dependent value is retained through
the actual observation family, while a hidden-length family cannot descend.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.FundedNuObservationControls

open FundedNuObservationClasses FundedNuBudgetDiagram FundedNuObservationEvidence
open FundedNuObservedPresheaves FundedNuReceiptPresheaves
open FundedNuBudgetSeparation
open _root_.CategoryTheory _root_.Opposite

theorem actual_three_cell_classes :
    classify 3 (some 0) = some ⟨0, by decide⟩ ∧
      classify 3 (some 1) = some ⟨1, by decide⟩ ∧
      classify 3 (some 2) = some ⟨2, by decide⟩ ∧
      classify 3 (some 3) = none ∧ classify 3 none = none := by decide

theorem actual_four_profiles : Nat.card (ActualProfile 3) = 4 := actual_profile_cardinality 3

theorem complete_actual_profiles_separate_short_chains : view 3 (some 0) ≠ view 3 (some 2) := by
  intro same
  have codes := (profile_equality_classifies 3 (some 0) (some 2)).mp same
  have different : classify 3 (some 0) ≠ classify 3 (some 2) := by decide
  exact different codes

theorem one_more_cell_separates_complete_profiles :
    view 3 (some 3) = view 3 none ∧ view 4 (some 3) ≠ view 4 none := by
  refine ⟨bounded_views_agree 3 3 le_rfl, ?_⟩
  intro same
  have codes := (profile_equality_classifies 4 (some 3) none).mp same
  have different : classify 4 (some 3) ≠ classify 4 none := by decide
  exact different codes

theorem larger_information_restricts :
    restriction 3 4 (by decide) (some ⟨3, by decide⟩) = none ∧
      restriction 3 4 (by decide) (some ⟨2, by decide⟩) = some ⟨2, by decide⟩ := by decide

theorem composed_resource_change :
    restriction 2 3 (by decide) (restriction 3 5 (by decide) (some ⟨1, by decide⟩)) =
      restriction 2 5 (by decide) (some ⟨1, by decide⟩) :=
  restriction_composition 2 3 5 (by decide) (by decide) _

theorem genuinely_varying_visible_fibres :
    ¬ Nonempty (visibleCertificate 3 (some ⟨0, by decide⟩) ≃
      visibleCertificate 3 (some ⟨2, by decide⟩)) := by
  change ¬ Nonempty (Fin 1 ≃ Fin 3)
  rintro ⟨equivalence⟩
  have same : equivalence.symm ⟨0, by decide⟩ = equivalence.symm ⟨1, by decide⟩ :=
    Subsingleton.elim _ _
  have collision := congrArg Fin.val (equivalence.symm.injective same)
  change (0 : Nat) = 1 at collision
  omega

theorem actual_visible_witness_roundtrip :
    ((familyFactorization 3 (visibleCertificate 3)).identify (some 2)).symm
      ((familyFactorization 3 (visibleCertificate 3)).identify (some 2)
        (visibleWitness 3 (classify 3 (some 2)))) = visibleWitness 3 (classify 3 (some 2)) :=
  supplied_witness_recovered 3 (visibleCertificate 3) (some 2) _

theorem actual_observed_code_retains_value :
    (imageEquivalence 3).symm (actualView 3 (some 2)) = some ⟨2, by decide⟩ :=
  observed_class_readout 3 (some 2)

theorem actual_hidden_fibre_boundary :
    ¬ Nonempty (Mettapedia.TypeTheory.DependentFamilyObserverFactorization.FamilyFactorization
      (actualView 3) hiddenCertificate) := hidden_certificate_does_not_descend 3

theorem actual_profile_resource_square :
    actualRestriction 3 4 (by decide) (actualView 4 (some 3)) = actualView 3 (some 3) :=
  actualRestriction_state 3 4 (by decide) (some 3)

theorem supplied_origin_survives_visibility_loss :
    (classOrigins.map (classStateArrow 0 3 (by decide) (some 2))
      (classReceipt 3 (some 2))).val = some 2 ∧ classify 0 (some 2) = none := by
  constructor
  · rw [class_receipt_restriction]
    rfl
  · decide

theorem actual_receipt_survives_resource_change :
    (actualOrigins.map (actualStateArrow 3 4 (by decide) (some 3))
      (actualReceipt 4 (some 3))).val = some 3 := by
  rw [actual_receipt_restriction]
  rfl

theorem same_actual_observation_distinct_receipts :
    actualView 3 (some 3) = actualView 3 none ∧
      (actualReceipt 3 (some 3)).val ≠ (actualReceipt 3 none).val := by
  constructor
  · apply Subtype.ext
    exact bounded_views_agree 3 3 le_rfl
  · exact Option.some_ne_none 3

theorem genuinely_varying_origin_fibres :
    ¬ Nonempty (classOrigins.obj ⟨op 3, some ⟨2, by decide⟩⟩ ≃
      classOrigins.obj ⟨op 3, none⟩) := by
  rintro ⟨equivalence⟩
  let loop : classOrigins.obj ⟨op 3, none⟩ := ⟨none, rfl⟩
  let longer : classOrigins.obj ⟨op 3, none⟩ := ⟨some 3, by
    change classify 3 (some 3) = none
    decide⟩
  have same : equivalence.symm loop = equivalence.symm longer := by
    apply Subtype.ext
    exact (finite_class_origin_unique 3 ⟨2, by decide⟩ _ (equivalence.symm loop).property).trans
      (finite_class_origin_unique 3 ⟨2, by decide⟩ _ (equivalence.symm longer).property).symm
  have collision := congrArg Subtype.val (equivalence.symm.injective same)
  change (none : Option Nat) = some 3 at collision
  cases collision

theorem supplied_native_origin_recovers :
    originFamilyRecovery.inv.app ⟨op 3, classify 3 (some 2)⟩
      (originFamilyRecovery.hom.app ⟨op 3, classify 3 (some 2)⟩
        (classReceipt 3 (some 2))) = classReceipt 3 (some 2) :=
  supplied_origin_recovered _ _

theorem observations_alone_cannot_choose_coherent_origins :
    ¬ ∃ decoder : actualProfiles ⟶ (Functor.const Natᵒᵖ).obj (Option Nat),
      decoder ≫ actualClassifications = 𝟙 actualProfiles :=
  actual_observations_no_natural_section

end Mettapedia.OSLF.Framework.FundedNuObservationControls
