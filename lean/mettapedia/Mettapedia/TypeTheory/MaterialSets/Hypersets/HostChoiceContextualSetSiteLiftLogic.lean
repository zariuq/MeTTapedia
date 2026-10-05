import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLift
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetTheorySoundness
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualBoundedFormulaComparison

/-!
# Logical comparison for the actual successor-site set embedding

Raising the site retains the same lower values and all original futures,
so every first-order formula has its original lower interpretation. The
actual embedding into the larger material carrier additionally preserves
and reflects every bounded formula. Its membership hypotheses are proved
from the full coalgebra square, not supplied as a compatibility interface.
External host dependencies come from the actual two contextual set models.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftLogic

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open ContextualMaterialLogic ContextualBoundedFormulaComparison
open HostChoiceContextualSetSiteLift HostChoiceContextualSetInterpretation

universe u
variable {D : Type u} [Category.{u} D]

def lowerModel : Model (source (D := D)) where
  member point child parent := Member point.down child parent
  member_transport := by
    intro point target arrow child parent belongs
    exact HostChoiceContextualSetInterpretation.member_transport arrow.down belongs

noncomputable def membershipEmbedding :
    MembershipEmbedding (lowerModel (D := D))
      (HostChoiceContextualMaterialLogic.model (D := UpperSite (D := D))) where
  valueMap := embedding
  injective := embedding_injective
  member_iff point child parent := current_member_embedding_iff point parent child
  member_onto point parent child belongs := by
    obtain ⟨original, same, _⟩ := (current_member_image point parent child).mp belongs
    exact ⟨original, same⟩

theorem lower_transport {n : Nat} {point target : UpperSite (D := D)} (arrow : point ⟶ target)
    (environment : Environment source n point) :
    ContextualMaterialLogic.transport source arrow environment = ContextualMaterialLogic.transport lowerSets arrow.down environment := by
  funext index
  rfl

/-- All original futures are present after the site is raised. This comparison
changes the context presentation, not the lower material value carrier. -/
theorem lower_force_iff {n : Nat} (formula : Formula n) (point : UpperSite (D := D))
    (environment : Environment source n point) :
    force source lowerModel formula point environment ↔
      force lowerSets (HostChoiceContextualMaterialLogic.model (D := D)) formula point.down environment := by
  induction formula generalizing point with
  | bottom => exact Iff.rfl
  | equal _ _ => exact Iff.rfl
  | member _ _ => exact Iff.rfl
  | both _ _ firstIH secondIH => exact and_congr (firstIH point environment) (secondIH point environment)
  | either _ _ firstIH secondIH => exact or_congr (firstIH point environment) (secondIH point environment)
  | imply first second firstIH secondIH =>
    constructor
    · intro lower target arrow premise
      let raised : point ⟶ ULift.up target := ULift.up arrow
      have oldPremise := (firstIH (ULift.up target) (ContextualMaterialLogic.transport source raised environment)).mpr premise
      exact (secondIH (ULift.up target) (ContextualMaterialLogic.transport source raised environment)).mp
        (lower (ULift.up target) raised oldPremise)
    · intro old target arrow premise
      exact (secondIH target (ContextualMaterialLogic.transport source arrow environment)).mpr
        (old target.down arrow.down ((firstIH target (ContextualMaterialLogic.transport source arrow environment)).mp premise))
  | all body bodyIH =>
    constructor
    · intro lower target arrow value
      let raised : point ⟶ ULift.up target := ULift.up arrow
      exact (bodyIH (ULift.up target) (extend source (ContextualMaterialLogic.transport source raised environment) value)).mp
        (lower (ULift.up target) raised value)
    · intro old target arrow value
      exact (bodyIH target (extend source (ContextualMaterialLogic.transport source arrow environment) value)).mpr
        (old target.down arrow.down value)
  | exist body bodyIH =>
    exact exists_congr fun value => bodyIH point (extend source environment value)

theorem raised_lower_valid_theory : ContextualMaterialSetTheory.ValidTheory (lowerModel (D := D)) := by
  intro n formula adopted point environment
  exact (lower_force_iff formula point environment).mpr
    (HostChoiceContextualSetTheorySoundness.valid_theory adopted point.down environment)

/-- Bounded truth agrees in the original lower model and the actual larger
material model, including all implication and member-quantifier futures. -/
theorem bounded_force_iff {n : Nat} {formula : Formula n} (bounded : Bounded formula)
    (point : UpperSite (D := D)) (environment : Environment source n point) :
    force lowerSets (HostChoiceContextualMaterialLogic.model (D := D)) formula point.down environment ↔
      force upperSets (HostChoiceContextualMaterialLogic.model (D := UpperSite (D := D))) formula point
        (mapEnvironment embedding point environment) :=
  (lower_force_iff formula point environment).symm.trans
    (force_iff lowerModel (HostChoiceContextualMaterialLogic.model (D := UpperSite (D := D)))
      membershipEmbedding bounded point environment)

theorem bounded_substitution_iff {n m : Nat} {formula : Formula n} (bounded : Bounded formula)
    (indices : Fin n → Fin m) (point : UpperSite (D := D)) (environment : Environment source m point) :
    force lowerSets (HostChoiceContextualMaterialLogic.model (D := D)) (substitute indices formula)
      point.down environment ↔
      force upperSets (HostChoiceContextualMaterialLogic.model (D := UpperSite (D := D)))
        (substitute indices formula) point (mapEnvironment embedding point environment) :=
  bounded_force_iff (bounded_substitute bounded indices) point environment

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftLogic
