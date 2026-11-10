import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusReadsValid
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaDepthSkeletonFamily

/-!
# The census half of coverage: valid census heads

`tower_underReads_of_valid` reads a valid equation of the store itself; the census head lives on the prepared store.
**Preparation reflects valid equations** (`tower_prepare_valid`): bounded normalization replaces each side by an
equivalent one (`termAt_equivalent`), and context normalization reindexes along an isomorphism, whose inverse brings a
valid equation back (`contextStep_valid`). So **a valid census head is read**, at every budget from the scan's bound on
(`tower_underReads_of_validHead`); no constancy of preparation is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCoverageReadersHalf

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

section Tower

open ContextualDependentPatternFiring.Controls

/-- **Context normalization reflects valid equations.** -/
theorem contextStep_valid (fuel : Nat) {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    (prepared : Update setting.levels problem)
    (same : prepared = ContextualDependentNormalizing.contextStep (S := setting) (fun _ => none)
      (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
      TowerModel.heads fuel problem)
    {moved : Equation (TotalTerm prepared.target)} (member : moved ∈ prepared.remaining)
    (valid : (frames setting.levels).E moved.1 moved.2) :
    ∃ equation ∈ problem, (frames setting.levels).E equation.1 equation.2 := by
  unfold ContextualDependentNormalizing.contextStep at same
  split at same
  · subst same
    exact ⟨moved, member, valid⟩
  · rename_i normalized _
    subst same
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    refine ⟨original, originalMember, ?_⟩
    have back := (frames setting.levels).preserves normalized.iso.inv valid
    rw [← (frames setting.levels).act_comp, ← (frames setting.levels).act_comp] at back
    have identity : (frames setting.levels).comp normalized.iso.inv normalized.iso.hom =
        (frames setting.levels).id Θ := normalized.iso.inv_hom_id
    rw [identity, (frames setting.levels).act_id, (frames setting.levels).act_id] at back
    exact back

/-- **Preparation reflects valid equations**: a valid equation of the prepared store comes from a valid equation of
the store. -/
theorem tower_prepare_valid (fuel : Nat) {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm (towerPrepare fuel problem).target)}
    (member : equation ∈ (towerPrepare fuel problem).remaining)
    (valid : (frames setting.levels).E equation.1 equation.2) :
    ∃ original ∈ problem, (frames setting.levels).E original.1 original.2 := by
  have eqv := (frames setting.levels).equivalence (towerPrepare fuel problem).target
  obtain ⟨moved, movedMember, rfl⟩ := List.mem_map.mp member
  have first := ContextualDependentNormalization.termAt_equivalent (S := setting) (fun _ => none) TowerModel.facts
    TowerModel.roots TowerModel.heads fuel moved.1
  have second := ContextualDependentNormalization.termAt_equivalent (S := setting) (fun _ => none) TowerModel.facts
    TowerModel.roots TowerModel.heads fuel moved.2
  exact contextStep_valid fuel _ rfl movedMember (eqv.trans first (eqv.trans valid (eqv.symm second)))

/-- **A valid census head is read** by the conversion scan from some budget on. -/
theorem tower_underReads_of_validHead {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat} {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (valid : (frames setting.levels).E equation.1 equation.2) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerUnderReads larger problem := by
  obtain ⟨original, originalMember, originalValid⟩ := tower_prepare_valid threshold member valid
  exact tower_underReads_of_valid originalMember originalValid

end Tower

end ContextualDependentCoverageReadersHalf
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
