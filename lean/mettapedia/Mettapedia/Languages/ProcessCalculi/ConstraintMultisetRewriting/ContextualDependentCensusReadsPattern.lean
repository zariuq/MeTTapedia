import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusReads

/-!
# The census half of coverage: pattern rows read by R107's and R110's firing theorems

R107 and R110 proved that three pattern rules fire, from some budget on, on an equation of a store in the dynamic
pattern fragment and in a named row: R94's conversion pattern rule on the inversion row for the newest metavariable
(`ContextualDependentPatternFiring.patternRuleConv_fires`), the rigid rule on the rigid out-of-scope row, with the
metavariable on either side (`rigidRule_fires`, `rigidRule_fires_right`), and R86's in-place rule on the placed row at
a positive depth (`placedRule_fires`). Each of these rules is a row of R110's flexible round, so each row is an
under-binder reader (`tower_underReads_of_inversion`, `tower_underReads_of_rigidOutside`,
`tower_underReads_of_rigidOutsideRight`, `tower_underReads_of_placed`). The rigid rule's normality certificate is
complete in the tower (`tower_certifies`).

These rows ask the equation itself to be in the dynamic pattern fragment. A store of the permuted Miller class need
not have such an equation: its census head lives on the prepared store and its sides are only Miller, with no arity
condition. Carrying these rows to the census head is open.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCoverageReadersHalf

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring ContextualDependentPatternFiring.Controls

/-- The tower's normality certificate accepts every normal term. -/
theorem tower_certifies {n : Nat} (term : Tower.Tm n) (normal : ContextualDependentExecutableJoin.Normal Tower.rules term) :
    (ContextualDependentGeneralPattern.DispatchControls.certifyNormal term).isSome := by
  unfold ContextualDependentGeneralPattern.DispatchControls.certifyNormal
  rw [dif_pos ((ContextualDependentNormalizing.normal_iff_step_none rfl term).mp normal)]
  rfl

/-- **The inversion row is read** by R94's conversion pattern rule. -/
theorem tower_underReads_of_inversion {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ))
    {equation : Equation (TotalTerm Θ)} (member : equation ∈ problem) (inside : InFragment equation)
    (nonempty : 0 < Θ.arity) (newestNormal : ContextualDependentExecutableJoin.Normal Tower.rules
      (Ctx.lookup Θ.raw ⟨0, nonempty⟩))
    (row : ∀ view : ContextualDependentWorklist.Newest Θ, InversionRow (view.same ▸ equation)) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerUnderReads larger problem := by
  obtain ⟨bound, fires⟩ := patternRuleConv_fires (fun _ => (0 : Nat)) ContextualDependentPiSpine.Controls.rigid
    TowerModel.complete ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal problem member inside nonempty newestNormal row
  exact ⟨bound, fun larger enough =>
    .full <| .inl <| .inl <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <| fires larger enough⟩

/-- **The rigid out-of-scope row is read** by the rigid rule. -/
theorem tower_underReads_of_rigidOutside {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ))
    {equation : Equation (TotalTerm Θ)} (member : equation ∈ problem) (inside : InFragment equation)
    (row : RigidOutside equation) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerUnderReads larger problem := by
  obtain ⟨bound, fires⟩ := rigidRule_fires (fun _ => (0 : Nat)) ContextualDependentPiSpine.Controls.rigid
    TowerModel.complete ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal problem member inside row tower_certifies
  exact ⟨bound, fun larger enough =>
    .full <| .inl <| .inl <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <| fires larger enough⟩

/-- **The rigid out-of-scope row with the metavariable on the right is read** by the rigid rule. -/
theorem tower_underReads_of_rigidOutsideRight {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ))
    {equation : Equation (TotalTerm Θ)} (member : equation ∈ problem) (inside : InFragment equation)
    (row : RigidOutsideRight equation) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerUnderReads larger problem := by
  obtain ⟨bound, fires⟩ := rigidRule_fires_right (fun _ => (0 : Nat)) ContextualDependentPiSpine.Controls.rigid
    TowerModel.complete ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal problem member inside row tower_certifies
  exact ⟨bound, fun larger enough =>
    .full <| .inl <| .inl <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <| fires larger enough⟩

/-- **The placed row is read** by R86's in-place rule at a positive depth. -/
theorem tower_underReads_of_placed {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ))
    {equation : Equation (TotalTerm Θ)} (member : equation ∈ problem) {depth : Nat} (positive : 0 < depth)
    (row : PlacedRow (fun _ => (0 : Nat)) depth equation) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerUnderReads larger problem := by
  obtain ⟨bound, fires⟩ := placedRule_fires (fun _ => (0 : Nat)) ContextualDependentPiSpine.Controls.rigid
    TowerModel.complete ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal problem member positive row
  exact ⟨bound, fun larger enough =>
    .full <| .inl <| .inl <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inr <| .inl <| fires larger enough⟩

end ContextualDependentCoverageReadersHalf
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
