import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusReads

/-!
# The census half of coverage: valid equations

Some census heads of the rigid kinds are valid: `λ g. g ≐ λ g x. g x` is a pair of distinct rigid heads at the left
side's depth, and its sides are equal by η. No clash reader may read it; the conversion scan drops it. The scan keeps a
sublist of the store (`scan_sublist`), so it shortens every store with an equation it drops (`scan_shorter`), and in the
tower it eventually drops every valid equation (R110's `scan_eventually`). Hence **a store with a valid equation is
read** from some budget on, by the first row of the upper chain (`tower_underReads_of_valid`).

The statement is about an equation of the store itself: the scan reads the store before preparation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCoverageReadersHalf

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

section General

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- The conversion scan keeps a sublist of the store. -/
theorem scan_sublist (fuel : Nat) {Γ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Γ),
      (Conversion.scan facts roots heads algebra reducer fuel problem).Sublist problem
  | [] => List.Sublist.slnil
  | equation :: rest => by
      simp only [Conversion.scan]
      split
      · exact (scan_sublist fuel rest).cons equation
      · exact (scan_sublist fuel rest).cons_cons equation

/-- **The scan shortens a store with an equation it drops.** -/
theorem scan_shorter (fuel : Nat) {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {equation : Equation (TotalTerm Γ)} (member : equation ∈ problem)
    (dropped : equation ∉ Conversion.scan facts roots heads algebra reducer fuel problem) :
    (Conversion.scan facts roots heads algebra reducer fuel problem).length < problem.length := by
  have sub := scan_sublist facts roots heads algebra reducer fuel problem
  rcases Nat.lt_or_ge (Conversion.scan facts roots heads algebra reducer fuel problem).length problem.length with
    shorter | longer
  · exact shorter
  · have same := sub.eq_of_length_le longer
    rw [same] at dropped
    exact absurd member dropped

end General

section Tower

open ContextualDependentPatternFiring.Controls

/-- **Valid equations are read**: a store with an equation whose sides are equal judged terms is shortened by the
conversion scan from some budget on, so the under-binder readers read it. -/
theorem tower_underReads_of_valid {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {equation : Equation (TotalTerm Θ)} (member : equation ∈ problem)
    (valid : (frames setting.levels).E equation.1 equation.2) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerUnderReads larger problem := by
  obtain ⟨bound, kept⟩ := ContextualDependentExecutableDiscovery.scan_eventually (fun _ => (0 : Nat)) problem
  refine ⟨bound, fun larger enough => .full (.inr (.inl ?_))⟩
  exact scan_shorter (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.reducer larger member (fun inside => kept larger enough equation inside valid)

end Tower

end ContextualDependentCoverageReadersHalf
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
