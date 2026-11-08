import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentMillerClosurePermuted

/-!
# R116's closure lemmas transfer to the permuted class

R116's closure lemmas for `StratifiedMiller` are of two kinds, and both transfer to `PermutedMiller` with no new
reasoning:

* **store-wide** steps commute with permutations: a pattern answer on every equation
  (`PermutedMiller.applyStore`), a map that keeps solutions and stratification (`PermutedMiller.map`), such as twin
  retyping (`permutedMiller_collapse_update`), and dropping valid equations (`PermutedMiller.filter_valid`);
* **positional** steps are proved at an arbitrary position `before ++ equation :: after`: replacing an equation by
  pieces with its solutions (`PermutedMiller.splice_of`, generic in the step), such as the pieces of formers under
  abstractions (`PermutedMiller.splice_underParts`).

So a rule that transforms the first equation of the store keeps the permuted class as soon as its `StratifiedMiller`
closure is proved at an arbitrary position, which is how R116 states its splices.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentMillerClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentDynamicFragment ContextualDependentShortClosure
open ContextualDependentHereditary ContextualDependentClosure ContextualDependentExecutableJoin

section General

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}

/-- **A positional step on the first equation keeps the permuted class**, when its `StratifiedMiller` closure holds
at every position. -/
theorem PermutedMiller.splice_of {Θ : Context rules} {equation : Equation (TotalTerm Θ)}
    {rest pieces : EquationStore (TotalTerm Θ)} (permuted : PermutedMiller levels (equation :: rest))
    (step : ∀ before after : EquationStore (TotalTerm Θ), StratifiedMiller levels (before ++ equation :: after) →
      StratifiedMiller levels (before ++ (pieces ++ after))) :
    PermutedMiller levels (pieces ++ rest) := by
  obtain ⟨ordered, perm, stratified⟩ := permuted
  obtain ⟨before, after, rfl⟩ := List.append_of_mem (perm.symm.subset List.mem_cons_self)
  have restPerm : (before ++ after).Perm rest := (List.perm_middle.symm.trans perm).cons_inv
  refine ⟨before ++ (pieces ++ after), ?_, step before after stratified⟩
  rw [← List.append_assoc]
  exact (List.perm_append_comm.append_right after).trans (by
    rw [List.append_assoc]
    exact restPerm.append_left pieces)

/-- **A map that keeps solutions, Miller sides and stratification keeps the permuted class.** -/
theorem PermutedMiller.map {Θ : Context rules} {problem : EquationStore (TotalTerm Θ)}
    (permuted : PermutedMiller levels problem) (f : Equation (TotalTerm Θ) → Equation (TotalTerm Θ))
    (same : ∀ (equation : Equation (TotalTerm Θ)) {Δ : Context rules} (σ : Δ ⟶ Θ),
      (frames levels).Solves σ (f equation) ↔ (frames levels).Solves σ equation)
    (sides : ∀ equation ∈ problem, FragmentSidesMiller equation → FragmentSidesMiller (f equation))
    (annotations : ∀ equation ∈ problem, ∀ before : EquationStore (TotalTerm Θ),
      StratifiedAt levels before equation → StratifiedAt levels before (f equation)) :
    PermutedMiller levels (problem.map f) := by
  obtain ⟨ordered, perm, stratified⟩ := permuted
  exact ⟨ordered.map f, perm.map f, StratifiedMiller.map stratified f same
    (fun equation member => sides equation (perm.subset member))
    (fun equation member => annotations equation (perm.subset member))⟩

/-- **Dropping valid equations keeps the permuted class.** -/
theorem PermutedMiller.filter_valid {Θ : Context rules} (keep : Equation (TotalTerm Θ) → Bool)
    (valid : ∀ equation, keep equation = false → ∀ {Δ : Context rules} (σ : Δ ⟶ Θ), (frames levels).Solves σ equation)
    {problem : EquationStore (TotalTerm Θ)} (permuted : PermutedMiller levels problem) :
    PermutedMiller levels (problem.filter keep) := by
  obtain ⟨ordered, perm, stratified⟩ := permuted
  exact ⟨ordered.filter keep, perm.filter keep, StratifiedMiller.filter_valid keep valid stratified⟩

/-- **A pattern answer on every equation keeps the permuted class.** -/
theorem PermutedMiller.applyStore (empty : rules.computation = RootComputation.empty) {Θ Δ : Context rules}
    (σ : Δ ⟶ Θ) (answer : PatternAnswer rules (bodyFlexible (o := Θ.arity) 0) (bodyFlexible (o := Δ.arity) 0)
      σ.substitution)
    {problem : EquationStore (TotalTerm Θ)} (permuted : PermutedMiller levels problem)
    (normalizes : ∀ equation ∈ problem,
      (∃ opened, Star (R := rules)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) opened ∧
          Normal rules opened) ∧
      (∃ opened, Star (R := rules)
        (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code) opened ∧
          Normal rules opened)) :
    PermutedMiller levels ((frames levels).applyStore σ problem) := by
  obtain ⟨ordered, perm, stratified⟩ := permuted
  exact ⟨(frames levels).applyStore σ ordered, perm.map _,
    stratifiedMiller_applyStore empty σ answer stratified fun equation member => normalizes equation
      (perm.subset member)⟩

end General

section Pieces

open ContextualDependentSpinesMany ContextualDependentRigidFormers

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L} [∀ head, Decidable (S.R.isUniverse head)]

/-- **Replacing the first equation, between formers under abstractions, by its pieces keeps the permuted class.** -/
theorem PermutedMiller.splice_underParts (empty : S.R.computation = RootComputation.empty)
    (facts : FormFacts S.R S.roles) (algebra : CumulativeAlgebra S.R) {Θ : Context S.R}
    {equation : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (permuted : PermutedMiller S.levels (equation :: rest)) {pieces : List (Piece Head Θ.arity)}
    (found : underParts (S := S) equation.1.1.code equation.1.2.code equation.2.2.code = some pieces)
    (normalLeft : Normal S.R equation.1.2.code) (normalRight : Normal S.R equation.2.2.code)
    (pieceEquations : EquationStore (TotalTerm Θ)) (codes : pieceEquations.map codePiece = pieces)
    (exact : ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ),
      (frames S.levels).Models σ pieceEquations ↔ (frames S.levels).Solves σ equation) :
    PermutedMiller S.levels (pieceEquations ++ rest) :=
  permuted.splice_of fun _ _ stratified =>
    StratifiedMiller.splice_underParts empty facts algebra stratified found normalLeft normalRight pieceEquations codes
      exact

end Pieces

section Twins

open ContextualDependentTwinsUnder

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- **The collapse update of the twin round keeps the permuted class.** -/
theorem permutedMiller_collapse_update (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (permuted : PermutedMiller S.levels problem) :
    PermutedMiller S.levels (collapse facts roots heads algebra reducer fuel problem).remaining := by
  obtain ⟨ordered, perm, stratified⟩ := permuted
  exact ⟨ordered.map (collapseOne facts roots heads algebra reducer fuel), perm.map _,
    stratifiedMiller_collapse facts roots heads algebra reducer fuel stratified⟩

end Twins

end ContextualDependentMillerClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
