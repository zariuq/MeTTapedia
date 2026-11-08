import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentMillerClosure

/-!
# The stratified Miller class under the general intersection rule

Every progress of the general intersection rule is a restriction's pruning answer applied to the store's other
equations, with the first equation dropped because the answer makes it valid (read off the rule's definition). So it
keeps the stratified Miller class, by R116's intersection closure in the general setting
(`stratifiedMiller_generalIntersect`, `stratifiedMiller_generalIntersectRule`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentMillerClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentScope
open ContextualDependentPrune ContextualDependentPatternSolver ContextualDependentDecisiveFragment
open ContextualDependentFragment ContextualDependentRank ContextualDependentConversionBudget
open ContextualDependentIntersection ContextualDependentIntersectionGeneral ContextualDependentDynamicFragment
open ContextualDependentShortClosure ExecutableReduction ContextualDependentExecutableJoin

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-- Every equation of a store has normal reducts of both its opened sides. -/
def OpenedNormal {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  ∀ equation ∈ problem,
    (∃ opened, Star (R := S.R)
      (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.1.2.code) opened ∧
        Normal S.R opened) ∧
    (∃ opened, Star (R := S.R)
      (openCode (ContextualDependentPatternSolver.lamDepth equation.1.2.code) equation.2.2.code) opened ∧
        Normal S.R opened)

/-- **A general intersection progress on one recognized pattern keeps the class.** -/
theorem stratifiedMiller_generalIntersect (fuel : Nat) {Γ₀ : Context S.R} (newer : TypeOver Γ₀)
    {scopeType : TypeOver (extend Γ₀ newer)} (scope : Spine scopeType) (active : Active scope.target)
    (equation : Equation (TotalTerm (extend Γ₀ newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ₀ newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ₀ newer))) (spine : Spine newer)
    (recognized : Recognized spine scope active)
    (stratified : StratifiedMiller S.levels (equation :: rest)) (opened : OpenedNormal (equation :: rest))
    {found : Progress facts roots heads algebra rigid complete (equation :: rest)}
    (fired : generalIntersect facts roots heads algebra rigid complete declared choices reducer normalizes
      headTypingUnique fuel newer scope active equation view rest spine recognized = some found) :
    StratifiedMiller S.levels found.val.remaining := by
  unfold generalIntersect at fired
  dsimp only at fired
  repeat' (first | (split at fired) | (cases fired))
  rename_i certificate _
  exact stratifiedMiller_intersect_rigid rigid _ stratified opened certificate.down

/-- **A general intersection progress on one store equation keeps the class.** -/
theorem stratifiedMiller_generalIntersectEquation (fuel : Nat) {Γ₀ : Context S.R} (newer : TypeOver Γ₀)
    (equation : Equation (TotalTerm (extend Γ₀ newer))) (rest : EquationStore (TotalTerm (extend Γ₀ newer)))
    (stratified : StratifiedMiller S.levels (equation :: rest)) (opened : OpenedNormal (equation :: rest))
    {found : Progress facts roots heads algebra rigid complete (equation :: rest)}
    (fired : generalIntersectEquation facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel newer equation rest = some found) :
    StratifiedMiller S.levels found.val.remaining := by
  unfold generalIntersectEquation at fired
  split at fired
  · cases fired
  split at fired
  · cases fired
  split at fired
  · cases fired
  split at fired
  · cases fired
  exact stratifiedMiller_generalIntersect facts roots heads algebra rigid complete declared choices reducer normalizes
    headTypingUnique fuel newer _ _ equation _ rest _ _ stratified opened fired

/-- **Every progress of the general intersection rule keeps the stratified Miller class.** -/
theorem stratifiedMiller_generalIntersectRule (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    (stratified : StratifiedMiller S.levels problem) (opened : OpenedNormal problem)
    {found : Progress facts roots heads algebra rigid complete problem}
    (fired : generalIntersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem = some found) :
    StratifiedMiller S.levels found.val.remaining := by
  unfold generalIntersectRule at fired
  split at fired
  · cases fired
  rename_i view _
  rcases view with ⟨base, type, same⟩
  subst same
  cases problem with
  | nil => cases fired
  | cons equation rest =>
      exact stratifiedMiller_generalIntersectEquation facts roots heads algebra rigid complete declared choices reducer
        root normalizes headTypingUnique fuel type equation rest stratified opened fired

end ContextualDependentMillerClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
