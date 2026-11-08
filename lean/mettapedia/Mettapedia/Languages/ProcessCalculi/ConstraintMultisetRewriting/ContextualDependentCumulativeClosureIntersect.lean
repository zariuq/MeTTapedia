import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosurePrepare

/-!
# Closure of the cumulative round: R110's isolated intersection

R110's intersection rule (`ContextualDependentIntersection.intersectRule`) prunes the newest metavariable to the
positions where the two spines agree, then drops the first equation by a certified conversion. That is a drop of the
first equation under a pattern answer (`tryIntersect_headDrop`, `intersectRule_headDrop`), so it keeps the permuted
class (`intersect_keeps`), as R119's general intersection does.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCumulativeClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentRank
open ContextualDependentMillerClosure ContextualDependentShortClosure ContextualDependentIntersection
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentScope

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

include rigid in
/-- **R110's intersection on one recognized pattern drops the first equation under a pattern answer.** -/
theorem tryIntersect_headDrop (fuel : Nat) {Γ₀ : Context S.R} (newer : TypeOver Γ₀)
    {scopeType : TypeOver (extend Γ₀ newer)} (scope : Spine scopeType) (active : Active scope.target)
    (equation : Equation (TotalTerm (extend Γ₀ newer)))
    (view : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ₀ newer),
      (frames S.levels).Models solution [equation] ↔ (scope.toScoped active).Holds solution)
    (rest : EquationStore (TotalTerm (extend Γ₀ newer))) (isolated : ∀ other ∈ rest, Weakened other)
    (spine : Spine newer) (recognized : Recognized spine scope active)
    {found : Progress facts roots heads algebra rigid complete (equation :: rest)}
    (fired : tryIntersect facts roots heads algebra rigid complete declared choices reducer normalizes
      headTypingUnique fuel newer scope active equation view rest isolated spine recognized = some found) :
    HeadDrop (equation :: rest) found.val := by
  unfold tryIntersect at fired
  dsimp only at fired
  repeat' (first | (split at fired) | (cases fired))
  rename_i certificate _
  exact ⟨equation, rest, _, rfl, (Category.id_comp _).symm, rfl,
    fun τ => (frames S.levels).preserves τ certificate.down, ⟨pruneAnswer (computation_empty rigid) _⟩⟩

include rigid in
theorem intersectEquation_headDrop (fuel : Nat) {Γ₀ : Context S.R} (newer : TypeOver Γ₀)
    (equation : Equation (TotalTerm (extend Γ₀ newer))) (rest : EquationStore (TotalTerm (extend Γ₀ newer)))
    {found : Progress facts roots heads algebra rigid complete (equation :: rest)}
    (fired : intersectEquation facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel newer equation rest = some found) :
    HeadDrop (equation :: rest) found.val := by
  unfold intersectEquation at fired
  split at fired
  · cases fired
  split at fired
  · cases fired
  split at fired
  · cases fired
  split at fired
  · cases fired
  split at fired
  · cases fired
  exact tryIntersect_headDrop facts roots heads algebra rigid complete declared choices reducer normalizes
    headTypingUnique fuel newer _ _ equation _ rest _ _ _ fired

include rigid in
/-- **Every progress of R110's intersection rule drops the first equation under a pattern answer.** -/
theorem intersectRule_headDrop (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ))
    {found : Progress facts roots heads algebra rigid complete problem}
    (fired : intersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem = some found) :
    HeadDrop problem found.val := by
  unfold intersectRule at fired
  split at fired
  · cases fired
  rename_i view _
  rcases view with ⟨base, type, same⟩
  subst same
  cases problem with
  | nil => cases fired
  | cons equation rest =>
      exact intersectEquation_headDrop facts roots heads algebra rigid complete declared choices reducer root
        normalizes headTypingUnique fuel type equation rest fired

include rigid in
/-- **R110's intersection keeps the permuted class** on a strongly normalizing package. -/
theorem intersect_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) (permuted : PermutedMiller S.levels problem)
    (moved : Progress facts roots heads algebra rigid complete problem)
    (fired : intersectRule facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem = some moved) :
    PermutedMiller S.levels moved.val.remaining :=
  permutedMiller_of_headDrop rigid permuted
    (ContextualDependentOpenedNormal.openedNormal_of_sn (computation_empty rigid) sn problem)
    (intersectRule_headDrop facts roots heads algebra rigid complete declared choices reducer root normalizes
      headTypingUnique fuel problem fired)

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
