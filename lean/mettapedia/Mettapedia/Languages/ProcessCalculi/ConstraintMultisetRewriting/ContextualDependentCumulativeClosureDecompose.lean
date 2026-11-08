import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureFirst

/-!
# Closure of the cumulative round: R99's decomposition round, reduced to two rules

R99's decomposition round (`ContextualDependentRigidDecomposition.decomposeRound`) is the decomposition of local
applications, then the rigid round: the local clash refutation, then R75's full round, which is R76's first rule and
then R75's worklist round (`ContextualDependentDecisiveFragment.fullRound_eq`). R76's first rule keeps the class
(`firstRule_stable`), and refutations offer no update, so the round keeps the class wherever the decomposition of
local applications and the worklist round do (`decomposeRound_keeps`).
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
open ContextualDependentMillerClosure

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
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

include rigid in
/-- **R75's full round keeps the class** wherever its worklist round does. -/
theorem fullRound_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    (worklist : LayerKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      ContextualDependentWorklist.round rigid facts complete roots heads algebra declared choices reducer fuel problem) :
    LayerKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      fullRound rigid facts complete roots heads algebra declared choices reducer root normalizes certifyNormal
        headTypingUnique fuel problem := by
  intro Θ problem permuted update offered
  dsimp only at offered
  rw [ContextualDependentDecisiveFragment.fullRound_eq] at offered
  split at offered
  · rename_i moved smaller computed
    cases offered
    exact (firstRule_stable facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique sn fuel problem _ smaller computed).keeps permuted
  · cases offered
  · exact worklist problem permuted update offered

include rigid in
/-- **R99's decomposition round keeps the class** wherever the decomposition of local applications and R75's worklist
round do. -/
theorem decomposeRound_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat)
    (search : RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      ContextualDependentRigidDecomposition.decomposeSearch rigid facts complete roots heads algebra declared choices
        reducer root normalizes certifyNormal fuel problem)
    (worklist : LayerKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      ContextualDependentWorklist.round rigid facts complete roots heads algebra declared choices reducer fuel problem) :
    LayerKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      ContextualDependentRigidDecomposition.decomposeRound rigid facts complete roots heads algebra declared choices
        reducer root normalizes certifyNormal headTypingUnique fuel problem := by
  intro Θ problem permuted update offered
  dsimp only at offered
  unfold ContextualDependentRigidDecomposition.decomposeRound at offered
  split at offered
  · rename_i moved smaller computed
    cases offered
    exact search problem permuted _ smaller computed
  · cases offered
  · unfold ContextualDependentRigidDecomposition.rigidRound at offered
    split at offered
    · cases offered
    · exact fullRound_keeps facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique sn fuel worklist problem permuted update offered

/-- **The dispatcher keeps the class** at the newest declaration, at a budget. -/
def DispatchKeeps (fuel : Nat) : Prop :=
  ∀ {Γ : Context S.R} (type : TypeOver Γ) (problem : EquationStore (TotalTerm (extend Γ type))),
    PermutedMiller S.levels problem → ∀ updated,
      ContextualDependentDispatch.search facts roots heads algebra declared choices reducer fuel type problem =
        some updated → PermutedMiller S.levels updated.remaining

/-- **R75's worklist round keeps the class** wherever its dispatcher does: a clash refutes, the conversion scan keeps
the class (`conversion_keeps`), and the dispatcher's answer is followed by the conversion scan again. -/
theorem worklistRound_keeps (fuel : Nat)
    (dispatch : DispatchKeeps facts roots heads algebra declared choices reducer fuel) :
    LayerKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      ContextualDependentWorklist.round rigid facts complete roots heads algebra declared choices reducer fuel
        problem := by
  intro Θ problem permuted update offered
  dsimp only at offered
  unfold ContextualDependentWorklist.round at offered
  split at offered
  · cases offered
  split at offered
  · cases offered
    exact conversion_keeps facts roots heads algebra reducer fuel problem permuted
  split at offered
  · cases offered
  rename_i view _
  rcases view with ⟨base, newer, same⟩
  subst same
  split at offered
  · cases offered
  · rename_i moved smaller computed
    cases offered
    change ContextualDependentWorklist.dispatchNewest facts roots heads algebra declared choices reducer fuel newer
      problem = some ⟨update, smaller⟩ at computed
    unfold ContextualDependentWorklist.dispatchNewest at computed
    split at computed
    · cases computed
    · rename_i updated found
      cases computed
      exact conversion_keeps facts roots heads algebra reducer fuel updated.remaining
        (dispatch newer problem permuted updated found)

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
