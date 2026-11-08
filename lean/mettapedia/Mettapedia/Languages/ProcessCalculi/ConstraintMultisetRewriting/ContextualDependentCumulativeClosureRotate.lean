import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosurePatternNewest

/-!
# Closure of the cumulative round: R99's rotation

R99's rotation rule (`ContextualDependentPermutation.rotateRule`) moves an older declaration to the newest position along
a renaming isomorphism of the context, then runs R75's pattern rule there. The renaming is a pattern answer
(`PatternAnswer.ofRenaming`), so the moved store stays in the permuted class, and the pattern rule keeps it
(`rotateRule_keeps`).
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
open ContextualDependentMillerClosure ContextualDependentShortClosure ContextualDependentPermutation

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **A renaming isomorphism of a nonempty context keeps the permuted class.** -/
theorem renamingIso_keeps (rigid : ∀ name, S.roles name = .rigid)
    (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) {Θ Θ' : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) (π : Ren Θ.arity Θ'.arity) (π' : Ren Θ'.arity Θ.arity)
    (forth : CtxRen Θ.raw Θ'.raw π) (back : CtxRen Θ'.raw Θ.raw π') (inverse : ∀ i, π' (π i) = i)
    (nonempty : 0 < Θ.arity) (permuted : PermutedMiller S.levels problem) :
    PermutedMiller S.levels (ofRenamingIso S.levels problem π π' forth back inverse).remaining :=
  PermutedMiller.applyStore (computation_empty rigid) (renamingHom π forth)
    (PatternAnswer.ofRenaming (computation_empty rigid) π
      (fun first second same => by rw [← inverse first, ← inverse second, same]) (fun _ => rfl) ⟨0, nonempty⟩)
    permuted fun equation member =>
      ContextualDependentOpenedNormal.openedNormal_of_sn (computation_empty rigid) sn problem equation member

variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
  (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))

include rigid in
/-- **Rotation at one depth keeps the permuted class.** -/
theorem rotateAt_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel depth : Nat) :
    RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      rotateAt rigid complete facts roots heads algebra declared choices reducer root normalizes certifyNormal fuel
        depth problem := by
  intro Θ problem permuted update smaller fired
  dsimp only at fired
  unfold rotateAt at fired
  split at fired
  · cases fired
  split at fired
  · cases fired
  split at fired
  · split at fired
    · split at fired
      · rename_i raw _ checked _ forth back inverse
        dsimp only at fired
        split at fired
        · rename_i solved solvedSmaller computed
          cases fired
          exact patternRule_keeps facts roots heads algebra declared choices reducer rigid complete root normalizes
            certifyNormal sn fuel _
            (renamingIso_keeps (Θ' := ⟨Θ.arity, _, _⟩) rigid sn problem _ _ forth back inverse (by omega) permuted)
            solved solvedSmaller computed
        · cases fired
        · cases fired
      · cases fired
    · cases fired
  · cases fired

include rigid in
theorem rotateSearch_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat) :
    ∀ depths : List Nat, RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      rotateSearch rigid complete facts roots heads algebra declared choices reducer root normalizes certifyNormal fuel
        problem depths
  | [] => fun _ _ _ _ _ fired => by cases fired
  | depth :: rest => by
      intro Θ problem permuted update smaller fired
      simp only [rotateSearch] at fired
      split at fired
      · rename_i found computed
        cases fired
        exact rotateAt_keeps facts roots heads algebra declared choices reducer rigid complete root normalizes
          certifyNormal sn fuel depth problem permuted update smaller computed
      · exact rotateSearch_keeps sn fuel rest problem permuted update smaller fired

include rigid in
/-- **R99's rotation rule keeps the permuted class** on a strongly normalizing package. -/
theorem rotateRule_keeps (sn : ContextualDependentOpenedNormal.StronglyNormalizing S.R) (fuel : Nat) :
    RuleKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      rotateRule rigid complete facts roots heads algebra declared choices reducer root normalizes certifyNormal fuel
        problem :=
  fun _ problem => rotateSearch_keeps facts roots heads algebra declared choices reducer rigid complete root
    normalizes certifyNormal sn fuel _ problem

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
