import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPatternFiringInstance
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternDispatch

/-!
# Refutation by a rigid out-of-scope local, with flexible spines anywhere

Miller's and Abel–Pientka's failure rule: in `F x̄ ≐ t`, a local `y ∉ x̄` that occurs in `t` outside the
arguments of every flexible spine makes the equation unsolvable. The general pattern step reads this
rule only when no outer metavariable heads an application or a projection anywhere in `t`
(`ContextualDependentGeneralPattern.refuted_rigid`); so `λ x y. F x ≐ λ x y. Π y (G x)` stays pending.

Here the side condition is the Miller condition on `t` alone. Every solution is typed-equal to one with
normal components; its instance of `t` reduces to a normal term that keeps `y`
(`ContextualDependentPatternFiring.miller_instance`), while the instance of `F x̄` has a normal form whose
locals are among `x̄`. Equal normal terms have the same support, so no solution exists in any future context
(`refuted_rigidOccurrence`). The rule that reads this on codes, for any metavariable, is
`ContextualDependentPatternFiring.readingRefute`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternFiring

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentPiSpine ContextualDependentEta ContextualDependentScope
open ContextualDependentDynamicFragment
open ContextualDependentGeneralPattern

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
variable (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
  ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
    Equal S.R Θ.raw term.code code type.code)

variable {Γ : Context S.R} {type : TypeOver Γ} {spine : Spine type}
  {scopeType : TypeOver (extend Γ type)} {scope : Spine scopeType}

include facts roots heads rigid complete normalizes in
/-- **A rigid local outside the argument image refutes the flex equation** whenever the right side has
Miller occurrences: flexible spines may occur anywhere in it. -/
theorem refuted_rigidOccurrence (pattern : Pattern spine scope)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom))
    (outside : scope.Local) (notArgument : ∀ position, pattern.args position ≠ outside)
    (occurs : scope.localIndex outside ∈ rigidSupport (outerFlexible scope) right.code)
    (millerRight : miller (outerFlexible scope) right.code = true)
    (normal : ContextualDependentNormalChecking.Normal (S := S) right.code)
    {Δ : Context S.R} (solution : Δ ⟶ extend Γ type) :
    ¬ (pattern.constraint right).Holds solution := by
  intro solved
  obtain ⟨normalSolution, same, componentsNormal⟩ := exists_normal_solution normalizes solution
  have moved := (Scoped.holds_iff_of_same S.levels (pattern.constraint right) solution normalSolution
    (act_equal_of_substEq S.levels same)).mp solved
  rw [ContextualDependentGeneralPattern.Pattern.constraint, Spine.toScoped_holds_iff] at moved
  change Equal S.R (scope.reindex normalSolution).target.raw
      (subst (scope.map normalSolution).substitution pattern.application.code)
      (subst (scope.map normalSolution).substitution right.code)
      (subst (scope.map normalSolution).substitution ((lifted spine).result.reindex pattern.map.hom).code) at moved
  rw [pattern.application_code, pattern.annotation_code] at moved
  obtain ⟨normalCode, isNormal, toNormal⟩ :=
    normalizes (((lifted spine).reindex normalSolution).openFunction ((newest Γ type).reindex normalSolution))
  have renamed := toNormal.rename (pattern.reread_compatible normalSolution)
  have joined := renamed.symm.trans moved
  have formed := (scope.reindex normalSolution).target.formed
  obtain ⟨result, reduced, resultNormal, _, keeps⟩ := miller_instance rigid right.code (outerFlexible scope)
    (scope.map normalSolution).substitution normal millerRight
    (admissible_map rigid scope normalSolution componentsNormal)
  have typedRight := (Equal.typed (S := S) joined formed).2
  have toResult := (Reduces.preserve facts roots heads formed reduced typedRight).2
  have supports := ContextualDependentNormalSupport.equal_support rigid complete formed (joined.trans toResult)
    (ContextualDependentNormalObservations.normal_rename rigid _ isNormal) resultNormal
  have member := keeps (scope.localIndex outside) (localRead scope normalSolution outside (scope.localIndex outside))
    occurs (map_localRead scope normalSolution outside outside)
  rw [← supports, ContextualDependentSupport.support_rename] at member
  obtain ⟨index, _, hit⟩ := Finset.mem_image.mp member
  rw [localRead_local] at hit
  obtain ⟨position, image⟩ := (local_mem_range_iff ((lifted spine).reindex normalSolution)
    (scope.reindex normalSolution) idRen (reindexArgs (lifted spine) scope pattern.liftedArgs normalSolution) _).mp
    ⟨index, hit⟩
  exact notArgument _ ((scope.localReindexEquiv normalSolution).symm.injective image)

end ContextualDependentPatternFiring
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
