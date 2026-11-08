import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruneIntersection

/-!
# Pruning a flexible subterm under a rigid head

Under a local telescope, the equation `c (G ȳ) ≐ f x̄` has the newest metavariable `G`
applied to distinct locals as the argument of a rigid local head `c`, and the other side applies
a term `f` (for instance an older metavariable `F`) to distinct locals `x̄`. Every solution, in
every future context, gives `G` a value whose opening is a renaming of a body over the binders of
`G` whose argument occurs among `x̄`.

The rigid head is what makes this sound: `c n` is normal whenever `n` is, and its support
contains the support of `n`. The typed equality of normal forms (`equal_support`) therefore
bounds the support of `G`'s normal opening by the arguments of `f`. The forcing core of
`ContextualDependentPruneIntersection` then gives the factorization, and `pruneRigidContext`
is a pruning update that loses no solution of any store containing the equation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPrune

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentEta
open ContextualDependentUpdate ContextualDependentTypedInversion ContextualDependentScope

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (facts : FormFacts S.R S.roles) (algebra : CumulativeAlgebra S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (declared : DeclaredTypesFormed S.R)

include rigid in
/-- A variable applied to a normal argument is normal. -/
theorem normal_app_var {n : Nat} (index : Fin n) {argument : Tm Head n}
    (normal : ContextualDependentNormalChecking.Normal (S := S) argument) :
    ContextualDependentNormalChecking.Normal (S := S) (.app (.var index) argument) := by
  intro target step
  cases step with
  | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
  | congAppFun inner =>
      cases inner with
      | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
  | congAppArg inner => exact normal _ inner

variable {Γ : Context S.R} {type : TypeOver Γ} {spine : Spine type}
  {scopeType : TypeOver (extend Γ type)} {scope : Spine scopeType}

include rigid complete normalizes facts algebra headTypingUnique roots heads declared in
/-- **Forcing under a rigid head.** For `c (G ȳ) ≐ f x̄` with `c` a local of the telescope,
every solution gives `G` a value whose opening is a renaming of a body over the kept binders,
for every restriction covering the arguments of `G` that occur among `x̄`. -/
theorem forced_rigidContext (pattern : Pattern spine scope) (app : Application scope)
    (head : scope.Local) (active : Active scope.target)
    (leftCode : active.left.code = .app (.var (scope.localIndex head)) pattern.application.code)
    (rightCode : active.right.code = app.term.code)
    (rightType : (app.spine.result.reindex app.map.hom).code = active.type.code)
    (headType : Ctx.lookup scope.target.raw (scope.localIndex head) =
      .pi ((lifted spine).result.reindex pattern.map.hom).code (Presentation.rename wk active.type.code))
    {keptType : TypeOver Γ} {kept : Spine keptType} (restriction : Restriction spine kept)
    (covers : ∀ position : spine.Local, (∃ other, app.args other = pattern.args position) →
      ∃ chosen, restriction.keep chosen = position)
    {Δ : Context S.R} (solution : Δ ⟶ extend Γ type) (held : (scope.toScoped active).Holds solution) :
    ∃ inner : Term (kept.reindex (solution ≫ projectionHom Γ type)).target
        (kept.reindex (solution ≫ projectionHom Γ type)).result,
      Equal S.R (spine.reindex (solution ≫ projectionHom Γ type)).target.raw
        ((spine.reindex (solution ≫ projectionHom Γ type)).openFunction (pulledNewest solution)).code
        (Presentation.rename (restriction.ren (solution ≫ projectionHom Γ type)) inner.code)
        (spine.reindex (solution ≫ projectionHom Γ type)).result.code := by
  rw [Spine.toScoped_holds_iff] at held
  change Equal S.R (scope.reindex solution).target.raw (subst (scope.map solution).substitution active.left.code)
    (subst (scope.map solution).substitution active.right.code)
    (subst (scope.map solution).substitution active.type.code) at held
  rw [leftCode, rightCode, app.term_code] at held
  let local' := (scope.localReindexEquiv solution).symm head
  have headImage : (scope.map solution).substitution (scope.localIndex head) =
      .var ((scope.reindex solution).localIndex local') := by
    have mapped := scope.map_local solution local'
    rwa [Equiv.apply_symm_apply] at mapped
  change Equal S.R _ (.app ((scope.map solution).substitution (scope.localIndex head))
    (subst (scope.map solution).substitution pattern.application.code)) _ _ at held
  rw [headImage, pattern.application_code] at held
  -- Normal forms of both opened values.
  obtain ⟨gCode, gNormal, gSame⟩ := normalizes
    (((lifted spine).reindex solution).openFunction ((newest Γ type).reindex solution))
  obtain ⟨fCode, fNormal, fSame⟩ := normalizes
    ((app.spine.reindex solution).openFunction (app.function.reindex solution))
  have gRenamed := gSame.rename (pattern.reread_compatible solution)
  have fRenamed := fSame.rename (app.reread_compatible solution)
  have fAnnotation : Presentation.rename (app.reread solution) (app.spine.reindex solution).result.code =
      subst (scope.map solution).substitution active.type.code := by
    rw [← app.annotation_code, rightType]
  rw [fAnnotation] at fRenamed
  -- The rigid head after the solution.
  have headTyped : Typed S.R (scope.reindex solution).target.raw
      (.var ((scope.reindex solution).localIndex local'))
      (.pi (Presentation.rename (pattern.reread solution) ((lifted spine).reindex solution).result.code)
        (Presentation.rename wk (subst (scope.map solution).substitution active.type.code))) := by
    have typed := Derivable.var (R := S.R) (Γ := (scope.reindex solution).target.raw)
      ((scope.reindex solution).localIndex local')
    rw [scope.local_lookup_reindex solution, Equiv.apply_symm_apply, headType] at typed
    change Typed S.R _ _ (.pi (subst (scope.map solution).substitution
      ((lifted spine).result.reindex pattern.map.hom).code)
      (subst (liftSub (scope.map solution).substitution) (Presentation.rename wk active.type.code))) at typed
    rw [subst_liftSub_wk, pattern.annotation_code] at typed
    exact typed
  have congruent := Derivable.appCong (Derivable.refl headTyped) gRenamed
  rw [inst0_rename_wk] at congruent
  have sameNormal : Equal S.R (scope.reindex solution).target.raw
      (.app (.var ((scope.reindex solution).localIndex local')) (Presentation.rename (pattern.reread solution) gCode))
      (Presentation.rename (app.reread solution) fCode)
      (subst (scope.map solution).substitution active.type.code) :=
    congruent.symm.trans (held.trans fRenamed)
  have supports := ContextualDependentNormalSupport.equal_support rigid complete
    (scope.reindex solution).target.formed sameNormal
    (normal_app_var rigid _ (ContextualDependentNormalObservations.normal_rename rigid _ gNormal))
    (ContextualDependentNormalObservations.normal_rename rigid _ fNormal)
  refine forced_of_hits rigid complete facts algebra headTypingUnique roots heads declared pattern app
    restriction covers solution gCode gNormal gSame ?_
  intro index present
  have inLeft : pattern.reread solution index ∈
      (Tm.app (.var ((scope.reindex solution).localIndex local'))
        (Presentation.rename (pattern.reread solution) gCode)).support := by
    rw [Tm.support, ContextualDependentSupport.support_rename]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨index, present, rfl⟩)
  rw [supports, ContextualDependentSupport.support_rename] at inLeft
  obtain ⟨other, _, same⟩ := Finset.mem_image.mp inLeft
  exact ⟨other, same⟩

include rigid complete normalizes facts algebra headTypingUnique roots heads declared in
/-- **Pruning a flexible subterm loses no solution.** A store whose solutions all satisfy
`c (G ȳ) ≐ f x̄` is instantiated with `G := λ ȳ. H (ȳ restricted)`. -/
def pruneRigidContext (pattern : Pattern spine scope) (app : Application scope)
    (head : scope.Local) (active : Active scope.target)
    (leftCode : active.left.code = .app (.var (scope.localIndex head)) pattern.application.code)
    (rightCode : active.right.code = app.term.code)
    (rightType : (app.spine.result.reindex app.map.hom).code = active.type.code)
    (headType : Ctx.lookup scope.target.raw (scope.localIndex head) =
      .pi ((lifted spine).result.reindex pattern.map.hom).code (Presentation.rename wk active.type.code))
    {keptType : TypeOver Γ} {kept : Spine keptType} (restriction : Restriction spine kept)
    (covers : ∀ position : spine.Local, (∃ other, app.args other = pattern.args position) →
      ∃ chosen, restriction.keep chosen = position)
    (problem : EquationStore (TotalTerm (extend Γ type)))
    (contains : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type), (frames S.levels).Models solution problem →
      (scope.toScoped active).Holds solution) :
    Update S.levels problem :=
  prune S.levels restriction problem fun _ solution solved =>
    forced_rigidContext rigid complete normalizes facts algebra headTypingUnique roots heads declared
      pattern app head active leftCode rightCode rightType headType restriction covers solution
      (contains solution solved)

end ContextualDependentPrune
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
