import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternReplacement
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalSupport

/-!
# Certified refutation of a pattern equation by an out-of-image local

Every solution of a flex equation `F x̄ ≐ t` makes `t` typed-equal to a
renaming, through the reindexed argument map, of `F`'s opened instance.
When `t` is normal, mentions only local rigid variables, and uses a local
that is not one of the pattern arguments, the two sides have different
normal supports at every outer substitution. This contradicts the support
theorem for equal normal terms in the rigid-constant profile. Hence the
equation has no solution in any future context.

The refutation is stated relative to a supplied normal-form theorem for
typed terms; the cumulative tower discharges it. A failed raw inversion
alone is never used as a refutation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentGeneralPattern

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentPiSpine ContextualDependentTypedInversion
open ContextualDependentEta ContextualDependentScope

section Support

variable {Head : Type}

theorem liftSub_agree {n m : Nat} {first second : Sub Head n m} {slots : Finset (Fin (n + 1))}
    (agree : ∀ index ∈ outerSupport slots, first index = second index) :
    ∀ index ∈ slots, liftSub first index = liftSub second index := by
  intro index
  refine Fin.cases (motive := fun index => index ∈ slots → liftSub first index = liftSub second index)
    (fun _ => rfl) (fun prior member => ?_) index
  simp only [liftSub_succ]
  rw [agree prior (mem_outerSupport.mpr member)]

/-- Substitution only reads the support of a term. -/
theorem subst_eq_of_support {n : Nat} (term : Tm Head n) :
    ∀ {m : Nat} (first second : Sub Head n m),
      (∀ index ∈ term.support, first index = second index) → subst first term = subst second term := by
  induction term with
  | var index =>
      intro m first second agree
      exact agree index (by simp [Tm.support])
  | const name => intro m first second _; rfl
  | head value => intro m first second _; rfl
  | pi domain body ihDomain ihBody =>
      intro m first second agree
      simp only [subst]
      rw [ihDomain first second (fun index member => agree index (by simp [Tm.support, member])),
        ihBody (liftSub first) (liftSub second)
          (liftSub_agree (fun index member => agree index (by simp [Tm.support, member])))]
  | sigma domain body ihDomain ihBody =>
      intro m first second agree
      simp only [subst]
      rw [ihDomain first second (fun index member => agree index (by simp [Tm.support, member])),
        ihBody (liftSub first) (liftSub second)
          (liftSub_agree (fun index member => agree index (by simp [Tm.support, member])))]
  | id carrier left right ihCarrier ihLeft ihRight =>
      intro m first second agree
      simp only [subst]
      rw [ihCarrier first second (fun index member => agree index (by simp [Tm.support, member])),
        ihLeft first second (fun index member => agree index (by simp [Tm.support, member])),
        ihRight first second (fun index member => agree index (by simp [Tm.support, member]))]
  | lam body ih =>
      intro m first second agree
      simp only [subst]
      rw [ih (liftSub first) (liftSub second)
        (liftSub_agree (fun index member => agree index (by simp [Tm.support, member])))]
  | app function argument ihFunction ihArgument =>
      intro m first second agree
      simp only [subst]
      rw [ihFunction first second (fun index member => agree index (by simp [Tm.support, member])),
        ihArgument first second (fun index member => agree index (by simp [Tm.support, member]))]
  | pair left right ihLeft ihRight =>
      intro m first second agree
      simp only [subst]
      rw [ihLeft first second (fun index member => agree index (by simp [Tm.support, member])),
        ihRight first second (fun index member => agree index (by simp [Tm.support, member]))]
  | fst value ih =>
      intro m first second agree
      simp only [subst]
      rw [ih first second (fun index member => agree index (by simp [Tm.support, member]))]
  | snd value ih =>
      intro m first second agree
      simp only [subst]
      rw [ih first second (fun index member => agree index (by simp [Tm.support, member]))]
  | refl value ih =>
      intro m first second agree
      simp only [subst]
      rw [ih first second (fun index member => agree index (by simp [Tm.support, member]))]

end Support

section Locals

variable {Head : Type} {rules : Rules Head}
variable {Γ : Context rules} {scopeType : TypeOver Γ} (scope : Spine scopeType)

/-- How an outer solution reads local rigid variables. Outer variables are
sent to the supplied fallback local; this branch is used only off support. -/
def localRead {Δ : Context rules} (solution : Δ ⟶ Γ) (fallback : scope.Local) :
    Ren scope.target.arity (scope.reindex solution).target.arity :=
  fun index => Sum.elim (fun _ => (scope.reindex solution).localIndex ((scope.localReindexEquiv solution).symm fallback))
    (fun position => (scope.reindex solution).localIndex ((scope.localReindexEquiv solution).symm position))
    (scope.originEquiv.symm index)

theorem localRead_local {Δ : Context rules} (solution : Δ ⟶ Γ) (fallback position : scope.Local) :
    localRead scope solution fallback (scope.localIndex position) =
      (scope.reindex solution).localIndex ((scope.localReindexEquiv solution).symm position) := by
  unfold localRead Spine.localIndex
  rw [Equiv.symm_apply_apply]
  rfl

theorem map_localRead {Δ : Context rules} (solution : Δ ⟶ Γ) (fallback position : scope.Local) :
    (scope.map solution).substitution (scope.localIndex position) =
      .var (localRead scope solution fallback (scope.localIndex position)) := by
  have lifted := scope.map_local solution ((scope.localReindexEquiv solution).symm position)
  rw [Equiv.apply_symm_apply] at lifted
  rw [lifted, localRead_local]

/-- A term using only local rigid variables is renamed, not instantiated,
by every outer solution. -/
theorem subst_local_only {Δ : Context rules} (solution : Δ ⟶ Γ) (fallback : scope.Local)
    (term : Tm Head scope.target.arity)
    (localOnly : ∀ index ∈ term.support, ∃ position, scope.localIndex position = index) :
    subst (scope.map solution).substitution term =
      Presentation.rename (localRead scope solution fallback) term := by
  rw [← subst_renSub]
  apply subst_eq_of_support
  intro index member
  obtain ⟨position, rfl⟩ := localOnly index member
  exact map_localRead scope solution fallback position

end Locals

section Refutation

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
variable (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
  ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
    Equal S.R Θ.raw term.code code type.code)

namespace Pattern

variable {Γ : Context S.R} {type : TypeOver Γ} {spine : Spine type}
  {scopeType : TypeOver (extend Γ type)} {scope : Spine scopeType} (pattern : Pattern spine scope)

include rigid complete normalizes in
/-- No solution exists in any future context. -/
theorem refuted (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom))
    (outside : scope.Local) (notArgument : ∀ position, pattern.args position ≠ outside)
    (occurs : scope.localIndex outside ∈ right.code.support)
    (localOnly : ∀ index ∈ right.code.support, ∃ position, scope.localIndex position = index)
    (normal : ContextualDependentNormalChecking.Normal (S := S) right.code)
    {Δ : Context S.R} (solution : Δ ⟶ extend Γ type) :
    ¬ (pattern.constraint right).Holds solution := by
  intro solved
  rw [constraint, Spine.toScoped_holds_iff] at solved
  change Equal S.R (scope.reindex solution).target.raw
      (subst (scope.map solution).substitution pattern.application.code)
      (subst (scope.map solution).substitution right.code)
      (subst (scope.map solution).substitution ((lifted spine).result.reindex pattern.map.hom).code) at solved
  rw [pattern.application_code, pattern.annotation_code,
    subst_local_only scope solution outside right.code localOnly] at solved
  obtain ⟨normalCode, isNormal, toNormal⟩ :=
    normalizes (((lifted spine).reindex solution).openFunction ((newest Γ type).reindex solution))
  have renamed := toNormal.rename (pattern.reread_compatible solution)
  have joined := renamed.symm.trans solved
  have supports := ContextualDependentNormalSupport.equal_support rigid complete
    (scope.reindex solution).target.formed joined
    (ContextualDependentNormalObservations.normal_rename rigid _ isNormal)
    (ContextualDependentNormalObservations.normal_rename rigid _ normal)
  have member : localRead scope solution outside (scope.localIndex outside) ∈
      (Presentation.rename (localRead scope solution outside) right.code).support := by
    rw [ContextualDependentSupport.support_rename]
    exact Finset.mem_image_of_mem _ occurs
  rw [← supports, ContextualDependentSupport.support_rename] at member
  obtain ⟨index, _, hit⟩ := Finset.mem_image.mp member
  rw [localRead_local] at hit
  obtain ⟨position, image⟩ := (local_mem_range_iff ((lifted spine).reindex solution) (scope.reindex solution) idRen
    (reindexArgs (lifted spine) scope pattern.liftedArgs solution) _).mp ⟨index, hit⟩
  exact notArgument _ ((scope.localReindexEquiv solution).symm.injective image)

include rigid complete normalizes in
/-- The refutation preserves closed and symbolic solvability separately:
there is no solution at any fixed target, including the empty context. -/
theorem refuted_at (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom))
    (outside : scope.Local) (notArgument : ∀ position, pattern.args position ≠ outside)
    (occurs : scope.localIndex outside ∈ right.code.support)
    (localOnly : ∀ index ∈ right.code.support, ∃ position, scope.localIndex position = index)
    (normal : ContextualDependentNormalChecking.Normal (S := S) right.code) (point : Context S.R) :
    ¬ ∃ solution : point ⟶ extend Γ type, (pattern.constraint right).Holds solution := by
  rintro ⟨solution, solved⟩
  exact pattern.refuted rigid complete normalizes right outside notArgument occurs localOnly normal solution solved

end Pattern
end Refutation

end ContextualDependentGeneralPattern
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
