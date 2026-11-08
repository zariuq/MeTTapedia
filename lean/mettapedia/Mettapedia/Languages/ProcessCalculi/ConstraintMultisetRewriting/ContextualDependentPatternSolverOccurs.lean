import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruneSubterm
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternRecognition

/-!
# The occurs check at a rigid base type

A normal term `a` of a variable type `T` is never typed-equal to `c a`, where `c : T → T` is a
variable. The algorithmic equality of normal terms at a variable type compares spines: the
comparison of `a` with `c a` forces `a = c a₁` with `a₁` compared to `c a₁` at the same type,
and `a₁` is a proper subterm. Hence no derivation exists, by descent on the size of `a`.

Consequently the pattern equation `F x̄ ≐ c (F x̄)`, at a type that is a local of the telescope
and with `c : T → T` a local, has no solution in any future context: every outer solution would
make the normal form of `F`'s opening such a fixed point. This is a certified refutation, not a
failed inversion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPatternSolver

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentEta ContextualDependentScope
open ContextualDependentNormalChecking

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (rigid : ∀ name, S.roles name = .rigid)

include rigid in
theorem normal_pi_vars {n : Nat} (domain : Fin n) (codomain : Fin (n + 1)) :
    Normal (S := S) (.pi (.var domain) (.var codomain)) := by
  intro target step
  cases step with
  | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
  | congPiDom inner => exact ContextualDependentNormalObservations.normal_var rigid domain _ inner
  | congPiCod inner => exact ContextualDependentNormalObservations.normal_var rigid codomain _ inner

theorem normal_app_argument {n : Nat} {function argument : Tm Head n}
    (normal : Normal (S := S) (.app function argument)) : Normal (S := S) argument :=
  fun _ step => normal _ (.congAppArg step)

include rigid in
/-- **No rigid fixed point.** At a variable type `T`, with `c : T → T` a variable, no normal `a`
is algorithmically equal to `c a`. -/
theorem no_rigid_fixed_point {n : Nat} {Γ : Ctx Head n} (head type : Fin n)
    (headType : Ctx.lookup Γ head = .pi (.var type) (.var type.succ)) :
    ∀ (size : Nat) (value : Tm Head n), sizeOf value = size → Normal (S := S) value →
      ¬ Algorithmic S.R S.roles (.terms Γ value (.app (.var head) value) (.var type)) := by
  intro size
  induction size using Nat.strong_induction_on with
  | _ size ih =>
  intro value sized normal derivation
  cases derivation with
  | terms typeRed _ leftRed rightRed inner =>
    have typeSame := WhRed.eq_of_whnf (S := S)
      (ContextualDependentNormalObservations.normal_whnf (ContextualDependentNormalObservations.normal_var rigid type))
      typeRed.red
    have leftSame := WhRed.eq_of_whnf (S := S) (ContextualDependentNormalObservations.normal_whnf normal) leftRed.red
    have rightSame := WhRed.eq_of_whnf (S := S)
      (ContextualDependentNormalObservations.normal_whnf (ContextualDependentPrune.normal_app_var rigid head normal))
      rightRed.red
    subst typeSame
    subst leftSame
    subst rightSame
    cases inner with
    | spine _ _ _ _ _ spines =>
      cases spines with
      | spinesW spinesInner _ _ =>
        cases spinesInner with
        | app headSpines argument =>
          cases headSpines with
          | spinesW headInner headRed _ =>
            cases headInner with
            | var index =>
              rw [headType] at headRed
              have domainSame := WhRed.eq_of_whnf (S := S)
                (ContextualDependentNormalObservations.normal_whnf (normal_pi_vars rigid type type.succ)) headRed.red
              obtain ⟨rfl, rfl⟩ := Tm.pi.inj domainSame
              exact ih (sizeOf _) (by subst sized; simp) _ rfl (normal_app_argument normal) argument

include rigid in
/-- **Spine injectivity.** At a variable type, `c m` and `c m'` with the same variable head `c : D → T`
are algorithmically equal only if their arguments are, at `D`. -/
theorem spine_injective {n : Nat} {Γ : Ctx Head n} (head domain type : Fin n)
    (headType : Ctx.lookup Γ head = .pi (.var domain) (.var type.succ)) {first second : Tm Head n}
    (firstNormal : Normal (S := S) first) (secondNormal : Normal (S := S) second)
    (derivation : Algorithmic S.R S.roles (.terms Γ (.app (.var head) first) (.app (.var head) second) (.var type))) :
    Algorithmic S.R S.roles (.terms Γ first second (.var domain)) := by
  cases derivation with
  | terms typeRed _ leftRed rightRed inner =>
    have typeSame := WhRed.eq_of_whnf (S := S)
      (ContextualDependentNormalObservations.normal_whnf (ContextualDependentNormalObservations.normal_var rigid type))
      typeRed.red
    have leftSame := WhRed.eq_of_whnf (S := S)
      (ContextualDependentNormalObservations.normal_whnf (ContextualDependentPrune.normal_app_var rigid head firstNormal))
      leftRed.red
    have rightSame := WhRed.eq_of_whnf (S := S)
      (ContextualDependentNormalObservations.normal_whnf (ContextualDependentPrune.normal_app_var rigid head secondNormal))
      rightRed.red
    subst typeSame
    subst leftSame
    subst rightSame
    cases inner with
    | spine _ _ _ _ _ spines =>
      cases spines with
      | spinesW spinesInner _ _ =>
        cases spinesInner with
        | app headSpines argument =>
          cases headSpines with
          | spinesW headInner headRed _ =>
            cases headInner with
            | var index =>
              rw [headType] at headRed
              have domainSame := WhRed.eq_of_whnf (S := S)
                (ContextualDependentNormalObservations.normal_whnf (normal_pi_vars rigid domain type.succ)) headRed.red
              obtain ⟨rfl, rfl⟩ := Tm.pi.inj domainSame
              exact argument

include rigid in
/-- **Spine injectivity**, typed. -/
theorem equal_arguments (complete : AlgorithmicComplete S.R S.roles) (facts : FormFacts S.R S.roles)
    (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
    {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (head domain type : Fin n)
    (headType : Ctx.lookup Γ head = .pi (.var domain) (.var type.succ)) {first second : Tm Head n}
    (firstNormal : Normal (S := S) first) (secondNormal : Normal (S := S) second)
    (same : Equal S.R Γ (.app (.var head) first) (.app (.var head) second) (.var type)) :
    Equal S.R Γ first second (.var domain) :=
  Algorithmic.sound_terms facts roots heads algebra formed
    (spine_injective rigid head domain type headType firstNormal secondNormal (complete formed same))

include rigid in
/-- **No rigid fixed point**, typed: `a ≐ c a` has no derivation at a variable type. -/
theorem not_equal_rigid_fixed_point (complete : AlgorithmicComplete S.R S.roles) {n : Nat} {Γ : Ctx Head n}
    (formed : CtxFormed S.R Γ) (head type : Fin n)
    (headType : Ctx.lookup Γ head = .pi (.var type) (.var type.succ)) {value : Tm Head n}
    (normal : Normal (S := S) value) : ¬ Equal S.R Γ value (.app (.var head) value) (.var type) :=
  fun same => no_rigid_fixed_point rigid head type headType _ value rfl normal (complete formed same)

variable (complete : AlgorithmicComplete S.R S.roles)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, Normal (S := S) code ∧ Equal S.R Θ.raw term.code code type.code)

variable {Γ : Context S.R} {type : TypeOver Γ} {spine : Spine type}
  {scopeType : TypeOver (extend Γ type)} {scope : Spine scopeType}

include rigid complete normalizes in
/-- **The occurs check.** The pattern equation `F x̄ ≐ c (F x̄)`, at a local type `T` of the telescope
and with a local `c : T → T`, has no solution in any future context. -/
theorem occurs_refuted (pattern : Pattern spine scope) (head typeLocal : scope.Local) (active : Active scope.target)
    (leftCode : active.left.code = pattern.application.code)
    (rightCode : active.right.code = .app (.var (scope.localIndex head)) pattern.application.code)
    (typeCode : active.type.code = .var (scope.localIndex typeLocal))
    (resultCode : ((lifted spine).result.reindex pattern.map.hom).code = .var (scope.localIndex typeLocal))
    (headType : Ctx.lookup scope.target.raw (scope.localIndex head) =
      .pi (.var (scope.localIndex typeLocal)) (.var (scope.localIndex typeLocal).succ))
    {Δ : Context S.R} (solution : Δ ⟶ extend Γ type) : ¬ (scope.toScoped active).Holds solution := by
  intro held
  rw [Spine.toScoped_holds_iff] at held
  change Equal S.R (scope.reindex solution).target.raw (subst (scope.map solution).substitution active.left.code)
    (subst (scope.map solution).substitution active.right.code)
    (subst (scope.map solution).substitution active.type.code) at held
  rw [leftCode, rightCode, typeCode] at held
  let headLocal := (scope.localReindexEquiv solution).symm head
  let typeLocal' := (scope.localReindexEquiv solution).symm typeLocal
  have headImage : (scope.map solution).substitution (scope.localIndex head) =
      .var ((scope.reindex solution).localIndex headLocal) := by
    have mapped := scope.map_local solution headLocal
    rwa [Equiv.apply_symm_apply] at mapped
  have typeImage : (scope.map solution).substitution (scope.localIndex typeLocal) =
      .var ((scope.reindex solution).localIndex typeLocal') := by
    have mapped := scope.map_local solution typeLocal'
    rwa [Equiv.apply_symm_apply] at mapped
  change Equal S.R _ (subst (scope.map solution).substitution pattern.application.code)
    (.app ((scope.map solution).substitution (scope.localIndex head))
      (subst (scope.map solution).substitution pattern.application.code))
    ((scope.map solution).substitution (scope.localIndex typeLocal)) at held
  rw [headImage, typeImage, pattern.application_code] at held
  obtain ⟨gCode, gNormal, gSame⟩ := normalizes
    (((lifted spine).reindex solution).openFunction ((newest Γ type).reindex solution))
  have gRenamed := gSame.rename (pattern.reread_compatible solution)
  have annotation : Presentation.rename (pattern.reread solution) ((lifted spine).reindex solution).result.code =
      .var ((scope.reindex solution).localIndex typeLocal') := by
    rw [← pattern.annotation_code, resultCode]
    exact typeImage
  rw [annotation] at gRenamed
  have headLookup : Ctx.lookup (scope.reindex solution).target.raw ((scope.reindex solution).localIndex headLocal) =
      .pi (.var ((scope.reindex solution).localIndex typeLocal'))
        (.var ((scope.reindex solution).localIndex typeLocal').succ) := by
    rw [scope.local_lookup_reindex solution, Equiv.apply_symm_apply, headType]
    change Tm.pi ((scope.map solution).substitution (scope.localIndex typeLocal))
      (Presentation.rename wk ((scope.map solution).substitution (scope.localIndex typeLocal))) = _
    rw [typeImage]
    rfl
  have headTyped := Derivable.var (R := S.R) (Γ := (scope.reindex solution).target.raw)
    ((scope.reindex solution).localIndex headLocal)
  rw [headLookup] at headTyped
  have congruent := Derivable.appCong (Derivable.refl headTyped) gRenamed
  have sameNormal : Equal S.R (scope.reindex solution).target.raw
      (Presentation.rename (pattern.reread solution) gCode)
      (.app (.var ((scope.reindex solution).localIndex headLocal)) (Presentation.rename (pattern.reread solution) gCode))
      (.var ((scope.reindex solution).localIndex typeLocal')) :=
    gRenamed.symm.trans (held.trans congruent)
  exact not_equal_rigid_fixed_point rigid complete (scope.reindex solution).target.formed _ _ headLookup
    (ContextualDependentNormalObservations.normal_rename rigid _ gNormal) sameNormal

variable [DecidableEq Head]

include rigid complete normalizes in
/-- **The executable occurs check** on a recognized pattern `F x̄ ≐ r`: it succeeds exactly when `r` is
`c (F x̄)` with `c : T → T` a local and `T` a local type; success is a certified refutation. -/
def occursCheck (pattern : Pattern spine scope)
    (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom)) :
    Option (PLift (∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type), ¬ (pattern.constraint right).Holds solution)) :=
  match right.code, ((lifted spine).result.reindex pattern.map.hom).code with
  | .app (.var headIndex) _, .var typeIndex =>
      match localOf scope headIndex, localOf scope typeIndex with
      | some head, some typeLocal =>
          if rightCode : right.code = .app (.var (scope.localIndex head)) pattern.application.code then
            if resultCode : ((lifted spine).result.reindex pattern.map.hom).code =
                .var (scope.localIndex typeLocal) then
              if headType : Ctx.lookup scope.target.raw (scope.localIndex head) =
                  .pi (.var (scope.localIndex typeLocal)) (.var (scope.localIndex typeLocal).succ) then
                some ⟨fun solution => occurs_refuted rigid complete normalizes pattern head typeLocal
                  ⟨_, pattern.application, right⟩ rfl rightCode resultCode resultCode headType solution⟩
              else none
            else none
          else none
      | _, _ => none
  | _, _ => none

end ContextualDependentPatternSolver
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
