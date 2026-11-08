import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentGeneralPatternRefutation

/-!
# Refutation by a rigid out-of-image local in the presence of metavariables

The right side of a flex equation may mention outer metavariables, provided
none of them is the function of an application or the argument of a
projection. Every solution is typed-equal to one with normal components;
substituting normal terms for such metavariables into a normal right side
creates no redex in the rigid-constant profile, and keeps every local
variable. Hence a local that is not a pattern argument stays in the normal
support of the instantiated right side, while the instantiated pattern
application has a normal form supported by the argument image. The
equation therefore has no solution in any future context.

Metavariables applied to arguments (flexible subterms) are outside this
fragment; their occurrences may be erased by instantiation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentGeneralPattern

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentPiSpine ContextualDependentEta ContextualDependentScope

section Shapes

variable {Head : Type}

/-- A flexible variable is not allowed as an elimination head. -/
def notFlexibleHead {n : Nat} (flexible : Fin n → Bool) : Tm Head n → Bool
  | .var index => !flexible index
  | _ => true

def liftFlexible {n : Nat} (flexible : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.cases false flexible

/-- No flexible variable occurs as the function of an application or the
argument of a projection. -/
def HeadFree : {n : Nat} → (Fin n → Bool) → Tm Head n → Bool
  | _, _, .var _ => true
  | _, _, .const _ => true
  | _, _, .head _ => true
  | _, flexible, .pi domain body => HeadFree flexible domain && HeadFree (liftFlexible flexible) body
  | _, flexible, .sigma domain body => HeadFree flexible domain && HeadFree (liftFlexible flexible) body
  | _, flexible, .id carrier left right =>
      HeadFree flexible carrier && HeadFree flexible left && HeadFree flexible right
  | _, flexible, .lam body => HeadFree (liftFlexible flexible) body
  | _, flexible, .app function argument =>
      notFlexibleHead flexible function && HeadFree flexible function && HeadFree flexible argument
  | _, flexible, .pair left right => HeadFree flexible left && HeadFree flexible right
  | _, flexible, .fst value => notFlexibleHead flexible value && HeadFree flexible value
  | _, flexible, .snd value => notFlexibleHead flexible value && HeadFree flexible value
  | _, flexible, .refl value => HeadFree flexible value

theorem subst_eq_lam {n m : Nat} {σ : Sub Head n m} {term : Tm Head n} {body : Tm Head (m + 1)}
    (same : subst σ term = .lam body) : (∃ index, term = .var index) ∨ ∃ inner, term = .lam inner := by
  cases term with
  | var index => exact .inl ⟨index, rfl⟩
  | lam inner => exact .inr ⟨inner, rfl⟩
  | _ => cases same

theorem subst_eq_pair {n m : Nat} {σ : Sub Head n m} {term : Tm Head n} {left right : Tm Head m}
    (same : subst σ term = .pair left right) :
    (∃ index, term = .var index) ∨ ∃ first second, term = .pair first second := by
  cases term with
  | var index => exact .inl ⟨index, rfl⟩
  | pair first second => exact .inr ⟨first, second, rfl⟩
  | _ => cases same

/-- A variable of the support whose image is a variable stays in the support. -/
theorem support_subst_var {n : Nat} (term : Tm Head n) :
    ∀ {m : Nat} (σ : Sub Head n m) (index : Fin n) (image : Fin m),
      index ∈ term.support → σ index = .var image → image ∈ (subst σ term).support := by
  induction term with
  | var other =>
      intro m σ index image member mapped
      have same : index = other := by simpa [Tm.support] using member
      subst same
      simp [subst, mapped, Tm.support]
  | const name => intro m σ index image member; simp [Tm.support] at member
  | head value => intro m σ index image member; simp [Tm.support] at member
  | pi domain body ihDomain ihBody =>
      intro m σ index image member mapped
      simp only [Tm.support, Finset.mem_union, mem_outerSupport] at member
      simp only [subst, Tm.support, Finset.mem_union, mem_outerSupport]
      rcases member with member | member
      · exact .inl (ihDomain σ index image member mapped)
      · exact .inr (ihBody (liftSub σ) index.succ image.succ member (by simp [liftSub_succ, mapped]; rfl))
  | sigma domain body ihDomain ihBody =>
      intro m σ index image member mapped
      simp only [Tm.support, Finset.mem_union, mem_outerSupport] at member
      simp only [subst, Tm.support, Finset.mem_union, mem_outerSupport]
      rcases member with member | member
      · exact .inl (ihDomain σ index image member mapped)
      · exact .inr (ihBody (liftSub σ) index.succ image.succ member (by simp [liftSub_succ, mapped]; rfl))
  | id carrier left right ihCarrier ihLeft ihRight =>
      intro m σ index image member mapped
      simp only [Tm.support, Finset.mem_union] at member
      simp only [subst, Tm.support, Finset.mem_union]
      rcases member with (member | member) | member
      · exact .inl (.inl (ihCarrier σ index image member mapped))
      · exact .inl (.inr (ihLeft σ index image member mapped))
      · exact .inr (ihRight σ index image member mapped)
  | lam body ih =>
      intro m σ index image member mapped
      simp only [Tm.support, mem_outerSupport] at member
      simp only [subst, Tm.support, mem_outerSupport]
      exact ih (liftSub σ) index.succ image.succ member (by simp [liftSub_succ, mapped]; rfl)
  | app function argument ihFunction ihArgument =>
      intro m σ index image member mapped
      simp only [Tm.support, Finset.mem_union] at member
      simp only [subst, Tm.support, Finset.mem_union]
      rcases member with member | member
      · exact .inl (ihFunction σ index image member mapped)
      · exact .inr (ihArgument σ index image member mapped)
  | pair left right ihLeft ihRight =>
      intro m σ index image member mapped
      simp only [Tm.support, Finset.mem_union] at member
      simp only [subst, Tm.support, Finset.mem_union]
      rcases member with member | member
      · exact .inl (ihLeft σ index image member mapped)
      · exact .inr (ihRight σ index image member mapped)
  | fst value ih =>
      intro m σ index image member mapped
      simp only [Tm.support] at member
      simp only [subst, Tm.support]
      exact ih σ index image member mapped
  | snd value ih =>
      intro m σ index image member mapped
      simp only [Tm.support] at member
      simp only [subst, Tm.support]
      exact ih σ index image member mapped
  | refl value ih =>
      intro m σ index image member mapped
      simp only [Tm.support] at member
      simp only [subst, Tm.support]
      exact ih σ index image member mapped

end Shapes

section Normality

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (rigid : ∀ name, S.roles name = .rigid)

local notation "Normal" => ContextualDependentNormalChecking.Normal (S := S)

/-- Flexible variables receive normal terms; the others are renamed. -/
def Admissible (S : Setting Head L) {n m : Nat} (flexible : Fin n → Bool) (σ : Sub Head n m) : Prop :=
  ∀ index, (flexible index = true → ContextualDependentNormalChecking.Normal (S := S) (σ index)) ∧ (flexible index = false → ∃ image, σ index = .var image)

include rigid in
theorem Admissible.lift {n m : Nat} {flexible : Fin n → Bool} {σ : Sub Head n m}
    (admissible : Admissible S flexible σ) : Admissible S (liftFlexible flexible) (liftSub σ) := by
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · exact ⟨fun impossible => (by cases impossible), fun _ => ⟨0, rfl⟩⟩
  · refine ⟨fun flexiblePrior => ?_, fun rigidPrior => ?_⟩
    · rw [liftSub_succ]
      exact ContextualDependentNormalObservations.normal_rename rigid wk ((admissible prior).1 flexiblePrior)
    · obtain ⟨image, mapped⟩ := (admissible prior).2 rigidPrior
      exact ⟨image.succ, by rw [liftSub_succ, mapped]; rfl⟩

include rigid in
/-- Substituting normal terms for flexible variables that never occur as
elimination heads, and variables for the others, preserves normality. -/
theorem subst_normal {n : Nat} (term : Tm Head n) :
    ∀ {m : Nat} (flexible : Fin n → Bool) (σ : Sub Head n m),
      Normal term → HeadFree flexible term = true → Admissible S flexible σ → Normal (subst σ term) := by
  induction term with
  | var index =>
      intro m flexible σ _ _ admissible target step
      cases mode : flexible index with
      | true => exact (admissible index).1 mode target step
      | false =>
          obtain ⟨image, mapped⟩ := (admissible index).2 mode
          change StrongNormalization.Reduces S.R (σ index) target at step
          rw [mapped] at step
          cases step with
          | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
  | const name =>
      intro m flexible σ _ _ _ target step
      change StrongNormalization.Reduces S.R (.const name) target at step
      cases step with
      | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
  | head value =>
      intro m flexible σ _ _ _ target step
      change StrongNormalization.Reduces S.R (.head value) target at step
      cases step with
      | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
      | head same => exact (same : False).elim
  | pi domain body ihDomain ihBody =>
      intro m flexible σ normal free admissible target step
      simp only [HeadFree, Bool.and_eq_true] at free
      change StrongNormalization.Reduces S.R (.pi (subst σ domain) (subst (liftSub σ) body)) target at step
      cases step with
      | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
      | congPiDom inner =>
          exact ihDomain flexible σ (fun _ next => normal _ (.congPiDom next)) free.1 admissible _ inner
      | congPiCod inner =>
          exact ihBody (liftFlexible flexible) (liftSub σ) (fun _ next => normal _ (.congPiCod next)) free.2
            (admissible.lift rigid) _ inner
  | sigma domain body ihDomain ihBody =>
      intro m flexible σ normal free admissible target step
      simp only [HeadFree, Bool.and_eq_true] at free
      change StrongNormalization.Reduces S.R (.sigma (subst σ domain) (subst (liftSub σ) body)) target at step
      cases step with
      | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
      | congSigmaDom inner =>
          exact ihDomain flexible σ (fun _ next => normal _ (.congSigmaDom next)) free.1 admissible _ inner
      | congSigmaCod inner =>
          exact ihBody (liftFlexible flexible) (liftSub σ) (fun _ next => normal _ (.congSigmaCod next)) free.2
            (admissible.lift rigid) _ inner
  | id carrier left right ihCarrier ihLeft ihRight =>
      intro m flexible σ normal free admissible target step
      simp only [HeadFree, Bool.and_eq_true] at free
      change StrongNormalization.Reduces S.R (.id (subst σ carrier) (subst σ left) (subst σ right)) target at step
      cases step with
      | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
      | congIdTy inner =>
          exact ihCarrier flexible σ (fun _ next => normal _ (.congIdTy next)) free.1.1 admissible _ inner
      | congIdLeft inner =>
          exact ihLeft flexible σ (fun _ next => normal _ (.congIdLeft next)) free.1.2 admissible _ inner
      | congIdRight inner =>
          exact ihRight flexible σ (fun _ next => normal _ (.congIdRight next)) free.2 admissible _ inner
  | lam body ih =>
      intro m flexible σ normal free admissible target step
      simp only [HeadFree] at free
      change StrongNormalization.Reduces S.R (.lam (subst (liftSub σ) body)) target at step
      cases step with
      | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
      | congLam inner =>
          exact ih (liftFlexible flexible) (liftSub σ) (fun _ next => normal _ (.congLam next)) free
            (admissible.lift rigid) _ inner
  | app function argument ihFunction ihArgument =>
      intro m flexible σ normal free admissible target step
      simp only [HeadFree, Bool.and_eq_true] at free
      obtain ⟨⟨notHead, functionFree⟩, argumentFree⟩ := free
      change StrongNormalization.Reduces S.R (.app (subst σ function) (subst σ argument)) target at step
      generalize shapeFunction : subst σ function = instantiated at step
      cases step with
      | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
      | betaPi inner _ =>
          rcases subst_eq_lam shapeFunction with ⟨index, rfl⟩ | ⟨inner', rfl⟩
          · have rigidIndex : flexible index = false := by simpa [notFlexibleHead] using notHead
            obtain ⟨image, mapped⟩ := (admissible index).2 rigidIndex
            change σ index = _ at shapeFunction
            rw [mapped] at shapeFunction
            cases shapeFunction
          · exact normal _ (.betaPi inner' argument)
      | congAppFun inner =>
          subst shapeFunction
          exact ihFunction flexible σ (fun _ next => normal _ (.congAppFun next)) functionFree admissible _ inner
      | congAppArg inner =>
          exact ihArgument flexible σ (fun _ next => normal _ (.congAppArg next)) argumentFree admissible _ inner
  | pair left right ihLeft ihRight =>
      intro m flexible σ normal free admissible target step
      simp only [HeadFree, Bool.and_eq_true] at free
      change StrongNormalization.Reduces S.R (.pair (subst σ left) (subst σ right)) target at step
      cases step with
      | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
      | congPairFst inner =>
          exact ihLeft flexible σ (fun _ next => normal _ (.congPairFst next)) free.1 admissible _ inner
      | congPairSnd inner =>
          exact ihRight flexible σ (fun _ next => normal _ (.congPairSnd next)) free.2 admissible _ inner
  | fst value ih =>
      intro m flexible σ normal free admissible target step
      simp only [HeadFree, Bool.and_eq_true] at free
      obtain ⟨notHead, valueFree⟩ := free
      change StrongNormalization.Reduces S.R (.fst (subst σ value)) target at step
      generalize shapeValue : subst σ value = instantiated at step
      cases step with
      | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
      | betaSigmaFst first second =>
          rcases subst_eq_pair shapeValue with ⟨index, rfl⟩ | ⟨first', second', rfl⟩
          · have rigidIndex : flexible index = false := by simpa [notFlexibleHead] using notHead
            obtain ⟨image, mapped⟩ := (admissible index).2 rigidIndex
            change σ index = _ at shapeValue
            rw [mapped] at shapeValue
            cases shapeValue
          · exact normal _ (.betaSigmaFst first' second')
      | congFst inner =>
          subst shapeValue
          exact ih flexible σ (fun _ next => normal _ (.congFst next)) valueFree admissible _ inner
  | snd value ih =>
      intro m flexible σ normal free admissible target step
      simp only [HeadFree, Bool.and_eq_true] at free
      obtain ⟨notHead, valueFree⟩ := free
      change StrongNormalization.Reduces S.R (.snd (subst σ value)) target at step
      generalize shapeValue : subst σ value = instantiated at step
      cases step with
      | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
      | betaSigmaSnd first second =>
          rcases subst_eq_pair shapeValue with ⟨index, rfl⟩ | ⟨first', second', rfl⟩
          · have rigidIndex : flexible index = false := by simpa [notFlexibleHead] using notHead
            obtain ⟨image, mapped⟩ := (admissible index).2 rigidIndex
            change σ index = _ at shapeValue
            rw [mapped] at shapeValue
            cases shapeValue
          · exact normal _ (.betaSigmaSnd first' second')
      | congSnd inner =>
          subst shapeValue
          exact ih flexible σ (fun _ next => normal _ (.congSnd next)) valueFree admissible _ inner
  | refl value ih =>
      intro m flexible σ normal free admissible target step
      simp only [HeadFree] at free
      change StrongNormalization.Reduces S.R (.refl (subst σ value)) target at step
      cases step with
      | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
      | congRefl inner =>
          exact ih flexible σ (fun _ next => normal _ (.congRefl next)) free admissible _ inner

end Normality

section NormalSolutions

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
  ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
    Equal S.R Θ.raw term.code code type.code)

include normalizes in
/-- Every solution is typed-equal to one whose components are normal. -/
theorem exists_normal_solution {Γ Δ : Context S.R} (solution : Δ ⟶ Γ) :
    ∃ normalSolution : Δ ⟶ Γ, homTypedEquality S.R solution normalSolution ∧
      ∀ index, ContextualDependentNormalChecking.Normal (S := S) (normalSolution.substitution index) := by
  have entry : ∀ index : Fin Γ.arity, ∃ code : Tm Head Δ.arity,
      ContextualDependentNormalChecking.Normal (S := S) code ∧
        Equal S.R Δ.raw (solution.substitution index) code (subst solution.substitution (Ctx.lookup Γ.raw index)) := by
    intro index
    obtain ⟨level, isUniverse, formed⟩ := CtxFormed.lookup Γ.formed index
    exact normalizes (type := (⟨Ctx.lookup Γ.raw index, level, isUniverse, formed⟩ : TypeOver Γ).reindex solution)
      ⟨solution.substitution index, solution.typed index⟩
  choose codes normal equal using entry
  have substEq : SubstEq S.R Γ.raw Δ.raw solution.substitution codes := ⟨solution.typed, equal⟩
  refine ⟨⟨codes, fun index => ?_⟩, substEq, normal⟩
  obtain ⟨level, isUniverse, formed⟩ := CtxFormed.lookup Γ.formed index
  have types := Typed.functional formed substEq
  have typed := (Equal.typed (S := S) (equal index) Δ.formed).2
  exact Typed.convType typed ⟨level, isUniverse, types⟩

end NormalSolutions

section RigidRefutation

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)
variable (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
  ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
    Equal S.R Θ.raw term.code code type.code)

/-- The outer variables of a local telescope are the flexible ones. -/
def outerFlexible {Γ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType) :
    Fin scope.target.arity → Bool :=
  fun index => (scope.originEquiv.symm index).isLeft

include rigid in
theorem admissible_map {Γ Δ : Context S.R} {scopeType : TypeOver Γ} (scope : Spine scopeType)
    (solution : Δ ⟶ Γ)
    (componentsNormal : ∀ index, ContextualDependentNormalChecking.Normal (S := S) (solution.substitution index)) :
    Admissible S (outerFlexible scope) (scope.map solution).substitution := by
  intro index
  cases origin : scope.originEquiv.symm index with
  | inl prior =>
      have located : scope.outerRen prior = index := by
        rw [← scope.outer_origin, ← origin, Equiv.apply_symm_apply]
      refine ⟨fun _ => ?_, fun flexibleFalse => ?_⟩
      · rw [← located, scope.map_outer]
        exact ContextualDependentNormalObservations.normal_rename rigid _ (componentsNormal prior)
      · simp [outerFlexible, origin] at flexibleFalse
  | inr position =>
      have located : scope.localIndex position = index := by
        unfold Spine.localIndex
        rw [← origin, Equiv.apply_symm_apply]
      refine ⟨fun flexibleTrue => ?_, fun _ => ?_⟩
      · simp [outerFlexible, origin] at flexibleTrue
      · subst located
        exact ⟨_, map_localRead scope solution position position⟩

namespace Pattern

variable {Γ : Context S.R} {type : TypeOver Γ} {spine : Spine type}
  {scopeType : TypeOver (extend Γ type)} {scope : Spine scopeType} (pattern : Pattern spine scope)

include rigid complete normalizes in
/-- A rigid local outside the argument image refutes the flex equation even
when the right side mentions outer metavariables, provided none of them is
an elimination head. -/
theorem refuted_rigid (right : Term scope.target ((lifted spine).result.reindex pattern.map.hom))
    (outside : scope.Local) (notArgument : ∀ position, pattern.args position ≠ outside)
    (occurs : scope.localIndex outside ∈ right.code.support)
    (free : HeadFree (outerFlexible scope) right.code = true)
    (normal : ContextualDependentNormalChecking.Normal (S := S) right.code)
    {Δ : Context S.R} (solution : Δ ⟶ extend Γ type) :
    ¬ (pattern.constraint right).Holds solution := by
  intro solved
  obtain ⟨normalSolution, same, componentsNormal⟩ := exists_normal_solution normalizes solution
  have moved := (Scoped.holds_iff_of_same S.levels (pattern.constraint right) solution normalSolution
    (act_equal_of_substEq S.levels same)).mp solved
  rw [constraint, Spine.toScoped_holds_iff] at moved
  change Equal S.R (scope.reindex normalSolution).target.raw
      (subst (scope.map normalSolution).substitution pattern.application.code)
      (subst (scope.map normalSolution).substitution right.code)
      (subst (scope.map normalSolution).substitution ((lifted spine).result.reindex pattern.map.hom).code) at moved
  rw [pattern.application_code, pattern.annotation_code] at moved
  obtain ⟨normalCode, isNormal, toNormal⟩ :=
    normalizes (((lifted spine).reindex normalSolution).openFunction ((newest Γ type).reindex normalSolution))
  have renamed := toNormal.rename (pattern.reread_compatible normalSolution)
  have joined := renamed.symm.trans moved
  have rightNormal := subst_normal rigid right.code (outerFlexible scope) (scope.map normalSolution).substitution
    normal free (admissible_map rigid scope normalSolution componentsNormal)
  have supports := ContextualDependentNormalSupport.equal_support rigid complete
    (scope.reindex normalSolution).target.formed joined
    (ContextualDependentNormalObservations.normal_rename rigid _ isNormal) rightNormal
  have member := support_subst_var right.code (scope.map normalSolution).substitution (scope.localIndex outside)
    (localRead scope normalSolution outside (scope.localIndex outside)) occurs
    (map_localRead scope normalSolution outside outside)
  rw [← supports, ContextualDependentSupport.support_rename] at member
  obtain ⟨index, _, hit⟩ := Finset.mem_image.mp member
  rw [localRead_local] at hit
  obtain ⟨position, image⟩ := (local_mem_range_iff ((lifted spine).reindex normalSolution)
    (scope.reindex normalSolution) idRen (reindexArgs (lifted spine) scope pattern.liftedArgs normalSolution) _).mp
    ⟨index, hit⟩
  exact notArgument _ ((scope.localReindexEquiv normalSolution).symm.injective image)

end Pattern
end RigidRefutation

end ContextualDependentGeneralPattern
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
