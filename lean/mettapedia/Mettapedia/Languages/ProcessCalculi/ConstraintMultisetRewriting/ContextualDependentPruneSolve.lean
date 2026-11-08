import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruneSubterm
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentOccursCheck
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRenameAgreement

/-!
# Pruning under rigid binder contexts

Under a local telescope, the equation `f x̄ ≐ t` has the newest metavariable `G` applied to distinct locals somewhere
in `t` along dependent function and pair types: in a domain, or in a codomain without mentioning its binder
(`BinderContext`), for instance `Π D (G ȳ)`, `Σ (G ȳ) B` or `Π A (Π B (G ȳ))`. The other side applies a term `f`, for
instance an older metavariable `F`, to distinct locals `x̄`. Every solution gives `G` a value whose opening is a
renaming of a body over the binders of `G` whose argument occurs among `x̄` (`forced_binderContext`).

The proof follows R76's forcing under a rigid head (`ContextualDependentPrune.forced_rigidContext`), with the binder
types as the rigid context. The equation is at a universe, so both sides are types. Along the context the other parts
are typed by the generation of the binder types and normalized at their own universes; the binder types of the normal
parts are normal (`normal_binderType`), and their support contains the support of the pattern's normal form, read past
the binders (`binderContext_support`). Typed equality of normal forms keeps supports (`equal_support`), so the support
of `G`'s normal opening is hit by the arguments of `f`, and R76's forcing core gives the factorization.

`pruneBinderContext` is the pruning update; it loses no solution of a store that contains the equation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPruneSolve

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentEta
open ContextualDependentUpdate ContextualDependentTypedInversion ContextualDependentScope ContextualDependentPrune

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
/-- A dependent function type of normal parts is normal. -/
theorem normal_pi {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)}
    (normalA : ContextualDependentNormalChecking.Normal (S := S) A)
    (normalB : ContextualDependentNormalChecking.Normal (S := S) B) :
    ContextualDependentNormalChecking.Normal (S := S) (.pi A B) := by
  intro target step
  cases step with
  | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
  | congPiDom inner => exact normalA _ inner
  | congPiCod inner => exact normalB _ inner

include rigid in
/-- A dependent pair type of normal parts is normal. -/
theorem normal_sigma {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)}
    (normalA : ContextualDependentNormalChecking.Normal (S := S) A)
    (normalB : ContextualDependentNormalChecking.Normal (S := S) B) :
    ContextualDependentNormalChecking.Normal (S := S) (.sigma A B) := by
  intro target step
  cases step with
  | root rootStep => exact ContextualDependentNormalObservations.no_root rigid rootStep
  | congSigmaDom inner => exact normalA _ inner
  | congSigmaCod inner => exact normalB _ inner

include rigid in
/-- A binder type of normal parts is normal. -/
theorem normal_binderType (isPi : Bool) {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)}
    (normalA : ContextualDependentNormalChecking.Normal (S := S) A)
    (normalB : ContextualDependentNormalChecking.Normal (S := S) B) :
    ContextualDependentNormalChecking.Normal (S := S) (ContextualDependentRigidFormers.binder isPi A B) := by
  cases isPi
  · exact normal_sigma rigid normalA normalB
  · exact normal_pi rigid normalA normalB

/-- The support of a binder type: the domain's, and the codomain's past the binder. -/
theorem support_binder (isPi : Bool) {n : Nat} (A : Tm Head n) (B : Tm Head (n + 1)) :
    (ContextualDependentRigidFormers.binder isPi A B).support = A.support ∪ outerSupport B.support := by
  cases isPi <;> rfl

/-! ## Rigid binder contexts -/

/-- **A rigid binder context around a pattern**: the pattern itself, a binder type with the context in its domain, or
a binder type with the context in its codomain and the pattern weakened past the binder. -/
inductive BinderContext : {m : Nat} → Tm Head m → Tm Head m → Prop
  | here {m : Nat} (P : Tm Head m) : BinderContext P P
  | domain {m : Nat} (isPi : Bool) {P A : Tm Head m} (B : Tm Head (m + 1)) :
      BinderContext P A → BinderContext P (ContextualDependentRigidFormers.binder isPi A B)
  | codomain {m : Nat} (isPi : Bool) {P : Tm Head m} (A : Tm Head m) {B : Tm Head (m + 1)} :
      BinderContext (Presentation.rename wk P) B → BinderContext P (ContextualDependentRigidFormers.binder isPi A B)

/-- **Binder contexts are kept by substitutions.** -/
theorem BinderContext.subst {m : Nat} {P t : Tm Head m} (context : BinderContext P t) :
    ∀ {k : Nat} (σ : Sub Head m k), BinderContext (Presentation.subst σ P) (Presentation.subst σ t) := by
  induction context with
  | here P => exact fun σ => .here _
  | domain isPi B _ ih =>
      intro k σ
      rw [ContextualDependentRigidFormers.subst_binder]
      exact .domain isPi _ (ih σ)
  | codomain isPi A _ ih =>
      intro k σ
      rw [ContextualDependentRigidFormers.subst_binder]
      have inner := ih (liftSub σ)
      rw [subst_liftSub_wk] at inner
      exact .codomain isPi _ inner

include rigid normalizes facts in
/-- **The support of a pattern's normal form survives in a rigid binder context.** A typed type in a binder context
around a pattern has a normal form whose support contains the support of the pattern's normal form. -/
theorem binderContext_support {m : Nat} {P t : Tm Head m} (context : BinderContext P t) :
    ∀ {Γ : Ctx Head m}, CtxFormed S.R Γ → ∀ {u : Head}, S.R.isUniverse u → TypedEquality.Typed S.R Γ t (.head u) →
      ∀ {gN : Tm Head m}, ContextualDependentNormalChecking.Normal (S := S) gN → TypeEq S.R Γ P gN →
        ∃ N, ContextualDependentNormalChecking.Normal (S := S) N ∧ TypeEq S.R Γ t N ∧ gN.support ⊆ N.support := by
  induction context with
  | here P =>
      intro Γ _ u _ _ gN gNormal same
      exact ⟨gN, gNormal, same, subset_refl _⟩
  | @domain m isPi P A B _ ih =>
      intro Γ formed u hu typed gN gNormal same
      obtain ⟨⟨w, hw, tA⟩, ⟨v, hv, tB⟩⟩ :=
        ContextualDependentOccursCheck.binder_parts_typed (S := S) isPi ⟨u, hu, typed⟩
      obtain ⟨NA, nNA, eqA, subA⟩ := ih formed hw tA gNormal same
      have isA : IsType S.R Γ A := ⟨w, hw, tA⟩
      let extended : Context S.R := ⟨m + 1, .snoc Γ A, formed.snoc isA⟩
      obtain ⟨v', hv', tv⟩ := ContextualDependentRigidFormers.universe_isType (S := S) extended.raw hv
      let universeType : TypeOver extended := ⟨.head v, v', hv', tv⟩
      obtain ⟨bCode, nB, eqB⟩ := normalizes (⟨B, tB⟩ : Term extended universeType)
      refine ⟨ContextualDependentRigidFormers.binder isPi NA bCode, normal_binderType rigid isPi nNA nB,
        (ContextualDependentRigidFormers.typeEq_binder_iff facts isPi formed).mpr ⟨eqA, ⟨v, hv, eqB⟩⟩, ?_⟩
      rw [support_binder]
      exact subA.trans Finset.subset_union_left
  | @codomain m isPi P A B _ ih =>
      intro Γ formed u hu typed gN gNormal same
      obtain ⟨⟨w, hw, tA⟩, ⟨v, hv, tB⟩⟩ :=
        ContextualDependentOccursCheck.binder_parts_typed (S := S) isPi ⟨u, hu, typed⟩
      have isA : IsType S.R Γ A := ⟨w, hw, tA⟩
      obtain ⟨NB, nNB, eqB, subB⟩ := ih (formed.snoc isA) hv tB
        (ContextualDependentNormalObservations.normal_rename rigid wk gNormal) (same.rename (CtxRen.wk Γ A))
      let base : Context S.R := ⟨m, Γ, formed⟩
      obtain ⟨w', hw', tw⟩ := ContextualDependentRigidFormers.universe_isType (S := S) base.raw hw
      let universeType : TypeOver base := ⟨.head w, w', hw', tw⟩
      obtain ⟨dCode, nD, eqD⟩ := normalizes (⟨A, tA⟩ : Term base universeType)
      refine ⟨ContextualDependentRigidFormers.binder isPi dCode NB, normal_binderType rigid isPi nD nNB,
        (ContextualDependentRigidFormers.typeEq_binder_iff facts isPi formed).mpr ⟨⟨w, hw, eqD⟩, eqB⟩, ?_⟩
      rw [support_binder]
      intro index present
      apply Finset.mem_union_right
      rw [mem_outerSupport]
      apply subB
      rw [ContextualDependentSupport.support_rename]
      exact Finset.mem_image.mpr ⟨index, present, rfl⟩

variable {Γ : Context S.R} {type : TypeOver Γ} {spine : Spine type}
  {scopeType : TypeOver (extend Γ type)} {scope : Spine scopeType}

include rigid complete normalizes facts algebra headTypingUnique roots heads declared in
/-- **Forcing under a rigid binder context.** For `f x̄ ≐ t` at a universe, with `t` a rigid binder context around
`G ȳ` at a universe, every solution gives `G` a value whose opening is a renaming of a body over the kept binders, for
every restriction covering the arguments of `G` that occur among `x̄`. -/
theorem forced_binderContext (pattern : Pattern spine scope) (app : Application scope) (active : Active scope.target)
    {u v : Head} (hu : S.R.isUniverse u) (hv : S.R.isUniverse v)
    (leftCode : active.left.code = app.term.code)
    (context : BinderContext pattern.application.code active.right.code)
    (annotation : active.type.code = .head u)
    (leftType : (app.spine.result.reindex app.map.hom).code = active.type.code)
    (gResult : ((lifted spine).result.reindex pattern.map.hom).code = .head v)
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
  rw [leftCode, app.term_code, annotation] at held
  change Equal S.R _ _ _ (.head u) at held
  have formed := (scope.reindex solution).target.formed
  have moved := context.subst (scope.map solution).substitution
  rw [pattern.application_code] at moved
  -- Normal forms of both opened values.
  obtain ⟨gCode, gNormal, gSame⟩ := normalizes
    (((lifted spine).reindex solution).openFunction ((newest Γ type).reindex solution))
  obtain ⟨fCode, fNormal, fSame⟩ := normalizes
    ((app.spine.reindex solution).openFunction (app.function.reindex solution))
  have gRenamed := gSame.rename (pattern.reread_compatible solution)
  have fRenamed := fSame.rename (app.reread_compatible solution)
  have fAnnotation : Presentation.rename (app.reread solution) (app.spine.reindex solution).result.code =
      .head u := by
    have mapped := app.annotation_code solution
    rw [leftType, annotation] at mapped
    exact mapped.symm
  rw [fAnnotation] at fRenamed
  have gAnnotation : ((lifted spine).reindex solution).result.code = .head v := by
    have mapped := pattern.annotation_code solution
    rw [gResult] at mapped
    exact ContextualDependentRenameAgreement.rename_eq_head mapped.symm
  rw [gAnnotation] at gRenamed
  -- The right side's normal form keeps the support of `G`'s.
  have rightTyped := (Equal.typed (S := S) held formed).2
  have gTypes : TypeEq S.R (scope.reindex solution).target.raw _ _ := ⟨v, hv, gRenamed⟩
  obtain ⟨N, nN, eqN, contains⟩ := binderContext_support rigid normalizes facts moved formed hu rightTyped
    (ContextualDependentNormalObservations.normal_rename rigid _ gNormal) gTypes
  have heldTypes : TypeEq S.R (scope.reindex solution).target.raw _ _ := ⟨u, hu, held⟩
  have fTypes : TypeEq S.R (scope.reindex solution).target.raw _ _ := ⟨u, hu, fRenamed⟩
  have sameNormal : TypeEq S.R (scope.reindex solution).target.raw N
      (Presentation.rename (app.reread solution) fCode) :=
    TypeEq.trans S.levels eqN.symm (TypeEq.trans S.levels heldTypes.symm fTypes)
  obtain ⟨_, _, sameEqual⟩ := sameNormal
  have supports := ContextualDependentNormalSupport.equal_support rigid complete formed sameEqual nN
    (ContextualDependentNormalObservations.normal_rename rigid _ fNormal)
  refine forced_of_hits rigid complete facts algebra headTypingUnique roots heads declared pattern app
    restriction covers solution gCode gNormal gSame ?_
  intro index present
  have inside : pattern.reread solution index ∈ N.support := by
    apply contains
    rw [ContextualDependentSupport.support_rename]
    exact Finset.mem_image.mpr ⟨index, present, rfl⟩
  rw [supports, ContextualDependentSupport.support_rename] at inside
  obtain ⟨other, _, same⟩ := Finset.mem_image.mp inside
  exact ⟨other, same⟩

include rigid complete normalizes facts algebra headTypingUnique roots heads declared in
/-- **Pruning under a rigid binder context loses no solution.** A store whose solutions all satisfy `f x̄ ≐ t`, with
`t` a rigid binder context around `G ȳ`, is instantiated with `G := λ ȳ. H (ȳ restricted)`. -/
def pruneBinderContext (pattern : Pattern spine scope) (app : Application scope) (active : Active scope.target)
    {u v : Head} (hu : S.R.isUniverse u) (hv : S.R.isUniverse v)
    (leftCode : active.left.code = app.term.code)
    (context : BinderContext pattern.application.code active.right.code)
    (annotation : active.type.code = .head u)
    (leftType : (app.spine.result.reindex app.map.hom).code = active.type.code)
    (gResult : ((lifted spine).result.reindex pattern.map.hom).code = .head v)
    {keptType : TypeOver Γ} {kept : Spine keptType} (restriction : Restriction spine kept)
    (covers : ∀ position : spine.Local, (∃ other, app.args other = pattern.args position) →
      ∃ chosen, restriction.keep chosen = position)
    (problem : EquationStore (TotalTerm (extend Γ type)))
    (contains : ∀ {Δ : Context S.R} (solution : Δ ⟶ extend Γ type), (frames S.levels).Models solution problem →
      (scope.toScoped active).Holds solution) :
    Update S.levels problem :=
  prune S.levels restriction problem fun _ solution solved =>
    forced_binderContext rigid complete normalizes facts algebra headTypingUnique roots heads declared
      pattern app active hu hv leftCode context annotation leftType gResult restriction covers solution
      (contains solution solved)

end ContextualDependentPruneSolve
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
