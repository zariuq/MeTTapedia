import Mettapedia.OSLF.Syntax.SecondOrderSchemaInterpretation
import Mettapedia.OSLF.Syntax.SemanticContextualMetavariables

/-!
# Restricting binding models along a signature inclusion

The original sorts and binder contexts are retained when freely adjoined
metavariable operators are forgotten. These laws do not use equation quotients.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FreeBindingTerms

variable {S : Signature} {M : List (MetaArity S)}

universe u u₁ u₂

/-- Repackage semantic arguments across the freely adjoined operator
signature. The carrier and all binder contexts are unchanged. -/
def toAmbientArgs (X : Object S) {F : Ctx S → S.Srt → Type u} :
    {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
      FamilyArgs S F arities Γ →
        FamilyArgs (withMetas S X.arities) F arities Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons head (toAmbientArgs X tail)

/-- The original signature and its contextual extension have the same
contexts, variables, and semantic substitution laws. -/
def restrictSubstitution (X : Object S)
    (A : BindingCloneAlgebra.Algebra.{u} (withMetas S X.arities)) :
    BindingSubstitutionAlgebra.Algebra.{u} S where
  Carrier := A.substitution.Carrier
  injectVar := A.substitution.injectVar
  substitute := A.substitution.substitute
  substitute_var := by intros; exact A.substitution.substitute_var _ _
  substitute_identity := by intros; exact A.substitution.substitute_identity _
  substitute_comp := by intros; exact A.substitution.substitute_comp _ _ _

theorem restrict_liftEnvironment (X : Object S)
    (A : BindingCloneAlgebra.Algebra.{u} (withMetas S X.arities))
    {Γ Δ : Ctx S}
    (environment : BindingSubstitutionAlgebra.Environment S
      A.substitution.Carrier Γ Δ) (binders : List S.Srt) :
    (restrictSubstitution X A).liftEnvironment environment binders =
      A.substitution.liftEnvironment environment binders := by
  induction binders with
  | nil => rfl
  | cons fresh binders ih =>
      funext sort index
      cases index with
      | zero => rfl
      | succ old =>
          change A.substitution.substitute
              (fun _ v => A.substitution.injectVar (.succ v))
              ((restrictSubstitution X A).liftEnvironment environment binders sort old) =
            A.substitution.substitute
              (fun _ v => A.substitution.injectVar (.succ v))
              (A.substitution.liftEnvironment environment binders sort old)
          exact congrArg _ (congrFun (congrFun ih sort) old)

/-- Repackaging each argument preserves its substitution under its own
binder extension. -/
theorem toAmbientArgs_substituteArgs (X : Object S)
    (A : BindingCloneAlgebra.Algebra.{u} (withMetas S X.arities))
    {Γ Δ : Ctx S}
    (environment : BindingSubstitutionAlgebra.Environment S
      A.substitution.Carrier Γ Δ) :
    ∀ {arities : List (List S.Srt × S.Srt)}
      (args : FamilyArgs S A.substitution.Carrier arities Γ),
      toAmbientArgs X
        ((restrictSubstitution X A).substituteArgs environment args) =
      A.substitution.substituteArgs environment (toAmbientArgs X args)
  | _, .nil => rfl
  | _, .cons head tail => by
      simp only [BindingSubstitutionAlgebra.Algebra.substituteArgs, toAmbientArgs]
      rw [restrict_liftEnvironment X A environment]
      exact congrArg (FamilyArgs.cons _)
        (toAmbientArgs_substituteArgs X A environment tail)

/-- Forget the freely adjoined contextual metavariable operators while
retaining the full substitution action and the original binding operators. -/
def restrictAlgebra (X : Object S)
    (A : BindingCloneAlgebra.Algebra.{u} (withMetas S X.arities)) :
    BindingCloneAlgebra.Algebra.{u} S where
  substitution := restrictSubstitution X A
  operation := fun op args => A.operation (Sum.inl op) (toAmbientArgs X args)
  operation_substitute := by
    intro Γ Δ sort environment op args
    let ambientEnvironment : BindingSubstitutionAlgebra.Environment
        (withMetas S X.arities) A.substitution.Carrier Γ Δ :=
      fun s v => environment s v
    change A.substitution.substitute ambientEnvironment
        (A.operation (Sum.inl op) (toAmbientArgs X args)) =
      A.operation (Sum.inl op)
        (toAmbientArgs X
          ((restrictSubstitution X A).substituteArgs environment args))
    rw [A.operation_substitute]
    exact congrArg (A.operation (Sum.inl op))
      (toAmbientArgs_substituteArgs X A environment args).symm

/-- Repackaging arguments commutes with mapping them. -/
theorem toAmbientArgs_map (X : Object S) {F : Ctx S → S.Srt → Type u₁}
    {G : Ctx S → S.Srt → Type u₂}
    (f : ∀ {Γ : Ctx S} {sort : S.Srt}, F Γ sort → G Γ sort) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S} (args : FamilyArgs S F arities Γ),
      toAmbientArgs X (FamilyArgs.map f args) = FamilyArgs.map f (toAmbientArgs X args)
  | _, _, .nil => rfl
  | _, _, .cons _ tail => congrArg _ (toAmbientArgs_map X f tail)

/-- A binding-clone map over the signature extended by the metavariables of
`X` restricts to a map of the underlying binding clones. -/
def restrictHom (X : Object S)
    {A : BindingCloneAlgebra.Algebra.{u₁} (withMetas S X.arities)}
    {B : BindingCloneAlgebra.Algebra.{u₂} (withMetas S X.arities)}
    (h : FreeBindingClone.Hom A B) :
    FreeBindingClone.Hom (restrictAlgebra X A) (restrictAlgebra X B) where
  raw :=
    { map := h.raw.map
      map_variable := h.raw.map_variable
      map_operation := by
        intro Γ sort op args
        exact (h.raw.map_operation (Sum.inl op) (toAmbientArgs X args)).trans
          (congrArg (B.operation (Sum.inl op)) (toAmbientArgs_map X h.raw.map args).symm) }
  map_substitute := h.map_substitute

/-- Repackaging metavariable arguments does not change the environment
that they supply to a semantic metavariable body. -/
theorem argsEnvironment_toAmbient (X : Object S)
    (A : BindingCloneAlgebra.Algebra.{u} (withMetas S X.arities)) :
    ∀ {dependencies : List S.Srt} {Γ : Ctx S}
      (args : FamilyArgs S A.substitution.Carrier
        (dependencies.map (fun sort => ([], sort))) Γ),
      BindingEquationalModels.argsEnvironment (restrictAlgebra X A) args =
        BindingEquationalModels.argsEnvironment A (toAmbientArgs X args)
  | [], _, .nil => by
      funext sort index
      exact nomatch index
  | _ :: _, _, .cons _head tail => by
      funext sort index
      cases index with
      | zero => rfl
      | succ old =>
          exact congrFun (congrFun (argsEnvironment_toAmbient X A tail) sort) old

mutual

/-- Restricting a model and interpreting an authored schema agrees with
interpreting its lifted schema in the full ambient model. -/
theorem interpretSchema_restrictAlgebra (X : Object S)
    (A : BindingCloneAlgebra.Algebra.{u} (withMetas S X.arities))
    (valuation : BindingEquationalModels.MetaValuation
      (restrictAlgebra X A) M) :
    ∀ {Γ : Ctx S} {sort : S.Srt}
      (schema : Term (withMetas S M) Γ sort),
      BindingEquationInterpretation.interpretSchema
        (restrictAlgebra X A) valuation schema =
      BindingEquationInterpretation.interpretSchema
        A valuation (liftSchema X schema)
  | _, _, .var _ => rfl
  | _, _, .op (Sum.inl op) args => by
      change A.operation (Sum.inl op)
        (toAmbientArgs X (BindingEquationInterpretation.interpretSchemaArgs
          (restrictAlgebra X A) valuation args)) =
        A.operation (Sum.inl op)
          (BindingEquationInterpretation.interpretSchemaArgs
            A valuation (liftSchemaArgs X args))
      exact congrArg (A.operation (Sum.inl op))
        (interpretSchemaArgs_restrictAlgebra X A valuation args)
  | _, _, .op (Sum.inr (.mk index)) args => by
      change A.substitution.substitute
          (BindingEquationalModels.argsEnvironment (restrictAlgebra X A)
            (BindingEquationInterpretation.interpretSchemaArgs
              (restrictAlgebra X A) valuation args)) (valuation index) =
        A.substitution.substitute
          (BindingEquationalModels.argsEnvironment A
            (BindingEquationInterpretation.interpretSchemaArgs
              A valuation (liftSchemaArgs X args))) (valuation index)
      have sameEnvironment :
          BindingEquationalModels.argsEnvironment (restrictAlgebra X A)
              (BindingEquationInterpretation.interpretSchemaArgs
                (restrictAlgebra X A) valuation args) =
            BindingEquationalModels.argsEnvironment A
              (BindingEquationInterpretation.interpretSchemaArgs
                A valuation (liftSchemaArgs X args)) := by
        calc
          _ = BindingEquationalModels.argsEnvironment A
              (toAmbientArgs X (BindingEquationInterpretation.interpretSchemaArgs
                (restrictAlgebra X A) valuation args)) :=
                  argsEnvironment_toAmbient X A _
          _ = _ := congrArg (BindingEquationalModels.argsEnvironment A)
            (interpretSchemaArgs_restrictAlgebra X A valuation args)
      exact congrArg (fun env => A.substitution.substitute env (valuation index))
        sameEnvironment

/-- The interpretation comparison respects every argument's binder context. -/
theorem interpretSchemaArgs_restrictAlgebra (X : Object S)
    (A : BindingCloneAlgebra.Algebra.{u} (withMetas S X.arities))
    (valuation : BindingEquationalModels.MetaValuation
      (restrictAlgebra X A) M) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : Args (withMetas S M) arities Γ),
      toAmbientArgs X (BindingEquationInterpretation.interpretSchemaArgs
        (restrictAlgebra X A) valuation args) =
      BindingEquationInterpretation.interpretSchemaArgs
        A valuation (liftSchemaArgs X args)
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      exact congrArg₂ FamilyArgs.cons
        (interpretSchema_restrictAlgebra X A valuation head)
        (interpretSchemaArgs_restrictAlgebra X A valuation tail)

end


private theorem weakenVar_restriction (X : Object S) {Γ : Ctx S} {s : S.Srt}
    (v : Var Γ s) : ∀ (bs : Ctx S),
    @weakenVar S Γ s bs v = @weakenVar (withMetas S X.arities) Γ s bs v
  | [] => rfl
  | _ :: bs => congrArg Var.succ (weakenVar_restriction X v bs)

/-- Restriction preserves the weakening of every captured ambient value. -/
theorem contextualWeakenEnvironment_restrictAlgebra (X : Object S)
    (A : BindingCloneAlgebra.Algebra.{u} (withMetas S X.arities))
    {Θ Γ : Ctx S}
    (ambient : BindingSubstitutionAlgebra.Environment S A.substitution.Carrier Θ Γ)
    (bs : Ctx S) :
    SemanticContextualMetavariables.weakenEnvironment (restrictAlgebra X A) bs ambient =
      SemanticContextualMetavariables.weakenEnvironment A bs ambient := by
  funext s v
  unfold SemanticContextualMetavariables.weakenEnvironment
  change A.substitution.substitute
      (fun s v => A.substitution.injectVar (@weakenVar S Γ s bs v)) (ambient s v) =
    A.substitution.substitute
      (fun s v => A.substitution.injectVar (@weakenVar (withMetas S X.arities) Γ s bs v))
      (ambient s v)
  congr 1
  funext s v
  exact congrArg A.substitution.injectVar (weakenVar_restriction X v bs)

/-- The shared dependency/ambient join is unchanged by signature restriction. -/
theorem contextualJoinEnvironment_restrictAlgebra (X : Object S)
    (A : BindingCloneAlgebra.Algebra.{u} (withMetas S X.arities)) {Θ Γ : Ctx S} :
    ∀ (deps : Ctx S)
      (arguments : BindingSubstitutionAlgebra.Environment S A.substitution.Carrier deps Γ)
      (ambient : BindingSubstitutionAlgebra.Environment S A.substitution.Carrier Θ Γ),
      SemanticContextualMetavariables.joinEnvironment (S := S) arguments ambient =
        SemanticContextualMetavariables.joinEnvironment
          (S := withMetas S X.arities) arguments ambient
  | [], _, _ => rfl
  | _ :: deps, arguments, ambient => by
      funext s v
      cases v with
      | zero => rfl
      | succ old => exact congrFun (congrFun
          (contextualJoinEnvironment_restrictAlgebra X A deps
            (fun s v => arguments s (.succ v)) ambient) s) old

mutual

/-- The shared contextual fold commutes with signature restriction, retaining
arbitrary captured bodies and both independent environments. -/
theorem interpretContextualSchema_restrictAlgebra (X : Object S)
    (A : BindingCloneAlgebra.Algebra.{u} (withMetas S X.arities))
    {Θ Ξ Γ : Ctx S}
    (body : SemanticContextualMetavariables.Valuation (M := M) (restrictAlgebra X A) Θ)
    (ambient : BindingSubstitutionAlgebra.Environment S A.substitution.Carrier Θ Γ)
    (ordinary : BindingSubstitutionAlgebra.Environment S A.substitution.Carrier Ξ Γ) :
    ∀ {s : S.Srt} (term : Term (withMetas S M) Ξ s),
      SemanticContextualMetavariables.interpretSchema (restrictAlgebra X A)
          body ambient ordinary term =
        SemanticContextualMetavariables.interpretSchema A
          body ambient ordinary (liftSchema X term)
  | _, .var _ => rfl
  | _, .op (.inl op) args => by
      change A.operation (.inl op)
          (toAmbientArgs X (SemanticContextualMetavariables.interpretArgs
            (restrictAlgebra X A) body ambient ordinary args)) =
        A.operation (.inl op) (SemanticContextualMetavariables.interpretArgs
          A body ambient ordinary (liftSchemaArgs X args))
      exact congrArg (A.operation (.inl op))
        (interpretContextualSchemaArgs_restrictAlgebra X A body ambient ordinary args)
  | _, .op (.inr (.mk k)) args => by
      simp only [SemanticContextualMetavariables.interpretSchema,
        SemanticContextualMetavariables.apply, liftSchema]
      change A.substitution.substitute
          (SemanticContextualMetavariables.joinEnvironment (S := S)
            (BindingEquationalModels.argsEnvironment (restrictAlgebra X A)
              (SemanticContextualMetavariables.interpretArgs
                (restrictAlgebra X A) body ambient ordinary args)) ambient) (body k) =
        A.substitution.substitute
          (SemanticContextualMetavariables.joinEnvironment (S := withMetas S X.arities)
            (BindingEquationalModels.argsEnvironment A
              (SemanticContextualMetavariables.interpretArgs
                A body ambient ordinary (liftSchemaArgs X args))) ambient) (body k)
      have arguments := (argsEnvironment_toAmbient X A
        (SemanticContextualMetavariables.interpretArgs
          (restrictAlgebra X A) body ambient ordinary args)).trans
        (congrArg (BindingEquationalModels.argsEnvironment A)
          (interpretContextualSchemaArgs_restrictAlgebra X A body ambient ordinary args))
      have joined := contextualJoinEnvironment_restrictAlgebra X A (M.get k).1
        (BindingEquationalModels.argsEnvironment (restrictAlgebra X A)
          (SemanticContextualMetavariables.interpretArgs
            (restrictAlgebra X A) body ambient ordinary args)) ambient
      exact congrArg (fun env => A.substitution.substitute env (body k))
        (joined.trans (congrArg
          (fun env => SemanticContextualMetavariables.joinEnvironment
            (S := withMetas S X.arities) env ambient) arguments))
termination_by _ term => 2 * termSize term
decreasing_by
  all_goals simp_wf
  all_goals simp only [termSize]
  all_goals omega

/-- Restriction preserves every ordered argument and its declared binder
context, including the separate ambient weakening and ordinary lifting. -/
theorem interpretContextualSchemaArgs_restrictAlgebra (X : Object S)
    (A : BindingCloneAlgebra.Algebra.{u} (withMetas S X.arities))
    {Θ Ξ Γ : Ctx S}
    (body : SemanticContextualMetavariables.Valuation (M := M) (restrictAlgebra X A) Θ)
    (ambient : BindingSubstitutionAlgebra.Environment S A.substitution.Carrier Θ Γ)
    (ordinary : BindingSubstitutionAlgebra.Environment S A.substitution.Carrier Ξ Γ) :
    ∀ {L : List (MetaArity S)} (args : Args (withMetas S M) L Ξ),
      toAmbientArgs X (SemanticContextualMetavariables.interpretArgs
          (restrictAlgebra X A) body ambient ordinary args) =
        SemanticContextualMetavariables.interpretArgs
          A body ambient ordinary (liftSchemaArgs X args)
  | _, .nil => rfl
  | _, .cons (bs := bs) head tail => by
      change FamilyArgs.cons (S := withMetas S X.arities)
          (SemanticContextualMetavariables.interpretSchema (restrictAlgebra X A) body
            (SemanticContextualMetavariables.weakenEnvironment (restrictAlgebra X A) bs ambient)
            ((restrictSubstitution X A).liftEnvironment ordinary bs) head)
          (toAmbientArgs X (SemanticContextualMetavariables.interpretArgs
            (restrictAlgebra X A) body ambient ordinary tail)) =
        FamilyArgs.cons (S := withMetas S X.arities)
          (SemanticContextualMetavariables.interpretSchema A body
            (SemanticContextualMetavariables.weakenEnvironment A bs ambient)
            (A.substitution.liftEnvironment ordinary bs) (liftSchema X head))
          (SemanticContextualMetavariables.interpretArgs A body ambient ordinary
            (liftSchemaArgs X tail))
      rw [contextualWeakenEnvironment_restrictAlgebra X A ambient bs,
        restrict_liftEnvironment X A ordinary bs]
      exact congrArg₂ FamilyArgs.cons
        (interpretContextualSchema_restrictAlgebra X A body _ _ head)
        (interpretContextualSchemaArgs_restrictAlgebra X A body ambient ordinary tail)
termination_by _ args => 2 * argsSize args + 1
decreasing_by
  all_goals simp_wf
  all_goals simp only [argsSize]
  all_goals first | omega | have := termSize_pos head; omega

end

end Mettapedia.OSLF.Binding.SecondOrderContext
