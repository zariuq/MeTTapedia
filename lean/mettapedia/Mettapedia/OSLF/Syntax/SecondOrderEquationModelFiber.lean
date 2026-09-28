import Mettapedia.OSLF.Syntax.SecondOrderEquationLexCompletion
import Mettapedia.OSLF.Syntax.FreeBindingEquationModel

/-!
# Binding equation models over contextual equation classes

At each second-order context, the quotient by lifted authored equations is
an actual binding-clone model of the original language. Its carrier is the
same equation-class term family represented by arrows of the quotient
context category. This identifies the categorical term object with the
existing free binding-equation semantics.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FreeBindingTerms

variable {S : Signature} {M : List (MetaArity S)}

universe u

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

/-- At every ambient second-order context, the actual equation quotient is
a semantic model of the original authored binding equations. -/
noncomputable def authoredEquationModelAt (S : Signature)
    {M : List (MetaArity S)}
    (equations : List (EqAxiom S M)) (X : Object S) :
    FreeBindingEquationModel.Model equations where
  algebra := restrictAlgebra X
    (BindingEquationQuotientModel.algebra
      ((authoredEquationPresentation S equations).axioms X))
  satisfies := by
    intro index valuation Γ environment
    let sourceIndex : Fin
        ((authoredEquationPresentation S equations).axioms X).length :=
      ⟨index.val, by simp [authoredEquationPresentation]⟩
    have selected :
        ((authoredEquationPresentation S equations).axioms X).get
          sourceIndex = liftEquation X (equations.get index) := by
      change (equations.map (liftEquation X))[index.val] =
        liftEquation X (equations[index.val])
      simp
    have valid := (BindingEquationQuotientModel.algebra_satisfies
      ((authoredEquationPresentation S equations).axioms X)) sourceIndex
    rw [selected] at valid
    have atInstance := valid (fun k => valuation k)
      (Γ := Γ) (fun s v => environment s v)
    change _ = _ at atInstance
    simp only [liftEquation] at atInstance
    rw [← interpretSchema_restrictAlgebra X
      (BindingEquationQuotientModel.algebra
        ((authoredEquationPresentation S equations).axioms X))
      valuation (equations.get index).lhs,
      ← interpretSchema_restrictAlgebra X
      (BindingEquationQuotientModel.algebra
        ((authoredEquationPresentation S equations).axioms X))
      valuation (equations.get index).rhs] at atInstance
    change BindingEquationQuotientSubstitution.substitute
        ((authoredEquationPresentation S equations).axioms X) environment
        (BindingEquationInterpretation.interpretSchema
          (restrictAlgebra X (BindingEquationQuotientModel.algebra
            ((authoredEquationPresentation S equations).axioms X)))
          valuation (equations.get index).lhs) =
      BindingEquationQuotientSubstitution.substitute
        ((authoredEquationPresentation S equations).axioms X) environment
        (BindingEquationInterpretation.interpretSchema
          (restrictAlgebra X (BindingEquationQuotientModel.algebra
            ((authoredEquationPresentation S equations).axioms X)))
          valuation (equations.get index).rhs)
    exact atInstance

end Mettapedia.OSLF.Binding.SecondOrderContext

#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredEquationModelAt
