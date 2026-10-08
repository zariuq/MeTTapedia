import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModelUniverseCommutation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualInterpretation

/-!
# Complete mixed declaration realization after a carrier change

Authored contexts retain both data binders and assumption restrictions.
Supplied substitutions retain their exact arrow. The four primitive
realization obligations follow from expression and context comparison;
the local product equations then qualify the lifted dependent model.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateModel ContextualPredicateModelScopes ContextualModelTelescopes
open ContextualCwfUniverseLift ContextualPredicateModelScopeUniverseLift
open ContextualTypeOperations ContextualPiEta
open External (bindResult)

universe a c s t m p uc vs wt ms ps
variable {S : Symbols.{a}} {C : CwfWithTerminal.{c,s,t,m}}
variable {localModel : LocalModel.{c,s,t,m,p} C} {D : Signature S}

namespace ModelData

theorem evaluateContext_carrierLift (model : ModelData S C localModel) :
    {n : Nat} → (raw : ContextExpr S n) → (Γ : ModelScope C localModel n) →
    model.evaluateContext raw = some Γ →
    (model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}).evaluateContext raw =
      some (liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} Γ)
  | _, .nil, Γ, evaluated => by
      have actual : Scope.nil C localModel.doctrine localModel.assumptions = Γ :=
        Option.some.inj evaluated
      rw [← actual]
      rfl
  | _, .snoc previous type, Γ, evaluated => by
      rw [evaluateContext] at evaluated
      rcases (External.bindResult_eq_some_iff _ _ _).mp evaluated with ⟨earlier, contextRead, rest⟩
      rcases (External.bindResult_eq_some_iff _ _ _).mp rest with ⟨A, typeRead, last⟩
      rw [← Option.some.inj last]
      exact model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}.evaluateContext_snoc previous type
        (liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} earlier) (ULift.up A)
        (evaluateContext_carrierLift model previous earlier contextRead)
        (model.evaluateType_carrierLift type earlier A typeRead)
  | _, .assume previous predicate, Γ, evaluated => by
      rw [evaluateContext] at evaluated
      rcases (External.bindResult_eq_some_iff _ _ _).mp evaluated with ⟨earlier, contextRead, rest⟩
      rcases (External.bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      rw [← Option.some.inj last]
      exact model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}.evaluateContext_assume previous predicate
        (liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} earlier) (ULift.up φ)
        (evaluateContext_carrierLift model previous earlier contextRead)
        (model.evaluatePredicate_carrierLift predicate earlier φ predicateRead)

theorem evaluateSubstitution_carrierLift (model : ModelData S C localModel) {n k : Nat}
    (Γ : ModelScope C localModel n) (Δ : ModelScope C localModel k)
    (substitution : Substitution S k n) (σ : C.toCwf.Sub Γ.1 Δ.1)
    (evaluated : model.evaluateSubstitution Γ Δ substitution = some σ) :
    (model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}).evaluateSubstitution
      (liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} Γ)
      (liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} Δ) substitution = some (ULift.up σ) := by
  apply (model.lift.evaluateSubstitution_eq_some_iff _ _ _ _).mpr
  intro index
  have read := (model.evaluateSubstitution_eq_some_iff _ _ _ _).mp evaluated index
  exact (model.evaluateTerm_carrierLift (substitution index) Γ _ read).trans
    (congrArg some (liftScopeData_components.{c,s,t,m,p,uc,vs,wt,ms,ps} Δ.2 σ index).symm)

end ModelData

namespace SignatureRealization

theorem carrierLift {model : ModelData S C localModel}
    (realization : SignatureRealization model D) :
    SignatureRealization (model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}) D where
  typeHeader symbol := model.evaluateContext_carrierLift _ _ (realization.typeHeader symbol)
  termHeader symbol := model.evaluateContext_carrierLift _ _ (realization.termHeader symbol)
  predicateHeader symbol := model.evaluateContext_carrierLift _ _ (realization.predicateHeader symbol)
  termResult symbol := model.evaluateType_carrierLift _ _ _ (realization.termResult symbol)

end SignatureRealization

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualCwfUniverseLift
open Mettapedia.TypeTheory.ContextualPredicateModelScopeUniverseLift
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualPiEta

universe a c s t m p uc vs wt ms ps
variable {S : Symbols.{a}} {D : Signature S} {C : CwfWithTerminal.{c,s,t,m}}

namespace QualifiedModel

def carrierLift (model : QualifiedModel.{a,c,s,t,m,p} D C) :
    QualifiedModel D (liftWithTerminal.{c,s,t,m,uc,vs,wt,ms} C) where
  localModel := ContextualPredicateModelUniverseLift.lift.{c,s,t,m,p,uc,vs,wt,ms,ps} model.localModel
  data := model.data.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}
  realization := model.realization.carrierLift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}
  products_substitution := lifted_products_substitution model.localModel.products model.products_substitution
  products_beta := lifted_products_beta model.localModel.products model.products_beta
  products_eta := lifted_products_eta model.localModel.products model.products_substitution.1 model.products_eta

/-- The predicate carrier remains independently sized while the four CwF
carriers use a common external level. -/
abbrev commonCarrierLift (model : QualifiedModel.{a,c,s,t,m,p} D C) :
    QualifiedModel D (commonLiftWithTerminal.{c,s,t,m,uc} C) :=
  model.carrierLift.{a,c,s,t,m,p,max c s t m uc,max c s t m uc,
    max c s t m uc,max c s t m uc,ps}

end QualifiedModel

theorem contextValue_carrierLift (model : QualifiedModel.{a,c,s,t,m,p} D C)
    (context : Context D) :
    contextValue (model.carrierLift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}) context =
      liftScope.{c,s,t,m,p,uc,vs,wt,ms,ps} (contextValue model context) :=
  Option.some.inj ((context_readout model.carrierLift context).symm.trans
    (model.data.evaluateContext_carrierLift context.raw (contextValue model context)
      (context_readout model context)))

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation
