import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModel
import Mettapedia.TypeTheory.ContextualPredicateModelScopeUniverseLift

/-!
# Changing the carriers of independent mixed declarations

All three primitive parameter scopes retain their ordered binders. Families,
complete term sections and predicates use the actual contextual carrier
lifts. The declaration meanings are recovered by their down readouts.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.TypeTheory.ContextualPredicateModelScopeUniverseLift
open Mettapedia.TypeTheory.ContextualModelTelescopes

universe a c s t m p uc vs wt ms ps
variable {S : Symbols.{a}} {C : CwfWithTerminal.{c,s,t,m}}
variable {localModel : LocalModel.{c,s,t,m,p} C}

namespace ModelData

def lift (model : ModelData S C localModel) :
    ModelData S (Mettapedia.TypeTheory.ContextualCwfUniverseLift.liftWithTerminal.{c,s,t,m,uc,vs,wt,ms} C)
      (Mettapedia.TypeTheory.ContextualPredicateModelUniverseLift.lift.{c,s,t,m,p,uc,vs,wt,ms,ps}
        localModel) where
  typeParameters symbol := liftScope (model.typeParameters symbol)
  typeFamily symbol := ULift.up (model.typeFamily symbol)
  termParameters symbol := liftScope (model.termParameters symbol)
  termType symbol := ULift.up (model.termType symbol)
  termValue symbol := ULift.up (model.termValue symbol)
  predicateParameters symbol := liftScope (model.predicateParameters symbol)
  predicateValue symbol := ULift.up (model.predicateValue symbol)

@[simp] theorem lift_type_parameter_context (model : ModelData S C localModel) (symbol : S.TypeSymbol) :
    ((model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}).typeParameters symbol).1.down =
      (model.typeParameters symbol).1 := rfl

@[simp] theorem lift_term_parameter_context (model : ModelData S C localModel) (symbol : S.TermSymbol) :
    ((model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}).termParameters symbol).1.down =
      (model.termParameters symbol).1 := rfl

@[simp] theorem lift_predicate_parameter_context (model : ModelData S C localModel)
    (symbol : S.PredicateSymbol) :
    ((model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}).predicateParameters symbol).1.down =
      (model.predicateParameters symbol).1 := rfl

@[simp] theorem lift_family_readout (model : ModelData S C localModel) (symbol : S.TypeSymbol) :
    ((model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}).typeFamily symbol).down =
      model.typeFamily symbol := rfl

@[simp] theorem lift_term_type_readout (model : ModelData S C localModel) (symbol : S.TermSymbol) :
    ((model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}).termType symbol).down = model.termType symbol := rfl

@[simp] theorem lift_term_readout (model : ModelData S C localModel) (symbol : S.TermSymbol) :
    ((model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}).termValue symbol).down = model.termValue symbol := rfl

@[simp] theorem lift_predicate_readout (model : ModelData S C localModel) (symbol : S.PredicateSymbol) :
    ((model.lift.{a,c,s,t,m,p,uc,vs,wt,ms,ps}).predicateValue symbol).down =
      model.predicateValue symbol := rfl

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
