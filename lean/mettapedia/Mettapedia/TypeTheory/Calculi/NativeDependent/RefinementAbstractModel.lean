import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSyntax
import Mettapedia.TypeTheory.ContextualPredicateModel
import Mettapedia.TypeTheory.ContextualPredicateModelScopes

/-!
# Independent declarations in local predicate models

Each primitive type, term and predicate has its own ordered mixed parameter
scope. Its semantic meaning is an actual local family, dependent section or
predicate at that scope. The semantic scopes are built from local operations;
no complete interpreter or generated-rule soundness is a field.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateModel ContextualPredicateModelScopes ContextualModelTelescopes

universe a c s t m p

variable (S : Symbols.{a}) (C : CwfWithTerminal.{c, s, t, m})
    (localModel : LocalModel.{c, s, t, m, p} C)

abbrev ModelScope (n : Nat) := Scope C localModel.doctrine localModel.assumptions n

structure ModelData where
  typeParameters : (symbol : S.TypeSymbol) → ModelScope C localModel (S.typeArity symbol)
  typeFamily : (symbol : S.TypeSymbol) → C.toCwf.Ty (typeParameters symbol).1
  termParameters : (symbol : S.TermSymbol) → ModelScope C localModel (S.termArity symbol)
  termType : (symbol : S.TermSymbol) → C.toCwf.Ty (termParameters symbol).1
  termValue : (symbol : S.TermSymbol) → C.toCwf.Tm (termParameters symbol).1 (termType symbol)
  predicateParameters : (symbol : S.PredicateSymbol) → ModelScope C localModel (S.predicateArity symbol)
  predicateValue : (symbol : S.PredicateSymbol) → localModel.doctrine.Predicate (predicateParameters symbol).1

namespace ModelData

variable {S C localModel}

def familyAt (model : ModelData S C localModel) {context : C.toCwf.Ctx} (symbol : S.TypeSymbol)
    (arguments : C.toCwf.Sub context (model.typeParameters symbol).1) : C.toCwf.Ty context :=
  C.toCwf.tySub (model.typeFamily symbol) arguments

def primitiveAt (model : ModelData S C localModel) {context : C.toCwf.Ctx} (symbol : S.TermSymbol)
    (arguments : C.toCwf.Sub context (model.termParameters symbol).1) : Value C.toCwf context :=
  Value.substitute (K := C.toCwf)
    (⟨model.termType symbol, model.termValue symbol⟩ : Value C.toCwf _) arguments

def predicateAt (model : ModelData S C localModel) {context : C.toCwf.Ctx} (symbol : S.PredicateSymbol)
    (arguments : C.toCwf.Sub context (model.predicateParameters symbol).1) :
    localModel.doctrine.Predicate context :=
  localModel.doctrine.reindex arguments (model.predicateValue symbol)

theorem familyAt_substitution (model : ModelData S C localModel) {source target : C.toCwf.Ctx}
    (symbol : S.TypeSymbol) (arguments : C.toCwf.Sub target (model.typeParameters symbol).1)
    (substitution : C.toCwf.Sub source target) :
    C.toCwf.tySub (model.familyAt symbol arguments) substitution =
      model.familyAt symbol (C.toCwf.compS arguments substitution) :=
  (C.toCwf.tySub_comp _ _ _).symm

theorem primitiveAt_substitution (model : ModelData S C localModel) {source target : C.toCwf.Ctx}
    (symbol : S.TermSymbol) (arguments : C.toCwf.Sub target (model.termParameters symbol).1)
    (substitution : C.toCwf.Sub source target) :
    Value.substitute (K := C.toCwf) (model.primitiveAt symbol arguments) substitution =
      model.primitiveAt symbol (C.toCwf.compS arguments substitution) :=
  (Value.substitute_composition _ _ _).symm

theorem predicateAt_substitution (model : ModelData S C localModel) {source target : C.toCwf.Ctx}
    (symbol : S.PredicateSymbol) (arguments : C.toCwf.Sub target (model.predicateParameters symbol).1)
    (substitution : C.toCwf.Sub source target) :
    localModel.doctrine.reindex substitution (model.predicateAt symbol arguments) =
      model.predicateAt symbol (C.toCwf.compS arguments substitution) :=
  (localModel.doctrine.reindex_comp _ _ _).symm

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
