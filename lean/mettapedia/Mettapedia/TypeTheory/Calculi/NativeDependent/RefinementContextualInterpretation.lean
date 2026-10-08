import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractEvidenceExtraction
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualCwf
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualPredicates
import Mettapedia.GSLT.Core.ContextualLadderBaseCategory

/-!
# Actual semantic values of generated refinement equation classes

The model supplies local dependent and predicate operations, their local
computational equations and independent primitive meanings. Induction on the
retained generated rule trees earns every interpreted family, section,
predicate and guarded substitution. Their generated equations then earn
descent to the independently authored quotients.

Raw contexts remain objects. The semantic readouts retain supplied dependent
values; no complete interpreter or classifying property is a model field.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualPiEta
open Mettapedia.TypeTheory.ContextualPredicateModel
open Refinement.Abstract

universe u c s t m p
variable {S : Symbols.{u}} {D : Signature S} {C : CwfWithTerminal.{c, s, t, m}}

/-- Only primitive declaration realization and local constructor equations
qualify the independently supplied model. -/
structure QualifiedModel (D : Signature S) (C : CwfWithTerminal.{c, s, t, m}) where
  localModel : LocalModel.{c, s, t, m, p} C
  data : Abstract.ModelData S C localModel
  realization : Abstract.SignatureRealization data D
  products_substitution : StrictPiSubstitution localModel.products
  products_beta : PiBeta localModel.products
  products_eta : PiEta localModel.products products_substitution.1

variable (model : QualifiedModel.{u,c,s,t,m,p} D C)

noncomputable def contextValue (context : Context D) :
    Abstract.ModelScope C model.localModel context.arity :=
  Abstract.Derivation.contextValue model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice context.formed.judgment)

theorem context_readout (context : Context D) :
    model.data.evaluateContext context.raw = some (contextValue model context) :=
  Abstract.Derivation.contextValue_readout model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice context.formed.judgment)

noncomputable def rawType {context : Context D} (type : TypeOver context) :
    C.toCwf.Ty (contextValue model context).1 :=
  Abstract.Derivation.typeValue model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice type.formed) _ (context_readout model context)

theorem type_readout {context : Context D} (type : TypeOver context) :
    model.data.evaluateType (contextValue model context) type.code = some (rawType model type) :=
  Abstract.Derivation.typeValue_readout model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice type.formed) _ (context_readout model context)

theorem rawType_congruent {context : Context D} {first second : TypeOver context}
    (same : Holds D (.typeEq context.raw first.code second.code)) :
    rawType model first = rawType model second :=
  Abstract.Derivation.typeValue_equation model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice first.formed)
    (Classical.choice second.formed) (Classical.choice same) _ (context_readout model context)

noncomputable def typeValue {context : Context D} (type : QType context) :
    C.toCwf.Ty (contextValue model context).1 :=
  _root_.Quotient.lift (rawType model) (fun _ _ same => rawType_congruent model same) type

@[simp] theorem typeValue_mk {context : Context D} (type : TypeOver context) :
    typeValue model (QType.mk type) = rawType model type := rfl

noncomputable def rawTerm {context : Context D} {type : TypeOver context} (term : Term context type) :
    C.toCwf.Tm (contextValue model context).1 (rawType model type) :=
  Abstract.Derivation.termSection model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice term.typed) _ _
      (context_readout model context) (type_readout model type)

theorem term_readout {context : Context D} {type : TypeOver context} (term : Term context type) :
    model.data.evaluateTerm (contextValue model context) term.code =
      some ⟨rawType model type, rawTerm model term⟩ :=
  Abstract.Derivation.termSection_readout model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice term.typed) _ _
      (context_readout model context) (type_readout model type)

noncomputable def rawTotal {context : Context D} (term : TotalTerm context) :
    ContextualModelTelescopes.Value C.toCwf (contextValue model context).1 :=
  ⟨rawType model term.1, rawTerm model term.2⟩

theorem rawTotal_congruent {context : Context D} {first second : TotalTerm context}
    (same : (totalTermSetoid context).r first second) :
    rawTotal model first = rawTotal model second := by
  rcases (Abstract.Derivation.sound model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice same.2)).termEqAt
      (contextValue model context) (rawType model first.1)
      (context_readout model context) (type_readout model first.1) with
        ⟨value, firstRead, secondRead⟩
  exact Option.some.inj ((term_readout model first.2).symm.trans
    (firstRead.trans (secondRead.symm.trans (term_readout model second.2))))

noncomputable def totalValue {context : Context D} (term : QTerm context) :
    ContextualModelTelescopes.Value C.toCwf (contextValue model context).1 :=
  _root_.Quotient.lift (rawTotal model) (fun _ _ same => rawTotal_congruent model same) term

@[simp] theorem totalValue_mk {context : Context D} {type : TypeOver context} (term : Term context type) :
    totalValue model (QTerm.mk term) = ⟨rawType model type, rawTerm model term⟩ := rfl

theorem totalValue_type {context : Context D} (term : QTerm context) :
    (totalValue model term).1 = typeValue model term.type := by
  induction term using _root_.Quotient.inductionOn with
  | h representative => rfl

/-- A fibre equation transports the retained section to the exact supplied
semantic family. The total-term quotient was formed independently. -/
noncomputable def termValue {context : QuotientCwf.QContext D} {type : QuotientCwf.Ty context}
    (term : QuotientCwf.Tm context type) :
    C.toCwf.Tm (contextValue model context.as).1 (typeValue model type) :=
  cast (congrArg (C.toCwf.Tm (contextValue model context.as).1)
    ((totalValue_type model term.val).trans (congrArg (typeValue model) term.property)))
      (totalValue model term.val).2

theorem termValue_retains_section {context : QuotientCwf.QContext D}
    {type : QuotientCwf.Ty context} (term : QuotientCwf.Tm context type) :
    HEq (termValue model term) (totalValue model term.val).2 := cast_heq _ _

noncomputable def rawArrow {source target : Context D} (morphism : source ⟶ target) :
    C.toCwf.Sub (contextValue model source).1 (contextValue model target).1 :=
  Abstract.Derivation.substitutionArrow model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice morphism.admitted) _ _
      (context_readout model source) (context_readout model target)

theorem arrow_readout {source target : Context D} (morphism : source ⟶ target) :
    model.data.evaluateSubstitution (contextValue model source) (contextValue model target)
      morphism.substitution = some (rawArrow model morphism) :=
  Abstract.Derivation.substitutionArrow_readout model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice morphism.admitted) _ _
      (context_readout model source) (context_readout model target)

theorem rawArrow_congruent {source target : Context D} {first second : source ⟶ target}
    (same : homEquality D first second) : rawArrow model first = rawArrow model second :=
  Abstract.Derivation.substitutionArrow_equation model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice first.admitted)
    (Classical.choice second.admitted) (Classical.choice same) _ _
      (context_readout model source) (context_readout model target)

noncomputable def rawPredicate {context : Context D} (predicate : PredicateOver context) :
    model.localModel.doctrine.Predicate (contextValue model context).1 :=
  Abstract.Derivation.predicateValue model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice predicate.formed) _ (context_readout model context)

theorem predicate_readout {context : Context D} (predicate : PredicateOver context) :
    model.data.evaluatePredicate (contextValue model context) predicate.code =
      some (rawPredicate model predicate) :=
  Abstract.Derivation.predicateValue_readout model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice predicate.formed) _ (context_readout model context)

theorem rawPredicate_congruent {context : Context D} {first second : PredicateOver context}
    (same : Holds D (.predicateEq context.raw first.code second.code)) :
    rawPredicate model first = rawPredicate model second :=
  Abstract.Derivation.predicateValue_equation model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice first.formed)
    (Classical.choice second.formed) (Classical.choice same) _ (context_readout model context)

noncomputable def predicateValue {context : Context D} (predicate : QPredicate context) :
    model.localModel.doctrine.Predicate (contextValue model context).1 :=
  _root_.Quotient.lift (rawPredicate model) (fun _ _ same => rawPredicate_congruent model same) predicate

@[simp] theorem predicateValue_mk {context : Context D} (predicate : PredicateOver context) :
    predicateValue model (QPredicate.mk predicate) = rawPredicate model predicate := rfl

theorem rawPredicate_entailment {context : Context D} (predicate : PredicateOver context)
    (evidence : Holds D (.entails context.raw predicate.code)) :
    rawPredicate model predicate = ⊤ :=
  Abstract.Derivation.predicateValue_entailment model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice predicate.formed)
    (Classical.choice evidence) _ (context_readout model context)

theorem predicateValue_entailment {context : Context D} (predicate : QPredicate context)
    (evidence : predicate.entails) : predicateValue model predicate = ⊤ := by
  revert evidence
  refine _root_.Quotient.inductionOn predicate fun formed evidence => ?_
  exact rawPredicate_entailment model formed evidence

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation
