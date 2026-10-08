import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualMorphism
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualProducts
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualSums
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractConstructorInterpretation

/-!
# Constructor readouts on interpreted contextual classes

Selected annotations and sections retain their complete model values.
The interpreted domain extension is the actual telescope extension. These
comparisons supply the child evaluations needed by the independently
defined constructor evaluator, including every dependent binder.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open QuotientComprehensionSyntax DependentTypes
open Refinement.Abstract

universe u c s t m p
variable {S : Symbols.{u}} {D : Signature S} {C : CwfWithTerminal.{c, s, t, m}}

variable (model : QualifiedModel.{u,c,s,t,m,p} D C)

theorem native_type_readout_transport {n : Nat}
    {first second : Abstract.ModelScope C model.localModel n}
    (contexts : first = second) (code : TypeExpr S n)
    {left : C.toCwf.Ty first.1} {right : C.toCwf.Ty second.1}
    (types : HEq left right) (read : model.data.evaluateType first code = some left) :
    model.data.evaluateType second code = some right := by
  cases contexts
  cases eq_of_heq types
  exact read

theorem native_term_readout_transport {n : Nat}
    {first second : Abstract.ModelScope C model.localModel n}
    (contexts : first = second) (code : TermExpr S n)
    {A : C.toCwf.Ty first.1} {B : C.toCwf.Ty second.1}
    (types : HEq A B) {left : C.toCwf.Tm first.1 A} {right : C.toCwf.Tm second.1 B}
    (terms : HEq left right)
    (read : model.data.evaluateTerm first code = some ⟨A, left⟩) :
    model.data.evaluateTerm second code = some ⟨B, right⟩ := by
  cases contexts
  cases eq_of_heq types
  cases eq_of_heq terms
  exact read

theorem represented_type_readout {context : QuotientCwf.QContext D}
    (type : QuotientCwf.Ty context) :
    model.data.evaluateType (contextValue model context.as)
        (QuotientCwf.typeRepresentative type).code = some (typeValue model type) :=
  (type_readout model (QuotientCwf.typeRepresentative type)).trans
    (congrArg some (congrArg (typeValue model) (QuotientCwf.typeRepresentative_class type)))

theorem termValue_total {context : QuotientCwf.QContext D} {type : QuotientCwf.Ty context}
    (term : QuotientCwf.Tm context type) :
    totalValue model term.val = ⟨typeValue model type, termValue model term⟩ := by
  apply Sigma.ext
  · exact (totalValue_type model term.val).trans (congrArg (typeValue model) term.property)
  · exact (termValue_retains_section model term).symm

theorem represented_term_readout {context : QuotientCwf.QContext D}
    {type : QuotientCwf.Ty context} (term : QuotientCwf.Tm context type)
    {annotation : TypeOver context.as} (actual : Term context.as annotation)
    (represents : QTerm.mk actual = term.val) :
    model.data.evaluateTerm (contextValue model context.as) actual.code =
      some ⟨typeValue model type, termValue model term⟩ := by
  have values : rawTotal model ⟨annotation, actual⟩ =
      ⟨typeValue model type, termValue model term⟩ := by
    change totalValue model (QTerm.mk actual) = _
    rw [represents]
    exact termValue_total model term
  exact (term_readout model actual).trans (congrArg some values)

theorem chosen_term_readout {context : QuotientCwf.QContext D}
    {type : QuotientCwf.Ty context} (term : QuotientCwf.Tm context type) :
    model.data.evaluateTerm (contextValue model context.as) (chosenTerm term).code =
      some ⟨typeValue model type, termValue model term⟩ :=
  represented_term_readout model term (chosenTerm term) (chosenTerm_class term)

theorem represented_extension {context : QuotientCwf.QContext D}
    (type : QuotientCwf.Ty context) :
    contextValue model (QuotientCwf.ext context type).as =
      (contextValue model context.as).snoc (typeValue model type) := by
  have annotation : rawType model (QuotientCwf.typeRepresentative type) =
      typeValue model type :=
    congrArg (typeValue model) (QuotientCwf.typeRepresentative_class type)
  exact (context_extension model context.as (QuotientCwf.typeRepresentative type)).trans
    (congrArg (Mettapedia.TypeTheory.ContextualPredicateModelScopes.Scope.snoc (contextValue model context.as)) annotation)

theorem represented_body_readout {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (body : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (B : C.toCwf.Ty (C.toCwf.ext (contextValue model context.as).1 (typeValue model domain)))
    (types : HEq (typeValue model body) B) :
    model.data.evaluateType ((contextValue model context.as).snoc (typeValue model domain))
      (QuotientCwf.typeRepresentative body).code = some B :=
  native_type_readout_transport model (represented_extension model domain) _ types
    (represented_type_readout model body)

theorem represented_body_term_readout {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) {body : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (term : QuotientCwf.Tm (QuotientCwf.ext context domain) body)
    (B : C.toCwf.Ty (C.toCwf.ext (contextValue model context.as).1 (typeValue model domain)))
    (types : HEq (typeValue model body) B)
    (value : C.toCwf.Tm (C.toCwf.ext (contextValue model context.as).1 (typeValue model domain)) B)
    (terms : HEq (termValue model term) value) :
    model.data.evaluateTerm ((contextValue model context.as).snoc (typeValue model domain))
      (chosenTerm term).code = some ⟨B, value⟩ :=
  native_term_readout_transport model (represented_extension model domain) _ types terms
    (chosen_term_readout model term)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation
