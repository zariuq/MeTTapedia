import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualLogicalMorphism
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualPredicateMorphism
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractSoundnessLogic

/-!
# Retained refinement comparisons of contextual interpretation

The interpreted refinement family, introduction and forgetting operation are
compared with the independently supplied target operations. The guard follows
the actual contextual section square and semantic predicate substitution.
The complete supplied inhabitant survives the comparison.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open QuotientComprehensionSyntax
open Refinement.Abstract

universe u c s t m p
variable {S : Symbols.{u}} {D : Signature S} {C : CwfWithTerminal.{c,s,t,m}}
variable (model : QualifiedModel.{u,c,s,t,m,p} D C)

theorem predicate_reindex_heq {source target source' target' : C.toCwf.Ctx}
    (sources : source = source') (targets : target = target')
    {predicate : model.localModel.doctrine.Predicate target}
    {predicate' : model.localModel.doctrine.Predicate target'} (predicates : HEq predicate predicate')
    {substitution : C.toCwf.Sub source target} {substitution' : C.toCwf.Sub source' target'}
    (substitutions : HEq substitution substitution') :
    HEq (model.localModel.doctrine.reindex substitution predicate)
      (model.localModel.doctrine.reindex substitution' predicate') := by
  cases sources
  cases targets
  cases eq_of_heq predicates
  cases eq_of_heq substitutions
  rfl

theorem refinement_type_value {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context) (body : QPredicate (QuotientCwf.ext context domain).as)
    (predicate : model.localModel.doctrine.Predicate
      (C.toCwf.ext (contextValue model context.as).1 (typeValue model domain)))
    (predicates : HEq (predicateValue model body) predicate) :
    typeValue model (Refinements.type domain body) =
      model.localModel.refinements.refined (typeValue model domain) predicate := by
  have computed := model.data.evaluate_comprehension (contextValue model context.as)
    (QuotientCwf.typeRepresentative domain).code (RefinementValues.predicateRepresentative body).code
    (typeValue model domain) predicate (represented_type_readout model domain)
    (represented_predicate_body_readout model domain body predicate predicates)
  exact (congrArg (typeValue model) (RefinementValues.typeRepresentative_class body)).symm.trans
    (Option.some.inj ((type_readout model (RefinementValues.typeRepresentative body)).symm.trans computed))

theorem refinement_guard_value {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context} (body : QPredicate (QuotientCwf.ext context domain).as)
    (argument : QuotientCwf.Tm context domain)
    (predicate : model.localModel.doctrine.Predicate
      (C.toCwf.ext (contextValue model context.as).1 (typeValue model domain)))
    (predicates : HEq (predicateValue model body) predicate)
    (value : C.toCwf.Tm (contextValue model context.as).1 (typeValue model domain))
    (arguments : HEq (termValue model argument) value) :
    predicateValue model (RefinementValues.guard body argument) =
      model.localModel.doctrine.reindex (selfExtend C.toCwf value) predicate :=
  (predicate_substitution model body (selfExtend (QuotientCwf.cwf D) argument)).trans
    (eq_of_heq (predicate_reindex_heq model rfl
      (congrArg Sigma.fst (represented_extension model domain)) predicates
      (section_value model argument value arguments)))

theorem refinement_guard_preserved {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context} (body : QPredicate (QuotientCwf.ext context domain).as)
    (argument : QuotientCwf.Tm context domain)
    (predicate : model.localModel.doctrine.Predicate
      (C.toCwf.ext (contextValue model context.as).1 (typeValue model domain)))
    (predicates : HEq (predicateValue model body) predicate)
    (value : C.toCwf.Tm (contextValue model context.as).1 (typeValue model domain))
    (arguments : HEq (termValue model argument) value)
    (evidence : RefinementValues.guard body argument = ⊤) :
    model.localModel.doctrine.reindex (selfExtend C.toCwf value) predicate = ⊤ :=
  (refinement_guard_value model body argument predicate predicates value arguments).symm.trans
    ((congrArg (predicateValue model) evidence).trans (predicateValue_top model context.as))

theorem refinement_introduction_value {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context} (body : QPredicate (QuotientCwf.ext context domain).as)
    (argument : QuotientCwf.Tm context domain)
    (predicate : model.localModel.doctrine.Predicate
      (C.toCwf.ext (contextValue model context.as).1 (typeValue model domain)))
    (predicates : HEq (predicateValue model body) predicate)
    (value : C.toCwf.Tm (contextValue model context.as).1 (typeValue model domain))
    (arguments : HEq (termValue model argument) value)
    (evidence : RefinementValues.guard body argument = ⊤) :
    HEq (termValue model (RefinementValues.intro_of_top body argument evidence))
      (model.localModel.refinements.intro (typeValue model domain) predicate value
        (refinement_guard_preserved model body argument predicate predicates value arguments evidence)) := by
  have termRead := native_term_readout_transport model rfl (chosenTerm argument).code HEq.rfl arguments
    (chosen_term_readout model argument)
  have computed := model.data.evaluate_refine (contextValue model context.as)
    (QuotientCwf.typeRepresentative domain).code (RefinementValues.predicateRepresentative body).code
    (chosenTerm argument).code (typeValue model domain) predicate value
    (represented_type_readout model domain)
    (represented_predicate_body_readout model domain body predicate predicates) termRead
    (refinement_guard_preserved model body argument predicate predicates value arguments evidence)
  have actual := represented_term_readout model (RefinementValues.intro_of_top body argument evidence)
    (Refinements.rawIntro (RefinementValues.predicateRepresentative body) (chosenTerm argument)
      (RefinementValues.raw_guard body argument ((Logic.entails_iff_eq_top _).mpr evidence))) rfl
  exact (Sigma.mk.inj (Option.some.inj (actual.symm.trans computed))).2

theorem refinement_forgetting_value {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context} (body : QPredicate (QuotientCwf.ext context domain).as)
    (term : QuotientCwf.Tm context (Refinements.type domain body))
    (predicate : model.localModel.doctrine.Predicate
      (C.toCwf.ext (contextValue model context.as).1 (typeValue model domain)))
    (predicates : HEq (predicateValue model body) predicate)
    (value : C.toCwf.Tm (contextValue model context.as).1
      (model.localModel.refinements.refined (typeValue model domain) predicate))
    (terms : HEq (termValue model term) value) :
    HEq (termValue model (RefinementValues.forget body term))
      (model.localModel.refinements.forget (typeValue model domain) predicate value) := by
  have termRead := native_term_readout_transport model rfl
    (RefinementValues.refinementTermRepresentative body term).code
    (heq_of_eq (refinement_type_value model domain body predicate predicates)) terms
    (represented_term_readout model term (RefinementValues.refinementTermRepresentative body term)
      (RefinementValues.refinementTermRepresentative_class body term))
  have computed := model.data.evaluate_forget (contextValue model context.as)
    (QuotientCwf.typeRepresentative domain).code (RefinementValues.predicateRepresentative body).code
    (RefinementValues.refinementTermRepresentative body term).code (typeValue model domain) predicate value
    (represented_type_readout model domain)
    (represented_predicate_body_readout model domain body predicate predicates) termRead
  have actual := represented_term_readout model (RefinementValues.forget body term)
    (Refinements.rawForget (RefinementValues.refinementTermRepresentative body term)) rfl
  exact (Sigma.mk.inj (Option.some.inj (actual.symm.trans computed))).2

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation
