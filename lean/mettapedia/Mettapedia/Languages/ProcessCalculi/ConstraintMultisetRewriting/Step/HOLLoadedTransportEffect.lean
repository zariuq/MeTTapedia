import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLTransportEffectBody
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedReadback

/-! # Interpretation of the received transported-equation profile

The historical source name is tc_prepared_effect. Its defining equation is
checked independently; general prepared effects use tc_semantic_effect.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedTransportEffect

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody hiding body
open HOLTransportEffectBody HOLOccurrenceCoding

theorem constant_available :
    (List.lookup "tc_prepared_effect" HOLSemanticDefinitions.received.symbols.constants).isSome = true := by decide +kernel

@[irreducible] def constant : Const :=
  (List.lookup "tc_prepared_effect" HOLSemanticDefinitions.received.symbols.constants).get constant_available

def symbol : Symbol predicateType := .constant constant (Ty.fromHOL predicateType) (Ty.toHOL_fromHOL predicateType)
def definition : HOL.ClosedFormula Symbol := .eq (.const symbol) body

theorem definition_readable :
    (ExactFormulaReadback.read? HOLSemanticDefinitions.received.received.registered 16 definition).isSome = true := by
  decide +kernel

@[irreducible] def readDefinition : ExactFormulaReadback.ReadFact HOLSemanticDefinitions.received.received.registered definition :=
  (ExactFormulaReadback.read? HOLSemanticDefinitions.received.received.registered 16 definition).get definition_readable

universe w

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLSemanticDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)

include full equations in
theorem constant_value : model.constDen symbol = model.denote body (fun index => nomatch index) :=
  HOLLoadedReadback.definition_value model full equations symbol body readDefinition

include full equations in
theorem operational_meaning (terms : HOL.Ty.denote.{0,w+1} model.Carrier HOLStoreBody.termsType)
    (hom : HOL.Ty.denote.{0,w+1} model.Carrier homType) (act : HOL.Ty.denote.{0,w+1} model.Carrier actionType)
    (a m b : HOL.Ty.denote.{0,w+1} model.Carrier objectType)
    (extension settle : HOL.Ty.denote.{0,w+1} model.Carrier mapType)
    (old information next : HOL.Ty.denote.{0,w+1} model.Carrier storeType)
    (present taken read made after : HOL.Ty.denote.{0,w+1} model.Carrier setType) :
    model.constDen symbol terms hom act a m b extension settle old information next present taken read made after =
      ULift.up (Contract model terms hom act a m b extension settle old information next present taken made after) := by
  rw [constant_value model full equations]
  exact denote_body model full (HOLLoadedBooleans.meanings_of_cache model equations full)
    terms hom act a m b extension settle old information next present taken read made after

#print axioms definition_readable
#print axioms operational_meaning

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedTransportEffect
