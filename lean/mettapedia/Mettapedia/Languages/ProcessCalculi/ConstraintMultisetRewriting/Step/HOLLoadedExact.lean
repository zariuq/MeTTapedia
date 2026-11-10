import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLExactBody
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedReadback

/-! # Exact meaning of the loaded optional knowledge predicate

The received tc_exact_knowledge equation must match the independent typed
body, including the validity guard and composition order.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedExact

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody hiding body
open HOLExactBody

theorem constant_available :
    (List.lookup "tc_exact_knowledge" HOLSemanticDefinitions.received.symbols.constants).isSome = true := by decide +kernel

@[irreducible] def constant : Const :=
  (List.lookup "tc_exact_knowledge" HOLSemanticDefinitions.received.symbols.constants).get constant_available

def symbol : Symbol predicateType := .constant constant (Ty.fromHOL predicateType) (Ty.toHOL_fromHOL predicateType)
def definition : HOL.ClosedFormula Symbol := .eq (.const symbol) body

theorem definition_readable :
    (ExactFormulaReadback.read? HOLSemanticDefinitions.received.received.registered 18 definition).isSome = true := by
  decide +kernel

@[irreducible] def readDefinition : ExactFormulaReadback.ReadFact HOLSemanticDefinitions.received.received.registered definition :=
  (ExactFormulaReadback.read? HOLSemanticDefinitions.received.received.registered 18 definition).get definition_readable

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
theorem operational_meaning (hom : HOL.Ty.denote.{0,w+1} model.Carrier homType)
    (equal : HOL.Ty.denote.{0,w+1} model.Carrier equalType)
    (act : HOL.Ty.denote.{0,w+1} model.Carrier actionType)
    (comp : HOL.Ty.denote.{0,w+1} model.Carrier HOLFramesBody.compositionType)
    (m b : HOL.Ty.denote.{0,w+1} model.Carrier objectType)
    (settle : HOL.Ty.denote.{0,w+1} model.Carrier mapType)
    (information next : HOL.Ty.denote.{0,w+1} model.Carrier storeType) :
    model.constDen symbol hom equal act comp m b settle information next =
      ULift.up (∀ c sigma, (hom b c sigma).down ∧
        (model.constDen HOLLoadedModels.symbol hom equal act m c (comp sigma settle) information).down →
        (model.constDen HOLLoadedModels.symbol hom equal act b c sigma next).down) := by
  rw [constant_value model full equations]
  exact denote_body model full (HOLLoadedBooleans.meanings_of_cache model equations full)
    hom equal act comp m b settle information next

#print axioms definition_readable
#print axioms operational_meaning

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedExact
