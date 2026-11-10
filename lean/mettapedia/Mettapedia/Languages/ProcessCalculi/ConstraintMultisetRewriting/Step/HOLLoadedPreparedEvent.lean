import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmissionDefinitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLPreparedEventBody
import Mettapedia.Languages.HOLLight.ExactReadbackCache

/-! # Exact interpretation of the loaded prepared-event predicate -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedPreparedEvent

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLAdmissionTypes HOLPreparedEventBody

theorem constant_available :
    (List.lookup "tc_prepared_event" HOLAdmissionDefinitions.received.symbols.constants).isSome = true := by decide +kernel

@[irreducible] def constant : Const :=
  (List.lookup "tc_prepared_event" HOLAdmissionDefinitions.received.symbols.constants).get constant_available

def symbol : Symbol preparedEventType := .constant constant (Ty.fromHOL preparedEventType) (Ty.toHOL_fromHOL preparedEventType)
def definition : HOL.ClosedFormula Symbol := .eq (.const symbol) body

theorem definition_readable :
    (ExactFormulaReadback.read? HOLAdmissionDefinitions.received.received.registered 19 definition).isSome = true := by decide +kernel

@[irreducible] def readDefinition : ExactFormulaReadback.ReadFact HOLAdmissionDefinitions.received.received.registered definition :=
  (ExactFormulaReadback.read? HOLAdmissionDefinitions.received.received.registered 19 definition).get definition_readable

universe w

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLAdmissionDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)

include full equations in
theorem constant_value : model.constDen symbol = model.denote body (fun index => nomatch index) :=
  ExactReadbackCache.definition_value model full equations symbol body readDefinition

include full equations in
theorem operational_meaning (preparation : HOL.Ty.denote.{0,w+1} model.Carrier preparationType)
    (result : HOL.Ty.denote.{0,w+1} model.Carrier resultType)
    (s t : HOL.Ty.denote.{0,w+1} model.Carrier stateType)
    (f : HOL.Ty.denote.{0,w+1} model.Carrier firingType)
    (p : HOL.Ty.denote.{0,w+1} model.Carrier witnessType) :
    model.constDen symbol preparation result s f p t = ULift.up ((preparation s f p).down ∧ t = result s f p) := by
  rw [constant_value model full equations]
  exact denote_body model full
    (HOLLoadedBooleans.meanings_of_cache model (HOLAdmissionDefinitions.earlier_equations model equations) full)
    preparation result s t f p

#print axioms definition_readable
#print axioms operational_meaning

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedPreparedEvent
