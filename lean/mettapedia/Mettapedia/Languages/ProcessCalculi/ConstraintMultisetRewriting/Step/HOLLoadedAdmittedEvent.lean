import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedPreparedEvent
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmittedEventBody

/-! # Exact interpretation of the loaded admitted-event predicate

The body calls the actual prepared-event constant and conjoins the supplied
permission. No guard-based default is substituted for that permission.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedAdmittedEvent

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLAdmissionTypes

theorem constant_available :
    (List.lookup "tc_admitted_event" HOLAdmissionDefinitions.received.symbols.constants).isSome = true := by decide +kernel

@[irreducible] def constant : Const :=
  (List.lookup "tc_admitted_event" HOLAdmissionDefinitions.received.symbols.constants).get constant_available

def symbol : Symbol admittedEventType := .constant constant (Ty.fromHOL admittedEventType) (Ty.toHOL_fromHOL admittedEventType)
def body : HOL.ClosedTerm Symbol admittedEventType := HOLAdmittedEventBody.body HOLLoadedPreparedEvent.symbol
def definition : HOL.ClosedFormula Symbol := .eq (.const symbol) body

theorem definition_readable :
    (ExactFormulaReadback.read? HOLAdmissionDefinitions.received.received.registered 20 definition).isSome = true := by decide +kernel

@[irreducible] def readDefinition : ExactFormulaReadback.ReadFact HOLAdmissionDefinitions.received.received.registered definition :=
  (ExactFormulaReadback.read? HOLAdmissionDefinitions.received.received.registered 20 definition).get definition_readable

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
theorem operational_meaning (preparation allow : HOL.Ty.denote.{0,w+1} model.Carrier preparationType)
    (result : HOL.Ty.denote.{0,w+1} model.Carrier resultType)
    (s t : HOL.Ty.denote.{0,w+1} model.Carrier stateType)
    (f : HOL.Ty.denote.{0,w+1} model.Carrier firingType)
    (p : HOL.Ty.denote.{0,w+1} model.Carrier witnessType) :
    model.constDen symbol preparation result allow s f p t =
      ULift.up ((preparation s f p).down ∧ t = result s f p ∧ (allow s f p).down) := by
  have interpreted := HOLAdmittedEventBody.denote_body model
    (HOLLoadedBooleans.meanings_of_cache model (HOLAdmissionDefinitions.earlier_equations model equations) full)
    HOLLoadedPreparedEvent.symbol preparation allow result s t f p
  have preparedMeaning := HOLLoadedPreparedEvent.operational_meaning model full equations preparation result s t f p
  rw [constant_value model full equations]
  refine interpreted.trans ?_
  apply ULift.ext
  apply propext
  rw [congrArg ULift.down preparedMeaning, and_assoc]

#print axioms definition_readable
#print axioms operational_meaning

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedAdmittedEvent
