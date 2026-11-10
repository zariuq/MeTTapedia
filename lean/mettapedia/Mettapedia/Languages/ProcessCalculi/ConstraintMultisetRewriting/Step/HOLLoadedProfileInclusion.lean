import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmissionDefinitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmissionProfileBodies
import Mettapedia.Languages.HOLLight.ExactReadbackCache

/-! # Exact interpretation of the received tc_profile_inclusion definition -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedProfileInclusion

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLAdmissionTypes HOLAdmissionProfileBodies.Inclusion

theorem constant_available :
    (List.lookup "tc_profile_inclusion" HOLAdmissionDefinitions.received.symbols.constants).isSome = true := by decide +kernel

@[irreducible] def constant : Const :=
  (List.lookup "tc_profile_inclusion" HOLAdmissionDefinitions.received.symbols.constants).get constant_available

def symbol : Symbol inclusionType := .constant constant (Ty.fromHOL inclusionType) (Ty.toHOL_fromHOL inclusionType)
def definition : HOL.ClosedFormula Symbol := .eq (.const symbol) body

theorem definition_readable :
    (ExactFormulaReadback.read? HOLAdmissionDefinitions.received.received.registered 23 definition).isSome = true := by decide +kernel

@[irreducible] def readDefinition : ExactFormulaReadback.ReadFact HOLAdmissionDefinitions.received.received.registered definition :=
  (ExactFormulaReadback.read? HOLAdmissionDefinitions.received.received.registered 23 definition).get definition_readable

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
theorem operational_meaning (preparation first second : HOL.Ty.denote.{0,w+1} model.Carrier preparationType) :
    model.constDen symbol preparation first second = ULift.up (∀ s f p, (preparation s f p).down → (first s f p).down → (second s f p).down) := by
  rw [constant_value model full equations]
  exact denote_body model full
    (HOLLoadedBooleans.meanings_of_cache model (HOLAdmissionDefinitions.earlier_equations model equations) full)
    preparation first second

#print axioms definition_readable
#print axioms operational_meaning

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedProfileInclusion
