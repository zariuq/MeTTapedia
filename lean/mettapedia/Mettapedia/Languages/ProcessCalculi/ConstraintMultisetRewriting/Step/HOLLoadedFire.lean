import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFireBody
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedReadback

/-! # Meaning of the actual loaded occurrence-update definition -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedFire

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLFireBody HOLOccurrenceCoding

theorem constant_available :
    (List.lookup "tc_fire" HOLSemanticDefinitions.received.symbols.constants).isSome = true := by decide +kernel

@[irreducible] def constant : Const :=
  (List.lookup "tc_fire" HOLSemanticDefinitions.received.symbols.constants).get constant_available

def symbol : Symbol predicateType := .constant constant (Ty.fromHOL predicateType) (Ty.toHOL_fromHOL predicateType)
def definition : HOL.ClosedFormula Symbol := .eq (.const symbol) body

theorem definition_readable :
    (ExactFormulaReadback.read? HOLSemanticDefinitions.received.received.registered 10 definition).isSome = true := by
  decide +kernel

@[irreducible] def readDefinition : ExactFormulaReadback.ReadFact HOLSemanticDefinitions.received.received.registered definition :=
  (ExactFormulaReadback.read? HOLSemanticDefinitions.received.received.registered 10 definition).get definition_readable

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
theorem operational_meaning (present taken made : HOL.Ty.denote.{0,w+1} model.Carrier setType)
    (occ : HOL.Ty.denote.{0,w+1} model.Carrier occurrenceType) :
    model.constDen symbol present taken made occ =
      ULift.up (((present occ).down ∧ ¬(taken occ).down) ∨ (made occ).down) := by
  rw [constant_value model full equations]
  exact denote_body model full equations present taken made occ

#print axioms definition_readable
#print axioms operational_meaning

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedFire
