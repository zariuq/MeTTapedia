import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmissionDefinitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLAdmissionProfileBodies
import Mettapedia.Languages.HOLLight.ExactReadbackCache

/-! # Exact interpretation of the received tc_solution_preparation definition -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedSolutionPreparation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLAdmissionTypes HOLAdmissionProfileBodies.SolutionPreparation

theorem constant_available :
    (List.lookup "tc_solution_preparation" HOLAdmissionDefinitions.received.symbols.constants).isSome = true := by decide +kernel

@[irreducible] def constant : Const :=
  (List.lookup "tc_solution_preparation" HOLAdmissionDefinitions.received.symbols.constants).get constant_available

def symbol : Symbol solutionPreparationType := .constant constant (Ty.fromHOL solutionPreparationType) (Ty.toHOL_fromHOL solutionPreparationType)
def definition : HOL.ClosedFormula Symbol := .eq (.const symbol) body

theorem definition_readable :
    (ExactFormulaReadback.read? HOLAdmissionDefinitions.received.received.registered 21 definition).isSome = true := by decide +kernel

@[irreducible] def readDefinition : ExactFormulaReadback.ReadFact HOLAdmissionDefinitions.received.received.registered definition :=
  (ExactFormulaReadback.read? HOLAdmissionDefinitions.received.received.registered 21 definition).get definition_readable

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
theorem operational_meaning (ready : HOL.Ty.denote.{0,w+1} model.Carrier readyType)
    (solution : HOL.Ty.denote.{0,w+1} model.Carrier solutionsType)
    (witness : HOL.Ty.denote.{0,w+1} model.Carrier preparationType)
    (s : HOL.Ty.denote.{0,w+1} model.Carrier stateType)
    (f : HOL.Ty.denote.{0,w+1} model.Carrier firingType)
    (p : HOL.Ty.denote.{0,w+1} model.Carrier witnessType) :
    model.constDen symbol ready solution witness s f p = ULift.up ((ready s f).down ∧ (∃ v, (solution s f v).down) ∧ (witness s f p).down) := by
  rw [constant_value model full equations]
  exact denote_body model full
    (HOLLoadedBooleans.meanings_of_cache model (HOLAdmissionDefinitions.earlier_equations model equations) full)
    ready solution witness s f p

#print axioms definition_readable
#print axioms operational_meaning

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedSolutionPreparation
