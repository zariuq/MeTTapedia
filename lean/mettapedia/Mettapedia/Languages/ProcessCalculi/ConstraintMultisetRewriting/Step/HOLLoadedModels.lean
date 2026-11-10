import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLModelsBody
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedReadback

/-! # Meaning of the actual loaded tc_models definition

The independent typed body must pass exact readback against the received
defining equation. Its denotation then follows from the constructed cache
model and the Boolean meanings earned from that same cache.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedModels

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody
open StandardTheoryInterpretation.Interpretation

theorem constant_available :
    (List.lookup "tc_models" HOLSemanticDefinitions.received.symbols.constants).isSome = true := by
  decide +kernel

@[irreducible] def constant : Const :=
  (List.lookup "tc_models" HOLSemanticDefinitions.received.symbols.constants).get constant_available

def symbol : Symbol modelsType :=
  .constant constant (Ty.fromHOL modelsType) (Ty.toHOL_fromHOL modelsType)

def definition : HOL.ClosedFormula Symbol := .eq (.const symbol) body

theorem definition_readable :
    (ExactFormulaReadback.read? HOLSemanticDefinitions.received.received.registered 11 definition).isSome = true := by
  decide +kernel

@[irreducible] def readDefinition : ExactFormulaReadback.ReadFact HOLSemanticDefinitions.received.received.registered definition :=
  (ExactFormulaReadback.read? HOLSemanticDefinitions.received.received.registered 11 definition).get definition_readable

universe w

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLSemanticDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧
      model.models formula)

include full equations in
theorem constant_value : model.constDen symbol = model.denote body (fun index => nomatch index) :=
  HOLLoadedReadback.definition_value model full equations symbol body readDefinition

include full equations in
theorem operational_meaning
    (hom : HOL.Ty.denote model.Carrier homType) (equal : HOL.Ty.denote model.Carrier equalType)
    (act : HOL.Ty.denote model.Carrier actionType)
    (a b : HOL.Ty.denote model.Carrier objectType) (map : HOL.Ty.denote model.Carrier mapType)
    (store : HOL.Ty.denote model.Carrier storeType) :
    model.constDen symbol hom equal act a b map store =
      ULift.up ((hom a b map).down ∧ ∀ x y, (store x y).down → (equal b (act map x) (act map y)).down) := by
  rw [constant_value model full equations]
  exact denote_body model full (HOLLoadedBooleans.meanings_of_cache model equations full) hom equal act a b map store

namespace Controls

/-- The two frame arguments have the same type. A sort check alone cannot
detect this permutation; exact source readback must refuse it. -/
def swappedHom : HOL.Term Symbol arguments .prop :=
  .app (.app (.app (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
    (.var (.vs (.vs .vz)))) (.var (.vs (.vs (.vs .vz))))) (.var (.vs .vz))

def swappedBody : HOL.ClosedTerm Symbol modelsType :=
  .lam (.lam (.lam (.lam (.lam (.lam (.lam
    (.app (.app (.const Symbols.conjunction) swappedHom) allEquations)))))))

theorem same_sort_argument_swap_refused :
    ExactFormulaReadback.read? HOLSemanticDefinitions.received.received.registered 11
      (.eq (.const symbol) swappedBody) = none := by
  decide +kernel

end Controls

#print axioms definition_readable
#print axioms operational_meaning
#print axioms Controls.same_sort_argument_swap_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedModels
