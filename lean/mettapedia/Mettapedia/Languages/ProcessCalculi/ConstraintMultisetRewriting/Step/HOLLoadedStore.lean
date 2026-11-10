import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLStoreBody
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedReadback

/-! # The actual loaded store-typing predicate

An independently authored named body is checked by the existing typed
elaborator, then compared with the received tc_store defining equation.
Its denotation retains both endpoints of every stored equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedStore

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody hiding body
open HOLStoreBody
open StandardTheoryInterpretation.Interpretation

theorem constant_available :
    (List.lookup "tc_store" HOLSemanticDefinitions.received.symbols.constants).isSome = true := by decide +kernel

@[irreducible] def constant : Const :=
  (List.lookup "tc_store" HOLSemanticDefinitions.received.symbols.constants).get constant_available

def symbol : Symbol predicateType := .constant constant (Ty.fromHOL predicateType) (Ty.toHOL_fromHOL predicateType)
def definition : HOL.ClosedFormula Symbol := .eq (.const symbol) body

theorem definition_readable :
    (ExactFormulaReadback.read? HOLSemanticDefinitions.received.received.registered 15 definition).isSome = true := by
  decide +kernel

@[irreducible] def readDefinition : ExactFormulaReadback.ReadFact HOLSemanticDefinitions.received.received.registered definition :=
  (ExactFormulaReadback.read? HOLSemanticDefinitions.received.received.registered 15 definition).get definition_readable

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
theorem operational_meaning (terms : HOL.Ty.denote model.Carrier termsType)
    (a : HOL.Ty.denote model.Carrier objectType) (store : HOL.Ty.denote model.Carrier storeType) :
    model.constDen symbol terms a store =
      ULift.up (∀ x y, (store x y).down → (terms a x).down ∧ (terms a y).down) := by
  rw [constant_value model full equations]
  exact denote_body model full (HOLLoadedBooleans.meanings_of_cache model equations full) terms a store

#print axioms body_typed
#print axioms definition_readable
#print axioms operational_meaning

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedStore
