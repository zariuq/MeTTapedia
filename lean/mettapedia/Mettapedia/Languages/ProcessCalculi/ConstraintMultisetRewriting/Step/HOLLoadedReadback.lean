import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedBooleans
import Mettapedia.Languages.HOLLight.ExactReadbackCache

/-! # Exact readings in a model of the actual definition cache

These laws connect the existing exact formula reader to the constructed
all-instance cache interpretation. They do not inspect the spelling or
implementation of the symbol whose defining equation was read.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedReadback

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight

universe w

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLSemanticDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧
      model.models formula)

include full equations in
theorem models {formula : HOL.ClosedFormula Symbol}
    (read : ExactFormulaReadback.ReadFact HOLSemanticDefinitions.received.received.registered formula) :
    model.models formula :=
  ExactReadbackCache.models model full equations read

include full equations in
theorem definition_value {type : HOL.Ty AtomicTy} (symbol : Symbol type) (body : HOL.ClosedTerm Symbol type)
    (read : ExactFormulaReadback.ReadFact HOLSemanticDefinitions.received.received.registered
      (.eq (.const symbol) body)) :
    model.constDen symbol = model.denote body (fun index => nomatch index) :=
  ExactReadbackCache.definition_value model full equations symbol body read

#print axioms models
#print axioms definition_value

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedReadback
