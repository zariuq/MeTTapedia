import Mettapedia.Languages.HOLLight.ExactFormulaReadback

/-! # Exact readback in a model of an arbitrary received cache

The cache may be extended without changing this interpretation theorem.
Source conclusions are interpreted at all type instances; a closed exact
reading then has the same denotation as its cached source formula.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.ExactReadbackCache

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ProofExecution

universe w

variable {state : Registered.State}
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (full : model.FullDomains)
  (equations : ∀ fact ∈ state.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)

include full equations in
theorem models {formula : HOL.ClosedFormula Symbol} (read : ExactFormulaReadback.ReadFact state formula) :
    model.models formula := by
  obtain ⟨actual, translated, holds⟩ := equations read.fact read.known TypeSubst.empty
  rw [TermSubst.typeInstance_identity] at translated
  let empty : model.Valuation [] := fun index => nomatch index
  have atEmpty (term : HOL.ClosedFormula Symbol) : model.models term = (model.denote term empty).down := by
    unfold HOL.HenkinModel.models HOL.PreModel.models
    exact congrArg ULift.down (model.denote_closed_valuation_eq _ _ _)
  have same := read.translated.denote_eq_compositional translated model full empty
  exact (atEmpty formula).mpr ((congrArg ULift.down same).mpr ((atEmpty actual).mp holds))

include full equations in
theorem definition_value {type : HOL.Ty AtomicTy} (symbol : Symbol type) (body : HOL.ClosedTerm Symbol type)
    (read : ExactFormulaReadback.ReadFact state (.eq (.const symbol) body)) :
    model.constDen symbol = model.denote body (fun index => nomatch index) := by
  have interpreted := models model full equations read
  change model.Eqv type _ _ at interpreted
  have same := (model.eqv_iff_eq_of_fullDomains full _ _).mp interpreted
  exact same.trans (model.denote_closed_valuation_eq body _ _)

#print axioms models
#print axioms definition_value

end Mettapedia.Languages.HOLLight.ExactReadbackCache
