import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFramesBody
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedReadback

/-! # Exact meaning of the loaded frame-law predicate

The real cached tc_frames equation is read against the independent typed
eleven-clause body. The resulting value theorem requires the cache's actual
defining equations, not a supplied claim about a constant's printed name.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedFrames

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody hiding body
open HOLFramesBody

theorem constant_available :
    (List.lookup "tc_frames" HOLSemanticDefinitions.received.symbols.constants).isSome = true := by decide +kernel

@[irreducible] def constant : Const :=
  (List.lookup "tc_frames" HOLSemanticDefinitions.received.symbols.constants).get constant_available

def symbol : Symbol predicateType := .constant constant (Ty.fromHOL predicateType) (Ty.toHOL_fromHOL predicateType)
def definition : HOL.ClosedFormula Symbol := .eq (.const symbol) body

theorem definition_readable :
    (ExactFormulaReadback.read? HOLSemanticDefinitions.received.received.registered 14 definition).isSome = true := by
  decide +kernel

@[irreducible] def readDefinition : ExactFormulaReadback.ReadFact HOLSemanticDefinitions.received.received.registered definition :=
  (ExactFormulaReadback.read? HOLSemanticDefinitions.received.received.registered 14 definition).get definition_readable

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
theorem operational_meaning (objects : HOL.Ty.denote.{0,w+1} model.Carrier objectsType)
    (terms : HOL.Ty.denote.{0,w+1} model.Carrier HOLStoreBody.termsType)
    (hom : HOL.Ty.denote.{0,w+1} model.Carrier homType) (equal : HOL.Ty.denote.{0,w+1} model.Carrier equalType)
    (act : HOL.Ty.denote.{0,w+1} model.Carrier actionType) (identity : HOL.Ty.denote.{0,w+1} model.Carrier identityType)
    (comp : HOL.Ty.denote.{0,w+1} model.Carrier compositionType) :
    model.constDen symbol objects terms hom equal act identity comp =
      ULift.up (Laws model objects terms hom equal act identity comp) := by
  rw [constant_value model full equations]
  exact denote_body model full (HOLLoadedBooleans.meanings_of_cache model equations full)
    objects terms hom equal act identity comp

#print axioms definition_readable
#print axioms operational_meaning

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedFrames
