import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLModelsSpecialization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLIndexedQuantifiers

/-! # Solution pullback through encoded frame morphisms

The universal quantifiers range over the full raw HOL carriers. A solution
supplies the validity evidence needed to recover an actual indexed future
map; invalid representatives introduce no extra solutions or obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLKnowledgePullback

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody HOLFrameCoding HOLFramesCoding HOLIndexedQuantifiers

universe w uO uT uH

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (X : Frames Tm Hom) (code : Coding model Obj Tm Hom)
  (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLSemanticDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)

include full equations in
theorem models_valid (a : Obj) (b : HOL.Ty.denote.{0,w+1} model.Carrier objectType)
    (sigma : HOL.Ty.denote.{0,w+1} model.Carrier mapType) (store : EquationStore (Tm a))
    (solves : (model.constDen HOLLoadedModels.symbol (homValue model code) (equalValue model X code)
      (actionValue model X code) (code.objects.symm (some a)) b sigma (storeValue model code store)).down) :
    (homValue model code (code.objects.symm (some a)) b sigma).down := by
  have evaluated := HOLLoadedModels.operational_meaning model full equations
    (homValue model code) (equalValue model X code) (actionValue model X code)
    (code.objects.symm (some a)) b sigma (storeValue model code store)
  exact ((iff_of_eq (congrArg ULift.down evaluated)).mp solves).1

include full equations in
theorem pullback_iff {a b : Obj} (map : Hom a b)
    (old : EquationStore (Tm a)) (next : EquationStore (Tm b)) :
    (∀ c sigma,
      (model.constDen HOLLoadedModels.symbol (homValue model code) (equalValue model X code)
        (actionValue model X code) (code.objects.symm (some b)) c sigma (storeValue model code next)).down →
      (model.constDen HOLLoadedModels.symbol (homValue model code) (equalValue model X code)
        (actionValue model X code) (code.objects.symm (some a)) c
        (compositionValue model X code sigma (code.morphisms.symm (HOLFrameEncoding.encodeHom map)))
        (storeValue model code old)).down) ↔
      ∀ (c : Obj) (sigma : Hom b c), X.Models sigma next → X.Models (X.comp sigma map) old := by
  constructor
  · intro pulls c sigma solves
    have answer := pulls (code.objects.symm (some c)) (code.morphisms.symm (HOLFrameEncoding.encodeHom sigma))
      ((HOLModelsSpecialization.models_iff model X code full equations sigma next).mpr solves)
    rw [composition_encoded] at answer
    exact (HOLModelsSpecialization.models_iff model X code full equations (X.comp sigma map) old).mp answer
  · intro pulls c sigma solves
    obtain ⟨target, typed, targetEq, mapEq⟩ := valid_map_values model code c sigma
      (models_valid model X code full equations b c sigma next solves)
    rw [targetEq, mapEq] at solves ⊢
    rw [composition_encoded]
    exact (HOLModelsSpecialization.models_iff model X code full equations (X.comp typed map) old).mpr
      (pulls target typed ((HOLModelsSpecialization.models_iff model X code full equations typed next).mp solves))

#print axioms models_valid
#print axioms pullback_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLKnowledgePullback
