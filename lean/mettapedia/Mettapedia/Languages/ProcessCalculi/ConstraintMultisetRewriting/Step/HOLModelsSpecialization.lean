import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFrameCoding

/-! # The loaded solution predicate agrees with indexed Lean frames

Carrier equivalences transport the encoded predicates and action into the
actual HOL model. The parameter assignment constructs these equivalences;
they are not assumed to exist for arbitrary unrelated models.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLModelsSpecialization

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody HOLFrameCoding

universe w uO uT uH uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (X : Frames Tm Hom) (code : Coding model Obj Tm Hom)

theorem models_raw_iff (full : model.FullDomains)
    (equations : ∀ fact ∈ HOLSemanticDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
      ∃ formula : HOL.ClosedFormula Symbol,
        TranslatesCompositionally []
          ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)
    (a b : HOLFrameEncoding.Objects Obj) (map : HOLFrameEncoding.Morphisms Hom)
    (store : HOLFrameEncoding.Terms Tm → HOLFrameEncoding.Terms Tm → Prop) :
    (model.constDen HOLLoadedModels.symbol (homValue model code) (equalValue model X code)
      (actionValue model X code) (code.objects.symm a) (code.objects.symm b)
      (code.morphisms.symm map) (predicateValue model code store)).down ↔
      HOLFrameEncoding.models X a b map store := by
  rw [HOLLoadedModels.constant_value model full equations]
  exact HOLFrameCoding.body_models_raw_iff model X code full
    (HOLLoadedBooleans.meanings_of_cache model equations full) a b map store

theorem models_iff (full : model.FullDomains)
    (equations : ∀ fact ∈ HOLSemanticDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
      ∃ formula : HOL.ClosedFormula Symbol,
        TranslatesCompositionally []
          ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)
    {a b : Obj} (map : Hom a b) (store : EquationStore (Tm a)) :
    (model.constDen HOLLoadedModels.symbol (homValue model code) (equalValue model X code)
      (actionValue model X code) (code.objects.symm (some a)) (code.objects.symm (some b))
      (code.morphisms.symm (HOLFrameEncoding.encodeHom map)) (storeValue model code store)).down ↔
      X.Models map store := by
  rw [HOLLoadedModels.constant_value model full equations]
  exact HOLFrameCoding.body_models_iff model X code full
    (HOLLoadedBooleans.meanings_of_cache model equations full) map store

theorem loaded_model_agrees (O : Type uOcc)
    (other : TypeFamilySemantics.OperatorFamilies.{max uO uT uH uOcc})
    (prior : TypeFamilySemantics.Assignment.{max uO uT uH uOcc}) :
    ∃ (actual : HOL.HenkinModel.{0,0,(max uO uT uH uOcc)+1} AtomicTy Symbol)
      (encoding : Coding actual Obj Tm Hom),
      actual.Carrier = (HOLFrameDomains.initial Obj Tm Hom O other prior).Carrier ∧ actual.FullDomains ∧
      ∀ (a b : Obj) (map : Hom a b) (store : EquationStore (Tm a)),
        (actual.constDen HOLLoadedModels.symbol (homValue actual encoding) (equalValue actual X encoding)
          (actionValue actual X encoding) (encoding.objects.symm (some a)) (encoding.objects.symm (some b))
          (encoding.morphisms.symm (HOLFrameEncoding.encodeHom map)) (storeValue actual encoding store)).down ↔
            X.Models map store := by
  obtain ⟨actual, same, full, equations⟩ := HOLFrameDomains.loaded_model_exists Obj Tm Hom O other prior
  let encoding := (initialCoding (Obj := Obj) (Tm := Tm) (Hom := Hom) O other prior).changeModel actual same
  exact ⟨actual, encoding, same, full, fun _ _ map store => models_iff actual X encoding full equations map store⟩

#print axioms models_iff
#print axioms loaded_model_agrees

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLModelsSpecialization
