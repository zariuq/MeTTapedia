import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedExact
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLIndexedQuantifiers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFramesSpecialization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EffectCore

/-! # Loaded exactness is the optional reverse solution implication

Every valid future map is represented, and invalid raw values contribute no
extra obligations. The per-preparation interpretation recovers precisely
EffectCore.ExactKnowledge, independently of an admission profile.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLExactSpecialization

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody HOLFrameCoding HOLFramesCoding HOLIndexedQuantifiers

universe w uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (X : Frames Tm Hom) (code : Coding model Obj Tm Hom)
  (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLSemanticDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)

include full equations in
theorem exact_iff {m b : Obj} (settle : Hom m b)
    (information : EquationStore (Tm m)) (next : EquationStore (Tm b)) :
    (model.constDen HOLLoadedExact.symbol (homValue model code) (equalValue model X code)
      (actionValue model X code) (compositionValue model X code)
      (code.objects.symm (some m)) (code.objects.symm (some b))
      (code.morphisms.symm (HOLFrameEncoding.encodeHom settle))
      (storeValue model code information) (storeValue model code next)).down ↔
      ∀ (c : Obj) (sigma : Hom b c), X.Models (X.comp sigma settle) information → X.Models sigma next := by
  have evaluated := HOLLoadedExact.operational_meaning model full equations
    (homValue model code) (equalValue model X code) (actionValue model X code)
    (compositionValue model X code) (code.objects.symm (some m)) (code.objects.symm (some b))
    (code.morphisms.symm (HOLFrameEncoding.encodeHom settle))
    (storeValue model code information) (storeValue model code next)
  refine (iff_of_eq (congrArg ULift.down evaluated)).trans ?_
  constructor
  · intro holds c sigma solves
    apply (HOLModelsSpecialization.models_iff model X code full equations sigma next).mp
    apply holds (code.objects.symm (some c)) (code.morphisms.symm (HOLFrameEncoding.encodeHom sigma))
    refine ⟨?_, ?_⟩
    · simpa only [homValue, Equiv.apply_symm_apply] using HOLFrameEncoding.hom_encoded sigma
    · rw [composition_encoded]
      exact (HOLModelsSpecialization.models_iff model X code full equations (X.comp sigma settle) information).mpr solves
  · rintro holds c sigma ⟨valid, solves⟩
    obtain ⟨target, map, targetEq, mapEq⟩ := valid_map_values model code c sigma valid
    rw [targetEq, mapEq] at solves ⊢
    rw [composition_encoded] at solves
    apply (HOLModelsSpecialization.models_iff model X code full equations map next).mpr
    exact holds target map
      ((HOLModelsSpecialization.models_iff model X code full equations (X.comp map settle) information).mp solves)

include full equations in
theorem effect_exact_iff {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
    (E : EffectCore X O State Firing) :
    (∀ {s : State} (f : Firing s) (p : E.Prepares f),
      (model.constDen HOLLoadedExact.symbol (homValue model code) (equalValue model X code)
        (actionValue model X code) (compositionValue model X code)
        (code.objects.symm (some (E.target f))) (code.objects.symm (some (E.frame (E.preparedResult f p))))
        (code.morphisms.symm (HOLFrameEncoding.encodeHom (E.preparedSettle f p)))
        (storeValue model code (E.information f)) (storeValue model code (E.knowledge (E.preparedResult f p)))).down) ↔
      E.ExactKnowledge := by
  simp only [exact_iff model X code full equations, EffectCore.ExactKnowledge]

structure Agreement : Prop extends toFramesAgreement : HOLFramesSpecialization.Agreement model X code where
  exactKnowledge : ∀ (m b : Obj) (settle : Hom m b)
    (information : EquationStore (Tm m)) (next : EquationStore (Tm b)),
    (model.constDen HOLLoadedExact.symbol (homValue model code) (equalValue model X code)
      (actionValue model X code) (compositionValue model X code)
      (code.objects.symm (some m)) (code.objects.symm (some b))
      (code.morphisms.symm (HOLFrameEncoding.encodeHom settle))
      (storeValue model code information) (storeValue model code next)).down ↔
      ∀ (c : Obj) (sigma : Hom b c), X.Models (X.comp sigma settle) information → X.Models sigma next

include full equations in
theorem agreement_of_cache : Agreement model X code where
  toFramesAgreement := HOLFramesSpecialization.agreement_of_cache model X code full equations
  exactKnowledge := fun _ _ settle information next => exact_iff model X code full equations settle information next

theorem constructed_agreement (O : Type uOcc)
    (other : TypeFamilySemantics.OperatorFamilies.{max uO uT uH uOcc})
    (prior : TypeFamilySemantics.Assignment.{max uO uT uH uOcc}) :
    ∃ (actual : HOL.HenkinModel.{0,0,(max uO uT uH uOcc)+1} AtomicTy Symbol)
      (encoding : Coding actual Obj Tm Hom),
      actual.Carrier = (HOLFrameDomains.initial Obj Tm Hom O other prior).Carrier ∧ Agreement actual X encoding := by
  obtain ⟨actual, same, actualFull, actualEquations⟩ := HOLFrameDomains.loaded_model_exists Obj Tm Hom O other prior
  let encoding := (initialCoding (Obj := Obj) (Tm := Tm) (Hom := Hom) O other prior).changeModel actual same
  exact ⟨actual, encoding, same, agreement_of_cache actual X encoding actualFull actualEquations⟩

#print axioms exact_iff
#print axioms effect_exact_iff
#print axioms constructed_agreement

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLExactSpecialization
