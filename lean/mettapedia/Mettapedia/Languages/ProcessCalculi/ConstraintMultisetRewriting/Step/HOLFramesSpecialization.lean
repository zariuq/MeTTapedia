import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedFrames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFramesCoding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLStoreSpecialization

/-! # One loaded interpretation of frames and equation stores

The actual frame-law predicate holds on the same carrier encoding used for
models, solvability, store typing and transport. Its meaning is obtained from
the received defining equation and the indexed frame laws.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFramesSpecialization

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody HOLFrameCoding HOLFramesCoding

universe w uO uT uH

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (X : Frames Tm Hom) (code : Coding model Obj Tm Hom)
  (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLSemanticDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)

include full equations in
theorem loaded_frames :
    (model.constDen HOLLoadedFrames.symbol (objectsValue model code) (termsValue model code)
      (homValue model code) (equalValue model X code) (actionValue model X code)
      (identityValue model X code) (compositionValue model X code)).down := by
  have evaluated := HOLLoadedFrames.operational_meaning model full equations
    (objectsValue model code) (termsValue model code) (homValue model code)
    (equalValue model X code) (actionValue model X code)
    (identityValue model X code) (compositionValue model X code)
  exact (iff_of_eq (congrArg ULift.down evaluated)).mpr (lawful model X code)

structure Agreement : Prop extends HOLStoreSpecialization.Agreement model X code where
  frames : (model.constDen HOLLoadedFrames.symbol (objectsValue model code) (termsValue model code)
    (homValue model code) (equalValue model X code) (actionValue model X code)
    (identityValue model X code) (compositionValue model X code)).down

include full equations in
theorem agreement_of_cache : Agreement model X code where
  toAgreement := HOLStoreSpecialization.agreement_of_cache model X code full equations
  frames := loaded_frames model X code full equations

universe uOcc

theorem constructed_agreement (O : Type uOcc)
    (other : TypeFamilySemantics.OperatorFamilies.{max uO uT uH uOcc})
    (prior : TypeFamilySemantics.Assignment.{max uO uT uH uOcc}) :
    ∃ (actual : HOL.HenkinModel.{0,0,(max uO uT uH uOcc)+1} AtomicTy Symbol)
      (encoding : Coding actual Obj Tm Hom),
      actual.Carrier = (HOLFrameDomains.initial Obj Tm Hom O other prior).Carrier ∧ Agreement actual X encoding := by
  obtain ⟨actual, same, actualFull, actualEquations⟩ := HOLFrameDomains.loaded_model_exists Obj Tm Hom O other prior
  let encoding := (initialCoding (Obj := Obj) (Tm := Tm) (Hom := Hom) O other prior).changeModel actual same
  exact ⟨actual, encoding, same, agreement_of_cache actual X encoding actualFull actualEquations⟩

#print axioms loaded_frames
#print axioms constructed_agreement

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFramesSpecialization
