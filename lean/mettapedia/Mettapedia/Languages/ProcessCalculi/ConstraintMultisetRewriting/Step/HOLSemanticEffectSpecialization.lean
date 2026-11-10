import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedSemanticEffect
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLKnowledgePullback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFireSpecialization

/-! # Semantic effects agree with indexed solution refinement

Store typing and morphism validity follow from the supplied indexed data.
The remaining obligations are exactly the two solution pullbacks and the
occurrence update. Neither exactness nor permission is required here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLSemanticEffectSpecialization

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLFrameCoding HOLFramesCoding
open HOLOccurrenceCoding (finiteValue)
open MeTTaCalculus.OccurrenceCommits (Commit fire)

universe w uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (X : Frames Tm Hom) (code : Coding model Obj Tm Hom)
  {O : Type uOcc} [DecidableEq O] (occurrences : HOLOccurrenceCoding.Coding model O)
  (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLSemanticDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)

include full equations in
theorem occurrences_iff (present after : Finset O) (commit : Commit O Unit) :
    (∀ occ, (finiteValue model occurrences after occ).down ↔
      (model.constDen HOLLoadedFire.symbol (finiteValue model occurrences present)
        (finiteValue model occurrences commit.taken) (finiteValue model occurrences commit.made) occ).down) ↔
      after = fire present commit := by
  have image := HOLFireSpecialization.fire_function model occurrences full equations present commit
  constructor
  · intro agrees
    apply HOLOccurrenceCoding.finiteValue_injective model occurrences
    funext occ
    apply ULift.ext
    exact propext ((agrees occ).trans (iff_of_eq (congrArg ULift.down (congrFun image occ))))
  · rintro rfl occ
    exact (iff_of_eq (congrArg ULift.down (congrFun image occ))).symm

noncomputable def effectValue {a m b : Obj} (extension : Hom a m) (settle : Hom m b)
    (old : EquationStore (Tm a)) (information : EquationStore (Tm m)) (next : EquationStore (Tm b))
    (present after : Finset O) (commit : Commit O Unit) :
    HOL.Ty.denote.{0,w+1} model.Carrier .prop :=
    model.constDen HOLLoadedSemanticEffect.symbol (termsValue model code) (homValue model code)
      (equalValue model X code) (actionValue model X code) (compositionValue model X code)
      (code.objects.symm (some a)) (code.objects.symm (some m)) (code.objects.symm (some b))
      (code.morphisms.symm (HOLFrameEncoding.encodeHom extension)) (code.morphisms.symm (HOLFrameEncoding.encodeHom settle))
      (storeValue model code old) (storeValue model code information) (storeValue model code next)
      (finiteValue model occurrences present) (finiteValue model occurrences commit.taken)
      (finiteValue model occurrences commit.kept) (finiteValue model occurrences commit.made)
      (finiteValue model occurrences after)

include full equations in
theorem semantic_iff {a m b : Obj} (extension : Hom a m) (settle : Hom m b)
    (old : EquationStore (Tm a)) (information : EquationStore (Tm m)) (next : EquationStore (Tm b))
    (present after : Finset O) (commit : Commit O Unit) :
    (model.constDen HOLLoadedSemanticEffect.symbol (termsValue model code) (homValue model code)
      (equalValue model X code) (actionValue model X code) (compositionValue model X code)
      (code.objects.symm (some a)) (code.objects.symm (some m)) (code.objects.symm (some b))
      (code.morphisms.symm (HOLFrameEncoding.encodeHom extension)) (code.morphisms.symm (HOLFrameEncoding.encodeHom settle))
      (storeValue model code old) (storeValue model code information) (storeValue model code next)
      (finiteValue model occurrences present) (finiteValue model occurrences commit.taken)
      (finiteValue model occurrences commit.kept) (finiteValue model occurrences commit.made)
      (finiteValue model occurrences after)).down ↔
      (∀ (c : Obj) (sigma : Hom m c), X.Models sigma information → X.Models (X.comp sigma extension) old) ∧
      (∀ (c : Obj) (sigma : Hom b c), X.Models sigma next → X.Models (X.comp sigma settle) information) ∧
      after = fire present commit := by
  have evaluated := HOLLoadedSemanticEffect.operational_meaning model full equations
    (termsValue model code) (homValue model code) (equalValue model X code) (actionValue model X code)
    (compositionValue model X code) (code.objects.symm (some a)) (code.objects.symm (some m)) (code.objects.symm (some b))
    (code.morphisms.symm (HOLFrameEncoding.encodeHom extension)) (code.morphisms.symm (HOLFrameEncoding.encodeHom settle))
    (storeValue model code old) (storeValue model code information) (storeValue model code next)
    (finiteValue model occurrences present) (finiteValue model occurrences commit.taken)
    (finiteValue model occurrences commit.kept) (finiteValue model occurrences commit.made)
    (finiteValue model occurrences after)
  refine (iff_of_eq (congrArg ULift.down evaluated)).trans ?_
  unfold HOLSemanticEffectBody.Contract
  rw [HOLKnowledgePullback.pullback_iff model X code full equations extension old information,
    HOLKnowledgePullback.pullback_iff model X code full equations settle information next,
    occurrences_iff model occurrences full equations present after commit]
  have validExtension : (homValue model code (code.objects.symm (some a)) (code.objects.symm (some m))
      (code.morphisms.symm (HOLFrameEncoding.encodeHom extension))).down := by
    simpa only [homValue, Equiv.apply_symm_apply] using HOLFrameEncoding.hom_encoded extension
  have validSettle : (homValue model code (code.objects.symm (some m)) (code.objects.symm (some b))
      (code.morphisms.symm (HOLFrameEncoding.encodeHom settle))).down := by
    simpa only [homValue, Equiv.apply_symm_apply] using HOLFrameEncoding.hom_encoded settle
  simp only [HOLStoreSpecialization.finite_store_typed model code full equations,
    validExtension, validSettle, true_and]

noncomputable def preparedValue {State : Type uS} {Firing : State → Type uF}
    (E : EffectCore X O State Firing) {s : State} (f : Firing s) (p : E.Prepares f) :
    HOL.Ty.denote.{0,w+1} model.Carrier .prop :=
    model.constDen HOLLoadedSemanticEffect.symbol (termsValue model code) (homValue model code)
      (equalValue model X code) (actionValue model X code) (compositionValue model X code)
      (code.objects.symm (some (E.frame s))) (code.objects.symm (some (E.target f)))
      (code.objects.symm (some (E.frame (E.preparedResult f p))))
      (code.morphisms.symm (HOLFrameEncoding.encodeHom (E.extension f)))
      (code.morphisms.symm (HOLFrameEncoding.encodeHom (E.preparedSettle f p)))
      (storeValue model code (E.knowledge s)) (storeValue model code (E.information f))
      (storeValue model code (E.knowledge (E.preparedResult f p)))
      (finiteValue model occurrences (E.present s)) (finiteValue model occurrences ((E.selection f).commit (T := Unit)).taken)
      (finiteValue model occurrences ((E.selection f).commit (T := Unit)).kept)
      (finiteValue model occurrences ((E.selection f).commit (T := Unit)).made)
      (finiteValue model occurrences (E.present (E.preparedResult f p)))

include full equations in
theorem prepared_effect {State : Type uS} {Firing : State → Type uF}
    (E : EffectCore X O State Firing) {s : State} (f : Firing s) (p : E.Prepares f) :
    (preparedValue model X code occurrences E f p).down := by
  apply (semantic_iff model X code occurrences full equations (E.extension f) (E.preparedSettle f p)
    (E.knowledge s) (E.information f) (E.knowledge (E.preparedResult f p))
    (E.present s) (E.present (E.preparedResult f p)) ((E.selection f).commit (T := Unit))).mpr
  exact ⟨fun _ sigma => E.information_refines f sigma,
    fun _ sigma => E.result_refines f p sigma, E.present_preparedResult f p⟩

structure Agreement : Prop extends toExactAgreement : HOLExactSpecialization.Agreement model X code where
  semanticEffect : ∀ (a m b : Obj) (extension : Hom a m) (settle : Hom m b)
    (old : EquationStore (Tm a)) (information : EquationStore (Tm m)) (next : EquationStore (Tm b))
    (present after : Finset O) (commit : Commit O Unit),
    (effectValue model X code occurrences extension settle old information next present after commit).down ↔
      (∀ (c : Obj) (sigma : Hom m c), X.Models sigma information → X.Models (X.comp sigma extension) old) ∧
      (∀ (c : Obj) (sigma : Hom b c), X.Models sigma next → X.Models (X.comp sigma settle) information) ∧
      after = fire present commit

include full equations in
theorem agreement_of_cache : Agreement model X code occurrences where
  toExactAgreement := HOLExactSpecialization.agreement_of_cache model X code full equations
  semanticEffect := fun _ _ _ extension settle old information next present after commit =>
    semantic_iff model X code occurrences full equations extension settle old information next present after commit

theorem constructed_agreement
    (other : TypeFamilySemantics.OperatorFamilies.{max uO uT uH uOcc})
    (prior : TypeFamilySemantics.Assignment.{max uO uT uH uOcc}) :
    ∃ (actual : HOL.HenkinModel.{0,0,(max uO uT uH uOcc)+1} AtomicTy Symbol)
      (frames : Coding actual Obj Tm Hom) (occurrences : HOLOccurrenceCoding.Coding actual O),
      actual.Carrier = (HOLFrameDomains.initial Obj Tm Hom O other prior).Carrier ∧ Agreement actual X frames occurrences := by
  obtain ⟨actual, same, actualFull, actualEquations⟩ := HOLFrameDomains.loaded_model_exists Obj Tm Hom O other prior
  let frames := (initialCoding (Obj := Obj) (Tm := Tm) (Hom := Hom) O other prior).changeModel actual same
  let occurrences := HOLOccurrenceCoding.changeModel (HOLOccurrenceCoding.initialCoding Obj Tm Hom O other prior) actual same
  exact ⟨actual, frames, occurrences, same, agreement_of_cache actual X frames occurrences actualFull actualEquations⟩

#print axioms occurrences_iff
#print axioms semantic_iff
#print axioms prepared_effect
#print axioms constructed_agreement

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLSemanticEffectSpecialization
