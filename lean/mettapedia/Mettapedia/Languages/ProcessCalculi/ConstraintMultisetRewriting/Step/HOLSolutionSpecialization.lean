import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLModelsSpecialization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedSolvable

/-! # Models and solvability agree in one constructed HOL interpretation

Both operational meanings use the same actual definition history, model and
carrier conversions. The existential target and morphism range over the full
raw domains; the encoded hom predicate excludes invalid representatives.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLSolutionSpecialization

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody HOLFrameCoding

universe w uO uT uH uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (X : Frames Tm Hom) (code : Coding model Obj Tm Hom)
  (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLSemanticDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)

include full equations in
theorem solvable_iff {a : Obj} (store : EquationStore (Tm a)) :
    (model.constDen HOLLoadedSolvable.symbol (homValue model code) (equalValue model X code)
      (actionValue model X code) (code.objects.symm (some a)) (storeValue model code store)).down ↔
      X.Solvable store := by
  have evaluated := HOLLoadedSolvable.operational_meaning model full equations
    (homValue model code) (equalValue model X code) (actionValue model X code)
    (code.objects.symm (some a)) (storeValue model code store)
  refine (iff_of_eq (congrArg ULift.down evaluated)).trans ?_
  rw [← HOLFrameEncoding.solvable_encoded X store]
  constructor
  · rintro ⟨target, map, solves⟩
    refine ⟨code.objects target, code.morphisms map, ?_⟩
    apply (HOLModelsSpecialization.models_raw_iff model X code full equations
      (some a) (code.objects target) (code.morphisms map) (HOLFrameEncoding.store store)).mp
    simpa only [Equiv.symm_apply_apply, storeValue] using solves
  · rintro ⟨target, map, solves⟩
    exact ⟨code.objects.symm target, code.morphisms.symm map,
      (HOLModelsSpecialization.models_raw_iff model X code full equations
        (some a) target map (HOLFrameEncoding.store store)).mpr solves⟩

include full equations in
theorem invalid_target_has_no_model (a : Obj) (map : HOLFrameEncoding.Morphisms Hom)
    (store : EquationStore (Tm a)) :
    ¬(model.constDen HOLLoadedModels.symbol (homValue model code) (equalValue model X code)
      (actionValue model X code) (code.objects.symm (some a)) (code.objects.symm none)
      (code.morphisms.symm map) (storeValue model code store)).down := by
  intro claimed
  have raw := (HOLModelsSpecialization.models_raw_iff model X code full equations
    (some a) none map (HOLFrameEncoding.store store)).mp claimed
  exact HOLFrameEncoding.invalid_object_has_no_hom (some a) map raw.1

theorem constructed_model_correct (O : Type uOcc)
    (other : TypeFamilySemantics.OperatorFamilies.{max uO uT uH uOcc})
    (prior : TypeFamilySemantics.Assignment.{max uO uT uH uOcc}) :
    ∃ (actual : HOL.HenkinModel.{0,0,(max uO uT uH uOcc)+1} AtomicTy Symbol)
      (encoding : Coding actual Obj Tm Hom),
      actual.Carrier = (HOLFrameDomains.initial Obj Tm Hom O other prior).Carrier ∧ actual.FullDomains ∧
      (∀ (a b : Obj) (map : Hom a b) (store : EquationStore (Tm a)),
        (actual.constDen HOLLoadedModels.symbol (homValue actual encoding) (equalValue actual X encoding)
          (actionValue actual X encoding) (encoding.objects.symm (some a)) (encoding.objects.symm (some b))
          (encoding.morphisms.symm (HOLFrameEncoding.encodeHom map)) (storeValue actual encoding store)).down ↔
            X.Models map store) ∧
      (∀ (a : Obj) (store : EquationStore (Tm a)),
        (actual.constDen HOLLoadedSolvable.symbol (homValue actual encoding) (equalValue actual X encoding)
          (actionValue actual X encoding) (encoding.objects.symm (some a)) (storeValue actual encoding store)).down ↔
            X.Solvable store) := by
  obtain ⟨actual, same, actualFull, actualEquations⟩ := HOLFrameDomains.loaded_model_exists Obj Tm Hom O other prior
  let encoding := (initialCoding (Obj := Obj) (Tm := Tm) (Hom := Hom) O other prior).changeModel actual same
  exact ⟨actual, encoding, same, actualFull,
    fun _ _ map store => HOLModelsSpecialization.models_iff actual X encoding actualFull actualEquations map store,
    fun _ store => solvable_iff actual X encoding actualFull actualEquations store⟩

#print axioms solvable_iff
#print axioms invalid_target_has_no_model
#print axioms constructed_model_correct

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLSolutionSpecialization
