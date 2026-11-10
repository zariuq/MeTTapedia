import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedStore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLLoadedMapStore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFrameCoding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLSolutionSpecialization

/-! # Loaded store typing and transport agree with indexed equation stores

The raw relations remain arbitrary predicates. Finite Lean stores supply
one representation, whose image is exactly the existing applyStore list
operation. No finite-representability assumption is imposed on all HOL stores.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLStoreSpecialization

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody HOLFrameCoding

universe w uO uT uH

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (X : Frames Tm Hom) (code : Coding model Obj Tm Hom)
  (full : model.FullDomains)
  (equations : ∀ fact ∈ HOLSemanticDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧ model.models formula)

include full equations in
theorem typed_raw_iff (a : HOLFrameEncoding.Objects Obj)
    (store : HOLFrameEncoding.Terms Tm → HOLFrameEncoding.Terms Tm → Prop) :
    (model.constDen HOLLoadedStore.symbol (termsValue model code) (code.objects.symm a)
      (predicateValue model code store)).down ↔
      ∀ x y, store x y → HOLFrameEncoding.terms a x ∧ HOLFrameEncoding.terms a y := by
  have evaluated := HOLLoadedStore.operational_meaning model full equations
    (termsValue model code) (code.objects.symm a) (predicateValue model code store)
  refine (iff_of_eq (congrArg ULift.down evaluated)).trans ?_
  simp only [termsValue, predicateValue, Equiv.apply_symm_apply]
  constructor
  · intro holds x y member
    have actual := holds (code.terms.symm x) (code.terms.symm y)
    simpa only [Equiv.apply_symm_apply] using actual (by simpa only [Equiv.apply_symm_apply] using member)
  · intro holds x y
    exact holds (code.terms x) (code.terms y)

include full equations in
theorem finite_store_typed {a : Obj} (store : EquationStore (Tm a)) :
    (model.constDen HOLLoadedStore.symbol (termsValue model code) (code.objects.symm (some a))
      (storeValue model code store)).down := by
  apply (typed_raw_iff model code full equations (some a) (HOLFrameEncoding.store store)).mpr
  intro x y member
  exact HOLFrameEncoding.store_typed store member

include full equations in
theorem transport_raw_iff (map : HOLFrameEncoding.Morphisms Hom)
    (store : HOLFrameEncoding.Terms Tm → HOLFrameEncoding.Terms Tm → Prop)
    (left right : HOLFrameEncoding.Terms Tm) :
    (model.constDen HOLLoadedMapStore.symbol (actionValue model X code) (code.morphisms.symm map)
      (predicateValue model code store) (code.terms.symm left) (code.terms.symm right)).down ↔
      HOLFrameEncoding.mapStore X map store left right := by
  have evaluated := HOLLoadedMapStore.operational_meaning model full equations
    (actionValue model X code) (code.morphisms.symm map) (predicateValue model code store)
    (code.terms.symm left) (code.terms.symm right)
  refine (iff_of_eq (congrArg ULift.down evaluated)).trans ?_
  simp only [actionValue, predicateValue, Equiv.apply_symm_apply]
  constructor
  · rintro ⟨x, y, member, first, second⟩
    refine ⟨code.terms x, code.terms y, member, ?_, ?_⟩
    · simpa only [Equiv.apply_symm_apply] using congrArg code.terms first
    · simpa only [Equiv.apply_symm_apply] using congrArg code.terms second
  · rintro ⟨x, y, member, first, second⟩
    refine ⟨code.terms.symm x, code.terms.symm y, ?_, ?_, ?_⟩
    · simpa only [Equiv.apply_symm_apply] using member
    · simpa only [Equiv.apply_symm_apply] using congrArg code.terms.symm first
    · simpa only [Equiv.apply_symm_apply] using congrArg code.terms.symm second

include full equations in
theorem finite_transport_iff {a b : Obj} (map : Hom a b) (store : EquationStore (Tm a))
    (left right : HOLFrameEncoding.Terms Tm) :
    (model.constDen HOLLoadedMapStore.symbol (actionValue model X code)
      (code.morphisms.symm (HOLFrameEncoding.encodeHom map)) (storeValue model code store)
      (code.terms.symm left) (code.terms.symm right)).down ↔
      HOLFrameEncoding.store (X.applyStore map store) left right := by
  have exactImage := transport_raw_iff model X code full equations
    (HOLFrameEncoding.encodeHom map) (HOLFrameEncoding.store store) left right
  rw [HOLFrameEncoding.mapped_store_encoded] at exactImage
  exact exactImage

include full equations in
theorem transport_function {a b : Obj} (map : Hom a b) (store : EquationStore (Tm a)) :
    model.constDen HOLLoadedMapStore.symbol (actionValue model X code)
      (code.morphisms.symm (HOLFrameEncoding.encodeHom map)) (storeValue model code store) =
      storeValue model code (X.applyStore map store) := by
  funext left right
  apply ULift.ext
  apply propext
  have exactImage := finite_transport_iff model X code full equations map store (code.terms left) (code.terms right)
  simpa only [Equiv.symm_apply_apply, storeValue, predicateValue] using exactImage

include full equations in
theorem transported_store_typed {a b : Obj} (map : Hom a b) (store : EquationStore (Tm a)) :
    (model.constDen HOLLoadedStore.symbol (termsValue model code) (code.objects.symm (some b))
      (model.constDen HOLLoadedMapStore.symbol (actionValue model X code)
        (code.morphisms.symm (HOLFrameEncoding.encodeHom map)) (storeValue model code store))).down := by
  rw [transport_function model X code full equations]
  exact finite_store_typed model code full equations _

/-- One interpretation supplies all four store-related correspondences. -/
structure Agreement : Prop where
  fullDomains : model.FullDomains
  models : ∀ (a b : Obj) (map : Hom a b) (store : EquationStore (Tm a)),
    (model.constDen HOLLoadedModels.symbol (homValue model code) (equalValue model X code)
      (actionValue model X code) (code.objects.symm (some a)) (code.objects.symm (some b))
      (code.morphisms.symm (HOLFrameEncoding.encodeHom map)) (storeValue model code store)).down ↔ X.Models map store
  solvable : ∀ (a : Obj) (store : EquationStore (Tm a)),
    (model.constDen HOLLoadedSolvable.symbol (homValue model code) (equalValue model X code)
      (actionValue model X code) (code.objects.symm (some a)) (storeValue model code store)).down ↔ X.Solvable store
  typed : ∀ (a : Obj) (store : EquationStore (Tm a)),
    (model.constDen HOLLoadedStore.symbol (termsValue model code) (code.objects.symm (some a))
      (storeValue model code store)).down
  transport : ∀ (a b : Obj) (map : Hom a b) (store : EquationStore (Tm a)),
    model.constDen HOLLoadedMapStore.symbol (actionValue model X code)
      (code.morphisms.symm (HOLFrameEncoding.encodeHom map)) (storeValue model code store) =
        storeValue model code (X.applyStore map store)

include full equations in
theorem agreement_of_cache : Agreement model X code :=
  ⟨full,
    fun _ _ map store => HOLModelsSpecialization.models_iff model X code full equations map store,
    fun _ store => HOLSolutionSpecialization.solvable_iff model X code full equations store,
    fun _ store => finite_store_typed model code full equations store,
    fun _ _ map store => transport_function model X code full equations map store⟩

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

#print axioms typed_raw_iff
#print axioms finite_transport_iff
#print axioms transported_store_typed
#print axioms constructed_agreement

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLStoreSpecialization
