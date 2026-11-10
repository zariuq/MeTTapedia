import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLModelsBody

/-! # Carrier conversions for the loaded transform predicates

The conversions are constructed from the actual A/T/H parameter assignment.
Frame predicates, action and finite stores are transported through those
bijections. Model extension preserves them through its proved carrier equality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFrameCoding

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open HOLModelsBody

universe w uO uT uH uOcc

structure Coding (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (Obj : Type uO) (Tm : Obj → Type uT) (Hom : Obj → Obj → Type uH) where
  objects : HOL.Ty.denote.{0,w+1} model.Carrier objectType ≃ HOLFrameEncoding.Objects Obj
  terms : HOL.Ty.denote.{0,w+1} model.Carrier termType ≃ HOLFrameEncoding.Terms Tm
  morphisms : HOL.Ty.denote.{0,w+1} model.Carrier mapType ≃ HOLFrameEncoding.Morphisms Hom

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (X : Frames Tm Hom) (code : Coding model Obj Tm Hom)

def homValue : HOL.Ty.denote.{0,w+1} model.Carrier homType :=
  fun a b map => ULift.up (HOLFrameEncoding.hom (code.objects a) (code.objects b) (code.morphisms map))

def termsValue : HOL.Ty.denote.{0,w+1} model.Carrier (.arr objectType (.arr termType .prop)) :=
  fun a term => ULift.up (HOLFrameEncoding.terms (code.objects a) (code.terms term))

def equalValue : HOL.Ty.denote.{0,w+1} model.Carrier equalType :=
  fun a x y => ULift.up (HOLFrameEncoding.equal X (code.objects a) (code.terms x) (code.terms y))

noncomputable def actionValue : HOL.Ty.denote.{0,w+1} model.Carrier actionType :=
  fun map term => code.terms.symm (HOLFrameEncoding.act X (code.morphisms map) (code.terms term))

def predicateValue (store : HOLFrameEncoding.Terms Tm → HOLFrameEncoding.Terms Tm → Prop) :
    HOL.Ty.denote.{0,w+1} model.Carrier storeType :=
  fun x y => ULift.up (store (code.terms x) (code.terms y))

def storeValue {a : Obj} (store : EquationStore (Tm a)) : HOL.Ty.denote.{0,w+1} model.Carrier storeType :=
  predicateValue model code (HOLFrameEncoding.store store)

theorem body_models_raw_iff (full : model.FullDomains) (booleans : HOLLoadedBooleans.Meanings model)
    (a b : HOLFrameEncoding.Objects Obj) (map : HOLFrameEncoding.Morphisms Hom)
    (store : HOLFrameEncoding.Terms Tm → HOLFrameEncoding.Terms Tm → Prop) :
    (model.denote HOLModelsBody.body (fun index => nomatch index) (homValue model code) (equalValue model X code)
      (actionValue model X code) (code.objects.symm a) (code.objects.symm b)
      (code.morphisms.symm map) (predicateValue model code store)).down ↔
      HOLFrameEncoding.models X a b map store := by
  have evaluated := HOLModelsBody.denote_body model full booleans
    (homValue model code) (equalValue model X code) (actionValue model X code)
    (code.objects.symm a) (code.objects.symm b) (code.morphisms.symm map) (predicateValue model code store)
  refine (iff_of_eq (congrArg ULift.down evaluated)).trans ?_
  simp only [homValue, equalValue, actionValue, predicateValue, Equiv.apply_symm_apply]
  constructor
  · rintro ⟨valid, satisfies⟩
    refine ⟨valid, ?_⟩
    intro x y member
    have actual := satisfies (code.terms.symm x) (code.terms.symm y)
    simpa only [Equiv.apply_symm_apply] using
      actual (by simpa only [Equiv.apply_symm_apply] using member)
  · rintro ⟨valid, satisfies⟩
    exact ⟨valid, fun x y => satisfies (code.terms x) (code.terms y)⟩

theorem body_models_iff (full : model.FullDomains) (booleans : HOLLoadedBooleans.Meanings model)
    {a b : Obj} (map : Hom a b) (store : EquationStore (Tm a)) :
    (model.denote HOLModelsBody.body (fun index => nomatch index) (homValue model code) (equalValue model X code)
      (actionValue model X code) (code.objects.symm (some a)) (code.objects.symm (some b))
      (code.morphisms.symm (HOLFrameEncoding.encodeHom map)) (storeValue model code store)).down ↔
      X.Models map store := by
  exact (body_models_raw_iff model X code full booleans (some a) (some b)
    (HOLFrameEncoding.encodeHom map) (HOLFrameEncoding.store store)).trans
    (HOLFrameEncoding.models_encoded X map store)

def Coding.changeModel {first : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol}
    (encoding : Coding first Obj Tm Hom) (second : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (same : second.Carrier = first.Carrier) : Coding second Obj Tm Hom where
  objects := (Equiv.cast (congrArg (fun carrier => HOL.Ty.denote.{0,w+1} carrier objectType) same)).trans encoding.objects
  terms := (Equiv.cast (congrArg (fun carrier => HOL.Ty.denote.{0,w+1} carrier termType) same)).trans encoding.terms
  morphisms := (Equiv.cast (congrArg (fun carrier => HOL.Ty.denote.{0,w+1} carrier mapType) same)).trans encoding.morphisms

def parameterCoding (O : Type uOcc)
    (other : TypeFamilySemantics.OperatorFamilies.{max uO uT uH uOcc})
    (prior : TypeFamilySemantics.Assignment.{max uO uT uH uOcc}) (slot : HOLFrameDomains.Slot) :
    HOL.Ty.denote.{0,(max uO uT uH uOcc)+1}
      (HOLFrameDomains.initial Obj Tm Hom O other prior).Carrier
      (Ty.var (HOLFrameDomains.parameter slot)).toHOL ≃ (HOLFrameDomains.domains Obj Tm Hom O slot).Carrier :=
  (TypeFamilySemantics.holValue other (HOLFrameDomains.assignment Obj Tm Hom O prior)
    (Ty.var (HOLFrameDomains.parameter slot))).symm.trans
      (Equiv.cast (congrArg TypeFamilySemantics.Domain.Carrier
        (HOLFrameDomains.evaluated_parameter Obj Tm Hom O other prior slot)))

def initialCoding (O : Type uOcc)
    (other : TypeFamilySemantics.OperatorFamilies.{max uO uT uH uOcc})
    (prior : TypeFamilySemantics.Assignment.{max uO uT uH uOcc}) :
    Coding (HOLFrameDomains.initial Obj Tm Hom O other prior) Obj Tm Hom where
  objects := (parameterCoding (Obj := Obj) (Tm := Tm) (Hom := Hom) O other prior .objects).trans Equiv.ulift
  terms := (parameterCoding (Obj := Obj) (Tm := Tm) (Hom := Hom) O other prior .terms).trans Equiv.ulift
  morphisms := (parameterCoding (Obj := Obj) (Tm := Tm) (Hom := Hom) O other prior .morphisms).trans Equiv.ulift


end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFrameCoding
