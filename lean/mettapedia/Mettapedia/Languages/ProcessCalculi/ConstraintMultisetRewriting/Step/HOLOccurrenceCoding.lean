import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFrameCoding

/-! # Occurrence predicates on an inhabited raw domain

The extra raw value is outside every represented occurrence set. In
particular, an empty occurrence type stays empty in all finite stores.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLOccurrenceCoding

open Mettapedia.Logic Mettapedia.Languages.OpenTheory

abbrev occurrenceType : HOL.Ty AtomicTy := (Ty.var (Name.global "O")).toHOL
abbrev setType : HOL.Ty AtomicTy := .arr occurrenceType .prop

universe w uO uT uH uOcc

abbrev Coding (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (O : Type uOcc) :=
  HOL.Ty.denote.{0,w+1} model.Carrier occurrenceType ≃ Option O

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) {O : Type uOcc}
  (code : Coding model O)

def predicateValue (predicate : Option O → Prop) : HOL.Ty.denote.{0,w+1} model.Carrier setType :=
  fun value => ULift.up (predicate (code value))

def finitePredicate (store : Finset O) : Option O → Prop
  | none => False
  | some occurrence => occurrence ∈ store

def finiteValue (store : Finset O) : HOL.Ty.denote.{0,w+1} model.Carrier setType :=
  predicateValue model code (finitePredicate store)

theorem invalid_absent (store : Finset O) :
    ¬(finiteValue model code store (code.symm none)).down := by
  simp only [finiteValue, predicateValue, Equiv.apply_symm_apply, finitePredicate, not_false_eq_true]

theorem encoded_member (store : Finset O) (occurrence : O) :
    (finiteValue model code store (code.symm (some occurrence))).down ↔ occurrence ∈ store := by
  simp only [finiteValue, predicateValue, Equiv.apply_symm_apply, finitePredicate]

theorem finiteValue_injective : Function.Injective (finiteValue model code) := by
  intro first second same
  apply Finset.ext
  intro occurrence
  have point := congrArg ULift.down (congrFun same (code.symm (some occurrence)))
  exact (encoded_member model code first occurrence).symm.trans
    ((iff_of_eq point).trans (encoded_member model code second occurrence))

def changeModel {first : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol}
    (encoding : Coding first O) (second : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (same : second.Carrier = first.Carrier) : Coding second O :=
  (Equiv.cast (congrArg (fun carrier => HOL.Ty.denote.{0,w+1} carrier occurrenceType) same)).trans encoding

def initialCoding (Obj : Type uO) (Tm : Obj → Type uT) (Hom : Obj → Obj → Type uH) (O : Type uOcc)
    (other : TypeFamilySemantics.OperatorFamilies.{max uO uT uH uOcc})
    (prior : TypeFamilySemantics.Assignment.{max uO uT uH uOcc}) :
    Coding (HOLFrameDomains.initial Obj Tm Hom O other prior) O :=
  (HOLFrameCoding.parameterCoding (Obj := Obj) (Tm := Tm) (Hom := Hom) O other prior .occurrences).trans Equiv.ulift

#print axioms invalid_absent
#print axioms initialCoding

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLOccurrenceCoding
