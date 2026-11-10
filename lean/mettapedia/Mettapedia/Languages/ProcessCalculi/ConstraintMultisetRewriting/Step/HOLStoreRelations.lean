import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLStoreSpecialization

/-! # Membership relations preserved by equation-predicate encoding

Equality of encoded stores means equality of equation membership, rather
than equality of list order or duplicate counts. Transported inclusion has
an exact indexed-list characterization.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLStoreRelations

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open HOLFrameCoding

universe w uO uT uH

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

theorem membership_encoded {a : Obj} (store : EquationStore (Tm a)) (x y : Tm a) :
    HOLFrameEncoding.store store (HOLFrameEncoding.encodeTerm x) (HOLFrameEncoding.encodeTerm y) ↔ (x,y) ∈ store := by
  constructor
  · rintro ⟨⟨left,right⟩, member, first, second⟩
    have leftEq : x = left := HOL.IndexedCarrier.encode_injective Tm a first
    have rightEq : y = right := HOL.IndexedCarrier.encode_injective Tm a second
    subst x y
    exact member
  · intro member
    exact ⟨(x,y), member, rfl, rfl⟩

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (X : Frames Tm Hom) (code : Coding model Obj Tm Hom)

theorem coded_member {a : Obj} (store : EquationStore (Tm a)) (x y : Tm a) :
    (storeValue model code store (code.terms.symm (HOLFrameEncoding.encodeTerm x))
      (code.terms.symm (HOLFrameEncoding.encodeTerm y))).down ↔ (x,y) ∈ store := by
  simp only [storeValue, predicateValue, Equiv.apply_symm_apply]
  exact membership_encoded store x y

theorem value_equal_iff {a : Obj} (first second : EquationStore (Tm a)) :
    storeValue model code first = storeValue model code second ↔ ∀ equation, equation ∈ first ↔ equation ∈ second := by
  constructor
  · intro same equation
    have point := congrArg ULift.down (congrFun (congrFun same
      (code.terms.symm (HOLFrameEncoding.encodeTerm equation.1)))
      (code.terms.symm (HOLFrameEncoding.encodeTerm equation.2)))
    exact (coded_member model code first equation.1 equation.2).symm.trans
      ((iff_of_eq point).trans (coded_member model code second equation.1 equation.2))
  · intro agrees
    funext x y
    apply ULift.ext
    apply propext
    change HOLFrameEncoding.store first (code.terms x) (code.terms y) ↔ HOLFrameEncoding.store second (code.terms x) (code.terms y)
    constructor
    · rintro ⟨equation, member, left, right⟩
      exact ⟨equation, (agrees equation).mp member, left, right⟩
    · rintro ⟨equation, member, left, right⟩
      exact ⟨equation, (agrees equation).mpr member, left, right⟩

theorem transported_inclusion_iff {a m : Obj} (extension : Hom a m)
    (old : EquationStore (Tm a)) (information : EquationStore (Tm m)) :
    (∀ x y, (storeValue model code old x y).down →
      (storeValue model code information
        (actionValue model X code (code.morphisms.symm (HOLFrameEncoding.encodeHom extension)) x)
        (actionValue model X code (code.morphisms.symm (HOLFrameEncoding.encodeHom extension)) y)).down) ↔
      ∀ equation ∈ old, (X.act extension equation.1, X.act extension equation.2) ∈ information := by
  constructor
  · intro contains equation member
    have result := contains (code.terms.symm (HOLFrameEncoding.encodeTerm equation.1))
      (code.terms.symm (HOLFrameEncoding.encodeTerm equation.2))
      ((coded_member model code old equation.1 equation.2).mpr member)
    apply (membership_encoded information (X.act extension equation.1) (X.act extension equation.2)).mp
    simpa only [storeValue, predicateValue, actionValue, Equiv.apply_symm_apply,
      HOLFrameEncoding.act_encoded] using result
  · intro contains x y member
    change HOLFrameEncoding.store old (code.terms x) (code.terms y) at member
    obtain ⟨equation, member, left, right⟩ := member
    simp only [storeValue, predicateValue, actionValue, Equiv.apply_symm_apply, left, right,
      HOLFrameEncoding.act_encoded]
    exact (membership_encoded information (X.act extension equation.1) (X.act extension equation.2)).mpr
      (contains equation member)

#print axioms membership_encoded
#print axioms value_equal_iff
#print axioms transported_inclusion_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLStoreRelations
