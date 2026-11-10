import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLStoreSpecialization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFrameEncodingControls

/-! # Direction, validity and observation boundaries of loaded store operations

The image of a concrete equation has its two endpoints in the correct order.
Empty-store typing does not invent a valid object. Predicate representation
forgets duplicate constraints; reconstructing the original list requires
additional retained data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLStoreControls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Logic.HOL.IndexedCarrier.Controls (family)
open HOLFrameEncoding.Controls (frame maps)
open HOLFrameCoding

def source : EquationStore (family true) := [((1 : Nat), (2 : Nat))]
def first : HOLFrameEncoding.Terms family := HOLFrameEncoding.encodeTerm (a := true) (2 : Nat)
def second : HOLFrameEncoding.Terms family := HOLFrameEncoding.encodeTerm (a := true) (3 : Nat)

theorem concrete_image (other : TypeFamilySemantics.OperatorFamilies.{0})
    (prior : TypeFamilySemantics.Assignment.{0}) :
    ∃ (actual : HOL.HenkinModel.{0,0,1} AtomicTy Symbol) (code : Coding actual Bool family maps),
      (actual.constDen HOLLoadedMapStore.symbol (actionValue actual frame code)
        (code.morphisms.symm (HOLFrameEncoding.encodeHom (Hom := maps) (a := true) (b := true) Nat.succ))
        (storeValue actual code source) (code.terms.symm first) (code.terms.symm second)).down ∧
      ¬(actual.constDen HOLLoadedMapStore.symbol (actionValue actual frame code)
        (code.morphisms.symm (HOLFrameEncoding.encodeHom (Hom := maps) (a := true) (b := true) Nat.succ))
        (storeValue actual code source) (code.terms.symm second) (code.terms.symm first)).down := by
  obtain ⟨actual, same, full, equations⟩ := HOLFrameDomains.loaded_model_exists Bool family maps Nat other prior
  let code := (initialCoding (Obj := Bool) (Tm := family) (Hom := maps) Nat other prior).changeModel actual same
  refine ⟨actual, code, ?_, ?_⟩
  · apply (HOLStoreSpecialization.finite_transport_iff actual frame code full equations
      (a := true) (b := true) Nat.succ source first second).mpr
    exact ⟨((2 : Nat), (3 : Nat)), List.mem_singleton_self _, rfl, rfl⟩
  · intro claimed
    obtain ⟨pair, member, wrong, _⟩ :=
      (HOLStoreSpecialization.finite_transport_iff actual frame code full equations
        (a := true) (b := true) Nat.succ source second first).mp claimed
    have samePair : pair = ((2 : Nat), (3 : Nat)) := List.mem_singleton.mp member
    subst pair
    have impossible : (3 : Nat) = 2 :=
      Mettapedia.Logic.HOL.IndexedCarrier.encode_injective family true wrong
    omega

theorem empty_store_not_object_certificate (other : TypeFamilySemantics.OperatorFamilies.{0})
    (prior : TypeFamilySemantics.Assignment.{0}) :
    ∃ (actual : HOL.HenkinModel.{0,0,1} AtomicTy Symbol) (code : Coding actual Bool family maps),
      (actual.constDen HOLLoadedStore.symbol (termsValue actual code) (code.objects.symm none)
        (predicateValue actual code (fun _ _ => False))).down ∧
      ¬HOLFrameEncoding.objects (Obj := Bool) none := by
  obtain ⟨actual, same, full, equations⟩ := HOLFrameDomains.loaded_model_exists Bool family maps Nat other prior
  let code := (initialCoding (Obj := Bool) (Tm := family) (Hom := maps) Nat other prior).changeModel actual same
  refine ⟨actual, code, ?_, ?_⟩
  · exact (HOLStoreSpecialization.typed_raw_iff actual code full equations none (fun _ _ => False)).mpr
      (fun _ _ impossible => False.elim impossible)
  · exact not_false

theorem duplicates_have_same_predicate (equation : family true × family true) :
    HOLFrameEncoding.store [equation, equation] = HOLFrameEncoding.store [equation] := by
  funext first second
  simp [HOLFrameEncoding.store]

theorem original_list_not_recoverable :
    ¬∃ recover : (HOLFrameEncoding.Terms family → HOLFrameEncoding.Terms family → Prop) → EquationStore (family true),
      ∀ store, recover (HOLFrameEncoding.store store) = store := by
  rintro ⟨recover, roundtrip⟩
  have same := congrArg recover (duplicates_have_same_predicate ((0 : Nat), (0 : Nat)))
  rw [roundtrip, roundtrip] at same
  have lengths := congrArg List.length same
  cases lengths

#print axioms concrete_image
#print axioms empty_store_not_object_certificate
#print axioms original_list_not_recoverable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLStoreControls
