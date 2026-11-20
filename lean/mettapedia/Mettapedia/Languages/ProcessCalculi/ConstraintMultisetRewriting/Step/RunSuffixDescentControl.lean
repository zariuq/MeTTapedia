import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunSuffixComposition
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunRearrangementControls
import Mathlib.CategoryTheory.SingleObj

/-!
# Raw continuation extension does not automatically descend through cancellation

The free comparison groupoid retains similarity generators, including an
explicit identity similarity. Extending a forward/backward raw path inserts
a round-trip similarity correction. Even on an empty continuation this can
be a nonidentity raw certificate, although the original path cancels.

This diagnoses the chosen certificate presentation and action. It is not an
obstruction to the calculus, nor a claim that an appropriately coherent
quotient or weak action cannot be constructed. Event and contextual
observations are separate from raw certificate equality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.RunSuffixDescentControl

open _root_.CategoryTheory
open Transport.RunRearrangement
open InterchangeTraceControls (P T)

def emptyRun : P.Run [] := .nil []

def identitySimilarity : Generator T emptyRun emptyRun := .inl (Transport.SimilarityWitness.refl emptyRun)

def roundTrip : RawCell T emptyRun emptyRun :=
  (Oriented.toPath (.inl identitySimilarity)).cons (.inr identitySimilarity)

def extended : Cell T emptyRun emptyRun := rightCell roundTrip (.nil [])

theorem original_cancels : rawToCell roundTrip = 𝟙 (object T emptyRun) := by
  unfold roundTrip
  rw [rawToCell_cons]
  change generator T identitySimilarity ≫ CategoryTheory.Groupoid.inv (generator T identitySimilarity) = _
  exact CategoryTheory.Groupoid.comp_inv _

def signedGenerators : Object T [] ⥤q SingleObj (Multiplicative Int) where
  obj _ := SingleObj.star _
  map witness := match witness with
    | .inl _ => Multiplicative.ofAdd 1
    | .inr _ => Multiplicative.ofAdd 0

def signedFunctor : Groupoid T [] ⥤ SingleObj (Multiplicative Int) := interpret T signedGenerators

def weight {first second : P.Run []} (cell : Cell T first second) : Int :=
  Multiplicative.toAdd (signedFunctor.map cell)

theorem weight_generator {first second : P.Run []} (witness : Generator T first second) :
    weight (generator T witness) = (match witness with | .inl _ => 1 | .inr _ => 0) := by
  have same := Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec signedGenerators) witness
  exact congrArg Multiplicative.toAdd same

theorem weight_identity (run : P.Run []) : weight (𝟙 (object T run)) = 0 := by
  unfold weight
  rw [signedFunctor.map_id]
  rfl

theorem weight_comp {first middle last : P.Run []} (one : Cell T first middle) (two : Cell T middle last) :
    weight (one ≫ two) = weight one + weight two := by
  unfold weight
  rw [signedFunctor.map_comp]
  exact Int.add_comm _ _

theorem weight_inverse {first second : P.Run []} (cell : Cell T first second) :
    weight (CategoryTheory.Groupoid.inv cell) = - weight cell := by
  unfold weight
  rw [CategoryTheory.Groupoid.inv_eq_inv, signedFunctor.map_inv, SingleObj.inv_as_inv]
  rfl

theorem extended_has_extra_similarity : weight extended = 1 := by
  simp only [extended, roundTrip, Oriented.toPath, rawIdentity,
    rightCell, rightEdge, Oriented.boundary, identitySimilarity]
  rfl

theorem extended_not_identity : extended ≠ 𝟙 (object T emptyRun) := by
  intro same
  have measured := congrArg weight same
  rw [extended_has_extra_similarity, weight_identity] at measured
  exact (by decide : (1 : Int) ≠ 0) measured

theorem no_raw_suffix_descent :
    ¬ ∃ operation : Cell T emptyRun emptyRun → Cell T emptyRun emptyRun,
      operation (𝟙 (object T emptyRun)) = 𝟙 (object T emptyRun) ∧
        operation (rawToCell roundTrip) = extended := by
  rintro ⟨operation, identity, extension⟩
  rw [original_cancels, identity] at extension
  exact extended_not_identity extension.symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.RunSuffixDescentControl

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.RunSuffixDescentControl.no_raw_suffix_descent
