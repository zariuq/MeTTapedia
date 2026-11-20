import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunRearrangementGrades
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunRearrangementDomain
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentContextGradeControls

/-!
# Context qualification cannot be read from an inverse-cancelled certificate

The native bounded-count example gives an admitted interchange whose two
runs have different context grades. Following the comparison and its inverse
is the identity in the generated groupoid, but its raw certificate visits
the excluded run. Qualification of every intermediate run therefore does
not descend to that quotient. The empty certificate at the admitted context
is the positive companion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextGradeControls

open _root_.CategoryTheory
open Transport.RunRearrangement
open ContextPlacement DependentFull.Controls

noncomputable def primitive : Generator (helperTransport setting.levels Nat) goodRun badRun := .inr comparison

noncomputable def roundTrip : RawCell (helperTransport setting.levels Nat) goodRun goodRun :=
  (Oriented.toPath (T := helperTransport setting.levels Nat) (.inl primitive)).cons (.inr primitive)

noncomputable def emptyCertificate : RawCell (helperTransport setting.levels Nat) goodRun goodRun :=
  rawIdentity (T := helperTransport setting.levels Nat) goodRun

theorem roundTrip_is_identity : rawToCell roundTrip = 𝟙 (object (helperTransport setting.levels Nat) goodRun) := by
  unfold roundTrip
  rw [rawToCell_cons]
  change generator (helperTransport setting.levels Nat) primitive ≫
      CategoryTheory.Groupoid.inv (generator (helperTransport setting.levels Nat) primitive) = 𝟙 _
  exact CategoryTheory.Groupoid.comp_inv _

theorem empty_is_within : Within (fun run => RunSafe {1} run) emptyCertificate := good_grade

theorem roundTrip_not_within : ¬ Within (fun run => RunSafe {1} run) roundTrip :=
  fun inside => bad_grade inside.1.2

theorem qualification_does_not_descend :
    ¬ ∃ supports : Cell (helperTransport setting.levels Nat) goodRun goodRun → Prop,
      ∀ path : RawCell (helperTransport setting.levels Nat) goodRun goodRun,
        supports (rawToCell path) ↔ Within (fun run => RunSafe {1} run) path := by
  rintro ⟨supports, agrees⟩
  have identityAllowed := (agrees emptyCertificate).mpr empty_is_within
  have loopAllowed : supports (rawToCell roundTrip) := by
    rw [roundTrip_is_identity]
    exact identityAllowed
  exact roundTrip_not_within ((agrees roundTrip).mp loopAllowed)

/-- A valid alternative certificate exists for the identity comparison,
although the particular cancelling detour fails the context qualification. -/
theorem valid_alternative_exists :
    Liftable (fun run => RunSafe {1} run) (rawToCell roundTrip) ∧
      ¬ Within (fun run => RunSafe {1} run) roundTrip := by
  refine ⟨?_, roundTrip_not_within⟩
  rw [roundTrip_is_identity]
  exact liftable_identity good_grade

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextGradeControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextGradeControls.qualification_does_not_descend
