import Mettapedia.Languages.OpenTheory.WMFreeSemanticModelBoundary
import Mettapedia.OSLF.Framework.WMCalculusGeneratedFreeReading

/-!
# The boundary of the generated WM reading

The generated reading has its universal strict interpretation into the
observational quotient of the theorem-list model. It cannot interpret
strictly into the unquotiented list model when two named theorem atoms
retain distinct append orders. This positive/negative pair isolates the
separation hypothesis in the free-generation theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory.WMGeneratedFreeBoundary

open Mettapedia.Languages.OpenTheory.WorldModelQueryGSLT
open Mettapedia.Languages.OpenTheory.CoreRulesFixtures
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusReadingMorphism
open Mettapedia.OSLF.Framework.WMCalculusReadingCategory
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
open Mettapedia.OSLF.Framework.WMCalculusFreeSemanticModel
open Mettapedia.OSLF.Framework.WMCalculusGeneratedFreeReading

def theoremListModel (atoms : TheoremAtoms) : LawfulReading where
  State := List Theorem
  Query := Theorem
  Evidence := Prop
  reading := theoremListReading atoms
  laws := theoremListReading_coreLaws atoms

/-- The theorem-list quotient forgets raw ordering but retains exactly
the membership observations, and its state equality is separated. -/
theorem theoremListQuotient_separated (atoms : TheoremAtoms) :
    ObservationSeparated (quotientObject (theoremListModel atoms)) :=
  quotientObject_separated (theoremListModel atoms)

/-- The generated free reading has its unique strict interpretation into
the behaviorally separated theorem-list quotient. -/
theorem generated_to_theoremList_quotient_unique (atoms : TheoremAtoms) :
    Subsingleton (ReadingMorphism generatedReading
      (quotientObject (theoremListModel atoms)).reading) ∧
    Nonempty (ReadingMorphism generatedReading
      (quotientObject (theoremListModel atoms)).reading) := by
  exact ⟨generatedMorphism_subsingleton _
      (theoremListQuotient_separated atoms),
    generatedMorphism_nonempty _
      (theoremListQuotient_separated atoms)⟩

/-- The same strict interpretation cannot land in raw theorem-list
history. The two named revisions are equal in the generated carrier but
different lists in the target, even though their observations agree. -/
theorem no_strict_morphism_to_raw_theoremList
    (atoms : TheoremAtoms)
    (readsBack : atoms.ReadsBack [axiomP, axiomQ]) :
    ¬ Nonempty (ReadingMorphism generatedReading
      (theoremListReading atoms)) := by
  rintro ⟨hom⟩
  let firstTerm : WMTerm .state :=
    .revise (.state (atoms.name axiomP)) (.state (atoms.name axiomQ))
  let secondTerm : WMTerm .state :=
    .revise (.state (atoms.name axiomQ)) (.state (atoms.name axiomP))
  have generatedEqual : generatedReading.denote firstTerm =
      generatedReading.denote secondTerm := by
    rw [generatedReading_denote_state firstTerm,
      generatedReading_denote_state secondTerm]
    apply Quotient.sound
    change stateNormalForm firstTerm = stateNormalForm secondTerm
    simpa [firstTerm, secondTerm, stateNormalForm] using
      (add_comm ({atoms.name axiomP} : Multiset String)
        ({atoms.name axiomQ} : Multiset String))
  have targetEqual :
      (theoremListReading atoms).denote firstTerm =
        (theoremListReading atoms).denote secondTerm := by
    calc
      (theoremListReading atoms).denote firstTerm =
          hom.mapState (generatedReading.denote firstTerm) :=
        (hom.denote_map firstTerm).symm
      _ = hom.mapState (generatedReading.denote secondTerm) :=
        congrArg hom.mapState generatedEqual
      _ = (theoremListReading atoms).denote secondTerm :=
        hom.denote_map secondTerm
  exact (revisionComm_changes_list_keeps_membership atoms readsBack).2.1
    targetEqual

end Mettapedia.Languages.OpenTheory.WMGeneratedFreeBoundary
