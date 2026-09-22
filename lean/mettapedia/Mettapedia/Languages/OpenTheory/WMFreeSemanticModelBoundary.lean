import Mettapedia.Languages.OpenTheory.WorldModelQueryGSLT
import Mettapedia.OSLF.Framework.WMCalculusFreeSemanticModel
import Mettapedia.OSLF.Framework.WMCalculusReadingMorphism

/-!
# Semantic separation is not strict initiality of WM readings

The multiset reading separates closed WM terms, but a target backend may
have noncommutative raw revision while satisfying all WM observation laws.
Consequently the multiset reading cannot be initial in the category whose
arrows preserve raw state operations strictly. The OpenTheory theorem-list
reading gives a concrete counterexample: append remembers order even though
membership observations do not.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory.WMFreeSemanticModelBoundary

open Mettapedia.Languages.OpenTheory.WorldModelQueryGSLT
open Mettapedia.Languages.OpenTheory.CoreRulesFixtures
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusReadingMorphism
open Mettapedia.OSLF.Framework.WMCalculusFreeSemanticModel

/-- There is no strict WM-reading morphism from the commutative multiset
separator to a theorem-list reading whose two named atoms retain distinct
raw list order. Both readings still satisfy the WM core observation laws. -/
theorem no_strict_morphism_from_free (atoms : TheoremAtoms)
    (readsBack : atoms.ReadsBack [axiomP, axiomQ]) :
    ¬ Nonempty (ReadingMorphism freeReading (theoremListReading atoms)) := by
  rintro ⟨hom⟩
  let firstTerm : WMTerm .state :=
    .revise (.state (atoms.name axiomP)) (.state (atoms.name axiomQ))
  let secondTerm : WMTerm .state :=
    .revise (.state (atoms.name axiomQ)) (.state (atoms.name axiomP))
  have freeEqual : freeReading.denote firstTerm =
      freeReading.denote secondTerm := by
    rw [freeReading_denote_state firstTerm,
      freeReading_denote_state secondTerm]
    simpa [firstTerm, secondTerm, stateNormalForm] using
      (add_comm ({atoms.name axiomP} : Multiset String)
        ({atoms.name axiomQ} : Multiset String))
  have targetEqual :
      (theoremListReading atoms).denote firstTerm =
        (theoremListReading atoms).denote secondTerm := by
    calc
      (theoremListReading atoms).denote firstTerm =
          hom.mapState (freeReading.denote firstTerm) :=
        (hom.denote_map firstTerm).symm
      _ = hom.mapState (freeReading.denote secondTerm) :=
        congrArg hom.mapState freeEqual
      _ = (theoremListReading atoms).denote secondTerm :=
        hom.denote_map secondTerm
  exact (revisionComm_changes_list_keeps_membership atoms readsBack).2.1
    targetEqual

end Mettapedia.Languages.OpenTheory.WMFreeSemanticModelBoundary
