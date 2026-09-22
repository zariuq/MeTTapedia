import Mettapedia.OSLF.Framework.WMCalculusBehavioralFamilyTransport
import Mettapedia.Languages.OpenTheory.WorldModelObservationalQuotient

/-!
# Theorem-list states separate raw and native observational equality

Two differently ordered theorem lists can answer every query identically.
They inhabit the WM behavioral-equality native predicate, and their quotient
classes are literally equal, while the raw-list diagonal rejects them. This
is a concrete control against treating observation as raw identity or as an
unqualified dependent identity former.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory.WorldModelNativeEqualityBoundary

open _root_.CategoryTheory
open Mettapedia.Languages.OpenTheory.WorldModelQueryGSLT
open Mettapedia.Languages.OpenTheory.CoreRulesFixtures
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
open Mettapedia.OSLF.Framework.WMCalculusNativeObservationalEquality
open Mettapedia.OSLF.Framework.WMCalculusBehavioralFamilyTransport

private abbrev wmLanguage : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef :=
  wmExtVertexLanguageDefWithCong wmExtVertexMinimal

private def stateStage : Opposite (ConstructorObj wmLanguage) :=
  Opposite.op (ConstructorObj.mk ⟨"State", by decide⟩)

private def forwardList (atoms : TheoremAtoms) : List Theorem :=
  (theoremListReading atoms).denote
    (WMTerm.revise (.state (atoms.name axiomP)) (.state (atoms.name axiomQ)))

private def reverseList (atoms : TheoremAtoms) : List Theorem :=
  (theoremListReading atoms).denote
    (WMTerm.revise (.state (atoms.name axiomQ)) (.state (atoms.name axiomP)))

/-- A concrete pair belongs to the native behavioral predicate but not
the raw diagonal. Its quotient classes are equal. -/
theorem theoremList_observational_not_raw
    (atoms : TheoremAtoms)
    (readsBack : atoms.ReadsBack [axiomP, axiomQ]) :
    (forwardList atoms, reverseList atoms) ∈
        (behavioralEquality (theoremListReading atoms)).obj stateStage ∧
      (forwardList atoms, reverseList atoms) ∉
        (rawDiagonal (List Theorem)).obj stateStage ∧
      classOf (theoremListReading atoms) (forwardList atoms) =
        classOf (theoremListReading atoms) (reverseList atoms) := by
  obtain ⟨_, distinct, agree⟩ :=
    revisionComm_changes_list_keeps_membership atoms readsBack
  exact ⟨agree, distinct,
    (classOf_eq_iff_agree (theoremListReading atoms) _ _).2 agree⟩

/-- The entire native predicates differ for the theorem-list backend; the
quotient diagonal is the correct equality readout. -/
theorem theoremList_behavioralEquality_ne_rawDiagonal
    (atoms : TheoremAtoms)
    (readsBack : atoms.ReadsBack [axiomP, axiomQ]) :
    behavioralEquality (theoremListReading atoms) ≠
      rawDiagonal (List Theorem) := by
  obtain ⟨_, distinct, agree⟩ :=
    revisionComm_changes_list_keeps_membership atoms readsBack
  exact behavioralEquality_ne_rawDiagonal_of_distinct_agree
    (theoremListReading atoms) stateStage distinct agree

/-- The same two histories transport every dependent family over observable
state classes, but not arbitrary dependent families over raw histories. -/
theorem theoremList_dependent_transport_boundary
    (atoms : TheoremAtoms)
    (readsBack : atoms.ReadsBack [axiomP, axiomQ]) :
    Nonempty (∀ P : ObsState (theoremListReading atoms) → Type,
      P (classOf (theoremListReading atoms) (forwardList atoms)) →
        P (classOf (theoremListReading atoms) (reverseList atoms))) ∧
      ¬ Nonempty (∀ P : List Theorem → Type,
        P (forwardList atoms) → P (reverseList atoms)) := by
  obtain ⟨_, distinct, agree⟩ :=
    revisionComm_changes_list_keeps_membership atoms readsBack
  exact distinct_agree_transport_boundary (theoremListReading atoms)
    distinct agree

end Mettapedia.Languages.OpenTheory.WorldModelNativeEqualityBoundary
