import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BorrowedQuery
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.NativeMatchControls

/-! # An actual borrowed binder row reaches an actual matching run -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BorrowedQueryControls

open Mettapedia.Machines.ResourceOwnership
open Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone
open Mettapedia.Machines.Cursor
open SourceLanguage.Elaboration SourceLanguage.Toolkit
open SourceLanguage.NativeQuery

def handle : BorrowedQuery.Address Nat Nat := ⟨7, 20, 3⟩
def lease : Lease Nat Nat Nat := ⟨handle, 1, .shared⟩
def frontier : Frontier Nat Nat Nat := {lease}
def stamp : RequestBorrow.Stamp Nat := ⟨7, 3⟩

def heap : Heap (BorrowedQuery.Address Nat Nat) BorrowedQuery.SourceRow where
  lookup address := if address = handle then some ⟨MatchControls.row, ∅, 8⟩ else none
  allocated := {handle}
  allocated_iff address := by simp
  closed address cell found next member := by
    by_cases same : address = handle
    · simp only [if_pos same] at found
      obtain rfl := Option.some.inj found
      simp at member
    · simp only [if_neg same] at found
      cases found

def store : StampedSnapshots.Store BorrowedQuery.SourceRow := StampedSnapshots.add StampedSnapshots.empty MatchControls.row

def machine : BorrowedQuery.Native :=
  ⟨(StampedSnapshots.apply (StampedSnapshots.initial store) (.openReader 0)).1,
    StampedSnapshots.valid_apply _ (StampedSnapshots.valid_initial store) (.openReader 0)⟩

theorem delivered : (StampedSnapshots.apply machine.val (.read 0)).2 = .value 0 MatchControls.row := rfl

theorem actual_borrowed_lambda_match :
    (Boundary.perform machine (Boundary.request stamp frontier 1 handle 0 true true)).1 =
        .observed (.value 0 MatchControls.row) ∧
      ∃ run : (RuleSyntax.step MatchKernel.X Nat MatchKernel.E MatchKernel.program).toStep.Run
          (MatchKernel.initial 0 [] MatchControls.pattern MatchControls.pattern MatchControls.row),
        run.word.length = 1 := by
  have valid : ValidRoots heap (BorrowedRoots.roots frontier) := by
    intro pair member
    have same : pair = (1, handle) := by
      simpa only [BorrowedRoots.roots, frontier, lease, Multiset.toFinset_singleton,
        Finset.image_singleton, Finset.mem_singleton] using member
    rw [same]
    exact Finset.mem_singleton_self _
  have authorized : Authorized frontier 1 handle := by
    simp only [Authorized]
    decide
  have found : heap.lookup handle = some ⟨MatchControls.row, ∅, 8⟩ := by simp [heap]
  have reachable : Live heap ({((), handle)} : Roots Unit (BorrowedQuery.Address Nat Nat)) handle :=
    live_of_root heap {((), handle)} (owner := ()) (Finset.mem_singleton_self _) (by simp [heap])
  obtain ⟨reply, _, _, run, length, _⟩ := BorrowedQuery.native_row_handoff machine 0 0 MatchControls.row delivered
    heap frontier valid 1 handle handle authorized stamp rfl ⟨MatchControls.row, ∅, 8⟩ found rfl reachable
    0 [] MatchControls.pattern MatchControls.pattern MatchControls.binding_match_live
  exact ⟨reply, run, length⟩

#print axioms delivered
#print axioms actual_borrowed_lambda_match

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BorrowedQueryControls
