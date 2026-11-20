import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.Boundary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.ContextualIndex

/-!
# One actual row links cursor delivery, retained storage and source execution

The same complete binding-aware row appears in the stamped cursor reply,
physical cell, index problem and actual template-match firing. The source
unification problem derives firing admission; no output-adequacy hypothesis
is supplied. Physical row decoding and the initial heap/cursor relation are
the native implementation boundary. Captured-answer reopening is a distinct
source policy, not silently identified with generative row copying.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BorrowedQuery

open Mettapedia.Machines.ResourceOwnership
open Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone
open Mettapedia.Machines.Cursor
open SourceLanguage.Elaboration SourceLanguage.Toolkit

abbrev SourceRow := SourceLanguage.Row mkeys [] ()
abbrev Native := CursorProtocol.Native SourceRow
abbrev Address (Provider Resource : Type) := Handle Provider Resource

variable {ProviderID Resource Holder : Type}
  [DecidableEq ProviderID] [DecidableEq Resource] [DecidableEq Holder]

theorem native_row_handoff
    (machine : Native) (reader occurrence : Nat) (row : SourceRow)
    (delivered : (StampedSnapshots.apply machine.val (.read reader)).2 = .value occurrence row)
    (heap : Heap (Address ProviderID Resource) SourceRow) (frontier : Frontier ProviderID Resource Holder)
    (valid : ValidRoots heap (BorrowedRoots.roots frontier))
    (holder : Holder) (view address : Address ProviderID Resource) (authorized : Authorized frontier holder view)
    (current : RequestBorrow.Stamp ProviderID) (live : BorrowedViews.stamp view = current)
    (cell : Cell (Address ProviderID Resource) SourceRow) (found : heap.lookup address = some cell) (payload : cell.value = row)
    (reachable : Live heap ({((), view)} : Roots Unit (Address ProviderID Resource)) address)
    (scope : Nat) (store : List (SourceLanguage.Constraint mkeys [] ())) (pattern template : MData)
    (solvable : SourceLanguage.Solvable (store ++ SourceLanguage.rowUse scope row pattern)) :
    (Boundary.perform machine (Boundary.request current frontier holder view reader true true)).1 =
        .observed (.value occurrence row) ∧
      ((collect heap (BorrowedRoots.roots frontier)).lookup address).map Cell.value = some row ∧
      ContextualIndex.permits pattern row.atom = true ∧
      ∃ run : (RuleSyntax.step SourceLanguage.NativeQuery.MatchKernel.X Nat
          SourceLanguage.NativeQuery.MatchKernel.E SourceLanguage.NativeQuery.MatchKernel.program).toStep.Run
          (SourceLanguage.NativeQuery.MatchKernel.initial scope store pattern template row),
        run.word.length = 1 ∧
          run.last = (SourceLanguage.NativeQuery.MatchKernel.firing scope store pattern template row).result
            SourceLanguage.NativeQuery.MatchKernel.X
              (SourceLanguage.NativeQuery.MatchKernel.initial scope store pattern template row) := by
  have native := Boundary.current_read_is_the_real_step current frontier holder view reader authorized live machine
  have storage := BorrowedRoots.authorized_descendant_survives_collection heap frontier valid
    holder view address authorized reachable
  have admitted := SourceLanguage.NativeQuery.MatchKernel.admitted_of_source scope store pattern template row solvable
  refine ⟨native.trans (congrArg CursorProtocol.Reply.observed delivered), ?_,
    ContextualIndex.row_problem_survives scope store pattern row solvable, ?_⟩
  · rw [storage, found]
    exact congrArg some payload
  · exact ⟨.cons (SourceLanguage.NativeQuery.MatchKernel.firing scope store pattern template row) admitted
      (.nil _), rfl, rfl⟩

#print axioms native_row_handoff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.BorrowedQuery
