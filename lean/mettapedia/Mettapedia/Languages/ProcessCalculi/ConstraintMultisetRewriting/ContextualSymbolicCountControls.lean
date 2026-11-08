import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSymbolicCountQueries
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeGuardControls

/-!
# A count compiled at its clause's own information cut

The entry row is box(X). The first clause tells X=1. Its count of box(1)
is one, and the compiled actual-data table with its finite count check
has exactly that verdict. Changing the requested count to zero refuses.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSymbolicCountControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows ContextualConditionalGuards ContextualPredicateQueryAdmission
open ContextualNativeGuardControls.OwnEquations
open ContextualPrefixPublicationControls
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

theorem source_count_is_one :
    Ask (body.native.entryCutAt watched).view.locals (body.native.entryCutAt watched).view.problem
      (body.native.entryCutAt watched).view.rows (body.native.entryCutAt watched).view.world (.count (box (symbol 1)) 1) := by
  intro Future future candidate model
  rw [(body.native.entry_cut_at_compare shapes resources watched).1] at model
  change ContextualResidual.Models candidate [(observe secondX, observe (symbol 1))] at model
  have equation := model _ (List.mem_singleton_self _)
  change observe (instantiate candidate secondX) = observe (symbol (decl := future) 1) at equation
  have same := observe_injective equation
  change (region _ _ _ _ (box (symbol 1))).card = 1
  rw [body.native.entry_cut_count watched candidate (box (symbol 1))]
  change (region none candidate body.native.sourceGuardInputs {9} (box (symbol 1))).card + 0 = 1
  have matched : Matches none result.declarations candidate (box (symbol 1)) (body.native.sourceGuardInputs 9) := by
    have row : body.native.sourceGuardInputs 9 = ofStored none result.declarations (.shared (box secondX)) := by
      with_unfolding_all rfl
    rw [row, ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff]
    change box (symbol (decl := future) 1) = box (instantiate candidate secondX)
    rw [same]
  have singleton : region none candidate body.native.sourceGuardInputs {9} (box (symbol 1)) = {9} := by
    ext occurrence
    rw [mem_region]
    constructor
    · exact And.left
    · intro member
      have equal : occurrence = 9 := Finset.mem_singleton.mp member
      subst occurrence
      exact ⟨member, matched⟩
  rw [singleton]
  rfl

noncomputable def table := body.native.nativeCountTable watched ∅ [] [] (box (symbol 1))
  ((body.native.entryCutAt watched).taken.image some)

theorem the_compiled_count_is_admitted :
    AskData (body.native.nativeBindingInformation ∅ [] [])
      (table.query (body.native.nativeCountPredicate watched (box (symbol 1)) ((body.native.entryCutAt watched).taken.image some)))
      (nativeLabels body.native.guardNativeBank (body.native.nativeBindingState ∅)) (body.native.nativeBindingState ∅).present ∧
    AskData (body.native.nativeBindingInformation ∅ [] [])
      (body.native.nativeCountCheckQuery watched (box (symbol 1)) table 1)
      (nativeLabels body.native.guardNativeBank (body.native.nativeBindingState ∅)) (body.native.nativeBindingState ∅).present :=
  (body.native.native_entry_count_iff watched shapes resources consistent ∅ [] [] (box (symbol 1)) 1).mp source_count_is_one

theorem the_wrong_compiled_count_is_refused :
    ¬ AskData (body.native.nativeBindingInformation ∅ [] [])
      (body.native.nativeCountCheckQuery watched (box (symbol 1)) table 0)
      (nativeLabels body.native.guardNativeBank (body.native.nativeBindingState ∅)) (body.native.nativeBindingState ∅).present := by
  intro accepted
  have source := (body.native.native_entry_count_from_table_iff watched shapes resources consistent ∅ [] []
    (box (symbol 1)) table 0 the_compiled_count_is_admitted.1).mpr accepted
  have model : ContextualResidual.Models (secondModel none) (body.native.entryCutAt watched).view.problem := by
    rw [(body.native.entry_cut_at_compare shapes resources watched).1]
    change ContextualResidual.Models (secondModel none) [(observe secondX, observe (symbol 1))]
    intro equation member
    have only := List.mem_singleton.mp member
    subst equation
    rfl
  have zero := source Empty none (secondModel none) model
  have one := source_count_is_one Empty none (secondModel none) model
  change (region _ _ _ _ _).card = 0 at zero
  change (region _ _ _ _ _).card = 1 at one
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSymbolicCountControls
