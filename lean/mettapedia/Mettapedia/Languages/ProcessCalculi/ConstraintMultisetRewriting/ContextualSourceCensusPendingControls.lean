import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceCensus
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalSourceControls

/-!
# A pending published condition changes the complete source census

The actual earlier source firing published x with x = 1 still pending.
The full candidate census rejects a take of 2. Erasing the row's condition
would let its displayed schema match 2, even though the conditional row
cannot. The census therefore uses the original source problem rather than
only the visible value.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceCensus.PendingControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualConditionalRows
open ContextualConditionalClauses.SourceControls (first nextLocals nextCaptures nextFamily wrongRule)
open ContextualConditionalExecution.Controls (base queries captures constantAt)
open SchematicReach.Controls (symbol)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (result : base.Srt) : DecidableEq (base.Op result) := by
  change DecidableEq (SchematicReach.Controls.DataOperator ⊕ Operator
    (SchematicReach.spaceDeclaration SchematicReach.Controls.dataSignature () (Name := Nat)) result)
  infer_instance
local instance : DecidableEq first.firing.update.Variables := first.firing.update.equality
local instance : DecidableEq first.firing.target.Names := first.firing.target.equality

def primary : Request nextLocals first.firing.target :=
  ⟨Nat, queries, inferInstance, ⟨wrongRule, [true], rfl⟩, [2], by decide +kernel, rfl, by decide +kernel⟩

theorem the_pending_condition_is_in_the_complete_census : primary.CertifiedEmpty := by
  have patterned : ∀ chosen ∈ primary.candidates,
      ContextualPatternFragment.checkProblem (primary.information chosen) = true := by decide +kernel
  have positions : ∀ chosen ∈ primary.candidates,
      (primary.selection chosen).taken = [1] := by decide +kernel
  refine ⟨fun chosen present => primary.rejected_of_no_admission chosen present
    ((ContextualPatternFragment.checkProblem_iff _).mp (patterned chosen present)) ?_⟩
  intro admitted
  have normalized : primary.selection chosen = ContextualConditionalClauses.SourceControls.secondSelection := by
    change Selection.mk (List.ofFn chosen.1) [] [2] = ⟨[1], [], [2]⟩
    exact congrArg (fun taken => Selection.mk taken [] [2]) (positions chosen present)
  rw [normalized] at admitted
  exact ContextualConditionalClauses.SourceControls.the_source_consumer_cannot_ignore_the_producers_condition admitted

def withoutCondition : Row nextLocals nextCaptures [] () :=
  ⟨(first.firing.target.rows 1).value, []⟩

theorem the_displayed_schema_alone_would_match_two
    {Next : Type} (next : Next → MetaArity base) (candidate : Assignment nextCaptures next) :
    Matches nextLocals nextCaptures candidate (symbol 2) withoutCondition := by
  refine ⟨Extension.identity next, (fun name => constantAt next 2 (nextLocals name)), ?_, ?_⟩
  · intro equation member
    cases member
  · rfl

theorem the_actual_conditional_row_refuses_two
    {Next : Type} (next : Next → MetaArity base) (candidate : Assignment nextCaptures next) :
    ¬ Matches nextLocals nextCaptures candidate (symbol 2) (first.firing.target.rows 1) :=
  ContextualConditionalClauses.SourceControls.the_first_source_answer_refuses_two next candidate

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceCensus.PendingControls
