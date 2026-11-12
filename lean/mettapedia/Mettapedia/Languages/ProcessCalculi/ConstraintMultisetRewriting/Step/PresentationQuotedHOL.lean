import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationQuotedEvents
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLRunAdmissionJoin

/-!
# Quoted source execution and the loaded HOL event/path definitions

The binding-aware contextual program uses the same received admission and
path operations as the ordinary occurrence profile. HOL states retain the
whole contextual inventory and declaration frame. The event word retains
the selected equation/context and its preparation witness; final answer
observation is a separate existential readout.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.QuotedHOL

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.Languages.OpenTheory
open QuotedLambda (sig)
open LambdaContextualRung (Srt)
open ProgramBinders Interface QuotedSource QuotedEvents
open HOLPreparedRunEncoding HOLRunSpecialization

local instance : DecidableEq sig.Srt := inferInstanceAs (DecidableEq Srt)

variable (Γ : Ctx sig) (input : HOLRunAdmissionJoin.Input)
  (other : TypeFamilySemantics.OperatorFamilies.{1}) (prior : TypeFamilySemantics.Assignment.{1})

noncomputable def accepts (events : List (RawEvent (step Γ).effectCore))
    (before after : State (program Γ)) : Prop :=
  (input.operations.signature.pathValue (input.model (step Γ).effectCore other prior)
    (input.admittedValue (step Γ).effectCore other prior (step Γ).eventAdmission)
    (wordValue (step Γ).effectCore _ _ (input.runCoding (step Γ).effectCore other prior)
      (input.runAgreement (step Γ).effectCore other prior) events)
    ((input.runCoding (step Γ).effectCore other prior).states.symm (some before))
    ((input.runCoding (step Γ).effectCore other prior).states.symm (some after))).down

theorem accepts_iff_path (events : List (RawEvent (step Γ).effectCore))
    (before after : Object Γ) :
    accepts Γ input other prior events before after ↔
      ∃ path : Quiver.Path before after, word (step Γ).effectCore (step Γ).eventAdmission path = events :=
  input.admitted_path_iff (step Γ).effectCore other prior (step Γ).eventAdmission events before after

theorem preserves_event_word {before after : Object Γ} (path : Quiver.Path before after) :
    accepts Γ input other prior (word (step Γ).effectCore (step Γ).eventAdmission path) before after :=
  (accepts_iff_path Γ input other prior _ before after).mpr ⟨path, rfl⟩

theorem reflects_event_word (events : List (RawEvent (step Γ).effectCore)) (before after : Object Γ)
    (accepted : accepts Γ input other prior events before after) :
    ∃ path : Quiver.Path before after, word (step Γ).effectCore (step Γ).eventAdmission path = events :=
  (accepts_iff_path Γ input other prior events before after).mp accepted

/-- The source reading and loaded run predicate describe the same answers.
The preceding word theorems retain the finer event data before this readout. -/
theorem source_execution_iff_loaded (call answer : Term sig Γ .term) :
    Relation.ReflTransGen (Reduces Γ) (source call) (source answer) ↔
      ∃ (after : Object Γ) (events : List (RawEvent (step Γ).effectCore)),
        accepts Γ input other prior events (initial call) after ∧ Reads (program Γ) after answer := by
  rw [source_path_iff]
  constructor
  · rintro ⟨after, ⟨path⟩, reads⟩
    exact ⟨after, _, preserves_event_word Γ input other prior path, reads⟩
  · rintro ⟨after, events, accepted, reads⟩
    obtain ⟨path, _⟩ := reflects_event_word Γ input other prior events (initial call) after accepted
    exact ⟨after, ⟨path⟩, reads⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.QuotedHOL
