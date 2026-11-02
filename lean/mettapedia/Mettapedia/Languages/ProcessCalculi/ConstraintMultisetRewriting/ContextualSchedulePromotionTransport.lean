import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchedulePromotion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPathInclusions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrincipalAsks
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedFrameAsks

/-!
# Stored schedule questions transport without importing later effects

Each question carries its original equation prefix and row world. Capture
substitution preserves its ask; an injective declaration extension or a
principal answer for that same question reflects it too. Actual solver-helper
inclusion followed by a later source path is such an extension. This moves
the original question into the later declaration family while retaining the
earlier equations and occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchedulePromotion

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualGuardMatching

variable {S : Signature} {Local O : Type} {locals : Local → MetaArity S}
  {Γ : Ctx S} {sort : S.Srt}

namespace Question

def map (question : Question locals (O := O) Γ sort) {Next : Type}
    {next : Next → MetaArity S} (change : Assignment question.declarations next) :
    Question locals (O := O) Γ sort where
  Names := Next
  declarations := next
  equations := ContextualFrameUnifier.mapProblem change question.equations
  rows occurrence := (question.rows occurrence).map locals change
  world := question.world
  check := question.check.map (instantiate change)

theorem holds_map (question : Question locals (O := O) Γ sort) {Next : Type}
    {next : Next → MetaArity S} (change : Assignment question.declarations next)
    (holds : question.Holds locals) : (question.map change).Holds locals :=
  ContextualGuardSemantics.Ask.transport locals holds change

theorem holds_extension_iff (question : Question locals (O := O) Γ sort)
    (extension : Extension question.declarations) :
    (question.map extension.assignment).Holds locals ↔ question.Holds locals :=
  ContextualGuardSemantics.Ask.extension_iff locals extension question.equations question.rows
    question.world question.check

theorem holds_principal_iff (question : Question locals (O := O) Γ sort) {Next : Type}
    {next : Next → MetaArity S} (answer : Assignment question.declarations next)
    (principal : ContextualFrameUnifier.Principal question.equations answer) :
    (question.map answer).Holds locals ↔ question.Holds locals :=
  ContextualGuardSemantics.Ask.principal_transport_iff locals question.equations answer principal
    question.rows question.world question.check

end Question

theorem checked_reframe_iff (questions : List (Question locals (O := O) Γ sort))
    (extensions : ∀ question : Question locals (O := O) Γ sort, Extension question.declarations) :
    Checked locals (questions.map fun question => question.map (extensions question).assignment) ↔
      Checked locals questions := by
  simp only [Checked, List.forall_mem_map, Question.holds_extension_iff]

variable [DecidableEq O] [DecidableEq Local]
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

namespace Prepared

variable {before after : Endpoint locals O Γ sort}

def questionAt (prepared : Prepared locals before)
    (check : Check (Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort))
    (later : Quiver.Path prepared.target after) : Question locals (O := O) Γ sort :=
  (prepared.question check).map
    ((ContextualComputedFreshFrame.declarationExtension prepared.update).trans
      (ContextualExecution.pathExtension later)).assignment

/-- A later declaration family may host the question; its later equations
and resource effects do not become assumptions of that earlier question. -/
theorem questionAt_holds_iff (prepared : Prepared locals before)
    (check : Check (Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort))
    (later : Quiver.Path prepared.target after) :
    (prepared.questionAt check later).Holds locals ↔ (prepared.question check).Holds locals :=
  Question.holds_extension_iff _ _

theorem questionAt_keeps_original_world (prepared : Prepared locals before)
    (check : Check (Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort))
    (later : Quiver.Path prepared.target after) :
    (prepared.questionAt check later).world = before.inventory.configuration.present := rfl

theorem questionAt_keeps_original_problem (prepared : Prepared locals before)
    (check : Check (Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort))
    (later : Quiver.Path prepared.target after) :
    (prepared.questionAt check later).equations =
      ContextualFrameUnifier.mapProblem
        ((ContextualComputedFreshFrame.declarationExtension prepared.update).trans
          (ContextualExecution.pathExtension later)).assignment
        (ContextualActivatedStep.problem locals before.declarations before.occupied prepared.selection
          prepared.rule before.inventory.rows before.inventory.configuration) := rfl

end Prepared

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSchedulePromotion
