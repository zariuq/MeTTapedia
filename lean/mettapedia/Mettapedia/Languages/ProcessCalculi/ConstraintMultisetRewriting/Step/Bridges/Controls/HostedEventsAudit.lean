import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedEvents
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Answers.Bags
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Observation

/-!
# Named choices, erased rule origins and the failure boundary

Two identical closed source equations have different names but the same compiled
rule. The named profile keeps both choices and their distinct words. Forgetting
names merges them; the corresponding distinction is already present in the
source's answer bags.

The profile describes live children of individual alternatives. A source
configuration can delete a failed alternative even though the failing branch
has no named child. Refusal and waiting are excluded by the plain-fragment
condition; finished-answer correspondence does not assert a general outcome
correspondence for the full source language.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.HostedEventsAudit

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives
open SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting.Answers.Bags (D N P1 P2 q W0 W1 X fT eqF live_ff matched2 sp supply)

def current : HostedEvents.SourceState (κ := mkeys) (D := D) := (W0, initialBranch q)

theorem first_move : NamedMove P2 current.1 current.2 (.eqn 0) W1 X :=
  NamedMove.eqn (D := D) (P := P2) (w := W0) [] fT [] [] 0 eqF rfl matched2

theorem second_move : NamedMove P2 current.1 current.2 (.eqn 1) W1 X :=
  .eqn [] fT [] [] 1 ⟨[401], fT, .ret (sym "one")⟩ rfl matched2

def firstChoice : (HostedEvents.sourceSystem (D := D) P2).Choice current :=
  ⟨.eqn 0, ⟨(W1, X), first_move, live_ff⟩⟩

def secondChoice : (HostedEvents.sourceSystem (D := D) P2).Choice current :=
  ⟨.eqn 1, ⟨(W1, X), second_move, live_ff⟩⟩

theorem choices_differ : firstChoice ≠ secondChoice := by
  intro same
  have names := congrArg Subtype.val same
  cases names

theorem compiled_rules_agree :
    ruleNamed N P2 firstChoice.1 = ruleNamed N P2 secondChoice.1 := rfl

/-- The selected successor is the unique child of the named source move. -/
theorem chosen_first : (HostedEvents.sourceSystem (D := D) P2).next current firstChoice = (W1, X) := by
  have selected := HostedEvents.source_next_spec P2 current firstChoice
  obtain ⟨world, branch⟩ := NamedMove.unique selected.1 first_move
  exact Prod.ext world branch

theorem chosen_second : (HostedEvents.sourceSystem (D := D) P2).next current secondChoice = (W1, X) := by
  have selected := HostedEvents.source_next_spec P2 current secondChoice
  obtain ⟨world, branch⟩ := NamedMove.unique selected.1 second_move
  exact Prod.ext world branch

theorem plain_program : PlainProgram P2 := by
  intro equation member
  simp only [P2, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> trivial

theorem initial_related : HostedEvents.Related (D := D) N P2 q current [] :=
  HostedEvents.initial (D := D) (N := N) (P := P2) (q := q) sp (by trivial) Hosting.Answers.Bags.q_unopened

def firstTarget : (HostedEvents.targetSystem (D := D) N P2 q).Choice [] :=
  (HostedEvents.bisimulation (D := D) (N := N) (P := P2) (q := q) plain_program).choices initial_related firstChoice

def secondTarget : (HostedEvents.targetSystem (D := D) N P2 q).Choice [] :=
  (HostedEvents.bisimulation (D := D) (N := N) (P := P2) (q := q) plain_program).choices initial_related secondChoice

/-- The named target retains two origins, although both denote one bare rule. -/
theorem named_origins_survive :
    firstTarget ≠ secondTarget ∧
      ruleNamed N P2 firstTarget.1 = ruleNamed N P2 secondTarget.1 := by
  refine ⟨?_, rfl⟩
  intro same
  have names := congrArg Subtype.val same
  cases names

theorem named_words_differ :
    (HostedEvents.targetSystem (D := D) N P2 q).next [] firstTarget ≠
      (HostedEvents.targetSystem (D := D) N P2 q).next [] secondTarget := by
  intro same
  change [RuleName.eqn 0] = [RuleName.eqn 1] at same
  cases same

/-- Erasing the names erases this distinction. The theorem is not an origin-recovery result. -/
theorem forgotten_words_agree :
    ((HostedEvents.targetSystem (D := D) N P2 q).next [] firstTarget).filterMap (ruleNamed N P2) =
      ((HostedEvents.targetSystem (D := D) N P2 q).next [] secondTarget).filterMap (ruleNamed N P2) := rfl

def failing : Branch mkeys [] () MTy := ⟨[], .eval .fail, [], []⟩

theorem failure_has_no_named_child :
    IsEmpty ((HostedEvents.sourceSystem (D := D) P1).Choice (W0, failing)) := by
  constructor
  rintro ⟨name, ⟨next, moved, _⟩⟩
  cases moved

/-- The full configuration has a deletion step which the live-child profile does not count. -/
theorem failure_configuration_moves :
    SourceLanguage.Step D P1 supply ⟨W0, {failing}⟩ ⟨W0, 0⟩ :=
  Step.of_eq (rest := 0) rfl rfl live_nil (.fail W0 [] [] [])

section Scope

variable {S : Signature} {Γ : Ctx S} {star : S.Srt}
  {κ : Keys S} {D : Discipline S Γ star}

theorem plain_has_no_refusal {branch : Branch κ Γ star D.Ty} (plain : PlainBranch branch) :
    Observation.refusal branch = none := by
  rcases plain.2 with ⟨code, focus, _⟩ | ⟨value, focus⟩ <;>
    simp [Observation.refusal, focus]

theorem plain_has_no_waiting {branch : Branch κ Γ star D.Ty} (plain : PlainBranch branch) :
    Observation.reason (D := D) branch = none := by
  rcases plain with ⟨frames, ⟨code, focus, shape⟩ | ⟨value, focus⟩⟩
  · cases code <;> simp_all [PlainComp, Observation.reason]
  · simp [Observation.reason, focus, frames]

end Scope

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.HostedEventsAudit

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.HostedEventsAudit.named_origins_survive
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.HostedEventsAudit.forgotten_words_agree
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.HostedEventsAudit.failure_configuration_moves
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.HostedEventsAudit.plain_has_no_waiting
