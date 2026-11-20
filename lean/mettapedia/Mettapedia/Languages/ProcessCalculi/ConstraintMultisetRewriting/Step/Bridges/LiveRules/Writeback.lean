import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.LiveRules.Persistent
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.WritingBack

/-!
# Consumed rule occurrences that write themselves back

One unused rule identity is sufficient, and the used identity becomes spare
after every firing. The representation therefore supports finite identity
types. The actual program and candidate runs preserve event counts and row
states in both directions; the held identity changes. This is the named
writeback profile, not arbitrary live rule updates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.LiveRules.Writeback

open RuleSyntax RuleSyntax.RuleOccurrences
open LogicOverTheStep.StepSpan (Succ)
open FragmentsOfTheStep.TransitionMaps
open WritingBack (codes consuming)

universe uO uT uH uE uOcc uR uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O] {R : Type uR} [DecidableEq R] {Z : Type uZ}
  (X : Frames Tm Hom) (E : Extensions.{uO, uH, uE} Hom) (zones : Rule Tm → Z)
  (program : Program Tm)

def Represents (state : State Tm O) (held : RState Tm O R (Rule Tm) Z) : Prop :=
  ∃ (ids : Finset R) (code : R → Rule Tm), Offers program ids code ∧
    (∃ spare : R, spare ∉ ids) ∧ held = consuming zones state ids code

omit [DecidableEq O] in
theorem spare_again {ids : Finset R} {used fresh : R} (present : used ∈ ids) (spare : fresh ∉ ids) :
    used ∉ insert fresh (ids.erase used) := by
  intro inside
  rcases Finset.mem_insert.mp inside with same | erased
  · exact spare (same ▸ present)
  · exact (Finset.mem_erase.mp erased).1 rfl

theorem bisimulation :
    IsBisimulation (Succ (step X O E program).toStep)
      (Succ (rstep X O R E (codes zones) (∅ : Set (Rule Tm))).toStep)
      (Represents zones program) := by
  constructor
  · rintro origin after current ⟨ids, code, offers, ⟨spare, missing⟩, rfl⟩ ⟨firing, admitted, rfl⟩
    obtain ⟨used, present, aligned⟩ := (offers firing.rule).mp firing.member
    obtain ⟨lifted, accepted, endpoint⟩ :=
      WritingBack.lift_admits X (zoneOf := zones) firing admitted present aligned missing
    refine ⟨_, ⟨lifted, accepted, rfl⟩, _, _,
      WritingBack.offers_writeBack offers present missing, ⟨used, spare_again present missing⟩, endpoint⟩
  · rintro origin current next ⟨ids, code, offers, _, rfl⟩ moved
    obtain ⟨after, used, fresh, present, missing, endpoint, projected⟩ :=
      WritingBack.consumed_closed R X E offers moved
    exact ⟨after, projected, _, _, WritingBack.offers_writeBack offers present missing,
      ⟨used, spare_again present missing⟩, endpoint⟩

def correspondence := Transitions.correspondence (bisimulation X E (O := O) (R := R) zones program)

theorem run_lifts : ∀ {state : State Tm O} (run : (step X O E program).toStep.Run state)
    {held : RState Tm O R (Rule Tm) Z}, Represents zones program state held →
      ∃ lifted : (rstep X O R E (codes zones) (∅ : Set (Rule Tm))).toStep.Run held,
        Represents zones program run.last lifted.last ∧ lifted.word.length = run.word.length
  | _, .nil _, _, represented => ⟨.nil _, represented, rfl⟩
  | _, .cons firing admitted rest, _, represented => by
      obtain ⟨next, ⟨lifted, accepted, rfl⟩, nextRelated⟩ :=
        (bisimulation X E zones program).1 represented ⟨firing, admitted, rfl⟩
      obtain ⟨tail, endpoint, count⟩ := run_lifts rest nextRelated
      exact ⟨.cons lifted accepted tail, endpoint, congrArg (· + 1) count⟩

theorem run_projects : ∀ {held : RState Tm O R (Rule Tm) Z}
    (run : (rstep X O R E (codes zones) (∅ : Set (Rule Tm))).toStep.Run held)
    {state : State Tm O}, Represents zones program state held →
      ∃ projected : (step X O E program).toStep.Run state,
        Represents zones program projected.last run.last ∧ projected.word.length = run.word.length
  | _, .nil _, _, represented => ⟨.nil _, represented, rfl⟩
  | _, .cons firing admitted rest, _, represented => by
      obtain ⟨after, ⟨projected, accepted, rfl⟩, nextRelated⟩ :=
        (bisimulation X E zones program).2 represented ⟨firing, admitted, rfl⟩
      obtain ⟨tail, endpoint, count⟩ := run_projects rest nextRelated
      exact ⟨.cons projected accepted tail, endpoint, congrArg (· + 1) count⟩

omit [DecidableEq O] [DecidableEq R] in
theorem represented_rows {state : State Tm O} {held : RState Tm O R (Rule Tm) Z}
    (represented : Represents zones program state held) : held.toState = state := by
  obtain ⟨_, _, _, _, rfl⟩ := represented
  rfl

theorem readout_iff {state : State Tm O} {held : RState Tm O R (Rule Tm) Z}
    (represented : Represents zones program state held) (observe : State Tm O → Prop) :
    (∃ run : (step X O E program).toStep.Run state, observe run.last) ↔
      ∃ run : (rstep X O R E (codes zones) (∅ : Set (Rule Tm))).toStep.Run held,
        observe run.last.toState := by
  constructor
  · rintro ⟨run, observed⟩
    obtain ⟨lifted, endpoint, _⟩ := run_lifts X E zones program run represented
    exact ⟨lifted, (represented_rows zones program endpoint).symm ▸ observed⟩
  · rintro ⟨run, observed⟩
    obtain ⟨projected, endpoint, _⟩ := run_projects X E zones program run represented
    exact ⟨projected, (represented_rows zones program endpoint) ▸ observed⟩

theorem normalization_iff {state : State Tm O} {held : RState Tm O R (Rule Tm) Z}
    (represented : Represents zones program state held) :
    Acc (fun after before => Succ (step X O E program).toStep before after) state ↔
      Acc (fun after before => Succ (rstep X O R E (codes zones) (∅ : Set (Rule Tm))).toStep before after) held :=
  Transitions.normalization_iff (bisimulation X E zones program) represented

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.LiveRules.Writeback
