import Mettapedia.GSLT.Causality.OccurrenceRealization

/-!
# Occurrence-block controls

The source offers two differently labelled occurrences with the same
endpoints. Each expands to a two-phase target execution. Histories retain the
selected labels, including repeated labels, while endpoint erasure cannot
recover them. Accounting includes both target phases.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.OccurrenceHistory.Controls

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent

@[reducible] def sourceTheory : GSLT where
  Term := Nat
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun first last => last = first + 1
  rewrites_resp_left := by
    intro first first' last equal step
    cases equal
    exact ⟨last, step, rfl⟩
  rewrites_resp_right := by
    intro first last last' step equal
    cases equal
    exact step

@[reducible] def sourceEvents : InteractionPresentation sourceTheory where
  Site := Bool
  Event _ first last := PLift (last = first + 1)
  sound event := event.down

inductive State where
  | ready : Nat → State
  | pending : Bool → Nat → State
  deriving DecidableEq

inductive Phase where
  | begin : Bool → Phase
  | finish : Bool → Phase
  deriving DecidableEq

inductive Event : Phase → State → State → Prop where
  | begin (choice : Bool) (index : Nat) :
      Event (.begin choice) (.ready index) (.pending choice index)
  | finish (choice : Bool) (index : Nat) :
      Event (.finish choice) (.pending choice index) (.ready (index + 1))

@[reducible] def targetTheory : GSLT where
  Term := State
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun first last => ∃ phase, Event phase first last
  rewrites_resp_left := by
    intro first first' last equal step
    cases equal
    exact ⟨last, step, rfl⟩
  rewrites_resp_right := by
    intro first last last' step equal
    cases equal
    exact step

@[reducible] def targetEvents : InteractionPresentation targetTheory where
  Site := Phase
  Event phase first last := PLift (Event phase first last)
  sound := by intro site first last event; exact ⟨site, event.down⟩

/-- A real two-phase realization with a retained choice at the intermediate state. -/
def twoPhase : OccurrenceRealization sourceEvents targetEvents where
  mapTerm := State.ready
  mapEquiv := by intro first last equal; cases equal; rfl
  mapOccurrence {first last} event := by
    have endpoint := event.evidence.down
    change last = first + 1 at endpoint
    subst last
    exact .cons ⟨.begin event.site, ⟨.begin event.site first⟩⟩
      (.cons ⟨.finish event.site, ⟨.finish event.site first⟩⟩ (.refl _))

def selected (choice : Bool) (index : Nat) :
    Occurrence sourceEvents index (index + 1) := ⟨choice, ⟨rfl⟩⟩

def one (choice : Bool) : OccurrencePath sourceEvents 0 1 :=
  .cons (selected choice 0) (OccurrencePath.refl (P := sourceEvents) (1 : Nat))

theorem expanded_sites (choice : Bool) :
    (twoPhase.mapPath (one choice)).sites = [.begin choice, .finish choice] := rfl

/-- Equal endpoints do not collapse the two authored occurrence histories. -/
theorem expanded_choices_distinct :
    twoPhase.mapPath (one false) ≠ twoPhase.mapPath (one true) := by
  intro equal
  have words := congrArg OccurrencePath.sites equal
  change [Phase.begin false, Phase.finish false] =
    [Phase.begin true, Phase.finish true] at words
  cases words

def twice (choice : Bool) : OccurrencePath sourceEvents 0 2 :=
  .cons (selected choice 0) (.cons (selected choice 1)
    (OccurrencePath.refl (P := sourceEvents) (2 : Nat)))

/-- Duplicate occurrences retain both copies and their ordered expansion. -/
theorem duplicate_sites_retained (choice : Bool) :
    (twoPhase.mapPath (twice choice)).sites =
      [.begin choice, .finish choice, .begin choice, .finish choice] := rfl

def communications : OccurrenceValuation targetEvents Nat where
  grade _ := 1

theorem one_source_event_costs_two :
    (twoPhase.pullValuation communications).onPath (one false) = 2 := rfl

theorem two_source_events_cost_four :
    communications.onPath (twoPhase.mapPath (twice false)) = 4 := rfl

/-- There is no endpoint-only reconstruction of the target's ordered history. -/
theorem no_endpoint_history :
    ¬ ∃ readout : Nat → Nat → List Phase,
      ∀ choice : Bool, readout 0 1 = (twoPhase.mapPath (one choice)).sites := by
  rintro ⟨readout, recovers⟩
  have equal := (recovers false).symm.trans (recovers true)
  change [Phase.begin false, Phase.finish false] =
    [Phase.begin true, Phase.finish true] at equal
  cases equal

end Mettapedia.GSLT.Causality.OccurrenceHistory.Controls
