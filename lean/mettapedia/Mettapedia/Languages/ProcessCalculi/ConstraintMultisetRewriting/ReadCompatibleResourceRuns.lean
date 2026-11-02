import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourceLifting

/-!
# Finite compatible resource runs lift under one final shared model

Every resource entry retains its source rule and read-port alias classes.
The implementation may choose different equal-valued physical rows; it does
not identify causal histories or preserve prototype identities across steps.
Every final observation is the complete residual bag.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourcePlanning

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open PositiveResourceProjection (realized)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] [DecidableEq T]
  {A : SubstitutionAction T S} {assignment : S} {label : O → T}

def Implements (entry : (resources A assignment label).Entry)
    (firing : ConditionalSchedule.Firing T O) : Prop :=
  firing.1 = entry.1.down.rule ∧ Nonempty (ReadRealization A assignment label entry.2.down firing.2)

theorem lift_fires (structural : A.E = Eq)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value) :
    ∀ (entries : List (resources A assignment label).Entry) (before : Configuration T O) (target : Multiset T),
      A.Models assignment before.equations →
      (resources A assignment label).Fires entries (labels (realized A assignment label) before.present) target →
      ∃ schedule : List (ConditionalSchedule.Firing T O),
        ConditionalSchedule.Executable A label before schedule ∧
        A.Models assignment (ConditionalSchedule.follow label before schedule).equations ∧
        List.Forall₂ (Implements (A := A) (assignment := assignment) (label := label)) entries schedule ∧
        labels (realized A assignment label) (ConditionalSchedule.follow label before schedule).present = target
  | [], before, target, oldSolved, fired =>
      ⟨[], ⟨assignment, oldSolved⟩, oldSolved, .nil, fired.symm⟩
  | entry :: rest, before, target, oldSolved, fired => by
      obtain ⟨enabled, later⟩ := fired
      obtain ⟨selection, valid, solved, realizedReads, observed⟩ :=
        lift_enabled structural supply entry.1.down entry.2.down before oldSolved enabled
      have actualLater : (resources A assignment label).Fires rest
          (labels (realized A assignment label) (selection.result label entry.1.down.rule before).present) target := by
        rw [observed]
        exact later
      obtain ⟨schedule, executable, finalSolved, matching, finalBag⟩ :=
        lift_fires structural supply rest (selection.result label entry.1.down.rule before) target solved actualLater
      exact ⟨(entry.1.down.rule, selection) :: schedule, ⟨valid, executable⟩, finalSolved,
        .cons ⟨rfl, realizedReads⟩ matching, finalBag⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourcePlanning
