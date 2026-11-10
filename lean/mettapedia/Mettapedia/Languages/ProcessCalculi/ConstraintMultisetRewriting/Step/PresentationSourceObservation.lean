import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationSourceControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventObserverLifting

/-! # Source records under normalization and event erasure

The canonical-input observer is pulled back from abstract events and therefore
commutes with finite-run erasure. The raw-input observer retains source spelling;
the concrete normalization control prevents it from descending through the same
erasure. Neither observer is read by execution in this profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Source

open Interface Payloads OccurrenceProfile

variable (label : Nat → Term) (decision : Decisions (effect label) (admission label))

def canonicalInputObserver : EventObserver (EffectCore.EventObject (effect label) (admission label)) where
  Data _ := List (List Nat)
  update {s} {_} event record := record ++ [requestInput s event.firing]

def normalizedSourceObserver (keep : ParsePolicy) : EventObserver (Object label decision keep) :=
  (canonicalInputObserver label).comap (erase label decision keep)

theorem normalized_record_commutes {keep : ParsePolicy} {source target : Object label decision keep}
    (path : Quiver.Path source target) (record : List (List Nat)) :
    (normalizedSourceObserver label decision keep).evaluate path record =
      (canonicalInputObserver label).evaluate ((erase label decision keep).mapPath path) record :=
  EventObserver.evaluate_comap (canonicalInputObserver label) (erase label decision keep) path record

def rawSourceObserver (keep : ParsePolicy) : EventObserver (Object label decision keep) where
  Data _ := List (List Nat)
  update event record := record ++ [event.input]

theorem raw_record_unique_lift (keep : ParsePolicy)
    (source : (rawSourceObserver label decision keep).Observed)
    (path : Quiver.PathStar source.1) :
    ∃! recorded : Quiver.PathStar source,
      (rawSourceObserver label decision keep).forget.pathStar source recorded = path :=
  EventObserver.unique_lift _ source path

namespace Controls

/-- The raw observer cannot be reconstructed from abstract events, even
starting with an empty record and even when both events change real resources. -/
theorem raw_observer_cannot_descend
    (decision : Decisions (effect ArgumentControls.label) (admission ArgumentControls.label)) :
    ¬ ∃ update : (effect ArgumentControls.label).Event (admission ArgumentControls.label)
        ArgumentControls.before Source.Controls.after → List (List Nat),
      ∀ event : SelectedEvent ArgumentControls.label decision allParses
          ArgumentControls.before Source.Controls.after,
        update (event.abstract ArgumentControls.label decision) =
          (rawSourceObserver ArgumentControls.label decision allParses).update
            (s := ⟨ArgumentControls.before⟩) (t := ⟨Source.Controls.after⟩) event [] := by
  rintro ⟨update, respects⟩
  obtain ⟨first, second, different, same, _⟩ :=
    Source.Controls.normalization_identifies_distinct_sources decision
  have records := (respects first).symm.trans ((congrArg update same).trans (respects second))
  change [first.input] = [second.input] at records
  exact different (List.singleton_inj.mp records)

end Controls

#print axioms normalized_record_commutes
#print axioms raw_record_unique_lift
#print axioms Controls.raw_observer_cannot_descend

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Source
