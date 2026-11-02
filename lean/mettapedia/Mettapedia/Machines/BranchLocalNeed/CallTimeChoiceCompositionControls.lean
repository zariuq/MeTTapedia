import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceComposition

/-! # Executable controls for compositional call-time choice

The countercontrols keep the observer explicit: result order, event order and
stored code are visible. None of these may be erased by a bag-level equality.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Composition.Controls

def discarded : Comp := .seq (.ret (.sym 1)) (.ret (.sym 2))

theorem discard_pure_stage (program : Program) :
    Equivalent program discarded (.ret (.sym 2)) := by
  intro store environment results
  constructor
  · intro evaluated
    cases evaluated with
    | seq first rest =>
      cases first
      cases rest with
      | seqKOk body tail =>
        cases tail
        cases body
        exact Derives.ret
      | seqKStop stopped _ => simp [Outcome.isOk] at stopped
  · intro evaluated
    cases evaluated
    exact Derives.seq_single Derives.ret Derives.ret

theorem stored_code_is_a_stronger_observer (program : Program) :
    ¬ Equivalent program (.quote discarded) (.quote (.ret (.sym 2))) := by
  intro same
  have target := (same Store.empty [] _).mp (Derives.quote (P := program))
  have equal := (quote_iff program Store.empty [] (.ret (.sym 2)) _).mp target
  have codes := congrArg (fun results : List Result =>
    results.map fun result => result.2.cells.map Suspension.code) equal
  have impossible : [discarded] = [.ret (.sym 2)] := by
    simpa [Store.alloc, Store.empty] using codes
  cases impossible

def eventPair : Comp := .emit 4 (.emit 5 (.ret (.sym 7)))

def read (program : Program) (code : Comp) : Option (List (Outcome × List Nat)) :=
  (run program 100 (.eval Store.empty [] code)).map
    (fun results => results.map fun result => (result.1, result.2.trace))

theorem nested_effect_order : read [] eventPair = some [(.ok (.sym 7), [4, 5])] := by
  decide +kernel

theorem reversing_effects_changes_observation :
    read [] eventPair ≠ read [] (.emit 5 (.emit 4 (.ret (.sym 7)))) := by
  decide +kernel

theorem quotation_keeps_effects_inert :
    read [] (.quote eventPair) = some [(.ok (.code 0), [])] := by
  decide +kernel

theorem explicit_activation_releases_effects :
    read [] (.seq (.quote eventPair) (.run (.var 0))) =
      some [(.ok (.sym 7), [4, 5])] := by
  decide +kernel

theorem noncode_activation_finishes_in_a_residual :
    read [] (.run (.sym 7)) = some [(.ok (.app (.sym unquoteHead) (.sym 7)), [])] := by
  decide +kernel

def choosing : Comp := .choose (.ret (.sym 2)) (.ret (.sym 3))

def pairTwice : Comp :=
  .seq (.force (.var 0))
    (.seq (.force (.var 1))
      (.ret (.app (.app (.sym 8) (.var 1)) (.var 0))))

def pair (left right : Nat) : Outcome :=
  .ok (.app (.app (.sym 8) (.sym left)) (.sym right))

theorem shared_choices_are_correlated :
    read [] (.need choosing pairTwice) = some [(pair 2 2, []), (pair 3 3, [])] := by
  decide +kernel

theorem independent_demands_are_not_shared :
    read [] (.delay choosing pairTwice) =
      some [(pair 2 2, []), (pair 2 3, []), (pair 3 2, []), (pair 3 3, [])] := by
  decide +kernel

theorem unused_producer_keeps_no_events :
    read [] (.need eventPair (.ret (.sym 9))) = some [(.ok (.sym 9), [])] := by
  decide +kernel

theorem eager_binding_runs_before_the_body :
    read [] (.seq eventPair (.ret (.sym 9))) = some [(.ok (.sym 9), [4, 5])] := by
  decide +kernel

theorem alternatives_retain_order_and_multiplicity :
    read [] (.choose (.ret (.sym 2)) (.choose (.ret (.sym 2)) (.ret (.sym 3)))) =
      some [(.ok (.sym 2), []), (.ok (.sym 2), []), (.ok (.sym 3), [])] := by
  decide +kernel

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice.Composition.Controls
