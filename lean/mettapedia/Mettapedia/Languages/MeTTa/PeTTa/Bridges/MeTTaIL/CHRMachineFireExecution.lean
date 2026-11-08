import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineStepExecution

/-! The CHR machine source executes as `Mettapedia.Languages.CHR.Machine`:
firing a complete selection, and deciding a complete selection by its
propagation history and guards. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Mettapedia.Languages.MeTTa.PeTTa.Eval
open Mettapedia.Languages.MeTTa.PeTTa.BridgeKit
open WireKit StrictCallKit CHRMachineSource
open Mettapedia.Languages.CHR (Value Term Environment Head Goal Rule guardsEval)
open Mettapedia.Languages.CHR.Machine (Key Occ Store Pick At Table slot put without alive removePicks ids)

theorem natural_member (item : Nat) (items : List Nat) :
    decide (natAtom item ∈ items.map natAtom) = decide (item ∈ items) := by
  apply decide_eq_decide.mpr
  constructor
  · intro inside
    obtain ⟨other, member, same⟩ := List.mem_map.mp inside
    simp only [natAtom, integer, Atom.grounded.injEq, OSLFCore.GroundedValue.int.injEq, Nat.cast_inj] at same
    exact same ▸ member
  · intro inside
    exact List.mem_map_of_mem inside

theorem idsAtom_inj {first second : List Nat} (same : idsAtom first = idsAtom second) : first = second := by
  induction first generalizing second with
  | nil => cases second with
    | nil => rfl
    | cons => simp [idsAtom, listAtom, nil, cons] at same
  | cons head rest ih => cases second with
    | nil => simp [idsAtom, listAtom, nil, cons] at same
    | cons other others =>
      simp only [idsAtom, List.map, listAtom, cons, Atom.expression.injEq, List.cons.injEq, true_and,
        and_true, natAtom, integer, Atom.grounded.injEq, OSLFCore.GroundedValue.int.injEq, Nat.cast_inj] at same
      rw [same.1, ih (by simpa [idsAtom] using same.2)]

theorem fired_member (key : Mettapedia.Languages.CHR.Key) (history : List Mettapedia.Languages.CHR.Key) :
    decide (firedAtom key ∈ history.map firedAtom) = decide (key ∈ history) := by
  apply decide_eq_decide.mpr
  constructor
  · intro inside
    obtain ⟨other, member, same⟩ := List.mem_map.mp inside
    have equal : other = key := by
      obtain ⟨rule, heads⟩ := other
      obtain ⟨rule', heads'⟩ := key
      simp only [firedAtom, Atom.expression.injEq, List.cons.injEq, true_and, and_true, integer,
        Atom.grounded.injEq, OSLFCore.GroundedValue.int.injEq, Nat.cast_inj] at same
      rw [same.1, idsAtom_inj same.2]
    exact equal ▸ member
  · intro inside
    exact List.mem_map_of_mem inside

theorem picksAtom_drop (picks : List Pick) (count : Nat) :
    picksAtom (picks.drop count) = listAtom ((picks.map pickAtom).drop count) := by
  simp [picksAtom, List.map_drop]

theorem fire_returns (caller : Subst) (state : State) (codes : List Atom) (active : Nat) (key : Key)
    (values : List Value) (occurrence : At) (after : List At) (environment : Environment) (picks : List Pick)
    (tail : List MachineTask) (machine : MachineState)
    (returns : List.Forall₂ (fun code value => Returns caller state code value) codes
      [integer active, keyAtom key, valuesAtom values, atAtom occurrence, listAtom (after.map atAtom),
        environmentAtom environment, picksAtom picks, tasksAtom tail, storeAtom machine.store,
        historyAtom machine.history, integer machine.next, statusAtom machine.status, idsAtom machine.seeds]) :
    Returns caller state (apply "gslt:chr-machine:fire" codes)
      (stateAtom (Mettapedia.Languages.CHR.Machine.fire active key values occurrence after environment picks tail
        machine)) := by
  machine_call returns
  state_case (bound) unfolding [ruleAtom]
  apply pure_let_star_returns _ _ _ _ _ _ _ rfl
  apply pure_let_returns _ _ _ "removedPicks" _ (picksAtom (picks.drop occurrence.body.kept.length)) _ _ (by rfl)
    (by
      rw [picksAtom_drop]
      apply drop_returns state _ _ _ _ _ _ bound
      have counted := length_returns state (occurrence.body.kept.map headAtom)
      rw [List.length_map] at counted
      exact counted _ _ bound)
  apply pure_let_returns _ _ _ "activeRemoved" _
    (Effects.boolean (decide (active ∈ ids (picks.drop occurrence.body.kept.length)))) _ _ (by rfl)
    (by
      rw [← natural_member]
      exact member_returns state _ _ _ _ _ bound (ids_returns state _ _ _ bound))
  apply pure_let_returns _ _ _ "continuation" _
    (tasksAtom (if active ∈ ids (picks.drop occurrence.body.kept.length) then tail
      else .scan active key values (occurrence :: after) :: tail)) _ _ (by rfl)
    (by
      apply pure_if_returns _ _ _ _ (decide (active ∈ ids (picks.drop occurrence.body.kept.length))) _ _ _ bound
      by_cases removed : active ∈ ids (picks.drop occurrence.body.kept.length)
      · simp only [removed, decide_true, ↓reduceIte]
        exact bound
      · simp only [removed, decide_false, Bool.false_eq_true, ↓reduceIte, tasksAtom, List.map, listAtom,
          taskAtom]
        exact cons_returns _ state _ _ _ _ (make_returns _ _ "ChrScan" _ _ inert (.cons bound (.cons bound
          (.cons bound (.cons (cons_returns _ state _ _ _ _ bound bound) .nil))))) bound)
  apply pure_let_returns _ _ _ "updated" _
    (historyAtom (if occurrence.body.propagation then ⟨occurrence.rule, ids picks⟩ :: machine.history
      else machine.history)) _ _ (by rfl)
    (by
      cases propagating : occurrence.body.propagation with
      | true =>
        state_case (bound) unfolding [kindAtom, propagating]
        simp only [↓reduceIte, historyAtom, List.map, listAtom, firedAtom]
        exact cons_returns _ state _ _ _ _ (make_returns _ _ "ChrFired" _ _ inert (.cons bound
          (.cons (ids_returns state _ _ _ bound) .nil))) bound
      | false =>
        state_case (bound) unfolding [kindAtom, propagating]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact bound)
  simp only [Mettapedia.Languages.CHR.Machine.fire, stateAtom, tasksAtom, List.map, listAtom, taskAtom]
  exact make_returns _ _ "ChrState" _ _ inert
    (.cons (cons_returns _ state _ _ _ _ (make_returns _ _ "ChrGoals" _ _ inert (.cons bound (.cons bound .nil)))
      bound)
    (.cons (removePicks_returns state _ machine.store _ _ _ bound bound) (.cons bound (.cons bound (.cons bound
    (.cons bound .nil))))))

theorem complete_returns (caller : Subst) (state : State) (codes : List Atom) (active : Nat) (key : Key)
    (values : List Value) (occurrence : At) (after : List At) (stay : List MachineFrame)
    (environment : Environment) (picks : List Pick) (tail : List MachineTask) (machine : MachineState)
    (returns : List.Forall₂ (fun code value => Returns caller state code value) codes
      [integer active, keyAtom key, valuesAtom values, atAtom occurrence, listAtom (after.map atAtom),
        listAtom (stay.map frameAtom), environmentAtom environment, picksAtom picks,
        listAtom (occurrence.body.guards.map guardAtom), kindAtom occurrence.body, integer occurrence.rule,
        tasksAtom tail, storeAtom machine.store, historyAtom machine.history, integer machine.next,
        statusAtom machine.status, idsAtom machine.seeds]) :
    Returns caller state (apply "gslt:chr-machine:complete" codes)
      (stateAtom (Mettapedia.Languages.CHR.Machine.complete active key values occurrence after stay environment
        picks tail machine)) := by
  machine_call returns
  apply pure_let_returns _ _ _ "retry" _
    (stateAtom { machine with tasks := .search active key values occurrence after stay :: tail }) _ _ (by rfl)
    (by
      simp only [stateAtom, tasksAtom, List.map, listAtom, taskAtom]
      exact make_returns _ _ "ChrState" _ _ inert
        (.cons (cons_returns _ state _ _ _ _ (make_returns _ _ "ChrSearch" _ _ inert (.cons bound (.cons bound
          (.cons bound (.cons bound (.cons bound (.cons bound .nil))))))) bound)
        (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound .nil)))))))
  have guarded := fun (caller : Subst) (first second : Atom) one two =>
    guards_returns state environment occurrence.body.guards caller first second one two
  cases propagating : occurrence.body.propagation with
  | true =>
    apply pure_if_returns _ _ _ _ (decide ((⟨occurrence.rule, ids picks⟩ : Mettapedia.Languages.CHR.Key) ∈
      machine.history)) _ _ _
      (by
        state_case (bound) unfolding [kindAtom, propagating]
        rw [← fired_member]
        exact member_returns state _ _ _ _ _ (make_returns _ _ "ChrFired" _ _ inert (.cons bound
          (.cons (ids_returns state _ _ _ bound) .nil))) bound)
    by_cases stale : (⟨occurrence.rule, ids picks⟩ : Mettapedia.Languages.CHR.Key) ∈ machine.history
    · simp only [stale, decide_true, ↓reduceIte, Mettapedia.Languages.CHR.Machine.complete, propagating, and_self]
      exact bound
    · simp only [stale, decide_false, Bool.false_eq_true, ↓reduceIte, Mettapedia.Languages.CHR.Machine.complete,
        propagating, true_and]
      cases result : guardsEval environment occurrence.body.guards with
      | error reason =>
        rw [result] at guarded
        state_case (guarded _ _ _ bound bound)
        exact withStatus_returns _ state _ _
          { machine with tasks := .search active key values occurrence after stay :: tail } (.faulted reason) bound
          (make_returns _ _ "ChrFaulted" _ _ inert (.cons bound .nil))
      | ok holds =>
        rw [result] at guarded
        state_case (guarded _ _ _ bound bound) unfolding [Effects.boolean]
        apply pure_if_returns _ _ _ _ holds _ _ _ bound
        cases holds with
        | true =>
          exact fire_returns _ state _ active key values occurrence after environment picks tail machine
            (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound
              (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound .nil)))))))))))))
        | false =>
          exact bound
  | false =>
    apply pure_if_returns _ _ _ _ false _ _ _
      (by
        state_case (bound) unfolding [kindAtom, propagating]
        exact grounded_returns runtime _ state (.bool false))
    simp only [Bool.false_eq_true, ↓reduceIte, Mettapedia.Languages.CHR.Machine.complete, propagating, false_and]
    cases result : guardsEval environment occurrence.body.guards with
    | error reason =>
      rw [result] at guarded
      state_case (guarded _ _ _ bound bound)
      exact withStatus_returns _ state _ _
        { machine with tasks := .search active key values occurrence after stay :: tail } (.faulted reason) bound
        (make_returns _ _ "ChrFaulted" _ _ inert (.cons bound .nil))
    | ok holds =>
      rw [result] at guarded
      state_case (guarded _ _ _ bound bound) unfolding [Effects.boolean]
      apply pure_if_returns _ _ _ _ holds _ _ _ bound
      cases holds with
      | true =>
        exact fire_returns _ state _ active key values occurrence after environment picks tail machine
          (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound
            (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound .nil)))))))))))))
      | false =>
        exact bound

#print axioms fire_returns
#print axioms complete_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution
