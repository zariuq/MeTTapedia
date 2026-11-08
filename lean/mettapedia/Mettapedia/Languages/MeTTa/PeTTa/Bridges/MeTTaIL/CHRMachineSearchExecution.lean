import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineFireExecution

/-! The CHR machine source executes as `Mettapedia.Languages.CHR.Machine`:
one partner-search tick. A frame with heads tries its next candidate: a used
or misplaced candidate is skipped, a matching one either completes the
selection or opens the frame of the next head. -/

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
open Mettapedia.Languages.CHR.Machine (Key Occ Store Pick At Table slot put without alive removePicks ids
  matchTerms)

theorem rejected_decide (id index position active : Nat) (used : List Nat) :
    (decide (id ∈ used) || (!decide (index = position) && decide (id = active))) =
      decide (id ∈ used ∨ (index ≠ position ∧ id = active)) := by
  by_cases inUsed : id ∈ used <;> by_cases same : index = position <;> by_cases isActive : id = active <;>
    simp [inUsed, same, isActive]

theorem picks_append (picks : List Pick) (pick : Pick) :
    picksAtom (picks ++ [pick]) = listAtom (picks.map pickAtom ++ [pickAtom pick]) := by
  simp [picksAtom]

theorem next_returns (caller : Subst) (state : State) (code : Atom) (index : Nat)
    (one : Returns caller state code (integer index)) :
    Returns caller state (apply "+" [code, .grounded (.int 1)]) (integer ((index + 1 : Nat) : Int)) := by
  rw [next_cast]
  exact integer_add_returns runtime _ state _ _ _ 1 one (integer_returns runtime _ state 1)

theorem search_returns (caller : Subst) (state : State) (codes : List Atom) (active : Nat) (key : Key)
    (values : List Value) (occurrence : At) (after : List At) (frames : List MachineFrame)
    (tail : List MachineTask) (machine : MachineState)
    (headed : ∀ frame ∈ frames, frame.heads ≠ [])
    (returns : List.Forall₂ (fun code value => Returns caller state code value) codes
      [integer active, keyAtom key, valuesAtom values, atAtom occurrence, listAtom (after.map atAtom),
        listAtom (frames.map frameAtom), tasksAtom tail, storeAtom machine.store, historyAtom machine.history,
        integer machine.next, statusAtom machine.status, idsAtom machine.seeds]) :
    Returns caller state (apply "gslt:chr-machine:search" codes)
      (stateAtom (Mettapedia.Languages.CHR.Machine.search active key values occurrence after frames tail
        machine)) := by
  machine_call returns
  cases frames with
  | nil =>
    state_case (bound)
    simp only [Mettapedia.Languages.CHR.Machine.search, stateAtom, tasksAtom, List.map, listAtom, taskAtom]
    exact make_returns _ _ "ChrState" _ _ inert
      (.cons (cons_returns _ state _ _ _ _ (make_returns _ _ "ChrScan" _ _ inert (.cons bound (.cons bound
        (.cons bound (.cons bound .nil))))) bound)
      (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound .nil))))))
  | cons frame below =>
    obtain ⟨index, heads, candidates, environment, picks, used⟩ := frame
    state_case (bound)
    cases candidates with
    | nil =>
      state_case (bound)
      simp only [Mettapedia.Languages.CHR.Machine.search, stateAtom, tasksAtom, List.map, listAtom, taskAtom]
      exact make_returns _ _ "ChrState" _ _ inert
        (.cons (cons_returns _ state _ _ _ _ (make_returns _ _ "ChrSearch" _ _ inert (.cons bound (.cons bound
          (.cons bound (.cons bound (.cons bound (.cons bound .nil))))))) bound)
        (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound .nil))))))
    | cons candidate others =>
      obtain ⟨id, arguments⟩ := candidate
      state_case (bound)
      apply pure_let_returns _ _ _ "stay" _
        (listAtom ((⟨index, heads, others, environment, picks, used⟩ :: below : List MachineFrame).map frameAtom))
        _ _ (by rfl)
        (by
          simp only [List.map, listAtom, frameAtom]
          exact cons_returns _ state _ _ _ _ (make_returns _ _ "ChrFrame" _ _ inert (.cons bound (.cons bound
            (.cons bound (.cons bound (.cons bound (.cons bound .nil))))))) bound)
      state_case (bound) unfolding [ruleAtom]
      apply pure_if_returns _ _ _ _ (decide (id ∈ used ∨ (index ≠ occurrence.head ∧ id = active))) _ _ _
        (by
          rw [← rejected_decide, ← natural_member, ← integer_nat_decide, ← integer_nat_decide id active]
          exact or_returns _ state _ _ _ _ (member_returns state _ _ _ _ _ bound bound)
            (and_returns _ state _ _ _ _ (not_returns _ state _ _ (equal_returns _ state _ _ _ _ bound bound))
              (equal_returns _ state _ _ _ _ bound bound)))
      by_cases rejected : id ∈ used ∨ (index ≠ occurrence.head ∧ id = active)
      · simp only [rejected, decide_true, ↓reduceIte, Mettapedia.Languages.CHR.Machine.search, stateAtom,
          tasksAtom, List.map, listAtom, taskAtom]
        exact make_returns _ _ "ChrState" _ _ inert
          (.cons (cons_returns _ state _ _ _ _ (make_returns _ _ "ChrSearch" _ _ inert (.cons bound (.cons bound
            (.cons bound (.cons bound (.cons bound (.cons bound .nil))))))) bound)
          (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound .nil))))))
      · simp only [rejected, decide_false, Bool.false_eq_true, ↓reduceIte]
        cases heads with
        | nil => exact absurd rfl (headed _ List.mem_cons_self)
        | cons head later =>
          state_case (bound) unfolding [headAtom]
          have matched := matchAll_returns state head.arguments arguments environment
          cases found : matchTerms head.arguments arguments environment with
          | none =>
            rw [found] at matched
            state_case (matched _ _ _ _ bound bound bound)
            simp only [Mettapedia.Languages.CHR.Machine.search, rejected, ↓reduceIte, found, stateAtom,
              tasksAtom, List.map, listAtom, taskAtom]
            exact make_returns _ _ "ChrState" _ _ inert
              (.cons (cons_returns _ state _ _ _ _ (make_returns _ _ "ChrSearch" _ _ inert (.cons bound (.cons bound
                (.cons bound (.cons bound (.cons bound (.cons bound .nil))))))) bound)
              (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound .nil))))))
          | some extended =>
            rw [found] at matched
            state_case (matched _ _ _ _ bound bound bound)
            apply pure_let_returns _ _ _ "chosen" _
              (picksAtom (picks ++ [⟨Mettapedia.Languages.CHR.Machine.Head.key head, id⟩])) _ _ (by rfl)
              (by
                rw [picks_append]
                exact append_returns state _ _ _ _ _ bound (cons_returns _ state _ _ _ _
                  (make_returns _ _ "ChrPick" _ _ inert (.cons (make_returns _ _ "ChrKey" _ _ inert
                    (.cons bound (.cons bound .nil))) (.cons bound .nil))) (Eval.symbol_returns runtime _ state _)))
            cases later with
            | nil =>
              state_case (bound)
              simp only [Mettapedia.Languages.CHR.Machine.search, rejected, ↓reduceIte, found]
              exact complete_returns _ state _ active key values occurrence after _ extended _ tail machine
                (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound
                  (.cons (by rw [picks_append]; exact bound) (.cons bound (.cons bound (.cons bound (.cons bound
                  (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound .nil)))))))))))))))))
            | cons nextHead rest =>
              state_case (bound)
              simp only [Mettapedia.Languages.CHR.Machine.search, rejected, ↓reduceIte, found, stateAtom,
                tasksAtom, List.map, listAtom, taskAtom]
              refine make_returns _ _ "ChrState" _ _ inert (.cons ?_ (.cons bound (.cons bound (.cons bound
                (.cons bound (.cons bound .nil))))))
              refine cons_returns _ state _ _ _ _ ?_ bound
              refine make_returns _ _ "ChrSearch" _ _ inert (.cons bound (.cons bound (.cons bound (.cons bound
                (.cons bound (.cons ?_ .nil))))))
              refine cons_returns _ state _ _ _ _ ?_ bound
              simp only [frameAtom]
              refine make_returns _ _ "ChrFrame" _ _ inert (.cons (next_returns _ state _ index bound)
                (.cons bound (.cons ?_ (.cons bound (.cons ?_ (.cons ?_ .nil))))))
              · exact candidates_returns _ state _ (index + 1) occurrence.head active values nextHead machine.store
                  (.cons (next_returns _ state _ index bound) (.cons bound (.cons bound (.cons bound (.cons bound
                    (.cons bound .nil))))))
              · rw [picks_append]
                exact bound
              · exact cons_returns _ state _ _ _ _ bound bound

#print axioms search_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution
