import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineStepExecution

/-! The CHR machine source executes as `Mettapedia.Languages.CHR.Machine`:
occurrence scans. A scan of an occurrence whose rule has heads starts its
partner search with every candidate of the first head. -/

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
open Mettapedia.Languages.CHR (Value Term Environment IntOperator IntExpr Comparison ArithmeticFault Guard
  guardsEval Head Goal Rule)
open Mettapedia.Languages.CHR.Machine (Key Occ Store Pick At Table slot put without alive removePicks ids
  occurrencesOf instantiateTerms)

/-! ## Scans -/

theorem frame_start (heads : List Head) (candidates : List Occ) :
    frameAtom ⟨0, heads, candidates, [], [], []⟩ =
      .expression [.symbol "ChrFrame", integer 0, listAtom (heads.map headAtom), occsAtom candidates,
        .symbol "ChrNil", .symbol "ChrNil", .symbol "ChrNil"] := rfl

theorem scan_returns (caller : Subst) (state : State) (codes : List Atom) (active : Nat) (key : Key)
    (values : List Value) (remaining : List At) (tail : List MachineTask) (machine : MachineState)
    (headed : ∀ occurrence after, remaining = occurrence :: after →
      occurrence.body.kept ++ occurrence.body.removed ≠ [])
    (returns : List.Forall₂ (fun code value => Returns caller state code value) codes
      [integer active, keyAtom key, valuesAtom values, listAtom (remaining.map atAtom), tasksAtom tail,
        storeAtom machine.store, historyAtom machine.history, integer machine.next, statusAtom machine.status,
        idsAtom machine.seeds]) :
    Returns caller state (apply "gslt:chr-machine:scan" codes)
      (stateAtom (Mettapedia.Languages.CHR.Machine.scan active key values remaining tail machine)) := by
  machine_call returns
  apply pure_if_returns _ _ _ _ (!alive active (slot key machine.store)) _ _ _
    (not_returns _ state _ _ (alive_returns state active _ _ _ _ bound
      (slot_returns state key machine.store _ _ _ bound bound)))
  unfold Mettapedia.Languages.CHR.Machine.scan
  by_cases living : alive active (slot key machine.store) = true
  · simp only [living, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases remaining with
    | nil =>
      state_case (bound)
      exact make_returns _ _ "ChrState" _ _ inert (.cons bound (.cons bound (.cons bound (.cons bound
        (.cons bound (.cons bound .nil))))))
    | cons occurrence after =>
      state_case (bound) unfolding [ruleAtom]
      cases headsEq : occurrence.body.kept ++ occurrence.body.removed with
      | nil => exact absurd headsEq (headed occurrence after rfl)
      | cons first later =>
        apply pure_let_star_returns _ _ _ _ _ _ _ rfl
        apply pure_let_returns _ _ _ "heads" _ (listAtom ((first :: later).map headAtom)) _ _ (by rfl)
          (by rw [← headsEq, List.map_append]; exact append_returns state _ _ _ _ _ bound bound)
        apply pure_let_returns _ _ _ "first" _ (headAtom first) _ _ (by rfl)
          (by state_case (bound); exact bound)
        simp only [headsEq, stateAtom, tasksAtom, List.map, listAtom, taskAtom, frame_start]
        refine make_returns _ _ "ChrState" _ _ inert (.cons ?_ (.cons bound (.cons bound (.cons bound
          (.cons bound (.cons bound .nil))))))
        refine cons_returns _ state _ _ _ _ ?_ bound
        refine make_returns _ _ "ChrSearch" _ _ inert (.cons bound (.cons bound (.cons bound (.cons ?_
          (.cons bound (.cons ?_ .nil))))))
        · exact make_returns _ _ "ChrAt" _ _ inert (.cons bound (.cons bound (.cons (make_returns _ _ "ChrRule" _ _
            inert (.cons bound (.cons bound (.cons bound (.cons bound (.cons bound .nil)))))) .nil)))
        · refine cons_returns _ state _ _ _ _ ?_ (Eval.symbol_returns runtime _ state _)
          refine make_returns _ _ "ChrFrame" _ _ inert (.cons (integer_returns runtime _ state 0) (.cons ?_
            (.cons ?_ (.cons (Eval.symbol_returns runtime _ state _) (.cons (Eval.symbol_returns runtime _ state _)
            (.cons (Eval.symbol_returns runtime _ state _) .nil))))))
          · exact bound
          · exact candidates_returns _ state _ 0 occurrence.head active values first machine.store
              (.cons (integer_returns runtime _ state 0) (.cons bound (.cons bound (.cons bound (.cons bound
                (.cons bound .nil))))))
  · have dead : alive active (slot key machine.store) = false := by simpa using living
    simp only [dead, Bool.not_false, ↓reduceIte]
    exact make_returns _ _ "ChrState" _ _ inert (.cons bound (.cons bound (.cons bound (.cons bound
      (.cons bound (.cons bound .nil))))))

#print axioms scan_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution
