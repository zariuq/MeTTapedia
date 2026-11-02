import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdvanceCall

/-! A running advance page performs one actual tick, decrements its tick
budget and reuses the retained machine in the recursive public call.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdvanceStep

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlInstallExecution

private theorem tick_at (state : State) (caller : Subst) (input answer : Term) (quantum : Nat)
    (inputRead : caller.lookup "machine" = some (encoded input))
    (quantumRead : caller.lookup "quantum" = some (number quantum))
    (computed : PureReturns runtime [] state (apply "gslt:ml:tick" [encoded input, number quantum]) state (encoded answer)) :
    PureReturns runtime caller state (apply "gslt:ml:tick" [.var "machine", .var "quantum"]) state (encoded answer) := by
  apply captured_call_returns runtime [] caller state state "gslt:ml:tick" [encoded input, number quantum]
    [.var "machine", .var "quantum"] _ (by decide +kernel) (by decide)
  · intro index item found
    cases index with
    | zero => exact Or.inl (by decide +kernel)
    | succ index =>
      cases index with
      | zero => simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at found; subst item; exact Or.inr rfl
      | succ index => simp at found
  · intro index item found
    cases index with
    | zero => simp at found; subst item; exact Or.inr rfl
    | succ index =>
      cases index with
      | zero => simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at found; subst item; exact Or.inr rfl
      | succ index => simp at found
  · simp only [List.map_cons, List.map_nil, applySubst, inputRead, quantumRead, Option.getD_some,
      CettaWireAtom.applySubst_encode]
  · exact computed

private theorem advance_at (state : State) (caller : Subst) (input answer : Term) (ticks quantum : Nat)
    (ticksRead : caller.lookup "remaining" = some (number ticks))
    (quantumRead : caller.lookup "quantum" = some (number quantum))
    (inputRead : caller.lookup "next" = some (encoded input))
    (computed : PureReturns runtime [] state (apply "gslt:ml:advance" [number ticks, number quantum, encoded input]) state (encoded answer)) :
    PureReturns runtime caller state (apply "gslt:ml:advance" [.var "remaining", .var "quantum", .var "next"]) state (encoded answer) := by
  apply captured_call_returns runtime [] caller state state "gslt:ml:advance" [number ticks, number quantum, encoded input]
    [.var "remaining", .var "quantum", .var "next"] _ (by decide +kernel) (by decide)
  · intro index item found
    cases index with
    | zero => simp at found; subst item; exact Or.inr rfl
    | succ index =>
      cases index with
      | zero => simp at found; subst item; exact Or.inr rfl
      | succ index =>
        cases index with
        | zero => exact Or.inl (by decide +kernel)
        | succ index => simp at found
  · intro index item found
    cases index with
    | zero => simp at found; subst item; exact Or.inr rfl
    | succ index => cases index with
      | zero => simp at found; subst item; exact Or.inr rfl
      | succ index =>
        cases index with
        | zero => simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at found; subst item; exact Or.inr rfl
        | succ index => simp at found
  · simp only [List.map_cons, List.map_nil, applySubst, ticksRead, quantumRead, inputRead, Option.getD_some,
      CettaWireAtom.applySubst_encode]
  · exact computed

theorem running_returns (state : State) (plan standard runner epochs next answer : Term) (ticks quantum : Nat)
    (ticked : PureReturns runtime [] state
      (apply "gslt:ml:tick" [encoded (machine "MlRunning" plan standard runner epochs), number quantum]) state (encoded next))
    (later : PureReturns runtime [] state (apply "gslt:ml:advance" [number ticks, number quantum, encoded next]) state (encoded answer)) :
    PureReturns runtime [] state
      (apply "gslt:ml:advance" [number (ticks + 1), number quantum, encoded (machine "MlRunning" plan standard runner epochs)]) state
      (encoded answer) := by
  apply OCamlAdvanceCall.returns
  metta_literal
  apply pure_if_returns
  · exact natural_equal_returns _ _ _ _ _ (ticks + 1) 0 (bound_returns _ _ _ (by rfl)) (number_returns _ _ _ _)
  · simp only [Nat.add_one_ne_zero, decide_false, Bool.false_eq_true, if_false]
    apply pure_case_returns _ _ _ _ _ _ _ _ rfl
    · exact bound_returns _ _ _ (by rfl)
    · metta_select [machine, CettaWireAtom.encode, CettaWireAtom.encodeMany]
    · intro selected body selection
      metta_select [machine, CettaWireAtom.encode, CettaWireAtom.encodeMany] at selection
      obtain ⟨bindings, branch⟩ := selection
      subst bindings
      subst branch
      apply pure_let_star_returns _ _ _ _ _ _ _ rfl
      apply pure_let_returns _ _ _ "next" _ (encoded next) _ _ (by rfl)
      · exact tick_at state _ _ next quantum (by rfl) (by rfl) ticked
      · apply pure_let_returns _ _ _ "remaining" _ (number ticks) _ _ (by rfl)
        · exact natural_pred_returns _ _ _ _ ticks (bound_returns _ _ _ (by rfl))
        · exact advance_at state _ next answer ticks quantum (by rfl) (by rfl) (by rfl) later

#print axioms running_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlAdvanceStep
