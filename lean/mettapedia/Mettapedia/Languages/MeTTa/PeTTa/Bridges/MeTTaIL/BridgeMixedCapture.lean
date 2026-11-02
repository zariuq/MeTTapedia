import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit
import Mettapedia.Languages.MeTTa.PeTTa.BridgeTransport
import Mathlib.Tactic.IntervalCases

/-! Calls at captured values retain mixed demand: raw data arguments remain
raw, while evaluated arguments must be passive literals or variables.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval

theorem capture_arguments_of_check (program : SpaceSemantics.Program) (head : String) (arguments : List Atom)
    (checked : arguments.zipIdx.all (fun pair => argumentIsRaw program head pair.2 || passiveArgument pair.1) = true) :
    ∀ index item, arguments[index]? = some item →
      argumentIsRaw program head index = true ∨ passiveArgument item = true := by
  intro index item found
  have member := List.mk_mem_zipIdx_iff_getElem?.mpr found
  simpa only [Bool.or_eq_true] using List.all_eq_true.mp checked (item, index) member

syntax "metta_capture_mixed " term (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| metta_capture_mixed $fact $[unfolding [$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let extra ← extra.mapM fun term => `(Lean.Parser.Tactic.simpLemma| $term:term)
    `(tactic|
      (refine captured_call_returns _ [] _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ $fact
       · decide +kernel
       · decide
       · intro index item found
         obtain ⟨bounded, _⟩ := List.getElem?_eq_some_iff.mp found
         simp only [List.length_cons, List.length_nil] at bounded
         interval_cases index
         all_goals
           simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at found
           subst item
           first | exact Or.inr rfl | exact Or.inl (by decide +kernel)
       · intro index item found
         obtain ⟨bounded, _⟩ := List.getElem?_eq_some_iff.mp found
         simp only [List.length_cons, List.length_nil] at bounded
         interval_cases index
         all_goals
           simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at found
           subst item
           first | exact Or.inr rfl | exact Or.inl (by decide +kernel)
       · simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
           Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
           Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,
           Mettapedia.Languages.MeTTa.PeTTa.BridgeKit.Library.bind,
           List.map_cons, List.map_nil, CettaWireAtom.applySubst_encode,
           encoded, number, CettaWireAtom.encode, CettaWireAtom.encodeMany, $extra,*]))

#print axioms capture_arguments_of_check

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit
