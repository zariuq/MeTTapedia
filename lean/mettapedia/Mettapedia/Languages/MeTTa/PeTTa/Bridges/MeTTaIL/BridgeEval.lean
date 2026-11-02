import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit
import Mettapedia.Languages.MeTTa.PeTTa.BridgeTransport
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeMixedCapture

/-!
# Evaluating a library body in a proof

`metta_call check` unfolds a call to an owned head of the library whose check is `check`: the
formals are bound to the arguments and the body is replaced by its literal source.

`metta_eval [lemmas]` then walks the body the way the evaluator does: variables, literals,
symbols, `let` of a fresh variable, `if` on a boolean, `case` on literal rows (selection computed
by `metta_select`), native natural equality, comparison, addition and predecessor, and calls to
owned heads closed by one of the supplied `lemmas` about the head at values. It goes as far as it
can and leaves what it cannot decide, such as a `case` on a value whose constructor is not yet
known, for the proof to split and resume.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit

open Mettapedia.Languages.MeTTa.PeTTa.BridgeKit

/-- Unfold a call to an owned head of a library. -/
syntax "metta_call " term : tactic
macro_rules
  | `(tactic| metta_call $checked) => `(tactic|
      (apply Library.call $checked (by decide +kernel) _ _ _ _ _ _ (by metta_literal; rfl) rfl
       simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
         CettaWireAtom.applySubst_encode]
       metta_literal))

/-- Unfold a body using a small source view, retaining the actual target program. -/
syntax "metta_call_in " term " using " term : tactic
macro_rules
  | `(tactic| metta_call_in $checked using $agreement) => `(tactic|
      (apply Library.call_in $checked $agreement (by decide +kernel) (by decide +kernel)
         _ _ _ _ _ _ (by metta_literal; rfl) rfl
       simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
         CettaWireAtom.applySubst_encode]
       metta_literal))

/-- Capture a fact using source-view metadata instead of reducing the target source. -/
syntax "metta_capture_in " term " using " term " from " term (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| metta_capture_in $checked using $agreement from $fact $[unfolding [$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let extra ← extra.mapM fun term => `(Lean.Parser.Tactic.simpLemma| $term:term)
    `(tactic|
      (apply Library.capture_in $checked $agreement (by decide +kernel) (by decide +kernel)
         _ _ _ _ _ _ (by metta_literal; rfl) rfl
       simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
         Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, Library.bind, List.zip, List.zipWith,
         List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.find?,
         CettaWireAtom.applySubst_encode]
       first
         | exact $fact
         | simpa using $fact
         | simpa [encoded, number, CettaWireAtom.encode, CettaWireAtom.encodeMany, $extra,*] using $fact))

/-- Capture any supported raw source head, including metadata inherited from the view's base. -/
syntax "metta_capture_agreed " term " from " term (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| metta_capture_agreed $agreement from $fact $[unfolding [$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let extra ← extra.mapM fun term => `(Lean.Parser.Tactic.simpLemma| $term:term)
    `(tactic|
      (refine PureData.raw_capture_returns _ [] _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ $fact
       · rw [← ($agreement).dispatch _ (by decide +kernel)]
         decide +kernel
       · intro index bounded
         rw [← ($agreement).demand _ index (by decide +kernel)]
         simp only [List.length_cons, List.length_nil, Nat.zero_add] at bounded
         revert index
         decide +kernel
       · decide
       · simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
           Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
           Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, Library.bind, List.map_cons, List.map_nil,
           CettaWireAtom.applySubst_encode, encoded, number, CettaWireAtom.encode, CettaWireAtom.encodeMany,
           $extra,*]))

/-- Close a call at evaluated arguments by a fact about the head at values. -/
syntax "metta_capture " term " using " term (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| metta_capture $checked using $fact $[unfolding [$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let extra ← extra.mapM fun term => `(Lean.Parser.Tactic.simpLemma| $term:term)
    `(tactic|
      (apply Library.capture $checked (by decide +kernel) _ _ _ _ _ _ (by metta_literal; rfl) rfl
       simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
         Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, Library.bind, List.zip, List.zipWith,
         List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.find?,
         CettaWireAtom.applySubst_encode]
       first
         | exact $fact
         | simpa using $fact
         | simpa [encoded, number, CettaWireAtom.encode, CettaWireAtom.encodeMany, $extra,*] using $fact))

/-- Close a call at evaluated arguments by a fact about the head at values, in the same program,
for any head the program defines. -/
syntax "metta_capture_any " term (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| metta_capture_any $fact $[unfolding [$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    let extra ← extra.mapM fun term => `(Lean.Parser.Tactic.simpLemma| $term:term)
    `(tactic|
      (refine PureData.raw_capture_returns _ [] _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ $fact
       · decide +kernel
       · intro index bounded
         simp only [List.length_cons, List.length_nil, Nat.zero_add] at bounded
         revert index
         decide +kernel
       · decide
       · simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
           Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
           Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, Library.bind, List.map_cons, List.map_nil,
           CettaWireAtom.applySubst_encode, encoded, number, CettaWireAtom.encode, CettaWireAtom.encodeMany,
           $extra,*]))

/-- Lift a fact about a base head at values into the library's runtime: `metta_lift check [names] fact`,
with one distinct name per value. -/
syntax "metta_lift " term:max " [" str,* "] " term:max : tactic
macro_rules
  | `(tactic| metta_lift $checked [$names,*] $fact) => `(tactic|
      exact Library.lift_call $checked (by decide +kernel) (by decide) (by decide +kernel) (by decide)
        [$names,*] (by decide) rfl (by decide +kernel) $fact)

/-- One evaluator step, then the steps it opens, as far as each goes. -/
syntax "metta_eval" (" [" term,* "]")? (" with " term)? (" in " term)? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| metta_eval $[[$lemmas,*]]? $[with $checked]? $[in $agreement]? $[unfolding [$unfold,*]]?) => do
    let lemmas := (lemmas.map (·.getElems)).getD #[]
    let unfold := (unfold.map (·.getElems)).getD #[]
    let unfoldLemmas ← unfold.mapM fun term => `(Lean.Parser.Tactic.simpLemma| $term:term)
    let recurse ← `(tactic| metta_eval [$lemmas,*] $[with $checked]? $[in $agreement]? unfolding [$unfold,*])
    let again ← `(tacticSeq| $recurse:tactic)
    let nothing ← `(tactic| fail "metta_eval: no supplied fact closes this call")
    let captures ← match checked, agreement with
      | some _, some agreement => lemmas.foldlM (init := nothing) fun rest fact =>
          `(tactic| first
            | metta_capture_agreed $agreement from $fact unfolding [$unfold,*]
            | $(⟨rest.raw⟩):tacticSeq)
      | none, some _ => Lean.Macro.throwError "metta_eval: source-view agreement requires a library check"
      | some checked, none => lemmas.foldlM (init := nothing) fun rest fact =>
          `(tactic| first
            | metta_capture $checked using $fact unfolding [$unfold,*]
            | metta_capture_any $fact unfolding [$unfold,*]
            | metta_capture_mixed $fact unfolding [$unfold,*]
            | $(⟨rest.raw⟩):tacticSeq)
      | none, none => lemmas.foldlM (init := nothing) fun rest fact =>
          `(tactic| first | metta_capture_any $fact unfolding [$unfold,*] | $(⟨rest.raw⟩):tacticSeq)
    let capturing ← `(tacticSeq| $captures:tactic)
    let data ← match agreement with
      | none => `(tactic| apply data_returns _ _ _ _ _ (by decide +kernel))
      | some agreement => `(tactic| apply data_in_program_returns $agreement _ _ _ _
          (by decide +kernel) (by decide +kernel))
    `(tactic| first
      | exact bound_returns _ _ _ (by rfl)
      | exact literal_returns _ _ _ _
      | exact Eval.symbol_returns _ _ _ _
      | focus
          (refine bound_answer_returns _ _ _ (by rfl) ?_
           simp [encoded, number, CettaWireAtom.encode, CettaWireAtom.encodeMany, $unfoldLemmas,*]
           done)
      | focus
          ($data:tactic
           first
             | (rfl; done)
             | skip
           try simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
             Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
             Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, Library.bind, encoded, number,
             CettaWireAtom.encode, CettaWireAtom.encodeMany, $unfoldLemmas,*]
           done)
      | (apply pure_let_returns _ _ _ _ _ _ _ _ (by rfl)
         $recurse
         try $again)
      | (apply pure_let_star_returns _ _ _ _ _ _ _ rfl
         try $again)
      | (apply pure_if_returns
         $recurse
         first
           | (simp only [decide_true, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_one_ne_zero,
               Nat.succ_ne_zero, decide_eq_true_eq, eq_self_iff_true, Mettapedia.GSLT.LanguageDef.CettaWire.Term.string.injEq,
               Mettapedia.GSLT.LanguageDef.CettaWire.Term.natural.injEq,
               $unfoldLemmas,*]
              try $again)
           | try $again)
      | (apply pure_case_returns _ _ _ _ _ _ _ _ rfl
         $recurse
         try (focus (metta_select [CettaWireAtom.encode, CettaWireAtom.encodeMany, encoded, number, $unfold,*]; done))
         try (intro selected body selection
              metta_select [CettaWireAtom.encode, CettaWireAtom.encodeMany, encoded, number, $unfold,*] at selection
              obtain ⟨bindings, branch⟩ := selection
              subst bindings
              subst branch
              try $again))
      | (apply natural_equal_returns) <;> $recurse
      | (apply string_equal_returns) <;> $recurse
      | (apply term_equal_returns) <;> $recurse
      | (apply natural_le_returns) <;> $recurse
      | (apply natural_lt_returns) <;> $recurse
      | (apply natural_add_returns) <;> $recurse
      | (apply natural_pred_returns) <;> $recurse
      | $capturing)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit
