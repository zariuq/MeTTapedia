import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangProgramCompilation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxCanonical

/-! Every compiled Erlang value is fixed by the emitted kernel's canonical
commit, including recursively captured closures. This is a representation
law, separate from source-value typing and evaluation adequacy. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangCompilation

open Mettapedia.OSLF.MeTTaIL Syntax CanonicalBags
open Mettapedia.Languages

theorem word_canonical (number : Nat) : canon (word number) = word number := by
  simp [word, canon_collection, arrange_vec, List.map_map, node, canon_apply]

theorem count_canonical (number : Nat) : canon (count number) = count number := by
  induction number with
  | zero => simp [count, node, canon_apply]
  | succ number ih => simp [count, node, canon_apply, ih]

theorem code_canonical (number : Nat) : canon (code number) = code number := by
  simp [code, node, canon_apply, word_canonical]

theorem literal_canonical (datum : Erlang.Literal) : canon (literal datum) = literal datum := by
  cases datum with
  | atom text =>
      simp [literal, ErlangMailbox.atom, ErlangMailbox.node, canon_apply, canon_collection, arrange_vec,
        List.map_flatMap]
  | integer number =>
      change canon (node "ErInteger" [node (if number < 0 then "ErNegative" else "ErNonnegative"), word number.natAbs]) =
        node "ErInteger" [node (if number < 0 then "ErNegative" else "ErNonnegative"), word number.natAbs]
      simp [node, canon_apply, word_canonical]
  | nil => simp [literal, node, canon_apply]

theorem value_canonical (source : Erlang.Value) : canon (value source) = value source := by
  refine Erlang.Value.rec
    (motive_1 := fun value => canon (ErlangCompilation.value value) = ErlangCompilation.value value)
    (motive_2 := fun values =>
      canon (valueList values) = valueList values ∧ canon (environment values) = environment values)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ source
  · intro datum
    exact literal_canonical datum
  · intro identity
    simp [value, node, canon_apply, word_canonical]
  · intro fields ih
    simp [value, node, canon_apply, ih.1]
  · intro head tail headIH tailIH
    simp [value, node, canon_apply, headIH, tailIH]
  · intro arity function captured ih
    cases function <;> simp [value, node, canon_apply, count_canonical, code_canonical, ih.2]
  · simp [valueList, environment, node, canon_apply]
  · intro head tail headIH tailIH
    simp [valueList, environment, node, canon_apply, headIH, tailIH.1, tailIH.2]

theorem mailbox_canonical (box : Erlang.Mailbox Erlang.Value) :
    canon (ErlangMailbox.mailbox value box) = ErlangMailbox.mailbox value box :=
  ErlangMailbox.Execution.canon_mailbox value value_canonical box

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangCompilation
