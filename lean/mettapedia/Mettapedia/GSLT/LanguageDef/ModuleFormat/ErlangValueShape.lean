import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangProgramCompilation
import Mettapedia.OSLF.MeTTaIL.GeneralVectorBindingAdmission

/-! Source Erlang values use only constructors and fixed vectors. In
particular, closure captures introduce neither binding metadata nor open
collection rests into an executable mailbox payload. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangCompilation

open Mettapedia.OSLF.MeTTaIL Syntax GeneralFirstOrderProjection
open Mettapedia.Languages

theorem node_vector (label : String) (arguments : List Pattern)
    (children : ∀ item ∈ arguments, VectorFirstOrder item) : VectorFirstOrder (node label arguments) :=
  .constructor label arguments children

private theorem one_vector (label : String) {child : Pattern} (shape : VectorFirstOrder child) :
    VectorFirstOrder (node label [child]) :=
  node_vector label [child] (by simpa only [List.mem_singleton, forall_eq] using shape)

private theorem two_vector (label : String) {first second : Pattern}
    (one : VectorFirstOrder first) (two : VectorFirstOrder second) : VectorFirstOrder (node label [first, second]) :=
  node_vector label [first, second] (by
    simpa [List.mem_cons] using And.intro one two)

private theorem three_vector (label : String) {first second third : Pattern}
    (one : VectorFirstOrder first) (two : VectorFirstOrder second) (three : VectorFirstOrder third) :
    VectorFirstOrder (node label [first, second, third]) :=
  node_vector label [first, second, third] (by
    simpa [List.mem_cons] using And.intro one (And.intro two three))

theorem word_vector (number : Nat) : VectorFirstOrder (word number) := by
  apply VectorFirstOrder.vector
  intro item member
  obtain ⟨digit, _, rfl⟩ := List.mem_map.mp member
  exact .constructor _ [] (by simp)

theorem count_vector (number : Nat) : VectorFirstOrder (count number) := by
  induction number with
  | zero => exact .constructor _ [] (by simp)
  | succ number ih => exact one_vector _ ih

theorem code_vector (number : Nat) : VectorFirstOrder (code number) := one_vector _ (word_vector number)

theorem atom_vector (text : String) : VectorFirstOrder (ErlangMailbox.atom text) := by
  apply one_vector
  apply VectorFirstOrder.vector
  intro item member
  obtain ⟨byte, _, present⟩ := List.mem_flatMap.mp member
  rcases List.mem_cons.mp present with rfl | present
  · exact .constructor _ [] (by simp)
  · have same := List.mem_singleton.mp present
    subst item
    exact .constructor _ [] (by simp)

theorem literal_vector (datum : Erlang.Literal) : VectorFirstOrder (literal datum) := by
  cases datum with
  | atom text => exact atom_vector text
  | integer number => exact two_vector _ (.constructor _ [] (by simp)) (word_vector number.natAbs)
  | nil => exact .constructor _ [] (by simp)

theorem function_vector (function : Erlang.FunctionRef) : VectorFirstOrder
    (match function with
      | .lambda reference => node "ErLambdaFunction" [code reference]
      | .recursive group slot => node "ErRecursiveFunction" [code group, count slot]) := by
  cases function with
  | lambda reference => exact one_vector _ (code_vector reference)
  | recursive group slot => exact two_vector _ (code_vector group) (count_vector slot)

theorem value_vector (source : Erlang.Value) : VectorFirstOrder (value source) := by
  refine Erlang.Value.rec
    (motive_1 := fun source => VectorFirstOrder (value source))
    (motive_2 := fun values => VectorFirstOrder (valueList values) ∧ VectorFirstOrder (environment values))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ source
  · exact literal_vector
  · intro identity
    exact one_vector _ (word_vector identity)
  · intro fields ih
    exact one_vector _ ih.1
  · intro head tail headIH tailIH
    exact two_vector _ headIH tailIH
  · intro arity function captured ih
    exact three_vector _ (count_vector arity) (function_vector function) ih.2
  · exact ⟨.constructor _ [] (by simp), .constructor _ [] (by simp)⟩
  · intro head tail headIH tailIH
    exact ⟨two_vector _ headIH tailIH.1, two_vector _ headIH tailIH.2⟩

theorem valueList_vector (items : List Erlang.Value) : VectorFirstOrder (valueList items) := by
  induction items with
  | nil => exact .constructor _ [] (by simp)
  | cons head tail ih => exact two_vector _ (value_vector head) ih

theorem environment_vector (items : List Erlang.Value) : VectorFirstOrder (environment items) := by
  induction items with
  | nil => exact .constructor _ [] (by simp)
  | cons head tail ih => exact two_vector _ (value_vector head) ih

theorem mapped_values (items : List Erlang.Value) : ErlangMailbox.values (items.map value) = valueList items := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp [valueList, ErlangMailbox.values, ih, node, ErlangMailbox.node]

theorem mailbox_vector (box : Erlang.Mailbox Erlang.Value) : VectorFirstOrder (ErlangMailbox.mailbox value box) := by
  unfold ErlangMailbox.mailbox
  simp only [mapped_values]
  exact three_vector _ (valueList_vector box.savedRev) (valueList_vector box.front) (valueList_vector box.rearRev)

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangCompilation
