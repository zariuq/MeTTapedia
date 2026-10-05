import Mettapedia.Languages.MM0.Kernel.Term
import Mettapedia.Languages.MM0.Kernel.Typing
import Mettapedia.Languages.MM0.MeTTa.ListAccess
import Mathlib.Data.Finset.Sort

/-!
# MM0 typed data in the native source carrier

The retained service uses native numeric atoms and constructor expressions.
This representation is distinct from the string-literal carrier of the
equation programs. The map below encodes data, not checking computations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.Data

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Kernel (Preterm)
open Store (natural)

def dependencies (values : Finset Nat) : Atom :=
  ListAccess.listValue ((values.sort (· ≤ ·)).map natural)

def binder : Kernel.Binder → Atom
  | .bound sort => ListAccess.listValue [.symbol "MM0:Bound", natural sort]
  | .regular sort values =>
      ListAccess.listValue [.symbol "MM0:Regular", natural sort, dependencies values]

def context (values : Kernel.Context) : Atom := ListAccess.listValue (values.map binder)

def inferred : Option Kernel.ExpressionType → Atom
  | none => .symbol "None"
  | some (remaining, sort) => .expression [.symbol "MM0:Inferred", context remaining, natural sort]

def declaration (value : Kernel.TermDecl) : Atom :=
  ListAccess.listValue [.symbol "MM0:TermDecl", context value.arguments,
    natural value.resultSort, dependencies value.dependencies]

theorem natural_injective : Function.Injective natural := by
  intro first second same
  have numbers : (first : Int) = (second : Int) := by simpa [natural] using same
  exact Int.ofNat.inj numbers

theorem dependencies_injective : Function.Injective dependencies := by
  intro first second same
  have items : first.sort (· ≤ ·) = second.sort (· ≤ ·) :=
    (List.map_injective_iff.mpr natural_injective) (by
      simpa [dependencies, ListAccess.listValue] using same)
  simpa using congrArg List.toFinset items

theorem binder_injective : Function.Injective binder := by
  intro first second same
  cases first with
  | bound first =>
      cases second with
      | bound second =>
          have numbers : natural first = natural second := by
            simpa [binder, ListAccess.listValue] using same
          exact congrArg Kernel.Binder.bound (natural_injective numbers)
      | regular => simp [binder, ListAccess.listValue] at same
  | regular first deps =>
      cases second with
      | bound => simp [binder, ListAccess.listValue] at same
      | regular second other =>
          have parts : natural first = natural second ∧ dependencies deps = dependencies other := by
            simpa [binder, ListAccess.listValue] using same
          exact congrArg₂ Kernel.Binder.regular
            (natural_injective parts.1) (dependencies_injective parts.2)

theorem context_injective : Function.Injective context := by
  intro first second same
  apply List.map_injective_iff.mpr binder_injective
  simpa [context, ListAccess.listValue] using same

theorem inferred_injective : Function.Injective inferred := by
  intro first second same
  cases first with
  | none => cases second <;> simp_all [inferred]
  | some first =>
      cases second with
      | none => simp [inferred] at same
      | some second =>
          rcases first with ⟨remaining, sort⟩
          rcases second with ⟨other, result⟩
          have parts : context remaining = context other ∧ natural sort = natural result := by
            simpa [inferred] using same
          exact congrArg some (Prod.ext (context_injective parts.1) (natural_injective parts.2))

def preterm : Preterm → Atom
  | .var index => .expression [.symbol "MM0:Var", natural index]
  | .term index => .expression [.symbol "MM0:Term", natural index]
  | .app function argument => .expression [.symbol "MM0:App", preterm function, preterm argument]

theorem preterm_injective : Function.Injective preterm := by
  intro first
  induction first with
  | var index =>
      intro second same
      cases second <;> simp [preterm, natural] at same
      cases same
      rfl
  | term index =>
      intro second same
      cases second <;> simp [preterm, natural] at same
      cases same
      rfl
  | app function argument ihFunction ihArgument =>
      intro second same
      cases second with
      | var | term => simp [preterm] at same
      | app otherFunction otherArgument =>
          simp only [preterm, Atom.expression.injEq, List.cons.injEq, true_and, and_true] at same
          exact congrArg₂ Preterm.app (ihFunction same.1) (ihArgument same.2)

open Mettapedia.Languages.MeTTa.PeTTa.SourceProgram (Literal)

theorem natural_literal (index : Nat) : Literal (natural index) := .grounded _

private theorem list_wrapper_literal (items : List Atom) (literal : Literal (.expression items)) :
    Literal (ListAccess.listValue items) := by
  apply Literal.constructor "MM0:L" [.expression items] (by decide)
  simpa using literal

theorem dependencies_literal (values : Finset Nat) : Literal (dependencies values) := by
  apply list_wrapper_literal
  apply Literal.expression
  · intro first rest same
    cases sorted : values.sort (· ≤ ·) with
    | nil => simp [sorted] at same
    | cons index indices => simp [sorted, natural] at same
  · intro item member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact natural_literal index

theorem binder_literal (value : Kernel.Binder) : Literal (binder value) := by
  cases value with
  | bound sort =>
      apply list_wrapper_literal
      apply Literal.constructor "MM0:Bound" [natural sort] (by decide)
      simpa using natural_literal sort
  | regular sort values =>
      apply list_wrapper_literal
      apply Literal.constructor "MM0:Regular" [natural sort, dependencies values] (by decide)
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact natural_literal sort
      · obtain rfl := List.mem_singleton.mp member
        exact dependencies_literal values

theorem context_literal (values : Kernel.Context) : Literal (context values) := by
  apply list_wrapper_literal
  apply Literal.expression
  · intro first rest same
    cases values with
    | nil => simp at same
    | cons value values =>
        cases value <;> simp [binder, ListAccess.listValue] at same
  · intro item member
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
    exact binder_literal value

theorem preterm_literal (value : Preterm) : Literal (preterm value) := by
  induction value with
  | var index =>
      apply Literal.constructor "MM0:Var" [natural index] (by decide)
      simpa using natural_literal index
  | term index =>
      apply Literal.constructor "MM0:Term" [natural index] (by decide)
      simpa using natural_literal index
  | app function argument ihFunction ihArgument =>
      apply Literal.constructor "MM0:App" [preterm function, preterm argument] (by decide)
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact ihFunction
      · obtain rfl := List.mem_singleton.mp member
        exact ihArgument

theorem optional_preterm_injective :
    Function.Injective (fun value : Option Preterm => ListAccess.optionValue (value.map preterm)) := by
  intro first second same
  cases first with
  | none => cases second <;> simp_all [ListAccess.optionValue]
  | some first =>
      cases second with
      | none => simp [ListAccess.optionValue] at same
      | some second =>
          simp only [Option.map_some, ListAccess.optionValue, Atom.expression.injEq,
            List.cons.injEq, true_and, and_true] at same
          exact congrArg some (preterm_injective same)

end Mettapedia.Languages.MM0.MeTTa.Data
