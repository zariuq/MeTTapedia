import Mettapedia.Languages.MM0.Presentation.ContextData

/-!
# Occurrence lists representing MM0 support

The computational representation retains occurrences instead of repeatedly
sorting and deduplicating unions. Its finite-set interpretation is exactly
the independently specified support. Undefined variables cause refusal;
an empty, successfully computed support is a different outcome. This is
occurrence support, not the binder-sensitive free-variable calculation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalSupport

open Kernel ComputationalContext
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

def indices? (context : Context) : Preterm → Option (List Nat)
  | .var index => do
      match ← context[index]? with
      | .bound _ => pure [index]
      | .regular _ dependencies => pure (dependencies.sort (· ≤ ·))
  | .term _ => some []
  | .app function argument => do
      let left ← indices? context function
      let right ← indices? context argument
      pure (left ++ right)

def encodeResult : Option (List Nat) → Term
  | none => .sym "None"
  | some indices => .expr [.sym "Some", encodeNaturals indices]

def decodeResult : Term → Option (Option (List Nat))
  | .sym "None" => some none
  | .expr [.sym "Some", values] => (decodeNaturals values).map some
  | _ => none

@[simp] theorem decodeResult_encode (result : Option (List Nat)) :
    decodeResult (encodeResult result) = some result := by
  cases result <;> simp [decodeResult, encodeResult]

theorem encodeResult_injective : Function.Injective encodeResult := by
  intro first second same
  have decoded := congrArg decodeResult same
  simpa using decoded

theorem indices_meaning (context : Context) (expression : Preterm) :
    (indices? context expression).map List.toFinset = Preterm.support? context expression := by
  induction expression with
  | var index =>
    cases found : context[index]? with
    | none => simp [indices?, Preterm.support?, found]
    | some binder => cases binder <;> simp [indices?, Preterm.support?, found]
  | term _ => rfl
  | app function argument ihFunction ihArgument =>
    cases left : indices? context function <;> cases right : indices? context argument <;>
      simp [indices?, Preterm.support?, left, right, ← ihFunction, ← ihArgument]

theorem indices_sound {context : Context} {expression : Preterm} {indices : List Nat}
    (computed : indices? context expression = some indices) :
    Preterm.Supports context expression indices.toFinset := by
  apply Preterm.support_sound
  rw [← indices_meaning, computed]
  rfl

theorem indices_complete {context : Context} {expression : Preterm} {support : Finset Nat}
    (derived : Preterm.Supports context expression support) :
    ∃ indices, indices? context expression = some indices ∧ indices.toFinset = support := by
  have meaning := indices_meaning context expression
  rw [derived.eval] at meaning
  cases computed : indices? context expression with
  | none => simp [computed] at meaning
  | some indices =>
    exact ⟨indices, rfl, by simpa [computed] using meaning⟩

theorem indices_refusal_iff (context : Context) (expression : Preterm) :
    indices? context expression = none ↔ ¬ ∃ support, Preterm.Supports context expression support := by
  constructor
  · intro refused ⟨support, derived⟩
    obtain ⟨indices, computed, _⟩ := indices_complete derived
    rw [refused] at computed
    contradiction
  · intro noSupport
    cases computed : indices? context expression with
    | none => rfl
    | some indices => exact False.elim (noSupport ⟨indices.toFinset, indices_sound computed⟩)

theorem indices_membership {context : Context} {expression : Preterm} {indices : List Nat}
    (computed : indices? context expression = some indices) (index : Nat) :
    index ∈ indices ↔ Preterm.HasVar context index expression := by
  simpa using (indices_sound computed).mem_iff_hasVar index

theorem repeated_occurrences_are_retained :
    indices? [.bound 0] (.app (.var 0) (.var 0)) = some [0, 0] := rfl

theorem repeated_occurrences_have_single_set_member :
    (indices? [.bound 0] (.app (.var 0) (.var 0))).map List.toFinset = some {0} := by
  simp [indices?, List.toFinset_cons]

theorem empty_support_is_success : indices? [] (.term 0) = some [] := rfl

theorem undefined_variable_is_not_empty_support : indices? [] (.var 0) = none := rfl

theorem a_valid_child_does_not_hide_an_undefined_child :
    indices? [.bound 0] (.app (.var 0) (.var 1)) = none := rfl

theorem malformed_encoded_support_refuses : decodeResult (.expr [.sym "Some", .sym "Nil"]) = none := rfl

end Mettapedia.Languages.MM0.Presentation.ComputationalSupport
