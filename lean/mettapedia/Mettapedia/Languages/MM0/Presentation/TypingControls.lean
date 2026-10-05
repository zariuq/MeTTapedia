import Mettapedia.Languages.MM0.Presentation.TypingTheory

/-! # Binding, saturation and result controls for authored MM0 typing -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalTyping.Controls

open Kernel ComputationalContext
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def table : SignatureTable := [
  (0, ⟨[], 0, {}⟩),
  (1, ⟨[.bound 0], 0, {}⟩),
  (2, ⟨[.regular 0 {}], 0, {}⟩),
  (3, ⟨[.regular 0 {}, .regular 0 {}], 0, {}⟩),
  (4, ⟨[], 1, {}⟩)]

private def context : Context := [.bound 0, .regular 0 {}, .bound 1]

private def run (expression : Preterm) (result : Option ExpressionType) : Prop :=
  Applies typingProgram computationalHost "mm0:infer"
    [encodeTable table, encodeContext context, encode expression] (encodeType result)

private theorem reference_run (expression : Preterm) :
    run expression (Preterm.infer (signatureOf table) context expression) :=
  infer_computes table context expression

theorem declared_constant : run (.term 0) (some ([], 0)) := by
  simpa [Preterm.infer, table, signatureOf] using reference_run (.term 0)

theorem bound_variable : run (.var 0) (some ([], 0)) := by
  simpa [Preterm.infer, context, Kernel.Binder.sort] using reference_run (.var 0)

theorem regular_variable : run (.var 1) (some ([], 0)) := by
  simpa [Preterm.infer, context, Kernel.Binder.sort] using reference_run (.var 1)

theorem missing_variable_refused : run (.var 3) none := by
  simpa [Preterm.infer, context] using reference_run (.var 3)

theorem undeclared_term_refused : run (.term 5) none := by
  simpa [Preterm.infer, table, signatureOf] using reference_run (.term 5)

theorem bound_argument_accepts_bound_variable : run (.app (.term 1) (.var 0)) (some ([], 0)) := by
  simpa [Preterm.infer, Preterm.boundSort?, table, context, signatureOf] using
    reference_run (.app (.term 1) (.var 0))

theorem bound_argument_refuses_regular_variable : run (.app (.term 1) (.var 1)) none := by
  simpa [Preterm.infer, Preterm.boundSort?, table, context, signatureOf] using
    reference_run (.app (.term 1) (.var 1))

theorem bound_argument_refuses_same_sort_constant : run (.app (.term 1) (.term 0)) none := by
  simpa [Preterm.infer, Preterm.boundSort?, table, signatureOf] using
    reference_run (.app (.term 1) (.term 0))

theorem bound_argument_refuses_wrong_sort : run (.app (.term 1) (.var 2)) none := by
  simpa [Preterm.infer, Preterm.boundSort?, table, context, signatureOf] using
    reference_run (.app (.term 1) (.var 2))

theorem regular_argument_accepts_constant : run (.app (.term 2) (.term 0)) (some ([], 0)) := by
  simpa [Preterm.infer, table, signatureOf] using reference_run (.app (.term 2) (.term 0))

theorem regular_argument_accepts_bound_variable : run (.app (.term 2) (.var 0)) (some ([], 0)) := by
  simpa [Preterm.infer, table, context, signatureOf, Kernel.Binder.sort] using
    reference_run (.app (.term 2) (.var 0))

theorem regular_argument_accepts_regular_variable : run (.app (.term 2) (.var 1)) (some ([], 0)) := by
  simpa [Preterm.infer, table, context, signatureOf, Kernel.Binder.sort] using
    reference_run (.app (.term 2) (.var 1))

theorem regular_argument_refuses_wrong_sort : run (.app (.term 2) (.term 4)) none := by
  simpa [Preterm.infer, table, signatureOf] using reference_run (.app (.term 2) (.term 4))

theorem regular_argument_refuses_unsaturated_term : run (.app (.term 2) (.term 2)) none := by
  simpa [Preterm.infer, table, signatureOf] using reference_run (.app (.term 2) (.term 2))

theorem unapplied_binders_retained : run (.term 3) (some ([.regular 0 {}, .regular 0 {}], 0)) := by
  simpa [Preterm.infer, table, signatureOf] using reference_run (.term 3)

theorem one_argument_consumes_one_binder :
    run (.app (.term 3) (.term 0)) (some ([.regular 0 {}], 0)) := by
  simpa [Preterm.infer, table, signatureOf] using reference_run (.app (.term 3) (.term 0))

theorem nested_application_saturates :
    run (.app (.app (.term 3) (.term 0)) (.term 0)) (some ([], 0)) := by
  simpa [Preterm.infer, table, signatureOf] using reference_run (.app (.app (.term 3) (.term 0)) (.term 0))

theorem saturated_term_cannot_take_another_argument : run (.app (.term 0) (.term 0)) none := by
  simpa [Preterm.infer, table, signatureOf] using reference_run (.app (.term 0) (.term 0))

theorem invalid_function_refuses : run (.app (.term 5) (.term 0)) none := by
  simpa [Preterm.infer, table, signatureOf] using reference_run (.app (.term 5) (.term 0))

theorem invalid_argument_refuses : run (.app (.term 2) (.term 5)) none := by
  simpa [Preterm.infer, table, signatureOf] using reference_run (.app (.term 2) (.term 5))

theorem wrong_claimed_sort_cannot_complete : ¬ run (.term 0) (some ([], 1)) := by
  intro wrong
  have same := wrong.deterministic declared_constant
  have impossible := encodeType_injective same
  cases impossible

theorem missing_term_cannot_complete_with_a_type (remaining : Context) (sort : Nat) :
    ¬ run (.term 5) (some (remaining, sort)) := by
  intro wrong
  have same := wrong.deterministic undeclared_term_refused
  have impossible := encodeType_injective same
  cases impossible

theorem zero_fuel_is_exhaustion :
    apply typingProgram computationalHost 0 "mm0:infer"
      [encodeTable table, encodeContext context, encode (.term 0)] = .exhausted := rfl

theorem large_symbol_and_sort_preserved :
    Applies typingProgram computationalHost "mm0:infer"
      [encodeTable [(18446744073709551616, ⟨[], 18446744073709551617, {}⟩)],
        encodeContext [], encode (.term 18446744073709551616)]
      (encodeType (some ([], 18446744073709551617))) := by
  simpa [Preterm.infer, signatureOf] using
    infer_computes [(18446744073709551616, ⟨[], 18446744073709551617, {}⟩)] []
      (.term 18446744073709551616)

theorem first_declaration_is_selected :
    Applies typingProgram computationalHost "mm0:infer"
      [encodeTable [(0, ⟨[], 7, {}⟩), (0, ⟨[], 8, {}⟩)], encodeContext [], encode (.term 0)]
      (encodeType (some ([], 7))) := by
  simpa [Preterm.infer, signatureOf] using infer_computes [(0, ⟨[], 7, {}⟩), (0, ⟨[], 8, {}⟩)] [] (.term 0)

end Mettapedia.Languages.MM0.Presentation.ComputationalTyping.Controls
