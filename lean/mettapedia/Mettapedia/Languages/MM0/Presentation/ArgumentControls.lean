import Mettapedia.Languages.MM0.Presentation.ArgumentCorrespondence

/-! # Boundness, saturation, sort and arity controls for authored MM0 arguments -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalArguments.Controls

open Kernel ComputationalContext ComputationalTyping
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => argumentProgram
local notation "H" => computationalHost

private def table : SignatureTable := [(0, ⟨[.regular 0 ∅], 1, ∅⟩), (1, ⟨[], 1, ∅⟩)]
private def target : Context := [.bound 0, .regular 1 {0}]

private theorem binder_checked (expression : Preterm) (binder : Kernel.Binder) (result : Bool)
    (checked : Preterm.checkBinder (signatureOf table) target expression binder = result) :
    Applies P H "mm0:check-binder"
      [encodeTable table, encodeContext target, encode expression, encodeBinder binder] (boolean result) := by
  simpa only [checked] using binder_computes table target expression binder

private theorem arguments_checked (expressions : List Preterm) (formal : Context) (result : Bool)
    (checked : Substitution.checkArguments (signatureOf table) target expressions formal = result) :
    Applies P H "mm0:check-arguments"
      [encodeTable table, encodeContext target, encodeExpressions expressions, encodeContext formal]
      (boolean result) := by
  simpa only [checked] using arguments_computes table target expressions formal

theorem bound_variable_of_matching_sort_accepts :
    Applies P H "mm0:check-binder"
      [encodeTable table, encodeContext target, encode (.var 0), encodeBinder (.bound 0)] (.sym "True") :=
  binder_checked _ _ true (by decide)

theorem wrong_bound_sort_refuses :
    Applies P H "mm0:check-binder"
      [encodeTable table, encodeContext target, encode (.var 0), encodeBinder (.bound 1)] (.sym "False") :=
  binder_checked _ _ false (by decide)

theorem regular_variable_is_not_a_bound_argument :
    Applies P H "mm0:check-binder"
      [encodeTable table, encodeContext target, encode (.var 1), encodeBinder (.bound 1)] (.sym "False") :=
  binder_checked _ _ false (by decide)

theorem compound_expression_is_not_a_bound_argument :
    Applies P H "mm0:check-binder"
      [encodeTable table, encodeContext target, encode (.app (.term 0) (.var 0)), encodeBinder (.bound 1)]
      (.sym "False") := binder_checked _ _ false (by decide)

theorem partial_application_is_not_a_regular_argument :
    Applies P H "mm0:check-binder"
      [encodeTable table, encodeContext target, encode (.term 0), encodeBinder (.regular 1 ∅)] (.sym "False") :=
  binder_checked _ _ false (by decide)

theorem saturated_application_accepts :
    Applies P H "mm0:check-binder"
      [encodeTable table, encodeContext target, encode (.app (.term 0) (.var 0)), encodeBinder (.regular 1 ∅)]
      (.sym "True") := binder_checked _ _ true (by decide)

theorem wrong_regular_sort_refuses :
    Applies P H "mm0:check-binder"
      [encodeTable table, encodeContext target, encode (.term 1), encodeBinder (.regular 0 ∅)] (.sym "False") :=
  binder_checked _ _ false (by decide)

/-- Typing a replacement does not establish its independence from another image. -/
theorem typing_alone_does_not_establish_independence :
    Applies P H "mm0:check-binder"
      [encodeTable table, encodeContext target, encode (.var 1), encodeBinder (.regular 1 ∅)] (.sym "True") ∧
      Substitution.checkPair target 0 0 ((.regular 1 ∅, .var 1), 1) = false := by
  exact ⟨binder_checked _ _ true (by decide), by decide⟩

theorem exact_argument_list_accepts :
    Applies P H "mm0:check-arguments"
      [encodeTable table, encodeContext target, encodeExpressions [.var 0, .term 1],
        encodeContext [.bound 0, .regular 1 ∅]] (.sym "True") := arguments_checked _ _ true (by decide)

theorem reversed_argument_list_refuses :
    Applies P H "mm0:check-arguments"
      [encodeTable table, encodeContext target, encodeExpressions [.term 1, .var 0],
        encodeContext [.bound 0, .regular 1 ∅]] (.sym "False") := arguments_checked _ _ false (by decide)

theorem missing_argument_refuses :
    Applies P H "mm0:check-arguments"
      [encodeTable table, encodeContext target, encodeExpressions [.var 0],
        encodeContext [.bound 0, .regular 1 ∅]] (.sym "False") := arguments_checked _ _ false (by decide)

theorem extra_argument_refuses :
    Applies P H "mm0:check-arguments"
      [encodeTable table, encodeContext target, encodeExpressions [.var 0, .term 1, .term 1],
        encodeContext [.bound 0, .regular 1 ∅]] (.sym "False") := arguments_checked _ _ false (by decide)

theorem empty_formal_context_requires_empty_arguments :
    Applies P H "mm0:check-arguments"
      [encodeTable table, encodeContext target, encodeExpressions [], encodeContext []] (.sym "True") ∧
    Applies P H "mm0:check-arguments"
      [encodeTable table, encodeContext target, encodeExpressions [.term 1], encodeContext []] (.sym "False") :=
  ⟨arguments_checked _ _ true (by decide), arguments_checked _ _ false (by decide)⟩

theorem cannot_accept_the_wrong_arity :
    ¬ Applies P H "mm0:check-arguments"
      [encodeTable table, encodeContext target, encodeExpressions [.var 0],
        encodeContext [.bound 0, .regular 1 ∅]] (.sym "True") := by
  intro accepted
  have impossible := accepted_arguments_have_exact_arity table target [.var 0] [.bound 0, .regular 1 ∅] accepted
  simp at impossible

theorem zero_fuel_does_not_refuse_valid_arguments :
    apply P H 0 "mm0:check-arguments"
      [encodeTable table, encodeContext target, encodeExpressions [.var 0, .term 1],
        encodeContext [.bound 0, .regular 1 ∅]] = .exhausted := rfl

end Mettapedia.Languages.MM0.Presentation.ComputationalArguments.Controls
