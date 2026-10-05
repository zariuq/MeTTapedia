import Mettapedia.Languages.MM0.Presentation.FreeVariablesCorrespondence

/-! # Binding, malformed-child and outcome controls for authored MM0 computation -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalFreeVariables.ExecutionControls

open Kernel ComputationalContext ComputationalTyping ComputationalArguments
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => freeVariablesProgram
local notation "H" => computationalHost
local notation "R" => ComputationalSupport.encodeResult

private def context : Context := [.bound 0, .bound 0, .regular 1 {0, 1}]
private def table (bindings : Finset Nat) : SignatureTable :=
  [(0, ⟨[.bound 0, .regular 1 bindings], 1, ∅⟩),
   (1, ⟨[.bound 0], 1, {0}⟩), (2, ⟨[], 1, ∅⟩)]
private def body : Preterm := .applyArgs (.term 0) [.var 0, .var 2]

private theorem checked (declarations : SignatureTable) (target : Context) (source : Preterm) (result : Finset Nat)
    (known : Preterm.freeVariables? (signatureOf declarations) target source = some result) :
    ∃ free, Applies P H "mm0:free-variables" [encodeTable declarations, encodeContext target, encode source]
      (R (some free)) ∧ free.toFinset = result :=
  (free_variables_accepts_iff _ _ _ _).mpr ((Preterm.freeVariables_eq_some_iff _ _ _ _).mp known)

private theorem refused (declarations : SignatureTable) (target : Context) (source : Preterm)
    (known : Preterm.freeVariables? (signatureOf declarations) target source = none) :
    Applies P H "mm0:free-variables" [encodeTable declarations, encodeContext target, encode source] (.sym "None") :=
  (free_variables_refuses_iff _ _ _).mpr ((Preterm.freeVariables_none_iff _ _ _).mp known)

theorem typed_binding_images_keep_order_and_duplicates :
    Applies P H "mm0:free-images" [encodeContext [.bound 0, .bound 0], encodeContext [.bound 0, .bound 0],
      encodeExpressions [.var 1, .var 0], encodeNaturals [1, 0, 1]] (R (some [0, 1, 0])) := by
  simpa only [Controls.bound_images_keep_order_and_duplicates] using
    images_computes [.bound 0, .bound 0] [.bound 0, .bound 0] [.var 1, .var 0] [1, 0, 1]

theorem regular_formal_cannot_capture :
    Applies P H "mm0:free-images" [encodeContext [.bound 0], encodeContext [.regular 0 ∅],
      encodeExpressions [.var 0], encodeNaturals [0]] (.sym "None") := by
  simpa only [Controls.regular_formal_is_not_a_binder, ComputationalSupport.encodeResult] using
    images_computes [.bound 0] [.regular 0 ∅] [.var 0] [0]

theorem same_sort_regular_target_cannot_be_a_binding_image :
    Applies P H "mm0:free-images" [encodeContext [.regular 0 ∅], encodeContext [.bound 0],
      encodeExpressions [.var 0], encodeNaturals [0]] (.sym "None") := by
  simpa only [Controls.same_sort_regular_target_is_not_a_bound_image, ComputationalSupport.encodeResult] using
    images_computes [.regular 0 ∅] [.bound 0] [.var 0] [0]

theorem wrong_sort_binding_image_refuses :
    Applies P H "mm0:free-images" [encodeContext [.bound 1], encodeContext [.bound 0],
      encodeExpressions [.var 0], encodeNaturals [0]] (.sym "None") := by
  simpa only [Controls.wrong_sort_bound_image_refuses, ComputationalSupport.encodeResult] using
    images_computes [.bound 1] [.bound 0] [.var 0] [0]

theorem missing_binding_image_refuses :
    Applies P H "mm0:free-images" [encodeContext [.bound 0], encodeContext [.bound 0],
      encodeExpressions [], encodeNaturals [0]] (.sym "None") := by
  simpa only [Controls.missing_image_refuses, ComputationalSupport.encodeResult] using
    images_computes [.bound 0] [.bound 0] [] [0]

theorem bound_argument_has_no_automatic_contribution :
    Applies P H "mm0:free-contributions" [encodeContext [.bound 0], encodeContext [.bound 0],
      encodeExpressions [.var 0], encodeContext [.bound 0], encodeFreeLists [[0]]] (R (some [])) := by
  simpa only [Controls.a_bound_argument_does_not_contribute_itself] using
    contributions_computes [.bound 0] [.bound 0] [.var 0] [.bound 0] [[0]]

theorem undeclared_binding_retains_occurrences :
    Applies P H "mm0:free-contributions" [encodeContext [.bound 0], encodeContext [.bound 0, .regular 0 ∅],
      encodeExpressions [.var 0, .var 0], encodeContext [.bound 0, .regular 0 ∅], encodeFreeLists [[0], [0]]]
      (R (some [0])) := by
  simpa only [Controls.an_undeclared_binding_keeps_occurrences_free] using
    contributions_computes [.bound 0] [.bound 0, .regular 0 ∅] [.var 0, .var 0] [.bound 0, .regular 0 ∅] [[0], [0]]

theorem declared_binding_removes_occurrences :
    Applies P H "mm0:free-contributions" [encodeContext [.bound 0], encodeContext [.bound 0, .regular 0 {0}],
      encodeExpressions [.var 0, .var 0], encodeContext [.bound 0, .regular 0 {0}], encodeFreeLists [[0], [0]]]
      (R (some [])) := by
  simpa only [Controls.a_declared_binding_removes_its_argument_occurrences] using
    contributions_computes [.bound 0] [.bound 0, .regular 0 {0}] [.var 0, .var 0] [.bound 0, .regular 0 {0}] [[0], [0]]

theorem other_free_occurrences_are_retained :
    Applies P H "mm0:free-contributions" [encodeContext [.bound 0, .bound 0], encodeContext [.bound 0, .regular 0 {0}],
      encodeExpressions [.var 0, .var 1], encodeContext [.bound 0, .regular 0 {0}], encodeFreeLists [[0], [0, 1, 1]]]
      (R (some [1, 1])) := by
  simpa only [Controls.binding_does_not_remove_other_variables] using
    contributions_computes [.bound 0, .bound 0] [.bound 0, .regular 0 {0}] [.var 0, .var 1]
      [.bound 0, .regular 0 {0}] [[0], [0, 1, 1]]

theorem a_missing_argument_free_list_refuses :
    Applies P H "mm0:free-contributions" [encodeContext [], encodeContext [.regular 0 ∅],
      encodeExpressions [], encodeContext [.regular 0 ∅], encodeFreeLists []] (.sym "None") :=
  contributions_computes [] [.regular 0 ∅] [] [.regular 0 ∅] []

theorem an_extra_argument_free_list_refuses :
    Applies P H "mm0:free-contributions" [encodeContext [], encodeContext [],
      encodeExpressions [], encodeContext [], encodeFreeLists [[]]] (.sym "None") :=
  contributions_computes [] [] [] [] [[]]

theorem declared_binding_computes_complete_expression :
    ∃ free, Applies P H "mm0:free-variables" [encodeTable (table {0}), encodeContext context, encode body]
      (R (some free)) ∧ free.toFinset = {1} := checked _ _ _ _ (by decide)

theorem removing_binding_changes_the_same_expression :
    ∃ free, Applies P H "mm0:free-variables" [encodeTable (table ∅), encodeContext context, encode body]
      (R (some free)) ∧ free.toFinset = {0, 1} := checked _ _ _ _ (by decide)

theorem an_old_binding_result_is_not_valid_in_the_changed_theory :
    ¬ ∃ free, Applies P H "mm0:free-variables" [encodeTable (table ∅), encodeContext context, encode body]
      (R (some free)) ∧ free.toFinset = {1} := by
  rw [free_variables_accepts_iff, ← Preterm.freeVariables_eq_some_iff]
  decide

theorem returned_binding_image_contributes :
    ∃ free, Applies P H "mm0:free-variables"
      [encodeTable (table {0}), encodeContext context, encode (.app (.term 1) (.var 1))]
      (R (some free)) ∧ free.toFinset = {1} := checked _ _ _ _ (by decide)

theorem nested_bindings_remove_only_their_own_images :
    ∃ free, Applies P H "mm0:free-variables"
      [encodeTable (table {0}), encodeContext context, encode (.applyArgs (.term 0) [.var 1, body])]
      (R (some free)) ∧ free.toFinset = ∅ := checked _ _ _ _ (by decide)

theorem a_closed_constant_has_a_successful_empty_result :
    ∃ free, Applies P H "mm0:free-variables" [encodeTable (table {0}), encodeContext context, encode (.term 2)]
      (R (some free)) ∧ free.toFinset = ∅ := checked _ _ _ _ (by decide)

theorem valid_first_child_cannot_hide_invalid_second_child :
    Applies P H "mm0:free-variables" [encodeTable (table {0}), encodeContext context,
      encode (.applyArgs (.term 0) [.var 0, .var 9])] (.sym "None") := refused _ _ _ (by decide)

theorem valid_second_child_cannot_hide_invalid_first_child :
    Applies P H "mm0:free-variables" [encodeTable (table {0}), encodeContext context,
      encode (.applyArgs (.term 0) [.var 9, .var 2])] (.sym "None") := refused _ _ _ (by decide)

theorem regular_argument_cannot_replace_a_bound_one :
    Applies P H "mm0:free-variables" [encodeTable (table {0}), encodeContext context,
      encode (.applyArgs (.term 0) [.var 2, .var 2])] (.sym "None") := refused _ _ _ (by decide)

theorem partial_application_refuses :
    Applies P H "mm0:free-variables" [encodeTable (table {0}), encodeContext context,
      encode (.app (.term 0) (.var 0))] (.sym "None") := refused _ _ _ (by decide)

theorem overapplication_refuses :
    Applies P H "mm0:free-variables" [encodeTable (table {0}), encodeContext context,
      encode (.app body (.term 2))] (.sym "None") := refused _ _ _ (by decide)

theorem unknown_term_refuses_even_with_valid_children :
    Applies P H "mm0:free-variables" [encodeTable (table {0}), encodeContext context,
      encode (.app (.term 99) (.var 0))] (.sym "None") := refused _ _ _ (by decide)

theorem an_invalid_return_dependency_refuses :
    Applies P H "mm0:free-variables"
      [encodeTable [(0, ⟨[.bound 0], 1, {1}⟩)], encodeContext context, encode (.app (.term 0) (.var 0))]
      (.sym "None") := refused _ _ _ (by decide)

theorem an_invalid_binding_dependency_refuses :
    Applies P H "mm0:free-variables" [encodeTable (table {1}), encodeContext context, encode body]
      (.sym "None") := refused _ _ _ (by decide)

theorem zero_allowance_is_unfinished_for_a_valid_request :
    apply P H 0 "mm0:free-variables" [encodeTable (table {0}), encodeContext context, encode body] = .exhausted := rfl

theorem malformed_child_does_not_authorize_an_empty_answer :
    ¬ Applies P H "mm0:free-variables" [encodeTable (table {0}), encodeContext context,
      encode (.applyArgs (.term 0) [.var 0, .var 9])] (R (some [])) := by
  intro accepted
  have impossible := accepted.deterministic valid_first_child_cannot_hide_invalid_second_child
  cases impossible

theorem term_and_variable_with_equal_indices_remain_distinct :
    encode (.term 0) ≠ encode (.var 0) := by
  intro same
  cases encode_injective same

end Mettapedia.Languages.MM0.Presentation.ComputationalFreeVariables.ExecutionControls
