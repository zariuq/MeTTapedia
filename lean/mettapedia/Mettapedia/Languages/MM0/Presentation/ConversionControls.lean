import Mettapedia.Languages.MM0.Presentation.ConversionCorrespondence

/-! # Supplied conversion evidence: positive and adversarial executions -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalConversion.Controls

open Kernel ComputationalContext ComputationalTyping ComputationalArguments ComputationalDefinitions
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def table : SignatureTable := [
  (0, ⟨[], 0, ∅⟩), (1, ⟨[.regular 0 ∅], 0, ∅⟩),
  (2, ⟨[.bound 0], 0, {0}⟩), (3, ⟨[], 1, ∅⟩),
  (4, ⟨[.regular 0 ∅, .regular 0 ∅], 0, ∅⟩), (5, ⟨[], 0, ∅⟩)]
private def definitions : DefinitionTable := [(1, ⟨[], .var 0⟩), (5, ⟨[0, 0], .var 0⟩)]
private def context : Context := [.bound 0, .regular 0 ∅, .bound 1]
private def identity (expression : Preterm) : Preterm := .app (.term 1) expression
private def unfoldIdentity (expression : Preterm) : ConvWitness := .unfold 1 [expression] []

private theorem accepted (witness : ConvWitness) (left right : Preterm) (sort : Nat)
    (computed : ConvWitness.conversion? (signatureOf table) (definitionsOf definitions) context witness =
      some ⟨left, right, sort⟩) :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness witness]
      (encodeConversion (some ⟨left, right, sort⟩)) := by
  simpa only [computed] using conversion_computes table definitions context witness

private theorem refused (witness : ConvWitness)
    (computed : ConvWitness.conversion? (signatureOf table) (definitionsOf definitions) context witness = none) :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness witness] (.sym "None") := by
  simpa only [computed, encodeConversion] using conversion_computes table definitions context witness

theorem typed_reflexivity :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness (.refl (.term 0))]
      (encodeConversion (some ⟨.term 0, .term 0, 0⟩)) := accepted _ _ _ _ (by decide +kernel)

theorem definition_computes_without_a_substitution_trace :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness (unfoldIdentity (.term 0))]
      (encodeConversion (some ⟨identity (.term 0), .term 0, 0⟩)) := accepted _ _ _ _ (by decide +kernel)

theorem symmetry_reverses_the_actual_endpoints :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness (.symm (unfoldIdentity (.term 0)))]
      (encodeConversion (some ⟨.term 0, identity (.term 0), 0⟩)) := accepted _ _ _ _ (by decide +kernel)

theorem transitivity_connects_actual_children :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context,
        encodeWitness (.trans (unfoldIdentity (.term 0)) (.refl (.term 0)))]
      (encodeConversion (some ⟨identity (.term 0), .term 0, 0⟩)) := accepted _ _ _ _ (by decide +kernel)

theorem nested_congruence_then_unfolding :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context,
        encodeWitness (.trans (.congruence 1 [unfoldIdentity (.term 0)]) (unfoldIdentity (.term 0)))]
      (encodeConversion (some ⟨identity (identity (.term 0)), .term 0, 0⟩)) := accepted _ _ _ _ (by decide +kernel)

theorem bound_congruence_keeps_the_bound_image :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness (.congruence 2 [.refl (.var 0)])]
      (encodeConversion (some ⟨.app (.term 2) (.var 0), .app (.term 2) (.var 0), 0⟩)) := accepted _ _ _ _ (by decide +kernel)

theorem same_index_does_not_join_variable_and_constant :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context,
        encodeWitness (.trans (.refl (.var 0)) (.refl (.term 0)))] (.sym "None") := refused _ (by decide +kernel)

theorem independently_valid_endpoint_does_not_repair_bad_child :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context,
        encodeWitness (.trans (.refl (.term 0)) (.refl (.term 99)))] (.sym "None") := refused _ (by decide +kernel)

theorem malformed_first_child_cannot_be_hidden_by_second :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context,
        encodeWitness (.trans (.refl (.term 99)) (.refl (.term 0)))] (.sym "None") := refused _ (by decide +kernel)

theorem reflexivity_requires_a_saturated_expression :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness (.refl (.term 1))]
      (.sym "None") := refused _ (by decide +kernel)

theorem unknown_congruence_symbol_refuses :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness (.congruence 99 [])]
      (.sym "None") := refused _ (by decide +kernel)

theorem missing_congruence_child_refuses :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness (.congruence 1 [])]
      (.sym "None") := refused _ (by decide +kernel)

theorem extra_congruence_child_refuses :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness (.congruence 0 [.refl (.term 0)])]
      (.sym "None") := refused _ (by decide +kernel)

theorem child_sort_must_fit_the_declared_binder :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness (.congruence 1 [.refl (.term 3)])]
      (.sym "None") := refused _ (by decide +kernel)

theorem regular_variable_is_not_a_bound_image :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness (.congruence 2 [.refl (.var 1)])]
      (.sym "None") := refused _ (by decide +kernel)

theorem left_endpoint_must_be_a_bound_image :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness (.congruence 2 [unfoldIdentity (.var 0)])]
      (.sym "None") := refused _ (by decide +kernel)

theorem right_endpoint_must_be_a_bound_image :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context,
        encodeWitness (.congruence 2 [.symm (unfoldIdentity (.var 0))])]
      (.sym "None") := refused _ (by decide +kernel)

theorem known_symbol_without_definition_refuses_unfolding :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness (.unfold 0 [] [])]
      (.sym "None") := refused _ (by decide +kernel)

theorem wrong_unfolding_argument_sort_refuses :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness (unfoldIdentity (.term 3))]
      (.sym "None") := refused _ (by decide +kernel)

theorem duplicated_dummy_image_refuses :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness (.unfold 5 [] [0, 0])]
      (.sym "None") := refused _ (by decide +kernel)

theorem untyped_stored_result_is_rejected :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions [(1, ⟨[], .term 3⟩)], encodeContext context, encodeWitness (unfoldIdentity (.term 0))]
      (.sym "None") := by
  have refused : ConvWitness.conversion? (signatureOf table) (definitionsOf [(1, ⟨[], .term 3⟩)])
      context (unfoldIdentity (.term 0)) = none := by decide +kernel
  simpa only [refused, encodeConversion] using
    conversion_computes table [(1, ⟨[], .term 3⟩)] context (unfoldIdentity (.term 0))

theorem changed_definition_changes_the_checked_endpoint :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions [(1, ⟨[], .term 0⟩)], encodeContext context, encodeWitness (unfoldIdentity (.var 0))]
      (encodeConversion (some ⟨identity (.var 0), .term 0, 0⟩)) := by
  have result : ConvWitness.conversion? (signatureOf table) (definitionsOf [(1, ⟨[], .term 0⟩)])
      context (unfoldIdentity (.var 0)) = some ⟨identity (.var 0), .term 0, 0⟩ := by decide +kernel
  simpa only [result] using conversion_computes table [(1, ⟨[], .term 0⟩)] context (unfoldIdentity (.var 0))

theorem stale_endpoint_is_not_accepted :
    ¬ Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions [(1, ⟨[], .term 0⟩)], encodeContext context, encodeWitness (unfoldIdentity (.var 0))]
      (encodeConversion (some ⟨identity (.var 0), .var 0, 0⟩)) := by
  intro wrong
  have impossible := encodeConversion_injective (wrong.deterministic changed_definition_changes_the_checked_endpoint)
  cases impossible

theorem wrong_sort_cannot_be_hidden_at_join (expression : Preterm) :
    Applies conversionProgram dataEqualityHost "mm0:conversion-join"
      [encode expression, encode expression, natural 0, encodeConversion (some ⟨expression, expression, 1⟩)] (.sym "None") := by
  simpa [encodeConversion] using join_computes expression expression 0 (some ⟨expression, expression, 1⟩)

theorem no_fuel_is_exhaustion (table : SignatureTable) (definitions : DefinitionTable)
    (context : Context) (witness : ConvWitness) :
    apply conversionProgram dataEqualityHost 0 "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness witness] = .exhausted := by
  cases witness <;> rw [encodeWitness, conversion_apply _ (by decide)] <;> rfl

theorem malformed_witness_tag_is_not_a_conversion_rule :
    apply conversionProgram dataEqualityHost 1 "mm0:conversion"
      [encodeTable [], encodeDefinitions [], encodeContext [], .list [.sym "MM0:AcceptAnything"]] = .failure := by
  rw [conversion_apply _ (by decide)]
  rfl

theorem duplicate_children_keep_both_argument_positions :
    Applies conversionProgram dataEqualityHost "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context,
        encodeWitness (.congruence 4 [.refl (.term 0), .refl (.term 0)])]
      (encodeConversion (some ⟨(Preterm.term 4).applyArgs [.term 0, .term 0], (Preterm.term 4).applyArgs [.term 0, .term 0], 0⟩)) :=
  accepted _ _ _ _ (by decide +kernel)

theorem direct_reflexivity_execution :
    apply conversionProgram dataEqualityHost 32 "mm0:conversion"
      [encodeTable [], encodeDefinitions [], encodeContext [.bound 0], encodeWitness (.refl (.var 0))] =
      .value (encodeConversion (some ⟨.var 0, .var 0, 0⟩)) := by
  let cached : Host := ⟨fun head arguments =>
    if head = "nik:nat-zero" then
      match arguments with
      | [.lit "0"] => .value (.sym "True")
      | _ => dataEqualityHost.primitive head arguments
    else dataEqualityHost.primitive head arguments⟩
  have identical : cached = dataEqualityHost := by
    apply congrArg Host.mk
    funext head arguments
    split
    · rename_i known
      subst head
      split
      · exact (naturalHost_zero 0).symm
      · rfl
    · rfl
  rw [← identical, encodeWitness]
  rfl

end Mettapedia.Languages.MM0.Presentation.ComputationalConversion.Controls
