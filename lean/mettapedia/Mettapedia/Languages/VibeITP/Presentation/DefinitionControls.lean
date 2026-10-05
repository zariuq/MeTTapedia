import Mettapedia.Languages.VibeITP.Presentation.DefinitionSignature

/-!
# Definition operand, traversal and claimed-result controls

Occurrence consumption is fused with the authored traversal. The examples
retain preorder, repeated children and unused hints. Parameter admission,
body formation and exact claimed-result checking remain separate checks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalDefinitions.Controls

open ComputationalData ComputationalShift ComputationalSubstitution ComputationalInference
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => definitionProgram
local notation "H" => productDivisionHost

private def F : Spec.SymId := .fresh 13
private def G : Spec.SymId := .fresh 14
private def pair : Spec.SymId := .fresh 15
private def binder : Spec.SymId := .fresh 16
private def constant : Spec.SymId := .fresh 17
private def unary : Spec.SymId := .fresh 18
private def unknown : Spec.SymId := .fresh 99
private def alpha : Spec.Term := .lit [1, 2]
private def table : SignatureTable :=
  [(F, Spec.SymInfo.fvarOf 0), (G, Spec.SymInfo.fvarOf 0),
    (pair, ⟨.constant, [0, 0]⟩), (binder, ⟨.constant, [1]⟩),
    (unary, Spec.SymInfo.fvarOf 1)]

private def request (parameters : List Spec.SymId) (hints : List Nat) (body : Spec.Term) : DefinitionRequest :=
  ⟨constant, parameters, hints, body⟩

private def queryArguments (submitted : DefinitionRequest) : List Term :=
  [encodeTable table, encodeSymbol submitted.constant, encodeSymbols submitted.parameters,
    encodeBinders submitted.hints, encode submitted.body]

private def statement (submitted : DefinitionRequest) : Spec.Term :=
  Spec.definitionStatement (signatureOf table) submitted.constant submitted.parameters submitted.body

theorem zero_parameter_literal_definition_accepts :
    Applies P H "vibe:definition-query" (queryArguments (request [] [] alpha))
      (encodeResult (some (statement (request [] [] alpha)))) :=
  definitionQuery_computes table _

theorem supplied_constant_does_not_need_a_previous_declaration :
    signatureOf table constant = none ∧
      Applies P H "vibe:check-definition"
        (queryArguments (request [] [] alpha) ++ [encode (statement (request [] [] alpha))]) (.sym "True") :=
  ⟨rfl, checkDefinition_computes table _ _⟩

theorem all_ordered_children_consume_hints :
    Applies P H "vibe:def-consume" [encodeTable table, encodeSymbols [F, G], encodeBinders [0, 1],
      encode (.app pair [.app F [], .app G []])] (encodeNatResult (some [])) :=
  consume_computes table _ _ _

theorem parent_occurrence_precedes_its_children :
    Applies P H "vibe:def-consume" [encodeTable table, encodeSymbols [unary, F], encodeBinders [0, 1],
      encode (.app unary [.app F []])] (encodeNatResult (some [])) :=
  consume_computes table _ _ _

theorem reversed_parent_child_hints_refuse :
    Applies P H "vibe:def-consume" [encodeTable table, encodeSymbols [unary, F], encodeBinders [1, 0],
      encode (.app unary [.app F []])] (.sym "None") :=
  consume_computes table _ _ _

theorem repeated_occurrences_require_repeated_hints :
    Applies P H "vibe:def-consume" [encodeTable table, encodeSymbols [F], encodeBinders [0, 0],
      encode (.app pair [.app F [], .app F []])] (encodeNatResult (some [])) :=
  consume_computes table _ _ _

theorem repeated_occurrence_missing_hint_refuses :
    Applies P H "vibe:definition-query"
      (queryArguments (request [F] [0] (.app pair [.app F [], .app F []]))) (.sym "None") :=
  definitionQuery_computes table _

theorem ordered_definition_accepts :
    Applies P H "vibe:check-definition"
      (queryArguments (request [F, G] [0, 1] (.app pair [.app F [], .app G []])) ++
        [encode (statement (request [F, G] [0, 1] (.app pair [.app F [], .app G []])))]) (.sym "True") :=
  checkDefinition_computes table _ _

theorem reversed_child_hints_refuse :
    Applies P H "vibe:definition-query"
      (queryArguments (request [F, G] [1, 0] (.app pair [.app F [], .app G []]))) (.sym "None") :=
  definitionQuery_computes table _

theorem wrong_parameter_hint_refuses :
    Applies P H "vibe:definition-query"
      (queryArguments (request [F, G] [1] (.app F []))) (.sym "None") :=
  definitionQuery_computes table _

theorem unused_valid_hint_suffix_accepts :
    Applies P H "vibe:definition-query" (queryArguments (request [F] [0, 0, 0] (.app F [])))
      (encodeResult (some (statement (request [F] [0, 0, 0] (.app F []))))) :=
  definitionQuery_computes table _

theorem fused_traversal_returns_unused_hint_suffix :
    Applies P H "vibe:def-consume" [encodeTable table, encodeSymbols [F], encodeBinders [0, 0, 0],
      encode (.app F [])] (encodeNatResult (some [0, 0])) :=
  consume_computes table _ _ _

theorem unused_out_of_range_hint_still_refuses :
    Applies P H "vibe:def-consume" [encodeTable table, encodeSymbols [F], encodeBinders [0, 1],
      encode (.app F [])] (encodeNatResult (some [1])) ∧
      Applies P H "vibe:definition-query" (queryArguments (request [F] [0, 1] (.app F []))) (.sym "None") :=
  ⟨consume_computes table _ _ _, definitionQuery_computes table _⟩

theorem zero_parameters_cannot_authorize_a_surplus_hint :
    Applies P H "vibe:definition-query" (queryArguments (request [] [0] alpha)) (.sym "None") :=
  definitionQuery_computes table _

theorem repeated_parameters_remain_permitted :
    Applies P H "vibe:check-definition"
      (queryArguments (request [F, F] [1] (.app F [])) ++
        [encode (statement (request [F, F] [1] (.app F [])))]) (.sym "True") :=
  checkDefinition_computes table _ _

theorem repeated_parameters_retain_both_binders :
    Applies P H "vibe:def-info" [encodeTable table, encodeSymbols [F, F]]
      (encodeInfoResult (some ⟨.constant, [0, 0]⟩)) :=
  definitionInfo_computes table _

theorem unused_parameters_remain_in_constant_information :
    Applies P H "vibe:def-info" [encodeTable table, encodeSymbols [F, unary]]
      (encodeInfoResult (some ⟨.constant, [0, 1]⟩)) :=
  definitionInfo_computes table _

theorem unknown_unused_parameter_refuses :
    Applies P H "vibe:definition-query" (queryArguments (request [unknown] [] alpha)) (.sym "None") :=
  definitionQuery_computes table _

theorem constant_parameter_refuses :
    Applies P H "vibe:definition-query" (queryArguments (request [pair] [] alpha)) (.sym "None") :=
  definitionQuery_computes table _

theorem parameter_index_at_length_is_missing :
    Applies P H "vibe:def-at" [encodeSymbols [F, G], natural 2] (.sym "None") :=
  parameterAt_computes _ _

theorem open_body_refuses :
    Applies P H "vibe:definition-query" (queryArguments (request [] [] (.bvar 0))) (.sym "None") :=
  definitionQuery_computes table _

theorem declared_binder_can_close_the_body :
    Applies P H "vibe:definition-query" (queryArguments (request [] [] (.app binder [.bvar 0])))
      (encodeResult (some (statement (request [] [] (.app binder [.bvar 0]))))) :=
  definitionQuery_computes table _

theorem unknown_body_head_refuses :
    Applies P H "vibe:definition-query" (queryArguments (request [] [] (.app unknown []))) (.sym "None") :=
  definitionQuery_computes table _

theorem wrong_body_arity_refuses :
    Applies P H "vibe:definition-query" (queryArguments (request [unary] [0] (.app unary []))) (.sym "None") :=
  definitionQuery_computes table _

theorem malformed_later_child_refuses :
    Applies P H "vibe:definition-query"
      (queryArguments (request [F] [0] (.app pair [.app F [], .app unknown []]))) (.sym "None") :=
  definitionQuery_computes table _

theorem oversized_literal_body_refuses (bytes : List UInt8) (large : Spec.wordBound ≤ bytes.length + 8) :
    Applies P H "vibe:definition-query" (queryArguments (request [] [] (.lit bytes))) (.sym "None") := by
  apply (definitionQuery_refuses_iff table _).mpr
  simp only [DefinitionRequest.result, request, Spec.WellFormed, Bool.and_eq_true]
  have outside : ¬ bytes.length + 8 < Spec.wordBound := Nat.not_lt.mpr large
  simp [outside]

theorem eta_arguments_are_descending :
    Applies P H "vibe:def-desc" [natural 3] (.list (encodeTerms [.bvar 2, .bvar 1, .bvar 0])) :=
  descending_computes 3

theorem nullary_eta_has_no_arguments :
    Applies P H "vibe:def-etas" [encodeSymbols [F], encodeBinders [0]]
      (.list (encodeTerms [.app F []])) :=
  etaTerms_computes (signatureOf table) [F]

/-- An unused declared parameter retains its arbitrary natural arity. The
constructed statement is not subjected to an extra machine-word guard. -/
theorem declared_parameter_arities_have_no_added_cap (arity : Nat) :
    let signature : Spec.Sig := fun symbol => if symbol = F then some (Spec.SymInfo.fvarOf arity) else none
    let submitted := request [F] [] alpha
    Applies P H "vibe:definition-query"
      [encodeTable (definitionSnapshot signature submitted), encodeSymbol constant,
        encodeSymbols [F], encodeBinders [], encode alpha]
      (encodeResult (some (Spec.definitionStatement signature constant [F] alpha))) := by
  dsimp only
  have computation := definitionQuery_computes_for_signature
    (fun symbol => if symbol = F then some (Spec.SymInfo.fvarOf arity) else none) (request [F] [] alpha)
  have authorized : (request [F] [] alpha).result
      (fun symbol => if symbol = F then some (Spec.SymInfo.fvarOf arity) else none) =
      some (Spec.definitionStatement
        (fun symbol => if symbol = F then some (Spec.SymInfo.fvarOf arity) else none) constant [F] alpha) := by
    rfl
  rw [authorized] at computation
  exact computation

theorem wrong_claimed_constant_is_refused :
    Applies P H "vibe:check-definition" (queryArguments (request [] [] alpha) ++
      [encode (Spec.definitionStatement (signatureOf table) unknown [] alpha)]) (.sym "False") :=
  checkDefinition_computes table _ _

theorem swapped_equation_sides_are_refused :
    Applies P H "vibe:check-definition" (queryArguments (request [] [] alpha) ++
      [encode (Spec.Term.eq alpha (.app constant []))]) (.sym "False") :=
  checkDefinition_computes table _ _

theorem changed_literal_byte_order_is_refused :
    Applies P H "vibe:check-definition" (queryArguments (request [] [] alpha) ++
      [encode (Spec.definitionStatement (signatureOf table) constant [] (.lit [2, 1]))]) (.sym "False") :=
  checkDefinition_computes table _ _

theorem valid_admitted_definition_produces_independent_derivation :
    Spec.Derives
      (⟨Spec.sigOf (fun identity => if identity = 17 then some ⟨.constant, []⟩
          else signatureOf table (.fresh identity)), [], [(request [] [] alpha).declaration]⟩ : Spec.Theory)
      (Spec.definitionStatement (Spec.sigOf (fun identity => if identity = 17 then some ⟨.constant, []⟩
          else signatureOf table (.fresh identity))) constant [] alpha) := by
  apply checkDefinition_derived _ (request [] [] alpha)
  · simp
  · apply (checkDefinition_for_signature_iff _ _ _).mpr
    rfl

theorem globally_derivable_claim_does_not_validate_missing_hints (theory : Spec.Theory)
    (asserted : statement (request [F] [] (.app F [])) ∈ theory.axioms) :
    Spec.Derives theory (statement (request [F] [] (.app F []))) ∧
      Applies P H "vibe:check-definition"
        (queryArguments (request [F] [] (.app F [])) ++
          [encode (statement (request [F] [] (.app F [])))]) (.sym "False") :=
  ⟨.axiom asserted, checkDefinition_computes table _ _⟩

theorem no_extra_completed_definition (submitted : DefinitionRequest) (claimed : Spec.Term)
    (wrong : submitted.result (signatureOf table) ≠ some claimed) :
    ¬ Applies P H "vibe:definition-query" (queryArguments submitted) (encodeResult (some claimed)) := by
  intro invented
  exact wrong ((definitionQuery_accepts_iff table submitted claimed).mp invented)

theorem no_extra_check_boolean (submitted : DefinitionRequest) (claimed : Spec.Term) :
    ¬ Applies P H "vibe:check-definition" (queryArguments submitted ++ [encode claimed]) (.sym "invented") := by
  change ¬ Applies P H "vibe:check-definition"
    [encodeTable table, encodeSymbol submitted.constant, encodeSymbols submitted.parameters,
      encodeBinders submitted.hints, encode submitted.body, encode claimed] (.sym "invented")
  rw [checkDefinition_result_exact]
  cases decide (submitted.result (signatureOf table) = some claimed) <;> simp [boolean]

theorem exhausted_valid_definition_is_not_refusal :
    apply P H 0 "vibe:check-definition"
      (queryArguments (request [] [] alpha) ++ [encode (statement (request [] [] alpha))]) = .exhausted ∧
      Applies P H "vibe:check-definition"
        (queryArguments (request [] [] alpha) ++ [encode (statement (request [] [] alpha))]) (.sym "True") := by
  constructor
  · rw [definition_apply _ (by decide +kernel)]
    rfl
  · exact checkDefinition_computes table _ _

end Mettapedia.Languages.VibeITP.Presentation.ComputationalDefinitions.Controls
