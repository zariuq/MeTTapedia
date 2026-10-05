import Mettapedia.Languages.VibeITP.Presentation.ProofCorrespondence

/-!
# Whole submitted-proof controls

The controls check actual theory positions, ordered recursive children and all
static leaf families. Unrelated derivability cannot repair a malformed supplied
witness. Completed refusal and finite execution exhaustion remain distinct.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalProofs.Controls

open ComputationalData ComputationalShift ComputationalDefinitions ComputationalLiterals
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => proofProgram
local notation "H" => productDivisionHost

private def a : Spec.Term := .lit [1]
private def b : Spec.Term := .lit [2]
private def wrong : Spec.Term := .lit [3]
private def F : Spec.SymId := .fresh 0
private def c : Spec.SymId := .fresh 1
private def table : SignatureTable :=
  Spec.Builtin.all.map (fun builtin => (.builtin builtin, builtin.info)) ++
    [(F, ⟨.fvar, []⟩), (c, ⟨.constant, [0]⟩)]
private def axioms : List Spec.Term := [Spec.Term.impl a b, a, b, wrong]
private def declarations : List Spec.Definition := [⟨c, [F], .app F []⟩]
private def definitionStatement : Spec.Term :=
  Spec.definitionStatement (signatureOf table) c [F] (.app F [])
private def mp : ProofWitness := .modusPonens (.axiom 0) (.axiom 1)

private theorem accepts (signature : SignatureTable) (assumptions : List Spec.Term) (definitions : List Spec.Definition)
    (witness : ProofWitness) (claimed : Spec.Term)
    (accepted : witness.result (theoryOf signature assumptions definitions) = some claimed) :
    Applies P H "vibe:check-proof"
      [encodeTable signature, encodeAxioms assumptions, encodeDefinitions definitions, encodeWitness witness, encode claimed]
      (.sym "True") :=
  (checkProof_accepts_iff _ _ _ _ _).mpr (ProofWitness.result_sound accepted)

private theorem refuses (signature : SignatureTable) (assumptions : List Spec.Term) (definitions : List Spec.Definition)
    (witness : ProofWitness) (claimed : Spec.Term)
    (refused : witness.result (theoryOf signature assumptions definitions) = none) :
    Applies P H "vibe:check-proof"
      [encodeTable signature, encodeAxioms assumptions, encodeDefinitions definitions, encodeWitness witness, encode claimed]
      (.sym "False") := by
  apply (checkProof_refuses_iff _ _ _ _ _).mpr
  intro checked
  have impossible := checked.eval
  rw [refused] at impossible
  cases impossible

theorem actual_axiom_position_accepts :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations, encodeWitness (.axiom 1), encode a]
      (.sym "True") := accepts _ _ _ _ _ rfl

theorem later_axiom_cannot_replace_selected_position :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations, encodeWitness (.axiom 1), encode b]
      (.sym "False") := by
  apply (checkProof_refuses_iff _ _ _ _ _).mpr
  intro checked
  have impossible := checked.eval
  simp [ProofWitness.result, axioms, a, b, theoryOf] at impossible

theorem ordered_modus_ponens_accepts :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations, encodeWitness mp, encode b]
      (.sym "True") := accepts _ _ _ _ _ rfl

theorem bad_premise_refuses_despite_admitted_conclusion :
    Spec.Derives (theoryOf table axioms declarations) b ∧
      Applies P H "vibe:check-proof"
        [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations,
          encodeWitness (.modusPonens (.axiom 0) (.axiom 3)), encode b] (.sym "False") := by
  constructor
  · exact .axiom (by simp [theoryOf, axioms])
  · exact refuses _ _ _ _ _ rfl

theorem reversed_premises_refuse :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations,
        encodeWitness (.modusPonens (.axiom 1) (.axiom 0)), encode b] (.sym "False") :=
  refuses _ _ _ _ _ rfl

theorem missing_child_refuses :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations,
        encodeWitness (.modusPonens (.axiom 0) (.axiom 99)), encode b] (.sym "False") :=
  refuses _ _ _ _ _ rfl

theorem changed_theory_positions_refuse_old_witness :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms [a, Spec.Term.impl a b, b], encodeDefinitions declarations,
        encodeWitness mp, encode b] (.sym "False") := refuses _ _ _ _ _ rfl

theorem removed_axiom_is_not_recovered_from_other_derivability :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms [b], encodeDefinitions declarations,
        encodeWitness (.axiom 2), encode b] (.sym "False") := refuses _ _ _ _ _ rfl

theorem duplicate_axioms_retain_their_positions :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms [a, a], encodeDefinitions [], encodeWitness (.axiom 1), encode a]
      (.sym "True") := accepts _ _ _ _ _ rfl

theorem huge_axiom_index_does_not_wrap :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms [a], encodeDefinitions [],
        encodeWitness (.axiom 18446744073709551616), encode a] (.sym "False") :=
  refuses _ _ _ _ _ rfl

theorem actual_definition_payload_and_hints_accept :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations,
        encodeWitness (.definition 0 [0]), encode definitionStatement] (.sym "True") :=
  accepts _ _ _ _ _ rfl

theorem missing_definition_hints_cannot_use_an_axiom_for_same_goal :
    Spec.Derives (theoryOf table [definitionStatement] declarations) definitionStatement ∧
      Applies P H "vibe:check-proof"
        [encodeTable table, encodeAxioms [definitionStatement], encodeDefinitions declarations,
          encodeWitness (.definition 0 []), encode definitionStatement] (.sym "False") := by
  constructor
  · exact .axiom (by simp [theoryOf])
  · exact refuses _ _ _ _ _ rfl

theorem invalid_surplus_definition_hint_refuses :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations,
        encodeWitness (.definition 0 [0, 1]), encode definitionStatement] (.sym "False") :=
  refuses _ _ _ _ _ rfl

theorem missing_definition_position_refuses :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations,
        encodeWitness (.definition 1 [0]), encode definitionStatement] (.sym "False") :=
  refuses _ _ _ _ _ rfl

theorem changed_definition_body_rejects_previous_statement :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions [⟨c, [F], .lit [8]⟩],
        encodeWitness (.definition 0 []), encode definitionStatement] (.sym "False") := by
  apply (checkProof_refuses_iff _ _ _ _ _).mpr
  intro checked
  have actual : ProofWitness.result (theoryOf table axioms [⟨c, [F], .lit [8]⟩]) (.definition 0 []) =
      some (Spec.definitionStatement (signatureOf table) c [F] (.lit [8])) := rfl
  have impossible := Option.some.inj (actual.symm.trans checked.eval)
  simp [definitionStatement, Spec.definitionStatement, Spec.Term.eq] at impossible

theorem nested_instantiation_and_modus_ponens_accept :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms [Spec.Term.impl (.app F []) b, .app F []], encodeDefinitions declarations,
        encodeWitness (.modusPonens (.instantiate F a (.axiom 0)) (.instantiate F a (.axiom 1))), encode b]
      (.sym "True") := accepts _ _ _ _ _ rfl

theorem changed_signature_refuses_previous_instantiation :
    Applies P H "vibe:check-proof"
      [encodeTable [], encodeAxioms [.app F []], encodeDefinitions [],
        encodeWitness (.instantiate F a (.axiom 0)), encode a] (.sym "False") :=
  refuses _ _ _ _ _ rfl

theorem malformed_instantiation_value_refuses :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms [.app F []], encodeDefinitions [],
        encodeWitness (.instantiate F (.bvar Spec.wordBound) (.axiom 0)), encode a] (.sym "False") :=
  refuses _ _ _ _ _ rfl

private theorem literal_accepts (request : LiteralRequest) (statement : Spec.Term)
    (authorized : request.result = some statement) :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations,
        encodeWitness (.literal request), encode statement] (.sym "True") := accepts _ _ _ _ _ authorized

theorem whole_isnat_leaf_accepts :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations,
        encodeWitness (.literal (.isNat 256)), encode (Spec.litIsNatStatement 256)] (.sym "True") :=
  literal_accepts _ _ rfl

theorem whole_less_than_leaf_accepts :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations,
        encodeWitness (.literal (.lessThan 3 4)), encode (Spec.litLtStatement 3 4)] (.sym "True") :=
  literal_accepts _ _ rfl

theorem whole_wrapped_addition_leaf_accepts :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations,
        encodeWitness (.literal (.addition (Spec.wordBound - 1) 1)),
        encode (Spec.litAddStatement (Spec.wordBound - 1) 1)] (.sym "True") := literal_accepts _ _ rfl

theorem whole_wrapped_multiplication_leaf_accepts :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations,
        encodeWitness (.literal (.multiplication (Spec.wordBound - 1) 2)),
        encode (Spec.litMulStatement (Spec.wordBound - 1) 2)] (.sym "True") := literal_accepts _ _ rfl

theorem whole_nonzero_division_leaf_accepts :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations,
        encodeWitness (.literal (.division 7 2)), encode (Spec.litDivStatement 7 2)] (.sym "True") :=
  literal_accepts _ _ rfl

theorem whole_literal_length_leaf_accepts :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations,
        encodeWitness (.literal (.length (.lit [4, 9]))), encode (Spec.litLengthStatement [4, 9])]
      (.sym "True") := literal_accepts _ _ rfl

theorem whole_ordered_byte_leaf_accepts :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations,
        encodeWitness (.literal (.get (.lit [4, 9]) 1)), encode (Spec.litGetStatement [4, 9] 1)] (.sym "True") :=
  literal_accepts _ _ rfl

theorem zero_divisor_witness_refuses_even_when_claim_is_an_axiom :
    Spec.Derives (theoryOf table [Spec.litDivStatement 7 0] []) (Spec.litDivStatement 7 0) ∧
      Applies P H "vibe:check-proof"
        [encodeTable table, encodeAxioms [Spec.litDivStatement 7 0], encodeDefinitions [],
          encodeWitness (.literal (.division 7 0)), encode (Spec.litDivStatement 7 0)] (.sym "False") := by
  constructor
  · exact .axiom (by simp [theoryOf])
  · exact refuses _ _ _ _ _ rfl

theorem literal_at_word_bound_refuses :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations,
        encodeWitness (.literal (.isNat Spec.wordBound)), encode (Spec.litIsNatStatement Spec.wordBound)]
      (.sym "False") := refuses _ _ _ _ _ rfl

theorem byte_at_length_refuses :
    Applies P H "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations,
        encodeWitness (.literal (.get (.lit [4, 9]) 2)), encode (Spec.litGetStatement [4, 9] 2)] (.sym "False") :=
  refuses _ _ _ _ _ rfl

theorem foreign_proof_tag_has_no_static_output :
    apply P H 1 "vibe:proof-query"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations, .list [.sym "MM0:Proof"]] =
      .value (.sym "None") := by
  rw [proof_apply _ (by decide +kernel)]
  rfl

theorem no_extra_whole_proof_answer :
    ¬ Applies P H "vibe:proof-query"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations, encodeWitness mp]
      (encodeResult (some wrong)) := by
  intro run
  have impossible := (proofQuery_accepts_iff _ _ _ _ _).mp run
  have computed := impossible.eval
  simp [ProofWitness.result, mp, axioms, theoryOf, modusPonensResult, Spec.Term.impl, a, b, wrong] at computed

theorem finite_valid_proof_can_exhaust :
    apply P H 0 "vibe:check-proof"
      [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations, encodeWitness mp, encode b] = .exhausted ∧
      Applies P H "vibe:check-proof"
        [encodeTable table, encodeAxioms axioms, encodeDefinitions declarations, encodeWitness mp, encode b] (.sym "True") := by
  constructor
  · rw [proof_apply _ (by decide +kernel)]
    rfl
  · exact ordered_modus_ponens_accepts

end Mettapedia.Languages.VibeITP.Presentation.ComputationalProofs.Controls
