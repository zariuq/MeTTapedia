import Mettapedia.Languages.VibeITP.Presentation.AdmissionCorrespondence

/-!
# Sequential declaration and resulting-theory controls

These checks use the fixed-initial authored entry. Definitions are checked
against the previous signature, fresh identities follow allocation order,
and proof positions refer to the actual resulting ordered theory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalAdmission.Controls

open ComputationalData ComputationalShift ComputationalDefinitions ComputationalProofs ComputationalLiterals
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => admissionProgram
local notation "H" => productDivisionHost

private def definitionFields (declaration : Spec.Definition) :=
  (declaration.symbol, declaration.fvars, declaration.value)

private theorem definitionFields_injective : Function.Injective definitionFields := by
  intro first second same
  cases first
  cases second
  cases same
  rfl

private instance definitionEquality : DecidableEq Spec.Definition := fun first second =>
  decidable_of_iff (definitionFields first = definitionFields second)
    ⟨fun same => definitionFields_injective same, congrArg definitionFields⟩

private def stateFields (state : AdmissionState) :=
  (state.phase, state.nextFresh, state.table, state.axioms, state.definitions)

private theorem stateFields_injective : Function.Injective stateFields := by
  intro first second same
  cases first
  cases second
  cases same
  rfl

private instance stateEquality : DecidableEq AdmissionState := fun first second =>
  decidable_of_iff (stateFields first = stateFields second)
    ⟨fun same => stateFields_injective same, congrArg stateFields⟩

private def a : Spec.Term := .lit [1]
private def b : Spec.Term := .lit [2]
private def F : Spec.SymId := .fresh 0
private def c : Spec.SymId := .fresh 1
private def parameterState : AdmissionState := initialAdmission.allocate (Spec.SymInfo.fvarOf 0)
private def definitionState : AdmissionState := parameterState.define [F] (.app F [])
private def defining : List Declaration := [.fvar 0, .definition [F] [0] (.app F [])]
private def definitionClaim : Spec.Term :=
  Spec.definitionStatement definitionState.theory.sig c [F] (.app F [])
private def orderedAxioms : List Declaration := [.axiom (Spec.Term.impl a b), .axiom a, .axiom b]
private def mp : ProofWitness := .modusPonens (.axiom 0) (.axiom 1)

private theorem starts (declarations : List Declaration) (after : AdmissionState)
    (computed : admitRun initialAdmission declarations = some after) :
    Applies P H "vibe:admission-start" [encodeDeclarations declarations]
      (encodeAdmissionResult (some after)) := by
  simpa only [computed] using admissionStart_computes declarations

private theorem stops (declarations : List Declaration)
    (computed : admitRun initialAdmission declarations = none) :
    Applies P H "vibe:admission-start" [encodeDeclarations declarations] (.sym "None") := by
  simpa only [computed, encodeAdmissionResult] using admissionStart_computes declarations

private theorem accepts (declarations : List Declaration) (witness : ProofWitness) (claimed : Spec.Term)
    (checked : checkStatic declarations witness claimed = true) :
    Applies P H "vibe:check-static" [encodeDeclarations declarations, encodeWitness witness, encode claimed]
      (.sym "True") := by
  have computed := checkStatic_computes declarations witness claimed
  rw [checked] at computed
  exact computed

private theorem refuses (declarations : List Declaration) (witness : ProofWitness) (claimed : Spec.Term)
    (checked : checkStatic declarations witness claimed = false) :
    Applies P H "vibe:check-static" [encodeDeclarations declarations, encodeWitness witness, encode claimed]
      (.sym "False") := by
  have computed := checkStatic_computes declarations witness claimed
  rw [checked] at computed
  exact computed

theorem empty_run_retains_initial_theory :
    Applies P H "vibe:admission-start" [encodeDeclarations []]
      (encodeAdmissionResult (some initialAdmission)) := starts _ _ rfl

theorem allocated_fvar_arity_has_no_added_cap (arity : Nat) :
    Applies P H "vibe:admission-start" [encodeDeclarations [.fvar arity]]
      (encodeAdmissionResult (some (initialAdmission.allocate (Spec.SymInfo.fvarOf arity)))) ∧
      signatureOf (initialAdmission.allocate (Spec.SymInfo.fvarOf arity)).table F =
        some (Spec.SymInfo.fvarOf arity) := by
  exact ⟨starts _ _ rfl, rfl⟩

theorem fresh_allocation_order_is_retained :
    Applies P H "vibe:admission-start" [encodeDeclarations [.fvar 0, .constant [1, 0]]]
      (encodeAdmissionResult (some (parameterState.allocate ⟨.constant, [1, 0]⟩))) ∧
      signatureOf (parameterState.allocate ⟨.constant, [1, 0]⟩).table F = some (Spec.SymInfo.fvarOf 0) ∧
      signatureOf (parameterState.allocate ⟨.constant, [1, 0]⟩).table c = some ⟨.constant, [1, 0]⟩ :=
  ⟨starts _ _ rfl, rfl, rfl⟩

theorem constant_binder_metadata_has_no_added_word_cap :
    Applies P H "vibe:admission-start" [encodeDeclarations [.constant [Spec.wordBound, 1]]]
      (encodeAdmissionResult (some (initialAdmission.allocate ⟨.constant, [Spec.wordBound, 1]⟩))) :=
  starts _ _ rfl

theorem builtins_are_not_overwritten :
    signatureOf (parameterState.allocate ⟨.constant, [1]⟩).table (.builtin .impl) = some Spec.Builtin.impl.info := rfl

theorem ordered_axiom_append_and_modus_ponens_accept :
    Applies P H "vibe:check-static" [encodeDeclarations orderedAxioms, encodeWitness mp, encode b]
      (.sym "True") := accepts _ _ _ (by decide +kernel)

theorem bad_premise_refuses_despite_admitted_conclusion :
    Applies P H "vibe:check-static"
      [encodeDeclarations orderedAxioms, encodeWitness (.modusPonens (.axiom 0) (.axiom 2)), encode b]
      (.sym "False") := refuses _ _ _ (by decide +kernel)

theorem declaration_order_changes_supplied_proof_acceptance :
    Applies P H "vibe:check-static"
      [encodeDeclarations [.axiom a, .axiom (Spec.Term.impl a b), .axiom b], encodeWitness mp, encode b]
      (.sym "False") := refuses _ _ _ (by decide +kernel)

theorem duplicate_axioms_retain_distinct_positions :
    Applies P H "vibe:check-static"
      [encodeDeclarations [.axiom a, .axiom a], encodeWitness (.axiom 1), encode a] (.sym "True") :=
  accepts _ _ _ (by decide +kernel)

theorem missing_position_is_not_rescued_by_duplicate_axioms :
    Applies P H "vibe:check-static"
      [encodeDeclarations [.axiom a, .axiom a], encodeWitness (.axiom 2), encode a] (.sym "False") :=
  refuses _ _ _ (by decide +kernel)

theorem early_forward_axiom_refuses :
    Applies P H "vibe:admission-start" [encodeDeclarations [.axiom (.app F []), .constant []]]
      (.sym "None") := stops _ (by decide +kernel)

theorem prior_constant_allows_the_same_axiom :
    Applies P H "vibe:check-static"
      [encodeDeclarations [.constant [], .axiom (.app F [])], encodeWitness (.axiom 0), encode (.app F [])]
      (.sym "True") := accepts _ _ _ (by decide +kernel)

theorem open_axiom_refuses :
    Applies P H "vibe:admission-start" [encodeDeclarations [.axiom (.bvar 0)]] (.sym "None") :=
  stops _ (by decide +kernel)

theorem declared_binder_closes_axiom :
    Applies P H "vibe:check-static"
      [encodeDeclarations [.constant [1], .axiom (.app F [.bvar 0])], encodeWitness (.axiom 0), encode (.app F [.bvar 0])]
      (.sym "True") := accepts _ _ _ (by decide +kernel)

theorem wrong_application_arity_refuses_admission :
    Applies P H "vibe:admission-start" [encodeDeclarations [.constant [0], .axiom (.app F [])]]
      (.sym "None") := stops _ (by decide +kernel)

theorem axiom_publication_after_proof_phase_refuses :
    Applies P H "vibe:admission-start" [encodeDeclarations [.enterProofs, .axiom a]] (.sym "None") :=
  stops _ (by decide +kernel)

theorem entering_proof_phase_twice_preserves_theory :
    Applies P H "vibe:admission-start" [encodeDeclarations [.enterProofs, .enterProofs]]
      (encodeAdmissionResult (some { initialAdmission with phase := .proofs })) := starts _ _ rfl

theorem definition_in_proof_phase_remains_permitted :
    Applies P H "vibe:admission-start" [encodeDeclarations [.enterProofs, .definition [] [] a]]
      (encodeAdmissionResult (some ({ initialAdmission with phase := .proofs }.define [] a))) :=
  starts _ _ (by decide +kernel)

theorem checked_definition_publishes_then_supports_its_proof :
    Applies P H "vibe:admission-start" [encodeDeclarations defining]
      (encodeAdmissionResult (some definitionState)) ∧
      Applies P H "vibe:check-static"
        [encodeDeclarations defining, encodeWitness (.definition 0 [0]), encode definitionClaim] (.sym "True") :=
  ⟨starts _ _ (by decide +kernel), accepts _ _ _ (by decide +kernel)⟩

theorem definition_signature_is_selected_by_allocation :
    signatureOf definitionState.table c = some ⟨.constant, [0]⟩ ∧
      definitionState.definitions = [⟨c, [F], .app F []⟩] := ⟨rfl, rfl⟩

theorem valid_surplus_hints_remain_permitted :
    Applies P H "vibe:admission-start" [encodeDeclarations [.fvar 0, .definition [F] [0, 0] (.app F [])]]
      (encodeAdmissionResult (some definitionState)) := starts _ _ (by decide +kernel)

theorem missing_definition_hint_refuses_before_publication :
    Applies P H "vibe:admission-start" [encodeDeclarations [.fvar 0, .definition [F] [] (.app F [])]]
      (.sym "None") := stops _ (by decide +kernel)

theorem out_of_range_surplus_hint_refuses :
    Applies P H "vibe:admission-start" [encodeDeclarations [.fvar 0, .definition [F] [0, 1] (.app F [])]]
      (.sym "None") := stops _ (by decide +kernel)

theorem self_reference_cannot_use_early_definition_publication :
    Applies P H "vibe:admission-start" [encodeDeclarations [.definition [] [] (.app F [])]]
      (.sym "None") := stops _ (by decide +kernel)

theorem forward_reference_cannot_use_a_later_constant :
    Applies P H "vibe:admission-start"
      [encodeDeclarations [.fvar 0, .definition [F] [0] (.app c []), .constant []]]
      (.sym "None") := stops _ (by decide +kernel)

theorem unknown_unused_parameter_refuses :
    Applies P H "vibe:admission-start" [encodeDeclarations [.definition [F] [] a]] (.sym "None") :=
  stops _ (by decide +kernel)

theorem constant_parameter_cannot_replace_fvar_admission :
    Applies P H "vibe:admission-start" [encodeDeclarations [.constant [], .definition [F] [] a]]
      (.sym "None") := stops _ (by decide +kernel)

theorem open_definition_body_refuses :
    Applies P H "vibe:admission-start" [encodeDeclarations [.definition [] [] (.bvar 0)]] (.sym "None") :=
  stops _ (by decide +kernel)

theorem prior_axiom_remains_usable_after_allocation_and_definition :
    Applies P H "vibe:check-static"
      [encodeDeclarations [.axiom a, .fvar 0, .definition [F] [0] (.app F [])], encodeWitness (.axiom 0), encode a]
      (.sym "True") := accepts _ _ _ (by decide +kernel)

theorem changed_definition_body_refuses_previous_claim :
    Applies P H "vibe:check-static"
      [encodeDeclarations [.fvar 0, .definition [F] [] b], encodeWitness (.definition 0 []), encode definitionClaim]
      (.sym "False") := refuses _ _ _ (by decide +kernel)

theorem failed_declaration_cannot_be_rescued_by_independent_derivability :
    Spec.Derives initialAdmission.theory (Spec.litIsNatStatement 1) ∧
      Applies P H "vibe:check-static"
        [encodeDeclarations [.axiom (.bvar 0)], encodeWitness (.literal (.isNat 1)), encode (Spec.litIsNatStatement 1)]
        (.sym "False") := by
  exact ⟨.litIsNat (by decide +kernel), refuses _ _ _ (by decide +kernel)⟩

theorem caller_selected_identity_declaration_is_refused :
    Applies P H "vibe:admit"
      [encodeState initialAdmission, .list [.sym "Declare:Constant", encodeSymbol F, encodeBinders []]] (.sym "None") := by
  refine admission_equation (equation := admissionEquations[21])
    (environment := [("state", encodeState initialAdmission),
      ("unknown", .list [.sym "Declare:Constant", encodeSymbol F, encodeBinders []])])
    (by decide +kernel) (by rfl) (by rfl) ?_
  exact .symbol _ _ _ _

theorem allocation_cannot_return_the_unextended_state :
    ¬ Applies P H "vibe:admission-start" [encodeDeclarations [.fvar 0]]
      (encodeAdmissionResult (some initialAdmission)) := by
  intro run
  have states := encodeAdmissionResult_injective
    (run.deterministic (admissionStart_computes [.fvar 0]))
  have identities := congrArg (Option.map AdmissionState.nextFresh) states
  simp [admitRun, admit, initialAdmission, AdmissionState.allocate] at identities

theorem successful_declarations_do_not_authorize_a_wrong_claim :
    Applies P H "vibe:check-static"
      [encodeDeclarations [.axiom a], encodeWitness (.axiom 0), encode b] (.sym "False") :=
  refuses _ _ _ (by decide +kernel)

theorem exhausted_execution_is_not_completed_refusal :
    apply P H 0 "vibe:check-static" [encodeDeclarations [], encodeWitness (.literal (.isNat 1)),
      encode (Spec.litIsNatStatement 1)] = .exhausted ∧
      Applies P H "vibe:check-static" [encodeDeclarations [], encodeWitness (.literal (.isNat 1)),
        encode (Spec.litIsNatStatement 1)] (.sym "True") :=
  by
    constructor
    · rw [admission_apply _ (by decide +kernel)]
      rfl
    · exact accepts _ _ _ (by decide +kernel)

end Mettapedia.Languages.VibeITP.Presentation.ComputationalAdmission.Controls
