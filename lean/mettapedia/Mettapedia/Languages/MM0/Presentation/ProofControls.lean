import Mettapedia.Languages.MM0.Presentation.ProofTheory

/-! # Positive and adversarial controls for complete supplied MM0 checking -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalProof.Controls

open Kernel ComputationalContext ComputationalTyping ComputationalArguments ComputationalDefinitions
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => proofProgram
local notation "H" => dataEqualityHost

private def implies (left right : Preterm) : Preterm := (Preterm.term 0).applyArgs [left, right]
private def mpDeclaration : TheoremDecl :=
  ⟨[.regular 1 ∅, .regular 1 ∅], [.var 0, implies (.var 0) (.var 1)], .var 1⟩
private def theory : Theory :=
  { sorts := [(0, {}), (1, { provable := true })]
    terms := [(0, ⟨[.regular 1 ∅, .regular 1 ∅], 1, ∅⟩),
      (1, ⟨[.regular 1 ∅], 1, ∅⟩), (2, ⟨[], 1, ∅⟩), (3, ⟨[], 1, ∅⟩),
      (4, ⟨[.bound 0], 1, {0}⟩), (5, ⟨[], 0, ∅⟩)]
    definitions := [(1, ⟨[], .var 0⟩)]
    theorems := [(0, mpDeclaration), (1, ⟨[], [], .term 2⟩),
      (2, ⟨[.bound 0, .regular 1 ∅], [], .term 2⟩),
      (3, ⟨[.bound 0, .bound 0], [], .term 2⟩),
      (4, ⟨[.regular 1 ∅], [.var 0, .var 0], .var 0⟩),
      (5, ⟨[], [], .var 0⟩), (6, ⟨[], [.var 0], .term 2⟩)] }
private def context : Context :=
  [.regular 1 ∅, .regular 1 ∅, .bound 0, .regular 1 {2}, .bound 0]
private def hypotheses : List Preterm := [.var 0, implies (.var 0) (.var 1)]
private def mp : ProofWitness := .theoremApp 0 [.var 0, .var 1] [.hyp 0, .hyp 1]
private def inputs (current : Theory) (locals : List Preterm) (witness : ProofWitness) (claim : Preterm) : List Term :=
  [encodeTable current.terms, encodeDefinitions current.definitions, encodeTheorems current.theorems,
    encodeContext context, encodeExpressions locals, encodeProof witness, encode claim]

private theorem accepts (current : Theory) (locals : List Preterm) (witness : ProofWitness) (claim : Preterm)
    (checked : ProofWitness.check current.termSignature current.definitionSignature current.theoremSignature
      context locals witness claim = true) :
    Applies P H "mm0:check-proof" (inputs current locals witness claim) (.sym "True") :=
  (theory_check_accepts_iff current context locals witness claim).mpr
    ((ProofWitness.check_iff _ _ _ _ _ _ _).mp checked)

private theorem refuses (current : Theory) (locals : List Preterm) (witness : ProofWitness) (claim : Preterm)
    (checked : ProofWitness.check (signatureOf current.terms) (definitionsOf current.definitions)
      (theoremsOf current.theorems) context locals witness claim = false) :
    Applies P H "mm0:check-proof" (inputs current locals witness claim) (.sym "False") := by
  apply (check_refuses_iff current.terms current.definitions current.theorems context locals witness claim).mpr
  rw [← ProofWitness.check_iff, checked]
  decide

theorem local_hypothesis :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.hyp 0) (.var 0)) (.sym "True") :=
  accepts theory hypotheses (.hyp 0) (.var 0) (by decide +kernel)

theorem wrong_local_claim :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.hyp 0) (.var 1)) (.sym "False") :=
  refuses theory hypotheses (.hyp 0) (.var 1) (by decide +kernel)

theorem missing_local_hypothesis :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.hyp 2) (.var 0)) (.sym "False") :=
  refuses theory hypotheses (.hyp 2) (.var 0) (by decide +kernel)

theorem modus_ponens :
    Applies P H "mm0:check-proof" (inputs theory hypotheses mp (.var 1)) (.sym "True") :=
  accepts theory hypotheses mp (.var 1) (by decide +kernel)

theorem wrong_modus_ponens_claim :
    Applies P H "mm0:check-proof" (inputs theory hypotheses mp (.var 0)) (.sym "False") :=
  refuses theory hypotheses mp (.var 0) (by decide +kernel)

theorem missing_premise :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.theoremApp 0 [.var 0, .var 1] [.hyp 1]) (.var 1)) (.sym "False") :=
  refuses theory hypotheses (.theoremApp 0 [.var 0, .var 1] [.hyp 1]) (.var 1) (by decide +kernel)

theorem extra_premise :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.theoremApp 0 [.var 0, .var 1] [.hyp 0, .hyp 1, .hyp 0]) (.var 1)) (.sym "False") :=
  refuses theory hypotheses (.theoremApp 0 [.var 0, .var 1] [.hyp 0, .hyp 1, .hyp 0]) (.var 1) (by decide +kernel)

theorem reversed_premises :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.theoremApp 0 [.var 0, .var 1] [.hyp 1, .hyp 0]) (.var 1)) (.sym "False") :=
  refuses theory hypotheses (.theoremApp 0 [.var 0, .var 1] [.hyp 1, .hyp 0]) (.var 1) (by decide +kernel)

theorem wrong_substitution_order :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.theoremApp 0 [.var 1, .var 0] [.hyp 0, .hyp 1]) (.var 0)) (.sym "False") :=
  refuses theory hypotheses (.theoremApp 0 [.var 1, .var 0] [.hyp 0, .hyp 1]) (.var 0) (by decide +kernel)

theorem missing_argument :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.theoremApp 0 [.var 0] [.hyp 0, .hyp 1]) (.var 1)) (.sym "False") :=
  refuses theory hypotheses (.theoremApp 0 [.var 0] [.hyp 0, .hyp 1]) (.var 1) (by decide +kernel)

theorem extra_argument :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.theoremApp 0 [.var 0, .var 1, .var 0] [.hyp 0, .hyp 1]) (.var 1)) (.sym "False") :=
  refuses theory hypotheses (.theoremApp 0 [.var 0, .var 1, .var 0] [.hyp 0, .hyp 1]) (.var 1) (by decide +kernel)

theorem wrong_argument_sort :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.theoremApp 0 [.var 2, .var 1] [.hyp 0, .hyp 1]) (.var 1)) (.sym "False") :=
  refuses theory hypotheses (.theoremApp 0 [.var 2, .var 1] [.hyp 0, .hyp 1]) (.var 1) (by decide +kernel)

theorem unknown_theorem :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.theoremApp 99 [] []) (.term 2)) (.sym "False") :=
  refuses theory hypotheses (.theoremApp 99 [] []) (.term 2) (by decide +kernel)

theorem no_premise_axiom :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.theoremApp 1 [] []) (.term 2)) (.sym "True") :=
  accepts theory hypotheses (.theoremApp 1 [] []) (.term 2) (by decide +kernel)

theorem bound_argument_must_be_variable :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.theoremApp 2 [.term 5, .var 0] []) (.term 2)) (.sym "False") :=
  refuses theory hypotheses (.theoremApp 2 [.term 5, .var 0] []) (.term 2) (by decide +kernel)

theorem dependency_collision :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.theoremApp 2 [.var 2, .var 3] []) (.term 2)) (.sym "False") :=
  refuses theory hypotheses (.theoremApp 2 [.var 2, .var 3] []) (.term 2) (by decide +kernel)

theorem fresh_dependency_substitution :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.theoremApp 2 [.var 4, .var 3] []) (.term 2)) (.sym "True") :=
  accepts theory hypotheses (.theoremApp 2 [.var 4, .var 3] []) (.term 2) (by decide +kernel)

theorem duplicate_bound_images :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.theoremApp 3 [.var 2, .var 2] []) (.term 2)) (.sym "False") :=
  refuses theory hypotheses (.theoremApp 3 [.var 2, .var 2] []) (.term 2) (by decide +kernel)

theorem distinct_bound_images :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.theoremApp 3 [.var 2, .var 4] []) (.term 2)) (.sym "True") :=
  accepts theory hypotheses (.theoremApp 3 [.var 2, .var 4] []) (.term 2) (by decide +kernel)

theorem repeated_premises_preserved :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.theoremApp 4 [.var 0] [.hyp 0, .hyp 0]) (.var 0)) (.sym "True") :=
  accepts theory hypotheses (.theoremApp 4 [.var 0] [.hyp 0, .hyp 0]) (.var 0) (by decide +kernel)

theorem repeated_premise_not_silently_dropped :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.theoremApp 4 [.var 0] [.hyp 0]) (.var 0)) (.sym "False") :=
  refuses theory hypotheses (.theoremApp 4 [.var 0] [.hyp 0]) (.var 0) (by decide +kernel)

theorem bad_child_not_replaced_by_another_derivation :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.theoremApp 4 [.var 0] [.hyp 0, .hyp 99]) (.var 0)) (.sym "False") :=
  refuses theory hypotheses (.theoremApp 4 [.var 0] [.hyp 0, .hyp 99]) (.var 0) (by decide +kernel)

theorem missing_conclusion_image :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.theoremApp 5 [] []) (.var 0)) (.sym "False") :=
  refuses theory hypotheses (.theoremApp 5 [] []) (.var 0) (by decide +kernel)

theorem missing_hypothesis_image :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.theoremApp 6 [] [.hyp 0]) (.term 2)) (.sym "False") :=
  refuses theory hypotheses (.theoremApp 6 [] [.hyp 0]) (.term 2) (by decide +kernel)

theorem nested_supplied_proof :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.theoremApp 4 [.var 1] [mp, mp]) (.var 1)) (.sym "True") :=
  accepts theory hypotheses (.theoremApp 4 [.var 1] [mp, mp]) (.var 1) (by decide +kernel)

theorem reflexive_conversion :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.conversion (.refl (.var 0)) (.hyp 0)) (.var 0)) (.sym "True") :=
  accepts theory hypotheses (.conversion (.refl (.var 0)) (.hyp 0)) (.var 0) (by decide +kernel)

theorem conversion_wrong_left_endpoint :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.conversion (.refl (.var 1)) (.hyp 0)) (.var 1)) (.sym "False") :=
  refuses theory hypotheses (.conversion (.refl (.var 1)) (.hyp 0)) (.var 1) (by decide +kernel)

theorem conversion_bad_midpoint :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.conversion (.trans (.refl (.var 0)) (.refl (.var 1))) (.hyp 0)) (.var 1)) (.sym "False") :=
  refuses theory hypotheses (.conversion (.trans (.refl (.var 0)) (.refl (.var 1))) (.hyp 0)) (.var 1) (by decide +kernel)

theorem definition_conversion_computes_substitution :
    Applies P H "mm0:check-proof" (inputs theory hypotheses (.conversion (.symm (.unfold 1 [.var 0] [])) (.hyp 0)) (.app (.term 1) (.var 0))) (.sym "True") :=
  accepts theory hypotheses (.conversion (.symm (.unfold 1 [.var 0] [])) (.hyp 0)) (.app (.term 1) (.var 0)) (by decide +kernel)

private def reversedTheory : Theory :=
  { theory with theorems := (0, ⟨mpDeclaration.arguments, mpDeclaration.hypotheses.reverse, mpDeclaration.conclusion⟩) :: theory.theorems }

private def changedAxiom : Theory :=
  { theory with theorems := (1, ⟨[], [], .term 3⟩) :: theory.theorems }

theorem changed_premise_order_rejects_original_certificate :
    Applies P H "mm0:check-proof" (inputs reversedTheory hypotheses mp (.var 1)) (.sym "False") :=
  refuses reversedTheory hypotheses mp (.var 1) (by decide +kernel)

theorem changed_premise_order_accepts_matching_certificate :
    Applies P H "mm0:check-proof"
      (inputs reversedTheory hypotheses (.theoremApp 0 [.var 0, .var 1] [.hyp 1, .hyp 0]) (.var 1)) (.sym "True") :=
  accepts reversedTheory hypotheses _ _ (by decide +kernel)

theorem changed_axiom_rejects_stale_conclusion :
    Applies P H "mm0:check-proof" (inputs changedAxiom hypotheses (.theoremApp 1 [] []) (.term 2)) (.sym "False") :=
  refuses changedAxiom hypotheses _ _ (by decide +kernel)

theorem changed_axiom_has_current_conclusion :
    Applies P H "mm0:check-proof" (inputs changedAxiom hypotheses (.theoremApp 1 [] []) (.term 3)) (.sym "True") :=
  accepts changedAxiom hypotheses _ _ (by decide +kernel)

theorem successful_claim_cannot_be_changed :
    ¬ Applies P H "mm0:check-proof" (inputs theory hypotheses mp (.var 1)) (.sym "False") := by
  intro computed
  have impossible := computed.deterministic modus_ponens
  simp at impossible

theorem no_fuel_is_not_refusal :
    apply P H 0 "mm0:check-proof" (inputs theory hypotheses mp (.var 1)) = .exhausted := rfl

theorem same_request_eventually_accepts :
    ∃ needed, ∀ fuel, needed ≤ fuel →
      apply P H fuel "mm0:check-proof" (inputs theory hypotheses mp (.var 1)) = .value (.sym "True") :=
  modus_ponens.at_least

theorem malformed_proof_tag_is_not_an_axiom :
    apply P H 1 "mm0:proof"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeTheorems theory.theorems,
        encodeContext context, encodeExpressions hypotheses, .list [.sym "MM0:FakeProof"]] = .failure := by
  rw [proof_apply _ (by decide)]
  rfl

theorem direct_hypothesis_execution :
    apply P H 16 "mm0:proof"
      [encodeTable [], encodeDefinitions [], encodeTheorems [], encodeContext [],
        encodeExpressions [.term 2], encodeProof (.hyp 0)] = .value (encodeResult (some (.term 2))) := by
  let cached : Host := ⟨fun head arguments =>
    if head = "nik:nat-zero" then
      match arguments with
      | [.lit "0"] => .value (.sym "True")
      | _ => dataEqualityHost.primitive head arguments
    else dataEqualityHost.primitive head arguments⟩
  have identical : cached = H := by
    apply congrArg Host.mk
    funext head arguments
    split
    · rename_i known
      subst head
      split
      · exact (naturalHost_zero 0).symm
      · rfl
    · rfl
  rw [← identical, encodeProof]
  rfl

end Mettapedia.Languages.MM0.Presentation.ComputationalProof.Controls
