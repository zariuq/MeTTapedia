import Mettapedia.Languages.MM0.Presentation.DeclarationCorrespondence

/-! # Positive and negative MM0 declaration formation controls -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalDeclaration.Controls

open Kernel ComputationalContext ComputationalTyping ComputationalArguments
open ComputationalDefinitions ComputationalProof
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => declarationProgram
local notation "H" => dataEqualityHost

private def sorts : SortTable :=
  [(0, {}), (1, { strict := true }), (2, { pure := true }),
    (3, { provable := true }), (4, { free := true })]

private def table : SignatureTable :=
  [(0, ⟨[], 0, ∅⟩), (1, ⟨[], 3, ∅⟩), (2, ⟨[.regular 3 ∅], 3, ∅⟩),
    (3, ⟨[], 99, ∅⟩)]

private def contextRun (context : Context) (result : Bool) : Prop :=
  Applies P H "mm0:form-context" [encodeSorts sorts, encodeContext context] (boolean result)

private theorem context_checked (context : Context) (result : Bool)
    (checked : Context.check (sortsOf sorts) context = result) : contextRun context result := by
  simpa only [contextRun, checked] using context_computes sorts context

theorem empty_context_accepts : contextRun [] true := context_checked [] true rfl

theorem preceding_bound_dependency_accepts : contextRun [.bound 0, .regular 0 {0}] true :=
  context_checked _ _ (by decide)

theorem self_dependency_refuses : contextRun [.regular 0 {0}] false := context_checked _ _ (by decide)

theorem forward_dependency_refuses : contextRun [.regular 0 {1}, .bound 0] false :=
  context_checked _ _ (by decide)

theorem regular_dependency_refuses : contextRun [.regular 0 ∅, .regular 0 {0}] false :=
  context_checked _ _ (by decide)

theorem missing_dependency_refuses : contextRun [.bound 0, .regular 0 {7}] false :=
  context_checked _ _ (by decide)

theorem strict_bound_sort_refuses : contextRun [.bound 1] false := context_checked _ _ (by decide)

theorem strict_regular_sort_accepts : contextRun [.regular 1 ∅] true := context_checked _ _ (by decide)

theorem pure_named_bound_parameter_accepts : contextRun [.bound 2] true := context_checked _ _ (by decide)

theorem free_named_bound_parameter_accepts : contextRun [.bound 4] true := context_checked _ _ (by decide)

theorem undeclared_sort_refuses : contextRun [.bound 99] false := context_checked _ _ (by decide)

theorem dependency_order_is_semantic :
    contextRun [.bound 0, .regular 0 {0}] true ∧ contextRun [.regular 0 {0}, .bound 0] false :=
  ⟨preceding_bound_dependency_accepts, context_checked _ _ (by decide)⟩

private theorem term_checked (declaration : TermDecl) (result : Bool)
    (checked : TermDecl.check (sortsOf sorts) declaration = result) :
    Applies P H "mm0:form-term" [encodeSorts sorts, encodeDeclaration declaration] (boolean result) := by
  simpa only [checked] using term_computes sorts declaration

theorem ordinary_term_accepts :
    Applies P H "mm0:form-term" [encodeSorts sorts, encodeDeclaration ⟨[], 0, ∅⟩] (.sym "True") :=
  term_checked _ true (by decide)

theorem pure_result_refuses :
    Applies P H "mm0:form-term" [encodeSorts sorts, encodeDeclaration ⟨[], 2, ∅⟩] (.sym "False") :=
  term_checked _ false (by decide)

theorem missing_result_sort_refuses :
    Applies P H "mm0:form-term" [encodeSorts sorts, encodeDeclaration ⟨[], 99, ∅⟩] (.sym "False") :=
  term_checked _ false (by decide)

theorem bound_return_dependency_accepts :
    Applies P H "mm0:form-term" [encodeSorts sorts, encodeDeclaration ⟨[.bound 0], 0, {0}⟩] (.sym "True") :=
  term_checked _ true (by decide)

theorem regular_return_dependency_refuses :
    Applies P H "mm0:form-term" [encodeSorts sorts, encodeDeclaration ⟨[.regular 0 ∅], 0, {0}⟩] (.sym "False") :=
  term_checked _ false (by decide)

theorem out_of_scope_return_dependency_refuses :
    Applies P H "mm0:form-term" [encodeSorts sorts, encodeDeclaration ⟨[.bound 0], 0, {1}⟩] (.sym "False") :=
  term_checked _ false (by decide)

private theorem dummies_checked (dummies : List Nat) (result : Bool)
    (checked : Definition.checkDummySorts (sortsOf sorts) dummies = result) :
    Applies P H "mm0:form-dummies" [encodeSorts sorts, encodeNaturals dummies] (boolean result) := by
  simpa only [checked] using dummies_computes sorts dummies

theorem repeated_dummy_sort_is_allowed :
    Applies P H "mm0:form-dummies" [encodeSorts sorts, encodeNaturals [0, 0]] (.sym "True") :=
  dummies_checked _ true (by decide)

theorem strict_dummy_sort_refuses :
    Applies P H "mm0:form-dummies" [encodeSorts sorts, encodeNaturals [1]] (.sym "False") :=
  dummies_checked _ false (by decide)

theorem free_dummy_sort_refuses :
    Applies P H "mm0:form-dummies" [encodeSorts sorts, encodeNaturals [4]] (.sym "False") :=
  dummies_checked _ false (by decide)

theorem unknown_dummy_sort_refuses :
    Applies P H "mm0:form-dummies" [encodeSorts sorts, encodeNaturals [99]] (.sym "False") :=
  dummies_checked _ false (by decide)

private theorem theorem_checked (declaration : TheoremDecl) (result : Bool)
    (checked : TheoremDecl.check (sortsOf sorts) (signatureOf table) declaration = result) :
    Applies P H "mm0:form-theorem" [encodeSorts sorts, encodeTable table, encodeTheorem declaration] (boolean result) := by
  simpa only [checked] using theorem_computes sorts table declaration

theorem statement_payload_accepts :
    Applies P H "mm0:form-theorem" [encodeSorts sorts, encodeTable table, encodeTheorem ⟨[], [], .term 1⟩] (.sym "True") :=
  theorem_checked _ true (by decide)

theorem data_is_not_a_statement :
    Applies P H "mm0:form-theorem" [encodeSorts sorts, encodeTable table, encodeTheorem ⟨[], [], .term 0⟩] (.sym "False") :=
  theorem_checked _ false (by decide)

theorem unknown_statement_sort_refuses :
    Applies P H "mm0:form-theorem" [encodeSorts sorts, encodeTable table, encodeTheorem ⟨[], [], .term 3⟩] (.sym "False") :=
  theorem_checked _ false (by decide)

theorem unapplied_statement_constructor_refuses :
    Applies P H "mm0:form-theorem" [encodeSorts sorts, encodeTable table, encodeTheorem ⟨[], [], .term 2⟩] (.sym "False") :=
  theorem_checked _ false (by decide)

theorem applied_statement_constructor_accepts :
    Applies P H "mm0:form-theorem" [encodeSorts sorts, encodeTable table,
      encodeTheorem ⟨[], [], .app (.term 2) (.term 1)⟩] (.sym "True") :=
  theorem_checked _ true (by decide)

theorem data_hypothesis_refuses :
    Applies P H "mm0:form-theorem" [encodeSorts sorts, encodeTable table,
      encodeTheorem ⟨[], [.term 0], .term 1⟩] (.sym "False") :=
  theorem_checked _ false (by decide)

theorem repeated_valid_hypotheses_accept :
    Applies P H "mm0:form-theorem" [encodeSorts sorts, encodeTable table,
      encodeTheorem ⟨[], [.term 1, .term 1], .term 1⟩] (.sym "True") :=
  theorem_checked _ true (by decide)

theorem malformed_formal_context_refuses :
    Applies P H "mm0:form-theorem" [encodeSorts sorts, encodeTable table,
      encodeTheorem ⟨[.regular 0 {0}], [], .term 1⟩] (.sym "False") :=
  theorem_checked _ false (by decide)

theorem valid_payload_does_not_publish_its_claim :
    Applies P H "mm0:check-proof" [encodeTable table, encodeDefinitions [], encodeTheorems [],
      encodeContext [], encodeExpressions [], encodeProof (.theoremApp 0 [] []), encode (.term 1)] (.sym "False") := by
  apply proof_reused _ (by
    simp only [proofProgram, Program.calledHeads, List.flatMap_append, List.mem_append]
    exact Or.inr (by decide))
  have run := check_computes table [] [] [] [] (.theoremApp 0 [] []) (.term 1)
  simpa [show ProofWitness.check (signatureOf table) (definitionsOf []) (theoremsOf [])
    [] [] (.theoremApp 0 [] []) (.term 1) = false from by decide +kernel, boolean] using run

theorem changing_sort_flag_changes_payload_acceptance :
    Applies P H "mm0:form-theorem"
      [encodeSorts [(3, {})], encodeTable table, encodeTheorem ⟨[], [], .term 1⟩] (.sym "False") := by
  have run := theorem_computes [(3, {})] table ⟨[], [], .term 1⟩
  simpa [show TheoremDecl.check (sortsOf [(3, {})]) (signatureOf table) ⟨[], [], .term 1⟩ = false from by decide,
    boolean] using run

theorem unbounded_sort_identity_is_preserved :
    Applies P H "mm0:form-context"
      [encodeSorts [(18446744073709551616, {})], encodeContext [.bound 18446744073709551616]] (.sym "True") := by
  have run := context_computes [(18446744073709551616, {})] [.bound 18446744073709551616]
  simpa [show Context.check (sortsOf [(18446744073709551616, {})]) [.bound 18446744073709551616] = true from by decide,
    boolean] using run

theorem exhaustion_is_not_invalid_payload :
    apply P H 0 "mm0:form-theorem" [encodeSorts sorts, encodeTable table, encodeTheorem ⟨[], [], .term 1⟩] =
      .exhausted := rfl

theorem direct_empty_context_execution :
    apply P H 4 "mm0:form-context" [encodeSorts sorts, encodeContext []] = .value (.sym "True") := by
  rw [declaration_apply _ (by decide)]
  rfl

end Mettapedia.Languages.MM0.Presentation.ComputationalDeclaration.Controls
