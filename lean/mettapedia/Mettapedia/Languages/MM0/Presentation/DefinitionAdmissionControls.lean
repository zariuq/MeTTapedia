import Mettapedia.Languages.MM0.Presentation.DefinitionAdmissionCorrespondence

/-! # Definition admission computes typing and binding-sensitive dependencies -/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalDefinitionAdmission.Controls

open Kernel ComputationalContext ComputationalTyping ComputationalDefinitions ComputationalDeclaration
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => bodyProgram
local notation "H" => dataEqualityHost

private def sorts : SortTable := [(0, {}), (1, { strict := true }), (2, {}), (4, { free := true })]
private def table : SignatureTable :=
  [(0, ⟨[], 0, ∅⟩), (1, ⟨[], 2, ∅⟩), (2, ⟨[.regular 0 ∅], 0, ∅⟩),
    (5, ⟨[.bound 0, .regular 0 {0}], 0, ∅⟩), (6, ⟨[.bound 0, .regular 0 {0}], 0, {0}⟩)]

private def run (declaration : TermDecl) (body : Definition.Body) (result : Bool) : Prop :=
  Applies P H "mm0:form-body" [encodeSorts sorts, encodeTable table, encodeDeclaration declaration, encodeBody body]
    (boolean result)

private theorem checked (declaration : TermDecl) (body : Definition.Body) (result : Bool)
    (accepted : Definition.checkBody (sortsOf sorts) (signatureOf table) declaration body = result) :
    run declaration body result := by
  simpa only [run, accepted] using body_computes sorts table declaration body

theorem closed_constant_accepts : run ⟨[], 0, ∅⟩ ⟨[], .term 0⟩ true := checked _ _ _ (by decide +kernel)

theorem wrong_result_sort_refuses : run ⟨[], 2, ∅⟩ ⟨[], .term 0⟩ false := checked _ _ _ (by decide +kernel)

theorem unknown_body_symbol_refuses : run ⟨[], 0, ∅⟩ ⟨[], .term 99⟩ false := checked _ _ _ (by decide +kernel)

theorem unapplied_body_refuses : run ⟨[], 0, ∅⟩ ⟨[], .term 2⟩ false := checked _ _ _ (by decide +kernel)

theorem applied_body_accepts : run ⟨[], 0, ∅⟩ ⟨[], .app (.term 2) (.term 0)⟩ true := checked _ _ _ (by decide +kernel)

theorem wrong_argument_sort_refuses : run ⟨[], 0, ∅⟩ ⟨[], .app (.term 2) (.term 1)⟩ false :=
  checked _ _ _ (by decide +kernel)

theorem declared_bound_dependency_accepts : run ⟨[.bound 0], 0, {0}⟩ ⟨[], .var 0⟩ true :=
  checked _ _ _ (by decide +kernel)

theorem undeclared_bound_dependency_refuses : run ⟨[.bound 0], 0, ∅⟩ ⟨[], .var 0⟩ false :=
  checked _ _ _ (by decide +kernel)

theorem regular_dependency_is_computed : run ⟨[.bound 0, .regular 0 {0}], 0, {0}⟩ ⟨[], .var 1⟩ true :=
  checked _ _ _ (by decide +kernel)

theorem undeclared_regular_dependency_refuses : run ⟨[.bound 0, .regular 0 {0}], 0, ∅⟩ ⟨[], .var 1⟩ false :=
  checked _ _ _ (by decide +kernel)

theorem unused_dummy_accepts : run ⟨[], 0, ∅⟩ ⟨[0], .term 0⟩ true := checked _ _ _ (by decide +kernel)

theorem strict_dummy_refuses_even_when_unused : run ⟨[], 0, ∅⟩ ⟨[1], .term 0⟩ false :=
  checked _ _ _ (by decide +kernel)

theorem free_dummy_refuses_even_when_unused : run ⟨[], 0, ∅⟩ ⟨[4], .term 0⟩ false :=
  checked _ _ _ (by decide +kernel)

theorem undeclared_dummy_sort_refuses : run ⟨[], 0, ∅⟩ ⟨[99], .term 0⟩ false := checked _ _ _ (by decide +kernel)

theorem dummy_escape_refuses : run ⟨[], 0, ∅⟩ ⟨[0], .var 0⟩ false := checked _ _ _ (by decide +kernel)

theorem dummy_follows_formal_context : run ⟨[.bound 0], 0, {0}⟩ ⟨[0], .var 0⟩ true :=
  checked _ _ _ (by decide +kernel)

theorem later_dummy_is_not_earlier_parameter : run ⟨[.bound 0], 0, {0}⟩ ⟨[0], .var 1⟩ false :=
  checked _ _ _ (by decide +kernel)

theorem binder_removes_its_argument_dependency :
    run ⟨[.bound 0, .regular 0 {0}], 0, ∅⟩ ⟨[], .app (.app (.term 5) (.var 0)) (.var 1)⟩ true :=
  checked _ _ _ (by decide +kernel)

theorem return_dependency_reintroduces_binding :
    run ⟨[.bound 0, .regular 0 {0}], 0, ∅⟩ ⟨[], .app (.app (.term 6) (.var 0)) (.var 1)⟩ false :=
  checked _ _ _ (by decide +kernel)

theorem dummy_can_be_bound_inside_body :
    run ⟨[], 0, ∅⟩ ⟨[0], .app (.app (.term 5) (.var 0)) (.var 0)⟩ true :=
  checked _ _ _ (by decide +kernel)

theorem body_check_does_not_replace_declaration_check :
    run ⟨[], 0, {99}⟩ ⟨[], .term 0⟩ true ∧
    Applies P H "mm0:form-term" [encodeSorts sorts, encodeDeclaration ⟨[], 0, {99}⟩] (.sym "False") := by
  constructor
  · exact checked _ _ _ (by decide +kernel)
  · apply declaration_suffix_reused _ (by decide)
    have formed := term_computes sorts ⟨[], 0, {99}⟩
    simpa [show TermDecl.check (sortsOf sorts) ⟨[], 0, {99}⟩ = false from by decide +kernel, boolean] using formed

theorem accepted_body_cannot_also_refuse : ¬ run ⟨[], 0, ∅⟩ ⟨[], .term 0⟩ false := by
  intro refused
  have impossible := refused.deterministic closed_constant_accepts
  simp [boolean] at impossible

theorem body_exhaustion_is_not_refusal :
    apply P H 0 "mm0:form-body" [encodeSorts sorts, encodeTable table,
      encodeDeclaration ⟨[], 0, ∅⟩, encodeBody ⟨[], .term 0⟩] = .exhausted := rfl

theorem dummy_context_retains_order_and_multiplicity :
    Applies P H "mm0:dummy-context" [encodeNaturals [0, 2, 0]]
      (encodeContext [.bound 0, .bound 2, .bound 0]) := dummy_context_computes _

theorem direct_empty_dummy_context_execution :
    apply P H 3 "mm0:dummy-context" [encodeNaturals []] = .value (encodeContext []) := by
  rw [body_apply _ (by decide)]
  rfl

end Mettapedia.Languages.MM0.Presentation.ComputationalDefinitionAdmission.Controls
