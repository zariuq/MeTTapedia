import Mettapedia.Languages.MM0.Kernel.SpecificationChecking

/-! # Fixed-specification admission controls -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.SpecificationControls

open SpecificationAdmission

private def claim : TheoremDecl := ⟨[], [], .term 7⟩
private def specification : List SpecificationEntry :=
  [.sort 0 { provable := true }, .term 7 ⟨[], 0, ∅⟩,
    .axiomDecl 10 claim, .theoremDecl 11 claim]
private def initialDeclarations : List ProofDeclaration :=
  [⟨.sort 0 { provable := true }, false⟩, ⟨.term 7 ⟨[], 0, ∅⟩, false⟩,
    ⟨.axiomDecl 10 claim, false⟩]
private def declarations : List ProofDeclaration := initialDeclarations ++
  [⟨.definition 9 ⟨[], 0, ∅⟩ ⟨[], .term 7⟩, true⟩,
    ⟨.theoremDecl 20 claim [] (.theoremApp 10 [] []), true⟩,
    ⟨.theoremDecl 11 claim [] (.theoremApp 20 [] []), false⟩]

theorem complete_specification_with_auxiliaries_accepts :
    (verify? specification declarations).isSome = true := by decide +kernel

theorem auxiliary_declarations_add_no_axiom :
    declarationAxioms declarations = [(10, claim)] := rfl

theorem specification_retains_complete_axiom_payload :
    specificationAxioms specification = [(10, claim)] := rfl

theorem missing_theorem_refuses : (verify? specification initialDeclarations).isNone = true := by decide +kernel

theorem axiom_cannot_replace_theorem :
    (verify? specification (initialDeclarations ++ [⟨.axiomDecl 11 claim, false⟩])).isNone = true := by decide +kernel

theorem extra_local_axiom_refuses :
    (verify? specification (initialDeclarations ++ [⟨.axiomDecl 11 claim, true⟩])).isNone = true := by decide +kernel

theorem extra_local_sort_refuses :
    (verify? specification (initialDeclarations ++ [⟨.sort 1 {}, true⟩])).isNone = true := by decide +kernel

theorem extra_local_primitive_term_refuses :
    (verify? specification (initialDeclarations ++ [⟨.term 8 ⟨[], 0, ∅⟩, true⟩])).isNone = true := by decide +kernel

theorem local_theorem_still_requires_proof :
    (verify? specification (initialDeclarations ++ [⟨.theoremDecl 20 claim [] (.hyp 0), true⟩])).isNone = true :=
  by decide +kernel

theorem public_theorem_still_requires_proof :
    (verify? specification (initialDeclarations ++ [⟨.theoremDecl 11 claim [] (.hyp 0), false⟩])).isNone = true :=
  by decide +kernel

theorem local_definition_still_requires_admitted_body :
    (verify? specification (initialDeclarations ++
      [⟨.definition 9 ⟨[], 0, ∅⟩ ⟨[], .term 9⟩, true⟩])).isNone = true := by decide +kernel

theorem unexpected_public_declaration_after_end_refuses :
    (verify? specification (declarations ++ [⟨.axiomDecl 21 claim, false⟩])).isNone = true :=
  by decide +kernel

theorem proved_local_theorem_after_end_accepts :
    (verify? specification (declarations ++
      [⟨.theoremDecl 21 claim [] (.theoremApp 11 [] []), true⟩])).isSome = true := by decide +kernel

theorem reordered_specification_refuses :
    (verify? specification.reverse declarations).isNone = true := by decide +kernel

theorem missing_specification_axiom_refuses :
    (verify? [.sort 0 { provable := true }, .term 7 ⟨[], 0, ∅⟩, .theoremDecl 11 claim]
      declarations).isNone = true := by decide +kernel

theorem changed_axiom_statement_refuses :
    (verify? [.sort 0 { provable := true }, .term 7 ⟨[], 0, ∅⟩,
      .axiomDecl 10 ⟨[], [.term 7], .term 7⟩, .theoremDecl 11 claim]
      declarations).isNone = true := by decide +kernel

theorem changed_sort_modifier_refuses :
    (verify? [.sort 0 {}, .term 7 ⟨[], 0, ∅⟩, .axiomDecl 10 claim, .theoremDecl 11 claim]
      declarations).isNone = true := by decide +kernel

theorem unfilled_definition_body_accepts_admitted_implementation :
    (verify? [.sort 0 { provable := true }, .term 7 ⟨[], 0, ∅⟩,
        .definition 9 ⟨[], 0, ∅⟩ none]
      [⟨.sort 0 { provable := true }, false⟩, ⟨.term 7 ⟨[], 0, ∅⟩, false⟩,
        ⟨.definition 9 ⟨[], 0, ∅⟩ ⟨[], .term 7⟩, false⟩]).isSome = true := by decide +kernel

theorem explicit_definition_body_must_match :
    SpecificationEntry.checkMatch (.definition 9 ⟨[], 0, ∅⟩ (some ⟨[], .term 7⟩))
      (.definition 9 ⟨[], 0, ∅⟩ ⟨[], .term 8⟩) = false := by decide +kernel

theorem matching_definition_body_accepts :
    SpecificationEntry.checkMatch (.definition 9 ⟨[], 0, ∅⟩ (some ⟨[], .term 7⟩))
      (.definition 9 ⟨[], 0, ∅⟩ ⟨[], .term 7⟩) = true := by decide +kernel

theorem extra_dummy_declaration_in_explicit_body_refuses :
    SpecificationEntry.checkMatch (.definition 9 ⟨[], 0, ∅⟩ (some ⟨[], .term 7⟩))
      (.definition 9 ⟨[], 0, ∅⟩ ⟨[0], .term 7⟩) = false := by decide +kernel

theorem theorem_hypothesis_order_is_significant :
    SpecificationEntry.checkMatch (.theoremDecl 11 ⟨[], [.term 7, .term 8], .term 7⟩)
      (.theoremDecl 11 ⟨[], [.term 8, .term 7], .term 7⟩ [] (.hyp 0)) = false := by decide +kernel

end Mettapedia.Languages.MM0.Kernel.SpecificationControls
