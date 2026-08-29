import Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationCanary

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofRulePresentationCanary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivationCanary

def oneRulePresentation : FiniteVerifierRulePresentation where
  family := "compressed-verifier-rule"
  owner := compressedVerifierRuleOwner
  endTag := "mm-compressed-verifier-rule-end"
  rules := [canaryOpaqueRule]

def mutatedOpaqueRule : Atom :=
  .expression [.symbol "compressed-mutated-rule"]

def mutatedPresentation : FiniteVerifierRulePresentation :=
  { oneRulePresentation with rules := [mutatedOpaqueRule] }

def twoRulePresentation : FiniteVerifierRulePresentation :=
  { oneRulePresentation with rules := [canaryOpaqueRule, mutatedOpaqueRule] }

/-- The presentation lowering transports the exact supplied target rule. -/
theorem one_rule_presentation_lowers_exactly :
    oneRulePresentation.rows = [canaryRuleRow] ∧
      oneRulePresentation.endRow = canaryRuleEnd 1 := by
  decide +kernel

/-- Changing the supplied target presentation changes the emitted MM2 rows;
the lowering does not recognize and replace a familiar verifier inventory. -/
theorem target_rule_mutation_changes_lowered_rows :
    oneRulePresentation.rows ≠ mutatedPresentation.rows := by
  decide +kernel

/-- The reusable GSLT-to-GSLT stage transports both ordered occurrences and
reaches the exact linked terminal state without inspecting either rule. -/
theorem two_rule_linked_loader_is_exact :
    twoRulePresentation.linkedLoaderTerminal.loaded =
        [canaryOpaqueRule, mutatedOpaqueRule] ∧
      twoRulePresentation.linkedLoaderTerminal.cursor = 2 ∧
      twoRulePresentation.linkedLoaderTerminal.remaining = [] ∧
      twoRulePresentation.linkedLoaderPath.length =
        twoRulePresentation.loaderPath.length := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · exact twoRulePresentation.linkedLoaderPath_length

#print axioms one_rule_presentation_lowers_exactly
#print axioms target_rule_mutation_changes_lowered_rows
#print axioms two_rule_linked_loader_is_exact

end Mettapedia.Languages.Metamath.MM2CompressedProofRulePresentationCanary
