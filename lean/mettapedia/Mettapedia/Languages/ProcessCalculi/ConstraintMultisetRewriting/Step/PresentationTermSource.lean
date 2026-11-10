import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationSourceRecovery

/-! # Unique scalar readback of terms in the composed transform grammar -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Source

open Mettapedia.GSLT.Parsing
open LanguageDefGrammarAlgebra PresentationExprSemantics
open Payloads

def termInput (term : Term) : List Nat :=
  SyntaxSource.printTokens ((syntaxAlgebra Payloads.rules).evaluate (termRoute term)).tokens

theorem canonical_term_source (term : Term) : ∃ tree,
    LanguageDefScalarStructural.tree? tree = some (termPattern term) ∧
      Nonempty (Parses "TcTerm" (termInput term) tree) :=
  LanguageDefScalarStructural.from_tokens (syntaxEmbedding.derives (printed_derivation term))
    (SyntaxSource.spell_printTokens _) (LanguageDefScalarPrinter.sequence_self _)

theorem canonical_term_recovery (term : Term) {tree : CST}
    (parsed : Parses "TcTerm" (termInput term) tree) :
    LanguageDefScalarStructural.tree? tree = some (termPattern term) := by
  obtain ⟨canonical, erased, ⟨derived⟩⟩ := canonical_term_source term
  have same := parse_unique parsed derived
  simpa only [same] using erased

theorem read_canonical_term (term : Term) {tree : CST}
    (parsed : Parses "TcTerm" (termInput term) tree) :
    (LanguageDefScalarStructural.tree? tree).bind readTerm = some term := by
  rw [canonical_term_recovery term parsed]
  exact readTerm_pattern term

theorem read_admitted_canonical_term (signature : Head → List Nat) (depth : Nat)
    (term : Term) (valid : Admitted signature depth term) {tree : CST}
    (parsed : Parses "TcTerm" (termInput term) tree) :
    (LanguageDefScalarStructural.tree? tree).bind (readAdmitted signature depth) = some ⟨term, valid⟩ := by
  rw [canonical_term_recovery term parsed]
  exact admitted_roundtrip signature depth ⟨term, valid⟩

def ruleInput (rule : RuleInstance Term) : List Nat := SyntaxSource.printTokens (ruleTokens rule)

theorem canonical_rule_source (rule : RuleInstance Term) : ∃ tree,
    LanguageDefScalarStructural.tree? tree = some (rulePattern rule) ∧
      Nonempty (Parses "TcRule" (ruleInput rule) tree) :=
  LanguageDefScalarStructural.from_tokens (syntaxEmbedding.derives (rule_printed_derivation rule))
    (SyntaxSource.spell_printTokens _) (LanguageDefScalarPrinter.sequence_self _)

theorem canonical_rule_recovery (rule : RuleInstance Term) {tree : CST}
    (parsed : Parses "TcRule" (ruleInput rule) tree) :
    (LanguageDefScalarStructural.tree? tree).bind readRule = some rule := by
  obtain ⟨canonical, erased, ⟨derived⟩⟩ := canonical_rule_source rule
  have same := parse_unique parsed derived
  rw [same, erased]
  exact readRule_pattern rule

#print axioms read_canonical_term
#print axioms read_admitted_canonical_term

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Source
