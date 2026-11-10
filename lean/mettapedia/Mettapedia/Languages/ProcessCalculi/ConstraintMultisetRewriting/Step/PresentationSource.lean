import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationOccurrenceProfile
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationSyntaxSource
import Mettapedia.GSLT.Parsing.LanguageDefGrammarEmbedding
import Mettapedia.GSLT.Parsing.ConstructorArgumentRouting

/-! # Source syntax for the composed transform entry

The entry grammar parses complete `Request` and `At` forms. Its structural
payload rows are embedded at their original positions. Scalar parsing and
packed-forest admission use the existing compiler and replay correspondence;
source derivations retain their production choices and CST spans.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Source

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.GSLT.Parsing
open LanguageDefSyntaxCompiler LanguageDefGrammarAlgebra
open ParserProfileSemantics PresentationExprSemantics ClassAwareParserPackCorrespondence
open ClassAwarePackedForest ClassAwareParserPackCertificate
open Payloads

/-- Preserve production occurrences, rather than searching for equal labels. -/
def syntaxEmbedding : LanguageDefGrammarEmbedding.Embedding dataLanguage authoredLanguage where
  index := {
    toFun := fun i => ⟨i.val, by have bound : i.val < 25 := i.isLt; change i.val < 29; omega⟩
    inj' := by
      intro first second same
      exact Fin.ext (congrArg (fun i : Fin authoredLanguage.terms.length => i.val) same) }
  row := by intro index; fin_cases index <;> rfl

def rules : List CompiledRule :=
  (compileRules? Payloads.binding authoredLanguage).get (by decide +kernel)

theorem rules_compiled : compileRules? Payloads.binding authoredLanguage = some rules := by
  decide +kernel

def profile (sort : String) : ParserProfileLayer := ⟨"Tcalc.Transform.scalar-v1", sort, [], []⟩

abbrev literalScalars := SyntaxSource.literalScalars

def plan (sort : String) : CompiledParserPackPlan :=
  { lexical := compileLexicalPack (profile sort)
    structural := (compileStructuralProductions? literalScalars sort rules).get (by rfl) }

theorem plan_compiled (sort : String) :
    compileParserPackPlan? literalScalars (profile sort) rules = some (plan sort) := rfl

theorem plan_agreement (sort : String) :
    ParserPackPlanAgreement literalScalars (profile sort) rules (plan sort) :=
  ParserPackPlanAgreement.of_compilation (plan_compiled sort)

abbrev Parses (sort : String) (input : List Nat) (tree : CST) :=
  LanguageDefScalarSyntax.DerivesAt literalScalars (profile sort) authoredLanguage input
    sort 0 input.length tree

/-- A static certificate for the direct structural reader. A same-sort
parameter permutation changes this obligation even when child sorts agree. -/
theorem arguments_direct : ∀ rule ∈ authoredLanguage.terms,
    ConstructorArgumentRouting.DirectOrder rule := by decide +kernel

theorem source_arguments_routed {sort : String} {input : List Nat} {tree : CST}
    (source : Parses sort input tree) {pattern : Pattern}
    (erased : LanguageDefScalarStructural.tree? tree = some pattern) :
    ConstructorArgumentRouting.Routed authoredLanguage pattern pattern := by
  obtain ⟨tokens, result, erased', derived, _⟩ :=
    LanguageDefScalarStructural.full_source_to_tokens rfl source
  have same : result = pattern := Option.some.inj (erased'.symm.trans erased)
  subst result
  exact ConstructorArgumentRouting.derives_routed_self arguments_direct derived

abbrev Packed (forest : Forest) (sort : String) (input : List Nat) (tree : CST) :=
  PackedFibre forest (profile sort) (plan sort) input sort 0 input.length tree

theorem source_iff_root (sort : String) (input : List Nat) (tree : CST) :
    Nonempty (Parses sort input tree) ↔
      Nonempty (ParserPackRootDerives (profile sort) (plan sort) input tree) :=
  (LanguageDefScalarSyntax.source_plan_iff rules_compiled).trans
    (sourcePlanRootDerivationEquiv (plan_agreement sort) tree).nonempty_congr

theorem packed_reflects (forest : Forest) (sort : String) (input : List Nat) (tree : CST) :
    Nonempty (Packed forest sort input tree) → Nonempty (Parses sort input tree) := by
  rintro ⟨certificate, replay⟩
  exact (source_iff_root sort input tree).mpr ⟨replay.derivation⟩

theorem complete_forest_iff_source (forest : Forest) (sort : String) (input : List Nat)
    (checked : ClassAwarePackedForestSaturation.validateRuleSaturation
      forest (profile sort) (plan sort) input = true) (tree : CST) :
    Nonempty (Packed forest sort input tree) ↔ Nonempty (Parses sort input tree) := by
  refine ⟨packed_reflects forest sort input tree, ?_⟩
  intro source
  obtain ⟨derived⟩ := (source_iff_root sort input tree).mp source
  have complete := ClassAwarePackedForestSaturation.validateRuleSaturation_root_complete checked tree
  exact ⟨Certificate.ofDerivation derived, ⟨complete derived⟩,
    ClassAwareParserPackCertificate.Replays.ofDerivation derived⟩

def configurationTokens (state : Execution.State) : List String :=
  ((syntaxAlgebra Payloads.rules).evaluate (configurationRoute state)).tokens

def ruleTokens (rule : RuleInstance Term) : List String :=
  ((syntaxAlgebra Payloads.rules).evaluate (ruleRoute rule)).tokens

def selectionTokens (selection : Selection Nat) : List String :=
  ((syntaxAlgebra Payloads.rules).evaluate (selectionRoute selection)).tokens

def stateTokens (state : Execution.State) : List String :=
  ["(", "state"] ++ configurationTokens state ++ [")"]

def firingTokens (candidate : (_state : Execution.State) × Execution.Candidate) : List String :=
  "(" :: "candidate" :: (configurationTokens candidate.1 ++
    (ruleTokens candidate.2.1 ++ (selectionTokens candidate.2.2 ++ [")"])))

def requestTokens (state : Execution.State) (candidate : Execution.Candidate) : List String :=
  "fire" :: (stateTokens state ++ firingTokens ⟨state, candidate⟩)

theorem state_derives (state : Execution.State) :
    GrammarDerives.Derives authoredLanguage "State" (stateTokens state)
      (OccurrenceProfile.statePattern state) := by
  refine .rule authoredLanguage.terms[25] (by decide +kernel) "State" rfl _ _ ?_
  refine .terminal _ "(" _ _ _ (.terminal _ "state" _ _ _ ?_)
  refine .nonTerminal _ "configuration" "TcConfiguration" rfl _ _
    (syntaxEmbedding.derives (configuration_printed_derivation state)) _ _ _ ?_
  exact .terminal _ ")" _ _ _ (.nil _)

theorem firing_derives (candidate : (_state : Execution.State) × Execution.Candidate) :
    GrammarDerives.Derives authoredLanguage "Firing" (firingTokens candidate)
      (OccurrenceProfile.firingPattern candidate) := by
  rcases candidate with ⟨state, rule, selection⟩
  refine .rule authoredLanguage.terms[26] (by decide +kernel) "Firing" rfl _ _ ?_
  refine .terminal _ "(" _ _ _ (.terminal _ "candidate" _ _ _ ?_)
  refine .nonTerminal authoredLanguage.terms[26] "source" "TcConfiguration" rfl _ _
    (syntaxEmbedding.derives (configuration_printed_derivation state)) _ _ _ ?_
  refine .nonTerminal authoredLanguage.terms[26] "rule" "TcRule" rfl _ _
    (syntaxEmbedding.derives (rule_printed_derivation rule)) _ _ _ ?_
  refine .nonTerminal authoredLanguage.terms[26] "selection" "TcSelection" rfl _ _
    (syntaxEmbedding.derives (selection_printed_derivation selection)) _ _ _ ?_
  exact .terminal _ ")" _ _ _ (.nil _)

theorem request_derives (state : Execution.State) (candidate : Execution.Candidate) :
    GrammarDerives.Derives authoredLanguage "Proc" (requestTokens state candidate)
      (request (OccurrenceProfile.statePattern state)
        (OccurrenceProfile.firingPattern ⟨state, candidate⟩)) := by
  refine .rule authoredLanguage.terms[28] (by decide +kernel) "Proc" rfl _ _ ?_
  refine .terminal _ "fire" _ _ _ ?_
  refine .nonTerminal _ "state" "State" rfl _ _ (state_derives state) _ _ _ ?_
  simpa only [List.append_nil] using
    (GrammarDerives.DerivesItems.nonTerminal authoredLanguage.terms[28]
      "firing" "Firing" rfl _ _ (firing_derives ⟨state, candidate⟩) [] [] [] (.nil _))

def requestInput (state : Execution.State) (candidate : Execution.Candidate) : List Nat :=
  SyntaxSource.printTokens (requestTokens state candidate)

/-- Every semantic occurrence candidate has a complete source request in the
composed entry grammar, not merely separate rule and selection documents. -/
theorem canonical_request_source (state : Execution.State) (candidate : Execution.Candidate) :
    ∃ tree, LanguageDefScalarStructural.tree? tree =
      some (request (OccurrenceProfile.statePattern state)
        (OccurrenceProfile.firingPattern ⟨state, candidate⟩)) ∧
      Nonempty (Parses "Proc" (requestInput state candidate) tree) :=
  LanguageDefScalarStructural.from_tokens (request_derives state candidate)
    (SyntaxSource.spell_printTokens _) (LanguageDefScalarPrinter.sequence_self _)

#print axioms syntaxEmbedding
#print axioms source_arguments_routed
#print axioms state_derives
#print axioms firing_derives
#print axioms request_derives
#print axioms canonical_request_source
#print axioms complete_forest_iff_source

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Source
