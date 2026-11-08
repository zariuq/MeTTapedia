import Mettapedia.GSLT.Parsing.GrammarCacheReuse

/-!
# Controls for grammar evolution and complete parse dependencies

These are executable guarded-grammar controls, not claims about Lean's surface
syntax. They distinguish irrelevant extension, missed alternatives, lookahead,
scope restoration, query changes, bounded emptiness and cache provenance.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GrammarCacheReuse.Controls

open CompilerCorrespondence (Category Codepoint CompiledSymbol)
open GuardCorrespondence (CompiledGrammar CompiledProduction CompiledGuard)
open BoundedScheduler (Candidate)
open GrammarReadDependencies
open Mettapedia.Machines

def rule (name category : String) (symbols : List CompiledSymbol)
    (guards : List CompiledGuard := []) : CompiledProduction :=
  { label := name, sourceRule := name, category, symbols, guards }

def startRule := rule "start" "S" [.nonterminal "A"]
def letterRule := rule "letter" "A" [.terminal 97]
def otherLetterRule := rule "other-letter" "A" [.terminal 98]
def alternativeRule := rule "alternative" "A" [.terminal 97]
def unrelatedRule := rule "unrelated" "B" [.terminal 99]

def base : CompiledGrammar := { start := "S", productions := [startRule, letterRule] }
def missing : CompiledGrammar := { base with productions := [startRule] }
def extended : CompiledGrammar := { base with productions := base.productions ++ [unrelatedRule] }
def ambiguous : CompiledGrammar := { base with productions := base.productions ++ [alternativeRule] }
def duplicate : CompiledGrammar := { base with productions := base.productions ++ [letterRule] }
def shadowed : CompiledGrammar := { base with productions := [startRule, otherLetterRule] }

def request : Request := { input := [97], fuel := 2 }
def entry := capture base request
def missingEntry := capture missing request

def roots (grammar : CompiledGrammar) (query : Request := request) : List Candidate :=
  BoundedScheduler.scheduleRoot grammar query.input query.fuel

theorem base_has_one_parse : (roots base).length = 1 := by decide

/-- The queried category catalogues are ordered; the unrelated category is not read. -/
theorem actual_catalogue_reads : entry.value.reads =
    [("S", [startRule]), ("A", [letterRule])] := by decide

theorem unrelated_extension_reuses :
    accepts extended request entry = true ∧
    (reuse extended request entry).2 = 0 ∧
    (reuse extended request entry).1.length = 1 := by decide

theorem newly_populated_missing_category_recomputes :
    missingEntry.value.reads = [("S", [startRule]), ("A", [])] ∧
    (roots missing).length = 0 ∧
    accepts base request missingEntry = false ∧
    (reuse base request missingEntry).2 = 1 ∧
    (reuse base request missingEntry).1.length = 1 := by decide

/-- A positive-only read check misses the insertion that creates a parse. -/
theorem discarding_negative_reads_is_unsound :
    ReadOnlyQuery.checkReads (catalogue base)
      (missingEntry.value.reads.filter fun observed => !observed.2.isEmpty) = true ∧
    missingEntry.value.answer.length = 0 ∧ (roots base).length = 1 := by decide

/-- Keeping the old winning rule does not preserve the complete result.
The second production creates another source-labelled tree. -/
theorem added_alternative_invalidates :
    accepts ambiguous request entry = false ∧
    (reuse ambiguous request entry).2 = 1 ∧
    (reuse ambiguous request entry).1.length = 2 := by decide

def childLabels (candidate : Candidate) : List String :=
  match candidate.tree with
  | .terminal _ => []
  | .node _ _ children => children.map fun tree =>
      match tree with
      | .terminal _ => "terminal"
      | .node label _ _ => label

theorem both_alternatives_retained :
    (roots ambiguous).map childLabels = [["letter"], ["alternative"]] := by decide

/-- Equal productions remain two occurrences in the candidate observation. -/
theorem duplicate_occurrences_retained :
    accepts duplicate request entry = false ∧
    (roots duplicate).map childLabels = [["letter"], ["letter"]] := by decide

/-- Merely retaining a subset loses a valid alternative. -/
theorem missing_parse_changes_observation :
    (roots ambiguous).length ≠ ((roots ambiguous).take 1).length := by decide

/-- Appending an unsupported result also changes the exact observation. -/
theorem spurious_parse_changes_observation :
    ((roots base) ++ roots base).length ≠ (roots base).length := by decide

/-- A packed node can be fabricated, but it has no source-rule replay. -/
theorem invented_rule_cannot_replay :
    ¬ GuardCorrespondence.CertificateReplays base [97]
      (.node "invented" "S" 0 1 []) "S" 0 1
      (.node "invented" "S" []) := by
  intro replay
  have rootRule : ∀ {certificate : CompilerCorrespondence.Certificate}
      {category : Category} {start stop : Nat} {tree : CompilerCorrespondence.ParseTree},
      GuardCorrespondence.CertificateReplays base [97] certificate category start stop tree →
      ∃ production ∈ base.productions, ∃ children,
        tree = .node production.sourceRule production.category children := by
    intro certificate category start stop tree checked
    cases checked with
    | node production member body guards => exact ⟨production, member, _, rfl⟩
  obtain ⟨production, member, children, same⟩ := rootRule replay
  have named : production.sourceRule = "invented" :=
    (CompilerCorrespondence.ParseTree.node.inj same).1.symm
  have impossible : ∃ production ∈ base.productions, production.sourceRule = "invented" :=
    ⟨production, member, named⟩
  simp [base, startRule, letterRule, rule] at impossible

theorem scope_change_then_restoration :
    accepts shadowed request entry = false ∧
    (reuse shadowed request entry).1.length = 0 ∧
    accepts base request entry = true ∧
    (reuse base request entry).2 = 0 ∧
    (reuse base request entry).1.length = 1 := by decide

def guardedRule := rule "guarded" "S" [.terminal 97] [.lookahead "Gate"]
def gateRule := rule "gate" "Gate" [] [.atEnd]
def gateMissing : CompiledGrammar := { start := "S", productions := [guardedRule] }
def gatePresent : CompiledGrammar := { gateMissing with productions := [guardedRule, gateRule] }
def gateEntry := capture gateMissing request

/-- A guard's zero-width category lookup is a dependency even though the
tree contains no child node for the lookahead witness. -/
theorem lookahead_insertion_invalidates :
    gateEntry.value.reads = [("S", [guardedRule]), ("Gate", [])] ∧
    accepts gatePresent request gateEntry = false ∧
    gateEntry.value.answer.length = 0 ∧
    (reuse gatePresent request gateEntry).1.length = 1 := by decide

theorem changed_input_recomputes :
    accepts base { request with input := [98] } entry = false ∧
    (reuse base { request with input := [98] } entry).2 = 1 ∧
    (reuse base { request with input := [98] } entry).1.length = 0 := by decide

theorem changed_root_recomputes :
    accepts { base with start := "A" } request entry = false ∧
    (reuse { base with start := "A" } request entry).2 = 1 := by decide

def shallow : Request := { request with fuel := 0 }
def shallowEntry := capture base shallow

/-- Bounded emptiness at fuel zero has no grammar reads and is reusable at
that bound. Increasing the budget is a different query and finds the parse. -/
theorem cutoff_is_not_rejection :
    shallowEntry.value.reads = [] ∧
    shallowEntry.value.answer.length = 0 ∧
    accepts ambiguous shallow shallowEntry = true ∧
    accepts base request shallowEntry = false ∧
    (reuse base request shallowEntry).1.length = 1 := by decide

/-- Validation is sufficient, not a minimal dependency characterization:
adding a failing rule in a read category can conservatively invalidate. -/
theorem conservative_invalidation :
    let after := { base with productions := base.productions ++ [otherLetterRule] }
    accepts after request entry = false ∧
    (roots after).map childLabels = (roots base).map childLabels := by decide

def forged : Entry :=
  { authority := "S", key := request, value := { answer := [], reads := [] } }

theorem read_validation_is_not_authentication :
    accepts base request forged = true ∧
    (reuse base request forged).1.length = 0 ∧ (roots base).length = 1 := by decide

/-- The generic correctness theorem requires an actual historical execution,
which this fabricated empty manifest cannot have. -/
theorem forged_not_recorded : ¬ ReadCertifiedQueryReuse.Recorded family forged := by
  intro recorded
  have exactAnswer := reuse_exact base request forged recorded
  have lengths := congrArg List.length exactAnswer
  have impossible : (0 : Nat) = 1 := lengths
  cases impossible

/-- Cache reuse removes the query execution while retaining all candidates. -/
theorem cached_execution_preserves_observation :
    (reuse extended request entry).1 = roots extended ∧
    (reuse extended request entry).2 = 0 :=
  ⟨reuse_capture_exact base extended request request, unrelated_extension_reuses.2.1⟩

end Mettapedia.GSLT.Parsing.GrammarCacheReuse.Controls
