import Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
import Mettapedia.GSLT.Parsing.HornCertificate

/-!
# Canonical source GSLTs as admitted first-order Horn programs

The native `gslt-presentation-v1` evaluator gives every authored `rule` the
ordinary definite-clause reading `head :- body`.  This module connects the
exact source decoder directly to the existing `HornCertificate` calculus.
It introduces no parser or compiler IR: the target is the same named,
ordered Horn program used by specialization and certificate replay.

Source variables are the non-anonymous `?name` atoms used by the native
format.  Their numeric Horn identifiers are assigned by first occurrence
inside each rule.  The accompanying variable-name list is only an exact
codec witness: re-quotation must reconstruct the original rule byte syntax
tree, including integer spelling, or elaboration fails closed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.CanonicalSourceHornElaboration

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
open Mettapedia.GSLT.Parsing.HornCertificate

abbrev ScopedRule := List String × Rule

def sourceVariableToken (token : String) : Bool :=
  token.startsWith "?" && token != "?" && token != "?_"

/-- A cheap transparent guard for tokens that can possibly be parsed as an
integer.  Besides making the common symbol path explicit, this keeps closed
source qualification kernel-reducible: `String.toInt?` is consulted only for
tokens beginning with a decimal digit or sign. -/
def mayStartInteger (token : String) : Bool :=
  match token.toList with
  | [] => false
  | head :: _ => head.isDigit || head == '-' || head == '+'

/-- Accumulate variable names in first-occurrence order.  This transparent
definition is used instead of the runtime-oriented library duplicate eraser so
closed source qualifications can reduce in the kernel. -/
def collectDistinctNames : List String -> List String -> List String
  | [], collected => collected
  | name :: rest, collected =>
      if name ∈ collected then
        collectDistinctNames rest collected
      else
        collectDistinctNames rest (collected ++ [name])

def distinctNames (occurrences : List String) : List String :=
  collectDistinctNames occurrences []

/-- First position of a variable name in the explicit scope. -/
def nameIndexFrom? (name : String) : List String -> Nat -> Option Nat
  | [], _ => none
  | candidate :: rest, index =>
      if candidate == name then some index
      else nameIndexFrom? name rest (index + 1)

def nameIndex? (name : String) (scopeNames : List String) : Option Nat :=
  nameIndexFrom? name scopeNames 0

mutual

  /-- Source variables in left-to-right occurrence order. -/
  def termVariableOccurrences : SExpr -> List String
    | .atom token =>
        if sourceVariableToken token then [token] else []
    | .list elements => termsVariableOccurrences elements
  termination_by term => sizeOf term

  def termsVariableOccurrences : List SExpr -> List String
    | [] => []
    | term :: terms =>
        termVariableOccurrences term ++ termsVariableOccurrences terms
  termination_by terms => sizeOf terms

end

def rewriteVariableNames (rewrite : Rewrite) : List String :=
  (termVariableOccurrences rewrite.head ++
      termsVariableOccurrences rewrite.body) |> distinctNames

mutual

  /-- Decode one source pattern into the established Horn term carrier.
  Only the first-order source fragment is admitted. -/
  def elaborateTerm? (scopeNames : List String) : SExpr -> Option Term
    | .atom token =>
        if token.startsWith "?" then
          if sourceVariableToken token then
            match nameIndex? token scopeNames with
            | some identifier => some (.var identifier)
            | none => none
          else
            none
        else if token.startsWith "$" then none
        else if mayStartInteger token then
          match token.toInt? with
          | some value =>
              if toString value == token then some (.integer value) else none
          | none => some (.atom token)
        else
          some (.atom token)
    | .list (.atom constructor :: arguments) =>
        if constructor.startsWith "?" || constructor.startsWith "$" then none
        else
          return .app constructor (<- elaborateTerms? scopeNames arguments)
    | _ => none
  termination_by term => sizeOf term

  def elaborateTerms? (scopeNames : List String) :
      List SExpr -> Option Terms
    | [] => some .nil
    | term :: terms =>
        return .cons (<- elaborateTerm? scopeNames term)
          (<- elaborateTerms? scopeNames terms)
  termination_by terms => sizeOf terms

end

def elaborateAtom? (scopeNames : List String) : SExpr -> Option Atom
  | .list (.atom relation :: arguments) =>
      if relation.startsWith "?" || relation.startsWith "$" then none
      else
        return { relation, arguments := <- elaborateTerms? scopeNames arguments }
  | _ => none

def elaborateAtoms? (scopeNames : List String) (patterns : List SExpr) :
    Option (List Atom) :=
  patterns.mapM (elaborateAtom? scopeNames)

mutual

  def quoteTerm? (scopeNames : List String) : Term -> Option SExpr
    | .var identifier =>
        return .atom (<- scopeNames[identifier]?)
    | .atom name => some (.atom name)
    | .integer value => some (.atom (toString value))
    | .app constructor arguments =>
        return .list (.atom constructor :: (<- quoteTerms? scopeNames arguments))

  def quoteTerms? (scopeNames : List String) : Terms -> Option (List SExpr)
    | .nil => some []
    | .cons term terms =>
        return (<- quoteTerm? scopeNames term) ::
          (<- quoteTerms? scopeNames terms)

end

def quoteAtom? (scopeNames : List String) (atom : Atom) : Option SExpr := do
  let arguments <- quoteTerms? scopeNames atom.arguments
  some (.list (.atom atom.relation :: arguments))

def quoteAtoms? (scopeNames : List String) (atoms : List Atom) :
    Option (List SExpr) :=
  atoms.mapM (quoteAtom? scopeNames)

def quoteRule? (scopeNames : List String) (rule : Rule) : Option Rewrite := do
  let head <- quoteAtom? scopeNames rule.head
  let body <- quoteAtoms? scopeNames rule.body
  some { name := rule.name, head, body }

/-- Structural first-order elaboration before the exact re-quotation check.
This is public so source-specific qualification proofs can normalize authored
rules without duplicating the elaborator.  `elaborateRewrite?`, not this helper,
remains the admission boundary. -/
def elaborateRewriteCandidate? (rewrite : Rewrite) : Option ScopedRule := do
  let scopeNames := rewriteVariableNames rewrite
  let head <- elaborateAtom? scopeNames rewrite.head
  let body <- elaborateAtoms? scopeNames rewrite.body
  let rule : Rule := { name := rewrite.name, head, body }
  some (scopeNames, rule)

/-- Exact, fail-closed elaboration of one authored rule occurrence. -/
def elaborateRewrite? (rewrite : Rewrite) : Option ScopedRule :=
  match elaborateRewriteCandidate? rewrite with
  | none => none
  | some namedRule =>
      if quoteRule? namedRule.1 namedRule.2 = some rewrite then
        some namedRule
      else
        none

theorem quoteRule?_of_elaborateRewrite? {rewrite : Rewrite}
    {namedRule : ScopedRule}
    (accepted : elaborateRewrite? rewrite = some namedRule) :
    quoteRule? namedRule.1 namedRule.2 = some rewrite := by
  unfold elaborateRewrite? at accepted
  split at accepted <;> simp_all
  rcases accepted with ⟨quoted, rfl⟩
  exact quoted

theorem rule_name_of_elaborateRewrite? {rewrite : Rewrite}
    {namedRule : ScopedRule}
    (accepted : elaborateRewrite? rewrite = some namedRule) :
    namedRule.2.name = rewrite.name := by
  have quoted := quoteRule?_of_elaborateRewrite? accepted
  cases headEq : quoteAtom? namedRule.1 namedRule.2.head with
  | none => simp [quoteRule?, headEq] at quoted
  | some head =>
      cases bodyEq : quoteAtoms? namedRule.1 namedRule.2.body with
      | none => simp [quoteRule?, headEq, bodyEq] at quoted
      | some body =>
          simp [quoteRule?, headEq, bodyEq] at quoted
          exact congrArg Rewrite.name quoted

/-- Exact re-quotation exposes the authored head without traversing its
arguments or the rule body in a client proof. -/
theorem head_of_elaborateRewrite? {rewrite : Rewrite} {namedRule : ScopedRule}
    (accepted : elaborateRewrite? rewrite = some namedRule) :
    ∃ arguments, rewrite.head = .list (.atom namedRule.2.head.relation :: arguments) := by
  have quoted := quoteRule?_of_elaborateRewrite? accepted
  cases headEq : quoteAtom? namedRule.1 namedRule.2.head with
  | none => simp [quoteRule?, headEq] at quoted
  | some head =>
    cases bodyEq : quoteAtoms? namedRule.1 namedRule.2.body with
    | none => simp [quoteRule?, headEq, bodyEq] at quoted
    | some body =>
      have same : ({ name := namedRule.2.name, head, body } : Rewrite) = rewrite := by
        simpa [quoteRule?, headEq, bodyEq] using quoted
      cases argumentsEq : quoteTerms? namedRule.1 namedRule.2.head.arguments with
      | none => simp [quoteAtom?, argumentsEq] at headEq
      | some arguments =>
        have shape : .list (.atom namedRule.2.head.relation :: arguments) = head := by
          simpa [quoteAtom?, argumentsEq] using headEq
        exact ⟨arguments, (congrArg Rewrite.head same).symm.trans shape.symm⟩

def elaborateRewrites? (rewrites : List Rewrite) :
    Option (List ScopedRule) :=
  rewrites.mapM elaborateRewrite?

/-- Successful traversal preserves each source occurrence, not only names
and counts. This permits qualification of a selected row without reducing
unrelated rows again. -/
theorem elaborateRewrites?_getElem? {rewrites : List Rewrite}
    {namedRules : List ScopedRule}
    (accepted : elaborateRewrites? rewrites = some namedRules) (index : Nat) :
    namedRules[index]? = (rewrites[index]?).bind elaborateRewrite? := by
  induction rewrites generalizing namedRules index with
  | nil =>
    simp [elaborateRewrites?] at accepted
    subst namedRules
    simp
  | cons row rows ih =>
    cases first : elaborateRewrite? row with
    | none => simp [elaborateRewrites?, List.mapM_cons, first] at accepted
    | some result =>
      cases rest : List.mapM elaborateRewrite? rows with
      | none => simp [elaborateRewrites?, List.mapM_cons, first, rest] at accepted
      | some results =>
        have same : result :: results = namedRules := by
          simpa [elaborateRewrites?, List.mapM_cons, first, rest] using accepted
        subst namedRules
        cases index with
        | zero => simp [first]
        | succ index => exact ih rest index

@[simp] private theorem isSome_bind_some {α β : Type}
    (value : Option α) (transform : α -> β) :
    (value.bind (fun item => some (transform item))).isSome = value.isSome := by
  cases value <;> rfl

/-- Horn elaboration succeeds on an ordered concatenation exactly when it
succeeds on both source segments.  This permits large authored compositions to
be qualified source-by-source without changing rule order. -/
theorem elaborateRewrites?_append_isSome
    (left right : List Rewrite) :
    (elaborateRewrites? (left ++ right)).isSome =
      ((elaborateRewrites? left).isSome &&
        (elaborateRewrites? right).isSome) := by
  induction left with
  | nil => simp [elaborateRewrites?]
  | cons head tail induction =>
      simp only [List.cons_append, elaborateRewrites?, List.mapM_cons]
      cases accepted : elaborateRewrite? head <;>
        simp [elaborateRewrites?] at induction ⊢
      exact induction

theorem elaborateRewrites?_preserves_length {rewrites : List Rewrite}
    {namedRules : List ScopedRule}
    (accepted : elaborateRewrites? rewrites = some namedRules) :
    namedRules.length = rewrites.length := by
  induction rewrites generalizing namedRules with
  | nil => simp [elaborateRewrites?] at accepted; simp_all
  | cons rewrite rewrites induction =>
      cases ruleAccepted : elaborateRewrite? rewrite with
      | none => simp [elaborateRewrites?, List.mapM_cons, ruleAccepted] at accepted
      | some namedRule =>
          cases tailAccepted : List.mapM elaborateRewrite? rewrites with
          | none =>
              simp [elaborateRewrites?, List.mapM_cons, ruleAccepted,
                tailAccepted] at accepted
          | some tail =>
              simp [elaborateRewrites?, List.mapM_cons, ruleAccepted,
                tailAccepted] at accepted
              subst namedRules
              have tailLength := induction (by
                simpa [elaborateRewrites?] using tailAccepted)
              simp [tailLength]

theorem elaborateRewrites?_preserves_names {rewrites : List Rewrite}
    {namedRules : List ScopedRule}
    (accepted : elaborateRewrites? rewrites = some namedRules) :
    namedRules.map (fun namedRule => namedRule.2.name) =
      rewrites.map Rewrite.name := by
  induction rewrites generalizing namedRules with
  | nil => simp [elaborateRewrites?] at accepted; simp_all
  | cons rewrite rewrites induction =>
      cases ruleAccepted : elaborateRewrite? rewrite with
      | none => simp [elaborateRewrites?, List.mapM_cons, ruleAccepted] at accepted
      | some namedRule =>
          cases tailAccepted : List.mapM elaborateRewrite? rewrites with
          | none =>
              simp [elaborateRewrites?, List.mapM_cons, ruleAccepted,
                tailAccepted] at accepted
          | some tail =>
              simp [elaborateRewrites?, List.mapM_cons, ruleAccepted,
                tailAccepted] at accepted
              subst namedRules
              have tailNames := induction (by
                simpa [elaborateRewrites?] using tailAccepted)
              simp [rule_name_of_elaborateRewrite? ruleAccepted, tailNames]

/-- A source with authored equational congruence is not silently reclassified
as a definite-clause program. -/
def elaborateSource? (source : Source) : Option (List ScopedRule) :=
  if source.equations.isEmpty then elaborateRewrites? source.rewrites else none

def compositionRewrites (sources : List Source) : List Rewrite :=
  sources.flatMap Source.rewrites

/-- Elaborate only a closed, structurally admitted source composition. -/
def elaborateComposition? (sources : List Source) :
    Option (List ScopedRule) :=
  if compositionValid sources && sources.all (fun source => source.equations.isEmpty) then
    elaborateRewrites? (compositionRewrites sources)
  else
    none

def programOf (rules : List ScopedRule) : Program :=
  rules.map Prod.snd

def elaborateProgram? (sources : List Source) : Option Program :=
  programOf <$> elaborateComposition? sources

theorem elaborateProgram?_getElem? {sources : List Source} {program : Program}
    (accepted : elaborateProgram? sources = some program) (index : Nat) :
    program[index]? = ((compositionRewrites sources)[index]?).bind
      (fun row => (elaborateRewrite? row).map Prod.snd) := by
  unfold elaborateProgram? elaborateComposition? at accepted
  split at accepted
  next guard =>
    cases compiled : elaborateRewrites? (compositionRewrites sources) with
    | none => simp [compiled] at accepted
    | some namedRules =>
      have same : programOf namedRules = program := by simpa [compiled] using accepted
      subst program
      rw [programOf, List.getElem?_map, elaborateRewrites?_getElem? compiled]
      cases selected : (compositionRewrites sources)[index]? <;> simp
  next guard => simp at accepted

/-- The compiled head and name belong to the very same authored occurrence.
This result uses accepted elaboration; it does not trust a separately supplied
inventory of rule heads. -/
theorem elaborateProgram?_getElem?_head {sources : List Source} {program : Program}
    (accepted : elaborateProgram? sources = some program) {index : Nat} {rule : Rule}
    (selected : program[index]? = some rule) :
    ∃ row arguments, (compositionRewrites sources)[index]? = some row ∧
      rule.name = row.name ∧ row.head = .list (.atom rule.head.relation :: arguments) := by
  have lookup := elaborateProgram?_getElem? accepted index
  rw [selected] at lookup
  cases sourceAt : (compositionRewrites sources)[index]? with
  | none => simp [sourceAt] at lookup
  | some row =>
    cases elaborated : elaborateRewrite? row with
    | none => simp [sourceAt, elaborated] at lookup
    | some namedRule =>
      have same : rule = namedRule.2 := by simpa [sourceAt, elaborated] using lookup
      subst rule
      obtain ⟨arguments, shape⟩ := head_of_elaborateRewrite? elaborated
      exact ⟨row, arguments, rfl, rule_name_of_elaborateRewrite? elaborated, shape⟩

/-- Equational congruence is rejected at the composition boundary as well as
at the single-source boundary. -/
theorem elaborateProgram?_refuses_equations {sources : List Source}
    (nonempty : ∃ source ∈ sources, source.equations ≠ []) :
    elaborateProgram? sources = none := by
  have guard : sources.all (fun source => source.equations.isEmpty) = false := by
    obtain ⟨source, member, nonempty⟩ := nonempty
    apply Bool.eq_false_iff.mpr
    intro h
    have empty := List.all_eq_true.mp h source member
    exact nonempty (List.isEmpty_iff.mp empty)
  simp [elaborateProgram?, elaborateComposition?, guard]

theorem elaborateProgram?_equations_empty {sources : List Source}
    {program : Program} (accepted : elaborateProgram? sources = some program)
    {source : Source} (member : source ∈ sources) :
    source.equations = [] := by
  by_contra nonempty
  have refused := elaborateProgram?_refuses_equations ⟨source, member, nonempty⟩
  rw [refused] at accepted
  cases accepted

theorem elaborateComposition?_preserves_length {sources : List Source}
    {namedRules : List ScopedRule}
    (accepted : elaborateComposition? sources = some namedRules) :
    namedRules.length = (compositionRewrites sources).length := by
  unfold elaborateComposition? at accepted
  split at accepted <;> try contradiction
  exact elaborateRewrites?_preserves_length accepted

theorem elaborateComposition?_preserves_names {sources : List Source}
    {namedRules : List ScopedRule}
    (accepted : elaborateComposition? sources = some namedRules) :
    namedRules.map (fun namedRule => namedRule.2.name) =
      (compositionRewrites sources).map Rewrite.name := by
  unfold elaborateComposition? at accepted
  split at accepted <;> try contradiction
  exact elaborateRewrites?_preserves_names accepted

theorem elaborateProgram?_preserves_length {sources : List Source}
    {program : Program}
    (accepted : elaborateProgram? sources = some program) :
    program.length = (compositionRewrites sources).length := by
  unfold elaborateProgram? at accepted
  cases rulesAccepted : elaborateComposition? sources with
  | none => simp [rulesAccepted] at accepted
  | some namedRules =>
      simp [rulesAccepted] at accepted
      subst program
      simpa [programOf] using
        elaborateComposition?_preserves_length rulesAccepted

theorem elaborateProgram?_preserves_names {sources : List Source}
    {program : Program}
    (accepted : elaborateProgram? sources = some program) :
    program.map Rule.name =
      (compositionRewrites sources).map Rewrite.name := by
  unfold elaborateProgram? at accepted
  cases rulesAccepted : elaborateComposition? sources with
  | none => simp [rulesAccepted] at accepted
  | some namedRules =>
      simp [rulesAccepted] at accepted
      subst program
      simpa [programOf, List.map_map, Function.comp_def] using
        elaborateComposition?_preserves_names rulesAccepted

/-- A complete source-head inventory can be computed without elaborating
the bodies again. The inline structural inspector is definitionally the
`sourceRelation?` used by downstream source-boundary checks. -/
theorem elaborateProgram?_getElem?_head_relation {sources : List Source} {program : Program}
    (accepted : elaborateProgram? sources = some program) (index : Nat) :
    (program[index]?).map (fun rule => rule.head.relation) =
      ((compositionRewrites sources)[index]?).bind (fun row =>
        match row.head with
        | .list (.atom relation :: _) => some relation
        | _ => none) := by
  cases selected : program[index]? with
  | none =>
    have past : program.length ≤ index := List.getElem?_eq_none_iff.mp selected
    have absent : (compositionRewrites sources)[index]? = none :=
      List.getElem?_eq_none (by rwa [← elaborateProgram?_preserves_length accepted])
    simp [absent]
  | some rule =>
    obtain ⟨row, arguments, sourceAt, _, shape⟩ :=
      elaborateProgram?_getElem?_head accepted selected
    simp [sourceAt, shape]

/-! ## Discriminating controls -/

theorem named_head_with_variable_argument_elaborates :
    elaborateRewrite?
      { name := "named-head"
        head := .list [.atom "result", .atom "?value"]
        body := [.list [.atom "premise", .atom "?value"]] } =
      some (["?value"],
        { name := "named-head"
          head := ⟨"result", .cons (.var 0) .nil⟩
          body := [⟨"premise", .cons (.var 0) .nil⟩] }) := by
  decide +kernel

/-- Reading a recognizable head is not an admission certificate: every body
must still pass the full source elaborator. -/
theorem visible_head_does_not_admit_malformed_body :
    let row : Rewrite :=
      { name := "malformed-body"
        head := .list [.atom "result"]
        body := [.atom "not-a-relation-application"] }
    (match row.head with
      | .list (.atom relation :: _) => some relation
      | _ => none) = some "result" ∧ elaborateRewrite? row = none := by
  decide +kernel

/-- Host variables are not source Horn metavariables. -/
theorem host_variable_is_refused :
    elaborateTerm? [] (.atom "$x") = none := by
  simp [elaborateTerm?]

/-- Negative: source equations cannot masquerade as Horn clauses. -/
theorem equation_source_is_refused :
    elaborateSource?
      { name := "equational"
        operators := []
        equations := [.atom "equation"]
        rewrites := [] } = none := by
  rfl

/-- An empty source list has no first-order constructor head. -/
theorem empty_expression_is_refused :
    elaborateTerm? [] (.list []) = none := by
  simp [elaborateTerm?]

theorem ordinary_symbol_does_not_enter_integer_parser :
    elaborateTerm? [] (.atom "BNFDefinitionsNilV1") =
      some (.atom "BNFDefinitionsNilV1") := by
  decide +kernel

theorem nullary_application_elaborates_as_application :
    elaborateTerm? [] (.list [.atom "bnf-v1:suffix-start"]) =
      some (.app "bnf-v1:suffix-start" .nil) := by
  decide +kernel

theorem nullary_application_does_not_elaborate_as_atom :
    elaborateTerm? [] (.list [.atom "bnf-v1:suffix-start"]) ≠
      elaborateTerm? [] (.atom "bnf-v1:suffix-start") := by
  decide +kernel

theorem source_atom_and_nullary_application_requote_distinctly (name : String) :
    quoteTerm? [] (.atom name) ≠ quoteTerm? [] (.app name .nil) := by
  simp [quoteTerm?, quoteTerms?]

theorem equational_composition_is_refused :
    elaborateProgram?
      [{ name := "equational", operators := [],
         equations := [.atom "equation"], rewrites := [] }] = none := by
  apply elaborateProgram?_refuses_equations
  exact ⟨⟨"equational", [], [.atom "equation"], []⟩, by simp, by simp⟩

theorem distinctNames_retains_first_occurrence_order :
    distinctNames ["?left", "?right", "?left", "?third", "?right"] =
      ["?left", "?right", "?third"] := by
  decide +kernel

theorem nameIndex_selects_first_position :
    nameIndex? "?right" ["?left", "?right", "?third"] = some 1 := by
  decide +kernel

#print axioms quoteRule?_of_elaborateRewrite?
#print axioms rule_name_of_elaborateRewrite?
#print axioms head_of_elaborateRewrite?
#print axioms elaborateProgram?_getElem?_head
#print axioms elaborateProgram?_getElem?_head_relation
#print axioms elaborateRewrites?_preserves_length
#print axioms elaborateRewrites?_append_isSome
#print axioms elaborateRewrites?_preserves_names
#print axioms elaborateProgram?_preserves_length
#print axioms elaborateProgram?_preserves_names
#print axioms elaborateProgram?_refuses_equations
#print axioms elaborateProgram?_equations_empty
#print axioms nullary_application_elaborates_as_application
#print axioms nullary_application_does_not_elaborate_as_atom
#print axioms equational_composition_is_refused
#print axioms host_variable_is_refused
#print axioms equation_source_is_refused
#print axioms empty_expression_is_refused
#print axioms ordinary_symbol_does_not_enter_integer_parser
#print axioms distinctNames_retains_first_occurrence_order
#print axioms nameIndex_selects_first_position

end Mettapedia.GSLT.Parsing.CanonicalSourceHornElaboration
