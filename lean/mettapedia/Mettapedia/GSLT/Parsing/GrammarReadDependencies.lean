import Mettapedia.GSLT.Parsing.BoundedScheduler
import Mettapedia.Machines.ReadOnlyQuery

/-!
# Complete grammar dependencies of bounded parsing

The existing exhaustive scheduler is lifted to adaptive reads of complete
category rule lists. Reads include empty categories and lookahead calls.
Erasing the reads gives the original scheduler's exact ordered candidates,
with their certificates; no ambiguity or duplicate occurrence is discarded.

The input and nesting budget are fixed query parameters. This is a dependency
theorem for the guarded compiled grammar, not a lexer, a Lean front end, or a
native compiler correctness claim. An empty bounded result is not an
unbounded rejection.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GrammarReadDependencies

open CompilerCorrespondence (Category Codepoint CompiledSymbol)
open GuardCorrespondence (CompiledGrammar CompiledProduction CompiledGuard)
open BoundedScheduler (Candidate BodyCandidate)
open Mettapedia.Machines

abbrev Query (Answer : Type) := ReadOnlyQuery.Program Category (List CompiledProduction) Answer

/-- A read returns all rules for the category, including their order. -/
def catalogue (grammar : CompiledGrammar) (category : Category) : List CompiledProduction :=
  grammar.productions.filter fun production => production.category == category

def mapQuery {A B : Type} (f : A → B) (query : Query A) : Query B :=
  ReadOnlyQuery.bind query fun value => .pure (f value)

def collect {A B : Type} (items : List A) (query : A → Query (List B)) : Query (List B) :=
  match items with
  | [] => .pure []
  | item :: rest => ReadOnlyQuery.bind (query item) fun first =>
      ReadOnlyQuery.bind (collect rest query) fun tail => .pure (first ++ tail)

@[simp] theorem mapQuery_answer {A B : Type} (store : Category → List CompiledProduction)
    (f : A → B) (query : Query A) :
    (ReadOnlyQuery.run store (mapQuery f query)).answer = f (ReadOnlyQuery.run store query).answer := by
  simp [mapQuery, ReadOnlyQuery.run_bind, ReadOnlyQuery.run]

@[simp] theorem collect_answer {A B : Type} (store : Category → List CompiledProduction)
    (items : List A) (query : A → Query (List B)) :
    (ReadOnlyQuery.run store (collect items query)).answer =
      items.flatMap (fun item => (ReadOnlyQuery.run store (query item)).answer) := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp [collect, ReadOnlyQuery.run_bind, ReadOnlyQuery.run, ih]

def body (recurse : Category → Nat → Query (List Candidate))
    (input : List Codepoint) : List CompiledSymbol → Nat → Query (List BodyCandidate)
  | [], cursor => .pure [{ stop := cursor, certificates := [], trees := [] }]
  | .terminal codepoint :: symbols, start =>
      if input[start]? = some codepoint then
        mapQuery (List.map fun rest =>
          { stop := rest.stop
            certificates := .terminal codepoint start (start + 1) :: rest.certificates
            trees := .terminal codepoint :: rest.trees })
          (body recurse input symbols (start + 1))
      else .pure []
  | .anyTerminal :: symbols, start =>
      match input[start]? with
      | none => .pure []
      | some codepoint =>
          mapQuery (List.map fun rest =>
            { stop := rest.stop
              certificates := .terminal codepoint start (start + 1) :: rest.certificates
              trees := .terminal codepoint :: rest.trees })
            (body recurse input symbols (start + 1))
  | .oneOfTerminal codepoints :: symbols, start =>
      match input[start]? with
      | none => .pure []
      | some codepoint =>
          if codepoint ∈ codepoints then
            mapQuery (List.map fun rest =>
              { stop := rest.stop
                certificates := .terminal codepoint start (start + 1) :: rest.certificates
                trees := .terminal codepoint :: rest.trees })
              (body recurse input symbols (start + 1))
          else .pure []
  | .nonterminal category :: symbols, start =>
      ReadOnlyQuery.bind (recurse category start) fun heads =>
        collect heads fun head =>
          mapQuery (List.map fun rest =>
            { stop := rest.stop
              certificates := head.certificate :: rest.certificates
              trees := head.tree :: rest.trees })
            (body recurse input symbols head.stop)

def guards (recurse : Category → Nat → Query (List Candidate))
    (input : List Codepoint) : List CompiledGuard → Nat → Query Bool
  | [], _ => .pure true
  | .atEnd :: rest, cursor =>
      mapQuery (fun passed => decide (cursor = input.length) && passed)
        (guards recurse input rest cursor)
  | .nextIn codepoints allowEof :: rest, cursor =>
      match input[cursor]? with
      | some codepoint =>
          mapQuery (fun passed => decide (codepoint ∈ codepoints) && passed)
            (guards recurse input rest cursor)
      | none =>
          mapQuery (fun passed => allowEof && decide (cursor = input.length) && passed)
            (guards recurse input rest cursor)
  | .lookahead category :: rest, cursor =>
      ReadOnlyQuery.bind (recurse category cursor) fun found =>
        mapQuery (fun passed => !found.isEmpty && passed)
          (guards recurse input rest cursor)

def category (input : List Codepoint) : Nat → Category → Nat → Query (List Candidate)
  | 0, _, _ => .pure []
  | fuel + 1, name, start =>
      .read name fun productions =>
        collect productions fun production =>
          ReadOnlyQuery.bind (body (category input fuel) input production.symbols start) fun bodies =>
            collect bodies fun parsed =>
              mapQuery (fun passed => if passed then
                [{ stop := parsed.stop
                   certificate := .node production.sourceRule production.category
                     start parsed.stop parsed.certificates
                   tree := .node production.sourceRule production.category parsed.trees }]
                else [])
                (guards (category input fuel) input production.guards parsed.stop)

def root (input : List Codepoint) (fuel : Nat) (start : Category) : Query (List Candidate) :=
  mapQuery (List.filter fun parsed => decide (parsed.stop = input.length))
    (category input fuel start 0)

theorem body_answer (store : Category → List CompiledProduction)
    (recurse : Category → Nat → Query (List Candidate))
    (input : List Codepoint) (symbols : List CompiledSymbol) (start : Nat) :
    (ReadOnlyQuery.run store (body recurse input symbols start)).answer =
      BoundedScheduler.scheduleBody (fun name cursor => (ReadOnlyQuery.run store (recurse name cursor)).answer)
        input symbols start := by
  induction symbols generalizing start with
  | nil => rfl
  | cons symbol symbols ih =>
      cases symbol with
      | terminal codepoint =>
          simp only [body, BoundedScheduler.scheduleBody]
          split <;> simp [ih, ReadOnlyQuery.run]
      | anyTerminal =>
          cases h : input[start]? <;> simp [body, BoundedScheduler.scheduleBody, h, ih, ReadOnlyQuery.run]
      | oneOfTerminal codepoints =>
          cases h : input[start]? with
          | none => simp [body, BoundedScheduler.scheduleBody, h, ReadOnlyQuery.run]
          | some codepoint =>
              by_cases member : codepoint ∈ codepoints <;>
                simp [body, BoundedScheduler.scheduleBody, h, member, ih, ReadOnlyQuery.run]
      | nonterminal name =>
          simp [body, BoundedScheduler.scheduleBody, ReadOnlyQuery.run_bind, ih]

theorem guards_answer (store : Category → List CompiledProduction)
    (recurse : Category → Nat → Query (List Candidate))
    (input : List Codepoint) (conditions : List CompiledGuard) (cursor : Nat) :
    (ReadOnlyQuery.run store (guards recurse input conditions cursor)).answer =
      BoundedScheduler.guardsPass (fun name position => (ReadOnlyQuery.run store (recurse name position)).answer)
        input conditions cursor := by
  induction conditions with
  | nil => rfl
  | cons condition rest ih =>
      cases condition with
      | atEnd => simp [guards, BoundedScheduler.guardsPass, ih]
      | nextIn codepoints allowEof =>
          cases h : input[cursor]? <;> simp [guards, BoundedScheduler.guardsPass, h, ih]
      | lookahead name => simp [guards, BoundedScheduler.guardsPass, ReadOnlyQuery.run_bind, ih]

private theorem filter_flatMap {A B : Type} (items : List A) (test : A → Bool) (f : A → List B) :
    (items.filter test).flatMap f = items.flatMap (fun item => if test item then f item else []) := by
  induction items with
  | nil => rfl
  | cons item rest ih => cases h : test item <;> simp [h, ih]

/-- A different execution program with category reads gives the existing
scheduler's exact ordered result, rather than only its set of trees. -/
theorem category_answer (grammar : CompiledGrammar) (input : List Codepoint)
    (fuel : Nat) (name : Category) (start : Nat) :
    (ReadOnlyQuery.run (catalogue grammar) (category input fuel name start)).answer =
      BoundedScheduler.scheduleCategory grammar input fuel name start := by
  induction fuel generalizing name start with
  | zero => rfl
  | succ fuel ih =>
      have recursive : (fun name cursor =>
          (ReadOnlyQuery.run (catalogue grammar) (category input fuel name cursor)).answer) =
          BoundedScheduler.scheduleCategory grammar input fuel := by
        funext name cursor
        exact ih name cursor
      simp only [category, ReadOnlyQuery.run, collect_answer, ReadOnlyQuery.run_bind, mapQuery_answer]
      simp only [body_answer, guards_answer, recursive]
      rw [catalogue, filter_flatMap]
      simp [BoundedScheduler.scheduleCategory]

theorem root_answer (grammar : CompiledGrammar) (input : List Codepoint) (fuel : Nat) :
    (ReadOnlyQuery.run (catalogue grammar) (root input fuel grammar.start)).answer =
      BoundedScheduler.scheduleRoot grammar input fuel := by
  simp [root, category_answer, BoundedScheduler.scheduleRoot]

/-- The validator reads only the old dependency list; it does not parse again.
The root belongs to the query's identity, independently of category contents. -/
def validates (before after : CompiledGrammar) (input : List Codepoint) (fuel : Nat) : Bool :=
  decide (after.start = before.start) &&
    ReadOnlyQuery.checkReads (catalogue after)
      (ReadOnlyQuery.run (catalogue before) (root input fuel before.start)).reads

/-- Validation preserves the whole candidate list: order, duplicates,
spans, parse trees and replay certificates. -/
theorem validated_candidates {before after : CompiledGrammar}
    {input : List Codepoint} {fuel : Nat}
    (valid : validates before after input fuel = true) :
    BoundedScheduler.scheduleRoot after input fuel =
      BoundedScheduler.scheduleRoot before input fuel := by
  simp only [validates, Bool.and_eq_true, decide_eq_true_eq] at valid
  have same := ReadOnlyQuery.validated_answer (catalogue before) (catalogue after)
    (root input fuel before.start) valid.2
  rw [← valid.1, root_answer] at same
  rw [valid.1, root_answer] at same
  exact same

/-- The existing packed forest is preserved without selecting one parse. -/
theorem validated_forest {before after : CompiledGrammar}
    {input : List Codepoint} {fuel : Nat}
    (valid : validates before after input fuel = true) :
    BoundedScheduler.scheduleForest after input fuel =
      BoundedScheduler.scheduleForest before input fuel := by
  simp only [BoundedScheduler.scheduleForest, validated_candidates valid]

/-- Reuse preserves the independently defined bounded derivation relation,
not merely agreement of two cache routines. -/
theorem validated_derivations {before after : CompiledGrammar}
    {input : List Codepoint} {fuel : Nat}
    (valid : validates before after input fuel = true) :
    BoundedScheduler.boundedResults after input fuel =
      BoundedScheduler.boundedResults before input fuel := by
  rw [← BoundedScheduler.bounded_result_set_agreement,
    ← BoundedScheduler.bounded_result_set_agreement]
  simp only [BoundedScheduler.scheduledResults, validated_candidates valid]

theorem validated_ambiguity {before after : CompiledGrammar}
    {input : List Codepoint} {fuel : Nat}
    (valid : validates before after input fuel = true) :
    BoundedScheduler.Ambiguous (BoundedScheduler.boundedResults after input fuel) ↔
      BoundedScheduler.Ambiguous (BoundedScheduler.boundedResults before input fuel) := by
  rw [validated_derivations valid]

/-- Unbounded preservation requires agreement at every nesting depth. A
single finite certificate is deliberately not claimed to establish it. -/
theorem validated_all_depths {before after : CompiledGrammar}
    {input : List Codepoint}
    (valid : ∀ fuel, validates before after input fuel = true) :
    GuardCorrespondence.grammarResults after input =
      GuardCorrespondence.grammarResults before input := by
  ext tree
  constructor
  · intro derivation
    obtain ⟨fuel, bounded⟩ := BoundedScheduler.compiledDerivation_hasBound derivation
    have member : tree ∈ BoundedScheduler.boundedResults after input fuel := bounded
    rw [validated_derivations (valid fuel)] at member
    exact BoundedScheduler.eraseDerivation member
  · intro derivation
    obtain ⟨fuel, bounded⟩ := BoundedScheduler.compiledDerivation_hasBound derivation
    have member : tree ∈ BoundedScheduler.boundedResults before input fuel := bounded
    rw [← validated_derivations (valid fuel)] at member
    exact BoundedScheduler.eraseDerivation member

/-- Appending declarations for categories that were never read is safe.
This is a syntactic update criterion, including negative and lookahead reads. -/
theorem append_unread_validates (before : CompiledGrammar)
    (extra : List CompiledProduction) (input : List Codepoint) (fuel : Nat)
    (untouched : ∀ observed ∈
      (ReadOnlyQuery.run (catalogue before) (root input fuel before.start)).reads,
      ∀ production ∈ extra, production.category ≠ observed.1) :
    validates before { before with productions := before.productions ++ extra } input fuel = true := by
  simp only [validates, decide_true, Bool.true_and]
  apply (ReadOnlyQuery.checkReads_iff _ _).mpr
  intro observed member
  have none : extra.filter (fun production => production.category == observed.1) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro production present
    simp [untouched observed member production present]
  have agreed := ReadOnlyQuery.run_agrees (catalogue before)
    (root input fuel before.start) observed member
  simpa [catalogue, List.filter_append, none] using agreed

end Mettapedia.GSLT.Parsing.GrammarReadDependencies
