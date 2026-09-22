import Mettapedia.GSLT.Parsing.PlainBnfGraphNameTrie
import Mettapedia.GSLT.Parsing.PlainBnfDeclarationAccumulator

/-!
# Sparse-trie declaration collection with exact ordered observations

The finite algorithm follows the discovery source's collection clauses:
first expression/span payloads are indexed; definitions are pushed onto a
private reversed list; duplicate diagnostics are emitted in source order.
The output is compared with the existing independent declaration semantics.

Only decidable equality of name components is used, including signed Integer
components in structured edits. Natural-number names remain the default.

This is an algorithm refinement, not a proof that authored clauses or their
generated PeTTa realization execute it. No new grammar carrier is introduced.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfTrieDeclarationCollector

open PlainBnfDeclarationSemantics

abbrev Name (Scalar : Type := Nat) := List Scalar

universe uE uS uT
variable {Expression : Type uE} {Span : Type uS} {Text : Type uT}
variable {Scalar : Type} [DecidableEq Scalar]

abbrev Index (Expression : Type uE) (Span : Type uS) (Scalar : Type := Nat) :=
  PlainBnfGraphNameTrie.Trie (Expression × Span) Scalar

def payload : LookupResult Expression Span → Option (Expression × Span)
  | .missing => none
  | .found expression span => some (expression, span)

def Represents (index : Index Expression Span Scalar)
    (definitions : List (Definition (Name Scalar) Expression Span)) : Prop :=
  ∀ name, PlainBnfGraphNameTrie.lookup name index = payload (lookup name definitions)

theorem represents_empty : Represents (.empty : Index Expression Span Scalar) [] := by
  intro name
  simp [PlainBnfGraphNameTrie.lookup_empty, lookup, payload]

theorem represents_append {index : Index Expression Span Scalar}
    {definitions : List (Definition (Name Scalar) Expression Span)}
    (represents : Represents index definitions) (definition : Definition (Name Scalar) Expression Span) :
    Represents (PlainBnfGraphNameTrie.insertFirst definition.name
      (definition.expression, definition.span) index) (definitions ++ [definition]) := by
  intro name
  unfold Represents at represents
  simp only [PlainBnfGraphNameTrie.lookup_insertFirst, represents,
    PlainBnfDeclarationAccumulator.lookup_append]
  by_cases same : name = definition.name
  · subst name
    cases lookup definition.name definitions <;> simp [lookup, payload]
  · cases lookup name definitions <;> simp [lookup, payload, same]

omit [DecidableEq Scalar] in
/-- The source's two reverse-definition clauses are the existing reverseAux
algorithm, including its arbitrary output-tail argument. -/
theorem reverse_definitions_observation (reversed before : List (Definition (Name Scalar) Expression Span)) :
    List.reverseAux reversed before = reversed.reverse ++ before := List.reverseAux_eq

def collectLoop : List (Entry (Name Scalar) Expression Span Text) → Index Expression Span Scalar →
    List (Definition (Name Scalar) Expression Span) →
    (List (Definition (Name Scalar) Expression Span) × List (Diagnostic (Name Scalar) Span)) × Index Expression Span Scalar
  | [], index, reversed => ((List.reverseAux reversed [], []), index)
  | .comment _ _ :: tail, index, reversed => collectLoop tail index reversed
  | .blank _ :: tail, index, reversed => collectLoop tail index reversed
  | .rule name expression span :: tail, index, reversed =>
      match PlainBnfGraphNameTrie.lookup name index with
      | none => collectLoop tail (PlainBnfGraphNameTrie.insertFirst name (expression, span) index)
          (⟨name, expression, span⟩ :: reversed)
      | some (_, firstSpan) =>
          let rest := collectLoop tail index reversed
          ((rest.1.1, .duplicate name firstSpan span :: rest.1.2), rest.2)

/-- Every output entry and diagnostic occurrence agrees, while the returned
index still stores the first complete expression/span for every known name. -/
theorem collectLoop_exact (entries : List (Entry (Name Scalar) Expression Span Text))
    (index : Index Expression Span Scalar) (reversed : List (Definition (Name Scalar) Expression Span))
    (represents : Represents index reversed.reverse) :
    (collectLoop entries index reversed).1 = collect entries reversed.reverse ∧
      Represents (collectLoop entries index reversed).2 (collectLoop entries index reversed).1.1 := by
  induction entries generalizing index reversed with
  | nil =>
      constructor
      · simp [collectLoop, collect]
      · simpa [collectLoop] using represents
  | cons entry tail ih =>
      cases entry with
      | comment text span => exact ih index reversed represents
      | blank span => exact ih index reversed represents
      | rule name expression span =>
          have query := represents name
          cases found : lookup name reversed.reverse with
          | missing =>
              simp only [found, payload] at query
              have next := represents_append represents
                (⟨name, expression, span⟩ : Definition (Name Scalar) Expression Span)
              rw [← List.reverse_cons] at next
              have result := ih _ _ next
              simpa [collectLoop, query, collect, found, definitionStep, List.reverse_cons] using result
          | found firstExpression firstSpan =>
              simp only [found, payload] at query
              have result := ih index reversed represents
              constructor
              · have observed := congrArg
                  (fun output => (output.1, Diagnostic.duplicate name firstSpan span :: output.2)) result.1
                simpa [collectLoop, query, collect, found, definitionStep] using observed
              · simpa [collectLoop, query] using result.2

def collectIndexed (entries : List (Entry (Name Scalar) Expression Span Text)) :
    (List (Definition (Name Scalar) Expression Span) × List (Diagnostic (Name Scalar) Span)) × Index Expression Span Scalar :=
  collectLoop entries .empty []

/-- No supplied index-correctness assumption: the actual empty index starts
the invariant, and each executed insertion preserves it. -/
theorem collectIndexed_eq (entries : List (Entry (Name Scalar) Expression Span Text)) :
    (collectIndexed entries).1 = collect entries [] :=
  (collectLoop_exact entries .empty [] represents_empty).1

theorem collectIndexed_index (entries : List (Entry (Name Scalar) Expression Span Text)) :
    Represents (collectIndexed entries).2 (collectIndexed entries).1.1 :=
  (collectLoop_exact entries .empty [] represents_empty).2

theorem collectIndexed_lookup (entries : List (Entry (Name Scalar) Expression Span Text)) (name : Name Scalar) :
    PlainBnfGraphNameTrie.lookup name (collectIndexed entries).2 =
      payload (lookup name (collect entries []).1) := by
  have indexed := collectIndexed_index entries name
  rwa [collectIndexed_eq] at indexed

theorem comments_and_blanks_preserve_outputs (text : Text) (commentSpan blankSpan : Span)
    (entries : List (Entry (Name Scalar) Expression Span Text)) :
    collectIndexed (.comment text commentSpan :: .blank blankSpan :: entries) =
      collectIndexed entries := rfl

theorem first_complete_definition_and_order (name : Name Scalar) (firstExpression : Expression)
    (firstSpan : Span) (text : Text) (commentSpan blankSpan : Span)
    (laterExpression : Expression) (laterSpan lastSpan : Span) :
    (collectIndexed [.rule name firstExpression firstSpan, .comment text commentSpan,
      .blank blankSpan, .rule name laterExpression laterSpan,
      .rule name laterExpression lastSpan]).1 =
      ([⟨name, firstExpression, firstSpan⟩],
        [.duplicate name firstSpan laterSpan, .duplicate name firstSpan lastSpan]) := by
  rw [collectIndexed_eq]
  exact collect_first_declaration_retained _ _ _ _ _ _ _ _ _ _

theorem first_complete_payload_in_index (name : Name Scalar) (firstExpression laterExpression : Expression)
    (firstSpan laterSpan : Span) :
    PlainBnfGraphNameTrie.lookup name
      (collectIndexed (Text := Text)
        [.rule name firstExpression firstSpan, .rule name laterExpression laterSpan]).2 =
      some (firstExpression, firstSpan) := by
  rw [collectIndexed_lookup]
  simp [collect, lookup, definitionStep, payload]

theorem identical_diagnostic_occurrences (name : Name Scalar) (firstExpression expression : Expression)
    (firstSpan duplicateSpan : Span) :
    (collectIndexed (Text := Text) [.rule name firstExpression firstSpan,
      .rule name expression duplicateSpan, .rule name expression duplicateSpan]).1 =
      ([⟨name, firstExpression, firstSpan⟩],
        [.duplicate name firstSpan duplicateSpan, .duplicate name firstSpan duplicateSpan]) := by
  rw [collectIndexed_eq]
  simp [collect, lookup, definitionStep]

theorem two_diagnostic_occurrences_are_not_one (name : Name Scalar) (firstExpression expression : Expression)
    (firstSpan duplicateSpan : Span) :
    (collectIndexed (Text := Text) [.rule name firstExpression firstSpan,
      .rule name expression duplicateSpan, .rule name expression duplicateSpan]).1.2 ≠
      [.duplicate name firstSpan duplicateSpan] := by
  rw [identical_diagnostic_occurrences]
  intro same
  have lengths := congrArg List.length same
  simp at lengths

theorem source_order_not_private_accumulator_order (firstName secondName : Name Scalar)
    (firstExpression secondExpression : Expression) (firstSpan secondSpan : Span)
    (different : firstName ≠ secondName) :
    (collectIndexed (Text := Text)
      [.rule firstName firstExpression firstSpan, .rule secondName secondExpression secondSpan]).1 =
      ([⟨firstName, firstExpression, firstSpan⟩, ⟨secondName, secondExpression, secondSpan⟩], []) := by
  rw [collectIndexed_eq]
  simp [collect, lookup, definitionStep, Ne.symm different]

omit [DecidableEq Scalar] in
theorem omitting_final_reverse_changes_order (firstName secondName : Name Scalar)
    (firstExpression secondExpression : Expression) (firstSpan secondSpan : Span)
    (different : firstName ≠ secondName) :
    List.reverseAux
      [⟨secondName, secondExpression, secondSpan⟩, ⟨firstName, firstExpression, firstSpan⟩]
      ([] : List (Definition (Name Scalar) Expression Span)) ≠
      [⟨secondName, secondExpression, secondSpan⟩, ⟨firstName, firstExpression, firstSpan⟩] := by
  intro same
  exact different (congrArg Definition.name (List.cons.inj same).1)

theorem wrong_first_span_breaks_index_representation (name : Name Scalar) (expression : Expression)
    (firstSpan wrongSpan : Span) (different : firstSpan ≠ wrongSpan) :
    ¬ Represents (PlainBnfGraphNameTrie.insertFirst name (expression, wrongSpan) .empty)
      [⟨name, expression, firstSpan⟩] := by
  intro represents
  have wrong := represents name
  simp [PlainBnfGraphNameTrie.lookup_inserted, lookup, payload] at wrong
  exact different wrong.symm

/-- A structured edit may contain signed name components and signed origin
integers. Collection preserves both, including equal duplicate occurrences. -/
theorem signed_keys_origins_and_duplicate_occurrences :
    let entries : List (Entry (Name Int) String Int String) :=
      [.rule [-1] "first" (-7), .rule [1] "other" 4,
       .rule [-1] "later" (-3), .rule [-1] "later" (-3)]
    (collectIndexed entries).1 =
      ([⟨[-1], "first", -7⟩, ⟨[1], "other", 4⟩],
       [.duplicate [-1] (-7) (-3), .duplicate [-1] (-7) (-3)]) := by rfl

theorem signed_first_payload_remains_indexed :
    let entries : List (Entry (Name Int) String Int String) :=
      [.rule [-1] "first" (-7), .rule [-1] "later" (-3)]
    PlainBnfGraphNameTrie.lookup [-1] (collectIndexed entries).2 = some ("first", -7) ∧
      PlainBnfGraphNameTrie.lookup [1] (collectIndexed entries).2 = none := by decide

#print axioms collectIndexed_eq
#print axioms collectIndexed_lookup
#print axioms signed_keys_origins_and_duplicate_occurrences

end Mettapedia.GSLT.Parsing.PlainBnfTrieDeclarationCollector
