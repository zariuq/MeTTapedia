import Mettapedia.GSLT.Parsing.PlainBnfNameIndexOrdered
import Mettapedia.GSLT.Parsing.PlainBnfDeclarationAccumulator

/-!
# Indexed declaration collection with exact ordered outputs

The index is only an auxiliary first-binding map. Declarations and diagnostics
remain separate ordered lists, including repeated initial declarations and
equal duplicate diagnostics. The independent index/list invariant proves this
collector agrees with the established declaration pass for all finite typed
inputs. Source-rule and runtime correspondence remain separate obligations.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfNameIndexCollector

open PlainBnfDeclarationSemantics
open PlainBnfDeclarationAccumulator

universe uN uE uS uT
variable {Name : Type uN} {Expression : Type uE} {Span : Type uS} {Text : Type uT}
variable [LinearOrder Name]

abbrev NameIndex (Name : Type uN) (Expression : Type uE) (Span : Type uS) :=
  PlainBnfNameIndex.Tree Name (Definition Name Expression Span)

def findDefinition (name : Name) : List (Definition Name Expression Span) →
    Option (Definition Name Expression Span)
  | [] => none
  | head :: tail => if name = head.name then some head else findDefinition name tail

def resultOfDefinition : Option (Definition Name Expression Span) → LookupResult Expression Span
  | none => .missing
  | some definition => .found definition.expression definition.span

theorem findDefinition_result (name : Name) (definitions : List (Definition Name Expression Span)) :
    resultOfDefinition (findDefinition name definitions) = lookup name definitions := by
  induction definitions with
  | nil => rfl
  | cons head tail ih =>
      simp only [findDefinition, lookup]
      split_ifs
      · rfl
      · exact ih

theorem findDefinition_append (name : Name)
    (left right : List (Definition Name Expression Span)) :
    findDefinition name (left ++ right) =
      match findDefinition name left with
      | some definition => some definition
      | none => findDefinition name right := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, findDefinition]
      split_ifs
      · rfl
      · exact ih

structure Represents (index : NameIndex Name Expression Span)
    (definitions : List (Definition Name Expression Span)) : Prop where
  ordered : PlainBnfNameIndex.Ordered index
  lookup_exact : ∀ name, PlainBnfNameIndex.lookup name index = findDefinition name definitions

theorem represents_empty : Represents (.empty : NameIndex Name Expression Span) [] := by
  exact ⟨List.Pairwise.nil, fun _ => rfl⟩

theorem Represents.append {index : NameIndex Name Expression Span}
    {definitions : List (Definition Name Expression Span)} (represents : Represents index definitions)
    (definition : Definition Name Expression Span) :
    Represents (PlainBnfNameIndex.insertFirst definition.name definition index) (definitions ++ [definition]) := by
  refine ⟨PlainBnfNameIndex.insertFirst_ordered _ _ _ represents.ordered, ?_⟩
  intro name
  rw [PlainBnfNameIndex.lookup_insertFirst name definition.name definition index represents.ordered,
    findDefinition_append, represents.lookup_exact, represents.lookup_exact]
  by_cases equal : name = definition.name
  · subst name
    simp only [findDefinition]
    cases findDefinition definition.name definitions <;> rfl
  · simp only [if_neg equal, findDefinition]
    cases findDefinition name definitions <;> rfl

def seed : List (Definition Name Expression Span) → NameIndex Name Expression Span →
    NameIndex Name Expression Span
  | [], index => index
  | head :: tail, index => seed tail (PlainBnfNameIndex.insertFirst head.name head index)

theorem seed_represents (added : List (Definition Name Expression Span))
    {index : NameIndex Name Expression Span} {before : List (Definition Name Expression Span)}
    (represents : Represents index before) : Represents (seed added index) (before ++ added) := by
  induction added generalizing index before with
  | nil => simpa [seed] using represents
  | cons head tail ih =>
      have next := ih (represents.append head)
      simpa [seed, List.append_assoc] using next

theorem seed_empty_represents (before : List (Definition Name Expression Span)) :
    Represents (seed before .empty) before := by
  simpa using seed_represents before represents_empty

theorem seed_balanced (added : List (Definition Name Expression Span))
    {index : NameIndex Name Expression Span} {height : Nat}
    (balanced : PlainBnfNameIndex.Balanced index height) :
    ∃ afterHeight, PlainBnfNameIndex.Balanced (seed added index) afterHeight ∧
      height ≤ afterHeight ∧ afterHeight ≤ height + added.length := by
  induction added generalizing index height with
  | nil => exact ⟨height, balanced, Nat.le_refl _, by simp⟩
  | cons head tail ih =>
      rcases PlainBnfNameIndex.insertFirst_balanced head.name head balanced with same | split
      · obtain ⟨afterHeight, afterBalanced, lower, upper⟩ := ih same
        exact ⟨afterHeight, afterBalanced, lower, by simp only [List.length_cons]; omega⟩
      · obtain ⟨afterHeight, afterBalanced, lower, upper⟩ := ih split
        exact ⟨afterHeight, afterBalanced, by omega, by simp only [List.length_cons]; omega⟩

/-- Seeding retains an equal-depth tree whose structural height is logarithmic
in its retained binding count. Name comparison and runtime allocation are not
included in this bound. -/
theorem seed_empty_height (before : List (Definition Name Expression Span)) :
    ∃ height, PlainBnfNameIndex.Balanced (seed before .empty) height ∧
      2 ^ height ≤ (PlainBnfNameIndex.bindings (seed before .empty)).length + 1 := by
  obtain ⟨height, balanced, _, _⟩ := seed_balanced before PlainBnfNameIndex.Balanced.empty
  exact ⟨height, balanced, PlainBnfNameIndex.balanced_min_bindings balanced⟩

def accumulateIndexed : List (Entry Name Expression Span Text) → NameIndex Name Expression Span →
    List (Definition Name Expression Span) → List (Diagnostic Name Span) →
    List (Definition Name Expression Span) × List (Diagnostic Name Span)
  | [], _, definitionsReversed, diagnosticsReversed => (definitionsReversed, diagnosticsReversed)
  | .comment _ _ :: tail, index, definitionsReversed, diagnosticsReversed =>
      accumulateIndexed tail index definitionsReversed diagnosticsReversed
  | .blank _ :: tail, index, definitionsReversed, diagnosticsReversed =>
      accumulateIndexed tail index definitionsReversed diagnosticsReversed
  | .rule name expression span :: tail, index, definitionsReversed, diagnosticsReversed =>
      match PlainBnfNameIndex.lookup name index with
      | none => accumulateIndexed tail
          (PlainBnfNameIndex.insertFirst name ⟨name, expression, span⟩ index)
          (⟨name, expression, span⟩ :: definitionsReversed) diagnosticsReversed
      | some first => accumulateIndexed tail index definitionsReversed
          (.duplicate name first.span span :: diagnosticsReversed)

/-- The index replaces lookup only. The exact two output lists, including
their order and repeated payloads, are unchanged. -/
theorem accumulateIndexed_eq (entries : List (Entry Name Expression Span Text))
    (index : NameIndex Name Expression Span) (definitionsReversed : List (Definition Name Expression Span))
    (diagnosticsReversed : List (Diagnostic Name Span))
    (represents : Represents index definitionsReversed.reverse) :
    accumulateIndexed entries index definitionsReversed diagnosticsReversed =
      accumulate entries definitionsReversed diagnosticsReversed := by
  induction entries generalizing index definitionsReversed diagnosticsReversed with
  | nil => rfl
  | cons entry tail ih =>
      cases entry with
      | comment text span => exact ih index definitionsReversed diagnosticsReversed represents
      | blank span => exact ih index definitionsReversed diagnosticsReversed represents
      | rule name expression span =>
          have search := congrArg resultOfDefinition (represents.lookup_exact name)
          rw [findDefinition_result] at search
          rw [accumulateIndexed, accumulate, lookupReversed_eq, ← search]
          cases found : PlainBnfNameIndex.lookup name index with
          | none =>
              have next := represents.append (⟨name, expression, span⟩ : Definition Name Expression Span)
              rw [← List.reverse_cons] at next
              exact ih _ _ _ next
          | some first => exact ih index definitionsReversed _ represents

def collectIndexed (entries : List (Entry Name Expression Span Text))
    (before : List (Definition Name Expression Span)) :
    List (Definition Name Expression Span) × List (Diagnostic Name Span) :=
  let result := accumulateIndexed entries (seed before .empty) before.reverse []
  (result.1.reverse, result.2.reverse)

/-- All-input ordered equivalence, including an initial prefix with duplicate
names and arbitrary comment/blank entries. -/
theorem collectIndexed_eq (entries : List (Entry Name Expression Span Text))
    (before : List (Definition Name Expression Span)) :
    collectIndexed entries before = collect entries before := by
  have represents : Represents (seed before .empty) before.reverse.reverse := by
    simpa using seed_empty_represents before
  rw [collectIndexed, accumulateIndexed_eq entries _ _ _ represents]
  exact collectWithAccumulator_eq entries before

/-- The map does not collapse repeated initial declarations or diagnostics.
Its first stored definition supplies the original source span each time. -/
theorem initial_duplicates_retained (name : Name) (firstExpression laterExpression expression : Expression)
    (firstSpan laterSpan span : Span) :
    collectIndexed (Text := Text) [.rule name expression span, .rule name expression span]
      [⟨name, firstExpression, firstSpan⟩, ⟨name, laterExpression, laterSpan⟩] =
      ([⟨name, firstExpression, firstSpan⟩, ⟨name, laterExpression, laterSpan⟩],
        [.duplicate name firstSpan span, .duplicate name firstSpan span]) := by
  rw [collectIndexed_eq]
  simp [collect, lookup, definitionStep]

/-- The index's key order is not the returned declaration order. -/
example : collectIndexed (Name := Nat) (Expression := String) (Span := Nat) (Text := String)
    [.rule 2 "two" 20, .comment "between" 21, .blank 22, .rule 1 "one" 10] [] =
    ([⟨2, "two", 20⟩, ⟨1, "one", 10⟩], []) := by
  rw [collectIndexed_eq]
  simp [collect, lookup, definitionStep]

example : collectIndexed (Name := Nat) (Expression := String) (Span := Nat) (Text := String)
    [.rule 2 "replacement" 30] [⟨2, "first", 20⟩, ⟨2, "later", 25⟩] =
    ([⟨2, "first", 20⟩, ⟨2, "later", 25⟩], [.duplicate 2 20 30]) := by
  rw [collectIndexed_eq]
  simp [collect, lookup, definitionStep]

end Mettapedia.GSLT.Parsing.PlainBnfNameIndexCollector
