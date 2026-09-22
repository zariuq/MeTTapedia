import Mettapedia.GSLT.Parsing.PlainBnfDeclarationSemantics
import Mathlib.Data.List.Nodup

/-!
# Append-free declaration accumulation

The accumulator is a separate list algorithm, compared with the established
declaration semantics for every finite typed input, including initial definition
prefixes containing duplicate names. It pushes definitions and diagnostics onto
reversed lists and reverses each output once.

Lookup remains a list traversal. Its reverse-order form retains the oldest
authored match, not the first match in the reversed representation. Consequently
this repairs repeated append work; it is not a linear-time admission algorithm.
No authored GSLT or native implementation is replaced by this module.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfDeclarationAccumulator

open PlainBnfDeclarationSemantics

universe uN uE uS uT
variable {Name : Type uN} {Expression : Type uE} {Span : Type uS} {Text : Type uT}
variable [DecidableEq Name]

/-- Tail-recursive lookup over reverse-authored order. A later encountered
match is older in source order and replaces the current candidate. -/
def lookupReversedFrom (name : Name) : List (Definition Name Expression Span) → (LookupResult Expression Span)
    → (LookupResult Expression Span)
  | [], candidate => candidate
  | head :: tail, candidate =>
      lookupReversedFrom name tail
        (if name = head.name then .found head.expression head.span else candidate)

def lookupReversed (name : Name) (definitionsReversed : List (Definition Name Expression Span)) : LookupResult
    Expression Span :=
  lookupReversedFrom name definitionsReversed .missing

theorem lookup_append (name : Name) (left right : List (Definition Name Expression Span)) :
    lookup name (left ++ right) =
      match lookup name left with
      | .missing => lookup name right
      | .found expression span => .found expression span := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      by_cases equal : name = head.name
      · simp [lookup, equal]
      · simpa [lookup, equal] using ih

theorem lookupReversedFrom_eq (name : Name) (definitionsReversed : List (Definition Name Expression Span))
    (candidate : LookupResult Expression Span) :
    lookupReversedFrom name definitionsReversed candidate =
      match lookup name definitionsReversed.reverse with
      | .missing => candidate
      | .found expression span => .found expression span := by
  induction definitionsReversed generalizing candidate with
  | nil => rfl
  | cons head tail ih =>
      rw [lookupReversedFrom, ih, List.reverse_cons, lookup_append]
      cases known : lookup name tail.reverse with
      | found expression span => rfl
      | missing =>
          by_cases equal : name = head.name <;> simp [lookup, equal]

theorem lookupReversed_eq (name : Name) (definitionsReversed : List (Definition Name Expression Span)) :
    lookupReversed name definitionsReversed = lookup name definitionsReversed.reverse := by
  unfold lookupReversed
  rw [lookupReversedFrom_eq]
  cases lookup name definitionsReversed.reverse <;> rfl

/-- Every rule allocates one list-spine cell: a fresh definition or a duplicate
diagnostic. Comments and blanks leave both accumulators unchanged. -/
def accumulate : List (Entry Name Expression Span Text) → List (Definition Name Expression Span) → List
    (Diagnostic Name Span) →
    List (Definition Name Expression Span) × List (Diagnostic Name Span)
  | [], definitionsReversed, diagnosticsReversed => (definitionsReversed, diagnosticsReversed)
  | .comment _ _ :: tail, definitionsReversed, diagnosticsReversed =>
      accumulate tail definitionsReversed diagnosticsReversed
  | .blank _ :: tail, definitionsReversed, diagnosticsReversed =>
      accumulate tail definitionsReversed diagnosticsReversed
  | .rule name expression span :: tail, definitionsReversed, diagnosticsReversed =>
      match lookupReversed name definitionsReversed with
      | .missing => accumulate tail
          (⟨name, expression, span⟩ :: definitionsReversed) diagnosticsReversed
      | .found _ firstSpan => accumulate tail definitionsReversed
          (.duplicate name firstSpan span :: diagnosticsReversed)

def collectWithAccumulator (entries : List (Entry Name Expression Span Text)) (before : List (Definition Name
    Expression Span)) :
    List (Definition Name Expression Span) × List (Diagnostic Name Span) :=
  let result := accumulate entries before.reverse []
  (result.1.reverse, result.2.reverse)

/-- General accumulator invariant. Existing diagnostics are preserved as a
prefix after reversal, so the inductive invariant also checks diagnostic order. -/
theorem accumulate_exact (entries : List (Entry Name Expression Span Text)) (definitionsReversed : List
    (Definition Name Expression Span))
    (diagnosticsReversed : List (Diagnostic Name Span)) :
    ((accumulate entries definitionsReversed diagnosticsReversed).1.reverse,
      (accumulate entries definitionsReversed diagnosticsReversed).2.reverse) =
    ((collect entries definitionsReversed.reverse).1,
      diagnosticsReversed.reverse ++ (collect entries definitionsReversed.reverse).2) := by
  induction entries generalizing definitionsReversed diagnosticsReversed with
  | nil => simp [accumulate, collect]
  | cons entry tail ih =>
      cases entry with
      | comment text span => exact ih definitionsReversed diagnosticsReversed
      | blank span => exact ih definitionsReversed diagnosticsReversed
      | rule name expression span =>
          rw [accumulate, lookupReversed_eq]
          cases found : lookup name definitionsReversed.reverse with
          | missing =>
              simpa [collect, found, definitionStep, List.reverse_cons] using
                ih (⟨name, expression, span⟩ :: definitionsReversed) diagnosticsReversed
          | found firstExpression firstSpan =>
              simpa [collect, found, definitionStep, List.reverse_cons, List.append_assoc] using
                ih definitionsReversed (.duplicate name firstSpan span :: diagnosticsReversed)

/-- Exact all-input comparison, not just equality on an example grammar. -/
theorem collectWithAccumulator_eq (entries : List (Entry Name Expression Span Text)) (before : List
    (Definition Name Expression Span)) :
    collectWithAccumulator entries before = collect entries before := by
  have exactResult := accumulate_exact entries before.reverse []
  simpa only [collectWithAccumulator, List.reverse_reverse, List.reverse_nil,
    List.nil_append, Prod.eta] using exactResult

/-- The number of declaration rules, excluding comments and blank entries. -/
def ruleCount : List (Entry Name Expression Span Text) → Nat
  | [] => 0
  | .rule _ _ _ :: tail => ruleCount tail + 1
  | .comment _ _ :: tail => ruleCount tail
  | .blank _ :: tail => ruleCount tail

/-- Exact list-spine growth: every declaration contributes one preserved cell.
This does not count lookup visits, term payload allocations, or native memory. -/
theorem accumulate_spine_growth (entries : List (Entry Name Expression Span Text)) (definitionsReversed : List
    (Definition Name Expression Span))
    (diagnosticsReversed : List (Diagnostic Name Span)) :
    (accumulate entries definitionsReversed diagnosticsReversed).1.length +
      (accumulate entries definitionsReversed diagnosticsReversed).2.length =
    definitionsReversed.length + diagnosticsReversed.length + ruleCount entries := by
  induction entries generalizing definitionsReversed diagnosticsReversed with
  | nil => simp [accumulate, ruleCount]
  | cons entry tail ih =>
      cases entry with
      | comment text span => exact ih definitionsReversed diagnosticsReversed
      | blank span => exact ih definitionsReversed diagnosticsReversed
      | rule name expression span =>
          rw [accumulate]
          cases found : lookupReversed name definitionsReversed <;>
            simp only [ih, List.length_cons, ruleCount] <;> omega

/-- Count only the definition/diagnostic list builder: reverse the initial
prefix, push once per declaration, then reverse the two output lists. -/
def builderConsWork (entries : List (Entry Name Expression Span Text)) (before : List (Definition Name
    Expression Span)) : Nat :=
  let result := accumulate entries before.reverse []
  before.length + ruleCount entries + result.1.length + result.2.length

theorem builderConsWork_exact (entries : List (Entry Name Expression Span Text)) (before : List (Definition
    Name Expression Span)) :
    builderConsWork entries before = 2 * before.length + 2 * ruleCount entries := by
  have growth := accumulate_spine_growth entries before.reverse []
  simp only [List.length_reverse, List.length_nil, Nat.add_zero] at growth
  dsimp [builderConsWork]
  omega

omit [DecidableEq Name] in
theorem ruleCount_le_length (entries : List (Entry Name Expression Span Text)) : ruleCount entries ≤
    entries.length := by
  induction entries with
  | nil => exact Nat.le_refl _
  | cons entry tail ih => cases entry <;> simp only [ruleCount, List.length_cons] <;> omega

theorem builderConsWork_linear_bound (entries : List (Entry Name Expression Span Text)) (before : List
    (Definition Name Expression Span)) :
    builderConsWork entries before ≤ 2 * before.length + 2 * entries.length := by
  rw [builderConsWork_exact]
  have bound := ruleCount_le_length entries
  omega

omit [DecidableEq Name] in
theorem fresh_ruleCount {entries : List (Entry Name Expression Span Text)} {before : List (Definition Name
    Expression Span)}
    (fresh : FreshEntries entries before) : ruleCount entries = entries.length := by
  induction fresh with
  | nil => rfl
  | rule name expression span fresh rest ih => simp [ruleCount, ih]

theorem fresh_empty_builderConsWork {entries : List (Entry Name Expression Span Text)} (fresh : FreshEntries
    entries []) :
    builderConsWork entries [] = 2 * entries.length := by
  simp [builderConsWork_exact, fresh_ruleCount fresh]

/-- The oldest initial definition remains authoritative even when the initial
prefix itself contains repeated names. -/
theorem initial_duplicate_authority (name : Name) (firstExpression : Expression) (firstSpan : Span)
    (laterExpression : Expression) (laterSpan : Span) (expression : Expression) (span : Span) :
    collectWithAccumulator (Text := Text) [.rule name expression span]
      [⟨name, firstExpression, firstSpan⟩, ⟨name, laterExpression, laterSpan⟩] =
      ([⟨name, firstExpression, firstSpan⟩, ⟨name, laterExpression, laterSpan⟩],
        [.duplicate name firstSpan span]) := by
  rw [collectWithAccumulator_eq]
  simp [collect, lookup, definitionStep]

/-- Using ordinary first-match lookup on reversed definitions would change
the authority, so that superficially simpler algorithm is not correct. -/
theorem naive_reversed_lookup_changes_authority (name : Name) (expression : Expression) (firstSpan : Span)
    (laterSpan : Span)
    (differentSpans : firstSpan ≠ laterSpan) :
    lookup name ([⟨name, expression, firstSpan⟩, ⟨name, expression, laterSpan⟩].reverse) ≠
      lookup name [⟨name, expression, firstSpan⟩, ⟨name, expression, laterSpan⟩] := by
  simp [lookup, Ne.symm differentSpans]

theorem duplicate_diagnostics_retained (name : Name) (firstExpression : Expression) (firstSpan : Span)
    (expression : Expression) (span : Span) :
    collectWithAccumulator (Text := Text) [.rule name expression span, .rule name expression span]
      [⟨name, firstExpression, firstSpan⟩] =
      ([⟨name, firstExpression, firstSpan⟩],
        [.duplicate name firstSpan span, .duplicate name firstSpan span]) := by
  rw [collectWithAccumulator_eq]
  exact collect_duplicate_order _ _ _ _ _ _ _ []

theorem distinct_rules_source_order (name₁ : Name) (expression₁ : Expression) (span₁ : Span) (name₂ : Name)
    (expression₂ : Expression) (span₂ : Span)
    (different : name₁ ≠ name₂) :
    collectWithAccumulator (Text := Text) [.rule name₁ expression₁ span₁, .rule name₂ expression₂ span₂] [] =
      ([⟨name₁, expression₁, span₁⟩, ⟨name₂, expression₂, span₂⟩], []) := by
  rw [collectWithAccumulator_eq]
  simp [collect, lookup, definitionStep, Ne.symm different]

/-- The accumulated environment has at most one retained definition per name.
Duplicate source declarations still remain present in the diagnostic list. -/
def DistinctDefinitionNames (definitions : List (Definition Name Expression Span)) : Prop :=
  (definitions.map Definition.name).Nodup

omit [DecidableEq Name] in
theorem distinctDefinitionNames_reverse (definitions : List (Definition Name Expression Span)) :
    DistinctDefinitionNames definitions.reverse ↔ DistinctDefinitionNames definitions := by
  simp [DistinctDefinitionNames, List.map_reverse, List.nodup_reverse]

theorem definitionStep_preserves_distinct {name : Name} {span : Span} {expression : Expression}
    {result : LookupResult Expression Span} {before after : List (Definition Name Expression Span)}
        {diagnostics : List (Diagnostic Name Span)}
    (queried : Lookup name before result)
    (stepped : DefinitionStep name span expression result before after diagnostics)
    (distinct : DistinctDefinitionNames before) : DistinctDefinitionNames after := by
  cases stepped with
  | fresh appended =>
      rw [appended.result_eq]
      have missing := queried.result_eq.symm
      have fresh := (lookup_missing_iff name before).mp missing
      simp only [DistinctDefinitionNames, List.map_append, List.map_cons, List.map_nil]
      apply List.Nodup.append distinct (by simp)
      apply List.disjoint_left.mpr
      intro key member memberSingle
      have equal := List.mem_singleton.mp memberSingle
      cases equal
      exact fresh member
  | duplicate => exact distinct

theorem collect_preserves_distinct {entries : List (Entry Name Expression Span Text)}
    {before after : List (Definition Name Expression Span)} {diagnostics : List (Diagnostic Name Span)}
    (derivation : Collect entries before after diagnostics)
    (distinct : DistinctDefinitionNames before) : DistinctDefinitionNames after := by
  induction derivation with
  | nil => exact distinct
  | comment text span rest ih => exact ih distinct
  | blank span rest ih => exact ih distinct
  | rule name expression span queried stepped rest appended ih =>
      exact ih (definitionStep_preserves_distinct queried stepped distinct)

/-- This is unconditional over entry lists: even repeated names are accepted
as input and diagnosed, while only their first declaration enters the environment. -/
theorem collect_empty_distinct (entries : List (Entry Name Expression Span Text)) :
    DistinctDefinitionNames (collect entries []).1 :=
  collect_preserves_distinct (collectDerivation entries []) (by simp [DistinctDefinitionNames])

/-- With distinct keys, reversal changes lookup order but not the selected definition. -/
theorem lookup_reverse_eq_of_distinct (name : Name) (definitions : List (Definition Name Expression Span))
    (distinct : DistinctDefinitionNames definitions) :
    lookup name definitions.reverse = lookup name definitions := by
  induction definitions with
  | nil => rfl
  | cons head tail ih =>
      have parts : head.name ∉ tail.map Definition.name ∧ DistinctDefinitionNames tail := by
        simpa [DistinctDefinitionNames] using distinct
      rw [List.reverse_cons, lookup_append, ih parts.2]
      by_cases same : name = head.name
      · have missing := (lookup_missing_iff name tail).mpr (by simpa [same] using parts.1)
        have missing' : lookup head.name tail = .missing := by simpa [same] using missing
        simp [lookup, same, missing']
      · cases known : lookup name tail <;> simp [lookup, same, known]

theorem lookupReversed_eq_lookup_of_distinct (name : Name) (definitions : List (Definition Name Expression
    Span))
    (distinct : DistinctDefinitionNames definitions) :
    lookupReversed name definitions = lookup name definitions := by
  rw [lookupReversed_eq, lookup_reverse_eq_of_distinct name definitions distinct]

/-- Specialization that can stop at the first matching reversed definition.
Its correctness precondition is proved invariant below, not silently assumed. -/
def accumulateDistinct : List (Entry Name Expression Span Text) → List (Definition Name Expression Span) →
    List (Diagnostic Name Span) →
    List (Definition Name Expression Span) × List (Diagnostic Name Span)
  | [], definitionsReversed, diagnosticsReversed => (definitionsReversed, diagnosticsReversed)
  | .comment _ _ :: tail, definitionsReversed, diagnosticsReversed =>
      accumulateDistinct tail definitionsReversed diagnosticsReversed
  | .blank _ :: tail, definitionsReversed, diagnosticsReversed =>
      accumulateDistinct tail definitionsReversed diagnosticsReversed
  | .rule name expression span :: tail, definitionsReversed, diagnosticsReversed =>
      match lookup name definitionsReversed with
      | .missing => accumulateDistinct tail
          (⟨name, expression, span⟩ :: definitionsReversed) diagnosticsReversed
      | .found _ firstSpan => accumulateDistinct tail definitionsReversed
          (.duplicate name firstSpan span :: diagnosticsReversed)

theorem accumulateDistinct_eq (entries : List (Entry Name Expression Span Text)) (definitionsReversed : List
    (Definition Name Expression Span))
    (diagnosticsReversed : List (Diagnostic Name Span)) (distinct : DistinctDefinitionNames
        definitionsReversed) :
    accumulateDistinct entries definitionsReversed diagnosticsReversed =
      accumulate entries definitionsReversed diagnosticsReversed := by
  induction entries generalizing definitionsReversed diagnosticsReversed with
  | nil => rfl
  | cons entry tail ih =>
      cases entry with
      | comment text span => exact ih definitionsReversed diagnosticsReversed distinct
      | blank span => exact ih definitionsReversed diagnosticsReversed distinct
      | rule name expression span =>
          rw [accumulateDistinct, accumulate, lookupReversed_eq_lookup_of_distinct _ _ distinct]
          cases queried : lookup name definitionsReversed with
          | missing =>
              have fresh := (lookup_missing_iff name definitionsReversed).mp queried
              apply ih _ diagnosticsReversed
              exact List.nodup_cons.mpr ⟨fresh, distinct⟩
          | found firstExpression firstSpan => exact ih _ _ distinct

theorem accumulateDistinct_preserves_distinct (entries : List (Entry Name Expression Span Text))
    (definitionsReversed : List (Definition Name Expression Span)) (diagnosticsReversed : List (Diagnostic
        Name Span))
    (distinct : DistinctDefinitionNames definitionsReversed) :
    DistinctDefinitionNames (accumulateDistinct entries definitionsReversed diagnosticsReversed).1 := by
  rw [accumulateDistinct_eq _ _ _ distinct]
  have computed := congrArg Prod.fst (accumulate_exact entries definitionsReversed diagnosticsReversed)
  have sourceDistinct := collect_preserves_distinct
    (collectDerivation entries definitionsReversed.reverse)
    ((distinctDefinitionNames_reverse _).mpr distinct)
  apply (distinctDefinitionNames_reverse _).mp
  change (accumulate entries definitionsReversed diagnosticsReversed).1.reverse =
    (collect entries definitionsReversed.reverse).1 at computed
  rw [computed]
  exact sourceDistinct

def collectFromEmptyFast (entries : List (Entry Name Expression Span Text)) : List (Definition Name Expression
    Span) × List (Diagnostic Name Span) :=
  let result := accumulateDistinct entries [] []
  (result.1.reverse, result.2.reverse)

theorem collectFromEmptyFast_eq (entries : List (Entry Name Expression Span Text)) :
    collectFromEmptyFast entries = collect entries [] := by
  have specialized := accumulateDistinct_eq entries [] [] (by simp [DistinctDefinitionNames])
  simpa only [collectFromEmptyFast, specialized, collectWithAccumulator, List.reverse_nil]
    using collectWithAccumulator_eq entries []

theorem collectFromEmptyFast_distinct (entries : List (Entry Name Expression Span Text)) :
    DistinctDefinitionNames (collectFromEmptyFast entries).1 := by
  rw [collectFromEmptyFast_eq]
  exact collect_empty_distinct entries

/-- The first-match specialization retains the same linear list-builder work.
This excludes lookup visits and does not assert a runtime speedup. -/
theorem fast_empty_builder_cons_work (entries : List (Entry Name Expression Span Text)) :
    ruleCount entries + (accumulateDistinct entries [] []).1.length +
      (accumulateDistinct entries [] []).2.length = 2 * ruleCount entries := by
  rw [accumulateDistinct_eq entries [] [] (by simp [DistinctDefinitionNames])]
  have growth := accumulate_spine_growth entries [] []
  simp only [List.length_nil, Nat.zero_add] at growth
  omega

theorem collectFromEmptyFast_duplicate_diagnostics (name : Name) (firstExpression : Expression) (firstSpan :
    Span) (expression : Expression) (duplicateSpan : Span) :
    collectFromEmptyFast (Text := Text) [.rule name firstExpression firstSpan,
      .rule name expression duplicateSpan, .rule name expression duplicateSpan] =
      ([⟨name, firstExpression, firstSpan⟩],
        [.duplicate name firstSpan duplicateSpan, .duplicate name firstSpan duplicateSpan]) := by
  rw [collectFromEmptyFast_eq]
  simp [collect, lookup, definitionStep]

omit [DecidableEq Name] in
/-- Equal lookup values do not imply equal lookup work. Reversed order can
lengthen a query for an old key even though early stopping is permitted. -/
theorem reversed_lookup_can_visit_more (oldName : Name) (oldExpression : Expression) (oldSpan : Span) (newName
    : Name) (newExpression : Expression) (newSpan : Span) (different : oldName ≠ newName) :
    ∃ forward : Lookup oldName [⟨oldName, oldExpression, oldSpan⟩,
        ⟨newName, newExpression, newSpan⟩] (.found oldExpression oldSpan),
      ∃ reversed : Lookup oldName [⟨newName, newExpression, newSpan⟩,
          ⟨oldName, oldExpression, oldSpan⟩] (.found oldExpression oldSpan),
        forward.occurrences.length = 1 ∧ reversed.occurrences.length = 2 := by
  exact ⟨.found _ _ rfl, .tail _ _ different (.found _ _ rfl), rfl, rfl⟩

end Mettapedia.GSLT.Parsing.PlainBnfDeclarationAccumulator
