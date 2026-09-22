import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
# Ordered, proof-relevant plain-BNF declaration collection

This independent finite-data semantics specifies the whole declaration pass:
first matching lookup, ordered insertion, duplicate diagnostics, and traversal
of rules, comments, and blank entries. Its derivations live in `Type`; proving
their uniqueness checks derivation constructors, not just answer values.
Correspondence with authored source occurrences is a separate obligation.

Names, expressions, spans, and comment text are independent payload types. The
algorithm uses decidable equality only on names. No source certificate carrier,
execution calculus, parser, or native runtime is part of this model. Source
representations and their comparison operations are connected separately.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfDeclarationSemantics

universe uN uE uS uT

structure Definition (Name : Type uN) (Expression : Type uE) (Span : Type uS) where
  name : Name
  expression : Expression
  span : Span
  deriving Repr

inductive Entry (Name : Type uN) (Expression : Type uE) (Span : Type uS)
    (Text : Type uT) where
  | rule (name : Name) (expression : Expression) (span : Span)
  | comment (text : Text) (span : Span)
  | blank (span : Span)
  deriving Repr

inductive Diagnostic (Name : Type uN) (Span : Type uS) where
  | duplicate (name : Name) (firstSpan duplicateSpan : Span)
  deriving Repr

inductive LookupResult (Expression : Type uE) (Span : Type uS) where
  | missing
  | found (expression : Expression) (span : Span)
  deriving Repr

variable {Name : Type uN} {Expression : Type uE} {Span : Type uS} {Text : Type uT}
variable [DecidableEq Name]

def lookup (name : Name) : List (Definition Name Expression Span) → (LookupResult Expression Span)
  | [] => .missing
  | head :: tail =>
      if name = head.name then .found head.expression head.span else lookup name tail

def definitionStep (name : Name) (span : Span) (expression : Expression) (result : LookupResult Expression Span)
    (before : List (Definition Name Expression Span)) : List (Definition Name Expression Span) × List
        (Diagnostic Name Span) :=
  match result with
  | .missing => (before ++ [⟨name, expression, span⟩], [])
  | .found _ firstSpan => (before, [.duplicate name firstSpan span])

def collect : List (Entry Name Expression Span Text) → List (Definition Name Expression Span) → List
    (Definition Name Expression Span) × List (Diagnostic Name Span)
  | [], before => (before, [])
  | .comment _ _ :: tail, before => collect tail before
  | .blank _ :: tail, before => collect tail before
  | .rule name expression span :: tail, before =>
      let next := definitionStep name span expression (lookup name before) before
      let rest := collect tail next.1
      (rest.1, next.2 ++ rest.2)

/-- Each constructor is a distinct declaration-lookup rule occurrence. -/
inductive Lookup (name : Name) : List (Definition Name Expression Span) → (LookupResult Expression Span) →
    Type _ where
  | missing : Lookup name [] .missing
  | found (head : Definition Name Expression Span) (tail : List (Definition Name Expression Span)) (equal :
      name = head.name) :
      Lookup name (head :: tail) (.found head.expression head.span)
  | tail (head : Definition Name Expression Span) (tail : List (Definition Name Expression Span)) (different :
      name ≠ head.name)
      {result : LookupResult Expression Span} (rest : Lookup name tail result) :
      Lookup name (head :: tail) result

inductive AppendDefinition : List (Definition Name Expression Span) → (Definition Name Expression Span) → List
    (Definition Name Expression Span) → Type _ where
  | nil (definition : Definition Name Expression Span) : AppendDefinition [] definition [definition]
  | cons (head : Definition Name Expression Span) {tail : List (Definition Name Expression Span)} {definition
      : Definition Name Expression Span}
      {after : List (Definition Name Expression Span)} (rest : AppendDefinition tail definition after) :
      AppendDefinition (head :: tail) definition (head :: after)

inductive AppendDiagnostics :
    List (Diagnostic Name Span) → List (Diagnostic Name Span) → List (Diagnostic Name Span) → Type _ where
  | nil (right : List (Diagnostic Name Span)) : AppendDiagnostics [] right right
  | cons (head : Diagnostic Name Span) {tail right after : List (Diagnostic Name Span)}
      (rest : AppendDiagnostics tail right after) :
      AppendDiagnostics (head :: tail) right (head :: after)

inductive DefinitionStep (name : Name) (span : Span) (expression : Expression) :
    (LookupResult Expression Span) → List (Definition Name Expression Span) → List (Definition Name Expression
        Span) → List (Diagnostic Name Span) → Type _ where
  | fresh {before after : List (Definition Name Expression Span)}
      (append : AppendDefinition before ⟨name, expression, span⟩ after) :
      DefinitionStep name span expression .missing before after []
  | duplicate (firstExpression : Expression) (firstSpan : Span) (before : List (Definition Name Expression
      Span)) :
      DefinitionStep name span expression (.found firstExpression firstSpan)
        before before [.duplicate name firstSpan span]

inductive Collect : List (Entry Name Expression Span Text) → List (Definition Name Expression Span) → List
    (Definition Name Expression Span) →
    List (Diagnostic Name Span) → Type _ where
  | nil (before : List (Definition Name Expression Span)) : Collect [] before before []
  | comment (text : Text) (span : Span) {tail : List (Entry Name Expression Span Text)}
      {before after : List (Definition Name Expression Span)} {diagnostics : List (Diagnostic Name Span)}
      (rest : Collect tail before after diagnostics) :
      Collect (.comment text span :: tail) before after diagnostics
  | blank (span : Span) {tail : List (Entry Name Expression Span Text)}
      {before after : List (Definition Name Expression Span)} {diagnostics : List (Diagnostic Name Span)}
      (rest : Collect tail before after diagnostics) :
      Collect (.blank span :: tail) before after diagnostics
  | rule (name : Name) (expression : Expression) (span : Span) {tail : List (Entry Name Expression Span Text)}
      {before next after : List (Definition Name Expression Span)} {result : LookupResult Expression Span}
      {currentDiagnostics tailDiagnostics diagnostics : List (Diagnostic Name Span)}
      (lookup : Lookup name before result)
      (step : DefinitionStep name span expression result before next currentDiagnostics)
      (rest : Collect tail next after tailDiagnostics)
      (append : AppendDiagnostics currentDiagnostics tailDiagnostics diagnostics) :
      Collect (.rule name expression span :: tail) before after diagnostics

def lookupDerivation (name : Name) :
    (definitions : List (Definition Name Expression Span)) → Lookup name definitions (lookup name definitions)
  | [] => .missing
  | head :: tail => by
      by_cases equal : name = head.name
      · simpa [lookup, equal] using Lookup.found head tail equal
      · simpa [lookup, equal] using Lookup.tail head tail equal (lookupDerivation name tail)

def appendDefinitionDerivation (definition : Definition Name Expression Span) :
    (before : List (Definition Name Expression Span)) → AppendDefinition before definition (before ++
        [definition])
  | [] => .nil definition
  | head :: tail => .cons head (appendDefinitionDerivation definition tail)

def appendDiagnosticsDerivation (right : List (Diagnostic Name Span)) :
    (left : List (Diagnostic Name Span)) → AppendDiagnostics left right (left ++ right)
  | [] => .nil right
  | head :: tail => .cons head (appendDiagnosticsDerivation right tail)

def definitionStepDerivation (name : Name) (span : Span) (expression : Expression)
    (result : LookupResult Expression Span) (before : List (Definition Name Expression Span)) :
    DefinitionStep name span expression result before
      (definitionStep name span expression result before).1
      (definitionStep name span expression result before).2 :=
  match result with
  | .missing => .fresh (appendDefinitionDerivation _ before)
  | .found firstExpression firstSpan => .duplicate firstExpression firstSpan before

def collectDerivation : (entries : List (Entry Name Expression Span Text)) → (before : List (Definition Name
    Expression Span)) →
    Collect entries before (collect entries before).1 (collect entries before).2
  | [], before => .nil before
  | .comment text span :: tail, before => .comment text span (collectDerivation tail before)
  | .blank span :: tail, before => .blank span (collectDerivation tail before)
  | .rule name expression span :: tail, before =>
      .rule name expression span (lookupDerivation name before)
        (definitionStepDerivation name span expression (lookup name before) before)
        (collectDerivation tail _)
        (appendDiagnosticsDerivation _ _)

theorem Lookup.result_eq {name : Name} {definitions : List (Definition Name Expression Span)}
    {result : LookupResult Expression Span} (derivation : Lookup name definitions result) :
    result = lookup name definitions := by
  induction derivation with
  | missing => rfl
  | found head tail equal => simp [lookup, equal]
  | tail head tail different rest ih => simpa [lookup, different] using ih

omit [DecidableEq Name] in
theorem AppendDefinition.result_eq {before after : List (Definition Name Expression Span)} {definition :
    Definition Name Expression Span}
    (derivation : AppendDefinition before definition after) :
    after = before ++ [definition] := by
  induction derivation with
  | nil => rfl
  | cons head rest ih => simpa using congrArg (head :: ·) ih

omit [DecidableEq Name] in
theorem AppendDiagnostics.result_eq {left right after : List (Diagnostic Name Span)}
    (derivation : AppendDiagnostics left right after) : after = left ++ right := by
  induction derivation with
  | nil => rfl
  | cons head rest ih => simpa using congrArg (head :: ·) ih

omit [DecidableEq Name] in
theorem DefinitionStep.result_eq {name : Name} {span : Span} {expression : Expression}
    {result : LookupResult Expression Span} {before after : List (Definition Name Expression Span)}
        {diagnostics : List (Diagnostic Name Span)}
    (derivation : DefinitionStep name span expression result before after diagnostics) :
    (after, diagnostics) = definitionStep name span expression result before := by
  cases derivation with
  | fresh append => exact Prod.ext append.result_eq rfl
  | duplicate => rfl

theorem Collect.result_eq {entries : List (Entry Name Expression Span Text)} {before after : List (Definition
    Name Expression Span)}
    {diagnostics : List (Diagnostic Name Span)} (derivation : Collect entries before after diagnostics) :
    (after, diagnostics) = collect entries before := by
  induction derivation with
  | nil => rfl
  | comment text span rest ih => exact ih
  | blank span rest ih => exact ih
  | rule name expression span lookup step rest append ih =>
      simp only [collect]
      rw [← lookup.result_eq, ← step.result_eq, ← ih]
      exact Prod.ext rfl append.result_eq

omit [DecidableEq Name] in
theorem Lookup.unique {name : Name} {definitions : List (Definition Name Expression Span)}
    {result : LookupResult Expression Span} (left right : Lookup name definitions result) : left = right := by
  induction left with
  | missing => cases right; rfl
  | found head tail equal =>
      cases right with
      | found => rfl
      | tail _ _ different => exact False.elim (different equal)
  | tail head tail different rest ih =>
      cases right with
      | found _ _ equal => exact False.elim (different equal)
      | tail _ _ _ other => exact congrArg (Lookup.tail head tail different) (ih other)

omit [DecidableEq Name] in
theorem AppendDefinition.unique {before after : List (Definition Name Expression Span)} {definition :
    Definition Name Expression Span}
    (left right : AppendDefinition before definition after) : left = right := by
  induction left with
  | nil => cases right; rfl
  | cons head rest ih =>
      cases right with
      | cons _ other => exact congrArg (AppendDefinition.cons head) (ih other)

omit [DecidableEq Name] in
theorem AppendDiagnostics.unique {left right after : List (Diagnostic Name Span)}
    (first second : AppendDiagnostics left right after) : first = second := by
  induction first with
  | nil => cases second; rfl
  | cons head rest ih =>
      cases second with
      | cons _ other => exact congrArg (AppendDiagnostics.cons head) (ih other)

omit [DecidableEq Name] in
theorem DefinitionStep.unique {name : Name} {span : Span} {expression : Expression}
    {result : LookupResult Expression Span} {before after : List (Definition Name Expression Span)}
        {diagnostics : List (Diagnostic Name Span)}
    (left right : DefinitionStep name span expression result before after diagnostics) :
    left = right := by
  cases left with
  | fresh append =>
      cases right with
      | fresh other => exact congrArg DefinitionStep.fresh (append.unique other)
  | duplicate => cases right; rfl

theorem Collect.unique {entries : List (Entry Name Expression Span Text)} {before after : List (Definition
    Name Expression Span)}
    {diagnostics : List (Diagnostic Name Span)} (left right : Collect entries before after diagnostics) :
    left = right := by
  induction left with
  | nil => cases right; rfl
  | comment text span rest ih =>
      cases right with
      | comment _ _ other => exact congrArg (Collect.comment text span) (ih other)
  | blank span rest ih =>
      cases right with
      | blank _ other => exact congrArg (Collect.blank span) (ih other)
  | rule name expression span lookup step rest append ih =>
      cases right with
      | rule _ _ _ lookup' step' rest' append' =>
          have resultEquality := lookup.result_eq.trans lookup'.result_eq.symm
          cases resultEquality
          have stepEquality := step.result_eq.trans step'.result_eq.symm
          cases Prod.mk.inj stepEquality with
          | intro nextEquality diagnosticsEquality =>
              cases nextEquality
              cases diagnosticsEquality
              have restEquality := rest.result_eq.trans rest'.result_eq.symm
              have tailEquality := congrArg Prod.snd restEquality
              cases tailEquality
              cases lookup.unique lookup'
              cases step.unique step'
              cases ih rest'
              cases append.unique append'
              rfl

/-- Both the output and its canonical execution occurrence are unique. -/
@[instance_reducible] def collectTotalUnique (entries : List (Entry Name Expression Span Text)) (before : List
    (Definition Name Expression Span)) :
    Unique (Σ after : List (Definition Name Expression Span), Σ diagnostics : List (Diagnostic Name Span),
      Collect entries before after diagnostics) := by
  refine ⟨⟨⟨(collect entries before).1, (collect entries before).2,
    collectDerivation entries before⟩⟩, ?_⟩
  rintro ⟨after, diagnostics, derivation⟩
  have outputs := derivation.result_eq
  have first := congrArg Prod.fst outputs
  have second := congrArg Prod.snd outputs
  cases first
  cases second
  cases derivation.unique (collectDerivation entries before)
  rfl

/-- Exact ordered output, without forgetting the inhabitance obligation. -/
theorem collect_iff {entries : List (Entry Name Expression Span Text)} {before after : List (Definition Name
    Expression Span)}
    {diagnostics : List (Diagnostic Name Span)} :
    Nonempty (Collect entries before after diagnostics) ↔
      (after, diagnostics) = collect entries before := by
  constructor
  · rintro ⟨derivation⟩
    exact derivation.result_eq
  · intro outputs
    have first := congrArg Prod.fst outputs
    have second := congrArg Prod.snd outputs
    cases first
    cases second
    exact ⟨collectDerivation entries before⟩

/-- Authored declaration-pass rule occurrence indices, omitting provider events.
The source client checks this index assignment against its actual source. -/
def Lookup.occurrences {name : Name} {definitions : List (Definition Name Expression Span)}
    {result : LookupResult Expression Span} : Lookup name definitions result → List Nat
  | .missing => [0]
  | .found _ _ _ => [1]
  | .tail _ _ _ rest => 2 :: rest.occurrences

def AppendDefinition.occurrences {before after : List (Definition Name Expression Span)} {definition :
    Definition Name Expression Span} :
    AppendDefinition before definition after → List Nat
  | .nil _ => [3]
  | .cons _ rest => 4 :: rest.occurrences

def AppendDiagnostics.occurrences {left right after : List (Diagnostic Name Span)} :
    AppendDiagnostics left right after → List Nat
  | .nil _ => [5]
  | .cons _ rest => 6 :: rest.occurrences

def DefinitionStep.occurrences {name : Name} {span : Span} {expression : Expression}
    {result : LookupResult Expression Span} {before after : List (Definition Name Expression Span)}
        {diagnostics : List (Diagnostic Name Span)} :
    DefinitionStep name span expression result before after diagnostics → List Nat
  | .fresh append => 7 :: append.occurrences
  | .duplicate _ _ _ => [8]

def Collect.occurrences {entries : List (Entry Name Expression Span Text)} {before after : List (Definition
    Name Expression Span)}
    {diagnostics : List (Diagnostic Name Span)} : Collect entries before after diagnostics → List Nat
  | .nil _ => [9]
  | .comment _ _ rest => 10 :: rest.occurrences
  | .blank _ rest => 11 :: rest.occurrences
  | .rule _ _ _ lookup step rest append =>
      12 :: (lookup.occurrences ++ step.occurrences ++ rest.occurrences ++ append.occurrences)

theorem Collect.occurrences_eq {entries : List (Entry Name Expression Span Text)} {before after : List
    (Definition Name Expression Span)}
    {diagnostics : List (Diagnostic Name Span)} (left right : Collect entries before after diagnostics) :
    left.occurrences = right.occurrences := congrArg Collect.occurrences (left.unique right)

omit [DecidableEq Name] in
/-- Missing lookup visits every definition and then the empty-list clause.
Provider guard actions are not included in `occurrences`. -/
theorem Lookup.missing_occurrences_length {name : Name} {definitions : List (Definition Name Expression Span)}
    (derivation : Lookup name definitions .missing) :
    derivation.occurrences.length = definitions.length + 1 := by
  induction definitions with
  | nil => cases derivation; rfl
  | cons head tail ih =>
      cases derivation with
      | tail _ _ _ rest => simp [Lookup.occurrences, ih rest]

omit [DecidableEq Name] in
theorem AppendDefinition.occurrences_length {before after : List (Definition Name Expression Span)}
    {definition : Definition Name Expression Span} (derivation : AppendDefinition before definition after) :
    derivation.occurrences.length = before.length + 1 := by
  induction derivation with
  | nil => rfl
  | cons head rest ih => simp [AppendDefinition.occurrences, ih]

omit [DecidableEq Name] in
theorem AppendDiagnostics.occurrences_length {left right after : List (Diagnostic Name Span)}
    (derivation : AppendDiagnostics left right after) :
    derivation.occurrences.length = left.length + 1 := by
  induction derivation with
  | nil => rfl
  | cons head rest ih => simp [AppendDiagnostics.occurrences, ih]

theorem lookup_missing_iff (name : Name) (definitions : List (Definition Name Expression Span)) :
    lookup name definitions = .missing ↔ name ∉ definitions.map Definition.name := by
  induction definitions with
  | nil => simp [lookup]
  | cons head tail ih =>
      by_cases equal : name = head.name
      · simp [lookup, equal]
      · simp [lookup, equal, ih]

/-- All entries are rules, and each new name is absent from the accumulated
environment. This states the all-fresh input case without referring to costs. -/
inductive FreshEntries : List (Entry Name Expression Span Text) → List (Definition Name Expression Span) →
    Prop where
  | nil (before : List (Definition Name Expression Span)) : FreshEntries [] before
  | rule (name : Name) (expression : Expression) (span : Span) {tail : List (Entry Name Expression Span Text)}
      {before : List (Definition Name Expression Span)}
      (fresh : name ∉ before.map Definition.name)
      (rest : FreshEntries tail (before ++ [⟨name, expression, span⟩])) :
      FreshEntries (.rule name expression span :: tail) before

/-- The all-fresh source-clause recurrence: lookup and ordered append each
traverse the current environment; the other fresh-step clauses contribute five.
This counts source clauses, not allocations, elapsed time, or provider actions. -/
def freshClauseWork (beforeLength : Nat) : Nat → Nat
  | 0 => 1
  | count + 1 => 2 * beforeLength + 5 + freshClauseWork (beforeLength + 1) count

theorem freshClauseWork_closed (beforeLength count : Nat) :
    freshClauseWork beforeLength count =
      count * count + 2 * (beforeLength * count) + 4 * count + 1 := by
  induction count generalizing beforeLength with
  | zero => simp [freshClauseWork]
  | succ count ih =>
      simp only [freshClauseWork, ih, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega

theorem Collect.fresh_occurrences_length {entries : List (Entry Name Expression Span Text)}
    {before after : List (Definition Name Expression Span)} {diagnostics : List (Diagnostic Name Span)}
    (derivation : Collect entries before after diagnostics) (fresh : FreshEntries entries before) :
    derivation.occurrences.length = freshClauseWork before.length entries.length := by
  induction fresh generalizing after diagnostics with
  | nil before => cases derivation; rfl
  | @rule name expression span tail before freshName freshRest ih =>
      cases derivation with
      | rule _ _ _ lookup step rest append =>
          have missing := lookup.result_eq.trans ((lookup_missing_iff name before).mpr freshName)
          cases missing
          cases step with
          | fresh insert =>
              have inserted := insert.result_eq
              cases inserted
              have restCount := ih rest
              have lookupCount := lookup.missing_occurrences_length
              have insertCount := insert.occurrences_length
              have appendCount := append.occurrences_length
              simp only [Collect.occurrences, DefinitionStep.occurrences, List.length_cons,
                List.length_append, lookupCount, insertCount, appendCount, List.length_nil,
                Nat.zero_add, restCount, freshClauseWork]
              omega

/-- The current all-fresh pass has quadratic source-clause work, independently
of any materialization overhead introduced by a target evaluator. -/
theorem Collect.fresh_occurrences_closed {entries : List (Entry Name Expression Span Text)}
    {before after : List (Definition Name Expression Span)} {diagnostics : List (Diagnostic Name Span)}
    (derivation : Collect entries before after diagnostics) (fresh : FreshEntries entries before) :
    derivation.occurrences.length = entries.length * entries.length +
      2 * (before.length * entries.length) + 4 * entries.length + 1 := by
  rw [derivation.fresh_occurrences_length fresh, freshClauseWork_closed]

theorem Collect.fresh_empty_occurrences_closed {entries : List (Entry Name Expression Span Text)}
    {after : List (Definition Name Expression Span)} {diagnostics : List (Diagnostic Name Span)}
    (derivation : Collect entries [] after diagnostics) (fresh : FreshEntries entries []) :
    derivation.occurrences.length = entries.length * entries.length + 4 * entries.length + 1 := by
  simpa using derivation.fresh_occurrences_closed fresh

omit [DecidableEq Name] in
theorem two_distinct_rules_fresh (name₁ : Name) (expression₁ : Expression) (span₁ : Span) (name₂ : Name)
    (expression₂ : Expression) (span₂ : Span)
    (different : name₁ ≠ name₂) :
    FreshEntries (Text := Text) [.rule name₁ expression₁ span₁, .rule name₂ expression₂ span₂] [] := by
  apply FreshEntries.rule _ _ _ (by simp)
  apply FreshEntries.rule _ _ _ (by simpa using Ne.symm different)
  exact .nil _

omit [DecidableEq Name] in
/-- The all-fresh cost law does not apply to a sequence repeating a name. -/
theorem duplicate_rules_not_fresh (name : Name) (expression₁ : Expression) (span₁ : Span) (expression₂ :
    Expression) (span₂ : Span) :
    ¬ FreshEntries (Text := Text) [.rule name expression₁ span₁, .rule name expression₂ span₂] [] := by
  intro fresh
  cases fresh with
  | rule _ _ _ _ rest =>
      cases rest with
      | rule _ _ _ impossible _ => simp at impossible

/-- First-match lookup cannot return the expression or span of a later name copy. -/
@[simp] theorem lookup_first (name : Name) (expression : Expression) (span : Span) (tail : List (Definition
    Name Expression Span)) :
    lookup name (⟨name, expression, span⟩ :: tail) = .found expression span := by
  simp [lookup]

/-- Skipped comments/blanks do not insert or reorder definitions or diagnostics. -/
theorem collect_nonrules (text : Text) (commentSpan : Span) (blankSpan : Span)
    (entries : List (Entry Name Expression Span Text)) (before : List (Definition Name Expression Span)) :
    collect (.comment text commentSpan :: .blank blankSpan :: entries) before =
      collect entries before := rfl

/-- Different declaration occurrences remain ordered even when their names coincide. -/
theorem collect_duplicate_order (name : Name) (firstExpression : Expression) (firstSpan : Span) (expression₁ :
    Expression) (span₁ : Span) (expression₂ : Expression) (span₂ : Span) (tail : List (Definition Name
    Expression Span)) :
    collect (Text := Text) [.rule name expression₁ span₁, .rule name expression₂ span₂]
      (⟨name, firstExpression, firstSpan⟩ :: tail) =
      (⟨name, firstExpression, firstSpan⟩ :: tail,
        [.duplicate name firstSpan span₁, .duplicate name firstSpan span₂]) := by
  simp [collect, definitionStep]

/-- Even equal diagnostics occur twice; their list cannot be replaced by its set image. -/
theorem duplicate_occurrences_not_collapsed (name : Name) (firstExpression : Expression) (firstSpan : Span)
    (expression : Expression) (duplicateSpan : Span) (tail : List (Definition Name Expression Span)) :
    (collect (Text := Text) [.rule name expression duplicateSpan, .rule name expression duplicateSpan]
      (⟨name, firstExpression, firstSpan⟩ :: tail)).2 ≠
      [.duplicate name firstSpan duplicateSpan] := by
  rw [collect_duplicate_order]
  intro collapsed
  have lengths := congrArg List.length collapsed
  simp at lengths

/-- Concrete mixed-entry execution retains the first declaration and both duplicate origins. -/
theorem collect_first_declaration_retained (name : Name) (firstExpression : Expression) (firstSpan : Span)
    (text : Text) (commentSpan : Span) (blankSpan : Span) (expression₁ : Expression) (span₁ : Span)
    (expression₂ : Expression) (span₂ : Span) :
    collect (Text := Text) [.rule name firstExpression firstSpan, .comment text commentSpan,
      .blank blankSpan, .rule name expression₁ span₁, .rule name expression₂ span₂] [] =
      ([⟨name, firstExpression, firstSpan⟩],
        [.duplicate name firstSpan span₁, .duplicate name firstSpan span₂]) := by
  simp [collect, lookup, definitionStep]


end Mettapedia.GSLT.Parsing.PlainBnfDeclarationSemantics
