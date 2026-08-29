import Mettapedia.GSLT.Parsing.CompilerCorrespondence

/-!
# Scannerless syntax-GSLT guard correspondence

EOF and positive lookahead depend on a production's position in the physical
input, not only on the substring it consumes.  This module therefore gives
the normalized guard fragment an explicit full-input/start/stop semantics.
Source and compiled judgments remain distinct, and guard compilation is proved
in both directions.
-/

namespace Mettapedia.GSLT.Parsing.GuardCorrespondence

open CompilerCorrespondence

inductive SourceGuard where
  | atEnd
  | nextIn (codepoints : List Codepoint) (allowEof : Bool)
  | lookahead (category : Category)
  deriving DecidableEq, Repr

structure SourceRule where
  sourceRule : RuleId
  category : Category
  symbols : List SourceSymbol
  guards : List SourceGuard
  deriving DecidableEq, Repr

structure SourceDefinition where
  start : Category
  rules : List SourceRule
  deriving DecidableEq, Repr

inductive CompiledGuard where
  | atEnd
  | nextIn (codepoints : List Codepoint) (allowEof : Bool)
  | lookahead (category : Category)
  deriving DecidableEq, Repr

structure CompiledProduction where
  label : RuleId
  category : Category
  symbols : List CompiledSymbol
  guards : List CompiledGuard
  sourceRule : RuleId
  deriving DecidableEq, Repr

structure CompiledGrammar where
  start : Category
  productions : List CompiledProduction
  deriving DecidableEq, Repr

def compileGuard : SourceGuard → CompiledGuard
  | .atEnd => .atEnd
  | .nextIn codepoints allowEof => .nextIn codepoints allowEof
  | .lookahead category => .lookahead category

def compileRule (rule : SourceRule) : CompiledProduction :=
  { label := rule.sourceRule
    category := rule.category
    symbols := rule.symbols.map compileSymbol
    guards := rule.guards.map compileGuard
    sourceRule := rule.sourceRule }

def compile (presentation : SourceDefinition) : CompiledGrammar :=
  { start := presentation.start
    productions := presentation.rules.map compileRule }

def decodeSymbol : CompiledSymbol → Option SourceSymbol
  | .terminal codepoint => some (.exact codepoint)
  | .anyTerminal => some .any
  | .oneOfTerminal _ => none
  | .nonterminal category => some (.call category)

def decodeSymbols : List CompiledSymbol → Option (List SourceSymbol)
  | [] => some []
  | symbol :: symbols => do
      let sourceSymbol ← decodeSymbol symbol
      let sourceSymbols ← decodeSymbols symbols
      pure (sourceSymbol :: sourceSymbols)

def decodeGuard : CompiledGuard → SourceGuard
  | .atEnd => .atEnd
  | .nextIn codepoints allowEof => .nextIn codepoints allowEof
  | .lookahead category => .lookahead category

@[simp] theorem decode_compileSymbol (symbol : SourceSymbol) :
    decodeSymbol (compileSymbol symbol) = some symbol := by
  cases symbol <;> rfl

@[simp] theorem decode_compileSymbols (symbols : List SourceSymbol) :
    decodeSymbols (symbols.map compileSymbol) = some symbols := by
  induction symbols with
  | nil => rfl
  | cons symbol symbols inductionHypothesis =>
      simp [decodeSymbols, inductionHypothesis]

@[simp] theorem decode_compileGuard (guard : SourceGuard) :
    decodeGuard (compileGuard guard) = guard := by
  cases guard <;> rfl

mutual
  /-- Source evaluation at an exact span of the physical input. -/
  inductive SourceDerivesAt (presentation : SourceDefinition)
      (fullInput : List Codepoint) :
      Category → Nat → Nat → ParseTree → Prop where
    | apply (rule : SourceRule)
        (member : rule ∈ presentation.rules)
        (body : SourceBodyDerivesAt presentation fullInput rule.symbols
          start stop children)
        (guards : SourceGuardsHold presentation fullInput rule.guards stop) :
        SourceDerivesAt presentation fullInput rule.category start stop
          (.node rule.sourceRule rule.category children)

  /-- Left-to-right source evaluation with exact cursor composition. -/
  inductive SourceBodyDerivesAt (presentation : SourceDefinition)
      (fullInput : List Codepoint) :
      List SourceSymbol → Nat → Nat → List ParseTree → Prop where
    | nil : SourceBodyDerivesAt presentation fullInput [] cursor cursor []
    | exact
        (lookup : fullInput[start]? = some codepoint)
        (rest : SourceBodyDerivesAt presentation fullInput symbols
          (start + 1) stop children) :
        SourceBodyDerivesAt presentation fullInput
          (.exact codepoint :: symbols) start stop
          (.terminal codepoint :: children)
    | any
        (lookup : fullInput[start]? = some codepoint)
        (rest : SourceBodyDerivesAt presentation fullInput symbols
          (start + 1) stop children) :
        SourceBodyDerivesAt presentation fullInput
          (.any :: symbols) start stop (.terminal codepoint :: children)
    | call
        (head : SourceDerivesAt presentation fullInput category start middle tree)
        (rest : SourceBodyDerivesAt presentation fullInput symbols
          middle stop children) :
        SourceBodyDerivesAt presentation fullInput
          (.call category :: symbols) start stop (tree :: children)

  /-- Guards are zero-width constraints checked at the production's final
  cursor.  Lookahead establishes existence but does not consume its witness. -/
  inductive SourceGuardsHold (presentation : SourceDefinition)
      (fullInput : List Codepoint) :
      List SourceGuard → Nat → Prop where
    | nil : SourceGuardsHold presentation fullInput [] cursor
    | atEnd
        (endEq : cursor = fullInput.length)
        (rest : SourceGuardsHold presentation fullInput guards cursor) :
        SourceGuardsHold presentation fullInput (.atEnd :: guards) cursor
    | nextIn
        (lookup : fullInput[cursor]? = some codepoint)
        (member : codepoint ∈ codepoints)
        (rest : SourceGuardsHold presentation fullInput guards cursor) :
        SourceGuardsHold presentation fullInput
          (.nextIn codepoints allowEof :: guards) cursor
    | nextInEof
        (allowed : allowEof = true)
        (endEq : cursor = fullInput.length)
        (rest : SourceGuardsHold presentation fullInput guards cursor) :
        SourceGuardsHold presentation fullInput
          (.nextIn codepoints allowEof :: guards) cursor
    | lookahead
        (witness : SourceDerivesAt presentation fullInput category
          cursor witnessStop tree)
        (rest : SourceGuardsHold presentation fullInput guards cursor) :
        SourceGuardsHold presentation fullInput
          (.lookahead category :: guards) cursor
end

mutual
  /-- The distinct compiled span semantics. -/
  inductive CompiledDerivesAt (grammar : CompiledGrammar)
      (fullInput : List Codepoint) :
      Category → Nat → Nat → ParseTree → Prop where
    | apply (production : CompiledProduction)
        (member : production ∈ grammar.productions)
        (body : CompiledBodyDerivesAt grammar fullInput production.symbols
          start stop children)
        (guards : CompiledGuardsHold grammar fullInput production.guards stop) :
        CompiledDerivesAt grammar fullInput production.category start stop
          (.node production.sourceRule production.category children)

  inductive CompiledBodyDerivesAt (grammar : CompiledGrammar)
      (fullInput : List Codepoint) :
      List CompiledSymbol → Nat → Nat → List ParseTree → Prop where
    | nil : CompiledBodyDerivesAt grammar fullInput [] cursor cursor []
    | terminal
        (lookup : fullInput[start]? = some codepoint)
        (rest : CompiledBodyDerivesAt grammar fullInput symbols
          (start + 1) stop children) :
        CompiledBodyDerivesAt grammar fullInput
          (.terminal codepoint :: symbols) start stop
          (.terminal codepoint :: children)
    | anyTerminal
        (lookup : fullInput[start]? = some codepoint)
        (rest : CompiledBodyDerivesAt grammar fullInput symbols
          (start + 1) stop children) :
        CompiledBodyDerivesAt grammar fullInput
          (.anyTerminal :: symbols) start stop (.terminal codepoint :: children)
    | oneOfTerminal
        (lookup : fullInput[start]? = some codepoint)
        (member : codepoint ∈ codepoints)
        (rest : CompiledBodyDerivesAt grammar fullInput symbols
          (start + 1) stop children) :
        CompiledBodyDerivesAt grammar fullInput
          (.oneOfTerminal codepoints :: symbols) start stop
          (.terminal codepoint :: children)
    | nonterminal
        (head : CompiledDerivesAt grammar fullInput category start middle tree)
        (rest : CompiledBodyDerivesAt grammar fullInput symbols
          middle stop children) :
        CompiledBodyDerivesAt grammar fullInput
          (.nonterminal category :: symbols) start stop (tree :: children)

  inductive CompiledGuardsHold (grammar : CompiledGrammar)
      (fullInput : List Codepoint) :
      List CompiledGuard → Nat → Prop where
    | nil : CompiledGuardsHold grammar fullInput [] cursor
    | atEnd
        (endEq : cursor = fullInput.length)
        (rest : CompiledGuardsHold grammar fullInput guards cursor) :
        CompiledGuardsHold grammar fullInput (.atEnd :: guards) cursor
    | nextIn
        (lookup : fullInput[cursor]? = some codepoint)
        (member : codepoint ∈ codepoints)
        (rest : CompiledGuardsHold grammar fullInput guards cursor) :
        CompiledGuardsHold grammar fullInput
          (.nextIn codepoints allowEof :: guards) cursor
    | nextInEof
        (allowed : allowEof = true)
        (endEq : cursor = fullInput.length)
        (rest : CompiledGuardsHold grammar fullInput guards cursor) :
        CompiledGuardsHold grammar fullInput
          (.nextIn codepoints allowEof :: guards) cursor
    | lookahead
        (witness : CompiledDerivesAt grammar fullInput category
          cursor witnessStop tree)
        (rest : CompiledGuardsHold grammar fullInput guards cursor) :
        CompiledGuardsHold grammar fullInput
          (.lookahead category :: guards) cursor
end

mutual
  private def preserveDerivation
      {presentation : SourceDefinition} {fullInput category start stop tree}
      (derivation : SourceDerivesAt presentation fullInput category start stop tree) :
      CompiledDerivesAt (compile presentation) fullInput category start stop tree :=
    match derivation with
    | .apply rule member body guards =>
        .apply (compileRule rule)
          (List.mem_map.mpr ⟨rule, member, rfl⟩)
          (preserveBody body) (preserveGuards guards)

  private def preserveBody
      {presentation : SourceDefinition} {fullInput symbols start stop children}
      (derivation : SourceBodyDerivesAt presentation fullInput symbols
        start stop children) :
      CompiledBodyDerivesAt (compile presentation) fullInput
        (symbols.map compileSymbol) start stop children :=
    match derivation with
    | .nil => .nil
    | .exact lookup rest => .terminal lookup (preserveBody rest)
    | .any lookup rest => .anyTerminal lookup (preserveBody rest)
    | .call head rest =>
        .nonterminal (preserveDerivation head) (preserveBody rest)

  private def preserveGuards
      {presentation : SourceDefinition} {fullInput guards cursor}
      (derivation : SourceGuardsHold presentation fullInput guards cursor) :
      CompiledGuardsHold (compile presentation) fullInput
        (guards.map compileGuard) cursor :=
    match derivation with
    | .nil => .nil
    | .atEnd endEq rest => .atEnd endEq (preserveGuards rest)
    | .nextIn lookup member rest =>
        .nextIn lookup member (preserveGuards rest)
    | .nextInEof allowed endEq rest =>
        .nextInEof allowed endEq (preserveGuards rest)
    | .lookahead witness rest =>
        .lookahead (preserveDerivation witness) (preserveGuards rest)
end

theorem compile_preserves
    {presentation : SourceDefinition} {fullInput category start stop tree}
    (derivation : SourceDerivesAt presentation fullInput category start stop tree) :
    CompiledDerivesAt (compile presentation) fullInput category start stop tree :=
  preserveDerivation derivation

theorem compile_reflects
    {presentation : SourceDefinition} {fullInput category start stop tree}
    (derivation : CompiledDerivesAt (compile presentation) fullInput
      category start stop tree) :
    SourceDerivesAt presentation fullInput category start stop tree := by
  exact CompiledDerivesAt.rec
    (motive_1 := fun category start stop tree _ =>
      SourceDerivesAt presentation fullInput category start stop tree)
    (motive_2 := fun symbols start stop children _ =>
      match decodeSymbols symbols with
      | none => True
      | some sourceSymbols =>
          SourceBodyDerivesAt presentation fullInput sourceSymbols
            start stop children)
    (motive_3 := fun guards cursor _ =>
      SourceGuardsHold presentation fullInput
        (guards.map decodeGuard) cursor)
    (fun {start} {stop} {children} production member _ _ bodyIH guardsIH => by
      change production ∈ presentation.rules.map compileRule at member
      obtain ⟨rule, ruleMember, compiledRule⟩ := List.mem_map.mp member
      subst production
      have sourceBody : SourceBodyDerivesAt presentation fullInput
          rule.symbols start stop children := by
        simpa [compileRule] using bodyIH
      have sourceGuards : SourceGuardsHold presentation fullInput
          rule.guards stop := by
        simpa [compileRule, List.map_map, Function.comp_def] using guardsIH
      simpa [compileRule] using
        SourceDerivesAt.apply rule ruleMember sourceBody sourceGuards)
    (by exact SourceBodyDerivesAt.nil)
    (fun {start} {codepoint} {symbols} {stop} {children}
        lookup _ restIH => by
      cases decoded : decodeSymbols symbols with
      | none => simp [decodeSymbols, decodeSymbol, decoded]
      | some sourceSymbols =>
          have sourceRest : SourceBodyDerivesAt presentation fullInput
              sourceSymbols (start + 1) stop children := by
            simpa [decoded] using restIH
          simpa [decodeSymbols, decodeSymbol, decoded] using
            SourceBodyDerivesAt.exact lookup sourceRest)
    (fun {start} {codepoint} {symbols} {stop} {children}
        lookup _ restIH => by
      cases decoded : decodeSymbols symbols with
      | none => simp [decodeSymbols, decodeSymbol, decoded]
      | some sourceSymbols =>
          have sourceRest : SourceBodyDerivesAt presentation fullInput
              sourceSymbols (start + 1) stop children := by
            simpa [decoded] using restIH
          simpa [decodeSymbols, decodeSymbol, decoded] using
            SourceBodyDerivesAt.any lookup sourceRest)
    (fun _ _ _ _ => by simp [decodeSymbols, decodeSymbol])
    (fun {category} {start} {middle} {tree} {symbols} {stop} {children}
        _ _ headIH restIH => by
      cases decoded : decodeSymbols symbols with
      | none => simp [decodeSymbols, decodeSymbol, decoded]
      | some sourceSymbols =>
          have sourceRest : SourceBodyDerivesAt presentation fullInput
              sourceSymbols middle stop children := by
            simpa [decoded] using restIH
          simpa [decodeSymbols, decodeSymbol, decoded] using
            SourceBodyDerivesAt.call headIH sourceRest)
    (by exact SourceGuardsHold.nil)
    (fun endEq _ restIH => by
      simpa [decodeGuard] using SourceGuardsHold.atEnd endEq restIH)
    (fun lookup member _ restIH => by
      simpa [decodeGuard] using
        SourceGuardsHold.nextIn lookup member restIH)
    (fun allowed endEq _ restIH => by
      simpa [decodeGuard] using
        SourceGuardsHold.nextInEof allowed endEq restIH)
    (fun _ _ witnessIH restIH => by
      simpa [decodeGuard] using
        SourceGuardsHold.lookahead witnessIH restIH)
    derivation

def sourceResults (presentation : SourceDefinition)
    (input : List Codepoint) : Set ParseTree :=
  { tree | SourceDerivesAt presentation input presentation.start
      0 input.length tree }

def compiledResults (presentation : SourceDefinition)
    (input : List Codepoint) : Set ParseTree :=
  { tree | CompiledDerivesAt (compile presentation) input presentation.start
      0 input.length tree }

theorem complete_result_set_agreement
    (presentation : SourceDefinition) (input : List Codepoint) :
    compiledResults presentation input = sourceResults presentation input := by
  ext tree
  constructor
  · exact compile_reflects
  · exact compile_preserves

def Ambiguous (results : Set ParseTree) : Prop :=
  ∃ first ∈ results, ∃ second ∈ results, first ≠ second

theorem ambiguity_agreement
    (presentation : SourceDefinition) (input : List Codepoint) :
    Ambiguous (compiledResults presentation input) ↔
      Ambiguous (sourceResults presentation input) := by
  rw [complete_result_set_agreement]

/-! ## Administrative-label plan correspondence -/

/-- Production equality at every semantic field.  Backend-local labels are
excluded because parse trees and certificates retain `sourceRule` instead. -/
def SameProductionShape
    (left right : CompiledProduction) : Prop :=
  left.category = right.category ∧
  left.symbols = right.symbols ∧
  left.guards = right.guards ∧
  left.sourceRule = right.sourceRule

private instance sameProductionShapeDecidable
    (left right : CompiledProduction) :
    Decidable (SameProductionShape left right) := by
  unfold SameProductionShape
  infer_instance

structure PlanCorrespondence (raw emitted : CompiledGrammar) : Prop where
  start_eq : emitted.start = raw.start
  forward : ∀ rawProduction, rawProduction ∈ raw.productions →
    ∃ emittedProduction, emittedProduction ∈ emitted.productions ∧
      SameProductionShape emittedProduction rawProduction
  backward : ∀ emittedProduction, emittedProduction ∈ emitted.productions →
    ∃ rawProduction, rawProduction ∈ raw.productions ∧
      SameProductionShape rawProduction emittedProduction

private def sameProductionShapeBool
    (left right : CompiledProduction) : Bool :=
  decide (SameProductionShape left right)

def validatePlanCorrespondence
    (raw emitted : CompiledGrammar) : Bool :=
  decide (emitted.start = raw.start) &&
  (raw.productions.all fun rawProduction =>
    emitted.productions.any fun emittedProduction =>
      sameProductionShapeBool emittedProduction rawProduction) &&
  (emitted.productions.all fun emittedProduction =>
    raw.productions.any fun rawProduction =>
      sameProductionShapeBool rawProduction emittedProduction)

theorem validatePlanCorrespondence_sound
    {raw emitted : CompiledGrammar}
    (accepted : validatePlanCorrespondence raw emitted = true) :
    PlanCorrespondence raw emitted := by
  simp only [validatePlanCorrespondence, Bool.and_eq_true,
    List.all_eq_true, List.any_eq_true, sameProductionShapeBool,
    decide_eq_true_eq] at accepted
  obtain ⟨startAndForward, backwardAccepted⟩ := accepted
  obtain ⟨startEq, forwardAccepted⟩ := startAndForward
  exact ⟨startEq, forwardAccepted, backwardAccepted⟩

theorem validatePlanCorrespondence_complete
    {raw emitted : CompiledGrammar}
    (witness : PlanCorrespondence raw emitted) :
    validatePlanCorrespondence raw emitted = true := by
  simp only [validatePlanCorrespondence, Bool.and_eq_true,
    List.all_eq_true, List.any_eq_true, sameProductionShapeBool,
    decide_eq_true_eq]
  exact ⟨⟨witness.start_eq, witness.forward⟩, witness.backward⟩

theorem validatePlanCorrespondence_iff
    {raw emitted : CompiledGrammar} :
    validatePlanCorrespondence raw emitted = true ↔
      PlanCorrespondence raw emitted :=
  ⟨validatePlanCorrespondence_sound, validatePlanCorrespondence_complete⟩

mutual
  private def planPreserveDerivation
      {raw emitted : CompiledGrammar}
      (witness : PlanCorrespondence raw emitted)
      {fullInput category start stop tree}
      (derivation : CompiledDerivesAt raw fullInput category start stop tree) :
      CompiledDerivesAt emitted fullInput category start stop tree :=
    match derivation with
    | .apply rawProduction member body guards => by
        obtain ⟨emittedProduction, emittedMember, categoryEq, symbolsEq,
          guardsEq, sourceRuleEq⟩ := witness.forward rawProduction member
        have emittedBody := planPreserveBody witness body
        have emittedGuards := planPreserveGuards witness guards
        rw [← symbolsEq] at emittedBody
        rw [← guardsEq] at emittedGuards
        simpa [categoryEq, sourceRuleEq] using
          CompiledDerivesAt.apply emittedProduction emittedMember
            emittedBody emittedGuards

  private def planPreserveBody
      {raw emitted : CompiledGrammar}
      (witness : PlanCorrespondence raw emitted)
      {fullInput symbols start stop children}
      (derivation : CompiledBodyDerivesAt raw fullInput symbols
        start stop children) :
      CompiledBodyDerivesAt emitted fullInput symbols start stop children :=
    match derivation with
    | .nil => .nil
    | .terminal lookup rest =>
        .terminal lookup (planPreserveBody witness rest)
    | .anyTerminal lookup rest =>
        .anyTerminal lookup (planPreserveBody witness rest)
    | .oneOfTerminal lookup member rest =>
        .oneOfTerminal lookup member (planPreserveBody witness rest)
    | .nonterminal head rest =>
        .nonterminal (planPreserveDerivation witness head)
          (planPreserveBody witness rest)

  private def planPreserveGuards
      {raw emitted : CompiledGrammar}
      (witness : PlanCorrespondence raw emitted)
      {fullInput guards cursor}
      (derivation : CompiledGuardsHold raw fullInput guards cursor) :
      CompiledGuardsHold emitted fullInput guards cursor :=
    match derivation with
    | .nil => .nil
    | .atEnd endEq rest =>
        .atEnd endEq (planPreserveGuards witness rest)
    | .nextIn lookup member rest =>
        .nextIn lookup member (planPreserveGuards witness rest)
    | .nextInEof allowed endEq rest =>
        .nextInEof allowed endEq (planPreserveGuards witness rest)
    | .lookahead lookahead rest =>
        .lookahead (planPreserveDerivation witness lookahead)
          (planPreserveGuards witness rest)
end

theorem planCorrespondence_preserves
    {raw emitted : CompiledGrammar}
    (witness : PlanCorrespondence raw emitted)
    {fullInput category start stop tree}
    (derivation : CompiledDerivesAt raw fullInput category start stop tree) :
    CompiledDerivesAt emitted fullInput category start stop tree :=
  planPreserveDerivation witness derivation

mutual
  private def planReflectDerivation
      {raw emitted : CompiledGrammar}
      (witness : PlanCorrespondence raw emitted)
      {fullInput category start stop tree}
      (derivation : CompiledDerivesAt emitted fullInput category start stop tree) :
      CompiledDerivesAt raw fullInput category start stop tree :=
    match derivation with
    | .apply emittedProduction member body guards => by
        obtain ⟨rawProduction, rawMember, categoryEq, symbolsEq,
          guardsEq, sourceRuleEq⟩ := witness.backward emittedProduction member
        have rawBody := planReflectBody witness body
        have rawGuards := planReflectGuards witness guards
        rw [← symbolsEq] at rawBody
        rw [← guardsEq] at rawGuards
        simpa [categoryEq, sourceRuleEq] using
          CompiledDerivesAt.apply rawProduction rawMember rawBody rawGuards

  private def planReflectBody
      {raw emitted : CompiledGrammar}
      (witness : PlanCorrespondence raw emitted)
      {fullInput symbols start stop children}
      (derivation : CompiledBodyDerivesAt emitted fullInput symbols
        start stop children) :
      CompiledBodyDerivesAt raw fullInput symbols start stop children :=
    match derivation with
    | .nil => .nil
    | .terminal lookup rest =>
        .terminal lookup (planReflectBody witness rest)
    | .anyTerminal lookup rest =>
        .anyTerminal lookup (planReflectBody witness rest)
    | .oneOfTerminal lookup member rest =>
        .oneOfTerminal lookup member (planReflectBody witness rest)
    | .nonterminal head rest =>
        .nonterminal (planReflectDerivation witness head)
          (planReflectBody witness rest)

  private def planReflectGuards
      {raw emitted : CompiledGrammar}
      (witness : PlanCorrespondence raw emitted)
      {fullInput guards cursor}
      (derivation : CompiledGuardsHold emitted fullInput guards cursor) :
      CompiledGuardsHold raw fullInput guards cursor :=
    match derivation with
    | .nil => .nil
    | .atEnd endEq rest =>
        .atEnd endEq (planReflectGuards witness rest)
    | .nextIn lookup member rest =>
        .nextIn lookup member (planReflectGuards witness rest)
    | .nextInEof allowed endEq rest =>
        .nextInEof allowed endEq (planReflectGuards witness rest)
    | .lookahead lookahead rest =>
        .lookahead (planReflectDerivation witness lookahead)
          (planReflectGuards witness rest)
end

theorem planCorrespondence_reflects
    {raw emitted : CompiledGrammar}
    (witness : PlanCorrespondence raw emitted)
    {fullInput category start stop tree}
    (derivation : CompiledDerivesAt emitted fullInput category start stop tree) :
    CompiledDerivesAt raw fullInput category start stop tree :=
  planReflectDerivation witness derivation

def grammarResults (grammar : CompiledGrammar)
    (input : List Codepoint) : Set ParseTree :=
  { tree | CompiledDerivesAt grammar input grammar.start 0 input.length tree }

theorem planCorrespondence_result_set_agreement
    {raw emitted : CompiledGrammar}
    (witness : PlanCorrespondence raw emitted)
    (input : List Codepoint) :
    grammarResults emitted input = grammarResults raw input := by
  ext tree
  constructor
  · intro derivation
    simpa [grammarResults, witness.start_eq] using
      planCorrespondence_reflects witness derivation
  · intro derivation
    simpa [grammarResults, witness.start_eq] using
      planCorrespondence_preserves witness derivation

/-! ## Guard-preserving finite-terminal-set compaction -/

/-- A checked terminal compaction for guarded plans.  Production labels may
change, but category, source identity, and guards are preserved exactly. -/
structure TerminalCompaction (raw compacted : CompiledGrammar) : Prop where
  start_eq : compacted.start = raw.start
  forward : ∀ rawProduction, rawProduction ∈ raw.productions →
    ∃ compactedProduction, compactedProduction ∈ compacted.productions ∧
      compactedProduction.category = rawProduction.category ∧
      compactedProduction.guards = rawProduction.guards ∧
      compactedProduction.sourceRule = rawProduction.sourceRule ∧
      SymbolsExpand rawProduction.symbols compactedProduction.symbols
  backward : ∀ compactedProduction,
    compactedProduction ∈ compacted.productions →
    ∀ rawSymbols, SymbolsExpand rawSymbols compactedProduction.symbols →
      ∃ rawProduction, rawProduction ∈ raw.productions ∧
        rawProduction.category = compactedProduction.category ∧
        rawProduction.guards = compactedProduction.guards ∧
        rawProduction.sourceRule = compactedProduction.sourceRule ∧
        rawProduction.symbols = rawSymbols

private def forwardTerminalCompactionMatch
    (rawProduction compactedProduction : CompiledProduction) : Bool :=
  decide (
    compactedProduction.category = rawProduction.category ∧
    compactedProduction.guards = rawProduction.guards ∧
    compactedProduction.sourceRule = rawProduction.sourceRule ∧
    rawProduction.symbols ∈ expandSymbols compactedProduction.symbols)

private def backwardTerminalCompactionMatch
    (rawProduction compactedProduction : CompiledProduction)
    (rawSymbols : List CompiledSymbol) : Bool :=
  decide (
    rawProduction.category = compactedProduction.category ∧
    rawProduction.guards = compactedProduction.guards ∧
    rawProduction.sourceRule = compactedProduction.sourceRule ∧
    rawProduction.symbols = rawSymbols)

/-- Fail-closed executable validation of guarded terminal compaction. -/
def validateTerminalCompaction
    (raw compacted : CompiledGrammar) : Bool :=
  decide (compacted.start = raw.start) &&
  (raw.productions.all fun rawProduction =>
    compacted.productions.any fun compactedProduction =>
      forwardTerminalCompactionMatch rawProduction compactedProduction) &&
  (compacted.productions.all fun compactedProduction =>
    (expandSymbols compactedProduction.symbols).all fun rawSymbols =>
      raw.productions.any fun rawProduction =>
        backwardTerminalCompactionMatch
          rawProduction compactedProduction rawSymbols)

theorem validateTerminalCompaction_sound
    {raw compacted : CompiledGrammar}
    (accepted : validateTerminalCompaction raw compacted = true) :
    TerminalCompaction raw compacted := by
  simp only [validateTerminalCompaction, Bool.and_eq_true,
    List.all_eq_true, List.any_eq_true, forwardTerminalCompactionMatch,
    backwardTerminalCompactionMatch, decide_eq_true_eq] at accepted
  obtain ⟨startAndForward, backwardAccepted⟩ := accepted
  obtain ⟨startEq, forwardAccepted⟩ := startAndForward
  constructor
  · exact startEq
  · intro rawProduction rawMember
    obtain ⟨compactedProduction, compactedMember, categoryEq, guardsEq,
      sourceRuleEq, symbolsMember⟩ := forwardAccepted rawProduction rawMember
    exact ⟨compactedProduction, compactedMember, categoryEq, guardsEq,
      sourceRuleEq, mem_expandSymbols_iff.mp symbolsMember⟩
  · intro compactedProduction compactedMember rawSymbols expansion
    have symbolsMember :
        rawSymbols ∈ expandSymbols compactedProduction.symbols :=
      mem_expandSymbols_iff.mpr expansion
    obtain ⟨rawProduction, rawMember, categoryEq, guardsEq,
      sourceRuleEq, symbolsEq⟩ :=
      backwardAccepted compactedProduction compactedMember
        rawSymbols symbolsMember
    exact ⟨rawProduction, rawMember, categoryEq, guardsEq,
      sourceRuleEq, symbolsEq⟩

theorem validateTerminalCompaction_complete
    {raw compacted : CompiledGrammar}
    (witness : TerminalCompaction raw compacted) :
    validateTerminalCompaction raw compacted = true := by
  simp only [validateTerminalCompaction, Bool.and_eq_true,
    List.all_eq_true, List.any_eq_true, forwardTerminalCompactionMatch,
    backwardTerminalCompactionMatch, decide_eq_true_eq]
  constructor
  · constructor
    · exact witness.start_eq
    · intro rawProduction rawMember
      obtain ⟨compactedProduction, compactedMember, categoryEq, guardsEq,
        sourceRuleEq, expansion⟩ := witness.forward rawProduction rawMember
      exact ⟨compactedProduction, compactedMember, categoryEq, guardsEq,
        sourceRuleEq, mem_expandSymbols_iff.mpr expansion⟩
  · intro compactedProduction compactedMember rawSymbols symbolsMember
    have expansion : SymbolsExpand rawSymbols compactedProduction.symbols :=
      mem_expandSymbols_iff.mp symbolsMember
    obtain ⟨rawProduction, rawMember, categoryEq, guardsEq,
      sourceRuleEq, symbolsEq⟩ :=
      witness.backward compactedProduction compactedMember rawSymbols expansion
    exact ⟨rawProduction, rawMember, categoryEq, guardsEq,
      sourceRuleEq, symbolsEq⟩

theorem validateTerminalCompaction_iff
    {raw compacted : CompiledGrammar} :
    validateTerminalCompaction raw compacted = true ↔
      TerminalCompaction raw compacted :=
  ⟨validateTerminalCompaction_sound, validateTerminalCompaction_complete⟩

mutual
  private def preserveTerminalCompactionDerivation
      {raw compacted : CompiledGrammar}
      (witness : TerminalCompaction raw compacted)
      {fullInput category start stop tree}
      (derivation : CompiledDerivesAt raw fullInput
        category start stop tree) :
      CompiledDerivesAt compacted fullInput category start stop tree :=
    match derivation with
    | .apply rawProduction member body guards => by
        obtain ⟨compactedProduction, compactedMember, categoryEq, guardsEq,
          sourceRuleEq, expansion⟩ := witness.forward rawProduction member
        have compactedBody :=
          preserveTerminalCompactionBody witness body expansion
        have compactedGuards :=
          preserveTerminalCompactionGuards witness guards
        rw [← guardsEq] at compactedGuards
        simpa [categoryEq, sourceRuleEq] using
          CompiledDerivesAt.apply compactedProduction compactedMember
            compactedBody compactedGuards

  private def preserveTerminalCompactionBody
      {raw compacted : CompiledGrammar}
      (witness : TerminalCompaction raw compacted)
      {fullInput rawSymbols compactedSymbols start stop trees}
      (derivation : CompiledBodyDerivesAt raw fullInput rawSymbols
        start stop trees)
      (expansion : SymbolsExpand rawSymbols compactedSymbols) :
      CompiledBodyDerivesAt compacted fullInput compactedSymbols
        start stop trees :=
    match expansion, derivation with
    | .nil, .nil => .nil
    | .terminal restExpansion, .terminal lookup rest =>
        .terminal lookup
          (preserveTerminalCompactionBody witness rest restExpansion)
    | .terminalSet member restExpansion, .terminal lookup rest =>
        .oneOfTerminal lookup member
          (preserveTerminalCompactionBody witness rest restExpansion)
    | .anyTerminal restExpansion, .anyTerminal lookup rest =>
        .anyTerminal lookup
          (preserveTerminalCompactionBody witness rest restExpansion)
    | .nonterminal restExpansion, .nonterminal head rest =>
        .nonterminal (preserveTerminalCompactionDerivation witness head)
          (preserveTerminalCompactionBody witness rest restExpansion)

  private def preserveTerminalCompactionGuards
      {raw compacted : CompiledGrammar}
      (witness : TerminalCompaction raw compacted)
      {fullInput guards cursor}
      (derivation : CompiledGuardsHold raw fullInput guards cursor) :
      CompiledGuardsHold compacted fullInput guards cursor :=
    match derivation with
    | .nil => .nil
    | .atEnd endEq rest =>
        .atEnd endEq (preserveTerminalCompactionGuards witness rest)
    | .nextIn lookup member rest =>
        .nextIn lookup member
          (preserveTerminalCompactionGuards witness rest)
    | .nextInEof allowed endEq rest =>
        .nextInEof allowed endEq
          (preserveTerminalCompactionGuards witness rest)
    | .lookahead lookahead rest =>
        .lookahead (preserveTerminalCompactionDerivation witness lookahead)
          (preserveTerminalCompactionGuards witness rest)
end

theorem terminalCompaction_preserves
    {raw compacted : CompiledGrammar}
    (witness : TerminalCompaction raw compacted)
    {fullInput category start stop tree}
    (derivation : CompiledDerivesAt raw fullInput category start stop tree) :
    CompiledDerivesAt compacted fullInput category start stop tree :=
  preserveTerminalCompactionDerivation witness derivation

mutual
  private def reflectTerminalCompactionDerivation
      {raw compacted : CompiledGrammar}
      (witness : TerminalCompaction raw compacted)
      {fullInput category start stop tree}
      (derivation : CompiledDerivesAt compacted fullInput
        category start stop tree) :
      CompiledDerivesAt raw fullInput category start stop tree :=
    match derivation with
    | .apply compactedProduction member body guards => by
        obtain ⟨rawSymbols, expansion, rawBody⟩ :=
          reflectTerminalCompactionBody witness body
        obtain ⟨rawProduction, rawMember, categoryEq, guardsEq,
          sourceRuleEq, symbolsEq⟩ := witness.backward
            compactedProduction member rawSymbols expansion
        have rawGuards := reflectTerminalCompactionGuards witness guards
        rw [← symbolsEq] at rawBody
        rw [← guardsEq] at rawGuards
        simpa [categoryEq, sourceRuleEq] using
          CompiledDerivesAt.apply rawProduction rawMember rawBody rawGuards

  private def reflectTerminalCompactionBody
      {raw compacted : CompiledGrammar}
      (witness : TerminalCompaction raw compacted)
      {fullInput compactedSymbols start stop trees}
      (derivation : CompiledBodyDerivesAt compacted fullInput
        compactedSymbols start stop trees) :
      ∃ rawSymbols, SymbolsExpand rawSymbols compactedSymbols ∧
        CompiledBodyDerivesAt raw fullInput rawSymbols start stop trees :=
    match derivation with
    | .nil => ⟨[], .nil, .nil⟩
    | .terminal lookup rest => by
        obtain ⟨rawSymbols, expansion, rawRest⟩ :=
          reflectTerminalCompactionBody witness rest
        exact ⟨.terminal _ :: rawSymbols, .terminal expansion,
          .terminal lookup rawRest⟩
    | .anyTerminal lookup rest => by
        obtain ⟨rawSymbols, expansion, rawRest⟩ :=
          reflectTerminalCompactionBody witness rest
        exact ⟨.anyTerminal :: rawSymbols, .anyTerminal expansion,
          .anyTerminal lookup rawRest⟩
    | .oneOfTerminal lookup member rest => by
        obtain ⟨rawSymbols, expansion, rawRest⟩ :=
          reflectTerminalCompactionBody witness rest
        exact ⟨.terminal _ :: rawSymbols, .terminalSet member expansion,
          .terminal lookup rawRest⟩
    | .nonterminal head rest => by
        obtain ⟨rawSymbols, expansion, rawRest⟩ :=
          reflectTerminalCompactionBody witness rest
        exact ⟨.nonterminal _ :: rawSymbols, .nonterminal expansion,
          .nonterminal (reflectTerminalCompactionDerivation witness head)
            rawRest⟩

  private def reflectTerminalCompactionGuards
      {raw compacted : CompiledGrammar}
      (witness : TerminalCompaction raw compacted)
      {fullInput guards cursor}
      (derivation : CompiledGuardsHold compacted fullInput guards cursor) :
      CompiledGuardsHold raw fullInput guards cursor :=
    match derivation with
    | .nil => .nil
    | .atEnd endEq rest =>
        .atEnd endEq (reflectTerminalCompactionGuards witness rest)
    | .nextIn lookup member rest =>
        .nextIn lookup member
          (reflectTerminalCompactionGuards witness rest)
    | .nextInEof allowed endEq rest =>
        .nextInEof allowed endEq
          (reflectTerminalCompactionGuards witness rest)
    | .lookahead lookahead rest =>
        .lookahead (reflectTerminalCompactionDerivation witness lookahead)
          (reflectTerminalCompactionGuards witness rest)
end

theorem terminalCompaction_reflects
    {raw compacted : CompiledGrammar}
    (witness : TerminalCompaction raw compacted)
    {fullInput category start stop tree}
    (derivation : CompiledDerivesAt compacted fullInput
      category start stop tree) :
    CompiledDerivesAt raw fullInput category start stop tree :=
  reflectTerminalCompactionDerivation witness derivation

theorem terminalCompaction_result_set_agreement
    {raw compacted : CompiledGrammar}
    (witness : TerminalCompaction raw compacted)
    (input : List Codepoint) :
    grammarResults compacted input = grammarResults raw input := by
  ext tree
  constructor
  · intro derivation
    simpa [grammarResults, witness.start_eq] using
      terminalCompaction_reflects witness derivation
  · intro derivation
    simpa [grammarResults, witness.start_eq] using
      terminalCompaction_preserves witness derivation

/-! ## Guarded certificate replay -/

mutual
  inductive CertificateReplays (grammar : CompiledGrammar)
      (fullInput : List Codepoint) :
      Certificate → Category → Nat → Nat → ParseTree → Prop where
    | node (production : CompiledProduction)
        (member : production ∈ grammar.productions)
        (body : CertificateBodyReplays grammar fullInput production.symbols
          start stop certificates trees)
        (guards : CompiledGuardsHold grammar fullInput production.guards stop) :
        CertificateReplays grammar fullInput
          (.node production.sourceRule production.category start stop certificates)
          production.category start stop
          (.node production.sourceRule production.category trees)

  inductive CertificateBodyReplays (grammar : CompiledGrammar)
      (fullInput : List Codepoint) :
      List CompiledSymbol → Nat → Nat →
        List Certificate → List ParseTree → Prop where
    | nil : CertificateBodyReplays grammar fullInput [] cursor cursor [] []
    | terminal
        (lookup : fullInput[start]? = some codepoint)
        (rest : CertificateBodyReplays grammar fullInput symbols
          (start + 1) stop certificates trees) :
        CertificateBodyReplays grammar fullInput
          (.terminal codepoint :: symbols) start stop
          (.terminal codepoint start (start + 1) :: certificates)
          (.terminal codepoint :: trees)
    | anyTerminal
        (lookup : fullInput[start]? = some codepoint)
        (rest : CertificateBodyReplays grammar fullInput symbols
          (start + 1) stop certificates trees) :
        CertificateBodyReplays grammar fullInput
          (.anyTerminal :: symbols) start stop
          (.terminal codepoint start (start + 1) :: certificates)
          (.terminal codepoint :: trees)
    | oneOfTerminal
        (lookup : fullInput[start]? = some codepoint)
        (member : codepoint ∈ codepoints)
        (rest : CertificateBodyReplays grammar fullInput symbols
          (start + 1) stop certificates trees) :
        CertificateBodyReplays grammar fullInput
          (.oneOfTerminal codepoints :: symbols) start stop
          (.terminal codepoint start (start + 1) :: certificates)
          (.terminal codepoint :: trees)
    | nonterminal
        (head : CertificateReplays grammar fullInput
          (.node sourceRule category start middle childCertificates)
          category start middle tree)
        (rest : CertificateBodyReplays grammar fullInput symbols
          middle stop certificates trees) :
        CertificateBodyReplays grammar fullInput
          (.nonterminal category :: symbols) start stop
          (.node sourceRule category start middle childCertificates :: certificates)
          (tree :: trees)
end

mutual
  private def certificateCompiledSound
      {grammar : CompiledGrammar} {fullInput certificate category start stop tree}
      (replay : CertificateReplays grammar fullInput certificate
        category start stop tree) :
      CompiledDerivesAt grammar fullInput category start stop tree :=
    match replay with
    | .node production member body guards =>
        .apply production member (certificateBodyCompiledSound body) guards

  private def certificateBodyCompiledSound
      {grammar : CompiledGrammar} {fullInput symbols start stop certificates trees}
      (replay : CertificateBodyReplays grammar fullInput symbols
        start stop certificates trees) :
      CompiledBodyDerivesAt grammar fullInput symbols start stop trees :=
    match replay with
    | .nil => .nil
    | .terminal lookup rest =>
        .terminal lookup (certificateBodyCompiledSound rest)
    | .anyTerminal lookup rest =>
        .anyTerminal lookup (certificateBodyCompiledSound rest)
    | .oneOfTerminal lookup member rest =>
        .oneOfTerminal lookup member (certificateBodyCompiledSound rest)
    | .nonterminal head rest =>
        .nonterminal (certificateCompiledSound head)
          (certificateBodyCompiledSound rest)
end

/-- Certificate replay reconstructs a derivation in the supplied compiled
grammar before any source-level reflection is applied. -/
theorem certificate_replay_compiled_sound
    {grammar : CompiledGrammar} {fullInput certificate category start stop tree}
    (replay : CertificateReplays grammar fullInput certificate
      category start stop tree) :
    CompiledDerivesAt grammar fullInput category start stop tree :=
  certificateCompiledSound replay

/-- Body-certificate replay reconstructs the corresponding compiled body. -/
theorem certificate_body_replay_compiled_sound
    {grammar : CompiledGrammar} {fullInput symbols start stop certificates trees}
    (replay : CertificateBodyReplays grammar fullInput symbols
      start stop certificates trees) :
    CompiledBodyDerivesAt grammar fullInput symbols start stop trees :=
  certificateBodyCompiledSound replay

def RootCertificateReplays (presentation : SourceDefinition)
    (input : List Codepoint) (certificate : Certificate) (tree : ParseTree) : Prop :=
  CertificateReplays (compile presentation) input certificate
      presentation.start 0 input.length tree ∧
    certificate.start = 0 ∧ certificate.stop = input.length

/-- Exact-span guarded certificate replay reconstructs an ordinary source
derivation. -/
theorem certificate_replay_sound
    {presentation : SourceDefinition} {input certificate tree}
    (replay : RootCertificateReplays presentation input certificate tree) :
    SourceDerivesAt presentation input presentation.start
      0 input.length tree :=
  compile_reflects (certificateCompiledSound replay.1)

/-! ## Guard witnesses -/

def eofPresentation : SourceDefinition :=
  { start := "start"
    rules :=
      [{ sourceRule := "terminal-at-eof", category := "start",
         symbols := [.exact 120], guards := [.atEnd] }] }

def eofTree : ParseTree :=
  .node "terminal-at-eof" "start" [.terminal 120]

def eofCertificate : Certificate :=
  .node "terminal-at-eof" "start" 0 1 [.terminal 120 0 1]

def eofWrongSpanCertificate : Certificate :=
  .node "terminal-at-eof" "start" 1 2 [.terminal 120 1 2]

theorem eof_source_accepts :
    SourceDerivesAt eofPresentation [120] "start" 0 1 eofTree := by
  apply SourceDerivesAt.apply eofPresentation.rules[0]
  · simp [eofPresentation]
  · apply SourceBodyDerivesAt.exact
    · rfl
    · exact .nil
  · exact .atEnd rfl .nil

theorem eof_compiled_accepts :
    CompiledDerivesAt (compile eofPresentation) [120] "start" 0 1 eofTree :=
  compile_preserves eof_source_accepts

theorem eof_certificate_replays :
    RootCertificateReplays eofPresentation [120] eofCertificate eofTree := by
  constructor
  · apply CertificateReplays.node (compileRule eofPresentation.rules[0])
    · simp [compile, eofPresentation]
    · apply CertificateBodyReplays.terminal
      · rfl
      · exact .nil
    · exact .atEnd rfl .nil
  · exact ⟨rfl, rfl⟩

theorem eof_certificate_sound :
    SourceDerivesAt eofPresentation [120] "start" 0 1 eofTree :=
  certificate_replay_sound eof_certificate_replays

theorem eof_wrong_span_certificate_rejected :
    ¬ RootCertificateReplays eofPresentation [120]
      eofWrongSpanCertificate eofTree := by
  intro replay
  exact Nat.one_ne_zero replay.2.1

private theorem eof_source_span
    {fullInput category start stop tree}
    (derivation : SourceDerivesAt eofPresentation fullInput
      category start stop tree) :
    stop = start + 1 := by
  cases derivation with
  | apply rule member body guards =>
      simp [eofPresentation] at member
      subst rule
      cases body with
      | exact lookup rest => cases rest; rfl

/-- A trailing codepoint makes the exact-root result set empty. -/
theorem eof_rejects_trailing_codepoint :
    sourceResults eofPresentation [120, 121] = ∅ := by
  ext tree
  simp only [Set.mem_empty_iff_false, iff_false, sourceResults]
  intro derivation
  have span := eof_source_span derivation
  simp at span

def lookaheadPresentation : SourceDefinition :=
  { start := "start"
    rules :=
      [{ sourceRule := "start", category := "start",
         symbols := [.call "peek", .call "letter"], guards := [] },
       { sourceRule := "peek-letter", category := "peek",
         symbols := [], guards := [.lookahead "letter"] },
       { sourceRule := "letter-a", category := "letter",
         symbols := [.exact 97], guards := [] }] }

def letterTree : ParseTree :=
  .node "letter-a" "letter" [.terminal 97]

def peekTree : ParseTree :=
  .node "peek-letter" "peek" []

def lookaheadTree : ParseTree :=
  .node "start" "start" [peekTree, letterTree]

theorem letter_source_witness :
    SourceDerivesAt lookaheadPresentation [97] "letter" 0 1 letterTree := by
  apply SourceDerivesAt.apply lookaheadPresentation.rules[2]
  · simp [lookaheadPresentation]
  · apply SourceBodyDerivesAt.exact
    · rfl
    · exact .nil
  · exact .nil

theorem peek_source_witness :
    SourceDerivesAt lookaheadPresentation [97] "peek" 0 0 peekTree := by
  apply SourceDerivesAt.apply lookaheadPresentation.rules[1]
  · simp [lookaheadPresentation]
  · exact .nil
  · exact .lookahead letter_source_witness .nil

theorem lookahead_source_accepts :
    SourceDerivesAt lookaheadPresentation [97] "start" 0 1
      lookaheadTree := by
  apply SourceDerivesAt.apply lookaheadPresentation.rules[0]
  · simp [lookaheadPresentation]
  · exact .call peek_source_witness (.call letter_source_witness .nil)
  · exact .nil

theorem lookahead_compiled_accepts :
    CompiledDerivesAt (compile lookaheadPresentation) [97] "start" 0 1
      lookaheadTree :=
  compile_preserves lookahead_source_accepts

def nextInPresentation : SourceDefinition :=
  { start := "peek"
    rules :=
      [{ sourceRule := "peek-a", category := "peek", symbols := [],
         guards := [.nextIn [97] false] }] }

def nextInEofPresentation : SourceDefinition :=
  { start := "peek"
    rules :=
      [{ sourceRule := "peek-a-or-eof", category := "peek", symbols := [],
         guards := [.nextIn [97] true] }] }

def nextInTree : ParseTree :=
  .node "peek-a" "peek" []

def nextInEofTree : ParseTree :=
  .node "peek-a-or-eof" "peek" []

theorem nextIn_source_accepts :
    SourceDerivesAt nextInPresentation [97] "peek" 0 0 nextInTree := by
  apply SourceDerivesAt.apply nextInPresentation.rules[0]
  · simp [nextInPresentation]
  · exact .nil
  · exact .nextIn rfl (by simp) .nil

theorem nextIn_compiled_accepts :
    CompiledDerivesAt (compile nextInPresentation) [97]
      "peek" 0 0 nextInTree :=
  compile_preserves nextIn_source_accepts

theorem nextInEof_source_accepts :
    SourceDerivesAt nextInEofPresentation []
      "peek" 0 0 nextInEofTree := by
  apply SourceDerivesAt.apply nextInEofPresentation.rules[0]
  · simp [nextInEofPresentation]
  · exact .nil
  · exact .nextInEof rfl rfl .nil

private theorem nextIn_source_codepoint
    {fullInput category start stop tree}
    (derivation : SourceDerivesAt nextInPresentation fullInput
      category start stop tree) :
    fullInput[stop]? = some 97 := by
  cases derivation with
  | apply rule member body guards =>
      simp [nextInPresentation] at member
      subst rule
      cases guards with
      | nextIn lookup codepointMember rest =>
          have codepointEq := List.mem_singleton.mp codepointMember
          simpa [codepointEq] using lookup
      | nextInEof allowed endEq rest =>
          simp at allowed

/-- A resolved finite lookahead rejects a codepoint outside its declared set. -/
theorem nextIn_rejects_other_codepoint (tree : ParseTree) :
    ¬ SourceDerivesAt nextInPresentation [98] "peek" 0 0 tree := by
  intro derivation
  have lookup := nextIn_source_codepoint derivation
  simp at lookup

end Mettapedia.GSLT.Parsing.GuardCorrespondence
