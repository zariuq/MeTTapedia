import Mathlib.Data.Set.Basic

/-!
# Scannerless syntax-GSLT compiler correspondence

This module isolates the normalized productive core shared by the ordinary
Horn stream rules and the packed parser plan: exact and wildcard codepoints,
recursive category calls, epsilon productions, and finite-terminal-set
compaction. Source and compiled derivations are separate inductive judgments.
The compiler maps source rules to a distinct grammar IR, and the
correspondence proofs traverse derivations in both directions.

Guards and packed-forest sharing are subsequent conservative extensions of
this core.
-/

namespace Mettapedia.GSLT.Parsing.CompilerCorrespondence

abbrev Codepoint := Nat
abbrev Category := String
abbrev RuleId := String

/-- Stream operations retained after specializing an ordinary Horn parse rule. -/
inductive SourceSymbol where
  | exact (codepoint : Codepoint)
  | any
  | call (category : Category)
  deriving DecidableEq, Repr

/-- One normalized source rule.  `sourceRule` is the identity of the admitted
Horn rule from which the stream path was recovered. -/
structure SourceRule where
  sourceRule : RuleId
  category : Category
  symbols : List SourceSymbol
  deriving DecidableEq, Repr

/-- The normalized source fragment selected from one admitted presentation. -/
structure SourceDefinition where
  start : Category
  rules : List SourceRule
  deriving DecidableEq, Repr

/-- Language-neutral symbols consumed by the packed parser plan. -/
inductive CompiledSymbol where
  | terminal (codepoint : Codepoint)
  | anyTerminal
  | oneOfTerminal (codepoints : List Codepoint)
  | nonterminal (category : Category)
  deriving DecidableEq, Repr

/-- One production in the compiled grammar IR. -/
structure CompiledProduction where
  label : RuleId
  category : Category
  symbols : List CompiledSymbol
  sourceRule : RuleId
  deriving DecidableEq, Repr

/-- The language-neutral grammar IR consumed by packed backends. -/
structure CompiledGrammar where
  start : Category
  productions : List CompiledProduction
  deriving DecidableEq, Repr

/-- Parse trees retain terminals and the exact source-rule identity. -/
inductive ParseTree where
  | terminal (codepoint : Codepoint)
  | node (sourceRule : RuleId) (category : Category)
      (children : List ParseTree)
  deriving Repr

def compileSymbol : SourceSymbol → CompiledSymbol
  | .exact codepoint => .terminal codepoint
  | .any => .anyTerminal
  | .call category => .nonterminal category

def compileRule (rule : SourceRule) : CompiledProduction :=
  { label := rule.sourceRule
    category := rule.category
    symbols := rule.symbols.map compileSymbol
    sourceRule := rule.sourceRule }

/-- Structural compilation of the normalized source fragment. -/
def compile (presentation : SourceDefinition) : CompiledGrammar :=
  { start := presentation.start
    productions := presentation.rules.map compileRule }

mutual
  /-- Ordinary source-rule evaluation for the normalized Horn stream core. -/
  inductive SourceDerives (presentation : SourceDefinition) :
      Category → List Codepoint → ParseTree → Prop where
    | apply (rule : SourceRule)
        (member : rule ∈ presentation.rules)
        (body : SourceBodyDerives presentation rule.symbols input children) :
        SourceDerives presentation rule.category input
          (.node rule.sourceRule rule.category children)

  /-- Left-to-right evaluation of a source-rule stream path. -/
  inductive SourceBodyDerives (presentation : SourceDefinition) :
      List SourceSymbol → List Codepoint → List ParseTree → Prop where
    | nil : SourceBodyDerives presentation [] [] []
    | exact
        (rest : SourceBodyDerives presentation symbols input children) :
        SourceBodyDerives presentation (.exact codepoint :: symbols)
          (codepoint :: input) (.terminal codepoint :: children)
    | any
        (rest : SourceBodyDerives presentation symbols input children) :
        SourceBodyDerives presentation (.any :: symbols)
          (codepoint :: input) (.terminal codepoint :: children)
    | call
        (head : SourceDerives presentation category consumed tree)
        (rest : SourceBodyDerives presentation symbols remaining children) :
        SourceBodyDerives presentation (.call category :: symbols)
          (consumed ++ remaining) (tree :: children)
end

mutual
  /-- Derivation represented by the compiled language-neutral grammar IR. -/
  inductive CompiledDerives (grammar : CompiledGrammar) :
      Category → List Codepoint → ParseTree → Prop where
    | apply (production : CompiledProduction)
        (member : production ∈ grammar.productions)
        (body : CompiledBodyDerives grammar production.symbols input children) :
        CompiledDerives grammar production.category input
          (.node production.sourceRule production.category children)

  /-- Left-to-right evaluation of one compiled production. -/
  inductive CompiledBodyDerives (grammar : CompiledGrammar) :
      List CompiledSymbol → List Codepoint → List ParseTree → Prop where
    | nil : CompiledBodyDerives grammar [] [] []
    | terminal
        (rest : CompiledBodyDerives grammar symbols input children) :
        CompiledBodyDerives grammar (.terminal codepoint :: symbols)
          (codepoint :: input) (.terminal codepoint :: children)
    | anyTerminal
        (rest : CompiledBodyDerives grammar symbols input children) :
        CompiledBodyDerives grammar (.anyTerminal :: symbols)
          (codepoint :: input) (.terminal codepoint :: children)
    | oneOfTerminal
        (member : codepoint ∈ codepoints)
        (rest : CompiledBodyDerives grammar symbols input children) :
        CompiledBodyDerives grammar (.oneOfTerminal codepoints :: symbols)
          (codepoint :: input) (.terminal codepoint :: children)
    | nonterminal
        (head : CompiledDerives grammar category consumed tree)
        (rest : CompiledBodyDerives grammar symbols remaining children) :
        CompiledBodyDerives grammar (.nonterminal category :: symbols)
          (consumed ++ remaining) (tree :: children)
end

mutual
  private def preserveDerivation
      {presentation : SourceDefinition} {category input tree}
      (derivation : SourceDerives presentation category input tree) :
      CompiledDerives (compile presentation) category input tree :=
    match derivation with
    | .apply rule member body =>
        .apply (compileRule rule)
          (List.mem_map.mpr ⟨rule, member, rfl⟩)
          (preserveBody body)

  private def preserveBody
      {presentation : SourceDefinition} {symbols input children}
      (derivation : SourceBodyDerives presentation symbols input children) :
      CompiledBodyDerives (compile presentation)
        (symbols.map compileSymbol) input children :=
    match derivation with
    | .nil => .nil
    | .exact rest => .terminal (preserveBody rest)
    | .any rest => .anyTerminal (preserveBody rest)
    | .call head rest =>
        .nonterminal (preserveDerivation head) (preserveBody rest)
end

/-- Preservation: every normalized syntax-GSLT result is represented by the
compiled grammar. -/
theorem compile_preserves
    {presentation : SourceDefinition} {category input tree}
    (derivation : SourceDerives presentation category input tree) :
    CompiledDerives (compile presentation) category input tree :=
  preserveDerivation derivation

mutual
  private def reflectDerivation
      {presentation : SourceDefinition} {category input tree}
      (derivation : CompiledDerives (compile presentation) category input tree) :
      SourceDerives presentation category input tree :=
    match derivation with
    | .apply production member body => by
        change production ∈ presentation.rules.map compileRule at member
        obtain ⟨rule, ruleMember, compiledRule⟩ := List.mem_map.mp member
        subst production
        exact .apply rule ruleMember (reflectBody body)

  private def reflectBody
      {presentation : SourceDefinition} {symbols input children}
      (derivation : CompiledBodyDerives (compile presentation)
        (symbols.map compileSymbol) input children) :
      SourceBodyDerives presentation symbols input children :=
    match symbols, derivation with
    | [], .nil => .nil
    | .exact _ :: _, .terminal rest => .exact (reflectBody rest)
    | .any :: _, .anyTerminal rest => .any (reflectBody rest)
    | .call _ :: _, .nonterminal head rest =>
        .call (reflectDerivation head) (reflectBody rest)
end

/-- Reflection: every compiled derivation comes from the normalized source
presentation. -/
theorem compile_reflects
    {presentation : SourceDefinition} {category input tree}
    (derivation : CompiledDerives (compile presentation) category input tree) :
    SourceDerives presentation category input tree :=
  reflectDerivation derivation

/-! ## Finite-terminal-set compaction -/

/-- A raw symbol sequence expands a compacted sequence.  Source-specialized
grammars have exact terminals; a compacted plan may replace one exact terminal
by a finite set containing it.  Wildcards and nonterminals are unchanged. -/
inductive SymbolsExpand :
    List CompiledSymbol → List CompiledSymbol → Prop where
  | nil : SymbolsExpand [] []
  | terminal
      (rest : SymbolsExpand raw compacted) :
      SymbolsExpand (.terminal codepoint :: raw)
        (.terminal codepoint :: compacted)
  | terminalSet
      (member : codepoint ∈ codepoints)
      (rest : SymbolsExpand raw compacted) :
      SymbolsExpand (.terminal codepoint :: raw)
        (.oneOfTerminal codepoints :: compacted)
  | anyTerminal
      (rest : SymbolsExpand raw compacted) :
      SymbolsExpand (.anyTerminal :: raw) (.anyTerminal :: compacted)
  | nonterminal
      (rest : SymbolsExpand raw compacted) :
      SymbolsExpand (.nonterminal category :: raw)
        (.nonterminal category :: compacted)

/-- Enumerate all exact raw symbol sequences denoted by a compacted sequence.
This is finite because terminal sets are serialized finite lists. -/
def expandSymbols : List CompiledSymbol → List (List CompiledSymbol)
  | [] => [[]]
  | .terminal codepoint :: rest =>
      (expandSymbols rest).map (.terminal codepoint :: ·)
  | .anyTerminal :: rest =>
      (expandSymbols rest).map (.anyTerminal :: ·)
  | .oneOfTerminal codepoints :: rest =>
      codepoints.flatMap fun codepoint =>
        (expandSymbols rest).map (.terminal codepoint :: ·)
  | .nonterminal category :: rest =>
      (expandSymbols rest).map (.nonterminal category :: ·)

/-- Enumeration agrees exactly with the relational expansion specification. -/
theorem mem_expandSymbols_iff
    {raw compacted : List CompiledSymbol} :
    raw ∈ expandSymbols compacted ↔ SymbolsExpand raw compacted := by
  induction compacted generalizing raw with
  | nil =>
      constructor
      · intro member
        simp [expandSymbols] at member
        subst raw
        exact .nil
      · intro expansion
        cases expansion
        simp [expandSymbols]
  | cons symbol rest inductionHypothesis =>
      cases symbol with
      | terminal codepoint =>
          constructor
          · intro member
            simp only [expandSymbols, List.mem_map] at member
            obtain ⟨rawRest, restMember, rfl⟩ := member
            exact .terminal (inductionHypothesis.mp restMember)
          · intro expansion
            cases expansion with
            | terminal restExpansion =>
                exact List.mem_map.mpr
                  ⟨_, inductionHypothesis.mpr restExpansion, rfl⟩
      | anyTerminal =>
          constructor
          · intro member
            simp only [expandSymbols, List.mem_map] at member
            obtain ⟨rawRest, restMember, rfl⟩ := member
            exact .anyTerminal (inductionHypothesis.mp restMember)
          · intro expansion
            cases expansion with
            | anyTerminal restExpansion =>
                exact List.mem_map.mpr
                  ⟨_, inductionHypothesis.mpr restExpansion, rfl⟩
      | oneOfTerminal codepoints =>
          constructor
          · intro member
            simp only [expandSymbols, List.mem_flatMap, List.mem_map] at member
            obtain ⟨codepoint, codepointMember, rawRest, restMember, rfl⟩ :=
              member
            exact .terminalSet codepointMember
              (inductionHypothesis.mp restMember)
          · intro expansion
            cases expansion with
            | terminalSet codepointMember restExpansion =>
                exact List.mem_flatMap.mpr
                  ⟨_, codepointMember, List.mem_map.mpr
                    ⟨_, inductionHypothesis.mpr restExpansion, rfl⟩⟩
      | nonterminal category =>
          constructor
          · intro member
            simp only [expandSymbols, List.mem_map] at member
            obtain ⟨rawRest, restMember, rfl⟩ := member
            exact .nonterminal (inductionHypothesis.mp restMember)
          · intro expansion
            cases expansion with
            | nonterminal restExpansion =>
                exact List.mem_map.mpr
                  ⟨_, inductionHypothesis.mpr restExpansion, rfl⟩

/-- A checked relationship between an uncompressed specialized grammar and a
finite-terminal-set compacted grammar.

`forward` prevents the optimizer from dropping a raw alternative. `backward`
prevents it from inventing an alternative: every concrete expansion admitted
by a compacted production must be an actual raw production. -/
structure TerminalCompaction (raw compacted : CompiledGrammar) : Prop where
  start_eq : compacted.start = raw.start
  forward : ∀ rawProduction, rawProduction ∈ raw.productions →
    ∃ compactedProduction, compactedProduction ∈ compacted.productions ∧
      compactedProduction.category = rawProduction.category ∧
      compactedProduction.sourceRule = rawProduction.sourceRule ∧
      SymbolsExpand rawProduction.symbols compactedProduction.symbols
  backward : ∀ compactedProduction,
    compactedProduction ∈ compacted.productions →
    ∀ rawSymbols, SymbolsExpand rawSymbols compactedProduction.symbols →
      ∃ rawProduction, rawProduction ∈ raw.productions ∧
        rawProduction.category = compactedProduction.category ∧
        rawProduction.sourceRule = compactedProduction.sourceRule ∧
        rawProduction.symbols = rawSymbols

private def forwardCompactionMatch
    (rawProduction compactedProduction : CompiledProduction) : Bool :=
  decide (
    compactedProduction.category = rawProduction.category ∧
    compactedProduction.sourceRule = rawProduction.sourceRule ∧
    rawProduction.symbols ∈ expandSymbols compactedProduction.symbols)

private def backwardCompactionMatch
    (rawProduction compactedProduction : CompiledProduction)
    (rawSymbols : List CompiledSymbol) : Bool :=
  decide (
    rawProduction.category = compactedProduction.category ∧
    rawProduction.sourceRule = compactedProduction.sourceRule ∧
    rawProduction.symbols = rawSymbols)

/-- Executable, finite validation of the terminal-compaction contract.  Every
finite-set choice is expanded and checked against a real raw production. -/
def validateTerminalCompaction
    (raw compacted : CompiledGrammar) : Bool :=
  decide (compacted.start = raw.start) &&
  (raw.productions.all fun rawProduction =>
    compacted.productions.any fun compactedProduction =>
      forwardCompactionMatch rawProduction compactedProduction) &&
  (compacted.productions.all fun compactedProduction =>
    (expandSymbols compactedProduction.symbols).all fun rawSymbols =>
      raw.productions.any fun rawProduction =>
        backwardCompactionMatch rawProduction compactedProduction rawSymbols)

/-- Validator soundness: executable acceptance constructs the full relational
compaction contract used by preservation, reflection, and certificate replay. -/
theorem validateTerminalCompaction_sound
    {raw compacted : CompiledGrammar}
    (accepted : validateTerminalCompaction raw compacted = true) :
    TerminalCompaction raw compacted := by
  simp only [validateTerminalCompaction, Bool.and_eq_true,
    List.all_eq_true, List.any_eq_true, forwardCompactionMatch,
    backwardCompactionMatch, decide_eq_true_eq] at accepted
  obtain ⟨startAndForward, backwardAccepted⟩ := accepted
  obtain ⟨startEq, forwardAccepted⟩ := startAndForward
  constructor
  · exact startEq
  · intro rawProduction rawMember
    obtain ⟨compactedProduction, compactedMember, categoryEq,
      sourceRuleEq, symbolsMember⟩ := forwardAccepted rawProduction rawMember
    exact ⟨compactedProduction, compactedMember, categoryEq, sourceRuleEq,
      mem_expandSymbols_iff.mp symbolsMember⟩
  · intro compactedProduction compactedMember rawSymbols expansion
    have symbolsMember :
        rawSymbols ∈ expandSymbols compactedProduction.symbols :=
      mem_expandSymbols_iff.mpr expansion
    obtain ⟨rawProduction, rawMember, categoryEq, sourceRuleEq, symbolsEq⟩ :=
      backwardAccepted compactedProduction compactedMember rawSymbols symbolsMember
    exact ⟨rawProduction, rawMember, categoryEq, sourceRuleEq, symbolsEq⟩

/-- Every relational compaction witness is accepted by the finite validator. -/
theorem validateTerminalCompaction_complete
    {raw compacted : CompiledGrammar}
    (witness : TerminalCompaction raw compacted) :
    validateTerminalCompaction raw compacted = true := by
  simp only [validateTerminalCompaction, Bool.and_eq_true,
    List.all_eq_true, List.any_eq_true, forwardCompactionMatch,
    backwardCompactionMatch, decide_eq_true_eq]
  constructor
  · constructor
    · exact witness.start_eq
    · intro rawProduction rawMember
      obtain ⟨compactedProduction, compactedMember, categoryEq,
        sourceRuleEq, expansion⟩ := witness.forward rawProduction rawMember
      exact ⟨compactedProduction, compactedMember, categoryEq, sourceRuleEq,
        mem_expandSymbols_iff.mpr expansion⟩
  · intro compactedProduction compactedMember rawSymbols symbolsMember
    have expansion : SymbolsExpand rawSymbols compactedProduction.symbols :=
      mem_expandSymbols_iff.mp symbolsMember
    obtain ⟨rawProduction, rawMember, categoryEq, sourceRuleEq, symbolsEq⟩ :=
      witness.backward compactedProduction compactedMember rawSymbols expansion
    exact ⟨rawProduction, rawMember, categoryEq, sourceRuleEq, symbolsEq⟩

/-- Executable validation is equivalent to the relational terminal-compaction
contract. -/
theorem validateTerminalCompaction_iff
    {raw compacted : CompiledGrammar} :
    validateTerminalCompaction raw compacted = true ↔
      TerminalCompaction raw compacted :=
  ⟨validateTerminalCompaction_sound, validateTerminalCompaction_complete⟩

mutual
  private def preserveCompactedDerivation
      {raw compacted : CompiledGrammar}
      (witness : TerminalCompaction raw compacted)
      {category input tree}
      (derivation : CompiledDerives raw category input tree) :
      CompiledDerives compacted category input tree :=
    match derivation with
    | .apply rawProduction member body => by
        obtain ⟨compactedProduction, compactedMember, categoryEq,
          sourceRuleEq, expansion⟩ := witness.forward rawProduction member
        have compactedBody := preserveCompactedBody witness body expansion
        simpa [categoryEq, sourceRuleEq] using
          CompiledDerives.apply compactedProduction compactedMember compactedBody

  private def preserveCompactedBody
      {raw compacted : CompiledGrammar}
      (witness : TerminalCompaction raw compacted)
      {rawSymbols compactedSymbols input children}
      (derivation : CompiledBodyDerives raw rawSymbols input children)
      (expansion : SymbolsExpand rawSymbols compactedSymbols) :
      CompiledBodyDerives compacted compactedSymbols input children :=
    match expansion, derivation with
    | .nil, .nil => .nil
    | .terminal restExpansion, .terminal rest =>
        .terminal (preserveCompactedBody witness rest restExpansion)
    | .terminalSet member restExpansion, .terminal rest =>
        .oneOfTerminal member
          (preserveCompactedBody witness rest restExpansion)
    | .anyTerminal restExpansion, .anyTerminal rest =>
        .anyTerminal (preserveCompactedBody witness rest restExpansion)
    | .nonterminal restExpansion, .nonterminal head rest =>
        .nonterminal (preserveCompactedDerivation witness head)
          (preserveCompactedBody witness rest restExpansion)
end

/-- Finite-terminal-set compaction preserves every raw derivation and its
exact parse tree. -/
theorem terminalCompaction_preserves
    {raw compacted : CompiledGrammar}
    (witness : TerminalCompaction raw compacted)
    {category input tree}
    (derivation : CompiledDerives raw category input tree) :
    CompiledDerives compacted category input tree :=
  preserveCompactedDerivation witness derivation

mutual
  private def reflectCompactedDerivation
      {raw compacted : CompiledGrammar}
      (witness : TerminalCompaction raw compacted)
      {category input tree}
      (derivation : CompiledDerives compacted category input tree) :
      CompiledDerives raw category input tree :=
    match derivation with
    | .apply compactedProduction member body => by
        obtain ⟨rawSymbols, expansion, rawBody⟩ :=
          reflectCompactedBody witness body
        obtain ⟨rawProduction, rawMember, categoryEq, sourceRuleEq,
          symbolsEq⟩ := witness.backward compactedProduction member
            rawSymbols expansion
        rw [← symbolsEq] at rawBody
        simpa [categoryEq, sourceRuleEq] using
          CompiledDerives.apply rawProduction rawMember rawBody

  private def reflectCompactedBody
      {raw compacted : CompiledGrammar}
      (witness : TerminalCompaction raw compacted)
      {compactedSymbols input children}
      (derivation : CompiledBodyDerives compacted compactedSymbols input children) :
      ∃ rawSymbols, SymbolsExpand rawSymbols compactedSymbols ∧
        CompiledBodyDerives raw rawSymbols input children :=
    match derivation with
    | .nil => ⟨[], .nil, .nil⟩
    | .terminal rest => by
        obtain ⟨rawSymbols, expansion, rawRest⟩ :=
          reflectCompactedBody witness rest
        exact ⟨.terminal _ :: rawSymbols, .terminal expansion,
          .terminal rawRest⟩
    | .anyTerminal rest => by
        obtain ⟨rawSymbols, expansion, rawRest⟩ :=
          reflectCompactedBody witness rest
        exact ⟨.anyTerminal :: rawSymbols, .anyTerminal expansion,
          .anyTerminal rawRest⟩
    | .oneOfTerminal member rest => by
        obtain ⟨rawSymbols, expansion, rawRest⟩ :=
          reflectCompactedBody witness rest
        exact ⟨.terminal _ :: rawSymbols, .terminalSet member expansion,
          .terminal rawRest⟩
    | .nonterminal head rest => by
        obtain ⟨rawSymbols, expansion, rawRest⟩ :=
          reflectCompactedBody witness rest
        exact ⟨.nonterminal _ :: rawSymbols, .nonterminal expansion,
          .nonterminal (reflectCompactedDerivation witness head) rawRest⟩
end

/-- Finite-terminal-set compaction reflects every compacted derivation to a
real raw production; no terminal can be accepted merely because it appears in
optimizer data. -/
theorem terminalCompaction_reflects
    {raw compacted : CompiledGrammar}
    (witness : TerminalCompaction raw compacted)
    {category input tree}
    (derivation : CompiledDerives compacted category input tree) :
    CompiledDerives raw category input tree :=
  reflectCompactedDerivation witness derivation

/-- The complete source may-set at the declared start category. -/
def sourceResults (presentation : SourceDefinition) (input : List Codepoint) :
    Set ParseTree :=
  { tree | SourceDerives presentation presentation.start input tree }

/-- The complete compiled may-set at the declared start category. -/
def compiledResults (presentation : SourceDefinition) (input : List Codepoint) :
    Set ParseTree :=
  { tree | CompiledDerives (compile presentation) presentation.start input tree }

/-- Complete may-set of an arbitrary compiled grammar. -/
def grammarResults (grammar : CompiledGrammar) (input : List Codepoint) :
    Set ParseTree :=
  { tree | CompiledDerives grammar grammar.start input tree }

/-- Finite-terminal-set compaction preserves and reflects the entire may-set,
not merely whether some parse exists. -/
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

/-- Complete bounded result-set agreement for the normalized compiler core. -/
theorem complete_result_set_agreement
    (presentation : SourceDefinition) (input : List Codepoint) :
    compiledResults presentation input = sourceResults presentation input := by
  ext tree
  constructor
  · exact compile_reflects
  · exact compile_preserves

/-- A may-set is ambiguous exactly when it contains two distinct trees. -/
def Ambiguous (results : Set ParseTree) : Prop :=
  ∃ first ∈ results, ∃ second ∈ results, first ≠ second

/-- Compilation preserves and reflects ambiguity, not merely acceptance. -/
theorem ambiguity_agreement
    (presentation : SourceDefinition) (input : List Codepoint) :
    Ambiguous (compiledResults presentation input) ↔
      Ambiguous (sourceResults presentation input) := by
  rw [complete_result_set_agreement]

/-- Finite-terminal-set compaction preserves and reflects ambiguity as a
property of distinct parse trees. -/
theorem terminalCompaction_ambiguity_agreement
    {raw compacted : CompiledGrammar}
    (witness : TerminalCompaction raw compacted)
    (input : List Codepoint) :
    Ambiguous (grammarResults compacted input) ↔
      Ambiguous (grammarResults raw input) := by
  rw [terminalCompaction_result_set_agreement witness input]

/-! ## Certificate replay soundness -/

/-- A packed-backend certificate records exact source-rule identities, spans,
terminals, and recursive children. -/
inductive Certificate where
  | terminal (codepoint : Codepoint) (start stop : Nat)
  | node (sourceRule : RuleId) (category : Category) (start stop : Nat)
      (children : List Certificate)
  deriving Repr

def Certificate.start : Certificate → Nat
  | .terminal _ start _ => start
  | .node _ _ start _ _ => start

def Certificate.stop : Certificate → Nat
  | .terminal _ _ stop => stop
  | .node _ _ _ stop _ => stop

mutual
  /-- Relational specification of replaying one certificate node. -/
  inductive CertificateReplays (grammar : CompiledGrammar)
      (fullInput : List Codepoint) :
      Certificate → Category → List Codepoint → ParseTree → Prop where
    | node (production : CompiledProduction)
        (member : production ∈ grammar.productions)
        (body : CertificateBodyReplays grammar fullInput production.symbols
          consumed start stop certificates trees) :
        CertificateReplays grammar fullInput
          (.node production.sourceRule production.category start stop certificates)
          production.category consumed
          (.node production.sourceRule production.category trees)

  /-- Replay of a production's symbol sequence.  Spans compose exactly from
  left to right, and each terminal is checked against the original input. -/
  inductive CertificateBodyReplays (grammar : CompiledGrammar)
      (fullInput : List Codepoint) :
      List CompiledSymbol → List Codepoint → Nat → Nat →
        List Certificate → List ParseTree → Prop where
    | nil : CertificateBodyReplays grammar fullInput [] [] cursor cursor [] []
    | terminal
        (lookup : fullInput[start]? = some codepoint)
        (rest : CertificateBodyReplays grammar fullInput symbols consumed
          (start + 1) stop certificates trees) :
        CertificateBodyReplays grammar fullInput
          (.terminal codepoint :: symbols) (codepoint :: consumed) start stop
          (.terminal codepoint start (start + 1) :: certificates)
          (.terminal codepoint :: trees)
    | anyTerminal
        (lookup : fullInput[start]? = some codepoint)
        (rest : CertificateBodyReplays grammar fullInput symbols consumed
          (start + 1) stop certificates trees) :
        CertificateBodyReplays grammar fullInput
          (.anyTerminal :: symbols) (codepoint :: consumed) start stop
          (.terminal codepoint start (start + 1) :: certificates)
          (.terminal codepoint :: trees)
    | oneOfTerminal
        (member : codepoint ∈ codepoints)
        (lookup : fullInput[start]? = some codepoint)
        (rest : CertificateBodyReplays grammar fullInput symbols consumed
          (start + 1) stop certificates trees) :
        CertificateBodyReplays grammar fullInput
          (.oneOfTerminal codepoints :: symbols) (codepoint :: consumed) start stop
          (.terminal codepoint start (start + 1) :: certificates)
          (.terminal codepoint :: trees)
    | nonterminal
        (head : CertificateReplays grammar fullInput
          (.node sourceRule category start middle childCertificates)
          category headInput tree)
        (rest : CertificateBodyReplays grammar fullInput symbols tailInput
          middle stop certificates trees) :
        CertificateBodyReplays grammar fullInput
          (.nonterminal category :: symbols) (headInput ++ tailInput) start stop
          (.node sourceRule category start middle childCertificates :: certificates)
          (tree :: trees)
end

mutual
  private def certificateReplayCompiledSound
      {grammar : CompiledGrammar} {fullInput certificate category consumed tree}
      (replay : CertificateReplays grammar fullInput certificate category consumed tree) :
      CompiledDerives grammar category consumed tree :=
    match replay with
    | .node production member body =>
        .apply production member (certificateBodyCompiledSound body)

  private def certificateBodyCompiledSound
      {grammar : CompiledGrammar} {fullInput symbols consumed start stop certificates trees}
      (replay : CertificateBodyReplays grammar fullInput symbols consumed
        start stop certificates trees) :
      CompiledBodyDerives grammar symbols consumed trees :=
    match replay with
    | .nil => .nil
    | .terminal _ rest => .terminal (certificateBodyCompiledSound rest)
    | .anyTerminal _ rest =>
        .anyTerminal (certificateBodyCompiledSound rest)
    | .oneOfTerminal member _ rest =>
        .oneOfTerminal member (certificateBodyCompiledSound rest)
    | .nonterminal head rest =>
        .nonterminal (certificateReplayCompiledSound head)
          (certificateBodyCompiledSound rest)
end

/-- Exact root-coverage replay for an arbitrary compiled grammar. -/
def GrammarRootCertificateReplays (grammar : CompiledGrammar)
    (input : List Codepoint) (certificate : Certificate) (tree : ParseTree) : Prop :=
  CertificateReplays grammar input certificate grammar.start input tree ∧
    certificate.start = 0 ∧ certificate.stop = input.length

/-- A root certificate accepted by a compiled grammar reconstructs a compiled
derivation with exact input coverage. -/
theorem grammar_certificate_replay_sound
    {grammar : CompiledGrammar} {input certificate tree}
    (replay : GrammarRootCertificateReplays grammar input certificate tree) :
    CompiledDerives grammar grammar.start input tree :=
  certificateReplayCompiledSound replay.1

/-- Exact root-coverage replay against the direct structural compilation. -/
def RootCertificateReplays (presentation : SourceDefinition)
    (input : List Codepoint) (certificate : Certificate) (tree : ParseTree) : Prop :=
  GrammarRootCertificateReplays (compile presentation) input certificate tree

/-- Certificate replay soundness: a root certificate accepted against the
compiled plan reconstructs an ordinary source-presentation derivation. -/
theorem certificate_replay_sound
    {presentation : SourceDefinition} {input certificate tree}
    (replay : RootCertificateReplays presentation input certificate tree) :
    SourceDerives presentation presentation.start input tree := by
  exact compile_reflects (certificateReplayCompiledSound replay.1)

/-- Certificate replay remains source-sound after checked finite-terminal-set
compaction. -/
theorem compacted_certificate_replay_sound
    {presentation : SourceDefinition} {compacted : CompiledGrammar}
    {input certificate tree}
    (witness : TerminalCompaction (compile presentation) compacted)
    (replay : GrammarRootCertificateReplays compacted input certificate tree) :
    SourceDerives presentation presentation.start input tree := by
  have compactedDerivation := grammar_certificate_replay_sound replay
  have rawDerivation :=
    terminalCompaction_reflects witness compactedDerivation
  apply compile_reflects
  simpa [compile, witness.start_eq] using rawDerivation

/-! ## Executable toy witnesses -/

def toyPresentation : SourceDefinition :=
  { start := "start"
    rules :=
      [{ sourceRule := "left", category := "start",
         symbols := [.exact 97] },
       { sourceRule := "right", category := "start",
         symbols := [.exact 97] }] }

def toyLeftTree : ParseTree :=
  .node "left" "start" [.terminal 97]

def toyRightTree : ParseTree :=
  .node "right" "start" [.terminal 97]

def toyLeftCertificate : Certificate :=
  .node "left" "start" 0 1 [.terminal 97 0 1]

def toyWrongSpanCertificate : Certificate :=
  .node "left" "start" 1 2 [.terminal 97 1 2]

def wildcardPresentation : SourceDefinition :=
  { start := "start"
    rules :=
      [{ sourceRule := "wild", category := "start", symbols := [.any] }] }

def wildcardCertificate (codepoint : Codepoint) : Certificate :=
  .node "wild" "start" 0 1 [.terminal codepoint 0 1]

/-- Two exact source alternatives with one source-rule identity, matching the
shape admitted by the production compiler's terminal-choice compactor. -/
def terminalFamilyPresentation : SourceDefinition :=
  { start := "start"
    rules :=
      [{ sourceRule := "letter", category := "start",
         symbols := [.exact 97] },
       { sourceRule := "letter", category := "start",
         symbols := [.exact 98] }] }

def terminalFamilyCompacted : CompiledGrammar :=
  { start := "start"
    productions :=
      [{ label := "letter__set_0_0", category := "start",
         symbols := [.oneOfTerminal [97, 98]], sourceRule := "letter" }] }

def terminalFamilyOverbroad : CompiledGrammar :=
  { start := "start"
    productions :=
      [{ label := "letter__set_0_0", category := "start",
         symbols := [.oneOfTerminal [97, 98, 99]], sourceRule := "letter" }] }

def terminalFamilyIncomplete : CompiledGrammar :=
  { start := "start"
    productions :=
      [{ label := "letter__set_0_0", category := "start",
         symbols := [.oneOfTerminal [97]], sourceRule := "letter" }] }

/-- Checked witness that the finite-set production contains exactly the two
raw exact-terminal alternatives. -/
theorem terminalFamilyCompaction :
    TerminalCompaction (compile terminalFamilyPresentation)
      terminalFamilyCompacted := by
  constructor
  · rfl
  · intro rawProduction member
    simp [compile, terminalFamilyPresentation, compileRule] at member
    rcases member with rfl | rfl
    · refine ⟨terminalFamilyCompacted.productions[0], ?_, rfl, rfl, ?_⟩
      · simp [terminalFamilyCompacted]
      · exact .terminalSet (by simp) .nil
    · refine ⟨terminalFamilyCompacted.productions[0], ?_, rfl, rfl, ?_⟩
      · simp [terminalFamilyCompacted]
      · exact .terminalSet (by simp) .nil
  · intro compactedProduction member rawSymbols expansion
    simp [terminalFamilyCompacted] at member
    subst compactedProduction
    cases expansion with
    | terminalSet codepointMember restExpansion =>
        cases restExpansion
        simp at codepointMember
        rcases codepointMember with rfl | rfl
        · refine ⟨compileRule terminalFamilyPresentation.rules[0], ?_,
            rfl, rfl, rfl⟩
          simp [compile, terminalFamilyPresentation]
        · refine ⟨compileRule terminalFamilyPresentation.rules[1], ?_,
            rfl, rfl, rfl⟩
          simp [compile, terminalFamilyPresentation]

/-- The executable validator accepts the exact compacted family. -/
theorem terminalFamily_validator_accepts :
    validateTerminalCompaction (compile terminalFamilyPresentation)
      terminalFamilyCompacted = true := by
  rfl

/-- Backward validation rejects a compacted set that invents a codepoint. -/
theorem terminalFamily_validator_rejects_overbroad :
    validateTerminalCompaction (compile terminalFamilyPresentation)
      terminalFamilyOverbroad = false := by
  rfl

/-- Forward validation rejects a compacted set that drops a source
alternative. -/
theorem terminalFamily_validator_rejects_incomplete :
    validateTerminalCompaction (compile terminalFamilyPresentation)
      terminalFamilyIncomplete = false := by
  rfl

def terminalFamilyATree : ParseTree :=
  .node "letter" "start" [.terminal 97]

def terminalFamilyBTree : ParseTree :=
  .node "letter" "start" [.terminal 98]

def terminalFamilyBCertificate : Certificate :=
  .node "letter" "start" 0 1 [.terminal 98 0 1]

def terminalFamilyWrongCertificate : Certificate :=
  .node "letter" "start" 0 1 [.terminal 99 0 1]

theorem terminalFamily_a_source :
    SourceDerives terminalFamilyPresentation "start" [97]
      terminalFamilyATree := by
  apply SourceDerives.apply terminalFamilyPresentation.rules[0]
  · simp [terminalFamilyPresentation]
  · exact .exact .nil

theorem terminalFamily_b_source :
    SourceDerives terminalFamilyPresentation "start" [98]
      terminalFamilyBTree := by
  apply SourceDerives.apply terminalFamilyPresentation.rules[1]
  · simp [terminalFamilyPresentation]
  · exact .exact .nil

/-- Both exact source alternatives survive finite-set compaction. -/
theorem terminalFamily_a_compacted :
    CompiledDerives terminalFamilyCompacted "start" [97]
      terminalFamilyATree :=
  terminalCompaction_preserves terminalFamilyCompaction
    (compile_preserves terminalFamily_a_source)

theorem terminalFamily_b_compacted :
    CompiledDerives terminalFamilyCompacted "start" [98]
      terminalFamilyBTree :=
  terminalCompaction_preserves terminalFamilyCompaction
    (compile_preserves terminalFamily_b_source)

/-- A finite-set certificate checks the concrete selected codepoint and its
exact span before reflecting through compaction to the source rules. -/
theorem terminalFamily_b_certificate_replays :
    GrammarRootCertificateReplays terminalFamilyCompacted [98]
      terminalFamilyBCertificate terminalFamilyBTree := by
  constructor
  · apply CertificateReplays.node terminalFamilyCompacted.productions[0]
    · simp [terminalFamilyCompacted]
    · apply CertificateBodyReplays.oneOfTerminal
      · simp
      · rfl
      · exact .nil
  · exact ⟨rfl, rfl⟩

theorem terminalFamily_b_certificate_sound :
    SourceDerives terminalFamilyPresentation "start" [98]
      terminalFamilyBTree :=
  compacted_certificate_replay_sound terminalFamilyCompaction
    terminalFamily_b_certificate_replays

/-- Every source derivation in the finite family consumes one of its two
declared codepoints. -/
private theorem terminalFamily_source_input
    {category input tree}
    (derivation : SourceDerives terminalFamilyPresentation category input tree) :
    input = [97] ∨ input = [98] := by
  cases derivation with
  | apply rule member body =>
      simp [terminalFamilyPresentation] at member
      rcases member with rfl | rfl
      · cases body with
        | exact rest => cases rest; exact Or.inl rfl
      · cases body with
        | exact rest => cases rest; exact Or.inr rfl

/-- The compact terminal set cannot accept a value absent from the source
alternatives. -/
theorem terminalFamily_compacted_rejects_other :
    grammarResults terminalFamilyCompacted [99] = ∅ := by
  ext tree
  simp only [Set.mem_empty_iff_false, iff_false, grammarResults]
  intro compactedDerivation
  have rawDerivation := terminalCompaction_reflects terminalFamilyCompaction
    compactedDerivation
  have sourceDerivation := compile_reflects rawDerivation
  have consumed := terminalFamily_source_input sourceDerivation
  simp at consumed

/-- A certificate cannot launder a codepoint absent from the compacted set. -/
theorem terminalFamily_wrong_certificate_rejected :
    ¬ GrammarRootCertificateReplays terminalFamilyCompacted [99]
      terminalFamilyWrongCertificate
      (.node "letter" "start" [.terminal 99]) := by
  intro replay
  have derivation := grammar_certificate_replay_sound replay
  have member :
      (.node "letter" "start" [.terminal 99]) ∈
        grammarResults terminalFamilyCompacted [99] := derivation
  rw [terminalFamily_compacted_rejects_other] at member
  exact member

theorem toy_left_source :
    SourceDerives toyPresentation "start" [97] toyLeftTree := by
  apply SourceDerives.apply toyPresentation.rules[0]
  · simp [toyPresentation]
  · exact .exact .nil

theorem toy_right_source :
    SourceDerives toyPresentation "start" [97] toyRightTree := by
  apply SourceDerives.apply toyPresentation.rules[1]
  · simp [toyPresentation]
  · exact .exact .nil

/-- Positive ambiguity witness: the same codepoint has two source-rule trees. -/
theorem toy_source_ambiguous :
    Ambiguous (sourceResults toyPresentation [97]) := by
  refine ⟨toyLeftTree, toy_left_source, toyRightTree, toy_right_source, ?_⟩
  simp [toyLeftTree, toyRightTree]

/-- The compiled may-set retains the two distinct trees. -/
theorem toy_compiled_ambiguous :
    Ambiguous (compiledResults toyPresentation [97]) :=
  (ambiguity_agreement toyPresentation [97]).mpr toy_source_ambiguous

/-- Positive certificate witness with exact root and terminal coverage. -/
theorem toy_left_certificate_replays :
    RootCertificateReplays toyPresentation [97] toyLeftCertificate toyLeftTree := by
  constructor
  · apply CertificateReplays.node (compileRule toyPresentation.rules[0])
    · simp [compile, toyPresentation]
    · apply CertificateBodyReplays.terminal
      · rfl
      · exact .nil
  · exact ⟨rfl, rfl⟩

theorem toy_left_certificate_sound :
    SourceDerives toyPresentation "start" [97] toyLeftTree :=
  certificate_replay_sound toy_left_certificate_replays

/-- Negative certificate witness: shifting the recorded root span cannot
replay as an exact-coverage certificate. -/
theorem toy_wrong_span_certificate_rejected :
    ¬ RootCertificateReplays toyPresentation [97]
      toyWrongSpanCertificate toyLeftTree := by
  intro replay
  exact Nat.one_ne_zero replay.2.1

/-- Wildcard consumption is generic over codepoints, not a guest-language
character policy. -/
theorem wildcard_source_witness (codepoint : Codepoint) :
    SourceDerives wildcardPresentation "start" [codepoint]
      (.node "wild" "start" [.terminal codepoint]) := by
  apply SourceDerives.apply wildcardPresentation.rules[0]
  · simp [wildcardPresentation]
  · exact .any .nil

theorem wildcard_compiled_witness (codepoint : Codepoint) :
    CompiledDerives (compile wildcardPresentation) "start" [codepoint]
      (.node "wild" "start" [.terminal codepoint]) :=
  compile_preserves (wildcard_source_witness codepoint)

/-- Wildcard certificates still record and check the concrete codepoint and
its exact span. -/
theorem wildcard_certificate_replays (codepoint : Codepoint) :
    RootCertificateReplays wildcardPresentation [codepoint]
      (wildcardCertificate codepoint)
      (.node "wild" "start" [.terminal codepoint]) := by
  constructor
  · apply CertificateReplays.node (compileRule wildcardPresentation.rules[0])
    · simp [compile, wildcardPresentation]
    · apply CertificateBodyReplays.anyTerminal
      · rfl
      · exact .nil
  · exact ⟨rfl, rfl⟩

theorem wildcard_certificate_sound (codepoint : Codepoint) :
    SourceDerives wildcardPresentation "start" [codepoint]
      (.node "wild" "start" [.terminal codepoint]) :=
  certificate_replay_sound (wildcard_certificate_replays codepoint)

/-- Every source derivation in the toy presentation consumes exactly `a`. -/
private theorem toy_source_input
    {category input tree}
    (derivation : SourceDerives toyPresentation category input tree) :
    input = [97] := by
  cases derivation with
  | apply rule member body =>
      simp [toyPresentation] at member
      rcases member with rfl | rfl
      · cases body with
        | exact rest => cases rest; rfl
      · cases body with
        | exact rest => cases rest; rfl

/-- Negative witness: the toy presentation cannot parse a different codepoint. -/
theorem toy_rejects_other_codepoint :
    sourceResults toyPresentation [98] = ∅ := by
  ext tree
  simp only [Set.mem_empty_iff_false, iff_false]
  intro derivation
  have consumed := toy_source_input derivation
  simp at consumed

end Mettapedia.GSLT.Parsing.CompilerCorrespondence
