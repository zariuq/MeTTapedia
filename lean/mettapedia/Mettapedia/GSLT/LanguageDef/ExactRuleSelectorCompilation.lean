import Mettapedia.GSLT.LanguageDef.FiniteRuleIndexCompilation
import Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation

/-!
# Exact rule-selector compilation

Finite rule indexing removes unrelated candidates while preserving every
candidate in a selected bucket.  This module isolates the stronger staging
boundary available when a stable key selects exactly one rule.  The partial
compiler rejects missing and duplicate keys, and the main theorem proves that
direct lookup has exactly the source relational observation.

The construction is independent of the meaning of keys and rules.  A proof
label, a state/token parser action, a bytecode opcode, and a singleton equation
head are all instances of the same optimization.
-/

namespace Mettapedia.GSLT.LanguageDef.ExactRuleSelectorCompilation

universe uKey uRule uState uResult

variable {Key : Type uKey} {Rule : Type uRule}

/-- A direct selector table.  Successful compilation guarantees that its keys
are the complete, duplicate-free source inventory. -/
abbrev ExactIndex (Key : Type uKey) (Rule : Type uRule) :=
  List (Key × Rule)

/-- Direct lookup in the physical selector table. -/
def lookup [DecidableEq Key] (query : Key) :
    ExactIndex Key Rule → Option Rule
  | [] => none
  | (key, rule) :: rest =>
      if query = key then some rule else lookup query rest

/-- Does a direct table already contain a selector key? -/
def containsKey [DecidableEq Key] (query : Key)
    (index : ExactIndex Key Rule) : Bool :=
  match index with
  | [] => false
  | (key, _) :: rest =>
      if query = key then true else containsKey query rest

/-- Compile a rule inventory only when every rule has a key and no two rules
have the same key.  Missing and ambiguous selectors fail closed. -/
def compile? [DecidableEq Key] (keyOf? : Rule → Option Key) :
    List Rule → Option (ExactIndex Key Rule)
  | [] => some []
  | rule :: rules =>
      match keyOf? rule with
      | none => none
      | some key =>
          match compile? keyOf? rules with
          | none => none
          | some tail =>
              if containsKey key tail then none
              else some ((key, rule) :: tail)

/-- Executable recognizer for the exactly selectable fragment. -/
def supported? [DecidableEq Key] (keyOf? : Rule → Option Key)
    (rules : List Rule) : Bool :=
  (compile? keyOf? rules).isSome

theorem containsKey_eq_false_iff_lookup_eq_none [DecidableEq Key]
    (query : Key) (index : ExactIndex Key Rule) :
    containsKey query index = false ↔ lookup query index = none := by
  induction index with
  | nil => simp [containsKey, lookup]
  | cons entry rest ih =>
      obtain ⟨key, rule⟩ := entry
      by_cases same : query = key
      · subst key
        simp [containsKey, lookup]
      · simp [containsKey, lookup, same, ih]

/-- Successful exact compilation turns the complete source candidate bag into
the optional result of one direct lookup.  Thus direct dispatch preserves
order and multiplicity rather than assuming them irrelevant: acceptance has
proved that the selected source bag has length at most one. -/
theorem sourceCandidates_eq_lookup_toList_of_compile?
    [DecidableEq Key] (keyOf? : Rule → Option Key) (rules : List Rule)
    (index : ExactIndex Key Rule)
    (accepted : compile? keyOf? rules = some index) (query : Key) :
    FiniteRuleIndexCompilation.sourceCandidates keyOf? rules query =
      (lookup query index).toList := by
  induction rules generalizing index query with
  | nil =>
      simp [compile?] at accepted
      subst index
      simp [FiniteRuleIndexCompilation.sourceCandidates, lookup]
  | cons rule rules ih =>
      cases keyEq : keyOf? rule with
      | none => simp [compile?, keyEq] at accepted
      | some key =>
          cases tailEq : compile? keyOf? rules with
          | none => simp [compile?, keyEq, tailEq] at accepted
          | some tail =>
              by_cases duplicate : containsKey key tail = true
              · simp [compile?, keyEq, tailEq, duplicate] at accepted
              · have noDuplicate : containsKey key tail = false :=
                  by cases present : containsKey key tail <;> simp_all
                simp [compile?, keyEq, tailEq, noDuplicate] at accepted
                subst index
                by_cases same : query = key
                · subst query
                  have tailLookup : lookup key tail = none :=
                    (containsKey_eq_false_iff_lookup_eq_none key tail).1
                      noDuplicate
                  have tailCandidates := ih tail tailEq key
                  rw [tailLookup] at tailCandidates
                  unfold FiniteRuleIndexCompilation.sourceCandidates at tailCandidates ⊢
                  simp only [Option.toList_none] at tailCandidates
                  rw [List.filter_cons]
                  rw [show (keyOf? rule == some key) = true by simp [keyEq]]
                  simp only [if_true]
                  rw [tailCandidates]
                  simp [lookup]
                · have reverse : key ≠ query := Ne.symm same
                  have tailCandidates := ih tail tailEq query
                  unfold FiniteRuleIndexCompilation.sourceCandidates at tailCandidates ⊢
                  rw [List.filter_cons]
                  rw [show (keyOf? rule == some query) = false by
                    simp [keyEq, reverse]]
                  simp only [lookup, same]
                  exact tailCandidates

/-- Source execution exposes every selected rule result. -/
def runSource [DecidableEq Key] (keyOf? : Rule → Option Key)
    (execute : Rule → State → Result) (rules : List Rule)
    (query : Key) (state : State) : List Result :=
  (FiniteRuleIndexCompilation.sourceCandidates keyOf? rules query).map
    fun rule => execute rule state

/-- Compiled execution applies at most one directly selected rule. -/
def runCompiled [DecidableEq Key] (execute : Rule → State → Result)
    (index : ExactIndex Key Rule) (query : Key) (state : State) :
    List Result :=
  (lookup query index).toList.map fun rule => execute rule state

/-- The exact selector is a semantics-preserving staging transformation for
every rule interpretation and machine state. -/
theorem runCompiled_eq_runSource_of_compile? [DecidableEq Key]
    (keyOf? : Rule → Option Key) (execute : Rule → State → Result)
    (rules : List Rule) (index : ExactIndex Key Rule)
    (accepted : compile? keyOf? rules = some index)
    (query : Key) (state : State) :
    runCompiled execute index query state =
      runSource keyOf? execute rules query state := by
  simp only [runCompiled, runSource]
  rw [sourceCandidates_eq_lookup_toList_of_compile?
    keyOf? rules index accepted query]

/-! ## Physical unique-index composition -/

/-- The exact selector's logical lookup is the source lookup already refined
by the shared monotone unique-index compiler. -/
theorem monotoneSourceLookup_eq_lookup
    [BEq Key] [LawfulBEq Key] [DecidableEq Key]
    (query : Key) (index : ExactIndex Key Rule) :
    MonotoneUniqueIndexCompilation.sourceLookup query index =
      lookup query index := by
  induction index with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨key, rule⟩ := entry
      by_cases same : key = query
      · subst key
        simp [MonotoneUniqueIndexCompilation.sourceLookup, lookup]
      · have reverse : query ≠ key := Ne.symm same
        simp [MonotoneUniqueIndexCompilation.sourceLookup, lookup,
          same, reverse, ih]

/-- The immutable hash-index realization used by the physical backend has
exactly the logical selector lookup. -/
theorem physicalLookup_eq_lookup
    [BEq Key] [Hashable Key] [LawfulBEq Key] [LawfulHashable Key]
    [DecidableEq Key] (query : Key) (index : ExactIndex Key Rule) :
    (MonotoneUniqueIndexCompilation.compileIndex index)[query]? =
      lookup query index := by
  rw [MonotoneUniqueIndexCompilation.lookup_compileIndex]
  exact monotoneSourceLookup_eq_lookup query index

/-- Successful selector staging followed by physical hash-index lowering
still returns exactly the complete source candidate bag. -/
theorem sourceCandidates_eq_physicalLookup_toList_of_compile?
    [BEq Key] [Hashable Key] [LawfulBEq Key] [LawfulHashable Key]
    [DecidableEq Key] (keyOf? : Rule → Option Key) (rules : List Rule)
    (index : ExactIndex Key Rule)
    (accepted : compile? keyOf? rules = some index) (query : Key) :
    FiniteRuleIndexCompilation.sourceCandidates keyOf? rules query =
      ((MonotoneUniqueIndexCompilation.compileIndex index)[query]?).toList := by
  rw [physicalLookup_eq_lookup]
  exact sourceCandidates_eq_lookup_toList_of_compile?
    keyOf? rules index accepted query

/-! ## Composition of an exact table read with exact action selection -/

universe uArtifact

variable {OuterKey InnerKey Row Action : Type uArtifact}

/-- The physical artifact for two existing exact relations: an outer table
read and the action table selected by the row's classification.  This pair is
derived during admission; it is not a new serialized plan vocabulary. -/
abbrev ComposedIndex
    (OuterKey : Type uArtifact) (InnerKey : Type uArtifact)
    (Row : Type uArtifact) (Action : Type uArtifact) :=
  ExactIndex OuterKey Row × ExactIndex InnerKey Action

/-- Admit a composed selector only when both of its already-present finite
relations are total on their records and duplicate-free on their keys. -/
def compileComposed? [DecidableEq OuterKey] [DecidableEq InnerKey]
    (outerKey? : Row → Option OuterKey)
    (innerKey? : Action → Option InnerKey)
    (rows : List Row) (actions : List Action) :
    Option (ComposedIndex OuterKey InnerKey Row Action) := do
  let outer ← compile? outerKey? rows
  let inner ← compile? innerKey? actions
  pure (outer, inner)

/-- Source relational meaning of label-to-row followed by
classification-to-action: retain every complete two-stage path. -/
def sourceComposedCandidates
    [DecidableEq OuterKey] [DecidableEq InnerKey]
    (outerKey? : Row → Option OuterKey) (classify : Row → InnerKey)
    (innerKey? : Action → Option InnerKey)
    (rows : List Row) (actions : List Action) (query : OuterKey) :
    List Action :=
  (FiniteRuleIndexCompilation.sourceCandidates outerKey? rows query).flatMap
    fun row =>
      FiniteRuleIndexCompilation.sourceCandidates
        innerKey? actions (classify row)

/-- Compiled meaning of the same two-stage path: one exact outer lookup and,
when it succeeds, one exact action lookup. -/
def runComposed
    [DecidableEq OuterKey] [DecidableEq InnerKey]
    (classify : Row → InnerKey)
    (index : ComposedIndex OuterKey InnerKey Row Action)
    (query : OuterKey) : List Action :=
  match lookup query index.1 with
  | none => []
  | some row => (lookup (classify row) index.2).toList

/-- The derived exact-selector gate preserves the complete relational path,
including absence.  In particular, direct label dispatch cannot hide a second
row or a second action: either ambiguity would make `compileComposed?` fail. -/
theorem sourceComposedCandidates_eq_runComposed_of_compileComposed?
    [DecidableEq OuterKey] [DecidableEq InnerKey]
    (outerKey? : Row → Option OuterKey) (classify : Row → InnerKey)
    (innerKey? : Action → Option InnerKey)
    (rows : List Row) (actions : List Action)
    (index : ComposedIndex OuterKey InnerKey Row Action)
    (accepted :
      compileComposed? outerKey? innerKey? rows actions = some index)
    (query : OuterKey) :
    sourceComposedCandidates outerKey? classify innerKey?
        rows actions query =
      runComposed classify index query := by
  cases outerAccepted : compile? outerKey? rows with
  | none => simp [compileComposed?, outerAccepted] at accepted
  | some outer =>
      cases innerAccepted : compile? innerKey? actions with
      | none =>
          simp [compileComposed?, outerAccepted, innerAccepted] at accepted
      | some inner =>
          simp [compileComposed?, outerAccepted, innerAccepted] at accepted
          subst index
          unfold sourceComposedCandidates runComposed
          rw [sourceCandidates_eq_lookup_toList_of_compile?
            outerKey? rows outer outerAccepted query]
          cases selected : lookup query outer with
          | none => simp
          | some row =>
              simp only [Option.toList_some, List.flatMap_singleton]
              exact sourceCandidates_eq_lookup_toList_of_compile?
                innerKey? actions inner innerAccepted (classify row)

/-- Hash lowering of both derived indices preserves the same composed source
relation.  This is the theorem used by an implementation with one exact table
lookup followed by one exact action lookup. -/
theorem sourceComposedCandidates_eq_physicalLookups_of_compileComposed?
    [BEq OuterKey] [Hashable OuterKey]
    [LawfulBEq OuterKey] [LawfulHashable OuterKey]
    [BEq InnerKey] [Hashable InnerKey]
    [LawfulBEq InnerKey] [LawfulHashable InnerKey]
    [DecidableEq OuterKey] [DecidableEq InnerKey]
    (outerKey? : Row → Option OuterKey) (classify : Row → InnerKey)
    (innerKey? : Action → Option InnerKey)
    (rows : List Row) (actions : List Action)
    (index : ComposedIndex OuterKey InnerKey Row Action)
    (accepted :
      compileComposed? outerKey? innerKey? rows actions = some index)
    (query : OuterKey) :
    sourceComposedCandidates outerKey? classify innerKey?
        rows actions query =
      match
        (MonotoneUniqueIndexCompilation.compileIndex index.1)[query]?
      with
      | none => []
      | some row =>
          ((MonotoneUniqueIndexCompilation.compileIndex index.2)[classify row]?).toList := by
  rw [sourceComposedCandidates_eq_runComposed_of_compileComposed?
    outerKey? classify innerKey? rows actions index accepted query]
  unfold runComposed
  rw [physicalLookup_eq_lookup]
  cases selected : lookup query index.1 with
  | none => rfl
  | some row =>
      simp only
      rw [physicalLookup_eq_lookup]

/-! ## Independent witnesses and fail-closed cases -/

private structure OpcodeRule where
  opcode : Nat
  delta : Int
  deriving DecidableEq, Repr

private def opcodeKey (rule : OpcodeRule) : Option Nat := some rule.opcode

private def opcodeRules : List OpcodeRule :=
  [{ opcode := 3, delta := 1 }, { opcode := 8, delta := -2 }]

/-- Numeric bytecode opcodes select one transition without scanning the other
opcode implementations. -/
example :
    compile? opcodeKey opcodeRules =
      some [(3, opcodeRules[0]), (8, opcodeRules[1])] := by
  decide

private structure ParserAction where
  state : Nat
  terminal : Char
  nextState : Nat
  deriving DecidableEq, Repr

private def parserKey (action : ParserAction) : Option (Nat × Char) :=
  some (action.state, action.terminal)

private def parserActions : List ParserAction :=
  [{ state := 0, terminal := 'a', nextState := 1 },
   { state := 1, terminal := 'b', nextState := 2 }]

/-- A distinct state/terminal parser table uses the same exact-selector
compiler. -/
example :
    (compile? parserKey parserActions).isSome = true := by
  decide

private structure ClassifiedDeclaration where
  label : String
  kind : Nat
  deriving DecidableEq, Repr

private structure PreparedAction where
  kind : Nat
  instruction : Nat
  deriving DecidableEq, Repr

private def declarationKey (row : ClassifiedDeclaration) : Option String :=
  some row.label

private def actionKey (action : PreparedAction) : Option Nat :=
  some action.kind

private def declarations : List ClassifiedDeclaration :=
  [{ label := "hyp", kind := 1 }, { label := "rule", kind := 2 }]

private def preparedActions : List PreparedAction :=
  [{ kind := 1, instruction := 11 }, { kind := 2, instruction := 19 }]

/-- The proof-label shape is one ordinary instance of the composed gate: a
label selects one declared kind, and that kind selects one closed action. -/
example :
    ∃ index,
      compileComposed? declarationKey actionKey
          declarations preparedActions = some index ∧
        runComposed ClassifiedDeclaration.kind index "rule" =
          [preparedActions[1]] := by
  refine ⟨([("hyp", declarations[0]), ("rule", declarations[1])],
      [(1, preparedActions[0]), (2, preparedActions[1])]), ?_, ?_⟩ <;>
    decide

/-- Ambiguity at either stage rejects the whole path.  Here the declaration
table is exact, but two actions claim the same classification. -/
example :
    (compileComposed? declarationKey actionKey declarations
      [{ kind := 1, instruction := 11 },
       { kind := 1, instruction := 12 }]).isSome = false := by
  decide

/-- Duplicate selector keys are rejected rather than silently choosing one
source transition. -/
example :
    (compile? opcodeKey
      [{ opcode := 3, delta := 1 }, { opcode := 3, delta := 4 }]).isSome =
      false := by
  decide

/-- A dynamically unclassified rule is rejected rather than assigned a
catch-all interpretation. -/
example :
    (compile? (fun value : Option Nat => value) [some 1, none]).isSome =
      false := by
  decide

end Mettapedia.GSLT.LanguageDef.ExactRuleSelectorCompilation
