import Mettapedia.GSLT.Parsing.ClassAwareNativeForestStructuralValidation

/-!
# Finite semantic identities for a native packed forest

Native parser arrays carry backend-local numeric identifiers.  This module
binds those identifiers to the independently authored symbol, terminal, and
production meanings expected by the class-aware ParserPack contract.

The inventory is finite and supports sparse identifiers.  Its executable
checker rejects duplicate keys and requires a meaning for every identifier
used by a node or choice.  It does not infer meanings from C names, enum
values, or table positions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityInventory

open Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract
open Mettapedia.GSLT.Parsing.ClassAwarePackedForest
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence

/-- One sparse native identifier and its independently supplied meaning. -/
structure IdentityRow (Meaning : Type) where
  identifier : Nat
  meaning : Meaning
  deriving DecidableEq, Repr

namespace IdentityRow

def lookup {Meaning : Type} (identifier : Nat) :
    List (IdentityRow Meaning) → Option Meaning
  | [] => none
  | row :: rows =>
      if row.identifier = identifier then some row.meaning
      else lookup identifier rows

@[simp] theorem lookup_nil {Meaning : Type} (identifier : Nat) :
    lookup (Meaning := Meaning) identifier [] = none := rfl

@[simp] theorem lookup_cons_same {Meaning : Type}
    (identifier : Nat) (meaning : Meaning)
    (rows : List (IdentityRow Meaning)) :
    lookup identifier ({ identifier, meaning } :: rows) = some meaning := by
  simp [lookup]

theorem lookup_cons_different
    {Meaning : Type} {left right : Nat}
    (different : left ≠ right) (meaning : Meaning)
    (rows : List (IdentityRow Meaning)) :
    lookup left ({ identifier := right, meaning } :: rows) = lookup left rows := by
  have reversed : right ≠ left := Ne.symm different
  simp [lookup, reversed]

/-- Every successful lookup is backed by an actual row occurrence. -/
theorem lookup_eq_some_has_row
    {Meaning : Type} {identifier : Nat} {meaning : Meaning}
    {rows : List (IdentityRow Meaning)}
    (lookupExact : lookup identifier rows = some meaning) :
    ∃ row, row ∈ rows ∧
      row.identifier = identifier ∧ row.meaning = meaning := by
  induction rows with
  | nil => simp at lookupExact
  | cons row rows inductionHypothesis =>
      simp only [lookup] at lookupExact
      split at lookupExact
      · rename_i identifierExact
        exact ⟨row, by simp, identifierExact,
          Option.some.inj lookupExact⟩
      · rcases inductionHypothesis lookupExact with
          ⟨found, member, identifierExact, meaningExact⟩
        exact ⟨found, by simp [member], identifierExact, meaningExact⟩

end IdentityRow

/-- Finite authority table supplied beside a physical forest snapshot. -/
structure Inventory where
  symbols : List (IdentityRow String)
  terminals : List (IdentityRow TerminalMatcher)
  productions : List (IdentityRow ProductionRef)
  deriving DecidableEq, Repr

def Inventory.toTable (inventory : Inventory) : IdentityTable := {
  symbolSort? := fun identifier => IdentityRow.lookup identifier inventory.symbols
  terminalMatcher? := fun identifier =>
    IdentityRow.lookup identifier inventory.terminals
  productionRef? := fun identifier =>
    IdentityRow.lookup identifier inventory.productions
}

/-- Duplicate keys are forbidden independently in each semantic namespace. -/
def Inventory.WellFormed (inventory : Inventory) : Prop :=
  (inventory.symbols.map IdentityRow.identifier).Nodup ∧
    (inventory.terminals.map IdentityRow.identifier).Nodup ∧
    (inventory.productions.map IdentityRow.identifier).Nodup

def Inventory.wellFormedValid (inventory : Inventory) : Bool :=
  decide (inventory.symbols.map IdentityRow.identifier).Nodup &&
    decide (inventory.terminals.map IdentityRow.identifier).Nodup &&
    decide (inventory.productions.map IdentityRow.identifier).Nodup

theorem Inventory.wellFormedValid_eq_true_iff (inventory : Inventory) :
    inventory.wellFormedValid = true ↔ inventory.WellFormed := by
  simp [Inventory.wellFormedValid, Inventory.WellFormed, and_assoc]

/-- Every result sort that an admitted plan can construct. -/
def planResultSorts (plan : CompiledParserPackPlan) : List String :=
  plan.lexical.productions.map CompiledLexicalProduction.resultSort ++
    plan.structural.map CompiledStructuralProduction.resultSort

/-- Terminal matchers occurring in the lexical or structural portion of an
admitted plan. -/
def planTerminalMatchers
    (plan : CompiledParserPackPlan) : List TerminalMatcher :=
  plan.lexical.productions.map CompiledLexicalProduction.matcher ++
    plan.structural.flatMap fun production =>
      production.items.filterMap fun
        | .terminal matcher => some matcher
        | .nonterminal _ => none

/-- A production reference denotes an exact physical occurrence in the
supplied ParserPack plan. -/
def ProductionResolves
    (plan : CompiledParserPackPlan) : ProductionRef → Prop
  | .lexical position => position < plan.lexical.productions.length
  | .structural position => position < plan.structural.length

def productionResolvesValid
    (plan : CompiledParserPackPlan) : ProductionRef → Bool
  | .lexical position => decide (position < plan.lexical.productions.length)
  | .structural position => decide (position < plan.structural.length)

theorem productionResolvesValid_eq_true_iff
    (plan : CompiledParserPackPlan) (production : ProductionRef) :
    productionResolvesValid plan production = true ↔
      ProductionResolves plan production := by
  cases production <;>
    simp [productionResolvesValid, ProductionResolves]

/-- Every claimed identity meaning is licensed by the supplied plan.  This
rules out an internally total table which assigns invented language meanings
to otherwise valid native identifiers. -/
def Inventory.AuthorizedByPlan
    (inventory : Inventory) (plan : CompiledParserPackPlan) : Prop :=
  (∀ row, row ∈ inventory.symbols →
      row.meaning ∈ planResultSorts plan) ∧
    (∀ row, row ∈ inventory.terminals →
      row.meaning ∈ planTerminalMatchers plan) ∧
    (∀ row, row ∈ inventory.productions →
      ProductionResolves plan row.meaning)

def Inventory.authorizationValid
    (inventory : Inventory) (plan : CompiledParserPackPlan) : Bool :=
  (inventory.symbols.all fun row =>
      decide (row.meaning ∈ planResultSorts plan)) &&
    (inventory.terminals.all fun row =>
      decide (row.meaning ∈ planTerminalMatchers plan)) &&
    (inventory.productions.all fun row =>
      productionResolvesValid plan row.meaning)

theorem Inventory.authorizationValid_eq_true_iff
    (inventory : Inventory) (plan : CompiledParserPackPlan) :
    inventory.authorizationValid plan = true ↔
      inventory.AuthorizedByPlan plan := by
  simp [Inventory.authorizationValid, Inventory.AuthorizedByPlan,
    productionResolvesValid_eq_true_iff, and_assoc]

theorem Inventory.AuthorizedByPlan.symbol_lookup
    {inventory : Inventory} {plan : CompiledParserPackPlan}
    (authorized : inventory.AuthorizedByPlan plan)
    {identifier : Nat} {resultSort : String}
    (lookupExact :
      inventory.toTable.symbolSort? identifier = some resultSort) :
    resultSort ∈ planResultSorts plan := by
  have rowLookup :
      IdentityRow.lookup identifier inventory.symbols = some resultSort := by
    simpa [Inventory.toTable] using lookupExact
  rcases IdentityRow.lookup_eq_some_has_row rowLookup with
    ⟨row, member, _identifierExact, meaningExact⟩
  simpa [meaningExact] using authorized.1 row member

theorem Inventory.AuthorizedByPlan.terminal_lookup
    {inventory : Inventory} {plan : CompiledParserPackPlan}
    (authorized : inventory.AuthorizedByPlan plan)
    {identifier : Nat} {matcher : TerminalMatcher}
    (lookupExact :
      inventory.toTable.terminalMatcher? identifier = some matcher) :
    matcher ∈ planTerminalMatchers plan := by
  have rowLookup :
      IdentityRow.lookup identifier inventory.terminals = some matcher := by
    simpa [Inventory.toTable] using lookupExact
  rcases IdentityRow.lookup_eq_some_has_row rowLookup with
    ⟨row, member, _identifierExact, meaningExact⟩
  simpa [meaningExact] using authorized.2.1 row member

theorem Inventory.AuthorizedByPlan.production_lookup
    {inventory : Inventory} {plan : CompiledParserPackPlan}
    (authorized : inventory.AuthorizedByPlan plan)
    {identifier : Nat} {production : ProductionRef}
    (lookupExact :
      inventory.toTable.productionRef? identifier = some production) :
    ProductionResolves plan production := by
  have rowLookup :
      IdentityRow.lookup identifier inventory.productions =
        some production := by
    simpa [Inventory.toTable] using lookupExact
  rcases IdentityRow.lookup_eq_some_has_row rowLookup with
    ⟨row, member, _identifierExact, meaningExact⟩
  simpa [meaningExact] using authorized.2.2 row member

/-- The semantic identity required by one physical node kind. -/
def NodeIdentityCovered (table : IdentityTable) (node : Node) : Prop :=
  match node.kind with
  | .terminal terminalId _ =>
      ∃ matcher, table.terminalMatcher? terminalId = some matcher
  | .epsilon => True
  | .symbol symbolId =>
      ∃ resultSort, table.symbolSort? symbolId = some resultSort
  | .intermediate production _ =>
      ∃ productionRef, table.productionRef? production = some productionRef

/-- The production identity required by one physical packed choice. -/
def ChoiceIdentityCovered (table : IdentityTable) (choice : Choice) : Prop :=
  ∃ productionRef,
    table.productionRef? choice.productionIndex = some productionRef

def Inventory.nodeIdentityValid (inventory : Inventory) (node : Node) : Bool :=
  match node.kind with
  | .terminal terminalId _ =>
      (IdentityRow.lookup terminalId inventory.terminals).isSome
  | .epsilon => true
  | .symbol symbolId =>
      (IdentityRow.lookup symbolId inventory.symbols).isSome
  | .intermediate production _ =>
      (IdentityRow.lookup production inventory.productions).isSome

def Inventory.choiceIdentityValid
    (inventory : Inventory) (choice : Choice) : Bool :=
  (IdentityRow.lookup choice.productionIndex inventory.productions).isSome

theorem Inventory.nodeIdentityValid_eq_true_iff
    (inventory : Inventory) (node : Node) :
    inventory.nodeIdentityValid node = true ↔
      NodeIdentityCovered inventory.toTable node := by
  rcases node with
    ⟨kind, scalarStart, scalarStop, byteStart, byteStop,
      choiceBegin, choiceCount⟩
  cases kind <;>
    simp [Inventory.nodeIdentityValid, NodeIdentityCovered,
      Inventory.toTable, Option.isSome_iff_exists]

theorem Inventory.choiceIdentityValid_eq_true_iff
    (inventory : Inventory) (choice : Choice) :
    inventory.choiceIdentityValid choice = true ↔
      ChoiceIdentityCovered inventory.toTable choice := by
  simp [Inventory.choiceIdentityValid, ChoiceIdentityCovered,
    Inventory.toTable, Option.isSome_iff_exists]

/-- All finite identities needed by this physical forest resolve through the
supplied well-formed inventory. -/
structure Covers (view : ForestView) (inventory : Inventory) : Prop where
  wellFormed : inventory.WellFormed
  nodes : ∀ node, node ∈ view.nodes →
    NodeIdentityCovered inventory.toTable node
  choices : ∀ choice, choice ∈ view.choices →
    ChoiceIdentityCovered inventory.toTable choice

def validate (view : ForestView) (inventory : Inventory) : Bool :=
  inventory.wellFormedValid &&
    view.nodes.all inventory.nodeIdentityValid &&
    view.choices.all inventory.choiceIdentityValid

/-- Successful finite identity checking constructs the exact coverage
proposition consumed by later family and root derivations. -/
theorem validate_sound {view : ForestView} {inventory : Inventory}
    (accepted : validate view inventory = true) : Covers view inventory := by
  rw [validate, Bool.and_eq_true_iff, Bool.and_eq_true_iff] at accepted
  exact {
    wellFormed :=
      (inventory.wellFormedValid_eq_true_iff).mp accepted.1.1
    nodes := by
      intro node member
      exact (inventory.nodeIdentityValid_eq_true_iff node).mp
        ((List.all_eq_true.mp accepted.1.2) node member)
    choices := by
      intro choice member
      exact (inventory.choiceIdentityValid_eq_true_iff choice).mp
        ((List.all_eq_true.mp accepted.2) choice member)
  }

/-- Identity coverage and plan authorization are retained as independent
premises: the first concerns the observed forest, while the second prevents
the supplied table from inventing ParserPack meanings. -/
structure CoversPlan (view : ForestView) (inventory : Inventory)
    (plan : CompiledParserPackPlan) : Prop extends Covers view inventory where
  authorized : inventory.AuthorizedByPlan plan

def validateForPlan (view : ForestView) (inventory : Inventory)
    (plan : CompiledParserPackPlan) : Bool :=
  validate view inventory && inventory.authorizationValid plan

theorem validateForPlan_sound
    {view : ForestView} {inventory : Inventory}
    {plan : CompiledParserPackPlan}
    (accepted : validateForPlan view inventory plan = true) :
    CoversPlan view inventory plan := by
  rw [validateForPlan, Bool.and_eq_true_iff] at accepted
  exact {
    toCovers := validate_sound accepted.1
    authorized :=
      (inventory.authorizationValid_eq_true_iff plan).mp accepted.2
  }

/-! ## Positive and negative controls -/

private def canarySymbolNode : Node := {
  kind := .symbol 3
  scalarStart := 0
  scalarStop := 1
  byteStart := 0
  byteStop := 1
  choiceBegin := 0
  choiceCount := 1
}

private def canaryTerminalNode : Node := {
  kind := .terminal 10 (.scalar 65)
  scalarStart := 0
  scalarStop := 1
  byteStart := 0
  byteStop := 1
  choiceBegin := 1
  choiceCount := 0
}

private def canaryChoice : Choice := {
  parent := 0
  prefixNode := none
  childNode := 1
  productionIndex := 7
  scalarPivot := 0
  bytePivot := 0
}

private def canaryView : ForestView := {
  nodes := [canarySymbolNode, canaryTerminalNode]
  choices := [canaryChoice]
  roots := [0]
  codepoints := [65]
  byteOffsets := [0, 1]
}

private def canaryInventory : Inventory := {
  symbols := [{ identifier := 3, meaning := "Value" }]
  terminals := [{ identifier := 10, meaning := .char 65 }]
  productions := [{ identifier := 7, meaning := .lexical 0 }]
}

private def canaryPlan : CompiledParserPackPlan := {
  lexical := {
    profileName := "NativeForestIdentityCanary"
    startSort := "Value"
    classes := []
    productions := [{
      label := "value-a"
      resultSort := "Value"
      matcher := .char 65
      childSlots := [0]
    }]
  }
  structural := []
}

theorem canary_validate : validate canaryView canaryInventory = true := by
  decide

theorem canary_covered : Covers canaryView canaryInventory :=
  validate_sound canary_validate

theorem canary_validateForPlan :
    validateForPlan canaryView canaryInventory canaryPlan = true := by
  decide

theorem canary_coversPlan :
    CoversPlan canaryView canaryInventory canaryPlan :=
  validateForPlan_sound canary_validateForPlan

/-- A duplicate symbol key is rejected even when both rows claim the same
meaning; otherwise a later row could be misleading shadow data. -/
theorem duplicate_symbol_key_rejected :
    validate canaryView
      { canaryInventory with symbols :=
          [{ identifier := 3, meaning := "Value" },
           { identifier := 3, meaning := "Value" }] } = false := by
  decide

/-- Every used terminal identifier needs an independently supplied matcher. -/
theorem missing_terminal_identity_rejected :
    validate canaryView { canaryInventory with terminals := [] } = false := by
  decide

/-- A mutation of a physical production occurrence cannot silently reuse the
meaning attached to a different occurrence. -/
theorem changed_production_occurrence_rejected :
    validate { canaryView with choices :=
      [{ canaryChoice with productionIndex := 8 }] }
      canaryInventory = false := by
  decide

/-- A total table cannot introduce a result sort absent from the plan. -/
theorem invented_symbol_meaning_rejected :
    validateForPlan canaryView
      { canaryInventory with symbols :=
          [{ identifier := 3, meaning := "Invented" }] }
      canaryPlan = false := by
  decide

/-- A total table cannot introduce a terminal matcher absent from the plan. -/
theorem invented_terminal_meaning_rejected :
    validateForPlan canaryView
      { canaryInventory with terminals :=
          [{ identifier := 10, meaning := .any }] }
      canaryPlan = false := by
  decide

/-- A production row must point to an actual physical plan occurrence. -/
theorem unresolved_production_meaning_rejected :
    validateForPlan canaryView
      { canaryInventory with productions :=
          [{ identifier := 7, meaning := .lexical 1 }] }
      canaryPlan = false := by
  decide

/-- Two distinct physical production identifiers may deliberately retain two
distinct source-row occurrences even when their other semantics coincide. -/
theorem distinct_production_occurrences_remain_distinct :
    IdentityRow.lookup 7
        [{ identifier := 7, meaning := ProductionRef.structural 2 },
         { identifier := 8, meaning := ProductionRef.structural 3 }] =
          some (.structural 2) ∧
      IdentityRow.lookup 8
        [{ identifier := 7, meaning := ProductionRef.structural 2 },
         { identifier := 8, meaning := ProductionRef.structural 3 }] =
          some (.structural 3) := by
  decide

end Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityInventory
