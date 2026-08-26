import Mettapedia.GSLT.Parsing.ClassAwareNativeForestReachabilityValidation

/-!
# Semantic validation of native forest terminal leaves

An identity table can license a terminal matcher without proving that a
particular terminal payload satisfies it.  This module checks the exact
scalar or EOF occurrence against the supplied profile and immutable input,
and constructs both terminal-value and ParserPack matcher evidence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareNativeForestTerminalValidation

open Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityInventory
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestReachabilityValidation
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ParserProfileSemantics

/-- Executable exact-span semantics for one licensed terminal payload. -/
def terminalSemanticValid
    (profile : ParserProfileLayer) (input : List Nat)
    (matcher : TerminalMatcher) (value : TerminalValue)
    (start stop : Nat) : Bool :=
  match matcher, value with
  | .any, .scalar codepoint =>
      input[start]? == some codepoint && stop == start + 1
  | .eof, .eof =>
      decide (start = input.length) && stop == start
  | .char expected, .scalar codepoint =>
      expected == codepoint &&
        input[start]? == some codepoint && stop == start + 1
  | .class className, .scalar codepoint =>
      input[start]? == some codepoint &&
        profile.classAccepts? className codepoint == some true &&
        stop == start + 1
  | _, _ => false

/-- Successful leaf checking constructs the exact two semantic witnesses
consumed by `ChildDerivation.terminal`. -/
def terminalSemanticValid_sound
    {profile : ParserProfileLayer} {input : List Nat}
    {matcher : TerminalMatcher} {value : TerminalValue}
    {start stop : Nat}
    (accepted :
      terminalSemanticValid profile input matcher value start stop = true) :
    TerminalValueAgrees input value start stop ×
      TerminalMatchesAt profile input matcher start stop := by
  cases matcher <;> cases value <;>
    simp [terminalSemanticValid] at accepted
  case any.scalar codepoint =>
    rcases accepted with ⟨lookup, stopExact⟩
    subst stop
    exact ⟨.scalar lookup, .any lookup⟩
  case eof.eof =>
    rcases accepted with ⟨startExact, stopExact⟩
    subst stop
    exact ⟨.eof startExact, .eof startExact⟩
  case char.scalar expected codepoint =>
    rcases accepted with ⟨⟨expectedExact, lookup⟩, stopExact⟩
    subst expected
    subst stop
    exact ⟨.scalar lookup, .char lookup⟩
  case class.scalar className codepoint =>
    rcases accepted with ⟨⟨lookup, classEvidence⟩, stopExact⟩
    subst stop
    exact ⟨.scalar lookup, .classMember lookup classEvidence⟩

/-- Typed semantic evidence for one native node.  Nonterminal node kinds have
no terminal obligation; a terminal retains its exact licensed matcher. -/
def TerminalNodeEvidence
    (inventory : Inventory) (profile : ParserProfileLayer)
    (input : List Nat) (node : Node) : Type :=
  match node.kind with
  | .terminal terminalId value =>
      Sigma fun matcher =>
        PLift (inventory.toTable.terminalMatcher? terminalId = some matcher) ×
          PLift (node.choiceCount = 0) ×
          TerminalValueAgrees input value node.scalarStart node.scalarStop ×
          TerminalMatchesAt profile input matcher
            node.scalarStart node.scalarStop
  | .epsilon | .symbol _ | .intermediate _ _ => Unit

def terminalNodeValid
    (inventory : Inventory) (profile : ParserProfileLayer)
    (input : List Nat) (node : Node) : Bool :=
  match node.kind with
  | .terminal terminalId value =>
      decide (node.choiceCount = 0) &&
        match IdentityRow.lookup terminalId inventory.terminals with
        | none => false
        | some matcher =>
            terminalSemanticValid profile input matcher value
              node.scalarStart node.scalarStop
  | .epsilon | .symbol _ | .intermediate _ _ => true

/-- The Boolean leaf check returns a complete typed witness. -/
def terminalNodeValid_sound
    {inventory : Inventory} {profile : ParserProfileLayer}
    {input : List Nat} {node : Node}
    (accepted : terminalNodeValid inventory profile input node = true) :
    TerminalNodeEvidence inventory profile input node := by
  rcases node with
    ⟨kind, scalarStart, scalarStop, byteStart, byteStop,
      choiceBegin, choiceCount⟩
  cases kind with
  | epsilon => exact ()
  | symbol symbolId => exact ()
  | intermediate production dot => exact ()
  | terminal terminalId value =>
      simp only [terminalNodeValid, Bool.and_eq_true_iff] at accepted
      rcases accepted with ⟨noChoices, semanticAccepted⟩
      cases matcherLookup :
          IdentityRow.lookup terminalId inventory.terminals with
      | none => simp [matcherLookup] at semanticAccepted
      | some matcher =>
          rw [matcherLookup] at semanticAccepted
          rcases terminalSemanticValid_sound semanticAccepted with
            ⟨valueAgrees, terminalMatches⟩
          exact ⟨matcher,
            ⟨by simpa [Inventory.toTable] using matcherLookup⟩,
            ⟨of_decide_eq_true noChoices⟩,
            valueAgrees, terminalMatches⟩

def validateTerminals
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) : Bool :=
  view.nodes.all (terminalNodeValid inventory profile view.codepoints)

/-- Every node occurrence in an accepted snapshot carries its appropriate
typed terminal evidence. -/
def validateTerminals_sound
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer}
    (accepted : validateTerminals view inventory profile = true) :
    ∀ node, node ∈ view.nodes →
      TerminalNodeEvidence inventory profile view.codepoints node := by
  intro node member
  exact terminalNodeValid_sound
    ((List.all_eq_true.mp accepted) node member)

/-- Typed leaf evidence plugs directly into the native forest's semantic
child judgment.  The separately supplied `NodeAt` proof contributes the
physical occurrence and byte-span facts. -/
def TerminalNodeEvidence.childDerivation
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {input : List Nat}
    {nodeIndex terminalId : Nat} {value : TerminalValue}
    {start stop byteStart byteStop choiceBegin choiceCount : Nat}
    (nodeAt : NodeAt view nodeIndex {
      kind := .terminal terminalId value
      scalarStart := start
      scalarStop := stop
      byteStart := byteStart
      byteStop := byteStop
      choiceBegin := choiceBegin
      choiceCount := choiceCount
    })
    (evidence : TerminalNodeEvidence inventory profile input {
      kind := .terminal terminalId value
      scalarStart := start
      scalarStop := stop
      byteStart := byteStart
      byteStop := byteStop
      choiceBegin := choiceBegin
      choiceCount := choiceCount
    }) :
    Sigma fun matcher =>
      ChildDerivation view inventory.toTable profile input nodeIndex
        [.terminal matcher start stop] := by
  rcases evidence with
    ⟨matcher, ⟨matcherAt⟩, ⟨noChoices⟩,
      valueAgrees, terminalMatches⟩
  change choiceCount = 0 at noChoices
  change TerminalValueAgrees input value start stop at valueAgrees
  change TerminalMatchesAt profile input matcher start stop at terminalMatches
  subst choiceCount
  exact ⟨matcher,
    ChildDerivation.terminal nodeAt matcherAt
      valueAgrees terminalMatches⟩

/-- All executable premises available before recursive binary-family
decoding.  The name is intentionally weaker than `Represents`: exact roots,
families, and choice derivations are not fields of this structure. -/
structure FamilyDecodingInputs
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) : Type where
  structural : StructurallyComplete view
  identities : CoversPlan view inventory plan
  terminals : ∀ node, node ∈ view.nodes →
    TerminalNodeEvidence inventory profile view.codepoints node

def validateFamilyDecodingInputs
    (view : ForestView) (inventory : Inventory)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) : Bool :=
  validateStructure view && validateForPlan view inventory plan &&
    validateTerminals view inventory profile

def validateFamilyDecodingInputs_sound
    {view : ForestView} {inventory : Inventory}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (accepted :
      validateFamilyDecodingInputs view inventory profile plan = true) :
    FamilyDecodingInputs view inventory profile plan := by
  rw [validateFamilyDecodingInputs, Bool.and_eq_true_iff,
    Bool.and_eq_true_iff] at accepted
  exact {
    structural := validateStructure_sound accepted.1.1
    identities := validateForPlan_sound accepted.1.2
    terminals := validateTerminals_sound accepted.2
  }

/-! ## Positive and negative controls -/

private def canaryProfile : ParserProfileLayer := {
  name := "NativeTerminalCanary"
  startSort := "Value"
  classes := [{ name := "capital-a", kind := .points [65] }]
  states := []
}

private def canaryInventory : Inventory := {
  symbols := [{ identifier := 5, meaning := "Value" }]
  terminals := [
    { identifier := 1, meaning := .any },
    { identifier := 2, meaning := .eof },
    { identifier := 3, meaning := .char 65 },
    { identifier := 4, meaning := .class "capital-a" }]
  productions := [{ identifier := 6, meaning := .lexical 0 }]
}

private def terminalNode
    (terminalId : Nat) (value : TerminalValue)
    (start stop : Nat) : Node := {
  kind := .terminal terminalId value
  scalarStart := start
  scalarStop := stop
  byteStart := start
  byteStop := stop
  choiceBegin := 0
  choiceCount := 0
}

theorem any_scalar_accepted :
    terminalNodeValid canaryInventory canaryProfile [65]
      (terminalNode 1 (.scalar 65) 0 1) = true := by
  decide

theorem exact_char_accepted :
    terminalNodeValid canaryInventory canaryProfile [65]
      (terminalNode 3 (.scalar 65) 0 1) = true := by
  decide

theorem class_member_accepted :
    terminalNodeValid canaryInventory canaryProfile [65]
      (terminalNode 4 (.scalar 65) 0 1) = true := by
  decide

theorem eof_accepted :
    terminalNodeValid canaryInventory canaryProfile [65]
      (terminalNode 2 .eof 1 1) = true := by
  decide

theorem wrong_character_rejected :
    terminalNodeValid canaryInventory canaryProfile [66]
      (terminalNode 3 (.scalar 66) 0 1) = false := by
  decide

theorem nonmember_class_rejected :
    terminalNodeValid canaryInventory canaryProfile [66]
      (terminalNode 4 (.scalar 66) 0 1) = false := by
  decide

theorem malformed_eof_span_rejected :
    terminalNodeValid canaryInventory canaryProfile [65]
      (terminalNode 2 .eof 0 0) = false := by
  decide

theorem witness_without_authored_semantics_rejected :
    terminalNodeValid canaryInventory canaryProfile [65]
      (terminalNode 1 (.witness 9) 0 1) = false := by
  decide

private def familyCanaryPlan : CompiledParserPackPlan := {
  lexical := {
    profileName := "NativeTerminalCanary"
    startSort := "Value"
    classes := canaryProfile.classes
    productions := [{
      label := "value-a"
      resultSort := "Value"
      matcher := .char 65
      childSlots := [0]
    }]
  }
  structural := []
}

private def familyCanaryInventory : Inventory := {
  symbols := [{ identifier := 5, meaning := "Value" }]
  terminals := [{ identifier := 3, meaning := .char 65 }]
  productions := [{ identifier := 6, meaning := .lexical 0 }]
}

private def familyCanarySymbol : Node := {
  kind := .symbol 5
  scalarStart := 0
  scalarStop := 1
  byteStart := 0
  byteStop := 1
  choiceBegin := 0
  choiceCount := 1
}

private def familyCanaryChoice : Choice := {
  parent := 0
  prefixNode := none
  childNode := 1
  productionIndex := 6
  scalarPivot := 0
  bytePivot := 0
}

private def familyCanaryView : ForestView := {
  nodes := [familyCanarySymbol, terminalNode 3 (.scalar 65) 0 1]
  choices := [familyCanaryChoice]
  roots := [0]
  codepoints := [65]
  byteOffsets := [0, 1]
}

theorem familyCanary_validateInputs :
    validateFamilyDecodingInputs familyCanaryView familyCanaryInventory
      canaryProfile familyCanaryPlan = true := by
  decide

def familyCanary_inputs :
    FamilyDecodingInputs familyCanaryView familyCanaryInventory
      canaryProfile familyCanaryPlan :=
  validateFamilyDecodingInputs_sound familyCanary_validateInputs

end Mettapedia.GSLT.Parsing.ClassAwareNativeForestTerminalValidation
