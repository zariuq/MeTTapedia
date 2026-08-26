import Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat
import Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityInventory

/-!
# Canonical semantic-identity packet for a native ParserPack forest

The neutral `CNF1` forest deliberately carries only disposable native
identifiers.  This module specifies a separate opt-in `PNI1` qualification
packet.  Its production rows carry semantic descriptors, not claimed source
positions.  The supplied ParserPack plan resolves each descriptor uniquely to
an exact lexical or structural occurrence; an absent or ambiguous descriptor
is rejected.

This separation keeps semantic authority in the authored target plan and
keeps identity strings and resolution work out of prepared parser hot paths.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityWire

open Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityInventory
open Mettapedia.GSLT.Parsing.ClassAwarePackedForest
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence

/-- The operational fields of a ParserPack production that survive in the
native grammar.  Source-only annotations are deliberately absent. -/
structure ProductionDescriptor where
  label : String
  resultSort : String
  items : List PackItem
  childSlots : List Nat
  deriving DecidableEq, Repr

def lexicalDescriptor
    (production : CompiledLexicalProduction) : ProductionDescriptor := {
  label := production.label
  resultSort := production.resultSort
  items := [.terminal production.matcher]
  childSlots := production.childSlots
}

def structuralDescriptor
    (production : CompiledStructuralProduction) : ProductionDescriptor := {
  label := production.label
  resultSort := production.resultSort
  items := production.items
  childSlots := production.childSlots
}

/-- Every exact target occurrence paired with its operational descriptor. -/
def planProductionRows
    (plan : CompiledParserPackPlan) :
    List (ProductionRef × ProductionDescriptor) :=
  (plan.lexical.productions.zipIdx.map fun
      | (production, position) =>
          (ProductionRef.lexical position, lexicalDescriptor production)) ++
    (plan.structural.zipIdx.map fun
      | (production, position) =>
          (ProductionRef.structural position,
            structuralDescriptor production))

/-- Resolve only a unique exact descriptor.  Neither labels nor table
positions alone authorize a source occurrence. -/
def resolveProduction?
    (plan : CompiledParserPackPlan)
    (descriptor : ProductionDescriptor) : Option ProductionRef :=
  match (planProductionRows plan).filter (fun row => row.2 == descriptor) with
  | [(production, _)] => some production
  | _ => none

/-- The semantic fact retained by successful descriptor resolution. -/
def DescriptorResolves
    (plan : CompiledParserPackPlan)
    (descriptor : ProductionDescriptor)
    (production : ProductionRef) : Prop :=
  (production, descriptor) ∈ planProductionRows plan

theorem resolveProduction?_sound
    {plan : CompiledParserPackPlan}
    {descriptor : ProductionDescriptor}
    {production : ProductionRef}
    (resolved : resolveProduction? plan descriptor = some production) :
    DescriptorResolves plan descriptor production := by
  unfold resolveProduction? at resolved
  generalize filteredEq :
      (planProductionRows plan).filter (fun row => row.2 == descriptor) =
        filteredRows at resolved
  cases filteredRows with
  | nil => simp at resolved
  | cons head tail =>
      cases tail with
      | nil =>
          simp only at resolved
          cases head with
          | mk candidate candidateDescriptor =>
              simp only [Option.some.injEq] at resolved
              subst candidate
              have memberFiltered :
                  (production, candidateDescriptor) ∈
                    (planProductionRows plan).filter
                      (fun row => row.2 == descriptor) := by
                rw [filteredEq]
                simp
              rcases List.mem_filter.mp memberFiltered with
                ⟨member, descriptorExact⟩
              have exactMeaning : candidateDescriptor = descriptor := by
                exact of_decide_eq_true descriptorExact
              simpa [DescriptorResolves, exactMeaning] using member
      | cons second rest => simp at resolved

/-! ## Reified identity rows -/

structure SymbolRow where
  identifier : Nat
  resultSort : String
  deriving DecidableEq, Repr

structure TerminalRow where
  identifier : Nat
  matcher : TerminalMatcher
  deriving DecidableEq, Repr

structure ProductionRow where
  identifier : Nat
  descriptor : ProductionDescriptor
  deriving DecidableEq, Repr

/-- Provenance strings identify the exact C-side source/profile compilation.
Their relation to source files remains a later reproducible-build obligation;
they do not grant semantic authority by themselves. -/
structure Snapshot where
  languageSourceDigest : String
  profileSourceDigest : String
  bindingDigest : String
  packDigest : String
  symbols : List SymbolRow
  terminals : List TerminalRow
  productions : List ProductionRow
  deriving DecidableEq, Repr

private def textBytes (text : String) : List UInt8 :=
  text.toUTF8.data.toList

private def encodeString (text : String) : List UInt8 :=
  encodeText (textBytes text)

private def readString : Reader String := fun input => do
  let (bytes, rest) ← readText input
  let text ← String.fromUTF8? ⟨bytes.toArray⟩
  if textBytes text = bytes then some (text, rest) else none

private def encodeMatcher (matcher : TerminalMatcher) : List UInt8 :=
  match matcher with
  | .any => encodeUInt32LE 0 ++ encodeUInt32LE 0 ++ encodeString ""
  | .eof => encodeUInt32LE 1 ++ encodeUInt32LE 0 ++ encodeString ""
  | .char codepoint =>
      encodeUInt32LE 2 ++ encodeUInt32LE (UInt32.ofNat codepoint) ++
        encodeString ""
  | .class className =>
      encodeUInt32LE 3 ++ encodeUInt32LE 0 ++ encodeString className

private def readMatcher : Reader TerminalMatcher := fun input => do
  let (kind, rest1) ← readUInt32LE input
  let (codepoint, rest2) ← readUInt32LE rest1
  let (className, rest) ← readString rest2
  match kind.toNat with
  | 0 => if codepoint = 0 ∧ className = "" then some (.any, rest) else none
  | 1 => if codepoint = 0 ∧ className = "" then some (.eof, rest) else none
  | 2 => if className = "" then some (.char codepoint.toNat, rest) else none
  | 3 =>
      if codepoint = 0 ∧ className ≠ "" then some (.class className, rest)
      else none
  | _ => none

private def encodeItem : PackItem → List UInt8
  | .terminal matcher => encodeUInt32LE 0 ++ encodeMatcher matcher
  | .nonterminal resultSort => encodeUInt32LE 1 ++ encodeString resultSort

private def readItem : Reader PackItem := fun input => do
  let (kind, rest) ← readUInt32LE input
  match kind.toNat with
  | 0 =>
      let (matcher, suffix) ← readMatcher rest
      some (.terminal matcher, suffix)
  | 1 =>
      let (resultSort, suffix) ← readString rest
      if resultSort = "" then none else some (.nonterminal resultSort, suffix)
  | _ => none

private def encodeSymbolRow (row : SymbolRow) : List UInt8 :=
  encodeUInt32LE (UInt32.ofNat row.identifier) ++ encodeString row.resultSort

private def readSymbolRow : Reader SymbolRow := fun input => do
  let (identifier, rest1) ← readUInt32LE input
  let (resultSort, rest) ← readString rest1
  if resultSort = "" then none
  else some ({ identifier := identifier.toNat, resultSort }, rest)

private def encodeTerminalRow (row : TerminalRow) : List UInt8 :=
  encodeUInt32LE (UInt32.ofNat row.identifier) ++ encodeMatcher row.matcher

private def readTerminalRow : Reader TerminalRow := fun input => do
  let (identifier, rest1) ← readUInt32LE input
  let (matcher, rest) ← readMatcher rest1
  some ({ identifier := identifier.toNat, matcher }, rest)

private def encodeProductionRow (row : ProductionRow) : List UInt8 :=
  encodeUInt32LE (UInt32.ofNat row.identifier) ++
    encodeString row.descriptor.label ++
    encodeString row.descriptor.resultSort ++
    encodeUInt32LE (UInt32.ofNat row.descriptor.items.length) ++
    row.descriptor.items.flatMap encodeItem ++
    encodeUInt32LE (UInt32.ofNat row.descriptor.childSlots.length) ++
    row.descriptor.childSlots.flatMap fun slot =>
      encodeUInt32LE (UInt32.ofNat slot)

private def readProductionRow : Reader ProductionRow := fun input => do
  let (identifier, rest1) ← readUInt32LE input
  let (label, rest2) ← readString rest1
  let (resultSort, rest3) ← readString rest2
  if label = "" ∨ resultSort = "" then none
  else
    let (itemCount, rest4) ← readUInt32LE rest3
    let (items, rest5) ← readMany readItem itemCount.toNat rest4
    let (childCount, rest6) ← readUInt32LE rest5
    let (childSlots, rest) ←
      readMany readUInt32LE childCount.toNat rest6
    some ({
      identifier := identifier.toNat
      descriptor := {
        label
        resultSort
        items
        childSlots := childSlots.map UInt32.toNat
      }
    }, rest)

private def magic : List UInt8 := [80, 78, 73, 49]

private def readMagic : Reader Unit
  | 80 :: 78 :: 73 :: 49 :: rest => some ((), rest)
  | _ => none

/-- Canonical, struct-layout-independent `PNI1` encoding. -/
def encodeSnapshot (snapshot : Snapshot) : List UInt8 :=
  magic ++
    encodeString snapshot.languageSourceDigest ++
    encodeString snapshot.profileSourceDigest ++
    encodeString snapshot.bindingDigest ++
    encodeString snapshot.packDigest ++
    encodeUInt32LE (UInt32.ofNat snapshot.symbols.length) ++
    encodeUInt32LE (UInt32.ofNat snapshot.terminals.length) ++
    encodeUInt32LE (UInt32.ofNat snapshot.productions.length) ++
    snapshot.symbols.flatMap encodeSymbolRow ++
    snapshot.terminals.flatMap encodeTerminalRow ++
    snapshot.productions.flatMap encodeProductionRow

/-- Exact decoder: malformed UTF-8, noncanonical matcher fields, truncation,
or trailing bytes are rejected. -/
def decodeSnapshot? (input : List UInt8) : Option Snapshot := do
  let (_, rest1) ← readMagic input
  let (languageSourceDigest, rest2) ← readString rest1
  let (profileSourceDigest, rest3) ← readString rest2
  let (bindingDigest, rest4) ← readString rest3
  let (packDigest, rest5) ← readString rest4
  let (symbolCount, rest6) ← readUInt32LE rest5
  let (terminalCount, rest7) ← readUInt32LE rest6
  let (productionCount, rest8) ← readUInt32LE rest7
  let (symbols, rest9) ← readMany readSymbolRow symbolCount.toNat rest8
  let (terminals, rest10) ←
    readMany readTerminalRow terminalCount.toNat rest9
  let (productions, rest) ←
    readMany readProductionRow productionCount.toNat rest10
  if rest.isEmpty then
    some {
      languageSourceDigest := languageSourceDigest
      profileSourceDigest := profileSourceDigest
      bindingDigest := bindingDigest
      packDigest := packDigest
      symbols := symbols
      terminals := terminals
      productions := productions
    }
  else none

/-- Resolve every physical production row through the supplied target plan.
This is the point at which raw C descriptors acquire `ProductionRef`
meaning. -/
def Snapshot.resolveInventory?
    (snapshot : Snapshot) (plan : CompiledParserPackPlan) : Option Inventory := do
  let productions ← snapshot.productions.mapM fun row => do
    let production ← resolveProduction? plan row.descriptor
    pure { identifier := row.identifier, meaning := production }
  pure {
    symbols := snapshot.symbols.map fun row =>
      { identifier := row.identifier, meaning := row.resultSort }
    terminals := snapshot.terminals.map fun row =>
      { identifier := row.identifier, meaning := row.matcher }
    productions
  }

/-! ## Executable controls -/

private def canaryLexicalProduction : CompiledLexicalProduction := {
  label := "value-digit"
  resultSort := "Value"
  matcher := .class "digit"
  childSlots := [0]
}

private def canaryStructuralProduction : CompiledStructuralProduction := {
  label := "value-array"
  resultSort := "Value"
  items := [.terminal (.char 91), .nonterminal "Value",
    .terminal (.char 93), .terminal .eof]
  childSlots := [1]
  source := {
    label := "value-array"
    category := "Value"
    params := []
    syntaxPattern := []
  }
}

private def canaryPlan : CompiledParserPackPlan := {
  lexical := {
    profileName := "IdentityWireCanary"
    startSort := "Value"
    classes := []
    productions := [canaryLexicalProduction]
  }
  structural := [canaryStructuralProduction]
}

private def lexicalCanaryDescriptor : ProductionDescriptor :=
  lexicalDescriptor canaryLexicalProduction

private def structuralCanaryDescriptor : ProductionDescriptor :=
  structuralDescriptor canaryStructuralProduction

private def canarySnapshot : Snapshot := {
  languageSourceDigest := String.replicate 64 'a'
  profileSourceDigest := String.replicate 64 'b'
  bindingDigest := String.replicate 64 'c'
  packDigest := String.replicate 64 'd'
  symbols := [{ identifier := 4, resultSort := "Value" }]
  terminals := [
    { identifier := 2, matcher := .class "digit" },
    { identifier := 3, matcher := .char 91 },
    { identifier := 5, matcher := .eof }]
  productions := [
    { identifier := 7, descriptor := lexicalCanaryDescriptor },
    { identifier := 9, descriptor := structuralCanaryDescriptor }]
}

theorem canary_roundtrip :
    decodeSnapshot? (encodeSnapshot canarySnapshot) = some canarySnapshot := by
  set_option maxRecDepth 100000 in
    decide +kernel

theorem lexical_descriptor_resolves :
    resolveProduction? canaryPlan lexicalCanaryDescriptor = some (.lexical 0) := by
  decide +kernel

theorem structural_descriptor_resolves :
    resolveProduction? canaryPlan structuralCanaryDescriptor =
      some (.structural 0) := by
  decide +kernel

theorem canary_inventory_resolves :
    canarySnapshot.resolveInventory? canaryPlan = some {
      symbols := [{ identifier := 4, meaning := "Value" }]
      terminals := [
        { identifier := 2, meaning := TerminalMatcher.class "digit" },
        { identifier := 3, meaning := TerminalMatcher.char 91 },
        { identifier := 5, meaning := TerminalMatcher.eof }]
      productions := [
        { identifier := 7, meaning := ProductionRef.lexical 0 },
        { identifier := 9, meaning := ProductionRef.structural 0 }]
    } := by
  decide +kernel

/-- A semantic mutation is not accepted merely because the production label
and physical identifier remain unchanged. -/
theorem changed_production_items_rejected :
    resolveProduction? canaryPlan
      { structuralCanaryDescriptor with
        items := [.terminal (.char 91), .terminal (.char 93), .terminal .eof] } =
      none := by
  decide +kernel

/-- Equal operational descriptors at two target occurrences are ambiguous and
therefore cannot be assigned an arbitrary source occurrence. -/
theorem ambiguous_descriptor_rejected :
    let duplicatePlan : CompiledParserPackPlan := {
      canaryPlan with
      structural := canaryPlan.structural ++ canaryPlan.structural
    }
    resolveProduction? duplicatePlan structuralCanaryDescriptor = none := by
  decide +kernel

/-- Trailing bytes cannot hide a second packet or unverified metadata. -/
theorem trailing_byte_rejected :
    decodeSnapshot? (encodeSnapshot canarySnapshot ++ [0]) = none := by
  set_option maxRecDepth 100000 in
    decide +kernel

end Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityWire
