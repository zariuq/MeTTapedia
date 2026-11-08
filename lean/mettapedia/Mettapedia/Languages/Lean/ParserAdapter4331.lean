import Mettapedia.Languages.Lean.ParserDescription
import Lean

/-!
# Lean 4.33.1 parser-description adapter

All matches on Lean's descriptor representation are isolated here. Both
round trips are kernel proved. Every constructor is explicit, so a changed
host datatype cannot silently be mapped to a default. This is a lossless data
adapter, not a source-to-GSLT parsing correspondence theorem.

For a new release, keep the portable schema and generic dependency laws,
adapt the exhaustive matches and `indexed_agrees`, and requalify the live
controls before changing the accepted release/profile. Named parser aliases
remain implementation references; a version string alone does not certify them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.ParserAdapter4331

open ParserDescription

def profile : Mettapedia.GSLT.Parsing.KeyedParserDispatch.Profile :=
  { schema := 1, release := "4.33.1", adapter := "lean-parser-descr-v1" }

def hostSupported : Bool := Lean.versionString == profile.release

def exportName : Lean.Name → Name
  | .anonymous => .anonymous
  | .str parent component => .str (exportName parent) component
  | .num parent component => .num (exportName parent) component

def importName : Name → Lean.Name
  | .anonymous => .anonymous
  | .str parent component => .str (importName parent) component
  | .num parent component => .num (importName parent) component

@[simp] theorem import_export_name (name : Lean.Name) : importName (exportName name) = name := by
  induction name <;> simp_all [importName, exportName]

@[simp] theorem export_import_name (name : Name) : exportName (importName name) = name := by
  induction name <;> simp_all [importName, exportName]

def exportDescription : Lean.ParserDescr → Description
  | .const name => .constant (exportName name)
  | .unary name body => .unary (exportName name) (exportDescription body)
  | .binary name left right => .binary (exportName name) (exportDescription left) (exportDescription right)
  | .node kind prec body => .node (exportName kind) prec (exportDescription body)
  | .trailingNode kind prec lhs body => .trailingNode (exportName kind) prec lhs (exportDescription body)
  | .symbol text => .symbol text
  | .nonReservedSymbol text includeIdent => .nonReservedSymbol text includeIdent
  | .cat name prec => .category (exportName name) prec
  | .parser name => .parser (exportName name)
  | .nodeWithAntiquot name kind body => .nodeWithAntiquot name (exportName kind) (exportDescription body)
  | .sepBy body sep parser trailing => .sepBy (exportDescription body) sep (exportDescription parser) trailing
  | .sepBy1 body sep parser trailing => .sepBy1 (exportDescription body) sep (exportDescription parser) trailing
  | .unicodeSymbol text ascii preserve => .unicodeSymbol text ascii preserve

def importDescription : Description → Lean.ParserDescr
  | .constant name => .const (importName name)
  | .unary name body => .unary (importName name) (importDescription body)
  | .binary name left right => .binary (importName name) (importDescription left) (importDescription right)
  | .node kind prec body => .node (importName kind) prec (importDescription body)
  | .trailingNode kind prec lhs body => .trailingNode (importName kind) prec lhs (importDescription body)
  | .symbol text => .symbol text
  | .nonReservedSymbol text includeIdent => .nonReservedSymbol text includeIdent
  | .category name prec => .cat (importName name) prec
  | .parser name => .parser (importName name)
  | .nodeWithAntiquot name kind body => .nodeWithAntiquot name (importName kind) (importDescription body)
  | .sepBy body sep parser trailing => .sepBy (importDescription body) sep (importDescription parser) trailing
  | .sepBy1 body sep parser trailing => .sepBy1 (importDescription body) sep (importDescription parser) trailing
  | .unicodeSymbol text ascii preserve => .unicodeSymbol text ascii preserve

@[simp] theorem import_export (description : Lean.ParserDescr) :
    importDescription (exportDescription description) = description := by
  induction description <;> simp_all [importDescription, exportDescription]

@[simp] theorem export_import (description : Description) :
    exportDescription (importDescription description) = description := by
  induction description <;> simp_all [importDescription, exportDescription]

theorem export_injective : Function.Injective exportDescription := by
  intro first second same
  have := congrArg importDescription same
  simpa using this

def importPacket (packet : Packet) : Option Lean.ParserDescr :=
  if hostSupported && decide (packet.profile = profile)
  then some (importDescription packet.description) else none

theorem packet_roundtrip (declaration : Lean.Name)
    (phase : Mettapedia.GSLT.Parsing.KeyedParserDispatch.Phase) (description : Lean.ParserDescr)
    (supported : hostSupported = true) :
    importPacket ⟨profile, exportName declaration, phase, exportDescription description⟩ = some description := by
  simp [importPacket, supported]

theorem other_profile_refused (packet : Packet) (different : packet.profile ≠ profile) :
    importPacket packet = none := by
  simp [importPacket, different]

def exportBehavior : Lean.Parser.LeadingIdentBehavior →
    Mettapedia.GSLT.Parsing.KeyedParserDispatch.IdentBehavior
  | .default => .default
  | .symbol => .symbol
  | .both => .both

def importBehavior : Mettapedia.GSLT.Parsing.KeyedParserDispatch.IdentBehavior →
    Lean.Parser.LeadingIdentBehavior
  | .default => .default
  | .symbol => .symbol
  | .both => .both

def exportEntry : Lean.Parser.ParserExtension.OLeanEntry → RegistryEntry
  | .token text => .token text
  | .kind name => .kind (exportName name)
  | .category name declaration behavior =>
      .category (exportName name) (exportName declaration) (exportBehavior behavior)
  | .parser category declaration priority =>
      .parser (exportName category) (exportName declaration) priority

def importEntry : RegistryEntry → Lean.Parser.ParserExtension.OLeanEntry
  | .token text => .token text
  | .kind name => .kind (importName name)
  | .category name declaration behavior =>
      .category (importName name) (importName declaration) (importBehavior behavior)
  | .parser category declaration priority =>
      .parser (importName category) (importName declaration) priority

theorem import_export_entry (entry : Lean.Parser.ParserExtension.OLeanEntry) :
    importEntry (exportEntry entry) = entry := by
  cases entry with
  | category name declaration behavior =>
      cases behavior <;> simp [importEntry, exportEntry, importBehavior, exportBehavior]
  | token text | kind name | parser category declaration priority =>
      simp [importEntry, exportEntry]

theorem export_import_entry (entry : RegistryEntry) : exportEntry (importEntry entry) = entry := by
  cases entry with
  | category name declaration behavior =>
      cases behavior <;> simp [importEntry, exportEntry, importBehavior, exportBehavior]
  | token text | kind name | parser category declaration priority =>
      simp [importEntry, exportEntry]

def tokenView : Lean.Syntax → Mettapedia.GSLT.Parsing.KeyedParserDispatch.Token Lean.Name
  | .atom _ text => .atom (.mkSimple text)
  | .ident _ _ name _ => .ident name
  | .node _ kind _ => .node kind
  | .missing => .other

def tableView {Parser : Type} (category : Lean.Name)
    (phase : Mettapedia.GSLT.Parsing.KeyedParserDispatch.Phase)
    (table : Lean.Parser.TokenMap Parser) :
    Mettapedia.GSLT.Parsing.KeyedParserDispatch.Store Lean.Name Parser := fun key =>
  if key.category = category ∧ key.phase = phase then
    match key.token with
    | none => none
    | some name => table.get? name
  else none

/-- The portable dispatch semantics agrees with the pinned host's actual
indexed lookup after successful token classification. Lexical failures and
execution of the returned parsers are deliberately separate boundaries. -/
theorem indexed_agrees {Parser : Type} (table : Lean.Parser.TokenMap Parser)
    (category : Lean.Name) (phase : Mettapedia.GSLT.Parsing.KeyedParserDispatch.Phase)
    (context : Lean.Parser.ParserContext) (state after : Lean.Parser.ParserState)
    (token : Lean.Syntax) (behavior : Lean.Parser.LeadingIdentBehavior)
    (peek : Lean.Parser.peekToken context state = (after, .ok token)) :
    (Lean.Parser.indexed table context state behavior).2 =
      Mettapedia.GSLT.Parsing.KeyedParserDispatch.indexed (tableView category phase table)
        ⟨category, phase, tokenView token, exportBehavior behavior, Lean.identKind⟩ := by
  cases token with
  | missing =>
      simp [Lean.Parser.indexed, peek, tokenView,
        Mettapedia.GSLT.Parsing.KeyedParserDispatch.indexed]
  | atom info text =>
      cases found : table.get? (.mkSimple text) <;>
        simp [Lean.Parser.indexed, peek, tokenView, tableView, found,
          Mettapedia.GSLT.Parsing.KeyedParserDispatch.indexed,
          Mettapedia.GSLT.Parsing.KeyedParserDispatch.Request.key]
  | node info kind children =>
      cases found : table.get? kind <;>
        simp [Lean.Parser.indexed, peek, tokenView, tableView, found,
          Mettapedia.GSLT.Parsing.KeyedParserDispatch.indexed,
          Mettapedia.GSLT.Parsing.KeyedParserDispatch.Request.key]
  | ident info raw name resolved =>
      cases named : table.get? name <;> cases fallback : table.get? Lean.identKind <;>
        cases behavior <;> by_cases same : name = Lean.identKind <;>
        simp_all [Lean.Parser.indexed, tokenView, tableView, exportBehavior,
          Mettapedia.GSLT.Parsing.KeyedParserDispatch.indexed,
          Mettapedia.GSLT.Parsing.KeyedParserDispatch.Request.key]

end Mettapedia.Languages.Lean.ParserAdapter4331
