import Mettapedia.OSLF.Framework.GrammarDerives
import Mettapedia.GSLT.Parsing.ParserProfileSemantics
import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-! Readback of a selected native parser packet against its authored grammar
and lexical profile. This boundary checks one retained tree; ambiguity policy,
source-to-IR lowering and execution remain separate. Packets are frontend data.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacket

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
abbrev Packet := Mettapedia.Languages.MeTTa.OSLFCore.Atom

def packetNodes : Packet → Nat
  | .expression children => 1 + listNodes children
  | _ => 1
where
  listNodes : List Packet → Nat
    | [] => 0
    | first :: rest => packetNodes first + listNodes rest

/-- Child packets use the parser ABI's ordered pair/nil encoding. -/
def children? : Packet → Option (List Packet)
  | .symbol "nil" => some []
  | .expression [.symbol "pair", first, rest] => (first :: ·) <$> children? rest
  | single => some [single]

def node? : Packet → Option (String × List Packet)
  | .expression [.symbol "node", .symbol label, body] =>
      (label, ·) <$> children? body
  | _ => none

private def structuralRow? (grammar : LanguageDef) (label : String) : Option GrammarRule :=
  match grammar.terms.filter (fun row => row.label == label) with
  | [row] => some row
  | _ => none

private def lexicalRow? (profile : ParserProfileLayer) (label : String) : Option LexicalStateDecl :=
  match profile.states.filter (fun row => row.ruleLabel == label) with
  | [row] => some row
  | _ => none

/-- Reconstruction consumes terminals from the actual declaration, rather
than guessing spelling from production labels. Duplicate labels are refused. -/
def readbackFuel? (grammar : LanguageDef) (profile : ParserProfileLayer) :
    Nat → String → Packet → Option String
  | 0, _, _ => none
  | fuel + 1, expected, packet => do
      match packet with
      | .expression [.symbol "node", .symbol label,
          .expression [.symbol "cp", .grounded (.int point)]] =>
          let row ← lexicalRow? profile label
          if row.resultSort != expected || point < 0 then none else do
            let scalar := point.toNat
            if profile.classAccepts? row.className scalar != some true then none else
              some (String.singleton (Char.ofNat scalar))
      | _ =>
          let (label, children) ← node? packet
          let row ← structuralRow? grammar label
          if row.category != expected || children.length != row.params.length then none else do
            let items ← row.syntaxPattern.mapM fun
              | .terminal text => some (Sum.inl text : Sum String String)
              | .nonTerminal name => some (Sum.inr name : Sum String String)
              | .separator _ | .delimiter _ _ | .op _ => none
            let mut remaining := children
            let mut text := ""
            for item in items do
              match item with
              | .inl literal => text := text ++ literal
              | .inr parameter =>
                  let first :: rest := remaining | none
                  let sort ← Mettapedia.OSLF.Framework.GrammarDerives.paramSort? row parameter
                  let child ← readbackFuel? grammar profile fuel sort first
                  text := text ++ child
                  remaining := rest
            if remaining.isEmpty then some text else none

def readback? (grammar : LanguageDef) (profile : ParserProfileLayer)
    (expected : String) (packet : Packet) : Option String :=
  readbackFuel? grammar profile (packetNodes packet + 1) expected packet

/-- Exact readback is a frontend admission check, not parser completeness or
semantic equivalence of a lowered program. -/
def validates (grammar : LanguageDef) (profile : ParserProfileLayer)
    (expected input : String) (packet : Packet) : Bool :=
  readback? grammar profile expected packet == some input

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacket
