import Mettapedia.Languages.MeTTa.Experimental.DerivedTransformForms.Presentations
import Mettapedia.Languages.MeTTa.Experimental.DerivedTransformForms.Code
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketView
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxIO

/-!
# Grammar-checked source packets to derived forms

Both frontends use the same retained-packet interface and structural compiler.
Only declared trivia fields are erased. Interaction put/chain fields are
explicitly reordered into the operation roles of Code. Named logic variables
remain names in the PeTTa expansion; no lexical-freshness claim is inferred.

The checked packet boundary proves exact source readback and grammar origin.
It does not by itself prove whole-family semantic adequacy of the expansion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Experimental.DerivedTransformForms.Lowering

open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.OSLF.MeTTaIL.Syntax (TermParam Pattern)
open Presentations (Surface)
open SourcePacket (Packet packetNodes)
open OSLFCore (Atom)

abbrev Lower := Except String

def description (surface : Surface) : Lower Portable.SyntaxDescription :=
  SourcePacketView.requireSome "candidate grammar did not elaborate" (Presentations.description? surface)

def keepField : TermParam → Bool
  | .simple _ (.base "SrcTrivia") | .simple _ (.base "SrcSpacing") => false
  | _ => true

def view (surface : Surface) (source : Packet) : Lower (String × List Packet) :=
  SourcePacketView.view (description surface) keepField source

def text (surface : Surface) (sort : String) (source : Packet) : Lower String :=
  SourcePacketView.text (description surface) sort source

def term : Nat → Surface → Packet → Lower Atom
  | 0, _, _ => .error "term exceeds retained packet extent"
  | fuel + 1, surface, source => do
      let (label, fields) ← view surface source
      match label, fields with
      | "DSymbol", [word] =>
          match PeTTa.SpaceSemantics.readToken (← text surface "DName" word) with
          | .ok value => pure value
          | .error reason => .error reason
      | "DVariable", [word] => pure (.var (← text surface "DName" word))
      | "DSpace", [word] => pure (.symbol ("&" ++ (← text surface "DName" word)))
      | "DInteger", [number] =>
          let spelling ← text surface "SrcInteger" number
          let value ← SourcePacketView.requireSome "invalid integer" spelling.toInt?
          pure (.grounded (.int value))
      | "DString", [literal] =>
          let spelling ← text surface "SrcString" literal
          match PeTTa.SpaceSemantics.readSource spelling with
          | .ok [value] => pure value
          | _ => .error "invalid string literal"
      | "DPlus", [] => pure (.symbol "+")
      | "DMinus", [] => pure (.symbol "-")
      | "DEqual", [] => pure (.symbol "==")
      | "DComma", [] => pure (.symbol ",")
      | "DEmptyExpression", [] => pure (.expression [])
      | "DExpression", [items] => pure (.expression (← terms fuel surface items))
      | _, _ => .error s!"invalid term production {label}"
where
  terms : Nat → Surface → Packet → Lower (List Atom)
    | 0, _, _ => .error "term sequence exceeds retained packet extent"
    | fuel + 1, surface, source => do
        let (label, fields) ← view surface source
        match label, fields with
        | "DTermsOne", [item] => pure [← term fuel surface item]
        | "DTermsMore", [item, rest] => pure ((← term fuel surface item) :: (← terms fuel surface rest))
        | _, _ => .error s!"invalid term sequence {label}"

def code : Nat → Surface → Packet → Lower Code
  | 0, _, _ => .error "program exceeds retained packet extent"
  | fuel + 1, surface, source => do
      let (label, fields) ← view surface source
      let atom := term fuel surface
      let lower := code fuel surface
      match label, fields with
      | "DProgram", [body] => lower body
      | "DValue", [value] => pure (.value (← atom value))
      | "DMatch", [space, pattern, body] => pure (.read (← atom space) (← atom pattern) (← lower body))
      | "DAdd", [first, second] =>
          let (space, value) := if surface = .expression then (first, second) else (second, first)
          pure (.add (← atom space) (← atom value))
      | "DRemove", [space, pattern] => pure (.remove (← atom space) (← atom pattern))
      | "DTransform", [space, sources, template] =>
          pure (.transform (← atom space) (← atom sources) (← atom template) none)
      | "DInto", [space, sources, template, destination] =>
          pure (.transform (← atom space) (← atom sources) (← atom template) (some (← atom destination)))
      | "DOnce", [body] => pure (.first (← lower body))
      | "DCollapse", [body] => pure (.collect (← lower body))
      | "DChoice", [alternatives] => pure (.choice (← codes fuel surface alternatives))
      | "DEmptyChoice", [] => pure (.choice [])
      | "DLet", [pattern, initializer, body] => pure (.bind (← atom pattern) (← lower initializer) (← lower body))
      | "DChain", [first, second, body] =>
          let (initializer, binder) := if surface = .expression then (first, second) else (second, first)
          let .var name ← atom binder | .error "chain binder must be a variable"
          pure (.chain name (← lower initializer) (← lower body))
      | "DCount", [body] => pure (.count (← lower body))
      | "DFold", [step, generator, seed] => pure (.fold (← atom step) (← lower generator) (← lower seed))
      | "DCase", [subject, branches] => pure (.cases (← lower subject) (← cases fuel surface branches))
      | "DEmpty", [] => pure .empty
      | _, _ => .error s!"invalid program production {label}"
where
  codes : Nat → Surface → Packet → Lower (List Code)
    | 0, _, _ => .error "choice exceeds retained packet extent"
    | fuel + 1, surface, source => do
        let (label, fields) ← view surface source
        match label, fields with
        | "DCodesOne", [body] => pure [← code fuel surface body]
        | "DCodesMore", [body, rest] => pure ((← code fuel surface body) :: (← codes fuel surface rest))
        | _, _ => .error s!"invalid choice sequence {label}"
  cases : Nat → Surface → Packet → Lower (List (Atom × Code))
    | 0, _, _ => .error "case exceeds retained packet extent"
    | fuel + 1, surface, source => do
        let (label, fields) ← view surface source
        match label, fields with
        | "DCasesOne", [branch] => pure [← clause fuel surface branch]
        | "DCasesMore", [branch, rest] => pure ((← clause fuel surface branch) :: (← cases fuel surface rest))
        | _, _ => .error s!"invalid case sequence {label}"
  clause : Nat → Surface → Packet → Lower (Atom × Code)
    | 0, _, _ => .error "case branch exceeds retained packet extent"
    | fuel + 1, surface, source => do
        let (label, fields) ← view surface source
        match label, fields with
        | "DCaseClause", [pattern, body] => pure ((← term fuel surface pattern), (← code fuel surface body))
        | _, _ => .error s!"invalid case branch {label}"

def accepted (surface : Surface) (source : String) (packet : Packet) : Lower Code := do
  let spec ← description surface
  let _ ← SourcePacketView.requireSome "source packet does not reproduce this complete input"
    (SourceSyntaxIO.read? spec source packet)
  code (packetNodes packet + 1) surface packet

/-- Acceptance cannot substitute a tree for different input text or bypass
the shared grammar/profile certificate replay. This is a frontend claim. -/
theorem acceptance_has_source (surface : Surface) (source : String) (packet : Packet) (result : Code)
    (read : accepted surface source packet = .ok result) :
    ∃ spec core, description surface = .ok spec ∧ SourceSyntaxIO.read? spec source packet = some core ∧
      SourceSyntaxIO.print? spec core = some source := by
  cases spec : description surface with
  | error reason =>
      rw [accepted, spec] at read
      change Except.error reason = Except.ok result at read
      cases read
  | ok value =>
      cases replay : SourceSyntaxIO.read? value source packet with
      | none =>
          rw [accepted, spec] at read
          change (SourcePacketView.requireSome "source packet does not reproduce this complete input"
              (SourceSyntaxIO.read? value source packet) >>= fun _ =>
                code (packetNodes packet + 1) surface packet) = .ok result at read
          rw [replay] at read
          change Except.error "source packet does not reproduce this complete input" = Except.ok result at read
          cases read
      | some core => exact ⟨value, core, rfl, replay, SourceSyntaxIO.read_print value source packet core replay⟩

end Mettapedia.Languages.MeTTa.Experimental.DerivedTransformForms.Lowering
