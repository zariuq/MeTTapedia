import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacket
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxReader

/-! A selected native packet proposes finite certificate data. Unique
row lookup retains its labels and ordered children; scalar payloads must
agree with the actual input. The independent replay is the authority for
admission. Native packed-forest and selection coverage are separate. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketCertificate

open Mettapedia.GSLT.Parsing
open ParserProfileSemantics ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate
open ScalarSyntaxCore SourcePacket

private def unique? {α : Type} : List α → Option α
  | [value] => some value
  | _ => none

private def terminalStop (start : Nat) : TerminalMatcher → Nat
  | .eof => start
  | _ => start + 1

mutual
  def proposeFuel (plan : CompiledParserPackPlan) (input : List Nat) :
      Nat → String → Nat → Packet → Option (Nat × Certificate)
    | 0, _, _, _ => none
    | fuel + 1, sort, start, packet => do
      match packet with
      | .expression [.symbol "node", .symbol label, .expression [.symbol "cp", .grounded (.int point)]] =>
          if point < 0 then none else do
            if input[start]? != some point.toNat then none else do
              let (row, position) ← unique? (plan.lexical.productions.zipIdx.filter fun (row, _) =>
                row.resultSort == sort && row.label == label)
              pure (start + 1, .lexical position row.matcher start (start + 1))
      | _ =>
          let (label, children) ← node? packet
          let (row, position) ← unique? (plan.structural.zipIdx.filter fun (row, _) =>
            row.resultSort == sort && row.label == label)
          let (stop, body, remaining) ← proposeItemsFuel plan input fuel row.items start children
          if remaining.isEmpty then pure (stop, .structural position start stop body) else none
    termination_by fuel => (fuel, 0)

  def proposeItemsFuel (plan : CompiledParserPackPlan) (input : List Nat) (fuel : Nat) :
      List PackItem → Nat → List Packet → Option (Nat × ItemsCertificate × List Packet)
    | [], start, children => some (start, .nil start, children)
    | .terminal matcher :: items, start, children => do
        let middle := terminalStop start matcher
        let (stop, rest, remaining) ← proposeItemsFuel plan input fuel items middle children
        pure (stop, .terminal matcher start middle rest, remaining)
    | .nonterminal sort :: items, start, children => do
        let first :: others := children | none
        let (middle, head) ← proposeFuel plan input fuel sort start first
        let (stop, rest, remaining) ← proposeItemsFuel plan input fuel items middle others
        pure (stop, .nonterminal sort start middle head rest, remaining)
    termination_by items => (fuel, items.length + 1)
end

def propose? (plan : CompiledParserPackPlan) (input : List Nat) (sort : String) (packet : Packet) : Option Certificate := do
  let (stop, certificate) ← proposeFuel plan input (packetNodes packet + 1) sort 0 packet
  if stop == input.length then some certificate else none

def readPacket? (description : Description) (parser : Parser description) (shape : Shape description)
    (input : List Nat) (sort : String) (packet : Packet) :
    Option (Reading description parser shape input sort 0 input.length) := do
  let certificate ← propose? parser.plan input sort packet
  readCertificate? description parser shape input sort 0 input.length certificate

def core? (description : Description) (parser : Parser description) (shape : Shape description)
    (input : List Nat) (sort : String) (packet : Packet) : Option Mettapedia.OSLF.MeTTaIL.Syntax.Pattern :=
  (readPacket? description parser shape input sort packet).map (·.core)

theorem core?_source {description : Description} {parser : Parser description} {shape : Shape description}
    {input : List Nat} {sort : String} {packet : Packet} {pattern : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (accepted : core? description parser shape input sort packet = some pattern) :
    ∃ tree, Nonempty (LanguageDefScalarSyntax.DerivesAt SourceSyntaxExport.literalScalars? description.profile
      description.grammar input sort 0 input.length tree) ∧ lowerCST? description sort tree = some pattern := by
  cases read : readPacket? description parser shape input sort packet with
  | none => simp [core?, read] at accepted
  | some reading =>
    have same : reading.core = pattern := by simpa [core?, read] using accepted
    exact ⟨reading.tree, reading.source, same ▸ reading.construction⟩

theorem core?_prints {description : Description} {parser : Parser description} {shape : Shape description}
    {input : List Nat} {sort : String} {packet : Packet} {pattern : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (accepted : core? description parser shape input sort packet = some pattern) :
    printScalars? description sort pattern = some input := by
  cases read : readPacket? description parser shape input sort packet with
  | none => simp [core?, read] at accepted
  | some reading =>
    have same : reading.core = pattern := by simpa [core?, read] using accepted
    exact same ▸ reading.full_source

#print axioms core?_source
#print axioms core?_prints

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketCertificate
