import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketCertificate
import Mettapedia.GSLT.Parsing.GrammarArgumentLayoutLaws

/-! Two genuine source productions print the same text while retaining
different constructor identities. Replay refuses missing rows, wrong spans
and wrong input. Invalid Unicode words do not become lexical leaves. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing ParserProfileSemantics GrammarArgumentLayout
open ClassAwareParserPackCertificate
open ScalarSyntaxCore SourcePacketCertificate

private def firstRow : GrammarRule := {label := "first", category := "Start", params := [], syntaxPattern := [.terminal "a"]}
private def secondRow : GrammarRule := {label := "second", category := "Start", params := [], syntaxPattern := [.terminal "a"]}

private def ambiguous : Description := {
  grammar := {name := "AmbiguityControl", types := ["Start"], terms := [firstRow, secondRow], equations := [], rewrites := []}
  profile := {name := "AmbiguityProfile", startSort := "Start", classes := [], states := []}
  leafPrefix := "control-scalar:" }

private theorem shape : Shape ambiguous := by
  have ordered : ∀ row ∈ ambiguous.grammar.terms, parameters? row row.syntaxPattern = some row.params := by decide +kernel
  refine ⟨ordered, fun row member => not_bare_of_parameters row (ordered row member), ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide +kernel

private def parser : Parser ambiguous := (compileParser? ambiguous).get (by decide +kernel)
private def packet (label : String) : SourcePacket.Packet := .expression [.symbol "node", .symbol label, .symbol "nil"]
private def core (label : String) := core? ambiguous parser shape [97] "Start" (packet label)

#guard core "first" == some (.apply "first" [])
#guard core "second" == some (.apply "second" [])
#guard core "first" != core "second"
#guard (core "first").bind (printText? ambiguous "Start") == some "a"
#guard (core "second").bind (printText? ambiguous "Start") == some "a"
#guard (core "missing").isNone
#guard (core? ambiguous parser shape [98] "Start" (packet "first")).isNone

private def certificate : Certificate := .structural 0 0 1 (.terminal (.char 97) 0 1 (.nil 1))
#guard readPrintScalars? ambiguous parser shape [97] "Start" certificate == some [97]
#guard (readCertificate? ambiguous parser shape [97] "Start" 0 1
  (.structural 2 0 1 (.terminal (.char 97) 0 1 (.nil 1)))).isNone
#guard (readCertificate? ambiguous parser shape [97] "Start" 0 1
  (.structural 0 0 1 (.terminal (.char 97) 0 0 (.nil 1)))).isNone

private def firstSource : LanguageDefScalarSyntax.DerivesAt SourceSyntaxExport.literalScalars? ambiguous.profile
    ambiguous.grammar [97] "Start" 0 1 (.node "first" 0 1 []) :=
  .structural ⟨0, by decide⟩ (.terminal rfl (.cons rfl (.nil 1)) .nil)

private def secondSource : LanguageDefScalarSyntax.DerivesAt SourceSyntaxExport.literalScalars? ambiguous.profile
    ambiguous.grammar [97] "Start" 0 1 (.node "second" 0 1 []) :=
  .structural ⟨1, by decide⟩ (.terminal rfl (.cons rfl (.nil 1)) .nil)

theorem alternatives_retained :
    ∃ (first second : Certificate) (left right : Reading ambiguous parser shape [97] "Start" 0 1),
      readCertificate? ambiguous parser shape [97] "Start" 0 1 first = some left ∧
      readCertificate? ambiguous parser shape [97] "Start" 0 1 second = some right ∧
      left.core ≠ right.core ∧ printScalars? ambiguous "Start" left.core = some [97] ∧
      printScalars? ambiguous "Start" right.core = some [97] := by
  obtain ⟨first, left, firstRead, _, firstCore⟩ := source_has_reading parser shape firstSource
  obtain ⟨second, right, secondRead, _, secondCore⟩ := source_has_reading parser shape secondSource
  refine ⟨first, second, left, right, firstRead, secondRead, ?_, left.full_source, right.full_source⟩
  rw [firstCore, secondCore]
  decide +kernel

#print axioms alternatives_retained

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxControls
