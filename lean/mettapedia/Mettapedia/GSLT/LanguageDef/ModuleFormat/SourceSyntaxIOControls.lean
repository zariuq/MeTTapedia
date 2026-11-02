import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxIO

/-! Shared admission, ambiguity and source-readback controls over an
independently declared grammar. No language-specific frontend is involved. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxIO.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open ScalarSyntaxCore

def first : GrammarRule := {label := "First",category := "Term",params := [],syntaxPattern := [.terminal "x"]}
def second : GrammarRule := {first with label := "Second"}
def pair : GrammarRule := {
  label := "Pair"
  category := "Term"
  params := [.simple "left" (.base "Term"),.simple "right" (.base "Term")]
  syntaxPattern := [.terminal "(",.nonTerminal "left",.terminal ",",.nonTerminal "right",.terminal ")"] }
def grammar : LanguageDef := {name := "SourceIO",types := ["Term"],terms := [first,second,pair],equations := [],rewrites := []}
def spec : Portable.SyntaxDescription := ⟨grammar,{name := "SourceIO",startSort := "Term",classes := [],states := []}⟩
def packet (label : String) : SourcePacket.Packet :=
  .expression [.symbol "node",.symbol label,.symbol "nil"]

theorem admitted : checkShape (description spec) = true := by decide +kernel

theorem duplicate_constructor_refused :
    checkShape (description {spec with grammar := {grammar with terms := [first,first]}}) = false := by
  decide +kernel

theorem swapped_parameters_refused :
    checkShape (description {spec with grammar := {grammar with terms :=
      [{pair with params := pair.params.reverse}]}}) = false := by decide +kernel

#guard (read? spec "x" (packet "First")).isSome
#guard (read? spec "x" (packet "Second")).isSome
#guard read? spec "x" (packet "First") != read? spec "x" (packet "Second")
#guard read? spec "y" (packet "First") == none
#guard read? spec "x" (packet "Missing") == none

theorem one_core_cannot_print_two_sources (left right : String) (one two : SourcePacket.Packet)
    (core : Pattern) (a : read? spec left one = some core) (b : read? spec right two = some core) :
    left = right :=
  Option.some.inj ((read_print spec left one core a).symm.trans (read_print spec right two core b))

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxIO.Controls
