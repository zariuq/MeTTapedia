import Mettapedia.GSLT.Parsing.ParserProfileSemantics

/-!
# Canonical parser-profile wire

Language-specific parser profiles use this single serialization before the
generic ParserPack compiler consumes them.  The renderer contains no language
dispatch and emits every lexical class and state in source order.
-/

namespace Mettapedia.GSLT.Parsing.ParserProfileWire

open Mettapedia.GSLT.Parsing.ParserProfileSemantics

private def quote (text : String) : String :=
  "\"" ++ (text.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

private def renderList (entries : List String) : String :=
  entries.foldr (fun entry rest => s!"(LCons {entry} {rest})") "LNil"

private def renderCodepoints (codepoints : List Nat) : String :=
  renderList (codepoints.map toString)

private def renderClass (declaration : LexicalClassDecl) : String :=
  match declaration.kind with
  | .points codepoints =>
      s!"(LexicalClassPoints {quote declaration.name} {renderCodepoints codepoints})"
  | .except excluded =>
      s!"(LexicalClassExcept {quote declaration.name} {renderCodepoints excluded})"

private def renderState (state : LexicalStateDecl) : String :=
  s!"(LexicalState {quote state.resultSort} {quote state.className} " ++
    s!"{quote state.ruleLabel})"

/-- Canonical source-order wire rendering of a parser-profile layer. -/
def render (profile : ParserProfileLayer) : String :=
  "(GSLTParserProfileLayerV1\n" ++
    s!"  {quote profile.name}\n" ++
    s!"  {quote profile.startSort}\n" ++
    s!"  {renderList (profile.classes.map renderClass)}\n" ++
    s!"  {renderList (profile.states.map renderState)})\n"

theorem render_nonempty (profile : ParserProfileLayer) :
    render profile ≠ "" := by
  simp [render]

#print axioms render_nonempty

end Mettapedia.GSLT.Parsing.ParserProfileWire
