import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourcePrinter
import Mettapedia.Languages.Datalog.ProgramStaticControls

/-! Canonical source text, independent-IR readback of constructed syntax and
separating diagnostics. Native packed-parser round trips are a separate gate. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter.Controls

open Mettapedia.Languages.Datalog

def basic : Program := ⟨[
  .declaration ⟨["N"],[⟨"x",.number⟩]⟩,
  .fact ⟨["N"],[.number (-1)]⟩,
  .fact ⟨["N"],[.number (-1)]⟩,
  .output ["N"]]⟩

def literalContents : Program := ⟨[
  .declaration ⟨["Text"],[⟨"value",.symbol⟩]⟩,
  .fact ⟨["Text"],[.symbol "quote\" slash\\ newline\n λ😀"]⟩,
  .output ["Text"]]⟩

def signedBounds : Program := ⟨[
  .declaration ⟨["N"],[⟨"x",.number⟩]⟩,
  .fact ⟨["N"],[.number (-(2^63))]⟩,
  .fact ⟨["N"],[.number (2^63-1)]⟩,
  .fact ⟨["N"],[.number 0]⟩,.output ["N"]]⟩

def anonymousComparisons : Program := ⟨[
  .declaration ⟨["N"],[⟨"x",.number⟩]⟩,.declaration ⟨["P"],[⟨"x",.number⟩]⟩,
  .fact ⟨["N"],[.number 0]⟩,.fact ⟨["N"],[.number 1]⟩,
  .rule ⟨⟨["P"],[.var "X"]⟩,[.atom ⟨["N"],[.var "X"]⟩,
    .atom ⟨["N"],[.anonymous]⟩,.comparison ⟨.greaterEqual,.var "X",.literal (.number 0)⟩]⟩,
  .output ["P"]]⟩

def treeRoundTrip (program : Program) : Bool :=
  match programTree? program with
  | .error _ => false
  | .ok tree =>
      ((ProgramProjection.Reference.projectProgram? tree).bind Frontend.normalize? |>.bind IRCodec.program?) == some program

def rejects (program : Program) : Bool := match print? program with | .error _ => true | .ok _ => false

#guard print? basic == .ok ".decl N(x: number)\nN(-1).\nN(-1).\n.output N\n"
#guard treeRoundTrip basic
#guard treeRoundTrip literalContents
#guard treeRoundTrip signedBounds
#guard treeRoundTrip anonymousComparisons
#guard treeRoundTrip Mettapedia.Languages.Datalog.ProgramStatic.Controls.cyclicGraph
#guard treeRoundTrip Mettapedia.Languages.Datalog.ProgramStatic.Controls.pointsTo
#guard rejects ⟨[.declaration ⟨["not a name"],[]⟩]⟩
#guard rejects ⟨[.declaration ⟨["Namespace","Relation"],[]⟩]⟩
#guard rejects ⟨[.rule ⟨⟨["N"],[.literal (.number 0)]⟩,[]⟩]⟩
#guard rejects ⟨[.fact ⟨["N"],[.number (2^63)]⟩]⟩
#guard rejects ⟨[.fact ⟨["N"],[.floating 0]⟩]⟩
#guard rejects ⟨[.rule ⟨⟨["N"],[.var "_"]⟩,[.atom ⟨["N"],[.var "_"]⟩]⟩]⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter.Controls
