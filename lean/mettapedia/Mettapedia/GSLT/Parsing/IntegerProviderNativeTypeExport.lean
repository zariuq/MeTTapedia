import Mettapedia.GSLT.Parsing.IntegerProviderNativeTypeCodec

/-!
# Executable native export from ordered authored source files

This reader uses the existing PeTTa source reader and structured source decoder. It
infers the selected binary completion types from source occurrences and emits
ordinary structured MeTTa. Rendering is checked by parsing the emitted text
back to the exact wire before it can be returned. This runtime check is not a
universal byte-parser or renderer theorem.
-/

namespace Mettapedia.GSLT.Parsing.IntegerProviderNativeTypeExport

open Algorithms.MeTTa.Simple.Parser (SExpr)
open IntegerProviderNativeTypeCodec

mutual

def renderSExpr : SExpr → String
  | .atom token => token
  | .list elements => "(" ++ renderElements elements ++ ")"
termination_by expression => sizeOf expression

def renderElements : List SExpr → String
  | [] => ""
  | [element] => renderSExpr element
  | element :: next :: rest => renderSExpr element ++ " " ++ renderElements (next :: rest)
termination_by elements => sizeOf elements

end

/-- Source token spellings are already retained by the existing reader. No
new token quoting convention is installed by this renderer. -/
def renderPacket (packet : Packet) : String :=
  "(integer-provider-native-types-v1\n  (source-composition\n" ++
    String.join (packet.sourceSyntax.map fun source => "    " ++ renderSExpr source ++ "\n") ++
    "  )\n  (types\n" ++
    String.join (packet.types.map fun info => "    " ++ renderSExpr (encodeInfo info) ++ "\n") ++
    "  ))\n"

def parseSource (text : String) : Except String SExpr :=
  (Algorithms.MeTTa.Simple.Parser.parseSExprWithDetailed MeTTailCore.MeTTaSyntax.petta text).mapError
    (fun error => error.render)

def checkedText (packet : Packet) : Except String String :=
  let rendered := renderPacket packet
  match parseSource rendered with
  | .error error => .error error
  | .ok parsed =>
      if parsed = encodePacket packet then .ok rendered
      else .error "rendered native-type packet changed structured MeTTa data"

theorem checkedText_sound {packet : Packet} {text : String}
    (checked : checkedText packet = .ok text) : parseSource text = .ok (encodePacket packet) := by
  cases parsed : parseSource (renderPacket packet) with
  | error error => simp [checkedText, parsed] at checked
  | ok wire =>
      by_cases same : wire = encodePacket packet
      · have textSame : renderPacket packet = text := by simpa [checkedText, parsed, same] using checked
        simpa [textSame, same] using parsed
      · simp [checkedText, parsed, same] at checked

def exportSources (rawSources : List SExpr) : Except String (Packet × String) := do
  let some packet := inferPacket? rawSources
    | throw "source composition does not decode as a valid structured GSLT composition"
  if !authenticate rawSources packet then
    throw "inferred packet failed source authentication"
  return (packet, ← checkedText packet)

theorem exportSources_of_inferred {rawSources : List SExpr} {packet : Packet} {text : String}
    (inferred : inferPacket? rawSources = some packet)
    (rendered : checkedText packet = .ok text) :
    exportSources rawSources = .ok (packet, text) := by
  have authentic : authenticate rawSources packet = true :=
    (authenticate_iff rawSources packet).mpr (inferred_packet_authentic inferred)
  simp [exportSources, inferred, authentic, rendered, bind, Except.bind, pure, Except.pure]

/-- A successful executable export is source-authentic and its text re-reads
to precisely the proved structured packet. The byte reader remains the same
explicit executable boundary used by `parseSource`. -/
theorem exportSources_sound {rawSources : List SExpr} {packet : Packet} {text : String}
    (exported : exportSources rawSources = .ok (packet, text)) :
    Authentic rawSources packet ∧ parseSource text = .ok (encodePacket packet) := by
  cases inferred : inferPacket? rawSources with
  | none => simp [exportSources, inferred] at exported
  | some actual =>
      have authentic := inferred_packet_authentic inferred
      have accepted : authenticate rawSources actual = true :=
        (authenticate_iff rawSources actual).mpr authentic
      cases rendered : checkedText actual with
      | error error =>
          simp [exportSources, inferred, accepted, rendered, bind, Except.bind] at exported
      | ok result =>
          have same : actual = packet ∧ result = text := by
            simpa [exportSources, inferred, accepted, rendered, bind, Except.bind,
              pure, Except.pure] using exported
          rcases same with ⟨rfl, rfl⟩
          exact ⟨authentic, checkedText_sound rendered⟩

def readSources (paths : List String) : IO (List SExpr) :=
  paths.mapM fun path => do
    let text ← IO.FS.readFile path
    match parseSource text with
    | .ok source => return source
    | .error error => throw (IO.userError s!"{path}: {error}")

/-- The command accepts the source composition in argument order. There is no
fixed provider-name registry or caller-supplied answer/type inventory. -/
def run (paths : List String) : IO UInt32 := do
  if paths.isEmpty then
    (← IO.getStderr).putStrLn "usage: integer-provider-native-type-export SOURCE.metta ..."
    return 2
  try
    let sources ← readSources paths
    match exportSources sources with
    | .error error =>
        (← IO.getStderr).putStrLn error
        return 1
    | .ok (_, text) =>
        (← IO.getStdout).putStr text
        return 0
  catch error =>
    (← IO.getStderr).putStrLn error.toString
    return 1

end Mettapedia.GSLT.Parsing.IntegerProviderNativeTypeExport
