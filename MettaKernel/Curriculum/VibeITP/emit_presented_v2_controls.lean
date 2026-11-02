import Mettapedia.GSLT.LanguageDef.FirstOrderCertificateData

/-! Shared calibration-article emission. The generated theorem checks the
supplied article against the independently authored crossing statement. -/

open Lean (Json)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.FirstOrderCertificateData

private structure Build where
  patterns : Std.HashMap (String × List Nat) Nat := {}
  articles : Std.HashMap (String × List Nat × List Nat) Nat := {}
  lines : Array String := #[]

private abbrev Emit := StateT Build (Except String)

private def names (stem : String) (identifiers : List Nat) : String :=
  String.intercalate ", " (identifiers.map (fun identifier => stem ++ toString identifier))

private partial def emitPattern : Pattern → Emit Nat
  | .apply head arguments => do
      let children ← arguments.mapM emitPattern
      let key := (head, children)
      let state ← get
      if let some identifier := state.patterns[key]? then return identifier
      let identifier := state.patterns.size
      let declaration := s!"private def p{identifier} : Pattern := .apply {reprStr head} [{names "p" children}]"
      set { state with patterns := state.patterns.insert key identifier, lines := state.lines.push declaration }
      return identifier
  | _ => throw "a concrete article argument must be a ground application"

private partial def emitArticle : RawProof → Emit Nat
  | .node application children => do
      let children ← children.mapM emitArticle
      let arguments ← application.arguments.mapM emitPattern
      let key := (application.ruleId.value, arguments, children)
      let state ← get
      if let some identifier := state.articles[key]? then return identifier
      let identifier := state.articles.size
      let declaration := s!"private def a{identifier} : RawProof := .node ⟨⟨{reprStr application.ruleId.value}⟩, [{names "p" arguments}]⟩ [{names "a" children}]"
      set { state with articles := state.articles.insert key identifier, lines := state.lines.push declaration }
      return identifier

private def header : String := "import Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentationControls\n\n" ++
  "-- Generated calibration data; the kernel checks the supplied article below.\n" ++
  "set_option maxRecDepth 200000\nset_option maxHeartbeats 10000000\n" ++
  "namespace Mettapedia.Languages.VibeITP.Presentation.SimultaneousArticleControl\n" ++
  "open Mettapedia.OSLF.MeTTaIL.Syntax\nopen Mettapedia.GSLT.LanguageDef.InferenceChecker\n" ++
  "open SimultaneousPresentation\n\n"

private def checks : String := "
theorem crossing_checked :
    checkRaw (validatedV2 Controls.theory Controls.allocated)
      (jThm (encTerm Controls.theory.sig Controls.crossing)) crossingArticle = true := by decide +kernel

theorem crossing_derived : Spec.DerivesV2 Controls.theory Controls.crossing :=
  checkRaw_soundV2 Controls.hosted crossing_checked

theorem sequential_goal_refused :
    checkRaw (validatedV2 Controls.theory Controls.allocated)
      (jThm (encTerm Controls.theory.sig Controls.sequential)) crossingArticle = false := by decide +kernel

#print axioms crossing_checked
#print axioms crossing_derived
#print axioms sequential_goal_refused
"

private def actualChecks : String := "
theorem actual_byte_theory_checks_same_article :
    checkRaw
      (validatedV2 Native.ProtocolV2LogicalControls.finalState.theory
        Native.ProtocolV2LogicalControls.finalState.nextFresh)
      (jThm (encTerm Native.ProtocolV2LogicalControls.finalState.theory.sig
        Spec.ProtocolV2.Controls.crossingResult)) crossingArticle = true :=
  Native.ProtocolV2PresentedReadback.supplied_article_transports crossingArticle crossing_checked

#print axioms actual_byte_theory_checks_same_article
"

private def run (input output : System.FilePath) (actual : Bool) : IO UInt32 := do
  let json ← unwrap (Json.parse (← IO.FS.readFile input))
  let rows ← unwrap (arrayField json "results")
  let selected := rows.filter fun row =>
    (stringField row "name").toOption == some "crossing" &&
      (stringField row "status").toOption == some "candidate"
  unless selected.size = 1 do throw (IO.userError "expected exactly one crossing candidate")
  let proof ← unwrap do article (← field selected[0]! "article")
  let (root, state) ← unwrap ((emitArticle proof).run {})
  let header := if actual then header.replace
    "import Mettapedia.Languages.VibeITP.Presentation.SimultaneousPresentationControls"
    "import Mettapedia.Languages.VibeITP.Native.ProtocolV2PresentedReadback" else header
  let text := header ++ String.intercalate "\n" state.lines.toList ++
    s!"\n\ndef crossingArticle : RawProof := a{root}\n" ++ checks ++
    (if actual then actualChecks else "") ++
    "end Mettapedia.Languages.VibeITP.Presentation.SimultaneousArticleControl\n"
  IO.FS.writeFile output text
  IO.println s!"{state.patterns.size} distinct patterns, {state.articles.size} distinct proof nodes"
  return 0

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [input, output] => run input output false
  | [input, output, "--actual-theory"] => run input output true
  | _ => throw (IO.userError "expected CANDIDATES OUTPUT [--actual-theory]")
