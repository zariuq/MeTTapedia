import Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementEntry
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedImprovementRows
import Mettapedia.Tools.KernelReflexivity

/-!
# Source-certificate-generated improvement canaries

Scenarios instantiate the actual source grammar and selected-clause checker.
Every emitted positive packet has a completed source-call theorem, including
the enclosing captured-variable bindings. Expected output observes collapsed
answers and the ordered natural-row projection. It is not a native whole-heap
or lifetime certificate. Rendering checks execute the existing text reader
separately from the kernel-checked source-carrier certificates; no text-parser
adequacy theorem is claimed here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedSourceQualification

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval SpaceSemantics NamedSpaces KeyedImprovementSource

structure Scenario where
  tag : String
  names : Names
  function : String
  head : String
  rows : List (Nat × Nat)
  key : Nat
  candidate : Nat

def Scenario.equation (scenario : Scenario) : Equation :=
  ⟨scenario.function, [.var scenario.names.space, .var scenario.names.vertex, .var scenario.names.candidate],
    source scenario.names scenario.head⟩

def Scenario.program (scenario : Scenario) : Program :=
  {equations := [scenario.equation], declarations := [], facts := KeyedImprovementRows.encodeRows scenario.head scenario.rows,
    layout := List.replicate scenario.rows.length .fact ++ [.equation]}

def Scenario.before (scenario : Scenario) : Effects.State := Effects.loaded scenario.program
def Scenario.caller (scenario : Scenario) : Subst := bindings scenario.names .self scenario.key scenario.candidate

def Scenario.closedCall (scenario : Scenario) : Atom :=
  .expression [.symbol "let", .var scenario.names.space, Effects.handleValue .self,
    .expression [.symbol "let", .var scenario.names.vertex, number scenario.key,
      .expression [.symbol "let", .var scenario.names.candidate, number scenario.candidate,
        KeyedImprovementEntry.call scenario.function scenario.names]]]

structure Qualified (scenario : Scenario) where
  certificate : KeyedImprovementEntry.Certificate scenario.program scenario.function scenario.names scenario.head .self scenario.key scenario.candidate
  after : Effects.State
  answers : List Atom
  executed : KeyedImprovementSource.run scenario.names scenario.head .self scenario.key scenario.candidate scenario.before = some (after, answers)

def qualify (scenario : Scenario) : Option (Qualified scenario) := do
  let certificate ← KeyedImprovementEntry.prepare scenario.program scenario.function scenario.names scenario.head .self scenario.key scenario.candidate
  match completed : KeyedImprovementSource.run scenario.names scenario.head .self scenario.key scenario.candidate scenario.before with
  | none => none
  | some result => some ⟨certificate, result.1, result.2, completed⟩

theorem Qualified.closed_returns {scenario : Scenario} (qualified : Qualified scenario) :
    Returns scenario.program [] scenario.before scenario.closedCall qualified.after qualified.answers := by
  have apart := scenario.names.distinct
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true] at apart
  have captured : [scenario.names.space, scenario.names.vertex, scenario.names.candidate].map
      (fun name => applySubst scenario.caller (.var name)) =
      [Effects.handleValue .self, number scenario.key, number scenario.candidate] := by
    simp [Scenario.caller, bindings, applySubst, Subst.lookup, Ne.symm apart.1.1,
      Ne.symm apart.1.2.1, Ne.symm apart.2.1.1]
  have called := qualified.certificate.call_returns scenario.caller captured scenario.before qualified.after qualified.answers qualified.executed
  apply let_answers scenario.program [] [(scenario.names.space, Effects.handleValue .self)]
    scenario.before scenario.before qualified.after (.var scenario.names.space) _ _ _ qualified.answers
    (symbol_returns scenario.program [] scenario.before "&self")
    (by simp [matchBinding, matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, Subst.lookup, Effects.handleValue])
  apply let_answers scenario.program _ [(scenario.names.vertex, number scenario.key), (scenario.names.space, Effects.handleValue .self)]
    scenario.before scenario.before qualified.after (.var scenario.names.vertex) _ _ _ qualified.answers
    (grounded_returns scenario.program _ scenario.before (.int scenario.key))
    (by simp [matchBinding, matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, Subst.lookup, apart.1.1, number])
  apply let_answers scenario.program _ scenario.caller scenario.before scenario.before qualified.after
    (.var scenario.names.candidate) _ _ _ qualified.answers
    (grounded_returns scenario.program _ scenario.before (.int scenario.candidate)) _ called
  simp [Scenario.caller, bindings, matchBinding, matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
    Subst.lookup, apart.1.2.1, apart.2.1.1, number]

def Scenario.programText (scenario : Scenario) : String :=
  "\n".intercalate ((loadedAtoms scenario.program).map Atom.toString) ++ "\n"

def projectionPattern (scenario : Scenario) : Atom := row scenario.head (.var "output-key") (.var "output-value")
def projectionTemplate : Atom := .expression [.var "output-key", .var "output-value"]
def projectionSource (scenario : Scenario) : Atom :=
  .expression [.symbol "match", .expression [.symbol "quote", Effects.handleValue .self],
    projectionPattern scenario, .expression [.symbol "quote", projectionTemplate]]

def Scenario.text (scenario : Scenario) : String :=
  scenario.programText ++ "!" ++ (Atom.expression [.symbol "collapse", scenario.closedCall]).toString ++ "\n" ++
    "!" ++ (Atom.expression [.symbol "collapse", projectionSource scenario]).toString ++ "\n"

def Qualified.expected {scenario : Scenario} (qualified : Qualified scenario) : String :=
  (Atom.expression qualified.answers).toString ++ "\n" ++
    (Atom.expression (SpaceSemantics.query qualified.after.core (projectionPattern scenario) projectionTemplate)).toString ++ "\n"

theorem Qualified.collapsed_returns {scenario : Scenario} (qualified : Qualified scenario) :
    PureReturns scenario.program [] scenario.before (.expression [.symbol "collapse", scenario.closedCall]) qualified.after
      (.expression qualified.answers) :=
  collapse_returns scenario.program [] scenario.before qualified.after scenario.closedCall qualified.answers qualified.closed_returns

theorem Qualified.projection_returns {scenario : Scenario} (qualified : Qualified scenario) :
    PureReturns scenario.program [] qualified.after (.expression [.symbol "collapse", projectionSource scenario]) qualified.after
      (.expression (SpaceSemantics.query qualified.after.core (projectionPattern scenario) projectionTemplate)) := by
  apply collapse_returns
  have result := CapturedQuerySource.match_returns scenario.program qualified.after []
    (.expression [.symbol "quote", Effects.handleValue .self]) (Effects.handleValue .self) qualified.after.core
    (by simpa [applySubst, Effects.handleValue] using quote_returns scenario.program [] qualified.after (Effects.handleValue .self))
    (by simp [Store.read]) (projectionPattern scenario) (.expression [.symbol "quote", projectionTemplate])
    (fun bound => [applySubst bound projectionTemplate])
    (fun _ _ bound _ => quote_returns scenario.program bound qualified.after projectionTemplate)
  have scan : (FlatQueryRelationCompilation.sourceScan [] (projectionPattern scenario) 0 qualified.after.core).map
      (fun result => applySubst result.2 projectionTemplate) =
        SpaceSemantics.query qualified.after.core (projectionPattern scenario) projectionTemplate := by
    rw [show (fun result : Nat × Subst => applySubst result.2 projectionTemplate) =
      (fun bound => applySubst bound projectionTemplate) ∘ Prod.snd from rfl,
      ← List.map_map, EffectfulQuerySource.scan_bindings]
    simp only [SpaceSemantics.query, List.map_filterMap]
  simpa only [projectionSource, ← List.map_eq_flatMap, scan] using result

def Qualified.packet {scenario : Scenario} (qualified : Qualified scenario) : Lean.Json :=
  Lean.Json.mkObj [("name", Lean.toJson scenario.tag), ("source", Lean.toJson scenario.text),
    ("expected", Lean.toJson qualified.expected),
    ("observation", Lean.toJson "collapsed answers and ordered natural rows"),
    ("source_theorems", Lean.toJson ["KeyedSourceQualification.Qualified.collapsed_returns",
      "KeyedSourceQualification.Qualified.projection_returns"])]

def schemes : List (String × Names × String × String) := [
  ("short", ⟨"s", "v", "c", "seen", "old", "written", by decide⟩, "improve", "sd"),
  ("renamed", ⟨"destination", "node", "proposal", "current", "previous", "discard", by decide⟩, "lower-distance", "distance"),
  ("alternate", ⟨"store", "vertex", "candidate", "found", "prior", "ack", by decide⟩, "update-bound", "best")]

def scenarios : List Scenario := schemes.flatMap fun (tag, names, function, head) => [
  ⟨tag ++ "-absent", names, function, head, [], 0, 7⟩,
  ⟨tag ++ "-better", names, function, head, [(0, 10), (1, 5)], 0, 7⟩,
  ⟨tag ++ "-unchanged", names, function, head, [(0, 10), (1, 5)], 0, 12⟩,
  ⟨tag ++ "-equal", names, function, head, [(0, 10), (1, 5)], 0, 10⟩,
  ⟨tag ++ "-large", names, function, head, [(0, 2^64 + 2)], 0, 2^64 + 1⟩]

theorem every_scenario_has_a_source_certificate : scenarios.all (fun scenario => (qualify scenario).isSome) = true := by
  decide +kernel

def renderingChecks : List Bool := scenarios.map (fun scenario =>
  (readProgram scenario.programText).map loadedAtoms == .ok (loadedAtoms scenario.program))

def packets : List Lean.Json := scenarios.filterMap (fun scenario => (qualify scenario).map Qualified.packet)

theorem no_scenario_is_silently_dropped : packets.length = scenarios.length := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.KeyedSourceQualification
