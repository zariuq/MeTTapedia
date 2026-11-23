import Mettapedia.Languages.HOLLight.NumberedReplay
import Mettapedia.Languages.HOLLight.SourceProfile
import Lean.Data.Json
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight Lean
open DefinitionAdapters SignatureFormation ProofExecution ExportReplay

/-!
# Numbered source-record intake

This untrusted source adapter expands numbered type and term nodes into the
existing source syntax. Every proof and definition is checked by the registered
HOL receiver. A separately supplied source profile fixes the primitive basis
and permitted axioms; the proof document cannot extend that policy.

The partial functions decode finite input graphs and reject non-earlier syntax
edges. They add no theorem or checker authority. Successful runs qualify the
selected inputs and receiver artifact, with no implementation-refinement claim.
-/
set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.RecordedSourceImport

structure Input where
  types : Array Json
  terms : Array Json
  events : Array Json

structure Reading where
  input : Input
  types : Array (Option Ty)
  terms : Array (Option SourceTerm)
  registered : ExportReplay.State
  symbols : ExportCodec.Symbols
  sourceConclusions : Std.TreeMap Nat SourceTerm := {}
  axioms : List Sequent := []
  refusalChecks : Nat := 0

abbrev Read := StateT Reading (Except String)

def fail {A : Type} (message : String) : Read A := throw message

def jsonNat (value : Json) : Read Nat :=
  NumberedReplay.jsonNat value

def jsonText (value : Json) : Read String :=
  NumberedReplay.jsonText value

def jsonArray (value : Json) : Read (Array Json) :=
  NumberedReplay.jsonArray value

def field (value : Json) (key : String) : Read Json :=
  NumberedReplay.field value key

def arrayAt (values : Array Json) (index : Nat) : Read Json :=
  NumberedReplay.arrayAt values index

def option {A : Type} (value : Option A) (message : String) : Read A :=
  match value with
  | some value => pure value
  | none => fail message

def syntaxReader : NumberedReplay.Syntax Reading where
  types :=
    ⟨(·.input.types), Reading.types, fun state index entry =>
      { state with types := state.types.set! index (some entry) }⟩
  terms :=
    ⟨(·.input.terms), Reading.terms, fun state index entry =>
      { state with terms := state.terms.set! index (some entry) }⟩
  symbols := Reading.symbols
  checkRowArity := true

opaque sourceType (index : Nat) : Read Ty :=
  syntaxReader.readType index

opaque sourceTerm (index : Nat) : Read SourceTerm :=
  syntaxReader.readTerm index

def canonical (index : Nat) : Read CanonicalTerm := do
  option (← sourceTerm index).check s!"ill-typed term {index}"

def checked (index : Nat) : Read CheckedSourceTerm := do
  option (ExportReplay.checkedSource? (← sourceTerm index)) s!"ill-typed source {index}"

def finitePolicy (allowed : List Sequent) : AxiomPolicy := fun sequent => sequent ∈ allowed
instance (allowed : List Sequent) : DecidablePred (finitePolicy allowed) :=
  fun _ => inferInstanceAs (Decidable (_ ∈ allowed))

def termReader : NumberedReplay.TermReader Reading :=
  ⟨sourceType, sourceTerm, canonical, checked⟩

def registry : NumberedReplay.Registry Reading where
  registered := Reading.registered
  symbols := Reading.symbols
  withSymbols state symbols := { state with symbols }
  sourceConclusions := Reading.sourceConclusions
  policy state := finitePolicy state.axioms
  decidePolicy _ := inferInstance
  install before event after _ sources refusals :=
    { before with
      registered := after
      sourceConclusions := ExportCodec.addConclusions before.sourceConclusions event.sourceIds sources
      refusalChecks := before.refusalChecks + refusals }
  registered_install _ _ _ _ _ _ := rfl

def claim (value : Json) : Read (Nat × Sequent × SourceTerm) :=
  NumberedReplay.claim termReader value

def parent (source : Nat) : Read (Nat × Theorem) :=
  NumberedReplay.parent registry source

def receiveEvent (source : Json) : Read Unit :=
  NumberedReplay.receiveEvent termReader registry true .selectedProfile
    (NumberedReplay.finish termReader registry .selectedProfile) source

end Mettapedia.Languages.HOLLight.RecordedSourceImport
namespace Mettapedia.Languages.HOLLight.RecordedSourceImport
def loadSource (path profilePath : String) (limit : Option Nat := none) : IO Reading := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let types ← IO.ofExcept ((json.getObjVal? "types").bind Json.getArr?)
  let terms ← IO.ofExcept ((json.getObjVal? "terms").bind Json.getArr?)
  let allEvents ← IO.ofExcept ((json.getObjVal? "events").bind Json.getArr?)
  if let some requested := limit then
    unless requested ≤ allEvents.size do throw (IO.userError "source prefix exceeds the supplied history")
  let events := allEvents.extract 0 (limit.getD allEvents.size)
  let input : Input := ⟨types, terms, events⟩
  let profileJson ← IO.ofExcept (Json.parse (← IO.FS.readFile profilePath))
  let some profile := SourceProfile.load? SourceProfile.primitiveBasis profileJson |
    throw (IO.userError "selected source profile refused")
  let mut state : Reading := ⟨input, Array.replicate types.size none, Array.replicate terms.size none,
    profile.initial.received, profile.initial.symbols, {}, profile.commitments, 0⟩
  let mut processed := 0
  for event in events do
    let (_, after) ← IO.ofExcept ((receiveEvent event).run state)
    state := after
    processed := processed + 1
    if processed % 8192 == 0 then
      (← IO.getStderr).putStrLn s!"source events {processed}/{events.size}"
      (← IO.getStderr).flush
  (← IO.getStderr).putStrLn s!"received {events.size} events; {state.registered.registered.cache.size} theorems"
  return state
end Mettapedia.Languages.HOLLight.RecordedSourceImport
