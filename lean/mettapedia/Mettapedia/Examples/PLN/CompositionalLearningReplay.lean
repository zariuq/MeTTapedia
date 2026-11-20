import Mettapedia.PLN.WorldModel.CompositionalBootstrap
import Lean.Data.Json.FromToJson

/-!
# Compositional learning replay

Each packet describes a Boolean feature vocabulary, independent training
tasks for the controller, and identified observations for one new task.
Each query is evaluated under the same model prior with a fixed frontier
priority and a learned frontier priority, under the supplied budgets.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.PLN.CompositionalLearningReplay

open Lean
open Mettapedia.PLN.WorldModel.PredictiveBootstrap (Candidate)
open Mettapedia.PLN.WorldModel.CompositionalBootstrap
open Mettapedia.ProbabilityTheory.StochasticInference
open AnytimeMixtures

structure Sample where
  id : Nat
  input : Array Bool
  outcome : Bool
  deriving FromJson

inductive Edit where
  | record (sample : Sample)
  | withdraw (id : Nat)
  | restore (id : Nat)
  deriving FromJson

structure Packet where
  features : Nat
  training : List (List Sample)
  edits : List Edit
  queries : List (Array Bool)
  budgets : List Nat
  checkFull : Bool
  reusePrefix : Bool
  deriving FromJson

private def inputAt (n : Nat) (raw : Array Bool) : Except String (Vector Bool n) :=
  if h : raw.size = n then .ok ⟨raw, h⟩ else .error s!"Expected {n} Boolean features"

private def update {n : Nat} (ledger : EvidenceLedger Nat (Vector Bool n × Bool))
    (edit : Edit) : Except String (EvidenceLedger Nat (Vector Bool n × Bool)) := do
  match edit with
  | .record sample =>
    let input ← inputAt n sample.input
    let (_, next) ← (ledger.observe sample.id (input, sample.outcome)).mapError
      (fun id => s!"Conflicting payload for observation {id}")
    pure next
  | .withdraw id =>
    let some _ := ledger.lookup id | throw s!"Unknown observation {id}"
    pure (ledger.retract id)
  | .restore id =>
    let some _ := ledger.lookup id | throw s!"Unknown observation {id}"
    pure (ledger.restore id)

private def includePrior : UnitProbability := ⟨1 / 4, by decide +kernel, by decide +kernel⟩

private def asPair (q : ℚ) : Json := toJson (q.num, q.den)

private def jsonInterval : Option (ℚ × ℚ) → Json
  | none => Json.null
  | some (low, high) => Json.arr #[asPair low, asPair high]

def evaluate (packet : Packet) : Except String Json := do
  let tests := (List.finRange packet.features).map (fun i (x : Vector Bool packet.features) => x[i.val])
  let dataset ← packet.edits.foldlM update EvidenceLedger.empty
  let training ← packet.training.mapM fun examples => do
    let observations ← (examples.map Edit.record).foldlM update EvidenceLedger.empty
    pure (Candidate.samples (Id := Nat) (Input := Vector Bool packet.features) observations)
  let queries ← packet.queries.mapM (inputAt packet.features)
  let samples := Candidate.samples (Id := Nat) (Input := Vector Bool packet.features) dataset
  let learned := learnPriority includePrior tests training
  let indexed := List.replicate tests.length includePrior.val
  let cap := if packet.reusePrefix then
    match samples with
    | [] => none
    | _ :: older => some (mixtureEvidence includePrior tests older)
    else none
  let evaluateBudget := fun (priority : List ℚ) (budget : Nat) =>
    let trace := run priority budget (.pending : Trace tests.length)
    let visited := Trace.visitedPaths trace
    let fitted := visited.map fun path =>
      let state := fit (model tests path) samples
      (path, state.evidence, fun input => state.query input true)
    let best := fitted.foldl (fun best (path, evidence, _) =>
      let score := pathMass indexed path * evidence
      if best.2 < score then (some path, score) else best)
      ((none : Option (List Bool)), (-1 : ℚ))
    let answer := fun input =>
      let summary := trace.summarize includePrior
        (fun path =>
          match fitted.find? (fun entry => entry.1 == path) with
          | some (_, _, query) => query input
          | none => (fit (model tests path) samples).query input true)
      let capped := cap.elim summary summary.capEvidence
      jsonInterval capped.interval?
    let prediction := fun input => best.1.map
      (fun path => (model tests path).prediction samples input true)
    Json.mkObj [("budget", toJson budget), ("visited", toJson visited.length),
      ("best", toJson best.1), ("intervals", toJson (queries.map answer)),
      ("bestPredictions", toJson (queries.map fun input => (prediction input).map asPair))]
  let full := if packet.checkFull then some (queries.map fun input =>
    (fullMass includePrior (fun path => (fit (model tests path) samples).query input true)
      tests.length).masses.posterior?.map asPair) else none
  pure (Json.mkObj [("indexed", toJson (packet.budgets.map (evaluateBudget indexed))),
    ("learned", toJson (packet.budgets.map (evaluateBudget learned))),
    ("priority", toJson (learned.map asPair)), ("full", toJson full)])

end Mettapedia.Examples.PLN.CompositionalLearningReplay

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let answer := do
      let json ← Lean.Json.parse line
      let packet ← Lean.fromJson? json
      Mettapedia.Examples.PLN.CompositionalLearningReplay.evaluate packet
    let response := match answer with
      | .ok value => value
      | .error message => Lean.Json.mkObj [("error", Lean.toJson message)]
    output.putStrLn response.compress
    output.flush
