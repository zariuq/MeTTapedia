import Mettapedia.ProbabilityTheory.StochasticInference.ProbLogic
import Lean.Data.Json.FromToJson

/-!
# Batch evaluator for grounded ProofWriter theories

One JSON object per line supplies a finite signed Horn program and normalized
product components. Signed literals have distinct atom indices. The compiler
is run once per theory, and each component reads the same query events.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.PLN.ProofWriterWorldModel

open Lean
open Mettapedia.Logic.BDDCore
open Mettapedia.ProbabilityTheory.StochasticInference (UnitProbability)
open Mettapedia.ProbabilityTheory.StochasticInference.ProbLogic (productMass coordinates eval_agree)
open HornClosure StatePredicates

structure Packet where
  atomCount : Nat
  sources : Array Nat
  clauses : Array (Nat × Array Nat)
  queries : Array (Nat × Nat)
  worlds : Array (Array Bool)
  productLaws : Array (Array (Nat × Nat))
  includeScopes : Option Bool := none
  deriving FromJson

def index (bound value : Nat) : Except String (Fin bound) :=
  if h : value < bound then .ok ⟨value, h⟩ else .error s!"Atom index {value} exceeds size {bound}"

def vector {α : Type} (width : Nat) (values : Array α) : Except String (Vector α width) :=
  if h : values.size = width then .ok ⟨values, h⟩
  else .error s!"Expected {width} source coordinates, got {values.size}"

def unitProbability (ratio : Nat × Nat) : Except String UnitProbability :=
  if 0 < ratio.2 then
    match UnitProbability.checked ((ratio.1 : ℚ) / ratio.2) with
    | some p => .ok p
    | none => .error s!"Invalid probability {ratio.1}/{ratio.2}"
  else .error s!"Invalid probability {ratio.1}/{ratio.2}"

def label (pos neg : Bool) : String :=
  match pos, neg with
  | true, true => "Both"
  | true, false => "True"
  | false, true => "False"
  | false, false => "Unknown"

def scope {n : Nat} (pos neg : Diagram n) : List (Fin n) :=
  (coordinates pos.val ++ coordinates neg.val).dedup

theorem label_agree {n : Nat} (pos neg : Diagram n) (x y : Fin n → Bool)
    (same : ∀ i ∈ scope pos neg, x i = y i) :
    label (pos.val.eval x) (neg.val.eval x) = label (pos.val.eval y) (neg.val.eval y) := by
  rw [eval_agree pos.val x y (fun i member => same i (by simp [scope, member])),
    eval_agree neg.val x y (fun i member => same i (by simp [scope, member]))]

private def scopeTable {n : Nat} (pos neg : Diagram n) : Json :=
  let localCoordinates := scope pos neg
  let labels := (List.range (2 ^ localCoordinates.length)).map fun world =>
    let assign (i : Fin n) := world.testBit (localCoordinates.idxOf i)
    label (pos.val.eval assign) (neg.val.eval assign)
  Json.mkObj [("coordinates", toJson (localCoordinates.map Fin.val)), ("labels", toJson labels)]

def evaluate (packet : Packet) : Except String Json := do
  let k := packet.atomCount
  let sources ← packet.sources.mapM (index k)
  let rules ← packet.clauses.toList.mapM fun (head, body) => do
    pure { head := ← index k head, body := ← body.toList.mapM (index k) : Clause k }
  let queries ← packet.queries.mapM fun (pos, neg) => do
    pure (← index k pos, ← index k neg)
  let n := sources.size
  let init := (List.finRange n).foldl (fun (table : Table n k) i =>
    let a := sources[i]
    table.set a.val (disj (table.get a) (bit i)) a.isLt)
    (Vector.replicate k (falsity n))
  let table := compile rules init
  let events := queries.map fun (pos, neg) => (table.get pos, table.get neg)
  let labels ← packet.worlds.mapM fun values => do
    let choice ← vector n values
    pure <| events.map fun (pos, neg) => label (pos.val.eval choice.get) (neg.val.eval choice.get)
  let masses ← packet.productLaws.mapM fun law => do
    let p ← vector n (← law.mapM unitProbability)
    pure <| events.map fun (pos, neg) =>
      #[pos, neg, conj pos neg].map fun (event : Diagram n) =>
        toString (productMass p.get event)
  let fields := [("labels", toJson labels), ("masses", toJson masses)]
  pure <| Json.mkObj (if packet.includeScopes.getD false then
    fields ++ [("scopes", toJson (events.map fun (pos, neg) => scopeTable pos neg))]
    else fields)

end Mettapedia.Examples.PLN.ProofWriterWorldModel

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let response := do
      let json ← Lean.Json.parse line
      let packet ← Lean.fromJson? json
      Mettapedia.Examples.PLN.ProofWriterWorldModel.evaluate packet
    match response with
    | .ok json => output.putStrLn json.compress
    | .error message => throw (IO.userError message)
    output.flush
