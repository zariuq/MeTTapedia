import Mettapedia.ProbabilityTheory.StochasticInference
import Lean.Data.Json.FromToJson

/-!
# JSON replay for a finite factor model

A packet gives positive domain sizes, base factors, and a sequence of edits
and queries. Factor scopes are ordered and the last coordinate varies
fastest. Every coefficient is an exact pair `[numerator, denominator]`.
Successful operations and validation errors return in order.

For a fair bit, a positive report of accuracy three quarters, and a query
for the bit, send this packet on one line.

```json
{"domains":[2],"base":[{"scope":[0],"rows":[[1,2],[1,2]]}],"operations":[{"observe":{"id":"a","likelihood":{"scope":[0],"rows":[[1,4],[3,4]]}}},{"probability":{"event":{"scope":[0],"rows":[[0,1],[1,1]]}}}]}
```

The probability response contains the query and evidence masses, with the
posterior in `value`. The value is null when the evidence mass is zero.
Use `{"retract":{"id":"a"}}` and `{"restore":{"id":"a"}}` to edit the ledger.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.StochasticInference.JsonReplay

open Lean
open Mettapedia.ProbabilityTheory.BayesianNetworks.ExecutableFactorTable (Table Config volume)
open Mettapedia.ProbabilityTheory.BayesianNetworks.ScopedFactorReadout (Masses)

structure Factor where
  scope : List Nat
  rows : Array (Int × Nat)
  deriving FromJson

inductive Operation where
  | observe (id : String) (likelihood : Factor)
  | retract (id : String)
  | restore (id : String)
  | probability (event : Factor)
  | expectation (payoff : Factor)
  | marginal (variableIndex : Nat)
  deriving FromJson

structure Packet where
  domains : Array Nat
  base : List Factor
  operations : Array Operation
  deriving FromJson

private def index (size value : Nat) : Except String (Fin size) :=
  if fit : value < size then .ok ⟨value, fit⟩ else .error s!"Variable index {value} out of range"

private def coefficient (ratio : Int × Nat) : Except String ℚ :=
  if ratio.2 = 0 then .error "A coefficient has a zero denominator"
  else .ok ((ratio.1 : ℚ) / (ratio.2 : ℚ))

private def Factor.table {n : Nat} (domains : Fin n → Nat) (input : Factor) :
    Except String (Table domains) := do
  let scope ← input.scope.mapM (index n)
  let rows ← input.rows.mapM coefficient
  if distinct : scope.Nodup then
    if size : rows.size = volume domains scope then
      pure ⟨scope, distinct, rows, size⟩
    else
      throw s!"Expected {volume domains scope} rows, got {rows.size}"
  else
    throw "A factor scope contains a repeated variable"

private def Factor.potential {n : Nat} (domains : Fin n → Nat) (input : Factor) :
    Except String (Potential domains) := do
  let table ← input.table domains
  let some potential := Potential.checked table | throw "A potential has a negative coefficient"
  pure potential

private def jsonRational (x : ℚ) : Json :=
  toJson (x.num, x.den)

private def jsonMasses (result : Masses) : Json :=
  Json.mkObj [("joint", jsonRational result.joint), ("evidence", jsonRational result.evidence),
    ("value", (result.posterior?).elim Json.null jsonRational)]

private def response (status : String) : Json := Json.mkObj [("status", toJson status)]

private structure Session {n : Nat} (domains : Fin n → Nat) where
  state : State String domains
  shared : Thunk (Schedule n × ℚ)

private def Session.start {n : Nat} {domains : Fin n → Nat} (positive : ∀ v, 0 < domains v)
    (state : State String domains) : Session domains :=
  ⟨state, Thunk.mk fun _ =>
    let schedule := Schedule.greedy domains (state.tables.map (·.scope))
    (schedule, mass positive schedule state.tables)⟩

/-- A complete order gives the same evidence mass for every query.
A joint payoff may still benefit from planning with its own scope. -/
private def Session.masses {n : Nat} {domains : Fin n → Nat} (session : Session domains)
    (positive : ∀ v, 0 < domains v) (payoff : Table domains) : Masses :=
  let (schedule, support) := session.shared.get
  let order := if 1 < payoff.scope.length then
    Schedule.greedy domains ((session.state.tables ++ [payoff]).map (·.scope))
    else schedule
  ⟨mass positive order (session.state.tables ++ [payoff]), support⟩

private def applyOperation {n : Nat} {domains : Fin n → Nat} (positive : ∀ v, 0 < domains v)
    (session : Session domains) (op : Operation) : Except String (Session domains × Json) := do
  let state := session.state
  match op with
  | .observe id likelihood =>
    let potential ← likelihood.potential domains
    let (arrival, next) ← (state.observe id potential).mapError (fun id => s!"Conflicting observation {id}")
    match arrival with
    | .recorded => pure (Session.start positive next, response "recorded")
    | .replay => pure (session, response "replay")
  | .retract id =>
    let some _ := state.ledger.lookup id | throw s!"Unknown observation {id}"
    pure (Session.start positive (state.retract id), response "retracted")
  | .restore id =>
    let some _ := state.ledger.lookup id | throw s!"Unknown observation {id}"
    pure (Session.start positive (state.restore id), response "restored")
  | .probability input =>
    let table ← input.table domains
    let some event := Event.checked table | throw "An event coefficient must be zero or one"
    pure (session, jsonMasses (session.masses positive event.table))
  | .expectation input =>
    let payoff ← input.table domains
    pure (session, jsonMasses (session.masses positive payoff))
  | .marginal raw =>
    let v ← index n raw
    let values := state.marginal? positive session.shared.get.1 v
    pure (session, values.elim Json.null (fun xs => .arr (xs.map jsonRational)))

def evaluate (packet : Packet) : Except String Json := do
  let domains := fun i : Fin packet.domains.size => packet.domains[i.val]
  if positive : ∀ v, 0 < domains v then
    let base ← packet.base.mapM (Factor.potential domains)
    let initial := Session.start positive (.initial base)
    let (_, answers) := packet.operations.foldl (fun (state, answers) op =>
      match applyOperation positive state op with
      | .ok (next, answer) => (next, answers.push answer)
      | .error message => (state, answers.push (Json.mkObj [("error", toJson message)])))
      (initial, #[])
    pure (.arr answers)
  else
    throw "Every variable must have a positive domain size"

end Mettapedia.ProbabilityTheory.StochasticInference.JsonReplay

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let evaluated := do
      let json ← Lean.Json.parse line
      let packet ← Lean.fromJson? json
      Mettapedia.ProbabilityTheory.StochasticInference.JsonReplay.evaluate packet
    let response := match evaluated with
      | .ok result => result
      | .error message => Lean.Json.mkObj [("error", Lean.toJson message)]
    output.putStrLn response.compress
    output.flush
