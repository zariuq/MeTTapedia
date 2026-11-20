import Mettapedia.ProbabilityTheory.ImpreciseProbability.AnytimeConditional
import Mettapedia.ProbabilityTheory.ImpreciseProbability.ConditionalCertificates
import Lean.Data.Json.FromToJson

/-!
# Rational credal query replay

One JSON packet per line specifies the truth table of each event, simultaneous
conditional constraints, and a sequence of pair budgets per projection pivot.
The runner retains the tightest enclosure reached on that knowledge snapshot.
Optional endpoint certificates carry row multipliers and attaining world
weights. A refutation instead combines rows to the positive constant one.
Its optional consistency witness supplies a model of the original base
for an unsupported-evidence claim.
-/

set_option autoImplicit false

namespace Mettapedia.Examples.PLN.AnytimeCredalReplay

open Lean
open Mettapedia.ProbabilityTheory.ImpreciseProbability
open FiniteConditionalConstraints

structure Reading where
  event : Array Bool
  condition : Array Bool
  lower : Int × Nat
  upper : Int × Nat
  deriving FromJson

structure Certificate where
  value : Int × Nat
  weights : List (Int × Nat)
  witness : Array (Int × Nat)
  deriving FromJson

structure Refutation where
  weights : List (Int × Nat)
  /-- A witness for the original base distinguishes unsupported evidence
  from inconsistent constraints. -/
  consistencyWitness : Option (Array (Int × Nat)) := none
  deriving FromJson

structure Packet where
  worlds : Nat
  constraints : List Reading
  query : Array Bool
  evidence : Array Bool
  budgets : List Nat
  certificates : Option (Certificate × Certificate) := none
  refutation : Option Refutation := none
  deriving FromJson

private def eventAt (worlds : Nat) (raw : Array Bool) : Except String (Event (Fin worlds)) :=
  if len : raw.size = worlds then
    .ok (fun index => raw[index.val]'(by rw [len]; exact index.isLt))
  else .error s!"Expected truth table with {worlds} worlds"

private def asRational (pair : Int × Nat) : Except String ℚ :=
  if pair.2 > 0 then .ok ((pair.1 : ℚ) / pair.2)
  else .error "A rational endpoint needs a positive denominator"

private def checked (worlds : Nat) (r : Reading) : Except String (Constraint (Fin worlds)) := do
  let event ← eventAt worlds r.event
  let condition ← eventAt worlds r.condition
  let lower ← asRational r.lower
  let upper ← asRational r.upper
  if h : 0 ≤ lower ∧ lower ≤ upper ∧ upper ≤ 1 then
    pure ⟨event, condition, lower, upper, h.1, h.2.1, h.2.2⟩
  else throw "A conditional interval must be ordered and lie in [0,1]"

private def encode (p : ℚ) : Json := toJson (p.num, p.den)

private def decodeModel (worlds : Nat) (raw : Array (Int × Nat)) : Except String (Fin worlds → ℚ) := do
  let witness ← raw.mapM asRational
  if h : witness.size = worlds then
    pure (fun index => witness[index.val]'(by rw [h]; exact index.isLt))
  else throw s!"Expected {worlds} witness coordinates"

private def decodeCertificate (worlds : Nat) (certificate : Certificate) :
    Except String (ConditionalCertificates.Endpoint × (Fin worlds → ℚ)) := do
  let value ← asRational certificate.value
  let weights ← certificate.weights.mapM asRational
  let witness ← decodeModel worlds certificate.witness
  pure (⟨value, weights⟩, witness)

private def classifyRefutation {worlds : Nat} (base : KnowledgeBase (Fin worlds))
    (event condition : Event (Fin worlds)) (refutation : Refutation) : Except String String := do
  let weights ← refutation.weights.mapM asRational
  match refutation.consistencyWitness with
  | none =>
    if ConditionalCertificates.checkInconsistent base weights then pure "inconsistent"
    else throw "The inconsistency certificate did not verify"
  | some raw =>
    let witness ← decodeModel worlds raw
    if ConditionalCertificates.checkConsistent base witness &&
        ConditionalCertificates.checkImpossible base event condition weights then pure "unsupported"
    else throw "The unsupported-evidence certificate did not verify"

def evaluate (packet : Packet) : Except String Json := do
  let base ← packet.constraints.mapM (checked packet.worlds)
  let event ← eventAt packet.worlds packet.query
  let condition ← eventAt packet.worlds packet.evidence
  let (_, _, responses) := packet.budgets.foldl (fun (current, finished, records) fuel =>
    let (next, complete) := if finished || current.isNone then (current, finished)
      else AnytimeConditional.queryReported fuel base event condition
    let refined := AnytimeConditional.tighten current next
    let interval := match refined with
      | some (lo, hi) => Json.arr #[encode lo, encode hi]
      | none => Json.null
    let report := Json.mkObj [("pairsPerPivot", toJson fuel), ("interval", interval),
      ("projectionComplete", toJson complete)]
    (refined, complete, records.push report))
    (AnytimeConditional.initial, false, (#[] : Array Json))
  match packet.certificates, packet.refutation with
  | none, none => pure (.arr responses)
  | none, some refutation =>
    let status ← classifyRefutation base event condition refutation
    pure (Json.mkObj [("projection", .arr responses), ("status", toJson status)])
  | some _, some _ => throw "Supply either endpoint certificates or a refutation"
  | some (lower, upper), none =>
    let (low, lowWitness) ← decodeCertificate packet.worlds lower
    let (high, highWitness) ← decodeCertificate packet.worlds upper
    if ConditionalCertificates.checkSharp base event condition low high lowWitness highWitness then
      pure (Json.mkObj [("projection", .arr responses),
        ("sharp", .arr #[encode low.value, encode high.value])])
    else throw "The endpoint certificates did not verify"

end Mettapedia.Examples.PLN.AnytimeCredalReplay

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := do
      let json ← Lean.Json.parse line
      let packet ← Lean.fromJson? json
      Mettapedia.Examples.PLN.AnytimeCredalReplay.evaluate packet
    let response := match result with
      | .ok value => value
      | .error message => Lean.Json.mkObj [("error", Lean.toJson message)]
    output.putStrLn response.compress
    output.flush
