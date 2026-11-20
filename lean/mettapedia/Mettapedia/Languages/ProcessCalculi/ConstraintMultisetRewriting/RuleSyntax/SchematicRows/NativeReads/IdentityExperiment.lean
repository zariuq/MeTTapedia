import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.OccurrenceKey

/-!
# Occurrence identity component experiment

The reference registers full origins by linear search. The alternative
encodes and decodes the complete key without a registration search. Both
return the same full origin sequence, not just a checksum or set. Timings
include registration or encoding and all returned decoding. They concern
this Lean identity component, not native row loading or whole queries.
Bounded encoding refusal and repeated-origin regimes are separate controls.
-/

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.IdentityExperiment

def input (size salt : Nat) (repeated : Bool) : Array OccurrenceKey :=
  (List.range size).toArray.map fun position =>
    ⟨salt % 3, salt % 5, salt % 7, if repeated then 0 else position⟩

def reference (keys : Array OccurrenceKey) : Array (Option OccurrenceKey) := Id.run do
  let mut registered : Array OccurrenceKey := #[]
  let mut output : Array (Option OccurrenceKey) := #[]
  for key in keys do
    match registered.findIdx? (fun row => decide (row = key)) with
    | some index => output := output.push registered[index]?
    | none =>
        registered := registered.push key
        output := output.push (some key)
  return output

def encoded (keys : Array OccurrenceKey) : Array (Option OccurrenceKey) :=
  keys.map fun key => OccurrenceKey.decode key.encode

def measure (name : String) (work : Array OccurrenceKey → Array (Option OccurrenceKey))
    (size batches : Nat) (repeated : Bool) : IO Nat := do
  let start ← IO.monoNanosNow
  let mut checksum := 0
  for batch in [:batches] do
    let keys := input size batch repeated
    let result := work keys
    unless result = keys.map some do
      throw (IO.userError s!"{name}: origin mismatch")
    checksum := checksum + result.size
  unless checksum = size * batches do
    throw (IO.userError s!"{name}: lost occurrence")
  let finish ← IO.monoNanosNow
  return finish - start

def controls : IO Unit := do
  let mut cases := 0
  for size in [0, 1, 2, 8, 33, 64] do
    for salt in [0, 3] do
      for repeated in [false, true] do
        let keys := input size salt repeated
        unless reference keys = encoded keys && encoded keys = keys.map some do
          throw (IO.userError s!"differential failure {size}/{salt}/{repeated}")
        cases := cases + 1
  for slot in List.range 64 do
    let key : OccurrenceKey := ⟨1, 2, 3, slot⟩
    let bounded := OccurrenceKey.checked 65536 key
    match bounded with
    | none =>
        unless 65536 ≤ key.encode do throw (IO.userError "false capacity refusal")
    | some word =>
        unless OccurrenceKey.decode word = some key do throw (IO.userError "truncated origin")
  IO.println s!"controls=pass differential_cases={cases} capacity_cases=64 scope=identity-component"

def experiment (batches : Nat) (encodedFirst : Bool) : IO Unit := do
  controls
  for repeated in [false, true] do
    for size in [8, 64, 256, 1024, 4096] do
      let times ← if encodedFirst then do
          let prepared ← measure "encoded" encoded size batches repeated
          let baseline ← measure "linear" reference size batches repeated
          pure (baseline, prepared)
        else do
          let baseline ← measure "linear" reference size batches repeated
          let prepared ← measure "encoded" encoded size batches repeated
          pure (baseline, prepared)
      let wordFits := (List.range batches).foldl (fun count batch => count +
        ((input size batch repeated).filter fun key => (OccurrenceKey.checked (2 ^ 64) key).isSome).size) 0
      IO.println s!"size={size} batches={batches} repeated={repeated} encoded_first={encodedFirst} linear_ns={times.1} encoded_ns={times.2} speedup_milli={1000 * times.1 / max 1 times.2} word64_fits={wordFits} total={size * batches}"

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.IdentityExperiment

def main (arguments : List String) : IO Unit :=
  Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.IdentityExperiment.experiment
    ((arguments.headD "3").toNat?.getD 3) (arguments.contains "encoded-first")
