import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# Running the PeTTa executable fragment

`pettaRun MODE REQUESTS FUEL PROGRAM...` reads the supplied program files
in order and executes them with Eval's machine. MODE is `stream`
for program initializers with parsed input, or `requests` for separate expressions
with persistent private spaces and state cells. Completed answers are printed;
faults and fuel exhaustion have separate nonzero exit statuses.

This driver contains no guest-specific checking operations. Text reading is the
source reader's stated boundary, and compiling the driver changes neither the
machine nor its operational GSLT.
-/

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Eval
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

private def readProgram (paths : List String) : IO SpaceSemantics.Program := do
  let mut loaded : SpaceSemantics.Program := { equations := [], declarations := [] }
  for path in paths do
    match SpaceSemantics.readProgram (← IO.FS.readFile path) with
    | .ok program => loaded := loaded.append program
    | .error reason => throw (IO.userError s!"{path}: {reason}")
  return loaded

private def readRequests (path : String) : IO (List Atom) := do
  let mut requests := []
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.trimAscii.toString.isEmpty then continue
    match SpaceSemantics.readSource line with
    | .ok [expression] => requests := expression :: requests
    | .ok _ => throw (IO.userError "expected one request per line")
    | .error reason => throw (IO.userError s!"request: {reason}")
  return requests.reverse

private def printAnswer (answer : Atom) : IO Unit :=
  match answer with
  | .grounded (.bool true) => IO.println "true"
  | .grounded (.bool false) => IO.println "false"
  | _ => IO.println answer

private def runStream (program : SpaceSemantics.Program) (fuel : Nat)
    (requests : List Atom) : IO UInt32 := do
  let initial : Configuration := {
    state := Effects.loaded program
    control := .sequence (program.initializers.map (.evaluate [] ·)) []
    input := requests }
  match run program fuel initial with
  | .complete _ answers remaining printed =>
      if !remaining.isEmpty then throw (IO.userError "unconsumed input")
      for answer in printed ++ answers do printAnswer answer
      return 0
  | .fault fault => IO.eprintln s!"fault: {repr fault}"; return 1
  | .exhausted configuration =>
      IO.eprintln s!"exhausted: {repr configuration.control}"
      return 2

private def runRequests (program : SpaceSemantics.Program) (fuel : Nat)
    (requests : List Atom) : IO UInt32 := do
  let mut state := Effects.loaded program
  for request in requests do
    match evaluate program fuel state request with
    | .complete after answers _ printed =>
        for answer in printed ++ answers do printAnswer answer
        state := after
    | .fault fault => IO.eprintln s!"fault: {repr fault}"; return 1
    | .exhausted configuration =>
        IO.eprintln s!"exhausted: {repr configuration.control}"
        return 2
  return 0

def main (arguments : List String) : IO UInt32 := do
  let mode :: requests :: rawFuel :: paths := arguments
    | throw (IO.userError "use MODE REQUESTS FUEL PROGRAM...")
  if paths.isEmpty then throw (IO.userError "no program files")
  let some fuel := rawFuel.toNat?
    | throw (IO.userError "expected a natural-number fuel bound")
  let program ← readProgram paths
  let requests ← readRequests requests
  match mode with
  | "stream" => runStream program fuel requests
  | "requests" => runRequests program fuel requests
  | _ => throw (IO.userError "mode must be stream or requests")
