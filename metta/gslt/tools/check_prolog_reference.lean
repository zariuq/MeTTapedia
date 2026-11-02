import Mettapedia.Logic.Prolog.ReaderTerm
import Mettapedia.Logic.LP.TermEquality
/-! Compare ground-numbered canonical reference output with the same LP carrier. -/
open Mettapedia.Logic.Prolog

def numbered : SourceSignature.Term → SourceSignature.Term
  | .var identity => SourceSignature.compound "$VAR" [SourceSignature.integer (Int.ofNat identity.occurrence)]
  | .const value => .const value
  | .app symbol args => .app symbol (fun i => numbered (args i))

def usesNumberingFunctor : SourceSignature.Term → Bool
  | .var _ | .const _ => false
  | .app symbol args => symbol.name == "$VAR" ||
      (List.ofFn fun i => usesNumberingFunctor (args i)).any id

def main (args : List String) : IO Unit := do
  let [dialect,input,canonical] := args | throw (IO.userError "expected profile and two sources")
  let profile ← match dialect with
    | "iso" => pure ReaderProfile.iso | "swi" => pure ReaderProfile.swi
    | _ => throw (IO.userError "unknown reader profile")
  let .ok original := ReaderTerm.readOneWith profile profile.operators (← IO.FS.readFile input)
    | throw (IO.userError "original source refused")
  if usesNumberingFunctor original.term then
    throw (IO.userError "canonical variable numbering needs a fresh marker")
  let .ok reference := ReaderTerm.readOneWith profile profile.operators (← IO.FS.readFile canonical)
    | throw (IO.userError "external canonical output refused")
  unless numbered original.term = reference.term do throw (IO.userError "external term differs")
  IO.println "external canonical term agrees"
