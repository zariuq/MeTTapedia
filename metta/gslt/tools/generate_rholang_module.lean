/-
Writes `tests/petta/emitted/rholang.metta` (canonical form) with `CompleteEmission.emitText?` for the
Rholang presentation, whose binders reach into quotations through the apply view, and prints
`tests/petta/gslt_rholang_module_controls.metta`. Every expected readout is the Lean explorer's
(`Complete.Explore` over `Complete.Normalized.search`).
Run from `lean/mettapedia`: `lake env lean --run ../../metta/gslt/tools/generate_rholang_module.lean`.
-/
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.OSLF.MeTTaIL.RholangClosure

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

def render (term : Term) : String := Term.render term
def pat (p : Pattern) : String := render (encodePattern p)

def spec : Spec := ⟨Rholang.plan, [], .base "Proc", .canonical⟩

def quote (process : Pattern) : Pattern := .apply "NQuote" [process]
def drop (name : Pattern) : Pattern := .apply "PDrop" [name]
def output (name process : Pattern) : Pattern := .apply "POutput" [name, process]
def input (name body : Pattern) : Pattern := .apply "PInput" [name, .lambda none body]
def par (processes : List Pattern) : Pattern := .collection .hashBag processes none

/-- `for(@v <- @"in"){ @{@v!(0)}!(1) } | @"in"!(42)`: the received `42` reaches into the quoted channel. -/
def stores : Pattern := Rholang.source
/-- `for(@v <- @"in"){ @{@"in"!(0)}!(v) } | @"in"!(42)`: a quotation that does not mention the binder. -/
def sealedQuote : Pattern :=
  par [input Rholang.inChannel (output (quote (output Rholang.inChannel Rholang.int0)) (drop (.bvar 0))),
    output Rholang.inChannel Rholang.int42]
/-- `for(@v <- @"in"){ @"in"!(@{v!(1)}) } | @"in"!(42) | for(@w <- @"in"){ *w }`: the received code is forwarded
inside a quotation, and the next receiver runs it. -/
def relay : Pattern :=
  par [input Rholang.inChannel (output Rholang.inChannel (output (quote (drop (.bvar 0))) Rholang.int1)),
    output Rholang.inChannel Rholang.int42, input Rholang.inChannel (drop (.bvar 0))]

/-- `for(@v <- @"in"){ v } | @"in"!(*κ(@42))`: the payload holds a context, which this presentation
does not type, so no step starts. -/
def contextPayload : Pattern := Rholang.Closure.contextPayload

def states (source : Pattern) (work : Nat) : List Pattern :=
  (Complete.Explore.explore (Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode)
    (Complete.Normalized.commit spec.plan spec.mode source) work).nodes.map (·.state)

def exploreControl (label : String) (source : Pattern) (work : Nat) : String :=
  "!(let $s (rholang:explore " ++ pat source ++ " " ++ toString work ++ ")\n" ++
  "  (println! (RholangModuleControl " ++ reprStr label ++ " (== $s (quote " ++
    render (CettaWire.encodeList encodePattern (states source work)) ++ ")))))"

def main : IO Unit := do
  let dir := "../../metta/gslt/tests/petta/emitted/"
  match emitText? spec "rholang" with
  | .ok text => IO.FS.writeFile (dir ++ "rholang.metta") text
  | .error _ => throw (IO.userError "refused: rholang")
  let work := 200
  let sources := [("stores-received", stores), ("sealed-quote", sealedQuote), ("relay", relay),
    ("context-rejected", contextPayload)]
  IO.println "; Controls for the emitted Rholang module, whose binders reach into quotations."
  IO.println "; Every expected readout is the Lean explorer's."
  for (label, source) in sources do
    IO.println (exploreControl label source work)
  for (label, source) in sources do
    IO.eprintln s!"{label}: {(states source work).length} states"
