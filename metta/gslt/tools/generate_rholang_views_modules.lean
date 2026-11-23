/-
Writes `tests/petta/emitted/rholang_closure.metta` and `tests/petta/emitted/rholang_freeze.metta`
(canonical form) with `CompleteEmission.emitText?` for Rholang's core under the closure view and
under the freeze view, and writes their controls `tests/petta/gslt_rholang_closure_controls.metta`
and `tests/petta/gslt_rholang_freeze_controls.metta`. Every expected readout is the Lean explorer's
(`Complete.Explore` over `Complete.Normalized.search`).
Run from `lean/mettapedia`: `lake env lean --run ../../metta/gslt/tools/generate_rholang_views_modules.lean`.
-/
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.OSLF.MeTTaIL.RholangClosure
import Mettapedia.OSLF.MeTTaIL.RholangFreeze

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire InferenceCettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

def render (term : Term) : String := Term.render term
def pat (p : Pattern) : String := render (encodePattern p)

def quote (process : Pattern) : Pattern := .apply "NQuote" [process]
def drop (name : Pattern) : Pattern := .apply "PDrop" [name]
def output (name process : Pattern) : Pattern := .apply "POutput" [name, process]
def input (name body : Pattern) : Pattern := .apply "PInput" [name, .lambda none body]
def par (processes : List Pattern) : Pattern := .collection .hashBag processes none

def states (spec : Spec) (source : Pattern) (work : Nat) : List Pattern :=
  (Complete.Explore.explore (Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode)
    (Complete.Normalized.commit spec.plan spec.mode source) work).nodes.map (·.state)

def exploreControl (spec : Spec) (module control label : String) (source : Pattern) (work : Nat) : String :=
  "!(let $s (" ++ module ++ ":explore " ++ pat source ++ " " ++ toString work ++ ")\n" ++
  "  (println! (" ++ control ++ " " ++ reprStr label ++ " (== $s (quote " ++
    render (CettaWire.encodeList encodePattern (states spec source work)) ++ ")))))"

/-! ## Closure -/

def closureSpec : Spec := ⟨Rholang.Closure.plan, [], .base "Proc", .canonical⟩

/-- `for(@v <- @"in"){ @"in"!(@{v!(1)}) } | @"in"!(42) | for(@w <- @"in"){ *w }`: the received
code is forwarded as a name, outside every genuine quotation, and the next receiver runs it. -/
def relay : Pattern :=
  par [input Rholang.inChannel (output Rholang.inChannel (output (quote (drop (.bvar 0))) Rholang.int1)),
    output Rholang.inChannel Rholang.int42, input Rholang.inChannel (drop (.bvar 0))]

def closureSources : List (String × Pattern) :=
  [("keeps-context", Rholang.source), ("relay", relay), ("context-payload", Rholang.Closure.contextPayload)]

/-! ## Freeze -/

def freezeSpec : Spec := ⟨Rholang.Freeze.plan, [], .base "Proc", .canonical⟩

/-- `@0(z).w!(y[z]) | @0!(0)`: the lifted body is outside every quotation, so the drop of `z` runs
the received payload. -/
def lifted : Pattern :=
  par [input Rholang.Freeze.zeroName (output Rholang.Freeze.zeroName (output Rholang.Freeze.zeroName
      (drop (.bvar 0)))),
    output Rholang.Freeze.zeroName (.apply "PZero" [])]

def freezeSources : List (String × Pattern) :=
  [("dynamic-quote", Rholang.Freeze.source), ("lifted-body", lifted),
    ("stores-spelling", Rholang.source)]

def emitModule (spec : Spec) (module control : String) (sources : List (String × Pattern))
    (header : String) (work : Nat) : IO Unit := do
  let dir := "../../metta/gslt/tests/petta/"
  match emitText? spec module with
  | .ok text => IO.FS.writeFile (dir ++ "emitted/" ++ module ++ ".metta") text
  | .error _ => throw (IO.userError s!"refused: {module}")
  let lines := [header, "; Every expected readout is the Lean explorer's."] ++
    sources.map fun (label, source) => exploreControl spec module control label source work
  IO.FS.writeFile (dir ++ "gslt_" ++ module ++ "_controls.metta") (String.intercalate "\n" lines ++ "\n")
  for (label, source) in sources do
    IO.eprintln s!"{module} {label}: {(states spec source work).length} states"

def main : IO Unit := do
  emitModule closureSpec "rholang_closure" "RholangClosureControl" closureSources
    "; Controls for the emitted Rholang module under the closure view." 200
  emitModule freezeSpec "rholang_freeze" "RholangFreezeControl" freezeSources
    "; Controls for the emitted Rholang module under the freeze view." 200
