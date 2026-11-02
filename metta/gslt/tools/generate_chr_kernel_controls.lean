import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRGroundKernel
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassGraph

/-! Ground CHR transactions through the shared compiler, retained runner,
explorer and receipt-bearing graph. This gate does not qualify source
parsing, guard execution or the refined CHR controller. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace CHRKernelControls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRKernel
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open CompleteEmission

def freeTypes : List (String × TypeExpr) :=
  [("c", .base "ChrConstraintData"), ("d", .base "ChrConstraintData"),
   ("zero", .base "ChrOccurrenceId"), ("one", .base "ChrOccurrenceId"),
   ("rule", .base "ChrRuleId")]

def snapshot : GeneralExecutionAdmission.Snapshot := ⟨language, freeTypes, {signatures := [], rows := []}⟩
def permissions : GeneralExecutionAdmission.Permissions := {sites := .rootOnly, includeDerivedEquations := false}
def spec : Spec := ⟨GeneralExecutionAdmission.compile snapshot permissions, [], .base "ChrApplication", .canonical⟩

example : pendingFor spec .classes = [] := by decide_cbv

def first : Pattern := occurrence (.fvar "zero") (.fvar "c")
def second : Pattern := occurrence (.fvar "one") (.fvar "c")
def firing (ids : List String) : Pattern := key (.fvar "rule") (ids.map Pattern.fvar)

structure Control where
  label : String
  source : Pattern
  result : Option Pattern

def controlCases : List Control :=
  [⟨"simplification", application (firing ["zero"]) [] [first] [.fvar "d"] [first],
      some (applied (firing ["zero"]) [.fvar "d"] [])⟩,
   ⟨"simpagation-equal-values", application (firing ["zero", "one"]) [first] [second] [] [first, second],
      some (applied (firing ["zero", "one"]) [] [first])⟩,
   ⟨"propagation-keeps", application (firing ["zero"]) [first] [] [.fvar "d"] [first],
      some (applied (firing ["zero"]) [.fvar "d"] [first])⟩,
   ⟨"two-occurrences", application (firing ["zero", "one"]) [] [first, second] [] [first, second],
      some (applied (firing ["zero", "one"]) [] [])⟩,
   ⟨"same-occurrence-twice", application (firing ["zero", "zero"]) [first] [first] [] [first], none⟩,
   ⟨"missing-occurrence", application (firing ["one"]) [] [second] [] [first], none⟩,
   ⟨"wrong-value", application (firing ["zero"]) [] [occurrence (.fvar "zero") (.fvar "d")] [] [first], none⟩,
   ⟨"body-order", application (firing ["zero"]) [] [first] [.fvar "d", .fvar "c", .fvar "d"] [first],
      some (applied (firing ["zero"]) [.fvar "d", .fvar "c", .fvar "d"] [])⟩]

def modelSearch := Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode
def committed (source : Pattern) := Complete.Normalized.commit spec.plan spec.mode source
def begun (source : Pattern) := Mettapedia.Machines.ResumableSearchRunner.Machine.begin modelSearch (committed source)
def paged (source : Pattern) :=
  Mettapedia.Machines.ResumableSearchRunner.Machine.advance modelSearch 2 3000 (begun source)
def explored (source : Pattern) :=
  Complete.Explore.explore modelSearch (committed source) 1000
def graph (source : Pattern) :=
  let explorer := Complete.Settled.roundsUntilSettled modelSearch 1000 (Complete.Explore.begin modelSearch (committed source))
  encodeList CompleteExecution.edgeTerm (Complete.Graph.edges modelSearch explorer)

def pat (source : Pattern) := CettaWire.Term.render (InferenceCettaWire.encodePattern source)

def controls (control : Control) : String :=
  let trace := CompleteExecution.SearchWire.traceTerm (paged control.source)
  let states := encodeList InferenceCettaWire.encodePattern ((explored control.source).nodes.map (·.state))
  let edges := graph control.source
  let resumed := Mettapedia.Machines.ResumableSearchRunner.Machine.advance modelSearch 2 3000
    (Mettapedia.Machines.ResumableSearchRunner.Machine.advance modelSearch 1 5 (begun control.source))
  let resumeTrace := CompleteExecution.SearchWire.traceTerm resumed
  let plan := (CompletePlanWire.planTerm spec.plan spec.plan.snapshot.freeTypes spec.bound spec.expected).render
  let standard := (StandardWire.commitTerm spec.plan spec.mode (table spec)).render
  "!(let* (($input (quote " ++ pat control.source ++ "))" ++
    " ($plan (quote " ++ plan ++ ")) ($standard (quote " ++ standard ++ "))" ++
    " ($expected (quote " ++ trace.render ++ "))" ++
    " ($expected-states (quote " ++ states.render ++ "))" ++
    " ($expected-edges (quote " ++ edges.render ++ "))" ++
    " ($expected-resume (quote " ++ resumeTrace.render ++ "))" ++
    " ($trace (chr-kernel:run $input 2 3000))" ++
    " ($states (chr-kernel:explore $input 1000))" ++
    " ($edges (chr-kernel:edges $input 1000))" ++
    " ($begun (chr-kernel:begin $input))" ++
    " ($interrupted (gslt:runner:advance ClassSearch $plan $standard 1 5 $begun))" ++
    " ($resumed (gslt:runner:advance ClassSearch $plan $standard 2 3000 $interrupted))" ++
    " ($resumed-trace (gslt:runner:trace $resumed)))" ++
    " (println! (CHRKernelModelControl " ++ reprStr control.label ++
    " (== $trace $expected) (== $states $expected-states)" ++
    " (== $edges $expected-edges) (== $resumed-trace $expected-resume))))"

def main (arguments : List String) : IO Unit := do
  let [directory] := arguments | throw (IO.userError "expected output directory")
  IO.FS.createDirAll directory
  for control in controlCases do
    let machine := paged control.source
    unless machine.phase == .done do
      throw (IO.userError s!"control {control.label} remains pending; no exhaustion claim is authorized")
    match control.result with
    | none => unless machine.receipts.isEmpty do
        throw (IO.userError s!"negative control {control.label} invented a firing")
    | some result =>
        unless machine.receipts.length == 1 && machine.state == committed result do
          throw (IO.userError s!"control {control.label} did not reach its declared transaction result")
    IO.println s!"model {control.label}: receipts={machine.receipts.length}, complete=true"
  let .ok text := emitText? spec "chr-kernel" .classes
    | throw (IO.userError s!"the CHR transaction kernel was refused: {reprStr spec.plan.obligations}")
  IO.FS.writeFile (System.FilePath.mk directory / "query.metta") text
  IO.FS.writeFile (System.FilePath.mk directory / "controls.metta")
    (String.intercalate "\n" (controlCases.map controls) ++ "\n")

end CHRKernelControls

def main := CHRKernelControls.main
