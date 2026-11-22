/-
Writes `tests/petta/emitted/*.metta` with `emitText?` and prints
`tests/petta/gslt_emitted_module_controls.metta`. Every expected trace is the Lean model's.
Run from `lean/mettapedia`: `lake env lean ../../metta/gslt/tools/generate_emitted_modules.lean`.
-/
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralLiveRunnerEmission
import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend
import Mettapedia.Languages.PartrecMachine.Adequacy

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralLiveRunnerExecution

def render (t : Mettapedia.GSLT.LanguageDef.CettaWire.Term) : String :=
  Mettapedia.GSLT.LanguageDef.CettaWire.Term.render t
def pat (p : Pattern) : String := render (Mettapedia.GSLT.LanguageDef.InferenceCettaWire.encodePattern p)

def c (name : String) (args : List Pattern := []) : Pattern := .apply name args
def nat : Nat → Pattern
  | 0 => c "Zero"
  | n + 1 => c "Succ" [nat n]

def simple (name sort : String) : TermParam := .simple name (.base sort)

def arithTerms : List GrammarRule :=
  [{ label := "Zero", category := "Nat", params := [], syntaxPattern := [] },
   { label := "Succ", category := "Nat", params := [simple "arg0" "Nat"], syntaxPattern := [.nonTerminal "arg0"] },
   { label := "Add", category := "Nat", params := [simple "arg0" "Nat", simple "arg1" "Nat"],
     syntaxPattern := [.nonTerminal "arg0", .nonTerminal "arg1"] }]

def arithRewrites : List RewriteRule :=
  [{ name := "add-zero", typeContext := [("y", .base "Nat")], premises := [],
     left := c "Add" [c "Zero", .fvar "y"], right := .fvar "y" },
   { name := "add-succ", typeContext := [("x", .base "Nat"), ("y", .base "Nat")], premises := [],
     left := c "Add" [c "Succ" [.fvar "x"], .fvar "y"], right := c "Succ" [c "Add" [.fvar "x", .fvar "y"]] }]

def arith : LanguageDef := LanguageDef.ofCore "Arith" ["Nat"] arithTerms [] arithRewrites

def arithSpec : Spec :=
  ⟨GeneralExecutionAdmission.compile ⟨arith, [("n", .base "Nat")], { signatures := [], rows := [] }⟩ {}, [], .base "Nat"⟩

def cycleTerms : List GrammarRule :=
  [{ label := "A", category := "State", params := [], syntaxPattern := [] },
   { label := "B", category := "State", params := [], syntaxPattern := [] }]

def cycleRewrites : List RewriteRule :=
  [{ name := "a-to-b", typeContext := [], premises := [], left := c "A", right := c "B" },
   { name := "b-to-a", typeContext := [], premises := [], left := c "B", right := c "A" }]

def cycleSpec : Spec :=
  ⟨GeneralExecutionAdmission.compile ⟨LanguageDef.ofCore "Cycle" ["State"] cycleTerms [] cycleRewrites, [], { signatures := [], rows := [] }⟩
    {sites := .rootOnly}, [], .base "State"⟩

def partrecSpec : Spec := ⟨Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan, [], .base "Cfg"⟩

def planText (spec : Spec) : String := render (planTerm spec spec.plan.snapshot.freeTypes)

def traceText (spec : Spec) (source : Pattern) (ticks quantum : Nat) : String :=
  render (Machine.advance spec ticks quantum (Machine.begin spec source)).traceTerm

def runControl (label : String) (spec : Spec) (source : Pattern) (ticks quantum : Nat) : String :=
  "!(let* (($m (gslt:live:begin " ++ planText spec ++ " " ++ pat source ++ "))\n" ++
  "        ($a (gslt:live:advance $m " ++ toString ticks ++ " " ++ toString quantum ++ "))\n" ++
  "        ($t (gslt:live:trace $a)))\n" ++
  "  (println! (LiveRunControl " ++ reprStr label ++ " (== $t (quote " ++ traceText spec source ticks quantum ++ ")))))"

def pagedControl (label : String) (spec : Spec) (source : Pattern) (first second quantum : Nat) : String :=
  "!(let* (($m (gslt:live:begin " ++ planText spec ++ " " ++ pat source ++ "))\n" ++
  "        ($a (gslt:live:advance $m " ++ toString first ++ " " ++ toString quantum ++ "))\n" ++
  "        ($b (gslt:live:advance $a " ++ toString second ++ " " ++ toString quantum ++ "))\n" ++
  "        ($w (gslt:live:advance $m " ++ toString (first + second) ++ " " ++ toString quantum ++ ")))\n" ++
  "  (println! (LiveRunControl " ++ reprStr label ++ " (== $b $w))))"

def fixedControl (label : String) (spec : Spec) (source : Pattern) (ticks quantum : Nat) : String :=
  "!(let* (($m (gslt:live:begin " ++ planText spec ++ " " ++ pat source ++ "))\n" ++
  "        ($a (gslt:live:advance $m " ++ toString ticks ++ " " ++ toString quantum ++ "))\n" ++
  "        ($b (gslt:live:tick $a " ++ toString quantum ++ ")))\n" ++
  "  (println! (LiveRunControl " ++ reprStr label ++ " (== $b $a))))"

def differControl (label : String) (spec : Spec) (source : Pattern) (first second quantum : Nat) : String :=
  "!(let* (($m (gslt:live:begin " ++ planText spec ++ " " ++ pat source ++ "))\n" ++
  "        ($a (gslt:live:advance $m " ++ toString first ++ " " ++ toString quantum ++ "))\n" ++
  "        ($b (gslt:live:advance $m " ++ toString second ++ " " ++ toString quantum ++ "))\n" ++
  "        ($s (gslt:live:trace $a)) ($t (gslt:live:trace $b)))\n" ++
  "  (println! (LiveRunControl " ++ reprStr label ++ " (== (== $s $t) False))))"

def two_plus_one : Pattern := c "Add" [nat 2, nat 1]
def open_term : Pattern := c "Add" [c "Succ" [.fvar "n"], c "Zero"]
def mixed : Pattern := .subst (c "f" [.fvar "a", .bvar 0]) (.collection .vec [.fvar "b"] (some "r"))

open Mettapedia.Languages.PartrecMachine in
def partrecSucc : Pattern := normalTerm .succ .halt [2]

open Mettapedia.Languages.PartrecMachine in
def partrecFix : Pattern := normalTerm (.fix .tail) .halt [3]

def table : List (String × TypeExpr) := [("a", .base "A"), ("b", .base "B"), ("a", .base "C")]
def names : List String := ["a", "z", "b", "a"]


open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralLiveRunnerEmission in
def emitTo (spec : Spec) (name : String) (path : String) : IO Unit := do
  match emitText? spec name with
  | .ok text => IO.FS.writeFile path text
  | .error _ => throw (IO.userError s!"refused: {name}")

def entryControl (label name : String) (spec : Spec) (source : Pattern) (ticks quantum : Nat) : String :=
  "!(let $t (" ++ name ++ ":run " ++ pat source ++ " " ++ toString ticks ++ " " ++ toString quantum ++ ")\n" ++
  "  (println! (EmittedRunControl " ++ reprStr label ++ " (== $t (quote " ++ traceText spec source ticks quantum ++ ")))))"

def beginControl (label name : String) (spec : Spec) (source : Pattern) (ticks quantum : Nat) : String :=
  "!(let* (($m (" ++ name ++ ":begin " ++ pat source ++ "))\n" ++
  "        ($a (gslt:live:advance $m " ++ toString ticks ++ " " ++ toString quantum ++ "))\n" ++
  "        ($t (gslt:live:trace $a)))\n" ++
  "  (println! (EmittedRunControl " ++ reprStr label ++ " (== $t (quote " ++ traceText spec source ticks quantum ++ ")))))"

open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralLiveRunnerEmission in
def refusalControl : String :=
  match emitText? arithSpec "gslt:live" with
  | .error (.nameCollision _) => "refused-name-collision"
  | _ => "NOT-REFUSED"

def main : IO Unit := do
  let dir := "../../metta/gslt/tests/petta/emitted/"
  IO.FS.createDirAll dir
  emitTo arithSpec "arith" (dir ++ "arith.metta")
  emitTo cycleSpec "cycle" (dir ++ "cycle.metta")
  emitTo partrecSpec "partrec" (dir ++ "partrec.metta")
  IO.println "; Controls for emitted modules. Each module was written by"
  IO.println "; GeneralLiveRunnerEmission.emitText?; every expected trace is the Lean model's."
  IO.println (entryControl "arith-run-normal" "arith" arithSpec two_plus_one 200 1)
  IO.println (entryControl "arith-open-term" "arith" arithSpec open_term 200 1)
  IO.println (beginControl "arith-begin-then-pages" "arith" arithSpec two_plus_one 60 1)
  IO.println (entryControl "cycle-keeps-running" "cycle" cycleSpec (c "A") 5 1000)
  IO.println (entryControl "partrec-succ-halts" "partrec" partrecSpec partrecSucc 50 1000)
  IO.println (entryControl "partrec-fix-tail-halts" "partrec" partrecSpec partrecFix 50 1000)
  IO.println ("; name collision with the runtime: " ++ refusalControl)

#eval main
