import Mettapedia.Languages.HOLLight.RuleModuleAlphaOrder
import Mettapedia.Languages.HOLLight.FirstOrder.NativePremises

/-! Differential controls for the two HOL rule presentations. The named
module goes through CeTTa's own module reader and tcalc evaluator; the
portable module goes through its validated reader and premise compiler. -/

open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.RuleModuleAlphaOrder
open RuleModulePrimitives (Str)
open RuleModuleComparisonLaws (Ty Term)

private structure Datum (α : Type) where
  value : α
  wire : String

private def nilName : Datum Str := ⟨.nnil, "(hl:nnil)"⟩
private def otherName : Datum Str :=
  ⟨.ncons (.byte .x0 .x0) .nnil, "(hl:ncons (hl:byte (hl:x0) (hl:x0)) (hl:nnil))"⟩
private def ty (n : Datum Str) : Datum Ty := ⟨.Tyvar n.value, "(hl:Tyvar " ++ n.wire ++ ")"⟩
private def var (n : Datum Str) (t : Datum Ty) : Datum Term :=
  ⟨.Var n.value t.value, "(hl:Var " ++ n.wire ++ " " ++ t.wire ++ ")"⟩
private def con (n : Datum Str) (t : Datum Ty) : Datum Term :=
  ⟨.Const n.value t.value, "(hl:Const " ++ n.wire ++ " " ++ t.wire ++ ")"⟩
private def lam (v b : Datum Term) : Datum Term :=
  ⟨.Abs v.value b.value, "(hl:Abs " ++ v.wire ++ " " ++ b.wire ++ ")"⟩
private def app (f a : Datum Term) : Datum Term :=
  ⟨.Comb f.value a.value, "(hl:Comb " ++ f.wire ++ " " ++ a.wire ++ ")"⟩

private structure Probe where
  label : String
  l : Datum Term
  r : Datum Term
  answer : Option Result

private def probes : List Probe := Id.run do
  let a := ty nilName
  let x := var nilName a
  let y := var otherName a
  let xb := var nilName (ty otherName)
  let c := con nilName a
  let malformed := lam c x
  return [⟨"renamed", lam x x, lam y y, some .eq⟩,
    ⟨"typed-free", lam x xb, lam y xb, some .eq⟩,
    ⟨"bound-before-free", lam x x, lam y x, some .lt⟩,
    ⟨"free-after-bound", lam y x, lam x x, some .gt⟩,
    ⟨"nearest-first", lam x (lam y y), lam x (lam y x), some .lt⟩,
    ⟨"shadow", lam x (lam x x), lam x (lam y y), some .eq⟩,
    ⟨"binder-type", lam x x, lam xb xb, some .lt⟩,
    ⟨"constructor-rank", c, x, some .lt⟩,
    ⟨"application-tail", app c (lam x x), app c (lam y x), some .lt⟩,
    ⟨"malformed-tie", malformed, malformed, none⟩,
    ⟨"malformed-head-only", malformed, c, some .gt⟩,
    ⟨"short-circuit", app c malformed, app x malformed, some .lt⟩]

private def sign : Result → String
  | .lt => "hl:lt" | .eq => "hl:eq" | .gt => "hl:gt"

private def run (bin : System.FilePath) (args : Array String) : IO String := do
  let p ← IO.Process.output {cmd := bin.toString, args}
  unless p.exitCode == 0 do throw (IO.userError (p.stderr ++ (p.stdout.takeEnd 1000).toString))
  return p.stdout

private def named (root cetta work : System.FilePath) : IO Unit := do
  let bin := cetta / "cetta"
  let path := work / "comparison.tcalc"
  let loader := work / "load.metta"
  let quote (p : System.FilePath) := (Lean.Json.str p.toString).compress
  IO.FS.writeFile loader ("!(import! &self " ++ quote (cetta / "lib/tcalc_modules.metta") ++ ")\n" ++
    "!(tcalc:module-write " ++ quote (root / "metta/gslt/module/HOLLightKernel.module") ++
    " \"Kernel\" " ++ quote path ++ ")\n")
  let _ ← run bin #[loader.toString]
  let mut program ← IO.FS.readFile path
  for p in probes do
    unless compiledOrder [] p.l.value p.r.value == p.answer do throw (IO.userError ("frame: " ++ p.label))
    let q := "(hl:alphaorder " ++ p.l.wire ++ " " ++ p.r.wire ++ ")"
    program := program ++ "\n(demand " ++ q ++ ")\n(rule check-" ++ p.label ++ " (read (value " ++ q ++
      " $result)) (make (observed " ++ p.label ++ " $result)))\n"
  IO.FS.writeFile path program
  let output ← run bin #["--lang", "tcalc", "--profile", "observe=outcomes", path.toString]
  unless output.contains "(finished true)" && (output.splitOn "(outcome ").length == 2 do
    throw (IO.userError "incomplete or non-unique reference outcome")
  for p in probes do
    let marker := "(observed " ++ p.label ++ " "
    let occurrences := (output.splitOn marker).length - 1
    match compiledOrder [] p.l.value p.r.value with
    | none => unless occurrences == 0 do throw (IO.userError ("unexpected answer: " ++ p.label))
    | some answer => unless occurrences == 1 && output.contains (marker ++ "(" ++ sign answer ++ "))") do
        throw (IO.userError ("wrong sign or multiplicity: " ++ p.label))
  IO.println s!"Named HOL module: {probes.length} complete tcalc/frame comparisons passed"

open Mettapedia.Languages.OpenTheory Mettapedia.GSLT.LanguageDef
open FirstOrder InferenceChecker NativePremiseCompilation

private def portable (root : System.FilePath) : IO Unit := do
  let doc ← IO.FS.readFile (root / "metta/native_inference/HOLLightKernel.module")
  unless doc.trimAscii == (kernelModule []).trimAscii do throw (IO.userError "different portable HOL package")
  let some d := ModuleFormat.Portable.readValidatedCalculus? doc | throw (IO.userError "portable module refused")
  let t := DBTerm.free ⟨.global "p", .bool⟩
  let term := groundP (encodeTerm t)
  let bool := groundP (encodeTy .bool)
  let refl : RuleInstance := ⟨⟨"hol.refl"⟩, [term, bool]⟩
  let conclusion := thmJ (contextP []) (equalityTermP bool term term)
  unless instantiateRule? d refl == some ([typeOfJ (contextP []) term bool], conclusion) &&
      compile d (NativePremises.typeOf [] t) refl == some ([], conclusion) &&
      compile d (NativePremises.typeOf [] (.bound 0)) refl == instantiateRule? d refl do
    throw (IO.userError "REFL lost its source conclusion, premise or fallback")
  let some schema := d.1.lookupRule? refl.ruleId | throw (IO.userError "missing REFL schema")
  let some emitted := NativePremises.activation d (NativePremises.typeOf [] t)
        (.inl refl.ruleId) (.inl refl.arguments) | throw (IO.userError "REFL failed to emit")
  let ticket := Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSchemaActivation.request
    refl.ruleId schema refl.arguments
  let output := Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSchemaActivation.judgment conclusion
  unless emitted.take == [(.requests, ticket)] && emitted.read.isEmpty &&
      emitted.produce == [(.judgments, output)] do throw (IO.userError "wrong protected firing layout")
  if checkRaw d conclusion (.node refl []) then throw (IO.userError "erased proof was accepted as a source receipt")
  let bad := groundP (encodeTerm (.bound 0))
  let rejected : RuleInstance := ⟨⟨"hol.refl"⟩, [bad, bool]⟩
  unless (instantiateRule? d rejected).isSome &&
      (compile d (NativePremises.typeOf [] (.bound 0)) rejected).isNone do
    throw (IO.userError "out-of-scope index accepted")
  let body := SourceSubstitution.Controls.collisionSource.toDB []
  let entries := SourceSubstitution.Controls.identifyTypes
  let decideInst := NativePremises.instType entries body
  let ask (out : DBTerm) := termTyActJ (typeMapletsP entries) (groundP (encodeTerm body)) (groundP (encodeTerm out))
  unless decideInst (ask (SourceSubstitution.Controls.collisionSafe.toDB [])) == some true &&
      decideInst (ask (SourceSubstitution.Controls.collisionCaptured.toDB [])) == some false do
    throw (IO.userError "type instantiation captured a free variable")
  IO.println "Portable HOL module: REFL premise, fallback, scope and INST_TYPE collision controls passed"

def main (args : List String) : IO Unit := do
  let [root, cetta] := args | throw (IO.userError "expected Mettapedia and CeTTa checkout roots")
  let root ← IO.FS.realPath root
  let cetta ← IO.FS.realPath cetta
  portable root
  IO.FS.withTempDir (named root cetta)
