import Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTa

/-! Run the same finite input through the contextual solver and a selected
CeTTa executable. The printer below is for these generated specimens. -/

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTa.Query

namespace Specimens
def index {Γ : List Unit} {s} : Var Γ s → Nat
  | .zero => 0
  | .succ v => index v + 1

def variableName (v : Name mkeys) : String :=
  let path := fun (p : List Nat) => String.intercalate "_" (p.map toString)
  s!"$v{path v.scopes}s{path v.key.site}i{v.key.index}"

mutual
def emit {Γ s} : Term (signature MSig (fam mkeys)) Γ s → String
  | .var v => s!"(idx {index v})"
  | .op (.inl (.sym s)) _ => s
  | .op (.inl (.num n)) _ => toString n
  | .op (.inl (.tup _)) xs => s!"({String.intercalate " " (args xs)})"
  | .op (.inl .hold) (.cons t .nil) => s!"(hold {emit t})"
  | .op (.inl .run) (.cons t .nil) => s!"(run {emit t})"
  | .op (.inl .lam) (.cons t .nil) => s!"(lam {emit t})"
  | .op (.inr (.mk x)) xs =>
    let name := variableName x
    if x.key.arity.1.isEmpty then name else s!"(ctx {name} {String.intercalate " " (args xs)})"
def args {Γ arities} : Args (signature MSig (fam mkeys)) arities Γ → List String
  | .nil => []
  | .cons head tail => emit head :: args tail
end

def check (bin profile source : String) (want : List String) (wait := false) : IO Unit := do
  let output ← IO.Process.output {cmd := bin, args := #["--lang", "tmetta", "--profile", profile, "--expr", source]}
  let actual := output.stdout.trimAscii.toString
  unless (if wait then output.exitCode != 0 && output.stderr.contains "suspended" else output.exitCode == 0) &&
      actual == String.intercalate "\n" want do
    throw <| IO.userError s!"{profile}: {source}\nexpected {want}, observed {actual}\n{output.stderr}"

def counts (bin profile : String) (cs : List Clause) (rows : List (Row mkeys [] ())) : IO Unit := do
  let request := Edges.q Edges.x
  let heads := cs.map fun e => s!"(= {emit e.lhs} (match &self {emit e.pattern} {emit e.template}))"
  let facts := rows.map fun r => emit r.atom
  let mut checks := [s!"!(count (reify {emit request}))"]
  let mut stores := [[]]
  for v in ["a", "b", "z"] do
    checks := checks ++ [s!"!(let $s (reify {emit request}) (count (reify (chain (unify {emit Edges.x} {v}) $_ (reflect $s)))))"]
    stores := stores ++ [[(Edges.x, sym v)]]
  let expected ← stores.mapM fun store => do
    let some n := countAt cs rows request 16 store | throw <| IO.userError "unfinished Lean count"
    return s!"[{n}]"
  check bin profile (String.intercalate "\n" (facts ++ heads ++ checks)) expected

def storedCapture (bin profile : String) : IO Unit := do
  let row := CapturedRow.row
  let store := NativeQuery.MatchKernel.Opened.rowEquations (openStoredRow 5 row) (sym "red")
  let mut source := s!"!(add-atom &self {emit row.atom})"
  let mut expected := ["[()]"]
  for color in ["blue", "red"] do
    let candidate := NativeQuery.MatchKernel.Opened.rowEquations (openStoredRow 6 row) (sym color)
    let result := solve 16 (store ++ candidate)
    unless ContextualQueryAnswers.closed result do
      throw <| IO.userError s!"unfinished Lean read of {color}"
    source := source ++ s!" !(count (reify (chain (match &self red seen) $_ (match &self {color} seen))))"
    expected := expected ++ [if ContextualQueryAnswers.successful result then "[1]" else "[0]"]
  check bin profile source expected

def effectOrder (bin profile : String) (first : Bool) : IO Unit := do
  let label := fun bit : Bool => if bit then "b" else "a"
  let firstRows := (Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTa.Publication.RemoveAndCount.afterOne first).present.card
  let lastRows := (Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTa.Publication.RemoveAndCount.afterBoth first).present.card
  let source := s!"!(bind! &s (new-space)) !(add-atom &s {label (!first)}) !(add-atom &s {label first}) " ++
    "!(let $t (match &s $x (chain (remove-atom &s $x) $_ " ++
    "  (let $n (count (reify (match &s $row $row))) (Pair $x $n)))) (run $t)) " ++
    "!(count (reify (match &s $row $row)))"
  check bin profile source ["[()]", "[()]", "[()]",
    s!"[(Pair {label first} {firstRows}), (Pair {label (!first)} {lastRows})]", s!"[{lastRows}]"]

def binder (bin profile : String) (l r : MData) (outside : Option (Option Bool) := none) : IO Unit := do
  let store := [(l, r)]
  let logical := solve 24 store
  let native := NativeSolver.attempt 24 (ContextualResidual.observeProblem store)
  let done_ := ContextualQueryAnswers.closed native
  let expected := if done_ then [if ContextualQueryAnswers.successful native then "[1]" else "[0]"] else []
  let source := s!"!(count (reify (unify {emit l} {emit r})))"
  match outside with
  | none =>
    unless done_ = ContextualQueryAnswers.closed logical &&
        ContextualQueryAnswers.successful native = ContextualQueryAnswers.successful logical do
      throw <| IO.userError s!"solver policies disagree on completed work for {source}"
    check bin profile source expected (!done_)
  | some recorded =>
    if ContextualPatternFragment.check l && ContextualPatternFragment.check r then
      throw <| IO.userError "expected a non-pattern input"
    let logicalStatus := if ContextualQueryAnswers.closed logical
      then some (ContextualQueryAnswers.successful logical) else none
    unless logicalStatus = recorded && !done_ do
      throw <| IO.userError s!"expected full residual under native policy for {source}"
    check bin profile source expected (!done_)

def lam {Γ : Ctx MSig} (t : Term (signature MSig (fam mkeys)) (() :: Γ) ()) :
    Term (signature MSig (fam mkeys)) Γ () := .op (.inl .lam) (.cons t .nil)

def openedRows (bin profile : String) : IO Unit := do
  let schematic := lam (tupleAt [symAt "Pair", bv, .op (.inr (.mk (fo [] [0] 0))) .nil])
  let row : Row mkeys [] () := ⟨schematic, []⟩
  let red := lam (tupleAt [symAt "Pair", bv, symAt "red"])
  let blue := lam (tupleAt [symAt "Pair", bv, symAt "blue"])
  let wrong := lam (tupleAt [symAt "Pair", symAt "free", symAt "red"])
  let rows := [row, row]
  let first := rows.zipIdx.map fun (stored, slot) =>
    NativeQuery.MatchKernel.Opened.rowEquations (openStoredRow (slot + 1) stored) red
  let next := fun pattern => rows.zipIdx.map fun (stored, slot) =>
    NativeQuery.MatchKernel.Opened.rowEquations (openStoredRow (slot + 3) stored) pattern
  let candidates := first.flatMap fun k => (next blue).map (k ++ ·)
  let count (stores : List (List (Constraint mkeys [] ()))) : IO Nat := do
    let mut n : Nat := 0
    for k in stores do
      let result := solve 16 k
      unless ContextualQueryAnswers.closed result do
        throw <| IO.userError "unfinished schematic read"
      if ContextualQueryAnswers.successful result then n := n + 1
    return n
  let n ← count candidates
  let m ← count (next wrong)
  check bin profile (String.intercalate "\n" ((rows.map fun r => emit r.atom) ++
    [s!"!(count (reify (chain (match &self {emit red} seen) $_ (match &self {emit blue} seen))))",
     s!"!(count (reify (match &self {emit wrong} seen)))"])) [s!"[{n}]", s!"[{m}]"]

def binary {Γ : Ctx MSig} (a b : Term (signature MSig (fam mkeys)) Γ ()) :
    Term (signature MSig (fam mkeys)) Γ () :=
  .op (.inr (.mk ⟨[], ⟨[4], 0, ([(), ()], ())⟩⟩)) (.cons a (.cons b .nil))

def mixedResidual (bin profile : String) (retained resolvable left right : MData) : IO Unit := do
  let tag := foD [] [17] 0
  let past := ContextualResidual.observeProblem [(retained, left), (tag, sym "kept")]
  let initial := NativeSolver.attempt 24 past
  if ContextualQueryAnswers.closed initial then throw <| IO.userError "lost the open equation"
  for supplied in [left, right] do
    let resumed := NativeSolver.resume initial 24 (ContextualResidual.observeProblem [(resolvable, supplied)])
    unless ContextualQueryAnswers.closed resumed do throw <| IO.userError "supplied closure did not settle"
    let expected := if ContextualQueryAnswers.successful resumed then ["[kept]"] else []
    let a := tuple [sym "Pair", retained, tag, resolvable]
    let b := tuple [sym "Pair", left, sym "kept", supplied]
    -- Expose the independent binding after the conjunction's decision.
    let source := s!"!(chain (unify {emit a} {emit b}) $_ {emit tag})"
    check bin profile source expected

def suite (bin : String) : IO Unit := do
  let at0 := (Term.var .zero : Term (signature MSig (fam mkeys)) [(), ()] ())
  let at1 := (Term.var (.succ .zero) : Term (signature MSig (fam mkeys)) [(), ()] ())
  for profile in ["native", "eager"] do
    for cs in [[Edges.clause], Edges.clauses] do
      for facts in [[], [Edges.fact], Edges.facts, [Edges.fact, ⟨Edges.edge (sym "z") (sym "b"), []⟩]] do
        counts bin profile cs facts
    storedCapture bin profile
    openedRows bin profile
    effectOrder bin profile false
    effectOrder bin profile true
    binder bin profile (lam (lam (binary at1 at0))) (lam (lam (tupleAt [symAt "Pair", at0, at1])))
    binder bin profile (lam (lam (hoD [] [4] 0 at0))) (lam (lam at1))
    binder bin profile (lam (lam (binary at0 at0))) (lam (lam (symAt "z"))) (some (some true))
    binder bin profile (lam (lam (binary (tupleAt [symAt "Pair", at1]) at0))) (lam (lam (symAt "z"))) (some none)
    mixedResidual bin profile (lam (lam (binary at0 at0))) (lam (lam (binary at1 at0)))
      (lam (lam (symAt "z"))) (lam (lam (symAt "different")))
    for depth in [1, 2, 5, 48] do
      let e := (List.range depth).foldl (fun e _ => s!"(reify {e})") "(empty)"
      check bin profile s!"!(count {e})" [if depth = 1 then "[0]" else "[1]"]
    check bin profile "!(quote (+ 1 2))" ["[(+ 1 2)]"]
    check bin profile "!(run $x)" [] true
    check bin profile "!(chain (unify $x 7) $_ (run $x))" ["[7]"]
  IO.println "PASS: scoped query observations, effects, activation and contextual residuals in both presets"
end Specimens

def main (argv : List String) : IO Unit := do
  let [bin] := argv | throw <| IO.userError "supply the path to the cetta executable"
  Specimens.suite bin
