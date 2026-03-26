import Algorithms.MeTTa.Eval.Core

/-! # LeanPeTTa Evaluator

Non-partial, fuel-indexed evaluator with special forms.
Fuel is spent at each `evalWith` dispatch — sub-evaluations within
special forms and ordinary calls share the decremented budget.
-/

namespace Algorithms.MeTTa.Eval

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match hiding applyBindings

-- ═════════════════════════════════════════════════════════════════════════
-- DISPATCH
-- ═════════════════════════════════════════════════════════════════════════

@[reducible] def dispatch : Pattern → Dispatch
  | .apply "superpose" args => .special .superpose args
  | .apply "collapse" args  => .special .collapse args
  | .apply "let" args       => .special .let_ args
  | .apply "let*" args      => .special .letStar args
  | .apply "if" args        => .special .if_ args
  | .apply "case" args      => .special .case_ args
  | .apply "match" args     => .special .match_ args
  | .apply "once" args      => .special .once args
  | .apply "catch" args     => .special .catch args
  | .apply "chain" args     => .special .chain args
  | .apply "progn" args     => .special .progn args
  | .apply "prog1" args     => .special .prog1 args
  | .apply ctor args        => .ordinary ctor args
  | _                       => .atom

-- ═════════════════════════════════════════════════════════════════════════
-- HEADSTEP? — pure operators on evaluated args
-- ═════════════════════════════════════════════════════════════════════════

def headStep? (s : Session) (binds : Bindings) (ctor : String)
    (args : List Pattern) : Option EvalOut :=
  match ctor, args with
  | "+", [a, b] => do
    let x ← Pattern.toInt? a; let y ← Pattern.toInt? b
    pure ⟨s, [⟨Pattern.ofInt (x + y), binds⟩], false⟩
  | "-", [a, b] => do
    let x ← Pattern.toInt? a; let y ← Pattern.toInt? b
    pure ⟨s, [⟨Pattern.ofInt (x - y), binds⟩], false⟩
  | "*", [a, b] => do
    let x ← Pattern.toInt? a; let y ← Pattern.toInt? b
    pure ⟨s, [⟨Pattern.ofInt (x * y), binds⟩], false⟩
  | "<", [a, b] => do
    let x ← Pattern.toInt? a; let y ← Pattern.toInt? b
    pure ⟨s, [⟨Pattern.ofBool (decide (x < y)), binds⟩], false⟩
  | ">", [a, b] => do
    let x ← Pattern.toInt? a; let y ← Pattern.toInt? b
    pure ⟨s, [⟨Pattern.ofBool (decide (x > y)), binds⟩], false⟩
  | "<=", [a, b] => do
    let x ← Pattern.toInt? a; let y ← Pattern.toInt? b
    pure ⟨s, [⟨Pattern.ofBool (decide (x ≤ y)), binds⟩], false⟩
  | ">=", [a, b] => do
    let x ← Pattern.toInt? a; let y ← Pattern.toInt? b
    pure ⟨s, [⟨Pattern.ofBool (decide (x ≥ y)), binds⟩], false⟩
  | "==", [a, b] =>
    some ⟨s, [⟨Pattern.ofBool (a == b), binds⟩], false⟩
  | "not", [a] =>
    some ⟨s, [⟨Pattern.ofBool !(a == .apply "True" []), binds⟩], false⟩
  | "car-atom", [.apply _ (hd :: _)] =>
    some ⟨s, [⟨hd, binds⟩], false⟩
  | "cdr-atom", [.apply c (_ :: tl)] =>
    some ⟨s, [⟨.apply c tl, binds⟩], false⟩
  | "cons-atom", [hd, .apply c tl] =>
    some ⟨s, [⟨.apply c (hd :: tl), binds⟩], false⟩
  -- Space ops
  | "add-atom", [_, atom] =>
    some ⟨{ s with space := atom :: s.space }, [⟨.apply "()" [], binds⟩], false⟩
  | "remove-atom", [_, atom] =>
    let space' := s.space.filter (· != atom)
    some ⟨{ s with space := space' }, [⟨.apply "()" [], binds⟩], false⟩
  | "get-atoms", [_] =>
    let atoms := s.space.map (fun a => ⟨a, binds⟩)
    some ⟨s, atoms, false⟩
  | _, _ => none

-- ═════════════════════════════════════════════════════════════════════════
-- EVALTUPLE (Phase 1)
-- ═════════════════════════════════════════════════════════════════════════

def evalTuple (cb : EvalCallback) (s : Session) (binds : Bindings)
    (args : List Pattern) : TupleOut :=
  match args with
  | [] => ⟨s, [[]], false⟩
  | arg :: rest =>
    let argOut := cb s binds arg
    let restOut := evalTuple cb argOut.s binds rest
    let combos := argOut.results.flatMap (fun r =>
      restOut.combos.map (fun rc => r :: rc))
    ⟨restOut.s, combos, argOut.cut || restOut.cut⟩

-- ═════════════════════════════════════════════════════════════════════════
-- RUNORDINARY — evalTuple + headStep?
-- ═════════════════════════════════════════════════════════════════════════

-- ─── Equation rewriting ─────────────────────────────────────────────────

/-- Try matching a term against rules, returning substituted RHS if matched. -/
private def tryRules (s : Session) (term : Pattern) : Option Pattern :=
  s.rules.findSome? fun rule =>
    (matchPattern rule.left term).head?.map (fun newBinds => applyBinds newBinds rule.right)

-- ═════════════════════════════════════════════════════════════════════════
-- RUNORDINARY — evalTuple + headStep? + equation rewriting
-- ═════════════════════════════════════════════════════════════════════════

/-- All-eager evaluation: evaluate all args, try headStep?, try rules, or normal form. -/
def runOrdinary (cb : EvalCallback) (s : Session) (binds : Bindings)
    (ctor : String) (args : List Pattern) : EvalOut :=
  let tupleOut := evalTuple cb s binds args
  let (finalS, results, cut) := tupleOut.combos.foldl
    (fun (acc : Session × List ResultBind × Bool) combo =>
      let (s', rs, cut) := acc
      let evaledArgs := combo.map ResultBind.term
      let term := Pattern.apply ctor evaledArgs
      match headStep? s' binds ctor evaledArgs with
      | some out => (out.s, rs ++ out.results, cut || out.cut)
      | none =>
        -- Try equation rewriting
        match tryRules s' term with
        | some rhs =>
          let rhsOut := cb s' binds rhs
          (rhsOut.s, rs ++ rhsOut.results, cut || rhsOut.cut)
        | none => (s', rs ++ [⟨term, binds⟩], cut))
    (tupleOut.s, [], tupleOut.cut)
  ⟨finalS, results, cut⟩

-- ═════════════════════════════════════════════════════════════════════════
-- SPECIAL FORM IMPLEMENTATIONS
-- ═════════════════════════════════════════════════════════════════════════

-- ─── superpose: fan out elements ────────────────────────────────────────

private def runSuperpose (cb : EvalCallback) (s : Session) (binds : Bindings)
    (args : List Pattern) : EvalOut :=
  match args with
  | [expr] =>
    let elems := exprElems expr
    let results := elems.foldl (fun (acc : Session × List ResultBind × Bool) elem =>
      let (s', rs, cut) := acc
      let out := cb s' binds elem
      (out.s, rs ++ out.results, cut || out.cut)) (s, [], false)
    ⟨results.1, results.2.1, results.2.2⟩
  | _ => ⟨s, [], false⟩

-- ─── collapse: collect all results into a tuple ─────────────────────────

private def runCollapse (cb : EvalCallback) (s : Session) (binds : Bindings)
    (args : List Pattern) : EvalOut :=
  match args with
  | [arg] =>
    let out := cb s binds arg
    let terms := out.results.map ResultBind.term
    ⟨out.s, [⟨mkExpr terms, binds⟩], out.cut⟩
  | _ => ⟨s, [], false⟩

-- ─── if: conditional branching ──────────────────────────────────────────

private def runIf (cb : EvalCallback) (s : Session) (binds : Bindings)
    (args : List Pattern) : EvalOut :=
  match args with
  | [cond, thenBr, elseBr] =>
    let condOut := cb s binds cond
    match condOut.results with
    | [] => ⟨condOut.s, [], condOut.cut⟩
    | r :: _ =>
      let brOut := if isTruthy r.term then cb condOut.s binds thenBr
                   else cb condOut.s binds elseBr
      ⟨brOut.s, brOut.results, condOut.cut || brOut.cut⟩
  | [cond, thenBr] =>
    let condOut := cb s binds cond
    match condOut.results with
    | [] => ⟨condOut.s, [], condOut.cut⟩
    | r :: _ =>
      if isTruthy r.term then
        let brOut := cb condOut.s binds thenBr
        ⟨brOut.s, brOut.results, condOut.cut || brOut.cut⟩
      else ⟨condOut.s, [], condOut.cut⟩
  | _ => ⟨s, [], false⟩

-- ─── let: single binding ────────────────────────────────────────────────

private def runLet (cb : EvalCallback) (s : Session) (binds : Bindings)
    (args : List Pattern) : EvalOut :=
  match args with
  | [pat, val, body] =>
    let valOut := cb s binds val
    let results := valOut.results.foldl (fun (acc : Session × List ResultBind × Bool) r =>
      let (s', rs, cut) := acc
      (matchPattern pat r.term).foldl (fun (acc2 : Session × List ResultBind × Bool) newBinds =>
        let (s2, rs2, cut2) := acc2
        match mergeBindings binds newBinds with
        | some merged =>
          let bodyOut := cb s2 merged body
          (bodyOut.s, rs2 ++ bodyOut.results, cut2 || bodyOut.cut)
        | none => (s2, rs2, cut2)) (s', rs, cut)
    ) (valOut.s, [], valOut.cut)
    ⟨results.1, results.2.1, results.2.2⟩
  | _ => ⟨s, [], false⟩

-- ─── let*: sequential bindings ──────────────────────────────────────────

private def runLetStarBindings (cb : EvalCallback) (s : Session) (binds : Bindings)
    (bindingList : List Pattern) (body : Pattern) : EvalOut :=
  match bindingList with
  | [] => cb s binds (applyBinds binds body)
  | (.apply _ [pat, val]) :: rest =>
    let valOut := cb s binds (applyBinds binds val)
    match valOut.results with
    | [] => ⟨valOut.s, [], valOut.cut⟩
    | r :: _ =>
      match (matchPattern pat r.term).head? with
      | some newBinds =>
        match mergeBindings binds newBinds with
        | some merged => runLetStarBindings cb valOut.s merged rest body
        | none => ⟨valOut.s, [], false⟩
      | none => ⟨valOut.s, [], false⟩
  | _ :: rest => runLetStarBindings cb s binds rest body

private def runLetStar (cb : EvalCallback) (s : Session) (binds : Bindings)
    (args : List Pattern) : EvalOut :=
  match args with
  | [.apply _ bindingList, body] => runLetStarBindings cb s binds bindingList body
  | _ => ⟨s, [], false⟩

-- ─── case: pattern match on key ─────────────────────────────────────────

private def runCaseBranches (cb : EvalCallback) (s : Session) (binds : Bindings)
    (key : Pattern) (branches : List Pattern) (priorCut : Bool) : EvalOut :=
  match branches with
  | [] => ⟨s, [], priorCut⟩
  | (.apply _ [pat, body]) :: rest =>
    match (matchPattern pat key).head? with
    | some newBinds =>
      match mergeBindings binds newBinds with
      | some merged =>
        let out := cb s merged body
        ⟨out.s, out.results, priorCut || out.cut⟩
      | none => runCaseBranches cb s binds key rest priorCut
    | none => runCaseBranches cb s binds key rest priorCut
  | _ :: rest => runCaseBranches cb s binds key rest priorCut

private def runCase (cb : EvalCallback) (s : Session) (binds : Bindings)
    (args : List Pattern) : EvalOut :=
  match args with
  | [key, branches] =>
    let keyOut := cb s binds key
    match keyOut.results with
    | [] => ⟨keyOut.s, [], keyOut.cut⟩
    | r :: _ => runCaseBranches cb keyOut.s binds r.term (exprElems branches) keyOut.cut
  | _ => ⟨s, [], false⟩

-- ─── match: pattern match against space ─────────────────────────────────

private def runMatch (cb : EvalCallback) (s : Session) (binds : Bindings)
    (args : List Pattern) : EvalOut :=
  match args with
  | [_space, pat, tmpl] =>
    let bindingSets := s.space.flatMap (fun atom => matchPattern pat atom)
    let instantiated := bindingSets.map (fun newBinds => applyBinds newBinds tmpl)
    let results := instantiated.foldl (fun (acc : Session × List ResultBind × Bool) inst =>
      let (s', rs, cut) := acc
      let out := cb s' binds inst
      (out.s, rs ++ out.results, cut || out.cut)) (s, [], false)
    ⟨results.1, results.2.1, results.2.2⟩
  | _ => ⟨s, [], false⟩

-- ─── once: take first result ────────────────────────────────────────────

private def runOnce (cb : EvalCallback) (s : Session) (binds : Bindings)
    (args : List Pattern) : EvalOut :=
  match args with
  | [arg] =>
    let out := cb s binds arg
    match out.results with
    | [] => ⟨out.s, [], out.cut⟩
    | r :: _ => ⟨out.s, [r], out.cut⟩
  | _ => ⟨s, [], false⟩

-- ─── catch: try-catch ───────────────────────────────────────────────────

private def runCatch (cb : EvalCallback) (s : Session) (binds : Bindings)
    (args : List Pattern) : EvalOut :=
  match args with
  | [expr, _handler, fallback] =>
    let out := cb s binds expr
    if out.results.isEmpty then
      let fbOut := cb out.s binds fallback
      ⟨fbOut.s, fbOut.results, out.cut || fbOut.cut⟩
    else out
  | [expr] => cb s binds expr
  | _ => ⟨s, [], false⟩

-- ─── chain: eval expr, bind each result, eval template ──────────────────

private def runChain (cb : EvalCallback) (s : Session) (binds : Bindings)
    (args : List Pattern) : EvalOut :=
  match args with
  | [expr, .fvar var, template] =>
    let exprOut := cb s binds expr
    let results := exprOut.results.foldl (fun (acc : Session × List ResultBind × Bool) r =>
      let (s', rs, cut) := acc
      match mergeBindings binds [(var, r.term)] with
      | some merged =>
        let bodyOut := cb s' merged template
        (bodyOut.s, rs ++ bodyOut.results, cut || bodyOut.cut)
      | none => (s', rs, cut)) (exprOut.s, [], exprOut.cut)
    ⟨results.1, results.2.1, results.2.2⟩
  | _ => ⟨s, [], false⟩

-- ─── progn: eval all, return last ───────────────────────────────────────

private def runProgn (cb : EvalCallback) (s : Session) (binds : Bindings)
    (args : List Pattern) (priorCut : Bool := false) : EvalOut :=
  match args with
  | [] => ⟨s, [⟨.apply "()" [], binds⟩], priorCut⟩
  | [last] =>
    let out := cb s binds last
    ⟨out.s, out.results, priorCut || out.cut⟩
  | expr :: rest =>
    let out := cb s binds expr
    runProgn cb out.s binds rest (priorCut || out.cut)

-- ─── prog1: eval all, return first ──────────────────────────────────────

private def runProg1 (cb : EvalCallback) (s : Session) (binds : Bindings)
    (args : List Pattern) : EvalOut :=
  match args with
  | [] => ⟨s, [⟨.apply "()" [], binds⟩], false⟩
  | first :: rest =>
    let firstOut := cb s binds first
    let (finalS, cutAcc) := rest.foldl (fun (acc : Session × Bool) expr =>
      let (s', cut) := acc
      let out := cb s' binds expr
      (out.s, cut || out.cut)) (firstOut.s, firstOut.cut)
    ⟨finalS, firstOut.results, cutAcc⟩

-- ═════════════════════════════════════════════════════════════════════════
-- RUNSPECIAL — dispatcher for all special forms
-- ═════════════════════════════════════════════════════════════════════════

def runSpecial (cb : EvalCallback) (s : Session) (binds : Bindings)
    (sf : SpecialForm) (args : List Pattern) : EvalOut :=
  match sf with
  | .superpose => runSuperpose cb s binds args
  | .collapse  => runCollapse cb s binds args
  | .if_       => runIf cb s binds args
  | .let_      => runLet cb s binds args
  | .letStar   => runLetStar cb s binds args
  | .case_     => runCase cb s binds args
  | .match_    => runMatch cb s binds args
  | .once      => runOnce cb s binds args
  | .catch     => runCatch cb s binds args
  | .chain     => runChain cb s binds args
  | .progn     => runProgn cb s binds args
  | .prog1     => runProg1 cb s binds args

-- ═════════════════════════════════════════════════════════════════════════
-- EVALWITH — the verified evaluator
-- ═════════════════════════════════════════════════════════════════════════

def evalWith : Nat → EvalCallback
  | 0 => fun s _binds _t => ⟨s, [], true⟩
  | n + 1 => fun s binds t =>
    match dispatch t with
    | .atom => ⟨s, [⟨resolveVar binds t, binds⟩], false⟩
    | .special sf args => runSpecial (evalWith n) s binds sf args
    | .ordinary ctor args => runOrdinary (evalWith n) s binds ctor args

def eval (fuel : Nat) (s : Session) (t : Pattern) : EvalOut :=
  evalWith fuel s [] t

end Algorithms.MeTTa.Eval
