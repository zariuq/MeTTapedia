import MeTTailCore
import Algorithms.MeTTa.Simple.Relations

namespace Algorithms.MeTTa.Simple.Semantics.StateEffects

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match

structure Interface (σ : Type) where
  eval : σ → Pattern → σ × List Pattern
  snapshot : σ → σ
  isFailure : Pattern → Bool
  truePattern : Pattern
  getStateCells : σ → List (String × Pattern)
  withStateCells : σ → List (String × Pattern) → σ

structure Preservation (I : Interface σ) (P : σ → Prop) where
  eval_preserves :
    ∀ {s : σ} {term : Pattern} {s' : σ} {out : List Pattern},
      I.eval s term = (s', out) →
      P s → P s'
  snapshot_preserves :
    ∀ {s : σ},
      P s → P (I.snapshot s)
  withStateCells_preserves :
    ∀ {s : σ} {cells : List (String × Pattern)},
      P s → P (I.withStateCells s cells)

private def stateKey? : Pattern → Option String
  | .apply ctor [] =>
      let k := ctor.trimAscii.toString
      if k.isEmpty then none else some k
  | .fvar v =>
      let k := v.trimAscii.toString
      if k.isEmpty then none else some k
  | _ => none

private def lookupState (cells : List (String × Pattern)) (k : String) : Option Pattern :=
  (cells.find? (fun kv => kv.1 == k)).map Prod.snd

private def isNumberAtom : Pattern → Bool
  | p =>
      match Algorithms.MeTTa.Simple.intOfPattern? p with
      | some _ => true
      | none =>
          match Algorithms.MeTTa.Simple.floatOfPattern? p with
          | some _ => true
          | none => false

private def isQuotedStringAtom : Pattern → Bool
  | .apply tok [] =>
      let t := tok.trimAscii.toString
      t.startsWith "\"" && t.endsWith "\""
  | _ => false

private def simpleTypeName (p : Pattern) : String :=
  if isNumberAtom p then
    "Number"
  else if isQuotedStringAtom p then
    "String"
  else
    "Expression"

private def badArgTypeError (stateRef valueExpr : Pattern)
    (expectedTy gotTy : String) : Pattern :=
  .apply "Error"
    [ .apply "change-state!" [stateRef, valueExpr]
    , .apply "BadArgType"
        [ .apply "2" []
        , .apply expectedTy []
        , .apply gotTy []
        ]
    ]

private def upsertState (cells : List (String × Pattern)) (k : String) (v : Pattern) :
    List (String × Pattern) :=
  let without := cells.filter (fun kv => kv.1 != k)
  (k, v) :: without

private def setStateValue (I : Interface σ) (s : σ) (k : String) (v : Pattern) : σ :=
  I.withStateCells s (upsertState (I.getStateCells s) k v)

private def evalStateValue (I : Interface σ) (s : σ) (expr : Pattern) : σ × Pattern :=
  let (s1, out) := I.eval s expr
  (s1, out.headD expr)

private theorem evalStateValue_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (expr : Pattern) :
    P s → P (evalStateValue I s expr).1 := by
  intro hP
  unfold evalStateValue
  exact H.eval_preserves rfl hP

private def evalBindableValue (I : Interface σ) (s : σ) (valueExpr : Pattern) : σ × Pattern :=
  match valueExpr with
  | .apply "new-state" [init] => (s, init)
  | _ => evalStateValue I s valueExpr

private theorem evalBindableValue_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (valueExpr : Pattern) :
    P s → P (evalBindableValue I s valueExpr).1 := by
  intro hP
  cases valueExpr with
  | fvar x =>
      simpa [evalBindableValue] using evalStateValue_preserves I P H s (.fvar x) hP
  | bvar n =>
      simpa [evalBindableValue] using evalStateValue_preserves I P H s (.bvar n) hP
  | apply ctor args =>
      cases args with
      | nil =>
          simpa [evalBindableValue] using
            evalStateValue_preserves I P H s (.apply ctor []) hP
      | cons init rest =>
          cases rest with
          | nil =>
              by_cases hCtor : ctor = "new-state"
              · subst hCtor
                simpa [evalBindableValue] using hP
              · simpa [evalBindableValue, hCtor] using
                  evalStateValue_preserves I P H s (.apply ctor [init]) hP
          | cons x xs =>
              simpa [evalBindableValue] using
                evalStateValue_preserves I P H s (.apply ctor (init :: x :: xs)) hP
  | lambda body =>
      simpa [evalBindableValue] using evalStateValue_preserves I P H s (.lambda body) hP
  | multiLambda n body =>
      simpa [evalBindableValue] using
        evalStateValue_preserves I P H s (.multiLambda n body) hP
  | subst body repl =>
      simpa [evalBindableValue] using evalStateValue_preserves I P H s (.subst body repl) hP
  | collection ct elems rest =>
      simpa [evalBindableValue] using
        evalStateValue_preserves I P H s (.collection ct elems rest) hP

private def evalHyperposeStep (I : Interface σ)
    (st : σ × List Pattern) (term : Pattern) : σ × List Pattern :=
  let (s, accRev) := st
  let (s1, out0) := I.eval s term
  let out := if out0.isEmpty then [term] else out0
  let chosen := out.headD term
  (s1, chosen :: accRev)

private def evalHyperposeTerms (I : Interface σ) (s : σ)
    (terms : List Pattern) (accRev : List Pattern) : σ × List Pattern :=
  let st := terms.foldl (evalHyperposeStep I) (s, accRev)
  (st.1, st.2.reverse)

private theorem evalHyperposeStep_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (st : σ × List Pattern) (term : Pattern) :
    P st.1 → P (evalHyperposeStep I st term).1 := by
  intro hP
  unfold evalHyperposeStep
  cases st with
  | mk s accRev =>
      simpa using H.eval_preserves (s := s) (term := term) rfl hP

private theorem evalHyperposeFold_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (terms : List Pattern) (st : σ × List Pattern) :
    P st.1 → P ((terms.foldl (evalHyperposeStep I) st).1) := by
  intro hP
  induction terms generalizing st with
  | nil =>
      simpa
  | cons term rest ih =>
      have hStep : P (evalHyperposeStep I st term).1 :=
        evalHyperposeStep_preserves I P H st term hP
      simpa [List.foldl] using ih (evalHyperposeStep I st term) hStep

private theorem evalHyperposeTerms_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (terms : List Pattern) (accRev : List Pattern) :
    P s → P (evalHyperposeTerms I s terms accRev).1 := by
  intro hP
  unfold evalHyperposeTerms
  exact evalHyperposeFold_preserves I P H terms (s, accRev) hP

private def evalBind (I : Interface σ) (s : σ) (stateRef valueExpr : Pattern) : σ × List Pattern :=
  match stateKey? stateRef with
  | none => (s, [])
  | some k =>
      let (s1, v) := evalBindableValue I s valueExpr
      let s2 := setStateValue I s1 k v
      (s2, [I.truePattern])

private theorem evalBind_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (stateRef valueExpr : Pattern) :
    P s → P (evalBind I s stateRef valueExpr).1 := by
  intro hP
  unfold evalBind
  cases hKey : stateKey? stateRef with
  | none =>
      simpa [hKey] using hP
  | some k =>
      have hVal : P (evalBindableValue I s valueExpr).1 :=
        evalBindableValue_preserves I P H s valueExpr hP
      cases hStep : evalBindableValue I s valueExpr with
      | mk s1 v =>
          have hS1 : P s1 := by
            simpa [hStep] using hVal
          have hSet :
              P (I.withStateCells s1 (upsertState (I.getStateCells s1) k v)) :=
            H.withStateCells_preserves hS1
          simpa [setStateValue, hKey, hStep] using hSet

private def evalChangeState (I : Interface σ) (s : σ) (stateRef valueExpr : Pattern) :
    σ × List Pattern :=
  match stateKey? stateRef with
  | none => (s, [])
  | some k =>
      let (s1, v) := evalStateValue I s valueExpr
      match lookupState (I.getStateCells s1) k with
      | some old =>
          let expectedTy := simpleTypeName old
          let gotTy := simpleTypeName v
          if expectedTy != gotTy &&
              (expectedTy == "Number" || expectedTy == "String") then
            let err := badArgTypeError stateRef valueExpr expectedTy gotTy
            (s1, [err])
          else
            let s2 := setStateValue I s1 k v
            (s2, [I.truePattern])
      | none =>
          let s2 := setStateValue I s1 k v
          (s2, [I.truePattern])

private theorem evalChangeState_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (stateRef valueExpr : Pattern) :
    P s → P (evalChangeState I s stateRef valueExpr).1 := by
  intro hP
  unfold evalChangeState
  cases hKey : stateKey? stateRef with
  | none =>
      simpa [hKey] using hP
  | some k =>
      have hEval : P (evalStateValue I s valueExpr).1 :=
        evalStateValue_preserves I P H s valueExpr hP
      cases hStep : evalStateValue I s valueExpr with
      | mk s1 v =>
          have hS1 : P s1 := by
            simpa [hStep] using hEval
          cases hLookup : lookupState (I.getStateCells s1) k with
          | none =>
              have hSet :
                  P (I.withStateCells s1 (upsertState (I.getStateCells s1) k v)) :=
                H.withStateCells_preserves hS1
              simpa [setStateValue, hKey, hStep, hLookup] using hSet
          | some old =>
              by_cases hBad :
                  simpleTypeName old != simpleTypeName v &&
                    (simpleTypeName old == "Number" || simpleTypeName old == "String")
              · simpa [hKey, hStep, hLookup, hBad] using hS1
              · have hSet :
                    P (I.withStateCells s1 (upsertState (I.getStateCells s1) k v)) :=
                  H.withStateCells_preserves hS1
                simpa [setStateValue, hKey, hStep, hLookup, hBad] using hSet

private def evalGetState (I : Interface σ) (s : σ) (stateRef : Pattern) : σ × List Pattern :=
  match stateKey? stateRef with
  | none => (s, [])
  | some k =>
      match lookupState (I.getStateCells s) k with
      | some v => (s, [v])
      | none => (s, [])

private theorem evalGetState_preserves
    (I : Interface σ) (P : σ → Prop) (s : σ) (stateRef : Pattern) :
    P s → P (evalGetState I s stateRef).1 := by
  intro hP
  unfold evalGetState
  cases hKey : stateKey? stateRef with
  | none =>
      simpa [hKey] using hP
  | some k =>
      cases hLookup : lookupState (I.getStateCells s) k with
      | none =>
          simpa [hKey, hLookup] using hP
      | some v =>
          simpa [hKey, hLookup] using hP

private def evalWithMutex (I : Interface σ) (s : σ) (body : Pattern) : σ × List Pattern :=
  let (s1, out) := I.eval s body
  let out' := if out.isEmpty then [body] else out
  (s1, out')

private theorem evalWithMutex_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (body : Pattern) :
    P s → P (evalWithMutex I s body).1 := by
  intro hP
  unfold evalWithMutex
  exact H.eval_preserves rfl hP

private def evalTransaction (I : Interface σ) (s : σ) (body : Pattern) : σ × List Pattern :=
  let snap := I.snapshot s
  let (s1, out) := I.eval s body
  let hasFailure := out.any I.isFailure
  let committed := out.filter (fun p => !(I.isFailure p))
  if committed.isEmpty || hasFailure then
    (snap, [])
  else
    (s1, committed)

private theorem evalTransaction_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (body : Pattern) :
    P s → P (evalTransaction I s body).1 := by
  intro hP
  unfold evalTransaction
  have hEval : P (I.eval s body).1 := H.eval_preserves rfl hP
  cases hStep : I.eval s body with
  | mk s1 out =>
      have hSnap : P (I.snapshot s) := H.snapshot_preserves hP
      have hS1 : P s1 := by
        simpa [hStep] using hEval
      by_cases hFail : (List.filter (fun p => !I.isFailure p) out).isEmpty || out.any I.isFailure
      · simpa [hStep, hFail] using hSnap
      · simpa [hStep, hFail] using hS1

private def evalIntrinsicApply1 (I : Interface σ) (s : σ)
    (ctor : String) (arg : Pattern) : Option (σ × List Pattern) :=
  if ctor = "hyperpose" then
    let (s1, vals) := evalHyperposeTerms I s (tupleElems arg) []
    some (s1, [tupleOfElems vals])
  else if ctor = "get-state" then
    some (evalGetState I s arg)
  else if ctor = "transaction" then
    some (evalTransaction I s arg)
  else
    none

private theorem evalIntrinsicApply1_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (ctor : String) (arg : Pattern) :
    P s →
      match evalIntrinsicApply1 I s ctor arg with
      | some res => P res.1
      | none => True := by
  intro hP
  unfold evalIntrinsicApply1
  by_cases hHyper : ctor = "hyperpose"
  · subst hHyper
    simpa using evalHyperposeTerms_preserves I P H s (tupleElems arg) [] hP
  · by_cases hGet : ctor = "get-state"
    · subst hGet
      simpa using evalGetState_preserves I P s arg hP
    · by_cases hTxn : ctor = "transaction"
      · subst hTxn
        simpa using evalTransaction_preserves I P H s arg hP
      · simp [hHyper, hGet, hTxn]

private def evalIntrinsicApply2 (I : Interface σ) (s : σ)
    (ctor : String) (arg1 arg2 : Pattern) : Option (σ × List Pattern) :=
  if ctor = "bind!" then
    some (evalBind I s arg1 arg2)
  else if ctor = "change-state!" then
    some (evalChangeState I s arg1 arg2)
  else if ctor = "with_mutex" then
    some (evalWithMutex I s arg2)
  else
    none

private theorem evalIntrinsicApply2_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (ctor : String) (arg1 arg2 : Pattern) :
    P s →
      match evalIntrinsicApply2 I s ctor arg1 arg2 with
      | some res => P res.1
      | none => True := by
  intro hP
  unfold evalIntrinsicApply2
  by_cases hBind : ctor = "bind!"
  · subst hBind
    simpa using evalBind_preserves I P H s arg1 arg2 hP
  · by_cases hChange : ctor = "change-state!"
    · subst hChange
      simpa using evalChangeState_preserves I P H s arg1 arg2 hP
    · by_cases hMutex : ctor = "with_mutex"
      · subst hMutex
        simpa using evalWithMutex_preserves I P H s arg2 hP
      · simp [hBind, hChange, hMutex]

def evalIntrinsic (I : Interface σ) (s : σ) (term : Pattern) : Option (σ × List Pattern) :=
  match term with
  | .apply ctor [arg] =>
      evalIntrinsicApply1 I s ctor arg
  | .apply ctor [arg1, arg2] =>
      evalIntrinsicApply2 I s ctor arg1 arg2
  | _ => none

/-- The set of heads handled by `StateEffects.evalIntrinsic`. -/
def evalIntrinsicSpecialHeads : List String :=
  ["hyperpose", "get-state", "transaction", "bind!", "change-state!", "with_mutex"]

/-- For ctors NOT in the special-head set, `evalIntrinsic` returns `none`. -/
theorem evalIntrinsic_none_of_nonSpecial
    (I : Interface σ) (s : σ) (ctor : String) (args : List Pattern)
    (hNotSpecial : ctor ∉ evalIntrinsicSpecialHeads) :
    evalIntrinsic I s (.apply ctor args) = none := by
  simp only [evalIntrinsicSpecialHeads, List.mem_cons, List.not_mem_nil, not_or,
    not_false_eq_true] at hNotSpecial
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hNotSpecial
  unfold evalIntrinsic
  -- evalIntrinsic dispatches by arity: 1-arg → evalIntrinsicApply1, 2-arg → evalIntrinsicApply2
  -- For any arity, if ctor not in special set → none
  cases args with
  | nil => simp
  | cons a rest =>
    cases rest with
    | nil => simp [evalIntrinsicApply1, h1, h2, h3]
    | cons b rest2 =>
      cases rest2 with
      | nil => simp [evalIntrinsicApply2, h4, h5, h6]
      | cons => simp

theorem evalIntrinsic_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (term : Pattern) :
    P s →
      match evalIntrinsic I s term with
      | some res => P res.1
      | none => True := by
  intro hP
  cases term with
  | fvar x =>
      simp [evalIntrinsic]
  | bvar n =>
      simp [evalIntrinsic]
  | lambda body =>
      simp [evalIntrinsic]
  | multiLambda n body =>
      simp [evalIntrinsic]
  | subst body repl =>
      simp [evalIntrinsic]
  | collection ct elems rest =>
      simp [evalIntrinsic]
  | apply ctor args =>
      cases args with
      | nil =>
          simp [evalIntrinsic]
      | cons a rest =>
          cases rest with
          | nil =>
              simpa [evalIntrinsic] using
                evalIntrinsicApply1_preserves I P H s ctor a hP
          | cons b rest' =>
              cases rest' with
              | nil =>
                  simpa [evalIntrinsic] using
                    evalIntrinsicApply2_preserves I P H s ctor a b hP
              | cons c cs =>
                  simp [evalIntrinsic]

end Algorithms.MeTTa.Simple.Semantics.StateEffects
