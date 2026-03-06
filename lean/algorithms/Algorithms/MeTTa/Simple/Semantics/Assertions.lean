import MeTTailCore
import Algorithms.MeTTa.Simple.Relations

namespace Algorithms.MeTTa.Simple.Semantics.Assertions

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match

inductive AssertEqualMode where
  | multiset
  | ordered
deriving Repr, DecidableEq

inductive AssertionResultStyle where
  | boolean
  | unitError
deriving Repr, DecidableEq

structure Policy where
  assertEqualMode : AssertEqualMode := .multiset
  resultStyle : AssertionResultStyle := .boolean
  tupleFallback : Bool := true
  emptyTupleMatchesEmpty : Bool := true
deriving Repr, DecidableEq

structure Interface (σ : Type) where
  eval : σ → Pattern → σ × List Pattern
  normalizeStrictValue : σ → Pattern → σ × Pattern
  noteEval : σ → σ
  withMessage : σ → String → σ
  noteError : σ → String → σ
  renderPattern : Pattern → String
  trueAtom : Pattern := .apply "True" []
  falseAtom : Pattern := .apply "False" []

structure Preservation (I : Interface σ) (P : σ → Prop) where
  eval_preserves :
    ∀ {s : σ} {term : Pattern} {s' : σ} {out : List Pattern},
      I.eval s term = (s', out) → P s → P s'
  normalizeStrictValue_preserves :
    ∀ {s : σ} {term : Pattern} {s' : σ} {out : Pattern},
      I.normalizeStrictValue s term = (s', out) → P s → P s'
  noteEval_preserves :
    ∀ {s : σ}, P s → P (I.noteEval s)
  withMessage_preserves :
    ∀ {s : σ} {msg : String}, P s → P (I.withMessage s msg)
  noteError_preserves :
    ∀ {s : σ} {msg : String}, P s → P (I.noteError s msg)

private def renderPatternList (I : Interface σ) (xs : List Pattern) : String :=
  "[" ++ String.intercalate ", " (xs.map I.renderPattern) ++ "]"

private def floatEqTol : Float := 0.000001

private def numericAtomEq (a b : Pattern) : Option Bool :=
  match numericOfPattern? a, numericOfPattern? b with
  | some x, some y => some (Float.abs (x - y) <= floatEqTol)
  | _, _ => none

private def boolOfPattern? : Pattern → Option Bool
  | .apply "True" [] => some true
  | .apply "False" [] => some false
  | .apply "true" [] => some true
  | .apply "false" [] => some false
  | _ => none

private def exprToListForm? : Pattern → Option Pattern
  | .apply "Expr" [] => some (.apply "()" [])
  | .apply "Expr" (.apply head [] :: tail) =>
      if head == "Expr" then
        none
      else
        some (.apply head tail)
  | _ => none

mutual
  private partial def patternSemEq : Pattern → Pattern → Bool
    | a, b =>
        match exprToListForm? a with
        | some a' => patternSemEq a' b
        | none =>
            match exprToListForm? b with
            | some b' => patternSemEq a b'
            | none =>
              match a, b with
              | .bvar n, .bvar m => n = m
              | .fvar x, .fvar y => x == y
              | .apply ca as, .apply cb bs =>
                  if as.isEmpty && bs.isEmpty then
                    match boolOfPattern? (.apply ca []), boolOfPattern? (.apply cb []) with
                    | some ba, some bb => ba = bb
                    | _, _ =>
                        match numericAtomEq (.apply ca []) (.apply cb []) with
                        | some ok => ok
                        | none => ca == cb
                  else
                    ca == cb && patternListSemEq as bs
              | .lambda x1, .lambda y1 => patternSemEq x1 y1
              | .multiLambda na x1, .multiLambda nb y1 =>
                  na = nb && patternSemEq x1 y1
              | .subst ba ra, .subst bb rb =>
                  patternSemEq ba bb && patternSemEq ra rb
              | .collection cta ea ra, .collection ctb eb rb =>
                  cta = ctb && ra = rb && patternListSemEq ea eb
              | _, _ => false

  private partial def patternListSemEq : List Pattern → List Pattern → Bool
    | [], [] => true
    | a :: as, b :: bs => patternSemEq a b && patternListSemEq as bs
    | _, _ => false
end

private partial def eraseFirstSemEq (x : Pattern) : List Pattern → Option (List Pattern)
  | [] => none
  | y :: ys =>
      if patternSemEq x y then
        some ys
      else
        match eraseFirstSemEq x ys with
        | some rest => some (y :: rest)
        | none => none

private partial def patternMultisetSemEq : List Pattern → List Pattern → Bool
  | [], ys => ys.isEmpty
  | x :: xs, ys =>
      match eraseFirstSemEq x ys with
      | some ys' => patternMultisetSemEq xs ys'
      | none => false

private def compareAssertOutputs (policy : Policy)
    (actualOut expectedOut : List Pattern) : Bool :=
  let sameDirect :=
    if policy.assertEqualMode = .multiset then
      patternMultisetSemEq actualOut expectedOut
    else
      patternListSemEq actualOut expectedOut
  let sameTupleFallback :=
    if policy.tupleFallback then
      match expectedOut with
      | [expOne] =>
          let expectedTupleElems := tupleElems expOne
          if policy.assertEqualMode = .multiset then
            patternMultisetSemEq actualOut expectedTupleElems
          else
            patternListSemEq actualOut expectedTupleElems
      | _ => false
    else
      false
  let sameEmptyTuple :=
    policy.emptyTupleMatchesEmpty && actualOut.isEmpty && expectedOut = [.apply "()" []]
  sameDirect || sameTupleFallback || sameEmptyTuple

private def patternToMettaString : Pattern → String
  | .fvar x => "$" ++ x
  | .bvar n => "$" ++ toString n
  | .apply "Expr" args =>
      if args.isEmpty then
        "()"
      else
        "(" ++ String.intercalate " " (args.map patternToMettaString) ++ ")"
  | .apply ctor [] => ctor
  | .apply ctor args =>
      "(" ++ ctor ++ " " ++ String.intercalate " " (args.map patternToMettaString) ++ ")"
  | .lambda body =>
      "(lambda " ++ patternToMettaString body ++ ")"
  | .multiLambda n body =>
      "(multi-lambda " ++ toString n ++ " " ++ patternToMettaString body ++ ")"
  | .subst body repl =>
      "(subst " ++ patternToMettaString body ++ " " ++ patternToMettaString repl ++ ")"
  | .collection _ elems _ =>
      "(" ++ String.intercalate " " (elems.map patternToMettaString) ++ ")"

private def outputsToTupleString (out : List Pattern) : String :=
  "(" ++ String.intercalate " " (out.map patternToMettaString) ++ ")"

private def successOut (I : Interface σ) (policy : Policy) : List Pattern :=
  match policy.resultStyle with
  | .boolean => [I.trueAtom]
  | .unitError => [.apply "Expr" []]

private def failureOut (I : Interface σ) (policy : Policy) : List Pattern :=
  match policy.resultStyle with
  | .boolean => [I.falseAtom]
  | .unitError => [I.falseAtom]

private def mkError (call reason : Pattern) : Pattern :=
  .apply "Error" [call, reason]

private def isUnitPattern : Pattern → Bool
  | .apply "Expr" [] => true
  | .apply "()" [] => true
  | _ => false

private def isUnitOut : List Pattern → Bool
  | [p] => isUnitPattern p
  | _ => false

private def tuplePatternOfOutputs (out : List Pattern) : Pattern :=
  .apply "Expr" out

private def tupleArg (p : Pattern) : Pattern :=
  match p with
  | .apply "Expr" _ => p
  | _ => .apply "Expr" [p]

private def normalizeOutValues (I : Interface σ) (s : σ)
    (xs : List Pattern) : σ × List Pattern :=
  xs.foldl
    (fun (acc : σ × List Pattern) p =>
      let sess0 := acc.1
      let vals := acc.2
      let (sess1, pN) := I.normalizeStrictValue sess0 p
      (sess1, vals ++ [pN]))
    (s, [])

private theorem normalizeOutValuesAux_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (vals : List Pattern) (xs : List Pattern) :
    P s →
      P
        ((xs.foldl
            (fun (acc : σ × List Pattern) p =>
              let sess0 := acc.1
              let vals0 := acc.2
              let (sess1, pN) := I.normalizeStrictValue sess0 p
              (sess1, vals0 ++ [pN]))
            (s, vals)).1) := by
  intro hP
  induction xs generalizing s vals with
  | nil =>
      simp [hP]
  | cons x rest ih =>
      simp
      let out := I.normalizeStrictValue s x
      have hStep : P out.1 := by
        exact H.normalizeStrictValue_preserves rfl hP
      simpa [out] using ih out.1 (vals ++ [out.2]) hStep

private theorem normalizeOutValues_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (xs : List Pattern) :
    P s → P (normalizeOutValues I s xs).1 := by
  intro hP
  simpa [normalizeOutValues] using
    normalizeOutValuesAux_preserves I P H s [] xs hP

def runStrictTest (I : Interface σ) (s : σ)
    (actual expected : Pattern) : σ × List Pattern :=
  let (s1, actualOut0) := I.eval s actual
  let (s2, expectedOut0) := I.eval s1 expected
  let (s3, actualOut) := normalizeOutValues I s2 actualOut0
  let (s4, expectedOut) := normalizeOutValues I s3 expectedOut0
  let sameDirect := patternListSemEq actualOut expectedOut
  let sameTupleFallback :=
    match expectedOut with
    | [expOne] => patternSemEq (tupleOfElems actualOut) expOne
    | _ => false
  let same := sameDirect || sameTupleFallback
  let s0 := I.noteEval (I.noteEval s4)
  if same then
    let s1 := I.withMessage s0 s!"test passed: actual={renderPatternList I actualOut}"
    (s1, [I.trueAtom])
  else
    let s1 := I.noteError s0
      s!"test failed: actual={renderPatternList I actualOut} expected={renderPatternList I expectedOut}"
    (s1, [I.falseAtom])

theorem runStrictTest_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (actual expected : Pattern) :
    P s → P (runStrictTest I s actual expected).1 := by
  intro hP
  unfold runStrictTest
  let e1 := I.eval s actual
  have h1 : P e1.1 := H.eval_preserves rfl hP
  let e2 := I.eval e1.1 expected
  have h2 : P e2.1 := H.eval_preserves rfl h1
  let n1 := normalizeOutValues I e2.1 e1.2
  have h3 : P n1.1 := normalizeOutValues_preserves I P H e2.1 e1.2 h2
  let n2 := normalizeOutValues I n1.1 e2.2
  have h4 : P n2.1 := normalizeOutValues_preserves I P H n1.1 e2.2 h3
  have h5 : P (I.noteEval (I.noteEval n2.1)) := H.noteEval_preserves (H.noteEval_preserves h4)
  by_cases hSame :
      patternListSemEq n1.2 n2.2 ||
        match n2.2 with
        | [expOne] => patternSemEq (tupleOfElems n1.2) expOne
        | _ => false
  · simpa [runStrictTest, e1, e2, n1, n2, hSame] using H.withMessage_preserves h5
  · simpa [runStrictTest, e1, e2, n1, n2, hSame] using H.noteError_preserves h5

theorem runStrictTestWithBool_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (actual expected expectedBool : Pattern) :
    P s →
      P
        (let (s0, out) := runStrictTest I s actual expected
         let actualBool := match out with | [b] => b | _ => I.falseAtom
         let (sBool, expectedBoolOut) := I.eval s0 expectedBool
         let sameBool := expectedBoolOut = [actualBool]
         let s1 := I.noteEval sBool
         let s2 :=
           if sameBool then
             I.withMessage s1 s!"test bool matched: {I.renderPattern actualBool}"
           else
             I.noteError s1
               s!"test bool mismatch: expected={renderPatternList I expectedBoolOut} actual={renderPatternList I [actualBool]}"
         s2) := by
  intro hP
  have h1 : P (runStrictTest I s actual expected).1 :=
    runStrictTest_preserves I P H s actual expected hP
  let out0 := runStrictTest I s actual expected
  let actualBool := match out0.2 with | [b] => b | _ => I.falseAtom
  let eBool := I.eval out0.1 expectedBool
  have h2 : P eBool.1 := H.eval_preserves rfl h1
  have h3 : P (I.noteEval eBool.1) := H.noteEval_preserves h2
  by_cases hSame : eBool.2 = [actualBool]
  · simpa [out0, actualBool, eBool, hSame] using H.withMessage_preserves h3
  · simpa [out0, actualBool, eBool, hSame] using H.noteError_preserves h3

def runAssertTest (I : Interface σ) (policy : Policy) (s : σ)
    (actual expected : Pattern) : σ × List Pattern :=
  let (s1, actualOut) := I.eval s actual
  let (s2, expectedOut) := I.eval s1 expected
  let same := compareAssertOutputs policy actualOut expectedOut
  let s0 := I.noteEval (I.noteEval s2)
  if same then
    let s1 := I.withMessage s0 s!"test passed: actual={renderPatternList I actualOut}"
    (s1, successOut I policy)
  else
    let s1 := I.noteError s0
      s!"test failed: actual={renderPatternList I actualOut} expected={renderPatternList I expectedOut}"
    (s1, failureOut I policy)

theorem runAssertTest_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (policy : Policy) (s : σ) (actual expected : Pattern) :
    P s → P (runAssertTest I policy s actual expected).1 := by
  intro hP
  unfold runAssertTest
  let e1 := I.eval s actual
  have h1 : P e1.1 := H.eval_preserves rfl hP
  let e2 := I.eval e1.1 expected
  have h2 : P e2.1 := H.eval_preserves rfl h1
  have h3 : P (I.noteEval (I.noteEval e2.1)) := H.noteEval_preserves (H.noteEval_preserves h2)
  by_cases hSame : compareAssertOutputs policy e1.2 e2.2
  · simpa [runAssertTest, e1, e2, hSame] using H.withMessage_preserves h3
  · simpa [runAssertTest, e1, e2, hSame] using H.noteError_preserves h3

private def runAssertCommand (I : Interface σ) (policy : Policy) (s : σ)
    (actual : Pattern) : σ × List Pattern :=
  let (s1, out) := I.eval s actual
  let truthy := out.any (patternSemEq · I.trueAtom)
  let s2 := I.noteEval s1
  if truthy then
    let s3 := I.withMessage s2 s!"assert passed: actual={renderPatternList I out}"
    (s3, successOut I policy)
  else
    let call := .apply "assert" [actual]
    let reason := .apply "Expr" [actual, .apply "not" [], .apply "True" []]
    let err := mkError call reason
    let s3 := I.noteError s2 s!"assert failed: actual={renderPatternList I out}"
    match policy.resultStyle with
    | .boolean => (s3, [I.falseAtom])
    | .unitError => (s3, [err])

private theorem runAssertCommand_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (policy : Policy) (s : σ) (actual : Pattern) :
    P s → P (runAssertCommand I policy s actual).1 := by
  intro hP
  unfold runAssertCommand
  let e1 := I.eval s actual
  have h1 : P e1.1 := H.eval_preserves rfl hP
  have h2 : P (I.noteEval e1.1) := H.noteEval_preserves h1
  by_cases hTruthy : e1.2.any (patternSemEq · I.trueAtom)
  · simpa [runAssertCommand, e1, hTruthy] using H.withMessage_preserves h2
  · cases hStyle : policy.resultStyle <;>
      simpa [runAssertCommand, e1, hTruthy, hStyle] using H.noteError_preserves h2

private def runAssertEqualMsgCommand (I : Interface σ) (policy : Policy) (s : σ)
    (actual expected msg : Pattern) : σ × List Pattern :=
  let (s1, out) := runAssertTest I policy s actual expected
  match policy.resultStyle with
  | .boolean => (s1, out)
  | .unitError =>
      if isUnitOut out then
        (s1, out)
      else
        (s1, [mkError (.apply "assertEqualMsg" [actual, expected]) msg])

private theorem runAssertEqualMsgCommand_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (policy : Policy) (s : σ) (actual expected msg : Pattern) :
    P s → P (runAssertEqualMsgCommand I policy s actual expected msg).1 := by
  intro hP
  let out0 := runAssertTest I policy s actual expected
  have h1 : P out0.1 := runAssertTest_preserves I P H policy s actual expected hP
  cases hStyle : policy.resultStyle <;>
    simp [runAssertEqualMsgCommand, out0, hStyle, h1]
  · by_cases hUnit : isUnitOut out0.2 <;>
      simp [out0, hUnit, h1]

private def runAssertEqualCommand (I : Interface σ) (policy : Policy) (s : σ)
    (actual expected : Pattern) : σ × List Pattern :=
  let (s1, out) := runAssertTest I policy s actual expected
  match policy.resultStyle with
  | .boolean => (s1, out)
  | .unitError =>
      if isUnitOut out then
        (s1, out)
      else
        let reason := .apply "Expr" [actual, .apply "!=" [expected]]
        (s1, [mkError (.apply "assertEqual" [actual, expected]) reason])

private theorem runAssertEqualCommand_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (policy : Policy) (s : σ) (actual expected : Pattern) :
    P s → P (runAssertEqualCommand I policy s actual expected).1 := by
  intro hP
  let out0 := runAssertTest I policy s actual expected
  have h1 : P out0.1 := runAssertTest_preserves I P H policy s actual expected hP
  cases hStyle : policy.resultStyle <;>
    simp [runAssertEqualCommand, out0, hStyle, h1]
  · by_cases hUnit : isUnitOut out0.2 <;>
      simp [out0, hUnit, h1]

private def runAssertEqualToResultCommand (I : Interface σ) (policy : Policy) (s : σ)
    (actual expected : Pattern) : σ × List Pattern :=
  let (s1, out) := runAssertTest I policy s actual expected
  match policy.resultStyle with
  | .boolean => (s1, out)
  | .unitError =>
      if isUnitOut out then
        (s1, out)
      else
        let reason := .apply "Expr" [actual, .apply "not in" [expected]]
        (s1, [mkError (.apply "assertEqualToResult" [actual, tupleArg expected]) reason])

private theorem runAssertEqualToResultCommand_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (policy : Policy) (s : σ) (actual expected : Pattern) :
    P s → P (runAssertEqualToResultCommand I policy s actual expected).1 := by
  intro hP
  let out0 := runAssertTest I policy s actual expected
  have h1 : P out0.1 := runAssertTest_preserves I P H policy s actual expected hP
  cases hStyle : policy.resultStyle <;>
    simp [runAssertEqualToResultCommand, out0, hStyle, h1]
  · by_cases hUnit : isUnitOut out0.2 <;>
      simp [out0, hUnit, h1]

private def runAssertEqualToResultMsgCommand (I : Interface σ) (policy : Policy) (s : σ)
    (actual expected msg : Pattern) : σ × List Pattern :=
  let (s1, out) := runAssertTest I policy s actual expected
  match policy.resultStyle with
  | .boolean => (s1, out)
  | .unitError =>
      if isUnitOut out then
        (s1, out)
      else
        (s1, [mkError (.apply "assertEqualToResultMsg" [actual, tupleArg expected]) msg])

private theorem runAssertEqualToResultMsgCommand_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (policy : Policy) (s : σ) (actual expected msg : Pattern) :
    P s → P (runAssertEqualToResultMsgCommand I policy s actual expected msg).1 := by
  intro hP
  let out0 := runAssertTest I policy s actual expected
  have h1 : P out0.1 := runAssertTest_preserves I P H policy s actual expected hP
  cases hStyle : policy.resultStyle <;>
    simp [runAssertEqualToResultMsgCommand, out0, hStyle, h1]
  · by_cases hUnit : isUnitOut out0.2 <;>
      simp [out0, hUnit, h1]

private def runAssertIncludesCommand (I : Interface σ) (policy : Policy) (s : σ)
    (actual expected : Pattern) : σ × List Pattern :=
  let (s1, actualOut) := I.eval s actual
  let (s2, expectedOut) := I.eval s1 expected
  let includes :=
    expectedOut.all (fun want => actualOut.any (patternSemEq want ·))
  let s3 := I.noteEval (I.noteEval s2)
  if includes then
    let s4 := I.withMessage s3 s!"assertIncludes passed: actual={renderPatternList I actualOut}"
    (s4, successOut I policy)
  else
    let s4 := I.noteError s3 s!"assertIncludes failed: actual={renderPatternList I actualOut}"
    match policy.resultStyle with
    | .boolean => (s4, [I.falseAtom])
    | .unitError =>
        let msg :=
          .apply "Expr"
            [ .apply "assertIncludes" []
            , .apply "error:" []
            , tuplePatternOfOutputs expectedOut
            , .apply "not" []
            , .apply "included" []
            , .apply "in" []
            , .apply "result:" []
            , tuplePatternOfOutputs actualOut
            ]
        (s4, [mkError (.apply "assertIncludes" [actual, tupleArg expected]) msg])

private theorem runAssertIncludesCommand_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (policy : Policy) (s : σ) (actual expected : Pattern) :
    P s → P (runAssertIncludesCommand I policy s actual expected).1 := by
  intro hP
  unfold runAssertIncludesCommand
  let e1 := I.eval s actual
  have h1 : P e1.1 := H.eval_preserves rfl hP
  let e2 := I.eval e1.1 expected
  have h2 : P e2.1 := H.eval_preserves rfl h1
  have h3 : P (I.noteEval (I.noteEval e2.1)) := H.noteEval_preserves (H.noteEval_preserves h2)
  by_cases hIncludes : e2.2.all (fun want => e1.2.any (patternSemEq want ·))
  · simpa [runAssertIncludesCommand, e1, e2, hIncludes] using H.withMessage_preserves h3
  · cases hStyle : policy.resultStyle <;>
      simpa [runAssertIncludesCommand, e1, e2, hIncludes, hStyle] using H.noteError_preserves h3

def evalAssertionCommand? (I : Interface σ) (policy : Policy) (s : σ)
    (term : Pattern) : Option (σ × List Pattern) :=
  match term with
  | .apply "test" [actual, expected] =>
      some (runStrictTest I s actual expected)
  | .apply "test" [actual, expected, expectedBool] =>
      let (s0, out) := runStrictTest I s actual expected
      let actualBool := match out with | [b] => b | _ => I.falseAtom
      let (sBool, expectedBoolOut) := I.eval s0 expectedBool
      let sameBool := expectedBoolOut = [actualBool]
      let s1 := I.noteEval sBool
      let s2 :=
        if sameBool then
          I.withMessage s1 s!"test bool matched: {I.renderPattern actualBool}"
        else
          I.noteError s1
            s!"test bool mismatch: expected={renderPatternList I expectedBoolOut} actual={renderPatternList I [actualBool]}"
      some (s2, out)
  | .apply "assertEqual" [actual, expected] =>
      some (runAssertEqualCommand I policy s actual expected)
  | .apply "assertEqualToResult" [actual, expected] =>
      some (runAssertEqualToResultCommand I policy s actual expected)
  | .apply "assertEqualMsg" [actual, expected, msg] =>
      some (runAssertEqualMsgCommand I policy s actual expected msg)
  | .apply "assertEqualToResultMsg" [actual, expected, msg] =>
      some (runAssertEqualToResultMsgCommand I policy s actual expected msg)
  | .apply "assert" [actual] =>
      some (runAssertCommand I policy s actual)
  | .apply "assertIncludes" [actual, expected] =>
      some (runAssertIncludesCommand I policy s actual expected)
  | _ =>
      none

theorem evalAssertionCommand?_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (policy : Policy) (s : σ) (term : Pattern) :
    P s →
      match evalAssertionCommand? I policy s term with
      | some res => P res.1
      | none => True := by
  intro hP
  cases term with
  | fvar x =>
      simp [evalAssertionCommand?]
  | bvar n =>
      simp [evalAssertionCommand?]
  | lambda body =>
      simp [evalAssertionCommand?]
  | multiLambda n body =>
      simp [evalAssertionCommand?]
  | subst body repl =>
      simp [evalAssertionCommand?]
  | collection ct elems rest =>
      simp [evalAssertionCommand?]
  | apply ctor args =>
      cases args with
      | nil =>
          simp [evalAssertionCommand?]
      | cons a as =>
          cases as with
          | nil =>
              by_cases hAssert : ctor = "assert"
              · subst hAssert
                simpa [evalAssertionCommand?] using
                  runAssertCommand_preserves I P H policy s a hP
              · simp [evalAssertionCommand?, hAssert]
          | cons b bs =>
              cases bs with
              | nil =>
                  by_cases hTest : ctor = "test"
                  · subst hTest
                    simpa [evalAssertionCommand?] using
                      runStrictTest_preserves I P H s a b hP
                  · by_cases hEq : ctor = "assertEqual"
                    · subst hEq
                      simpa [evalAssertionCommand?] using
                        runAssertEqualCommand_preserves I P H policy s a b hP
                    · by_cases hEqRes : ctor = "assertEqualToResult"
                      · subst hEqRes
                        simpa [evalAssertionCommand?] using
                          runAssertEqualToResultCommand_preserves I P H policy s a b hP
                      · by_cases hIncl : ctor = "assertIncludes"
                        · subst hIncl
                          simpa [evalAssertionCommand?] using
                            runAssertIncludesCommand_preserves I P H policy s a b hP
                        · simp [evalAssertionCommand?, hTest, hEq, hEqRes, hIncl]
              | cons c cs =>
                  cases cs with
                  | nil =>
                      by_cases hTest : ctor = "test"
                      · subst hTest
                        simpa [evalAssertionCommand?] using
                          runStrictTestWithBool_preserves I P H s a b c hP
                      · by_cases hEqMsg : ctor = "assertEqualMsg"
                        · subst hEqMsg
                          simpa [evalAssertionCommand?] using
                            runAssertEqualMsgCommand_preserves I P H policy s a b c hP
                        · by_cases hEqResMsg : ctor = "assertEqualToResultMsg"
                          · subst hEqResMsg
                            simpa [evalAssertionCommand?] using
                              runAssertEqualToResultMsgCommand_preserves I P H policy s a b c hP
                          · simp [evalAssertionCommand?, hTest, hEqMsg, hEqResMsg]
                  | cons d ds =>
                      simp [evalAssertionCommand?]

end Algorithms.MeTTa.Simple.Semantics.Assertions
