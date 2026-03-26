import MeTTailCore
import Algorithms.MeTTa.Simple.Semantics.DeterministicStrategy

namespace Algorithms.MeTTa.Simple.Semantics.DeterministicEval

open MeTTailCore.MeTTaIL.Syntax

structure Interface (σ : Type) where
  evalTupleIntrinsic : σ → List Pattern → σ × List Pattern
  translateCall : σ → Pattern → List Pattern
  deterministicPreserveArgs : String → Bool
  intrinsicDirect : σ → String → List Pattern → List Pattern
  firstRuleReduction? : σ → Pattern → Option Pattern
  rewriteAritiesForHead : σ → String → List Nat
  builtinPartialMinArity : String → Option Nat
  partialPattern : String → List Pattern → Pattern
  memoLimit : σ → Nat

structure Preservation (I : Interface σ) (P : σ → Prop) where
  evalTupleIntrinsic_preserves :
    ∀ {s : σ} {elems : List Pattern} {s' : σ} {out : List Pattern},
      I.evalTupleIntrinsic s elems = (s', out) →
      P s → P s'

private def boolOfPattern? : Pattern → Option Bool
  | .apply "True" [] => some true
  | .apply "true" [] => some true
  | .apply "False" [] => some false
  | .apply "false" [] => some false
  | _ => none

private abbrev DetMemo := List (Pattern × Pattern)

private def detMemoLookup (memo : DetMemo) (term : Pattern) : Option Pattern :=
  (memo.find? (fun kv => kv.1 == term)).map Prod.snd

private def detMemoInsert (memo : DetMemo) (term out : Pattern) (limit : Nat) : DetMemo :=
  let updated := (term, out) :: (memo.filter (fun kv => kv.1 != term))
  if updated.length <= limit then
    updated
  else
    updated.take limit

mutual
  private def evalArgs (I : Interface σ) (s : σ) (fuel : Nat)
      (memo : DetMemo) (args : List Pattern) : σ × DetMemo × List Pattern :=
    match args with
    | [] => (s, memo, [])
    | a :: rest =>
        let (s1, memo1, aV) := evalMemo I s fuel memo a
        let (s2, memo2, restV) := evalArgs I s1 fuel memo1 rest
        (s2, memo2, aV :: restV)

  private def evalMemo (I : Interface σ) (s : σ) (fuel : Nat)
      (memo : DetMemo) (term : Pattern) : σ × DetMemo × Pattern :=
    match fuel with
    | 0 => (s, memo, term)
    | fuel + 1 =>
        match term with
        | .apply "if" [cond, thenBr, elseBr] =>
            let (s1, memo1, condV) := evalMemo I s fuel memo cond
            match boolOfPattern? condV with
            | some true => evalMemo I s1 fuel memo1 thenBr
            | some false => evalMemo I s1 fuel memo1 elseBr
            | none => (s1, memo1, .apply "if" [condV, thenBr, elseBr])
        | .apply "Expr" elems =>
            let (s1, out) := I.evalTupleIntrinsic s elems
            match out with
            | [] => (s1, memo, .apply "Expr" elems)
            | one :: _ =>
                if one == .apply "Expr" elems then
                  (s1, memo, one)
                else
                  evalMemo I s1 fuel memo one
        | .apply ctor args =>
            let callRaw := .apply ctor args
            let memoizable :=
              Algorithms.MeTTa.Simple.Semantics.DeterministicStrategy.isMemoizableDeterministicCall callRaw
            match (if memoizable then detMemoLookup memo callRaw else none) with
            | some cached =>
                (s, memo, cached)
            | none =>
                let finalize (sOut : σ) (memoOut : DetMemo) (out : Pattern) :
                    σ × DetMemo × Pattern :=
                  let memo' :=
                    if memoizable then
                      detMemoInsert memoOut callRaw out (I.memoLimit sOut)
                    else
                      memoOut
                  (sOut, memo', out)
                let translated := I.translateCall s callRaw
                if !translated.isEmpty then
                  let out := translated.headD callRaw
                  if out == callRaw then
                    finalize s memo out
                  else
                    let (sR, memoR, outR) := evalMemo I s fuel memo out
                    finalize sR memoR outR
                else
                  let (s1, memo1, argsV) :=
                    if I.deterministicPreserveArgs ctor then
                      (s, memo, args)
                    else
                      evalArgs I s fuel memo args
                  let callV := .apply ctor argsV
                  if ctor == "=" then
                    finalize s1 memo1 callV
                  else
                    match I.builtinPartialMinArity ctor with
                    | some minArity =>
                        if argsV.length < minArity then
                          finalize s1 memo1 (I.partialPattern ctor argsV)
                        else
                          let direct := I.intrinsicDirect s1 ctor argsV
                          if !direct.isEmpty then
                            let out := direct.headD callV
                            if out == callV then
                              finalize s1 memo1 out
                            else
                              let (sR, memoR, outR) := evalMemo I s1 fuel memo1 out
                              finalize sR memoR outR
                          else
                            match I.firstRuleReduction? s1 callV with
                            | some rhs =>
                                let (sR, memoR, outR) := evalMemo I s1 fuel memo1 rhs
                                finalize sR memoR outR
                            | none =>
                                let arities := I.rewriteAritiesForHead s1 ctor
                                let hasExact := arities.any (fun n => n == argsV.length)
                                let hasLarger := arities.any (fun n => n > argsV.length)
                                if hasLarger && !hasExact && !argsV.isEmpty then
                                  finalize s1 memo1 (I.partialPattern ctor argsV)
                                else
                                  finalize s1 memo1 callV
                    | none =>
                        let direct := I.intrinsicDirect s1 ctor argsV
                        if !direct.isEmpty then
                          let out := direct.headD callV
                          if out == callV then
                            finalize s1 memo1 out
                          else
                            let (sR, memoR, outR) := evalMemo I s1 fuel memo1 out
                            finalize sR memoR outR
                        else
                          match I.firstRuleReduction? s1 callV with
                          | some rhs =>
                              let (sR, memoR, outR) := evalMemo I s1 fuel memo1 rhs
                              finalize sR memoR outR
                          | none =>
                              let arities := I.rewriteAritiesForHead s1 ctor
                              let hasExact := arities.any (fun n => n == argsV.length)
                              let hasLarger := arities.any (fun n => n > argsV.length)
                              if hasLarger && !hasExact && !argsV.isEmpty then
                                finalize s1 memo1 (I.partialPattern ctor argsV)
                              else
                                finalize s1 memo1 callV
        | _ => (s, memo, term)
end

theorem evalMemo_preserves (I : Interface σ) (P : σ → Prop) (H : Preservation I P) :
    ∀ (fuel : Nat) (s : σ) (memo : DetMemo) (term : Pattern),
      P s → P (evalMemo I s fuel memo term).1 := by
  intro fuel
  induction fuel with
  | zero =>
      intro s memo term hP
      simpa [evalMemo.eq_def] using hP
  | succ fuel ih =>
      have hArgsFuel :
          ∀ (s : σ) (memo : DetMemo) (args : List Pattern),
            P s → P (evalArgs I s fuel memo args).1 := by
        intro s memo args hP
        induction args generalizing s memo with
        | nil =>
            simpa [evalArgs.eq_def] using hP
        | cons a rest ihArgs =>
            have hHead : P (evalMemo I s fuel memo a).1 := ih s memo a hP
            cases hEvalHead : evalMemo I s fuel memo a with
            | mk s1 rest1 =>
                cases rest1 with
                | mk memo1 aV =>
                    have hs1 : P s1 := by
                      simpa [hEvalHead] using hHead
                    have hTail : P (evalArgs I s1 fuel memo1 rest).1 :=
                      ihArgs s1 memo1 hs1
                    rw [evalArgs.eq_def]
                    simpa [hEvalHead] using hTail
      intro s memo term hP
      cases term with
      | fvar x =>
          simpa [evalMemo.eq_def] using hP
      | bvar n =>
          simpa [evalMemo.eq_def] using hP
      | lambda body =>
          simpa [evalMemo.eq_def] using hP
      | multiLambda n body =>
          simpa [evalMemo.eq_def] using hP
      | subst body repl =>
          simpa [evalMemo.eq_def] using hP
      | collection ct elems rest =>
          simpa [evalMemo.eq_def] using hP
      | apply ctor args =>
          let genericApplyBody := fun (ctor : String) (args : List Pattern) =>
            let callRaw : Pattern := Pattern.apply ctor args
            let memoizable :=
              Algorithms.MeTTa.Simple.Semantics.DeterministicStrategy.isMemoizableDeterministicCall callRaw
            match (if memoizable then detMemoLookup memo callRaw else none) with
            | some cached =>
                (s, memo, cached)
            | none =>
                let finalize (sOut : σ) (memoOut : DetMemo) (out : Pattern) :
                    σ × DetMemo × Pattern :=
                  let memo' :=
                    if memoizable then
                      detMemoInsert memoOut callRaw out (I.memoLimit sOut)
                    else
                      memoOut
                  (sOut, memo', out)
                let translated := I.translateCall s callRaw
                if !translated.isEmpty then
                  let out := translated.headD callRaw
                  if out == callRaw then
                    finalize s memo out
                  else
                    let (sR, memoR, outR) := evalMemo I s fuel memo out
                    finalize sR memoR outR
                else
                  let (s1, memo1, argsV) :=
                    if I.deterministicPreserveArgs ctor then
                      (s, memo, args)
                    else
                      evalArgs I s fuel memo args
                  let callV := Pattern.apply ctor argsV
                  if ctor == "=" then
                    finalize s1 memo1 callV
                  else
                    match I.builtinPartialMinArity ctor with
                    | some minArity =>
                        if argsV.length < minArity then
                          finalize s1 memo1 (I.partialPattern ctor argsV)
                        else
                          let direct := I.intrinsicDirect s1 ctor argsV
                          if !direct.isEmpty then
                            let out := direct.headD callV
                            if out == callV then
                              finalize s1 memo1 out
                            else
                              let (sR, memoR, outR) := evalMemo I s1 fuel memo1 out
                              finalize sR memoR outR
                          else
                            match I.firstRuleReduction? s1 callV with
                            | some rhs =>
                                let (sR, memoR, outR) := evalMemo I s1 fuel memo1 rhs
                                finalize sR memoR outR
                            | none =>
                                let arities := I.rewriteAritiesForHead s1 ctor
                                let hasExact := arities.any (fun n => n == argsV.length)
                                let hasLarger := arities.any (fun n => n > argsV.length)
                                if hasLarger && !hasExact && !argsV.isEmpty then
                                  finalize s1 memo1 (I.partialPattern ctor argsV)
                                else
                                  finalize s1 memo1 callV
                    | none =>
                        let direct := I.intrinsicDirect s1 ctor argsV
                        if !direct.isEmpty then
                          let out := direct.headD callV
                          if out == callV then
                            finalize s1 memo1 out
                          else
                            let (sR, memoR, outR) := evalMemo I s1 fuel memo1 out
                            finalize sR memoR outR
                        else
                          match I.firstRuleReduction? s1 callV with
                          | some rhs =>
                              let (sR, memoR, outR) := evalMemo I s1 fuel memo1 rhs
                              finalize sR memoR outR
                          | none =>
                              let arities := I.rewriteAritiesForHead s1 ctor
                              let hasExact := arities.any (fun n => n == argsV.length)
                              let hasLarger := arities.any (fun n => n > argsV.length)
                              if hasLarger && !hasExact && !argsV.isEmpty then
                                finalize s1 memo1 (I.partialPattern ctor argsV)
                              else
                                finalize s1 memo1 callV
          let genericApply :
              ∀ (ctor : String) (args : List Pattern),
                P ((genericApplyBody ctor args).1) := by
            intro ctor args
            let callRaw : Pattern := .apply ctor args
            let memoizable :=
              Algorithms.MeTTa.Simple.Semantics.DeterministicStrategy.isMemoizableDeterministicCall callRaw
            have finalize_preserves :
                ∀ {sOut : σ} {memoOut : DetMemo} {out : Pattern},
                  P sOut →
                    P
                      ((let memo' :=
                            if memoizable then
                              detMemoInsert memoOut callRaw out (I.memoLimit sOut)
                            else
                              memoOut
                        (sOut, memo', out)).1) := by
              intro sOut memoOut out hsOut
              simpa using hsOut
            have recursiveFinalize_preserves :
                ∀ (s0 : σ) (memo0 : DetMemo) (t : Pattern),
                  P s0 →
                    P
                      ((let (sR, memoR, outR) := evalMemo I s0 fuel memo0 t
                        let memo' :=
                          if memoizable then
                            detMemoInsert memoR callRaw outR (I.memoLimit sR)
                          else
                            memoR
                        (sR, memo', outR)).1) := by
              intro s0 memo0 t hs0
              have hRec : P (evalMemo I s0 fuel memo0 t).1 := ih s0 memo0 t hs0
              cases hEval : evalMemo I s0 fuel memo0 t with
              | mk sR rest =>
                  cases rest with
                  | mk memoR outR =>
                      have hsR : P sR := by
                        simpa [hEval] using hRec
                      simpa [hEval] using
                        finalize_preserves (sOut := sR) (memoOut := memoR) (out := outR) hsR
            have afterDirectRule_preserves :
                ∀ (s1 : σ) (memo1 : DetMemo) (argsV : List Pattern),
                  P s1 →
                    P
                      ((let callV : Pattern := .apply ctor argsV
                        let direct := I.intrinsicDirect s1 ctor argsV
                        if !direct.isEmpty then
                          let out := direct.headD callV
                          if out == callV then
                            let memo' :=
                              if memoizable then
                                detMemoInsert memo1 callRaw out (I.memoLimit s1)
                              else
                                memo1
                            (s1, memo', out)
                          else
                            let (sR, memoR, outR) := evalMemo I s1 fuel memo1 out
                            let memo' :=
                              if memoizable then
                                detMemoInsert memoR callRaw outR (I.memoLimit sR)
                              else
                                memoR
                            (sR, memo', outR)
                        else
                          match I.firstRuleReduction? s1 callV with
                          | some rhs =>
                              let (sR, memoR, outR) := evalMemo I s1 fuel memo1 rhs
                              let memo' :=
                                if memoizable then
                                  detMemoInsert memoR callRaw outR (I.memoLimit sR)
                                else
                                  memoR
                              (sR, memo', outR)
                          | none =>
                              let arities := I.rewriteAritiesForHead s1 ctor
                              let hasExact := arities.any (fun n => n == argsV.length)
                              let hasLarger := arities.any (fun n => n > argsV.length)
                              if hasLarger && !hasExact && !argsV.isEmpty then
                                let memo' :=
                                  if memoizable then
                                    detMemoInsert memo1 callRaw (I.partialPattern ctor argsV)
                                      (I.memoLimit s1)
                                  else
                                    memo1
                                (s1, memo', I.partialPattern ctor argsV)
                              else
                                let memo' :=
                                  if memoizable then
                                    detMemoInsert memo1 callRaw callV (I.memoLimit s1)
                                  else
                                    memo1
                                (s1, memo', callV)).1) := by
              intro s1 memo1 argsV hs1
              let callV : Pattern := .apply ctor argsV
              cases hDirect : I.intrinsicDirect s1 ctor argsV with
              | nil =>
                  simp
                  cases hRule : I.firstRuleReduction? s1 callV with
                  | some rhs =>
                      simpa [callV, hRule] using recursiveFinalize_preserves s1 memo1 rhs hs1
                  | none =>
                      have hState :
                          (match I.firstRuleReduction? s1 callV with
                           | some rhs =>
                               let (sR, memoR, outR) := evalMemo I s1 fuel memo1 rhs
                               let memo' :=
                                 if memoizable then
                                   detMemoInsert memoR callRaw outR (I.memoLimit sR)
                                 else
                                   memoR
                               (sR, memo', outR)
                           | none =>
                               let arities := I.rewriteAritiesForHead s1 ctor
                               let hasExact := arities.any (fun n => n == argsV.length)
                               let hasLarger := arities.any (fun n => n > argsV.length)
                               if hasLarger && !hasExact && !argsV.isEmpty then
                                 let memo' :=
                                   if memoizable then
                                     detMemoInsert memo1 callRaw (I.partialPattern ctor argsV)
                                       (I.memoLimit s1)
                                   else
                                     memo1
                                 (s1, memo', I.partialPattern ctor argsV)
                               else
                                 let memo' :=
                                   if memoizable then
                                     detMemoInsert memo1 callRaw callV (I.memoLimit s1)
                                 else
                                     memo1
                                 (s1, memo', callV)).1 = s1 := by
                        let arities := I.rewriteAritiesForHead s1 ctor
                        let hasExact := arities.any (fun n => n == argsV.length)
                        let hasLarger := arities.any (fun n => n > argsV.length)
                        by_cases hBranch : (hasLarger && !hasExact && !argsV.isEmpty) = true
                        · simp [hRule, arities, hasExact, hasLarger, hBranch, callV]
                        · simp [hRule, arities, hasExact, hasLarger, hBranch, callV]
                      have hsState :
                          P
                            ((match I.firstRuleReduction? s1 callV with
                              | some rhs =>
                                  let (sR, memoR, outR) := evalMemo I s1 fuel memo1 rhs
                                  let memo' :=
                                    if memoizable then
                                      detMemoInsert memoR callRaw outR (I.memoLimit sR)
                                    else
                                      memoR
                                  (sR, memo', outR)
                              | none =>
                                  let arities := I.rewriteAritiesForHead s1 ctor
                                  let hasExact := arities.any (fun n => n == argsV.length)
                                  let hasLarger := arities.any (fun n => n > argsV.length)
                                  if hasLarger && !hasExact && !argsV.isEmpty then
                                    let memo' :=
                                      if memoizable then
                                        detMemoInsert memo1 callRaw (I.partialPattern ctor argsV)
                                          (I.memoLimit s1)
                                      else
                                        memo1
                                    (s1, memo', I.partialPattern ctor argsV)
                                  else
                                    let memo' :=
                                      if memoizable then
                                        detMemoInsert memo1 callRaw callV (I.memoLimit s1)
                                      else
                                        memo1
                                    (s1, memo', callV)).1) := by
                        exact Eq.mp (congrArg P hState.symm) hs1
                      simpa [callV, hRule] using hsState
              | cons out directRest =>
                  simp
                  by_cases hEq : out == callV
                  · have hEqOut : out = callV := by
                      simpa using hEq
                    simpa [callV, hEqOut] using
                      finalize_preserves (sOut := s1) (memoOut := memo1) (out := out) hs1
                  · have hNeOut : ¬ out = callV := by
                      simpa using hEq
                    simpa [callV, hNeOut] using recursiveFinalize_preserves s1 memo1 out hs1
            have afterArgs_preserves :
                ∀ (s1 : σ) (memo1 : DetMemo) (argsV : List Pattern),
                  P s1 →
                    P
                      ((let callV : Pattern := .apply ctor argsV
                        if ctor == "=" then
                          let memo' :=
                            if memoizable then
                              detMemoInsert memo1 callRaw callV (I.memoLimit s1)
                            else
                              memo1
                          (s1, memo', callV)
                        else
                          match I.builtinPartialMinArity ctor with
                          | some minArity =>
                              if argsV.length < minArity then
                                let memo' :=
                                  if memoizable then
                                    detMemoInsert memo1 callRaw (I.partialPattern ctor argsV)
                                      (I.memoLimit s1)
                                  else
                                    memo1
                                (s1, memo', I.partialPattern ctor argsV)
                              else
                                let direct := I.intrinsicDirect s1 ctor argsV
                                if !direct.isEmpty then
                                  let out := direct.headD callV
                                  if out == callV then
                                    let memo' :=
                                      if memoizable then
                                        detMemoInsert memo1 callRaw out (I.memoLimit s1)
                                      else
                                        memo1
                                    (s1, memo', out)
                                  else
                                    let (sR, memoR, outR) := evalMemo I s1 fuel memo1 out
                                    let memo' :=
                                      if memoizable then
                                        detMemoInsert memoR callRaw outR (I.memoLimit sR)
                                      else
                                        memoR
                                    (sR, memo', outR)
                                else
                                  match I.firstRuleReduction? s1 callV with
                                  | some rhs =>
                                      let (sR, memoR, outR) := evalMemo I s1 fuel memo1 rhs
                                      let memo' :=
                                        if memoizable then
                                          detMemoInsert memoR callRaw outR (I.memoLimit sR)
                                        else
                                          memoR
                                      (sR, memo', outR)
                                  | none =>
                                      let arities := I.rewriteAritiesForHead s1 ctor
                                      let hasExact := arities.any (fun n => n == argsV.length)
                                      let hasLarger := arities.any (fun n => n > argsV.length)
                                      if hasLarger && !hasExact && !argsV.isEmpty then
                                        let memo' :=
                                          if memoizable then
                                            detMemoInsert memo1 callRaw (I.partialPattern ctor argsV)
                                              (I.memoLimit s1)
                                          else
                                            memo1
                                        (s1, memo', I.partialPattern ctor argsV)
                                      else
                                        let memo' :=
                                          if memoizable then
                                            detMemoInsert memo1 callRaw callV (I.memoLimit s1)
                                          else
                                            memo1
                                        (s1, memo', callV)
                          | none =>
                              let direct := I.intrinsicDirect s1 ctor argsV
                              if !direct.isEmpty then
                                let out := direct.headD callV
                                if out == callV then
                                  let memo' :=
                                    if memoizable then
                                      detMemoInsert memo1 callRaw out (I.memoLimit s1)
                                    else
                                      memo1
                                  (s1, memo', out)
                                else
                                  let (sR, memoR, outR) := evalMemo I s1 fuel memo1 out
                                  let memo' :=
                                    if memoizable then
                                      detMemoInsert memoR callRaw outR (I.memoLimit sR)
                                    else
                                      memoR
                                  (sR, memo', outR)
                              else
                                match I.firstRuleReduction? s1 callV with
                                | some rhs =>
                                    let (sR, memoR, outR) := evalMemo I s1 fuel memo1 rhs
                                    let memo' :=
                                      if memoizable then
                                        detMemoInsert memoR callRaw outR (I.memoLimit sR)
                                      else
                                        memoR
                                    (sR, memo', outR)
                                | none =>
                                    let arities := I.rewriteAritiesForHead s1 ctor
                                    let hasExact := arities.any (fun n => n == argsV.length)
                                    let hasLarger := arities.any (fun n => n > argsV.length)
                                    if hasLarger && !hasExact && !argsV.isEmpty then
                                      let memo' :=
                                        if memoizable then
                                          detMemoInsert memo1 callRaw (I.partialPattern ctor argsV)
                                            (I.memoLimit s1)
                                        else
                                          memo1
                                      (s1, memo', I.partialPattern ctor argsV)
                                    else
                                      let memo' :=
                                        if memoizable then
                                          detMemoInsert memo1 callRaw callV (I.memoLimit s1)
                                        else
                                          memo1
                                      (s1, memo', callV)).1) := by
              intro s1 memo1 argsV hs1
              let callV : Pattern := .apply ctor argsV
              by_cases hEqCtor : ctor = "="
              · simpa [callV, hEqCtor] using
                  finalize_preserves (sOut := s1) (memoOut := memo1) (out := callV) hs1
              · simp [hEqCtor]
                cases hMin : I.builtinPartialMinArity ctor with
                | some minArity =>
                    by_cases hShort : argsV.length < minArity
                    · simpa [callV, hMin, hShort] using
                        finalize_preserves
                          (sOut := s1) (memoOut := memo1)
                          (out := I.partialPattern ctor argsV) hs1
                    · simpa [callV, hMin, hShort] using
                        afterDirectRule_preserves s1 memo1 argsV hs1
                | none =>
                    simpa [callV, hMin] using afterDirectRule_preserves s1 memo1 argsV hs1
            cases hCache : (if memoizable then detMemoLookup memo callRaw else none) with
            | some cached =>
                simpa [genericApplyBody, callRaw, memoizable, hCache] using hP
            | none =>
                cases hTranslated : I.translateCall s callRaw with
                | cons out translatedRest =>
                    simp [genericApplyBody, callRaw, memoizable, hCache, hTranslated]
                    by_cases hEq : out == callRaw
                    · have hEqOut : out = Pattern.apply ctor args := by
                        simpa [callRaw] using hEq
                      simpa [hEqOut] using
                        finalize_preserves (sOut := s) (memoOut := memo) (out := out) hP
                    · have hNeOut : ¬ out = callRaw := by
                        simpa using hEq
                      have hNeOut' : ¬ out = Pattern.apply ctor args := by
                        simpa [callRaw] using hNeOut
                      simpa [hNeOut'] using recursiveFinalize_preserves s memo out hP
                | nil =>
                    by_cases hPreserve : I.deterministicPreserveArgs ctor
                    · simpa [genericApplyBody, callRaw, memoizable, hCache, hTranslated, hPreserve] using
                        afterArgs_preserves s memo args hP
                    · have hArgs : P (evalArgs I s fuel memo args).1 := hArgsFuel s memo args hP
                      cases hEvalArgs : evalArgs I s fuel memo args with
                      | mk s1 rest1 =>
                          cases rest1 with
                          | mk memo1 argsV =>
                              have hs1 : P s1 := by
                                simpa [hEvalArgs] using hArgs
                              simpa [genericApplyBody, callRaw, memoizable, hCache, hTranslated, hPreserve, hEvalArgs] using
                                afterArgs_preserves s1 memo1 argsV hs1
          by_cases hCtorIf : ctor = "if"
          · subst hCtorIf
            cases args with
            | nil =>
                rw [evalMemo.eq_def]
                simpa [genericApplyBody] using genericApply "if" []
            | cons cond rest =>
                cases rest with
                | nil =>
                    rw [evalMemo.eq_def]
                    simpa [genericApplyBody] using genericApply "if" [cond]
                | cons thenBr rest =>
                    cases rest with
                    | nil =>
                        rw [evalMemo.eq_def]
                        simpa [genericApplyBody] using genericApply "if" [cond, thenBr]
                    | cons elseBr rest =>
                        cases rest with
                        | nil =>
                            have hCond : P (evalMemo I s fuel memo cond).1 := ih s memo cond hP
                            cases hEvalCond : evalMemo I s fuel memo cond with
                            | mk s1 rest1 =>
                                cases rest1 with
                                | mk memo1 condV =>
                                    have hs1 : P s1 := by
                                      simpa [hEvalCond] using hCond
                                    cases hBool : boolOfPattern? condV with
                                    | none =>
                                        rw [evalMemo.eq_def]
                                        simpa [hEvalCond, hBool] using hs1
                                    | some b =>
                                        cases b with
                                        | false =>
                                            rw [evalMemo.eq_def]
                                            simpa [hEvalCond, hBool] using
                                              ih s1 memo1 elseBr hs1
                                        | true =>
                                            rw [evalMemo.eq_def]
                                            simpa [hEvalCond, hBool] using
                                              ih s1 memo1 thenBr hs1
                        | cons extra rest =>
                            rw [evalMemo.eq_def]
                            simpa [genericApplyBody] using
                              genericApply "if" (cond :: thenBr :: elseBr :: extra :: rest)
          · by_cases hCtorExpr : ctor = "Expr"
            · subst hCtorExpr
              cases hTuple : I.evalTupleIntrinsic s args with
              | mk s1 out =>
                  have hs1 : P s1 := by
                    exact H.evalTupleIntrinsic_preserves hTuple hP
                  cases out with
                  | nil =>
                      rw [evalMemo.eq_def]
                      simpa [hTuple] using hs1
                  | cons one rest =>
                      by_cases hEq : one == .apply "Expr" args
                      · rw [evalMemo.eq_def]
                        simpa [hTuple, hEq] using hs1
                      · rw [evalMemo.eq_def]
                        simpa [hTuple, hEq] using ih s1 memo one hs1
            · rw [evalMemo.eq_def]
              simpa [genericApplyBody, hCtorIf, hCtorExpr] using genericApply ctor args

theorem evalArgs_preserves (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (fuel : Nat) (s : σ) (memo : DetMemo) (args : List Pattern) :
    P s → P (evalArgs I s fuel memo args).1 := by
  intro hP
  induction args generalizing s memo with
  | nil =>
      simpa [evalArgs.eq_def] using hP
  | cons a rest ih =>
      have hHead : P (evalMemo I s fuel memo a).1 :=
        evalMemo_preserves I P H fuel s memo a hP
      cases hEvalHead : evalMemo I s fuel memo a with
      | mk s1 rest1 =>
          cases rest1 with
          | mk memo1 aV =>
              have hs1 : P s1 := by
                simpa [hEvalHead] using hHead
              have hTail : P (evalArgs I s1 fuel memo1 rest).1 :=
                ih s1 memo1 hs1
              rw [evalArgs.eq_def]
              simpa [hEvalHead] using hTail

def eval (I : Interface σ) (s : σ) (fuel : Nat) (term : Pattern) : σ × Pattern :=
  let (s1, _, out) := evalMemo I s fuel [] term
  (s1, out)

theorem eval_preserves (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (fuel : Nat) (term : Pattern) :
    P s → P (eval I s fuel term).1 := by
  intro hP
  unfold eval
  simpa using evalMemo_preserves I P H fuel s [] term hP

-- ─── Result-shape lemmas ───────────────────────────────────────────────────

/-- `evalMemo` on a non-`.apply` term returns `(s, memo, term)` unchanged. -/
private theorem evalMemo_non_apply (I : Interface σ) (s : σ) (fuel : Nat)
    (memo : DetMemo) (term : Pattern)
    (hNonApply : ∀ ctor args, term ≠ .apply ctor args) :
    evalMemo I s fuel memo term = (s, memo, term) := by
  cases fuel with
  | zero => simp [evalMemo.eq_def]
  | succ fuel =>
      cases term with
      | fvar x => simp [evalMemo.eq_def]
      | bvar n => simp [evalMemo.eq_def]
      | lambda body => simp [evalMemo.eq_def]
      | multiLambda n body => simp [evalMemo.eq_def]
      | subst body repl => simp [evalMemo.eq_def]
      | collection ct elems rest => simp [evalMemo.eq_def]
      | apply ctor args => exact absurd rfl (hNonApply ctor args)

/-- `eval` on a non-`.apply` term returns `(s, term)` unchanged. -/
theorem eval_non_apply (I : Interface σ) (s : σ) (fuel : Nat)
    (term : Pattern)
    (hNonApply : ∀ ctor args, term ≠ .apply ctor args) :
    eval I s fuel term = (s, term) := by
  unfold eval
  rw [evalMemo_non_apply I s fuel [] term hNonApply]

/-- At zero fuel, `evalMemo` returns `(s, memo, term)` unchanged. -/
private theorem evalMemo_zero_fuel (I : Interface σ) (s : σ) (memo : DetMemo) (term : Pattern) :
    evalMemo I s 0 memo term = (s, memo, term) := by
  simp [evalMemo.eq_def]

/-- At zero fuel, `eval` returns `(s, term)` unchanged. -/
theorem eval_zero_fuel (I : Interface σ) (s : σ) (term : Pattern) :
    eval I s 0 term = (s, term) := by
  unfold eval
  rw [evalMemo_zero_fuel I s [] term]

-- ─── Phase 2-D: directIntrinsic branch theorem ──────────────────────────────

/-- `evalMemo` in the no-builtinMinArity direct-intrinsic branch:
    when translateCall is empty, args are preserved, builtinPartialMinArity = none,
    and intrinsicDirect returns a singleton [result] with result ≠ callV,
    the state and output of evalMemo equal those of recursing on result. -/
private theorem evalMemo_apply_directIntrinsic_eq
    (I : Interface σ) (s : σ) (fuel : Nat) (memo : DetMemo)
    (ctor : String) (argsV : List Pattern) (result : Pattern)
    (hMemoMiss : (if DeterministicStrategy.isMemoizableDeterministicCall (.apply ctor argsV)
                   then detMemoLookup memo (.apply ctor argsV) else none) = none)
    (hNotEq : ctor ≠ "=")
    -- evalMemo has special branches for "if" [a,b,c] and "Expr"; callers must avoid them
    (hNotIf : ctor ≠ "if")
    (hNotExpr : ctor ≠ "Expr")
    (hTranslate : I.translateCall s (.apply ctor argsV) = [])
    (hPreserveArgs : I.deterministicPreserveArgs ctor = true)
    (hArity : I.builtinPartialMinArity ctor = none)
    (hDirect : I.intrinsicDirect s ctor argsV = [result])
    (hNotSelf : result ≠ .apply ctor argsV) :
    (evalMemo I s (fuel + 1) memo (.apply ctor argsV)).1 =
      (evalMemo I s fuel memo result).1 ∧
    (evalMemo I s (fuel + 1) memo (.apply ctor argsV)).2.2 =
      (evalMemo I s fuel memo result).2.2 := by
  have hNotEqBEq : (ctor == "=") = false := beq_eq_false_iff_ne.mpr hNotEq
  have hbeq : (result == .apply ctor argsV) = false := beq_eq_false_iff_ne.mpr hNotSelf
  -- Project from the full evalMemo equality
  suffices hFull : evalMemo I s (fuel + 1) memo (.apply ctor argsV) =
      (let r := evalMemo I s fuel memo result
       let memoizable :=
         DeterministicStrategy.isMemoizableDeterministicCall (.apply ctor argsV)
       (r.1, if memoizable then detMemoInsert r.2.1 (.apply ctor argsV) r.2.2 (I.memoLimit r.1)
              else r.2.1, r.2.2)) by
    constructor <;> simp [hFull]
  -- Unfold evalMemo once; simp applies Nat ι-reduction; split cases on Pattern match.
  rw [evalMemo.eq_def]; simp only []
  split
  · -- "if" [a,b,c] branch: ctor must be "if", contradicts hNotIf
    rename_i a b c h
    simp only [Pattern.apply.injEq] at h
    exact absurd h.1 hNotIf
  · -- "Expr" elems branch: ctor must be "Expr", contradicts hNotExpr
    rename_i elems h
    simp only [Pattern.apply.injEq] at h
    exact absurd h.1 hNotExpr
  · -- generic .apply ctor✝ args✝ branch: split introduces
    --   term✝ : Pattern, ctor✝ : String, args✝ : List Pattern,
    --   x✝¹ (not-if), x✝ (not-Expr), heq✝ : Pattern.apply ctor argsV = .apply ctor✝ args✝
    rename_i _ c as _ _ heq
    simp only [Pattern.apply.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [hMemoMiss, hTranslate, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true,
               ite_false, hPreserveArgs, ite_true, hNotEqBEq, hArity, hDirect,
               List.headD_cons, List.isEmpty_cons, Bool.not_false, hbeq]
  · -- non-apply wildcard: impossible since term = .apply ctor argsV
    rename_i h
    simp [Pattern.apply.injEq] at h

/-- `eval` in the direct-intrinsic branch (starting from empty memo):
    when translateCall is empty, args are preserved, builtinPartialMinArity = none,
    and intrinsicDirect returns [result] ≠ callV,
    `eval` at fuel+1 on the call equals `eval` at fuel on the result. -/
theorem eval_apply_directIntrinsic_onestep
    (I : Interface σ) (s : σ) (fuel : Nat)
    (ctor : String) (argsV : List Pattern) (result : Pattern)
    (hNotEq : ctor ≠ "=")
    (hNotIf : ctor ≠ "if")
    (hNotExpr : ctor ≠ "Expr")
    (hTranslate : I.translateCall s (.apply ctor argsV) = [])
    (hPreserveArgs : I.deterministicPreserveArgs ctor = true)
    (hArity : I.builtinPartialMinArity ctor = none)
    (hDirect : I.intrinsicDirect s ctor argsV = [result])
    (hNotSelf : result ≠ .apply ctor argsV) :
    eval I s (fuel + 1) (.apply ctor argsV) = eval I s fuel result := by
  unfold eval
  have hMemoMiss : (if DeterministicStrategy.isMemoizableDeterministicCall (.apply ctor argsV)
                    then detMemoLookup [] (.apply ctor argsV) else none) = none := by
    simp [detMemoLookup]
  have h := evalMemo_apply_directIntrinsic_eq I s fuel [] ctor argsV result
    hMemoMiss hNotEq hNotIf hNotExpr hTranslate hPreserveArgs hArity hDirect hNotSelf
  exact Prod.ext h.1 h.2

/-- `evalMemo` in the unchanged branch: returns `(s, memo', .apply ctor argsV)`. -/
private theorem evalMemo_apply_unchanged_eq
    (I : Interface σ) (s : σ) (fuel : Nat) (memo : DetMemo)
    (ctor : String) (argsV : List Pattern)
    (hMemoMiss : (if DeterministicStrategy.isMemoizableDeterministicCall (.apply ctor argsV)
                   then detMemoLookup memo (.apply ctor argsV) else none) = none)
    (hNotEq : ctor ≠ "=")
    (hNotIf : ctor ≠ "if")
    (hNotExpr : ctor ≠ "Expr")
    (hTranslate : I.translateCall s (.apply ctor argsV) = [])
    (hPreserveArgs : I.deterministicPreserveArgs ctor = true)
    (hArity : I.builtinPartialMinArity ctor = none)
    (hDirect : I.intrinsicDirect s ctor argsV = [])
    (hNoRule : I.firstRuleReduction? s (.apply ctor argsV) = none)
    (hNoPartial :
      ¬((I.rewriteAritiesForHead s ctor).any (· > argsV.length) = true ∧
        (I.rewriteAritiesForHead s ctor).any (· == argsV.length) = false ∧
        argsV.isEmpty = false)) :
    (evalMemo I s (fuel + 1) memo (.apply ctor argsV)).1 = s ∧
    (evalMemo I s (fuel + 1) memo (.apply ctor argsV)).2.2 = .apply ctor argsV := by
  have hNotEqBEq : (ctor == "=") = false := beq_eq_false_iff_ne.mpr hNotEq
  rw [evalMemo.eq_def]; simp only []
  split
  · rename_i a b c h; simp only [Pattern.apply.injEq] at h; exact absurd h.1 hNotIf
  · rename_i elems h; simp only [Pattern.apply.injEq] at h; exact absurd h.1 hNotExpr
  · rename_i _ c as _ _ heq
    simp only [Pattern.apply.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp only [hMemoMiss, hTranslate, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true,
               ite_false, hPreserveArgs, ite_true, hNotEqBEq, hArity, hDirect,
               List.isEmpty_nil, hNoRule]
    -- After simp: goal is about the arity check fallthrough.
    -- hNoPartial says the triple conjunction is false.
    -- Case-split on each condition.
    -- The arity triple condition evaluates to false under hNoPartial
    suffices hCond :
        ((((I.rewriteAritiesForHead s ctor).any fun n => decide (n > argsV.length)) &&
            !((I.rewriteAritiesForHead s ctor).any fun n => n == argsV.length)) &&
            !argsV.isEmpty) = false by
      simp [hCond]
    by_cases hLarger : (I.rewriteAritiesForHead s ctor).any (· > argsV.length) = true
    · by_cases hExact : (I.rewriteAritiesForHead s ctor).any (· == argsV.length) = false
      · by_cases hNonEmpty : argsV.isEmpty = false
        · exact absurd ⟨hLarger, hExact, hNonEmpty⟩ hNoPartial
        · simp only [Bool.not_eq_false] at hNonEmpty; simp [hNonEmpty]
      · simp only [Bool.not_eq_false] at hExact; simp [hExact]
    · simp only [Bool.not_eq_true] at hLarger; simp [hLarger]
  · exact ⟨rfl, rfl⟩

/-- `eval` in the unchanged branch (starting from empty memo):
    when translateCall is empty, args are preserved, intrinsicDirect = [],
    firstRuleReduction? = none, and arity conditions don't trigger partial,
    `eval` returns the term unchanged. -/
theorem eval_apply_unchanged
    (I : Interface σ) (s : σ) (fuel : Nat)
    (ctor : String) (argsV : List Pattern)
    (hNotEq : ctor ≠ "=")
    (hNotIf : ctor ≠ "if")
    (hNotExpr : ctor ≠ "Expr")
    (hTranslate : I.translateCall s (.apply ctor argsV) = [])
    (hPreserveArgs : I.deterministicPreserveArgs ctor = true)
    (hArity : I.builtinPartialMinArity ctor = none)
    (hDirect : I.intrinsicDirect s ctor argsV = [])
    (hNoRule : I.firstRuleReduction? s (.apply ctor argsV) = none)
    (hNoPartial :
      ¬((I.rewriteAritiesForHead s ctor).any (· > argsV.length) = true ∧
        (I.rewriteAritiesForHead s ctor).any (· == argsV.length) = false ∧
        argsV.isEmpty = false)) :
    eval I s (fuel + 1) (.apply ctor argsV) = (s, .apply ctor argsV) := by
  unfold eval
  have hMemoMiss : (if DeterministicStrategy.isMemoizableDeterministicCall (.apply ctor argsV)
                    then detMemoLookup [] (.apply ctor argsV) else none) = none := by
    simp [detMemoLookup]
  have h := evalMemo_apply_unchanged_eq I s fuel [] ctor argsV
    hMemoMiss hNotEq hNotIf hNotExpr hTranslate hPreserveArgs hArity hDirect hNoRule hNoPartial
  exact Prod.ext h.1 h.2

end Algorithms.MeTTa.Simple.Semantics.DeterministicEval
