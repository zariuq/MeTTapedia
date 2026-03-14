import MeTTailCore

namespace Algorithms.MeTTa.Simple.Backend.ReferenceEval

open MeTTailCore.MeTTaIL.Syntax

structure Interface (σ : Type) where
  maxNodes : σ → Nat
  maxSteps : σ → Nat
  runNestedEffects : σ → Bool → Bool → Pattern → σ × Pattern × Bool
  intrinsicStateful : σ → Pattern → Option (σ × List Pattern)
  isEagerCallableHead : σ → String → Bool
  step : σ → Pattern → List Pattern
  enqueueNext : List (Pattern × Nat) → Nat → List Pattern → List (Pattern × Nat)
  insertUnique : List Pattern → Pattern → List Pattern
  dedupPatterns : List Pattern → List Pattern

structure AuxState (σ : Type) where
  s : σ
  fuel : Nat
  pending : List (Pattern × Nat)
  normals : List Pattern

abbrev AuxStepOut (σ : Type) := Sum (AuxState σ) (σ × List Pattern)

mutual
  def runNestedEffectsArgs (I : Interface σ) (s : σ) (parentCallable : Bool) :
      List Pattern → List Pattern → Bool → σ × List Pattern × Bool
    | [], accRev, changed => (s, accRev.reverse, changed)
    | a :: rest, accRev, changed =>
        let (s1, a', ch) := runNestedEffects I s false parentCallable a
        runNestedEffectsArgs I s1 parentCallable rest (a' :: accRev) (changed || ch)
  termination_by
    args => sizeOf args

  /-- Execute stateful intrinsics under a term before reducing the term itself. -/
  def runNestedEffects (I : Interface σ) (s : σ) (isRoot : Bool)
      (_parentCallable : Bool) : Pattern → σ × Pattern × Bool
    | .apply "let" [pat, val, body] =>
        (s, .apply "let" [pat, val, body], false)
    | .apply "let*" [binds, body] =>
        (s, .apply "let*" [binds, body], false)
    | .apply "quote" [q] =>
        (s, .apply "quote" [q], false)
    | .apply "add-atom" [space, fact] =>
        (s, .apply "add-atom" [space, fact], false)
    | .apply "add-atom!" [space, fact] =>
        (s, .apply "add-atom!" [space, fact], false)
    | .apply "remove-atom" [space, fact] =>
        (s, .apply "remove-atom" [space, fact], false)
    | .apply "remove-atom!" [space, fact] =>
        (s, .apply "remove-atom!" [space, fact], false)
    | .apply "remove-all-atoms" [space] =>
        (s, .apply "remove-all-atoms" [space], false)
    | .apply "remove-all-atoms!" [space] =>
        (s, .apply "remove-all-atoms!" [space], false)
    | .apply "get-atoms" [space] =>
        (s, .apply "get-atoms" [space], false)
    | .apply "get-atoms!" [space] =>
        (s, .apply "get-atoms!" [space], false)
    | .apply "bind!" [stateRef, valueExpr] =>
        (s, .apply "bind!" [stateRef, valueExpr], false)
    | .apply "change-state!" [stateRef, valueExpr] =>
        (s, .apply "change-state!" [stateRef, valueExpr], false)
    | .apply "get-state" [stateRef] =>
        (s, .apply "get-state" [stateRef], false)
    | .apply "with_mutex" [mutex, body] =>
        (s, .apply "with_mutex" [mutex, body], false)
    | .apply "transaction" [body] =>
        (s, .apply "transaction" [body], false)
    | .apply "import!" [space, path] =>
        (s, .apply "import!" [space, path], false)
    | .apply "import!" [space, path, opts] =>
        (s, .apply "import!" [space, path, opts], false)
    | .apply "call" args =>
        if isRoot then
          let (s1, args', changedArgs) := runNestedEffectsArgs I s true args [] false
          (s1, .apply "call" args', changedArgs)
        else
          match I.intrinsicStateful s (.apply "call" args) with
          | some (s1, out) =>
              let repl := out.headD (.apply "call" args)
              (s1, repl, true)
          | none =>
              let (s1, args', changedArgs) := runNestedEffectsArgs I s true args [] false
              (s1, .apply "call" args', changedArgs)
    | .apply "eval" args =>
        if isRoot then
          let (s1, args', changedArgs) := runNestedEffectsArgs I s true args [] false
          (s1, .apply "eval" args', changedArgs)
        else
          match I.intrinsicStateful s (.apply "eval" args) with
          | some (s1, out) =>
              let repl := out.headD (.apply "eval" args)
              (s1, repl, true)
          | none =>
              let (s1, args', changedArgs) := runNestedEffectsArgs I s true args [] false
              (s1, .apply "eval" args', changedArgs)
    | .apply "reduce" args =>
        if isRoot then
          let (s1, args', changedArgs) := runNestedEffectsArgs I s true args [] false
          (s1, .apply "reduce" args', changedArgs)
        else
          match I.intrinsicStateful s (.apply "reduce" args) with
          | some (s1, out) =>
              let repl := out.headD (.apply "reduce" args)
              (s1, repl, true)
          | none =>
              let (s1, args', changedArgs) := runNestedEffectsArgs I s true args [] false
              (s1, .apply "reduce" args', changedArgs)
    | .apply "chain" args =>
        if isRoot then
          let (s1, args', changedArgs) := runNestedEffectsArgs I s true args [] false
          (s1, .apply "chain" args', changedArgs)
        else
          match I.intrinsicStateful s (.apply "chain" args) with
          | some (s1, out) =>
              let repl := out.headD (.apply "chain" args)
              (s1, repl, true)
          | none =>
              let (s1, args', changedArgs) := runNestedEffectsArgs I s true args [] false
              (s1, .apply "chain" args', changedArgs)
    | .apply "match" args =>
        (s, .apply "match" args, false)
    | .apply "collapse" args =>
        if isRoot then
          (s, .apply "collapse" args, false)
        else
          match I.intrinsicStateful s (.apply "collapse" args) with
          | some (s1, out) =>
              let repl := out.headD (.apply "collapse" args)
              (s1, repl, true)
          | none =>
              (s, .apply "collapse" args, false)
    | .apply "superpose" args =>
        if isRoot then
          (s, .apply "superpose" args, false)
        else
          let (s1, args', changedArgs) := runNestedEffectsArgs I s false args [] false
          (s1, .apply "superpose" args', changedArgs)
    | .apply "msort" args =>
        if isRoot then
          (s, .apply "msort" args, false)
        else
          match I.intrinsicStateful s (.apply "msort" args) with
          | some (s1, out) =>
              let repl := out.headD (.apply "msort" args)
              (s1, repl, true)
          | none =>
              (s, .apply "msort" args, false)
    | .apply ctor args =>
        let currentCallable := I.isEagerCallableHead s ctor
        let (s1, args', changedArgs) := runNestedEffectsArgs I s currentCallable args [] false
        let term' := .apply ctor args'
        (s1, term', changedArgs)
    | .lambda body =>
        let (s1, body', changed) := runNestedEffects I s false false body
        (s1, .lambda body', changed)
    | .multiLambda n body =>
        let (s1, body', changed) := runNestedEffects I s false false body
        (s1, .multiLambda n body', changed)
    | .subst body repl =>
        let (s1, body', c1) := runNestedEffects I s false false body
        let (s2, repl', c2) := runNestedEffects I s1 false false repl
        (s2, .subst body' repl', c1 || c2)
    | .collection ct elems rest =>
        let (s1, elems', changed) := runNestedEffectsArgs I s false elems [] false
        (s1, .collection ct elems' rest, changed)
    | term =>
        (s, term, false)
  termination_by
    term => sizeOf term
end

structure Preservation (I : Interface σ) (P : σ → Prop) where
  runNestedEffects_preserves :
    ∀ {s : σ} {isRoot parentCallable : Bool} {term : Pattern}
      {s' : σ} {term' : Pattern} {changed : Bool},
      runNestedEffects I s isRoot parentCallable term = (s', term', changed) →
      P s → P s'
  intrinsicStateful_preserves :
    ∀ {s : σ} {term : Pattern} {s' : σ} {out : List Pattern},
      I.intrinsicStateful s term = some (s', out) →
      P s → P s'

private def preserveMultiplicityRoot (term0 : Pattern) : Bool :=
  match term0 with
  | .apply "let" _ => true
  | .apply "match" _ => true
  | .apply "foldall" _ => true
  | .apply "forall" _ => true
  | .apply "if" _ => true
  | .apply "case" _ => true
  | .apply "unique" _ => true
  | .apply "union" _ => true
  | .apply "intersection" _ => true
  | .apply "subtraction" _ => true
  | _ => false

def stepAux (I : Interface σ) (st : AuxState σ) : AuxStepOut σ :=
  match st.fuel with
  | 0 =>
      .inr (st.s, st.normals.reverse ++ st.pending.map Prod.fst)
  | fuel + 1 =>
      match st.pending with
      | [] =>
          .inr (st.s, st.normals.reverse)
      | (term, depth) :: rest =>
          let (s0, term0, _) := runNestedEffects I st.s true false term
          if depth >= I.maxSteps st.s then
            .inl { s := s0, fuel := fuel, pending := rest, normals := term0 :: st.normals }
          else
            match I.intrinsicStateful s0 term0 with
            | some (s1, intrinsicOut) =>
                let reducts :=
                  if preserveMultiplicityRoot term0 then
                    intrinsicOut
                  else
                    I.dedupPatterns intrinsicOut
                if reducts.isEmpty then
                  match term0 with
                  | .apply "Expr" _ =>
                      .inl { s := s1, fuel := fuel, pending := rest, normals := term0 :: st.normals }
                  | _ =>
                      .inl { s := s1, fuel := fuel, pending := rest, normals := st.normals }
                else
                  match term0 with
                  | .apply "if" _
                  | .apply "case" _
                  | .apply "unique" _
                  | .apply "union" _
                  | .apply "intersection" _
                  | .apply "subtraction" _ =>
                      -- Preserve multiplicity/order for control-flow and stream outputs.
                      .inl { s := s1, fuel := fuel, pending := rest, normals := reducts.reverse ++ st.normals }
                  | _ =>
                      let pending' := I.enqueueNext rest (depth + 1) reducts
                      .inl { s := s1, fuel := fuel, pending := pending', normals := st.normals }
            | none =>
                let reducts := I.step s0 term0
                if reducts.isEmpty then
                  .inl { s := s0, fuel := fuel, pending := rest, normals := term0 :: st.normals }
                else
                  let pending' := I.enqueueNext rest (depth + 1) reducts
                  .inl { s := s0, fuel := fuel, pending := pending', normals := st.normals }

/-- When `runNestedEffects` passes state through and `intrinsicStateful` returns
    `some (s, out)` (same state), every branch of `stepAux` preserves `.s`. -/
theorem stepAux_s_eq_of_passthrough
    (I : Interface σ) (s : σ) (term term' : Pattern) (changed : Bool) (out : List Pattern)
    (fuel depth : Nat) (rest : List (Pattern × Nat)) (normals : List Pattern)
    (hRNE : runNestedEffects I s true false term = (s, term', changed))
    (hIntr : I.intrinsicStateful s term' = some (s, out)) :
    match stepAux I ⟨s, fuel + 1, (term, depth) :: rest, normals⟩ with
    | .inl st' => st'.s = s
    | .inr out' => out'.1 = s := by
  simp only [stepAux, hRNE, hIntr]
  split
  all_goals rename_i _ _ heq
  all_goals
    split at heq <;> (try split at heq) <;> (try split at heq) <;> (try split at heq)
    <;> simp at heq <;> (try subst heq) <;> rfl

theorem stepAux_preserves (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (st : AuxState σ) :
    P st.s →
    match stepAux I st with
    | .inl st' => P st'.s
    | .inr out => P out.1 := by
  intro hP
  cases hFuel : st.fuel with
  | zero =>
      simp [stepAux, hFuel, hP]
  | succ fuel =>
      cases hPending : st.pending with
      | nil =>
          simp [stepAux, hFuel, hPending, hP]
      | cons hd rest =>
          rcases hd with ⟨term, depth⟩
          cases hRun : runNestedEffects I st.s true false term with
          | mk s0 rest0 =>
              cases rest0 with
              | mk term0 changed =>
                  have hRunPres : P s0 := H.runNestedEffects_preserves hRun hP
                  by_cases hDepth : depth >= I.maxSteps st.s
                  · simp [stepAux, hFuel, hPending, hRun, hDepth, hRunPres]
                  · cases hIntr : I.intrinsicStateful s0 term0 with
                    | none =>
                        cases hRed : I.step s0 term0 <;>
                          simp [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hRed, hRunPres]
                    | some out =>
                        have hIntrPres : P out.1 :=
                          H.intrinsicStateful_preserves hIntr hRunPres
                        by_cases hReducts :
                            (if preserveMultiplicityRoot term0 then out.2 else I.dedupPatterns out.2) = []
                        · cases term0 with
                          | fvar x =>
                              simp [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts, hIntrPres]
                          | bvar n =>
                              simp [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts, hIntrPres]
                          | apply ctor args =>
                              by_cases hExpr : ctor = "Expr"
                              · subst ctor
                                simpa [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts] using hIntrPres
                              · simpa [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts, hExpr] using hIntrPres
                          | lambda body =>
                              simp [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts, hIntrPres]
                          | multiLambda n body =>
                              simp [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts, hIntrPres]
                          | subst body repl =>
                              simp [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts, hIntrPres]
                          | collection ct elems restTail =>
                              simp [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts, hIntrPres]
                        · cases term0 with
                          | fvar x =>
                              simp [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts, hIntrPres]
                          | bvar n =>
                              simp [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts, hIntrPres]
                          | apply ctor args =>
                              by_cases hIf : ctor = "if"
                              · subst ctor
                                simpa [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts] using hIntrPres
                              · by_cases hCase : ctor = "case"
                                · subst ctor
                                  simpa [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts] using hIntrPres
                                · by_cases hUnique : ctor = "unique"
                                  · subst ctor
                                    simpa [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts] using hIntrPres
                                  · by_cases hUnion : ctor = "union"
                                    · subst ctor
                                      simpa [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts] using hIntrPres
                                    · by_cases hIntersection : ctor = "intersection"
                                      · subst ctor
                                        simpa [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts] using hIntrPres
                                      · by_cases hSubtraction : ctor = "subtraction"
                                        · subst ctor
                                          simpa [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts] using hIntrPres
                                        · simpa [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts, hIf, hCase, hUnique, hUnion, hIntersection, hSubtraction] using hIntrPres
                          | lambda body =>
                              simp [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts, hIntrPres]
                          | multiLambda n body =>
                              simp [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts, hIntrPres]
                          | subst body repl =>
                              simp [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts, hIntrPres]
                          | collection ct elems restTail =>
                              simp [stepAux, hFuel, hPending, hRun, hDepth, hIntr, hReducts, hIntrPres]

mutual
  def evalAuxStateful (I : Interface σ) (s : σ) (fuel : Nat)
      (pending : List (Pattern × Nat)) (normals : List Pattern) : σ × List Pattern :=
    match fuel with
    | 0 => (s, normals.reverse ++ pending.map Prod.fst)
    | fuel + 1 =>
        match stepAux I { s := s, fuel := fuel + 1, pending := pending, normals := normals } with
        | .inr out =>
            out
        | .inl st' =>
            evalAuxStateful I st'.s fuel st'.pending st'.normals

  def evalWithStateCore (I : Interface σ) (s : σ) (term : Pattern) : σ × List Pattern :=
    evalAuxStateful I s (I.maxNodes s) [(term, 0)] []
end

theorem evalAuxStateful_preserves (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (fuel : Nat) (pending : List (Pattern × Nat)) (normals : List Pattern) :
    P s → P (evalAuxStateful I s fuel pending normals).1 := by
  intro hP
  induction fuel generalizing s pending normals with
  | zero =>
      simpa [evalAuxStateful] using hP
  | succ fuel ih =>
      have hStep :
          match stepAux I { s := s, fuel := fuel + 1, pending := pending, normals := normals } with
          | .inl st' => P st'.s
          | .inr out => P out.1 :=
        stepAux_preserves I P H { s := s, fuel := fuel + 1, pending := pending, normals := normals } hP
      simp [evalAuxStateful]
      cases hOut : stepAux I { s := s, fuel := fuel + 1, pending := pending, normals := normals } with
      | inl st' =>
          simp [hOut] at hStep
          simpa [hOut] using ih st'.s st'.pending st'.normals hStep
      | inr out =>
          simpa [hOut] using hStep

theorem evalWithStateCore_preserves (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (term : Pattern) :
    P s → P (evalWithStateCore I s term).1 := by
  simpa [evalWithStateCore] using
    evalAuxStateful_preserves I P H s (I.maxNodes s) [(term, 0)] []

/-- When `maxNodes = 1` and both `runNestedEffects` and `intrinsicStateful` pass state
    through, the one-step evaluator preserves state.  Composes `stepAux_s_eq_of_passthrough`
    with the `evalAuxStateful` loop at fuel 1 (one iteration → fuel 0 base case). -/
theorem evalWithStateCore_s_eq_of_passthrough_one_step
    (I : Interface σ) (s : σ) (term : Pattern) (hNodes : I.maxNodes s = 1)
    (term' : Pattern) (changed : Bool) (out : List Pattern)
    (hRNE : runNestedEffects I s true false term = (s, term', changed))
    (hIntr : I.intrinsicStateful s term' = some (s, out)) :
    (evalWithStateCore I s term).1 = s := by
  simp only [evalWithStateCore, hNodes]
  have hPass := stepAux_s_eq_of_passthrough I s term term' changed out 0 0 [] [] hRNE hIntr
  simp only [evalAuxStateful]
  cases h : stepAux I { s := s, fuel := 1, pending := [(term, 0)], normals := [] } with
  | inl st' =>
      simp only [h] at hPass
      simp only [hPass]
  | inr out' =>
      simp only [h] at hPass
      exact hPass

-- ─── Phase 2-D exact control lemmas ────────────────────────────────────────

/-- One-step unfolding of `evalAuxStateful` when `intrinsicStateful` returns `none`:
    takes one iteration of the work-queue loop, reducing via `I.step`. -/
theorem evalAuxStateful_step_of_intrinsicNone
    (I : Interface σ) (s s0 : σ) (term term0 : Pattern) (changed : Bool) (depth : Nat)
    (rest : List (Pattern × Nat)) (normals : List Pattern) (fuel : Nat)
    (hRNE : runNestedEffects I s true false term = (s0, term0, changed))
    (hDepth : depth < I.maxSteps s)
    (hIntr : I.intrinsicStateful s0 term0 = none) :
    evalAuxStateful I s (fuel + 1) ((term, depth) :: rest) normals =
    let reducts := I.step s0 term0
    if reducts.isEmpty then
      evalAuxStateful I s0 fuel rest (term0 :: normals)
    else
      evalAuxStateful I s0 fuel (I.enqueueNext rest (depth + 1) reducts) normals := by
  have hNotDepth : ¬(depth ≥ I.maxSteps s) := by omega
  simp only [evalAuxStateful, stepAux, hRNE, if_neg hNotDepth, hIntr]
  cases (I.step s0 term0).isEmpty <;> simp

def evalSequenceStateful (I : Interface σ) (s : σ)
    (terms : List Pattern) (acc : List Pattern) : σ × List Pattern :=
  match terms with
  | [] => (s, acc)
  | t :: ts =>
      let (s1, out) := evalWithStateCore I s t
      evalSequenceStateful I s1 ts (acc ++ out)

theorem evalSequenceStateful_preserves (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (terms : List Pattern) (acc : List Pattern) :
    P s → P (evalSequenceStateful I s terms acc).1 := by
  intro hP
  induction terms generalizing s acc with
  | nil =>
      simpa [evalSequenceStateful] using hP
  | cons t ts ih =>
      let out := evalWithStateCore I s t
      have h1 : P out.1 := evalWithStateCore_preserves I P H s t hP
      simpa [evalSequenceStateful, out] using ih out.1 (acc ++ out.2) h1

theorem runNestedEffectsArgs_preserves_of_runNestedEffects
    (I : Interface σ) (P : σ → Prop)
    (hRunNestedEffectsPres :
      ∀ (s : σ) (isRoot parentCallable : Bool) (term : Pattern),
        P s →
        P (runNestedEffects I s isRoot parentCallable term).1)
    (s : σ) (parentCallable : Bool)
    (args accRev : List Pattern) (changed : Bool) :
    P s → P (runNestedEffectsArgs I s parentCallable args accRev changed).1 := by
  intro hP
  induction args generalizing s accRev changed with
  | nil =>
      simpa [runNestedEffectsArgs] using hP
  | cons a rest ih =>
      have hRun : P (runNestedEffects I s false parentCallable a).1 :=
        hRunNestedEffectsPres s false parentCallable a hP
      cases hStep : runNestedEffects I s false parentCallable a with
      | mk s1 rest1 =>
          cases rest1 with
          | mk a' ch =>
              have hS1 : P s1 := by
                simpa [hStep] using hRun
              simpa [runNestedEffectsArgs, hStep] using
                ih s1 (a' :: accRev) (changed || ch) hS1

private theorem sizeOf_lt_of_mem_applyArgs
    (ctor : String) (args : List Pattern) (a : Pattern)
    (ha : a ∈ args) :
    sizeOf a < sizeOf (Pattern.apply ctor args) := by
  have hmem := List.sizeOf_lt_of_mem ha
  simp_wf
  omega

private theorem sizeOf_lt_of_mem_collectionElems
    (ct : CollType) (elems : List Pattern) (rest : Option String) (a : Pattern)
    (ha : a ∈ elems) :
    sizeOf a < sizeOf (Pattern.collection ct elems rest) := by
  have hmem := List.sizeOf_lt_of_mem ha
  simp_wf
  omega

private theorem sizeOf_body_lt_lambda (body : Pattern) :
    sizeOf body < sizeOf (Pattern.lambda body) := by
  simp_wf

private theorem sizeOf_body_lt_multiLambda (n : Nat) (body : Pattern) :
    sizeOf body < sizeOf (Pattern.multiLambda n body) := by
  simp_wf
  omega

private theorem sizeOf_body_lt_subst (body repl : Pattern) :
    sizeOf body < sizeOf (Pattern.subst body repl) := by
  simp_wf
  omega

private theorem sizeOf_repl_lt_subst (body repl : Pattern) :
    sizeOf repl < sizeOf (Pattern.subst body repl) := by
  simp_wf
  omega

/-- `runNestedEffectsArgs` depends only on `I.intrinsicStateful` and `I.isEagerCallableHead`. -/
private theorem runNestedEffectsArgs_ext_of_lt {σ : Type}
    (I1 I2 : Interface σ)
    (_h_intr : I1.intrinsicStateful = I2.intrinsicStateful)
    (_h_eager : I1.isEagerCallableHead = I2.isEagerCallableHead)
    (bound : Nat)
    (hRunExt :
      ∀ (s : σ) (isRoot parentCallable : Bool) (term : Pattern),
        sizeOf term < bound →
        runNestedEffects I1 s isRoot parentCallable term =
        runNestedEffects I2 s isRoot parentCallable term)
    (args : List Pattern)
    (hSmall : ∀ a, a ∈ args → sizeOf a < bound)
    (s : σ) (parentCallable : Bool) (accRev : List Pattern) (changed : Bool) :
    runNestedEffectsArgs I1 s parentCallable args accRev changed =
    runNestedEffectsArgs I2 s parentCallable args accRev changed := by
  induction args generalizing s accRev changed with
  | nil => simp [runNestedEffectsArgs]
  | cons a rest ih =>
      have hRunEq : runNestedEffects I1 s false parentCallable a =
                    runNestedEffects I2 s false parentCallable a :=
        hRunExt s false parentCallable a (hSmall a (by simp))
      cases hStep : runNestedEffects I2 s false parentCallable a with
      | mk s1 rest1 =>
          cases rest1 with
          | mk a' ch =>
              have hStep1 : runNestedEffects I1 s false parentCallable a = (s1, a', ch) := by
                rw [hRunEq]; exact hStep
              have hSmallRest : ∀ b, b ∈ rest → sizeOf b < bound := by
                intro b hb; exact hSmall b (by simp [hb])
              simp only [runNestedEffectsArgs, hStep, hStep1]
              exact ih hSmallRest s1 (a' :: accRev) (changed || ch)

-- Helper for the apply-ctor case of runNestedEffects_ext.
-- Proves equality by explicit by_cases on ctor, mirroring runNestedEffectsApply_preserves_local.
-- This proof has many by_cases guards passed to simp where only some are needed per branch.
set_option linter.unusedSimpArgs false in
private theorem runNestedEffectsApply_ext_local {σ : Type}
    (I1 I2 : Interface σ)
    (h_intr : I1.intrinsicStateful = I2.intrinsicStateful)
    (h_eager : I1.isEagerCallableHead = I2.isEagerCallableHead)
    (s : σ) (isRoot parentCallable : Bool) (ctor : String) (args : List Pattern)
    (hArgsTrue : runNestedEffectsArgs I1 s true args [] false =
                 runNestedEffectsArgs I2 s true args [] false)
    (hArgsFalse : runNestedEffectsArgs I1 s false args [] false =
                  runNestedEffectsArgs I2 s false args [] false)
    (hArgsCurrent : runNestedEffectsArgs I1 s (I2.isEagerCallableHead s ctor) args [] false =
                    runNestedEffectsArgs I2 s (I2.isEagerCallableHead s ctor) args [] false) :
    runNestedEffects I1 s isRoot parentCallable (.apply ctor args) =
    runNestedEffects I2 s isRoot parentCallable (.apply ctor args) := by
  have h_eager_ctor : I1.isEagerCallableHead s ctor = I2.isEagerCallableHead s ctor := by
    rw [h_eager]
  -- Close both sides at (s', term', ch) via cases on the resolved generic result
  by_cases hCall : ctor = "call"
  · subst hCall
    simp only [runNestedEffects.eq_def, h_intr, hArgsTrue]
  · by_cases hEval : ctor = "eval"
    · subst hEval
      simp only [runNestedEffects.eq_def, hCall, h_intr, hArgsTrue]
    · by_cases hReduce : ctor = "reduce"
      · subst hReduce
        simp only [runNestedEffects.eq_def, hCall, hEval, h_intr, hArgsTrue]
      · by_cases hChain : ctor = "chain"
        · subst hChain
          simp only [runNestedEffects.eq_def, hCall, hEval, hReduce, h_intr, hArgsTrue]
        · by_cases hMatch : ctor = "match"
          · subst hMatch
            simp [runNestedEffects.eq_def]
          · by_cases hCollapse : ctor = "collapse"
            · subst hCollapse
              simp only [runNestedEffects.eq_def, hCall, hEval, hReduce, hChain, hMatch, h_intr]
            · by_cases hSuperpose : ctor = "superpose"
              · subst hSuperpose
                simp only [runNestedEffects.eq_def, hCall, hEval, hReduce, hChain, hMatch,
                  hCollapse, hArgsFalse]
              · by_cases hMsort : ctor = "msort"
                · subst hMsort
                  simp only [runNestedEffects.eq_def, hCall, hEval, hReduce, hChain, hMatch,
                    hCollapse, hSuperpose, h_intr]
                · cases args with
                  | nil =>
                      simp only [runNestedEffects.eq_def, hCall, hEval, hReduce, hChain, hMatch,
                        hCollapse, hSuperpose, hMsort, h_eager_ctor, hArgsCurrent]
                  | cons a as =>
                      cases as with
                      | nil =>
                          by_cases hQuote : ctor = "quote"
                          · subst hQuote; simp [runNestedEffects.eq_def]
                          · by_cases hRemoveAll : ctor = "remove-all-atoms"
                            · subst hRemoveAll; simp [runNestedEffects.eq_def]
                            · by_cases hRemoveAllBang : ctor = "remove-all-atoms!"
                              · subst hRemoveAllBang; simp [runNestedEffects.eq_def]
                              · by_cases hGetAtoms : ctor = "get-atoms"
                                · subst hGetAtoms; simp [runNestedEffects.eq_def]
                                · by_cases hGetAtomsBang : ctor = "get-atoms!"
                                  · subst hGetAtomsBang; simp [runNestedEffects.eq_def]
                                  · by_cases hGetState : ctor = "get-state"
                                    · subst hGetState; simp [runNestedEffects.eq_def]
                                    · by_cases hTransaction : ctor = "transaction"
                                      · subst ctor; simp [runNestedEffects.eq_def]
                                      · rw [runNestedEffects.eq_def, runNestedEffects.eq_def]
                                        simp [hCall, hEval, hReduce, hChain, hMatch, hCollapse,
                                          hSuperpose, hMsort, hQuote, hRemoveAll, hRemoveAllBang,
                                          hGetAtoms, hGetAtomsBang, hGetState, hTransaction,
                                          h_eager_ctor, hArgsCurrent]
                      | cons b bs =>
                          cases bs with
                          | nil =>
                              by_cases hLetStar : ctor = "let*"
                              · subst hLetStar; simp [runNestedEffects.eq_def]
                              · by_cases hAddAtom : ctor = "add-atom"
                                · subst hAddAtom; simp [runNestedEffects.eq_def]
                                · by_cases hAddAtomBang : ctor = "add-atom!"
                                  · subst hAddAtomBang; simp [runNestedEffects.eq_def]
                                  · by_cases hRemoveAtom : ctor = "remove-atom"
                                    · subst hRemoveAtom; simp [runNestedEffects.eq_def]
                                    · by_cases hRemoveAtomBang : ctor = "remove-atom!"
                                      · subst hRemoveAtomBang; simp [runNestedEffects.eq_def]
                                      · by_cases hBindBang : ctor = "bind!"
                                        · subst hBindBang; simp [runNestedEffects.eq_def]
                                        · by_cases hChangeState : ctor = "change-state!"
                                          · subst hChangeState; simp [runNestedEffects.eq_def]
                                          · by_cases hWithMutex : ctor = "with_mutex"
                                            · subst hWithMutex; simp [runNestedEffects.eq_def]
                                            · by_cases hImport : ctor = "import!"
                                              · subst ctor; simp [runNestedEffects.eq_def]
                                              · rw [runNestedEffects.eq_def, runNestedEffects.eq_def]
                                                simp [hCall, hEval,
                                                  hReduce, hChain, hMatch, hCollapse, hSuperpose,
                                                  hMsort, hLetStar, hAddAtom, hAddAtomBang,
                                                  hRemoveAtom, hRemoveAtomBang, hBindBang,
                                                  hChangeState, hWithMutex, hImport,
                                                  h_eager_ctor, hArgsCurrent]
                          | cons c cs =>
                              cases cs with
                              | nil =>
                                  by_cases hLet : ctor = "let"
                                  · subst hLet; simp [runNestedEffects.eq_def]
                                  · by_cases hImport : ctor = "import!"
                                    · subst ctor; simp [runNestedEffects.eq_def]
                                    · rw [runNestedEffects.eq_def, runNestedEffects.eq_def]
                                      simp [hCall, hEval, hReduce, hChain, hMatch, hCollapse,
                                        hMsort, hLet, hImport,
                                        h_eager_ctor, hArgsCurrent]
                              | cons d ds =>
                                  rw [runNestedEffects.eq_def, runNestedEffects.eq_def]
                                  simp [hCall, hEval, hReduce, hChain,
                                    h_eager_ctor, hArgsCurrent]

/-- `runNestedEffects` depends only on `I.intrinsicStateful` and `I.isEagerCallableHead`;
    the `I.runNestedEffects` field is never called. -/
theorem runNestedEffects_ext {σ : Type}
    (I1 I2 : Interface σ)
    (h_intr : I1.intrinsicStateful = I2.intrinsicStateful)
    (h_eager : I1.isEagerCallableHead = I2.isEagerCallableHead) :
    ∀ (s : σ) (isRoot parentCallable : Bool) (term : Pattern),
      runNestedEffects I1 s isRoot parentCallable term =
      runNestedEffects I2 s isRoot parentCallable term := by
  have hMain :
      ∀ n, ∀ (s : σ) (isRoot parentCallable : Bool) (term : Pattern),
        sizeOf term ≤ n →
        runNestedEffects I1 s isRoot parentCallable term =
        runNestedEffects I2 s isRoot parentCallable term := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
        intro s isRoot parentCallable term hSize
        cases term with
        | fvar x => simp [runNestedEffects.eq_def]
        | bvar x => simp [runNestedEffects.eq_def]
        | apply ctor args =>
            have hRunLt :
                ∀ (s : σ) (isRoot parentCallable : Bool) (term : Pattern),
                  sizeOf term < sizeOf (Pattern.apply ctor args) →
                  runNestedEffects I1 s isRoot parentCallable term =
                  runNestedEffects I2 s isRoot parentCallable term := fun s' ir pc t hLt =>
              ih (sizeOf t) (Nat.lt_of_lt_of_le hLt hSize) s' ir pc t (Nat.le_refl _)
            have hArgsTrue :=
              runNestedEffectsArgs_ext_of_lt I1 I2 h_intr h_eager
                (sizeOf (Pattern.apply ctor args)) hRunLt
                args (sizeOf_lt_of_mem_applyArgs ctor args) s true [] false
            have hArgsFalse :=
              runNestedEffectsArgs_ext_of_lt I1 I2 h_intr h_eager
                (sizeOf (Pattern.apply ctor args)) hRunLt
                args (sizeOf_lt_of_mem_applyArgs ctor args) s false [] false
            have hArgsCurrent :=
              runNestedEffectsArgs_ext_of_lt I1 I2 h_intr h_eager
                (sizeOf (Pattern.apply ctor args)) hRunLt
                args (sizeOf_lt_of_mem_applyArgs ctor args)
                s (I2.isEagerCallableHead s ctor) [] false
            exact runNestedEffectsApply_ext_local I1 I2 h_intr h_eager s isRoot parentCallable
              ctor args hArgsTrue hArgsFalse hArgsCurrent
        | lambda body =>
            have hBody :=
              ih (sizeOf body) (Nat.lt_of_lt_of_le (sizeOf_body_lt_lambda body) hSize)
                s false false body (Nat.le_refl _)
            cases hStep : runNestedEffects I2 s false false body with
            | mk s1 rest1 =>
                cases rest1 with
                | mk body' changed =>
                    have hStep1 : runNestedEffects I1 s false false body = (s1, body', changed) :=
                      by rw [hBody]; exact hStep
                    rw [show runNestedEffects I1 s isRoot parentCallable (.lambda body) =
                              (s1, .lambda body', changed) by
                          rw [runNestedEffects.eq_def]; simp [hStep1]]
                    rw [show runNestedEffects I2 s isRoot parentCallable (.lambda body) =
                              (s1, .lambda body', changed) by
                          rw [runNestedEffects.eq_def]; simp [hStep]]
        | multiLambda n body =>
            have hBody :=
              ih (sizeOf body) (Nat.lt_of_lt_of_le (sizeOf_body_lt_multiLambda n body) hSize)
                s false false body (Nat.le_refl _)
            cases hStep : runNestedEffects I2 s false false body with
            | mk s1 rest1 =>
                cases rest1 with
                | mk body' changed =>
                    have hStep1 : runNestedEffects I1 s false false body = (s1, body', changed) :=
                      by rw [hBody]; exact hStep
                    rw [show runNestedEffects I1 s isRoot parentCallable (.multiLambda n body) =
                              (s1, .multiLambda n body', changed) by
                          rw [runNestedEffects.eq_def]; simp [hStep1]]
                    rw [show runNestedEffects I2 s isRoot parentCallable (.multiLambda n body) =
                              (s1, .multiLambda n body', changed) by
                          rw [runNestedEffects.eq_def]; simp [hStep]]
        | subst body repl =>
            have hBody :=
              ih (sizeOf body) (Nat.lt_of_lt_of_le (sizeOf_body_lt_subst body repl) hSize)
                s false false body (Nat.le_refl _)
            cases hStep1 : runNestedEffects I2 s false false body with
            | mk s1 rest1 =>
                cases rest1 with
                | mk body' c1 =>
                    have hStep1Eq : runNestedEffects I1 s false false body = (s1, body', c1) :=
                      by rw [hBody]; exact hStep1
                    have hRepl :=
                      ih (sizeOf repl) (Nat.lt_of_lt_of_le (sizeOf_repl_lt_subst body repl) hSize)
                        s1 false false repl (Nat.le_refl _)
                    cases hStep2 : runNestedEffects I2 s1 false false repl with
                    | mk s2 rest2 =>
                        cases rest2 with
                        | mk repl' c2 =>
                            have hStep2Eq :
                                runNestedEffects I1 s1 false false repl = (s2, repl', c2) :=
                              by rw [hRepl]; exact hStep2
                            rw [show runNestedEffects I1 s isRoot parentCallable
                                        (.subst body repl) = (s2, .subst body' repl', c1 || c2) by
                                  rw [runNestedEffects.eq_def]; simp [hStep1Eq, hStep2Eq]]
                            rw [show runNestedEffects I2 s isRoot parentCallable
                                        (.subst body repl) = (s2, .subst body' repl', c1 || c2) by
                                  rw [runNestedEffects.eq_def]; simp [hStep1, hStep2]]
        | collection ct elems rest =>
            have hArgsEq :=
              runNestedEffectsArgs_ext_of_lt I1 I2 h_intr h_eager
                (sizeOf (Pattern.collection ct elems rest))
                (fun s' ir pc t hLt =>
                  ih (sizeOf t) (Nat.lt_of_lt_of_le hLt hSize)
                    s' ir pc t (Nat.le_refl _))
                elems (sizeOf_lt_of_mem_collectionElems ct elems rest) s false [] false
            cases hStep : runNestedEffectsArgs I2 s false elems [] false with
            | mk s1 rest1 =>
                cases rest1 with
                | mk elems' changed =>
                    have hStepEq :
                        runNestedEffectsArgs I1 s false elems [] false = (s1, elems', changed) :=
                      by rw [hArgsEq]; exact hStep
                    rw [show runNestedEffects I1 s isRoot parentCallable
                                (.collection ct elems rest) = (s1, .collection ct elems' rest, changed) by
                          rw [runNestedEffects.eq_def]; simp [hStepEq]]
                    rw [show runNestedEffects I2 s isRoot parentCallable
                                (.collection ct elems rest) = (s1, .collection ct elems' rest, changed) by
                          rw [runNestedEffects.eq_def]; simp [hStep]]
  intro s isRoot parentCallable term
  exact hMain (sizeOf term) s isRoot parentCallable term (Nat.le_refl _)

theorem runNestedEffectsArgs_ext {σ : Type}
    (I1 I2 : Interface σ)
    (h_intr : I1.intrinsicStateful = I2.intrinsicStateful)
    (h_eager : I1.isEagerCallableHead = I2.isEagerCallableHead)
    (s : σ) (pc : Bool) (args accRev : List Pattern) (changed : Bool) :
    runNestedEffectsArgs I1 s pc args accRev changed =
    runNestedEffectsArgs I2 s pc args accRev changed := by
  induction args generalizing s accRev changed with
  | nil => simp [runNestedEffectsArgs]
  | cons a rest ih =>
      have hRunEq := runNestedEffects_ext I1 I2 h_intr h_eager s false pc a
      cases hStep : runNestedEffects I2 s false pc a with
      | mk s1 rest1 =>
          cases rest1 with
          | mk a' ch =>
              have hStep1 : runNestedEffects I1 s false pc a = (s1, a', ch) := by
                rw [hRunEq]; exact hStep
              simp only [runNestedEffectsArgs, hStep, hStep1]
              exact ih s1 (a' :: accRev) (changed || ch)

private theorem runNestedEffectsArgs_preserves_of_lt
    (I : Interface σ) (P : σ → Prop)
    (bound : Nat)
    (hRunLt :
      ∀ (s : σ) (isRoot parentCallable : Bool) (term : Pattern),
        sizeOf term < bound →
        P s → P ((runNestedEffects I s isRoot parentCallable term).1))
    (args : List Pattern)
    (hSmall : ∀ a, a ∈ args → sizeOf a < bound)
    (s : σ) (parentCallable : Bool)
    (accRev : List Pattern) (changed : Bool) :
    P s → P ((runNestedEffectsArgs I s parentCallable args accRev changed).1) := by
  intro hP
  induction args generalizing s accRev changed with
  | nil =>
      simpa [runNestedEffectsArgs] using hP
  | cons a rest ih =>
      have hRun : P ((runNestedEffects I s false parentCallable a).1) :=
        hRunLt s false parentCallable a (hSmall a (by simp)) hP
      cases hStep : runNestedEffects I s false parentCallable a with
      | mk s1 rest1 =>
          cases rest1 with
          | mk a' ch =>
              have hS1 : P s1 := by
                simpa [hStep] using hRun
              have hSmallRest : ∀ b, b ∈ rest → sizeOf b < bound := by
                intro b hb
                exact hSmall b (by simp [hb])
              simpa [runNestedEffectsArgs, hStep] using
                ih hSmallRest s1 (a' :: accRev) (changed || ch) hS1

private theorem preserve_intrinsic_or_args
    (I : Interface σ) (P : σ → Prop)
    (hIntrinsicPres :
      ∀ {s : σ} {term : Pattern} {s' : σ} {out : List Pattern},
        I.intrinsicStateful s term = some (s', out) →
        P s → P s')
    (head : String) (s : σ) (isRoot : Bool) (args : List Pattern)
    (hArgs : P ((runNestedEffectsArgs I s true args [] false).1))
    (hP : P s) :
    (let out :=
      if isRoot then
        let (s1, args', changedArgs) := runNestedEffectsArgs I s true args [] false
        (s1, .apply head args', changedArgs)
      else
        match I.intrinsicStateful s (.apply head args) with
        | some (s1, out) =>
            let repl := out.headD (.apply head args)
            (s1, repl, true)
        | none =>
            let (s1, args', changedArgs) := runNestedEffectsArgs I s true args [] false
            (s1, .apply head args', changedArgs)
      P out.1) := by
  cases isRoot with
  | false =>
      simp
      cases h : I.intrinsicStateful s (.apply head args) with
      | none =>
          simpa [h] using hArgs
      | some out =>
          exact hIntrinsicPres h hP
  | true =>
      simpa

private theorem preserve_intrinsic_or_original
    (I : Interface σ) (P : σ → Prop)
    (hIntrinsicPres :
      ∀ {s : σ} {term : Pattern} {s' : σ} {out : List Pattern},
        I.intrinsicStateful s term = some (s', out) →
        P s → P s')
    (head : String) (s : σ) (isRoot : Bool) (args : List Pattern)
    (hP : P s) :
    (let out :=
      if isRoot then
        (s, .apply head args, false)
      else
        match I.intrinsicStateful s (.apply head args) with
        | some (s1, out) =>
            let repl := out.headD (.apply head args)
            (s1, repl, true)
        | none =>
            (s, .apply head args, false)
      P out.1) := by
  cases isRoot with
  | false =>
      simp
      cases h : I.intrinsicStateful s (.apply head args) with
      | none =>
      simpa [h] using hP
      | some out =>
          exact hIntrinsicPres h hP
  | true =>
      simpa

private theorem runNestedEffectsApply_preserves_local
    (I : Interface σ) (P : σ → Prop)
    (hIntrinsicPres :
      ∀ {s : σ} {term : Pattern} {s' : σ} {out : List Pattern},
        I.intrinsicStateful s term = some (s', out) →
        P s → P s')
    (s : σ) (isRoot parentCallable : Bool) (ctor : String) (args : List Pattern)
    (hP : P s)
    (hArgsTrue : P ((runNestedEffectsArgs I s true args [] false).1))
    (hArgsFalse : P ((runNestedEffectsArgs I s false args [] false).1))
    (hArgsCurrent : P ((runNestedEffectsArgs I s (I.isEagerCallableHead s ctor) args [] false).1)) :
    P ((runNestedEffects I s isRoot parentCallable (.apply ctor args)).1) := by
  by_cases hCall : ctor = "call"
  · subst hCall
    simpa [runNestedEffects.eq_def] using
      preserve_intrinsic_or_args I P hIntrinsicPres "call" s isRoot args hArgsTrue hP
  · by_cases hEval : ctor = "eval"
    · subst hEval
      simpa [runNestedEffects.eq_def, hCall] using
        preserve_intrinsic_or_args I P hIntrinsicPres "eval" s isRoot args hArgsTrue hP
    · by_cases hReduce : ctor = "reduce"
      · subst hReduce
        simpa [runNestedEffects.eq_def, hCall, hEval] using
          preserve_intrinsic_or_args I P hIntrinsicPres "reduce" s isRoot args hArgsTrue hP
      · by_cases hChain : ctor = "chain"
        · subst hChain
          simpa [runNestedEffects.eq_def, hCall, hEval, hReduce] using
            preserve_intrinsic_or_args I P hIntrinsicPres "chain" s isRoot args hArgsTrue hP
        · by_cases hMatch : ctor = "match"
          · subst hMatch
            simp [runNestedEffects.eq_def, hP]
          · by_cases hCollapse : ctor = "collapse"
            · subst hCollapse
              simpa [runNestedEffects.eq_def] using
                preserve_intrinsic_or_original I P hIntrinsicPres "collapse" s isRoot args hP
            · by_cases hSuperpose : ctor = "superpose"
              · subst hSuperpose
                cases isRoot with
                | true =>
                    simp [runNestedEffects.eq_def, hP]
                | false =>
                    simpa [runNestedEffects.eq_def] using hArgsFalse
              · by_cases hMsort : ctor = "msort"
                · subst hMsort
                  simpa [runNestedEffects.eq_def, hSuperpose] using
                    preserve_intrinsic_or_original I P hIntrinsicPres "msort" s isRoot args hP
                · cases args with
                  | nil =>
                      simpa [runNestedEffects.eq_def, hCall, hEval, hReduce, hChain, hMatch,
                        hCollapse, hSuperpose, hMsort] using hArgsCurrent
                  | cons a as =>
                      cases as with
                      | nil =>
                          by_cases hQuote : ctor = "quote"
                          · subst hQuote
                            simp [runNestedEffects.eq_def, hP]
                          · by_cases hRemoveAll : ctor = "remove-all-atoms"
                            · subst hRemoveAll
                              simp [runNestedEffects.eq_def, hP]
                            · by_cases hRemoveAllBang : ctor = "remove-all-atoms!"
                              · subst hRemoveAllBang
                                simp [runNestedEffects.eq_def, hP]
                              · by_cases hGetAtoms : ctor = "get-atoms"
                                · subst hGetAtoms
                                  simp [runNestedEffects.eq_def, hP]
                                · by_cases hGetAtomsBang : ctor = "get-atoms!"
                                  · subst hGetAtomsBang
                                    simp [runNestedEffects.eq_def, hP]
                                  · by_cases hGetState : ctor = "get-state"
                                    · subst hGetState
                                      simp [runNestedEffects.eq_def, hP]
                                    · by_cases hTransaction : ctor = "transaction"
                                      · subst ctor
                                        simp [runNestedEffects.eq_def, hP]
                                      · have hArgs :=
                                          hArgsCurrent
                                        simpa [runNestedEffects.eq_def, hCall, hEval, hReduce, hChain, hMatch,
                                          hCollapse, hSuperpose, hMsort, hQuote, hRemoveAll,
                                          hRemoveAllBang, hGetAtoms, hGetAtomsBang, hGetState,
                                          hTransaction] using hArgs
                      | cons b bs =>
                          cases bs with
                          | nil =>
                              by_cases hLetStar : ctor = "let*"
                              · subst hLetStar
                                simp [runNestedEffects.eq_def, hP]
                              · by_cases hAddAtom : ctor = "add-atom"
                                · subst hAddAtom
                                  simp [runNestedEffects.eq_def, hP]
                                · by_cases hAddAtomBang : ctor = "add-atom!"
                                  · subst hAddAtomBang
                                    simp [runNestedEffects.eq_def, hP]
                                  · by_cases hRemoveAtom : ctor = "remove-atom"
                                    · subst hRemoveAtom
                                      simp [runNestedEffects.eq_def, hP]
                                    · by_cases hRemoveAtomBang : ctor = "remove-atom!"
                                      · subst hRemoveAtomBang
                                        simp [runNestedEffects.eq_def, hP]
                                      · by_cases hBindBang : ctor = "bind!"
                                        · subst hBindBang
                                          simp [runNestedEffects.eq_def, hP]
                                        · by_cases hChangeState : ctor = "change-state!"
                                          · subst hChangeState
                                            simp [runNestedEffects.eq_def, hP]
                                          · by_cases hWithMutex : ctor = "with_mutex"
                                            · subst hWithMutex
                                              simp [runNestedEffects.eq_def, hP]
                                            · by_cases hImport : ctor = "import!"
                                              · subst ctor
                                                simp [runNestedEffects.eq_def, hP]
                                              · have hArgs :=
                                                  hArgsCurrent
                                                simpa [runNestedEffects.eq_def, hCall, hEval, hReduce, hChain,
                                                  hMatch, hCollapse, hSuperpose, hMsort, hLetStar,
                                                  hAddAtom, hAddAtomBang, hRemoveAtom, hRemoveAtomBang,
                                                  hBindBang, hChangeState, hWithMutex, hImport] using hArgs
                          | cons c cs =>
                              cases cs with
                              | nil =>
                                  by_cases hLet : ctor = "let"
                                  · subst hLet
                                    simp [runNestedEffects.eq_def, hP]
                                  · by_cases hImport : ctor = "import!"
                                    · subst ctor
                                      simp [runNestedEffects.eq_def, hP]
                                    · have hArgs :=
                                        hArgsCurrent
                                      simpa [runNestedEffects.eq_def, hCall, hEval, hReduce, hChain,
                                        hMatch, hCollapse, hSuperpose, hMsort, hLet, hImport] using hArgs
                              | cons d ds =>
                                  have hArgs :=
                                    hArgsCurrent
                                  simpa [runNestedEffects.eq_def, hCall, hEval, hReduce, hChain, hMatch,
                                    hCollapse, hSuperpose, hMsort] using hArgs

theorem runNestedEffects_preserves_of_intrinsicStateful
    (I : Interface σ) (P : σ → Prop)
    (hIntrinsicPres :
      ∀ {s : σ} {term : Pattern} {s' : σ} {out : List Pattern},
        I.intrinsicStateful s term = some (s', out) →
        P s → P s') :
    ∀ (s : σ) (isRoot parentCallable : Bool) (term : Pattern),
      P s → P ((runNestedEffects I s isRoot parentCallable term).1) := by
  have hMain :
      ∀ n, ∀ (s : σ) (isRoot parentCallable : Bool) (term : Pattern),
        sizeOf term ≤ n →
        P s → P ((runNestedEffects I s isRoot parentCallable term).1) := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
        intro s isRoot parentCallable term hSize hP
        cases term with
        | fvar x =>
            simpa [runNestedEffects.eq_def] using hP
        | bvar x =>
            simpa [runNestedEffects.eq_def] using hP
        | apply ctor args =>
            have hRunLt :
                ∀ (s : σ) (isRoot parentCallable : Bool) (term : Pattern),
                  sizeOf term < sizeOf (Pattern.apply ctor args) →
                  P s → P ((runNestedEffects I s isRoot parentCallable term).1) := by
              intro s isRoot parentCallable term hLt hP
              exact ih (sizeOf term) (Nat.lt_of_lt_of_le hLt hSize) s isRoot parentCallable term (Nat.le_refl _) hP
            have hArgsTrue :
                P ((runNestedEffectsArgs I s true args [] false).1) :=
              runNestedEffectsArgs_preserves_of_lt I P (sizeOf (Pattern.apply ctor args))
                hRunLt args (sizeOf_lt_of_mem_applyArgs ctor args) s true [] false hP
            have hArgsFalse :
                P ((runNestedEffectsArgs I s false args [] false).1) :=
              runNestedEffectsArgs_preserves_of_lt I P (sizeOf (Pattern.apply ctor args))
                hRunLt args (sizeOf_lt_of_mem_applyArgs ctor args) s false [] false hP
            have hArgsCurrent :
                P ((runNestedEffectsArgs I s (I.isEagerCallableHead s ctor) args [] false).1) :=
              runNestedEffectsArgs_preserves_of_lt I P (sizeOf (Pattern.apply ctor args))
                hRunLt args (sizeOf_lt_of_mem_applyArgs ctor args)
                s (I.isEagerCallableHead s ctor) [] false hP
            exact runNestedEffectsApply_preserves_local I P hIntrinsicPres
              s isRoot parentCallable ctor args hP hArgsTrue hArgsFalse hArgsCurrent
        | lambda body =>
            have hBody :
                P ((runNestedEffects I s false false body).1) :=
              ih (sizeOf body) (Nat.lt_of_lt_of_le (sizeOf_body_lt_lambda body) hSize)
                s false false body (Nat.le_refl _) hP
            cases hStep : runNestedEffects I s false false body with
            | mk s1 rest1 =>
                cases rest1 with
                | mk body' changed =>
                    have hS1 : P s1 := by
                      simpa [hStep] using hBody
                    have hEq :
                        (runNestedEffects I s isRoot parentCallable (.lambda body)).1 = s1 := by
                      rw [runNestedEffects.eq_def]
                      simp [hStep]
                    rw [hEq]
                    exact hS1
        | multiLambda n body =>
            have hBody :
                P ((runNestedEffects I s false false body).1) :=
              ih (sizeOf body) (Nat.lt_of_lt_of_le (sizeOf_body_lt_multiLambda n body) hSize)
                s false false body (Nat.le_refl _) hP
            cases hStep : runNestedEffects I s false false body with
            | mk s1 rest1 =>
                cases rest1 with
                | mk body' changed =>
                    have hS1 : P s1 := by
                      simpa [hStep] using hBody
                    have hEq :
                        (runNestedEffects I s isRoot parentCallable (.multiLambda n body)).1 = s1 := by
                      rw [runNestedEffects.eq_def]
                      simp [hStep]
                    rw [hEq]
                    exact hS1
        | subst body repl =>
            have hBody :
                P ((runNestedEffects I s false false body).1) :=
              ih (sizeOf body) (Nat.lt_of_lt_of_le (sizeOf_body_lt_subst body repl) hSize)
                s false false body (Nat.le_refl _) hP
            cases hStep1 : runNestedEffects I s false false body with
            | mk s1 rest1 =>
                cases rest1 with
                | mk body' c1 =>
                    have hS1 : P s1 := by
                      simpa [hStep1] using hBody
                    have hRepl :
                        P ((runNestedEffects I s1 false false repl).1) :=
                      ih (sizeOf repl) (Nat.lt_of_lt_of_le (sizeOf_repl_lt_subst body repl) hSize)
                        s1 false false repl (Nat.le_refl _) hS1
                    cases hStep2 : runNestedEffects I s1 false false repl with
                    | mk s2 rest2 =>
                        cases rest2 with
                        | mk repl' c2 =>
                            have hS2 : P s2 := by
                              simpa [hStep2] using hRepl
                            have hEq :
                                (runNestedEffects I s isRoot parentCallable (.subst body repl)).1 = s2 := by
                              rw [runNestedEffects.eq_def]
                              simp [hStep1, hStep2]
                            rw [hEq]
                            exact hS2
        | collection ct elems rest =>
            have hElems :
                P ((runNestedEffectsArgs I s false elems [] false).1) :=
              runNestedEffectsArgs_preserves_of_lt I P (sizeOf (Pattern.collection ct elems rest))
                (by
                  intro s isRoot parentCallable term hLt hP
                  exact ih (sizeOf term) (Nat.lt_of_lt_of_le hLt hSize)
                    s isRoot parentCallable term (Nat.le_refl _) hP)
                elems (sizeOf_lt_of_mem_collectionElems ct elems rest) s false [] false hP
            cases hStep : runNestedEffectsArgs I s false elems [] false with
            | mk s1 rest1 =>
                cases rest1 with
                | mk elems' changed =>
                    have hS1 : P s1 := by
                      simpa [hStep] using hElems
                    have hEq :
                        (runNestedEffects I s isRoot parentCallable (.collection ct elems rest)).1 = s1 := by
                      rw [runNestedEffects.eq_def]
                      simp [hStep]
                    rw [hEq]
                    exact hS1
  intro s isRoot parentCallable term hP
  exact hMain (sizeOf term) s isRoot parentCallable term (Nat.le_refl _) hP

theorem preservation_of_intrinsicStateful
    (I : Interface σ) (P : σ → Prop)
    (hIntrinsicPres :
      ∀ {s : σ} {term : Pattern} {s' : σ} {out : List Pattern},
        I.intrinsicStateful s term = some (s', out) →
        P s → P s') :
    Preservation I P := by
  refine {
    runNestedEffects_preserves := ?_,
    intrinsicStateful_preserves := ?_
  }
  · intro s isRoot parentCallable term s' term' changed hRun hP
    have hPres :
        P ((runNestedEffects I s isRoot parentCallable term).1) :=
      runNestedEffects_preserves_of_intrinsicStateful I P hIntrinsicPres
        s isRoot parentCallable term hP
    have hState :
        (runNestedEffects I s isRoot parentCallable term).1 = s' := by
      simpa using congrArg Prod.fst hRun
    simpa [hState] using hPres
  · intro s term s' out hIntr hP
    exact hIntrinsicPres hIntr hP

end Algorithms.MeTTa.Simple.Backend.ReferenceEval
