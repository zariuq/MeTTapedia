import Mettapedia.Languages.ProcessCalculi.MORK.Space
import Mettapedia.Languages.ProcessCalculi.MORK.ThreePhaseExec
import Mettapedia.Languages.ProcessCalculi.MORK.ThreePhaseRefinement
import Mettapedia.Languages.ProcessCalculi.MORK.MatchSpec

/-!
# MORK: Invertible Compat-Head Fragment

PeTTa compat-head rules evaluate subterms during matching
(`matchHeadArgWithEval` calls `I.eval` in Dispatch.lean:504).
MORK's `matchAtom` is purely structural.

However, for a *significant subfragment* — head functions that are
**pure, structurally recursive, and produce constructor-wrapped outputs** —
the evaluation-during-matching can be compiled to standard MORK/MM2 using
the UNFOLD/BASE/FOLD three-phase architecture.

The key idea: instead of evaluating `f(x)` forward and matching, we
*reverse-match* the query argument against `f`'s output structure to
recover `x`. For injective structural functions, this produces the same
bindings.

## Validated by PoC

Nine passing Rust tests (`compat_head_poc_*` in `mork_translator_test.rs`)
demonstrate the three encoding strategies:
1. Compile-time specialization (non-recursive)
2. Reverse-match from query (non-recursive, runtime)
3. UNFOLD/BASE/FOLD inversion (recursive, runtime)

## Scope

This file formalizes the *fragment boundary* and the compilation scheme.
The main theorem (`staged_inverse_sound`) proves that the staged MORK
execution produces results consistent with forward evaluation of the
head function.

The bridge to `matchHeadArgWithEval` (Dispatch.lean) is Step 5 of the
plan, to be added after the core soundness proof is established.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Atom helpers for recursive structure analysis -/

/-- Check if a symbol name occurs anywhere in an atom (at head or nested). -/
def atomContainsSymbol : String → Atom → Bool
  | s, .symbol t      => s == t
  | _, .var _          => false
  | _, .grounded _     => false
  | s, .expression es  => atomContainsSymbolList s es
where
  atomContainsSymbolList : String → List Atom → Bool
    | _, []      => false
    | s, a :: as => atomContainsSymbol s a || atomContainsSymbolList s as

/-- Count how many times a symbol name appears as the head of an
    `.expression (.symbol name :: args)` subterm. -/
def atomHeadCallCount : String → Atom → Nat
  | name, .expression (.symbol s :: args) =>
    (if s == name then 1 else 0) + atomHeadCallCountList name args
  | name, .expression es => atomHeadCallCountList name es
  | _, _ => 0
where
  atomHeadCallCountList : String → List Atom → Nat
    | _, []      => 0
    | name, a :: as => atomHeadCallCount name a + atomHeadCallCountList name as

/-! ## Head function definitions -/

/-- A defining equation for a head function: `(= (f lhsArgs...) rhs)`.
    Expressed in MORK `Atom` terms (not MeTTaIL `Pattern`). -/
structure HeadEquation where
  /-- The head function name (e.g., "mk", "tail") -/
  funcName : String
  /-- Argument patterns on the LHS (e.g., `[.var "x"]` for `(mk $x)`) -/
  lhsArgs  : List Atom
  /-- RHS expression (e.g., `(wrap $x)`) -/
  rhs      : Atom
  deriving Repr, DecidableEq

/-- A head function definition is a list of equations sharing the same head. -/
structure HeadFuncDef where
  /-- The head function name -/
  funcName  : String
  /-- The defining equations -/
  equations : List HeadEquation
  /-- All equations share the function name -/
  consistent : ∀ eq ∈ equations, eq.funcName = funcName
  deriving Repr

/-! ## Equation classification -/

/-- A head equation is a base case when its RHS contains no call to `funcName`. -/
def HeadEquation.isBase (eq : HeadEquation) : Bool :=
  atomHeadCallCount eq.funcName eq.rhs == 0

/-- A head equation is a step case with exactly one recursive call in the RHS. -/
def HeadEquation.isStep (eq : HeadEquation) : Bool :=
  atomHeadCallCount eq.funcName eq.rhs == 1

/-- Collect all variable names from a list of argument atoms. -/
def lhsArgVars : List Atom → List String
  | [] => []
  | a :: as => atomFreeVars a ++ lhsArgVars as

/-! ## Structural recursion shape

For a step equation `(= (f (C $n)) (D (f $n)))`, the RHS has the shape:
  `.expression (.symbol D :: outerArgs ++ [.expression (.symbol f :: recArgs)])`

The key property is that the recursive call is *wrapped in a constructor*,
making the RHS strictly larger than the recursive sub-result. This ensures
the inverse is structurally decreasing. -/

/-- Extract the position of a recursive call in an expression's argument list.
    Returns `(pre, recArgs, post)` where `pre ++ [.expression (.symbol f :: recArgs)] ++ post`
    equals the original argument list. -/
def findRecursiveCallPos (funcName : String) :
    List Atom → Option (List Atom × List Atom × List Atom)
  | [] => none
  | (.expression (.symbol s :: recArgs)) :: rest =>
    if s == funcName then some ([], recArgs, rest)
    else match findRecursiveCallPos funcName rest with
      | some (pre, rArgs, post) =>
        some (.expression (.symbol s :: recArgs) :: pre, rArgs, post)
      | none => none
  | a :: rest =>
    match findRecursiveCallPos funcName rest with
    | some (pre, rArgs, post) => some (a :: pre, rArgs, post)
    | none => none

/-! ## The InvertibleHead predicate -/

/-- A head function is invertible within MORK when:

1. **Has a base case**: At least one equation with no recursive calls.
2. **Variable coverage**: All RHS free variables come from LHS arguments.
3. **Base cases produce constructor expressions**: The RHS of each base
   equation is an `.expression (.symbol ctor :: args)` — a constructor
   application that structural matching can decompose.
4. **Step cases wrap exactly one recursive call in a constructor**: The
   RHS has the shape `(ctor pre... (f recArgs...) post...)` where `ctor`
   is a symbol and the recursive call to `f` is at a known position.
-/
structure InvertibleHead (def_ : HeadFuncDef) : Prop where
  /-- At least one base case equation -/
  hasBase : ∃ eq ∈ def_.equations, eq.isBase = true
  /-- All RHS free variables are bound by LHS arguments -/
  varsCovered : ∀ eq ∈ def_.equations,
    ∀ v ∈ atomFreeVars eq.rhs, v ∈ lhsArgVars eq.lhsArgs
  /-- Base case RHS is a constructor application -/
  basesAreCtorApps : ∀ eq ∈ def_.equations, eq.isBase = true →
    ∃ ctor args, eq.rhs = .expression (.symbol ctor :: args)
  /-- Step case RHS wraps exactly one recursive call in a constructor -/
  stepsWrapRecursion : ∀ eq ∈ def_.equations, eq.isStep = true →
    ∃ ctor outerArgs,
      eq.rhs = .expression (.symbol ctor :: outerArgs) ∧
      findRecursiveCallPos def_.funcName outerArgs ≠ none
  /-- Base recoverability: for each base equation, every LHS variable appears in
      the RHS. This ensures reverse-matching the RHS recovers all LHS variables
      needed to reconstruct the input.

      This is the correct-direction complement to `varsCovered` (which goes RHS→LHS);
      here we need LHS→RHS. The positive example `(= (mk $x) (wrap $x))` satisfies
      this; the negative example `(= (f $x $y) (wrap $x))` does not (y is lost). -/
  lhsVarsRecoverableBase : ∀ eq ∈ def_.equations, eq.isBase = true →
    ∀ lhsPat ∈ eq.lhsArgs,
    ∀ v ∈ atomFreeVars lhsPat, v ∈ atomFreeVars eq.rhs
  /-- Step recoverability: for each step equation, every LHS variable is either
      recoverable from the outer RHS shell (pre/post around the recursive call),
      or appears in the recursive call's arguments (recovered via the IH).

      More precisely, given the decomposition
      `rhs = (ctor pre... (funcName recArgs...) post...)`,
      each var in any lhsPat is in `atomFreeVarsList (pre ++ post) ∪ atomFreeVarsList recArgs`. -/
  lhsVarsRecoverableStep : ∀ eq ∈ def_.equations, eq.isStep = true →
    ∀ lhsPat ∈ eq.lhsArgs,
    ∀ v ∈ atomFreeVars lhsPat,
    match findRecursiveCallPos def_.funcName (match eq.rhs with
      | .expression (.symbol _ :: outerArgs) => outerArgs | _ => []) with
    | some (pre, recArgs, post) =>
        v ∈ lhsArgVars (pre ++ post) ∨ v ∈ lhsArgVars recArgs
    | none => False
  /-- Position stability: `findRecursiveCallPos` on the symbolic `outerArgs`
      agrees with the position in `applySubst.applySubstList σ outerArgs`
      for any ground substitution σ that binds all variables.

      Concretely, if the recursive call is at position `(pre, recArgs, post)`,
      then after substitution it is at `(σ(pre), σ(recArgs), σ(post))`.

      This holds automatically when `findRecursiveCallPos` looks only at
      `.expression (.symbol f :: _)` heads — substitution does not change
      `.symbol` nodes. -/
  positionStable : ∀ eq ∈ def_.equations, eq.isStep = true →
    ∀ (ctor : String) (outerArgs pre recArgs post : List Atom),
    eq.rhs = .expression (.symbol ctor :: outerArgs) →
    findRecursiveCallPos def_.funcName outerArgs = some (pre, recArgs, post) →
    ∀ (σ : Subst),
    (∀ v ∈ lhsArgVars eq.lhsArgs,
      ∃ b, Subst.lookup σ v = some b ∧ isGroundAtom b = true) →
    findRecursiveCallPos def_.funcName (applySubst.applySubstList σ outerArgs) =
      some (applySubst.applySubstList σ pre,
            applySubst.applySubstList σ recArgs,
            applySubst.applySubstList σ post)
  /-- Base/step constructor disjointness: the outer constructor of every base
      equation's RHS differs from the outer constructor of every step equation's RHS.

      This ensures that `reverseEval`'s base sweep does not spuriously match a
      step equation's output.

      Positive example: `mkRecDef` has base ctor = "z", step ctor = "s".
      Negative example: a function where base and step share the same wrapper
      constructor would fail this (and indeed could not be inverted by the staged
      scheme without additional discrimination). -/
  baseStepCtorDisjoint : ∀ beq ∈ def_.equations, beq.isBase = true →
    ∀ seq ∈ def_.equations, seq.isStep = true →
    ∀ (bctor : String) (bargs : List Atom) (sctor : String) (sargs : List Atom),
    beq.rhs = .expression (.symbol bctor :: bargs) →
    seq.rhs = .expression (.symbol sctor :: sargs) →
    bctor ≠ sctor

/-! ## Canary examples -/

section InvertibleHeadExamples

/-- Example: `mk` with `(= (mk $x) (wrap $x))` — non-recursive, one equation.
    This is the simplest invertible head. -/
private def mkEq : HeadEquation :=
  ⟨"mk", [.var "x"], .expression [.symbol "wrap", .var "x"]⟩

private def mkDef : HeadFuncDef where
  funcName := "mk"
  equations := [mkEq]
  consistent := by intro eq h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; rfl

private theorem mkDef_base : mkEq.isBase = true := by
  simp [HeadEquation.isBase, mkEq, atomHeadCallCount, atomHeadCallCount.atomHeadCallCountList]

/-- Example: recursive `mk` with:
    `(= (mk 0) (z))`
    `(= (mk (S $n)) (s (mk $n)))` -/
private def mkRecEq0 : HeadEquation :=
  ⟨"mk", [.symbol "0"], .expression [.symbol "z"]⟩

private def mkRecEqS : HeadEquation :=
  ⟨"mk", [.expression [.symbol "S", .var "n"]],
   .expression [.symbol "s", .expression [.symbol "mk", .var "n"]]⟩

private def mkRecDef : HeadFuncDef where
  funcName := "mk"
  equations := [mkRecEq0, mkRecEqS]
  consistent := by
    intro eq h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> rfl

private theorem mkRecDef_eq0_isBase : mkRecEq0.isBase = true := by
  simp [HeadEquation.isBase, mkRecEq0, atomHeadCallCount, atomHeadCallCount.atomHeadCallCountList]

private theorem mkRecDef_eqS_isStep : mkRecEqS.isStep = true := by
  simp [HeadEquation.isStep, mkRecEqS, atomHeadCallCount, atomHeadCallCount.atomHeadCallCountList,
        BEq.beq, decide_true]

end InvertibleHeadExamples

/-! ## Staged inverse compilation

Given an `InvertibleHead`, compile it to MORK three-phase rules.

For each base equation `(= (f basePattern) baseRHS)`:
  - BASE rule: match `baseRHS` structurally against query arg → result `basePattern`

For each step equation `(= (f (C $n)) (D (f $n)))`:
  - UNFOLD rule: match outer constructor `D` in query → spawn sub-query for inner
  - FOLD rule: wait + sub-result `$x` → result `(C $x)` -/

/-- The staged inverse compilation result for one invertible head function. -/
structure StagedInverseCompilation (def_ : HeadFuncDef) where
  /-- Unfold rules for step equations -/
  unfoldRules : List (HeadEquation × UnfoldStep)
  /-- Base rules for base equations -/
  baseRules   : List (HeadEquation × BaseStep)
  /-- Fold rules for step equations -/
  foldRules   : List (HeadEquation × FoldStep)
  /-- Every step equation has an unfold + fold rule -/
  stepCoverage : ∀ eq ∈ def_.equations, eq.isStep = true →
    (∃ p ∈ unfoldRules, p.1 = eq) ∧ (∃ p ∈ foldRules, p.1 = eq)
  /-- Every base equation has a base rule -/
  baseCoverage : ∀ eq ∈ def_.equations, eq.isBase = true →
    ∃ p ∈ baseRules, p.1 = eq

/-! ## Forward evaluation (for stating the soundness theorem) -/

/-- Forward evaluation of a head function on an argument: apply matching
    equations until a base case is reached. Returns `none` if no equation
    matches or the recursion depth exceeds the fuel.

    For step cases, uses `findRecursiveCallPos` to locate the single recursive
    call, evaluates it, and reconstructs the result. -/
def forwardEval (def_ : HeadFuncDef) : Nat → Atom → Option Atom
  | 0, _ => none
  | fuel + 1, arg =>
    def_.equations.findSome? fun eq =>
      match eq.lhsArgs with
      | [lhsPat] =>
        match matchAtom [] lhsPat arg with
        | some σ =>
          let result := applySubst σ eq.rhs
          if eq.isBase then some result
          else
            -- Step case: find the recursive call in the substituted RHS,
            -- evaluate it, and reconstruct with the result.
            match result with
            | .expression (.symbol ctor :: outerArgs) =>
              match findRecursiveCallPos def_.funcName outerArgs with
              | some (pre, [recArg], post) =>
                (forwardEval def_ fuel recArg).map fun innerResult =>
                  .expression (.symbol ctor :: pre ++ [innerResult] ++ post)
              | _ => none
            | _ => none
        | none => none
      | _ => none

/-! ## Reverse matching (for the inverse direction)

Given a query argument `queryArg` and a head function definition,
find the input `arg` such that `forwardEval def_ fuel arg = queryArg`. -/

/-- Reverse-match a query argument against a base equation's RHS.
    If `matchAtom [] rhs queryArg = some σ`, then the inverse is
    `applySubst σ lhsArg`. -/
def reverseMatchBase (eq : HeadEquation) (queryArg : Atom) : Option Atom :=
  match eq.lhsArgs with
  | [lhsPat] =>
    match matchAtom [] eq.rhs queryArg with
    | some σ => some (applySubst σ lhsPat)
    | none => none
  | _ => none

/-! ## Substitution stability lemmas

The roundtrip property (`matchAtom σ pat conc = some σ' → applySubst σ' pat = conc`)
requires two supporting lemmas:

1. `matchAtom` only extends the substitution in a lookup-stable way: existing
   lookup results are preserved.
2. Applying a ground-producing substitution is stable under lookup extension. -/

/-- Lookup-level extension: σ' extends σ when every existing lookup is preserved.
    Uses fully-qualified `Subst.lookup` to avoid dot-notation resolving to
    `List.lookup` for cons expressions. -/
def Subst.lookupExtends (σ' σ : Subst) : Prop :=
  ∀ v a, Subst.lookup σ v = some a → Subst.lookup σ' v = some a

theorem Subst.lookupExtends_refl (σ : Subst) : σ.lookupExtends σ :=
  fun _ _ h => h

theorem Subst.lookupExtends_trans {σ₁ σ₂ σ₃ : Subst}
    (h₁₂ : σ₂.lookupExtends σ₁) (h₂₃ : σ₃.lookupExtends σ₂) :
    σ₃.lookupExtends σ₁ :=
  fun v a hv => h₂₃ v a (h₁₂ v a hv)

/-- Prepending a fresh binding preserves existing lookups. -/
theorem Subst.lookupExtends_cons_fresh {σ : Subst} {w : String} {b : Atom}
    (hfresh : Subst.lookup σ w = none) :
    Subst.lookupExtends ((w, b) :: σ) σ := by
  intro v a hva
  by_cases hwv : w = v
  · subst hwv; rw [hfresh] at hva; cases hva
  · show Subst.lookup ((w, b) :: σ) v = some a
    unfold Subst.lookup
    simp only [List.find?_cons]
    have hneq : (w == v) = false := beq_eq_false_iff_ne.mpr hwv
    simp only [hneq]
    exact hva

/-- `matchAtom` preserves existing lookups: σ' from matching extends σ. -/
theorem matchAtom_lookupExtends {σ : Subst} {pat conc : Atom} {σ' : Subst}
    (h : matchAtom σ pat conc = some σ') :
    σ'.lookupExtends σ := by
  match pat, conc with
  | .var v, a =>
    simp only [matchAtom] at h
    cases hlookup : Subst.lookup σ v with
    | none =>
      simp [hlookup] at h; subst h
      exact Subst.lookupExtends_cons_fresh hlookup
    | some a' =>
      by_cases heq : a == a'
      · simp [hlookup, heq] at h; subst h; exact Subst.lookupExtends_refl _
      · simp [hlookup, heq] at h
  | .symbol s, .symbol t =>
    simp only [matchAtom] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact Subst.lookupExtends_refl _
    · simp at h
  | .grounded g, .grounded g' =>
    simp only [matchAtom] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact Subst.lookupExtends_refl _
    · simp at h
  | .expression ps, .expression cs =>
    simp only [matchAtom] at h
    exact matchAtomList_lookupExtends h
  | .symbol _, .var _ => simp [matchAtom] at h
  | .symbol _, .grounded _ => simp [matchAtom] at h
  | .symbol _, .expression _ => simp [matchAtom] at h
  | .grounded _, .var _ => simp [matchAtom] at h
  | .grounded _, .symbol _ => simp [matchAtom] at h
  | .grounded _, .expression _ => simp [matchAtom] at h
  | .expression _, .var _ => simp [matchAtom] at h
  | .expression _, .symbol _ => simp [matchAtom] at h
  | .expression _, .grounded _ => simp [matchAtom] at h
where
  matchAtomList_lookupExtends {σ : Subst} {ps cs : List Atom} {σ' : Subst}
      (h : matchAtom.matchAtomList σ ps cs = some σ') :
      σ'.lookupExtends σ := by
    match ps, cs with
    | [], [] =>
      simp [matchAtom.matchAtomList] at h; cases h; exact Subst.lookupExtends_refl σ
    | [], _ :: _ => simp [matchAtom.matchAtomList] at h
    | _ :: _, [] => simp [matchAtom.matchAtomList] at h
    | p :: ps, c :: cs =>
      simp only [matchAtom.matchAtomList] at h
      cases hm : matchAtom σ p c with
      | none => simp [hm] at h
      | some σ_mid =>
        simp [hm] at h
        exact Subst.lookupExtends_trans
          (matchAtom_lookupExtends hm)
          (matchAtomList_lookupExtends h)

/-- If `applySubst σ a` is ground, then any lookup-extension σ' gives the same result. -/
theorem applySubst_ground_ext {σ σ' : Subst} {a : Atom}
    (hext : σ'.lookupExtends σ)
    (hg : isGroundAtom (applySubst σ a) = true) :
    applySubst σ' a = applySubst σ a := by
  match a with
  | .var v =>
    cases hlookup : Subst.lookup σ v with
    | none => simp only [applySubst, hlookup] at hg; cases hg
    | some b => simp only [applySubst, hlookup, hext v b hlookup]
  | .symbol s => rfl
  | .grounded g => rfl
  | .expression es =>
    simp only [applySubst] at hg ⊢
    congr 1
    exact applySubstList_ground_ext hext hg
where
  applySubstList_ground_ext {σ σ' : Subst} {es : List Atom}
      (hext : σ'.lookupExtends σ)
      (hg : isGroundAtom.isGroundList (applySubst.applySubstList σ es) = true) :
      applySubst.applySubstList σ' es = applySubst.applySubstList σ es := by
    match es with
    | [] => rfl
    | a :: as =>
      simp only [applySubst.applySubstList]
      simp only [applySubst.applySubstList, isGroundAtom.isGroundList,
                  Bool.and_eq_true] at hg
      congr 1
      · exact applySubst_ground_ext hext hg.1
      · exact applySubstList_ground_ext hext hg.2

/-! ## Roundtrip: match then substitute recovers the ground atom -/

/-- General roundtrip: `matchAtom σ pat conc = some σ' → applySubst σ' pat = conc`
    when `conc` is ground. Works for any initial σ.

    The proof uses `matchAtom_lookupExtends` to thread σ stability through the
    expression-cons case, and `applySubst_ground_ext` to transfer head-match
    results across the tail-match's σ extension. -/
theorem matchAtom_applySubst_ground :
    ∀ (σ : Subst) (pat conc : Atom) (σ' : Subst),
    matchAtom σ pat conc = some σ' →
    isGroundAtom conc = true →
    applySubst σ' pat = conc := by
  intro σ pat conc σ' hm hg
  match pat, conc with
  | .var v, a =>
    simp only [matchAtom] at hm
    cases hlookup : σ.lookup v with
    | none =>
      simp [hlookup] at hm; cases hm
      simp [applySubst, Subst.lookup, List.find?]
    | some a' =>
      by_cases heq : a == a'
      · simp [hlookup, heq] at hm; cases hm
        have ha : a = a' := eq_of_beq heq
        simp [applySubst, hlookup, ha]
      · simp [hlookup, heq] at hm
  | .symbol s, .symbol t =>
    simp only [matchAtom] at hm; split at hm <;> simp_all [applySubst]
  | .grounded g, .grounded g' =>
    simp only [matchAtom] at hm; split at hm <;> simp_all [applySubst]
  | .expression ps, .expression cs =>
    simp only [matchAtom] at hm
    simp only [applySubst]
    congr 1
    exact matchAtomList_applySubst_ground hm hg
  | .symbol _, .var _ => simp [matchAtom] at hm
  | .symbol _, .grounded _ => simp [matchAtom] at hm
  | .symbol _, .expression _ => simp [matchAtom] at hm
  | .grounded _, .var _ => simp [matchAtom] at hm
  | .grounded _, .symbol _ => simp [matchAtom] at hm
  | .grounded _, .expression _ => simp [matchAtom] at hm
  | .expression _, .var _ => simp [matchAtom] at hm
  | .expression _, .symbol _ => simp [matchAtom] at hm
  | .expression _, .grounded _ => simp [matchAtom] at hm
where
  matchAtomList_applySubst_ground {σ : Subst} {ps cs : List Atom} {σ' : Subst}
      (hm : matchAtom.matchAtomList σ ps cs = some σ')
      (hg : isGroundAtom (.expression cs) = true) :
      applySubst.applySubstList σ' ps = cs := by
    match ps, cs with
    | [], [] =>
      simp [matchAtom.matchAtomList] at hm; cases hm
      simp [applySubst.applySubstList]
    | [], _ :: _ => simp [matchAtom.matchAtomList] at hm
    | _ :: _, [] => simp [matchAtom.matchAtomList] at hm
    | p :: ps, c :: cs =>
      simp only [matchAtom.matchAtomList] at hm
      cases hm_head : matchAtom σ p c with
      | none => simp [hm_head] at hm
      | some σ_mid =>
        simp [hm_head] at hm
        simp only [applySubst.applySubstList]
        -- Ground decomposition
        simp only [isGroundAtom, isGroundAtom.isGroundList, Bool.and_eq_true] at hg
        -- Head: applySubst σ_mid p = c, then stable under extension to σ'
        have hhead_rt := matchAtom_applySubst_ground σ p c σ_mid hm_head hg.1
        have htail_ext := matchAtom_lookupExtends.matchAtomList_lookupExtends hm
        have hhead_ground : isGroundAtom (applySubst σ_mid p) = true := by
          rw [hhead_rt]; exact hg.1
        have hhead_stable := applySubst_ground_ext htail_ext hhead_ground
        -- Tail: recursive call
        have htail_ground : isGroundAtom (.expression cs) = true := by
          simp [isGroundAtom]; exact hg.2
        have htail_rt := matchAtomList_applySubst_ground hm htail_ground
        have hhead_final : applySubst σ' p = c := by rw [hhead_stable, hhead_rt]
        simp only [hhead_final, htail_rt]

/-! ## Base inverse soundness

For a non-recursive (base) equation, `reverseMatchBase` recovers the
original input to `forwardEval`. The proof uses the roundtrip theorem
`matchAtom_applySubst_ground`.

This is the core correctness property for compile-time specialization
and reverse-match encoding strategies (PoC tests 1-2, 5-6). -/

/-- Base inverse soundness: if the reverse match succeeds on a ground query
    argument, then the recovered input forward-evaluates to that query argument.

    More precisely: given a base equation `(= (f lhsPat) rhs)` and a ground
    query argument `queryArg`, if `matchAtom [] rhs queryArg = some σ`, then
    `applySubst σ rhs = queryArg` (the substituted RHS equals the query). -/
theorem reverseMatchBase_rhs_roundtrip (eq : HeadEquation) (queryArg : Atom) (σ : Subst)
    (hm : matchAtom [] eq.rhs queryArg = some σ)
    (hg : isGroundAtom queryArg = true) :
    applySubst σ eq.rhs = queryArg :=
  matchAtom_applySubst_ground [] eq.rhs queryArg σ hm hg

/-- For a base equation with a single LHS pattern `lhsPat`, if
    `matchAtom [] rhs (applySubst σ rhs) = some σ` (the RHS pattern
    round-trips against the substituted result), then `reverseMatchBase`
    recovers the substituted LHS pattern.

    This connects forward evaluation to reverse matching for base cases. -/
theorem base_forward_reverse_roundtrip
    (eq : HeadEquation) (lhsPat : Atom) (σ : Subst)
    (hlhs : eq.lhsArgs = [lhsPat])
    (hreverse : matchAtom [] eq.rhs (applySubst σ eq.rhs) = some σ) :
    reverseMatchBase eq (applySubst σ eq.rhs) = some (applySubst σ lhsPat) := by
  simp only [reverseMatchBase, hlhs, hreverse]

/-! ## Compilation: HeadEquation → Three-Phase Rules

Each equation compiles to MORK rules as follows:

**Base equation** `(= (f pat) rhs)`:
  `BaseStep` with priority 32 (first base slot).
  The `qid` is an abstract query marker; `result` is the reverse-matched LHS pattern.

**Step equation** `(= (f pat) (ctor pre... (f recArgs...) post...))`:
  `UnfoldStep` with priority 0: decomposes the outer constructor, spawns a sub-query
    for the inner expression (the recursive call's argument after evaluation).
  `FoldStep` with priority 64: waits for the sub-result and wraps it back in the
    LHS constructor pattern.

Priority assignments use the lowest slot in each band (0, 32, 64) since we have
a single head function — no inter-rule priority ordering is needed within a phase. -/

/-- Compile a base equation to a `BaseStep`.
    The `qid` and `result` are abstract markers — the actual query/result atoms
    depend on the runtime query. This structure records the *rule shape*. -/
def compileBaseStep (eq : HeadEquation) : BaseStep where
  qid      := .expression [.symbol "inv-query", .symbol eq.funcName]
  result   := .expression [.symbol "inv-result", .symbol eq.funcName]
  priority := 32
  inBase   := by simp [inPhase, phaseRange]

/-- Compile a step equation to an `UnfoldStep`.
    Spawns one sub-query for the recursive call's argument. -/
def compileUnfoldStep (eq : HeadEquation) : UnfoldStep where
  qid      := .expression [.symbol "inv-query", .symbol eq.funcName]
  subQids  := [.expression [.symbol "inv-sub", .symbol eq.funcName]]
  waitAtom := .expression [.symbol "inv-wait", .symbol eq.funcName]
  priority := 0
  inUnfold := by simp [inPhase, phaseRange]

/-- Compile a step equation to a `FoldStep`.
    Waits for one sub-result and wraps it back in the LHS pattern. -/
def compileFoldStep (eq : HeadEquation) : FoldStep where
  qid        := .expression [.symbol "inv-query", .symbol eq.funcName]
  waitAtom   := .expression [.symbol "inv-wait", .symbol eq.funcName]
  subResults := [.expression [.symbol "inv-sub-result", .symbol eq.funcName]]
  assembled  := .expression [.symbol "inv-assembled", .symbol eq.funcName]
  priority   := 64
  inFold     := by simp [inPhase, phaseRange]

/-- Compile an entire `HeadFuncDef` with an `InvertibleHead` proof into
    a `StagedInverseCompilation`. -/
def compileInverse (def_ : HeadFuncDef) (_hinv : InvertibleHead def_) :
    StagedInverseCompilation def_ where
  unfoldRules := def_.equations.filterMap fun eq =>
    if eq.isStep then some (eq, compileUnfoldStep eq) else none
  baseRules := def_.equations.filterMap fun eq =>
    if eq.isBase then some (eq, compileBaseStep eq) else none
  foldRules := def_.equations.filterMap fun eq =>
    if eq.isStep then some (eq, compileFoldStep eq) else none
  stepCoverage := by
    intro eq hmem hstep
    constructor
    · exact ⟨(eq, compileUnfoldStep eq), by
        simp only [List.mem_filterMap]
        exact ⟨eq, hmem, by simp [hstep]⟩, rfl⟩
    · exact ⟨(eq, compileFoldStep eq), by
        simp only [List.mem_filterMap]
        exact ⟨eq, hmem, by simp [hstep]⟩, rfl⟩
  baseCoverage := by
    intro eq hmem hbase
    exact ⟨(eq, compileBaseStep eq), by
      simp only [List.mem_filterMap]
      exact ⟨eq, hmem, by simp [hbase]⟩, rfl⟩

/-! ## Reverse evaluation (semantic inverse)

`reverseEval` is the fuel-indexed semantic inverse of `forwardEval`.
Given a query result `queryArg`, it tries to recover the input `arg`
such that `forwardEval def_ fuel arg = some queryArg`.

For base equations: reverse-match RHS pattern against `queryArg` → recover LHS.
For step equations: decompose outer constructor of `queryArg`, recurse on the
piece at the recursive-call position, wrap the sub-result in the LHS constructor.

This is a *semantic* function — it doesn't reference MORK space transitions.
The staged UNFOLD/BASE/FOLD compilation correctness (Step 4d) will be proven
against this semantic inverse. -/

/-- Extract the element at position `n` from a list, returning `none` if out of bounds. -/
def listGetAt : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: as, n + 1 => listGetAt as n

/-- Reverse-match a step equation's RHS outer constructor against a query.
    Given step RHS `(ctor pre... (f recArgs...) post...)` and a query
    `(ctor q0... qInner q_{k+1}...)`, extract `qInner` at the recursive-call position.

    Returns `(σ, innerQuery)` where `σ` binds LHS variables from outer args
    and `innerQuery` is the atom at the recursive-call position. -/
def reverseMatchStep (eq : HeadEquation) (funcName : String) (queryArg : Atom) :
    Option (Subst × Atom) :=
  match eq.rhs with
  | .expression (.symbol ctor :: outerArgs) =>
    match findRecursiveCallPos funcName outerArgs with
    | some (pre, _recArgs, post) =>
      match queryArg with
      | .expression (.symbol qctor :: queryOuter) =>
        if qctor == ctor && queryOuter.length == outerArgs.length then
          let recPos := pre.length
          match listGetAt queryOuter recPos with
          | some innerQuery =>
            let patternParts := pre ++ post
            let queryParts := queryOuter.take recPos ++ queryOuter.drop (recPos + 1)
            match matchAtom.matchAtomList [] patternParts queryParts with
            | some σ => some (σ, innerQuery)
            | none => none
          | none => none
        else none
      | _ => none
    | none => none
  | _ => none

/-- Extract the recursive call's arguments from a step equation's RHS.
    For `(= (f (C $n)) (D (f $n)))`, returns `[.var "n"]`. -/
def stepRecArgs (eq : HeadEquation) (funcName : String) : Option (List Atom) :=
  match eq.rhs with
  | .expression (.symbol _ :: outerArgs) =>
    match findRecursiveCallPos funcName outerArgs with
    | some (_, recArgs, _) => some recArgs
    | none => none
  | _ => none

/-- Fuel-indexed reverse evaluation: recover the input from a query result.
    Mirrors `forwardEval` but works backwards.

    For step cases: decomposes the outer constructor, recurses on the inner
    piece, then reconstructs the LHS by binding the recursive variable(s)
    to the recursive sub-input.
    -- Uses fully-qualified `Subst.lookup` throughout (see comment at `lookupExtends`). -/
def reverseEval (def_ : HeadFuncDef) : Nat → Atom → Option Atom
  | 0, _ => none
  | fuel + 1, queryArg =>
    let baseResult := def_.equations.findSome? fun eq =>
      if eq.isBase then reverseMatchBase eq queryArg else none
    match baseResult with
    | some r => some r
    | none =>
      def_.equations.findSome? fun eq =>
        if eq.isStep then
          match reverseMatchStep eq def_.funcName queryArg with
          | some (σ, innerQuery) =>
            match eq.lhsArgs with
            | [lhsPat] =>
              -- Recurse on the inner query to get the sub-input
              (reverseEval def_ fuel innerQuery).bind fun innerInput =>
                -- The recursive call in the RHS has arguments `recArgs`.
                -- We need to bind these to `innerInput` to reconstruct the LHS.
                match stepRecArgs eq def_.funcName with
                | some [.var recVar] =>
                  -- Common case: single variable → bind it to innerInput
                  some (applySubst ((recVar, innerInput) :: σ) lhsPat)
                | _ => none
            | _ => none
          | none => none
        else none

/-! ## Step 4b: Structural helpers for recursive inversion -/

/-- `findRecursiveCallPos` locates a unique position: if it returns
    `some (pre, recArgs, post)`, then
    `outerArgs = pre ++ [.expression (.symbol f :: recArgs)] ++ post`. -/
theorem findRecursiveCallPos_spec (f : String) (args : List Atom)
    (pre recArgs post : List Atom)
    (h : findRecursiveCallPos f args = some (pre, recArgs, post)) :
    args = pre ++ [.expression (.symbol f :: recArgs)] ++ post := by
  induction args generalizing pre recArgs post with
  | nil => simp [findRecursiveCallPos] at h
  | cons a as ih =>
    match a with
    | .expression (.symbol s :: sArgs) =>
      simp only [findRecursiveCallPos] at h
      by_cases hsf : s == f
      · simp only [hsf, ite_true] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have := eq_of_beq hsf; subst this; rfl
      · simp only [hsf] at h
        match hrest : findRecursiveCallPos f as with
        | none => simp [hrest] at h
        | some (pre', rArgs', post') =>
          simp [hrest] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          simp [ih _ _ _ hrest]
    | .var _ =>
      simp only [findRecursiveCallPos] at h
      match hrest : findRecursiveCallPos f as with
      | none => simp [hrest] at h
      | some (pre', rArgs', post') =>
        simp [hrest] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp [ih _ _ _ hrest]
    | .symbol _ =>
      simp only [findRecursiveCallPos] at h
      match hrest : findRecursiveCallPos f as with
      | none => simp [hrest] at h
      | some (pre', rArgs', post') =>
        simp [hrest] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp [ih _ _ _ hrest]
    | .grounded _ =>
      simp only [findRecursiveCallPos] at h
      match hrest : findRecursiveCallPos f as with
      | none => simp [hrest] at h
      | some (pre', rArgs', post') =>
        simp [hrest] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp [ih _ _ _ hrest]
    | .expression [] =>
      simp only [findRecursiveCallPos] at h
      match hrest : findRecursiveCallPos f as with
      | none => simp [hrest] at h
      | some (pre', rArgs', post') =>
        simp [hrest] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp [ih _ _ _ hrest]
    | .expression ((.var _) :: _) =>
      simp only [findRecursiveCallPos] at h
      match hrest : findRecursiveCallPos f as with
      | none => simp [hrest] at h
      | some (pre', rArgs', post') =>
        simp [hrest] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp [ih _ _ _ hrest]
    | .expression ((.grounded _) :: _) =>
      simp only [findRecursiveCallPos] at h
      match hrest : findRecursiveCallPos f as with
      | none => simp [hrest] at h
      | some (pre', rArgs', post') =>
        simp [hrest] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp [ih _ _ _ hrest]
    | .expression ((.expression _) :: _) =>
      simp only [findRecursiveCallPos] at h
      match hrest : findRecursiveCallPos f as with
      | none => simp [hrest] at h
      | some (pre', rArgs', post') =>
        simp [hrest] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp [ih _ _ _ hrest]

/-- `listGetAt` returns a member of the list. -/
theorem listGetAt_mem {l : List α} {n : Nat} {a : α}
    (h : listGetAt l n = some a) : a ∈ l := by
  induction l generalizing n with
  | nil => simp [listGetAt] at h
  | cons x xs ih =>
    cases n with
    | zero =>
      simp [listGetAt] at h; subst h
      exact List.Mem.head _
    | succ n =>
      simp [listGetAt] at h
      exact List.Mem.tail _ (ih h)

/-! ## Canary: compileInverse on the non-recursive example -/

section CompileCanary

private theorem mkDef_invertible : InvertibleHead mkDef where
  hasBase := ⟨mkEq, by simp [mkDef], mkDef_base⟩
  varsCovered := by
    intro eq hmem v hv
    simp [mkDef] at hmem; subst hmem
    simp [mkEq, atomFreeVars, atomFreeVars.atomFreeVarsList, lhsArgVars] at hv ⊢; exact hv
  basesAreCtorApps := by
    intro eq hmem _
    simp [mkDef] at hmem; subst hmem
    exact ⟨"wrap", [.var "x"], by simp [mkEq]⟩
  stepsWrapRecursion := by
    intro eq hmem hstep
    simp [mkDef] at hmem; subst hmem
    simp [HeadEquation.isStep, mkEq, atomHeadCallCount,
          atomHeadCallCount.atomHeadCallCountList] at hstep
  lhsVarsRecoverableBase := by
    intro eq hmem _hbase lhsPat hlhsPat v hv
    simp [mkDef] at hmem; subst hmem
    -- mkEq has lhsArgs = [.var "x"], rhs = .expression [.symbol "wrap", .var "x"]
    simp [mkEq] at hlhsPat; subst hlhsPat
    -- v ∈ atomFreeVars (.var "x") means v = "x"
    simp [atomFreeVars] at hv; subst hv
    -- "x" ∈ atomFreeVars (.expression [.symbol "wrap", .var "x"])
    simp [mkEq, atomFreeVars, atomFreeVars.atomFreeVarsList]
  lhsVarsRecoverableStep := by
    intro eq hmem hstep
    simp [mkDef] at hmem; subst hmem
    simp [HeadEquation.isStep, mkEq, atomHeadCallCount,
          atomHeadCallCount.atomHeadCallCountList] at hstep
  positionStable := by
    intro eq hmem hstep
    simp [mkDef] at hmem; subst hmem
    simp [HeadEquation.isStep, mkEq, atomHeadCallCount,
          atomHeadCallCount.atomHeadCallCountList] at hstep
  baseStepCtorDisjoint := by
    intro beq hmemb _hbase seq hmems hstep
    simp [mkDef] at hmemb hmems; subst hmemb; subst hmems
    simp [HeadEquation.isStep, mkEq, atomHeadCallCount,
          atomHeadCallCount.atomHeadCallCountList] at hstep

#check compileInverse mkDef mkDef_invertible

end CompileCanary

/-! ## Recursive example: mkRecDef is invertible -/

section RecInvertible

private theorem mkRecDef_invertible : InvertibleHead mkRecDef where
  hasBase := ⟨mkRecEq0, by simp [mkRecDef], mkRecDef_eq0_isBase⟩
  varsCovered := by
    intro eq hmem v hv
    simp [mkRecDef] at hmem
    rcases hmem with rfl | rfl
    · simp [mkRecEq0, atomFreeVars, atomFreeVars.atomFreeVarsList] at hv
    · simp [mkRecEqS, atomFreeVars, atomFreeVars.atomFreeVarsList, lhsArgVars] at hv ⊢
      exact hv
  basesAreCtorApps := by
    intro eq hmem hbase
    simp [mkRecDef] at hmem
    rcases hmem with rfl | rfl
    · exact ⟨"z", [], by simp [mkRecEq0]⟩
    · simp [HeadEquation.isBase, mkRecEqS, atomHeadCallCount,
            atomHeadCallCount.atomHeadCallCountList, BEq.beq, decide_true] at hbase
  stepsWrapRecursion := by
    intro eq hmem hstep
    simp [mkRecDef] at hmem
    rcases hmem with rfl | rfl
    · simp [HeadEquation.isStep, mkRecEq0, atomHeadCallCount,
            atomHeadCallCount.atomHeadCallCountList] at hstep
    · exact ⟨"s", [.expression [.symbol "mk", .var "n"]], by simp [mkRecEqS], by
        simp [mkRecDef, findRecursiveCallPos, BEq.beq]⟩
  lhsVarsRecoverableBase := by
    intro eq hmem hbase lhsPat hlhsPat v hv
    simp [mkRecDef] at hmem
    rcases hmem with rfl | rfl
    · simp [mkRecEq0] at hlhsPat; subst hlhsPat
      simp [atomFreeVars] at hv
    · simp [HeadEquation.isBase, mkRecEqS, atomHeadCallCount,
            atomHeadCallCount.atomHeadCallCountList, BEq.beq, decide_true] at hbase
  lhsVarsRecoverableStep := by
    intro eq hmem hstep lhsPat hlhsPat v hv
    simp [mkRecDef] at hmem
    rcases hmem with rfl | rfl
    · simp [HeadEquation.isStep, mkRecEq0, atomHeadCallCount,
            atomHeadCallCount.atomHeadCallCountList] at hstep
    · simp [mkRecEqS] at hlhsPat; subst hlhsPat
      simp [atomFreeVars, atomFreeVars.atomFreeVarsList] at hv; subst hv
      simp [mkRecDef, mkRecEqS, findRecursiveCallPos, BEq.beq,
            lhsArgVars, atomFreeVars]
  positionStable := by
    intro eq hmem hstep ctor outerArgs pre recArgs post hrhs hpos σ _hbinds
    simp [mkRecDef] at hmem
    rcases hmem with rfl | rfl
    · simp [HeadEquation.isStep, mkRecEq0, atomHeadCallCount,
            atomHeadCallCount.atomHeadCallCountList] at hstep
    · -- mkRecEqS: rhs = (s (mk $n)), outerArgs = [(mk $n)], pre = [], post = []
      simp [mkRecEqS] at hrhs
      obtain ⟨rfl, rfl⟩ := hrhs
      simp [mkRecDef, findRecursiveCallPos, BEq.beq] at hpos
      obtain ⟨rfl, rfl, rfl⟩ := hpos
      simp [mkRecDef, findRecursiveCallPos, applySubst.applySubstList, applySubst,
            BEq.beq]
  baseStepCtorDisjoint := by
    intro beq hmemb hbase seq hmems hstep bctor bargs sctor sargs hrhs_b hrhs_s
    simp [mkRecDef] at hmemb hmems
    rcases hmemb with rfl | rfl <;> rcases hmems with rfl | rfl
    · -- beq = mkRecEq0 (base), seq = mkRecEq0 — but mkRecEq0 is not a step
      simp [HeadEquation.isStep, mkRecEq0, atomHeadCallCount,
            atomHeadCallCount.atomHeadCallCountList] at hstep
    · -- beq = mkRecEq0 (base), seq = mkRecEqS (step): bctor = "z", sctor = "s"
      simp [mkRecEq0] at hrhs_b; simp [mkRecEqS] at hrhs_s
      obtain ⟨rfl, _⟩ := hrhs_b; obtain ⟨rfl, _⟩ := hrhs_s
      decide
    · -- beq = mkRecEqS — but it's not a base
      simp [HeadEquation.isBase, mkRecEqS, atomHeadCallCount,
            atomHeadCallCount.atomHeadCallCountList, BEq.beq, decide_true] at hbase
    · -- beq = mkRecEqS — but it's not a base
      simp [HeadEquation.isBase, mkRecEqS, atomHeadCallCount,
            atomHeadCallCount.atomHeadCallCountList, BEq.beq, decide_true] at hbase

#check @mkRecDef_invertible

end RecInvertible

/-! ## Step 4b/4c: Roundtrip theorems

The semantic correctness of the inverse: if forward evaluation produces a result,
reverse evaluation on that result recovers the original input.

### Approach

Rather than proving the most general roundtrip theorem immediately, we build up:

1. **matchAtom roundtrip** (already proven): `matchAtom [] pat conc = some σ → applySubst σ pat = conc`
2. **Non-overlap**: At most one equation matches any ground input
3. **Base roundtrip**: If `forwardEval` uses a base equation, `reverseEval` recovers the input
4. **Recursive roundtrip**: Induction on fuel, using base + step cases

### Non-overlap predicate

For a well-defined function, at most one equation matches any ground input.
This is stated as: if two equations both match the same input, they are the same. -/

/-- Self-matching with compatible accumulator: a pattern matches its own ground
    substitution, starting from any initial `σ₀` that is consistent with `σ`
    on variables already bound.

    "Compatible" means: for every variable `v`, if `Subst.lookup σ₀ v = some a`,
    then `applySubst σ (.var v) = a`.

    This generality is needed because `matchAtomList` threads the accumulator
    through head → tail, and after matching the head, the accumulator may contain
    bindings that the tail needs to be consistent with.

    Returns the existence of some `σ'` (the exact bindings aren't important
    for the roundtrip — only that match succeeds and `applySubst σ'` agrees
    with `applySubst σ` on the pattern). -/
def Subst.compatWith (σ₀ σ : Subst) : Prop :=
  ∀ v a, Subst.lookup σ₀ v = some a → applySubst σ (.var v) = a

/-- Construct a `MatchAtomRel` derivation for self-matching with compatible accumulator.
    Uses the MatchAtomRel inductive to avoid fighting with executable `matchAtom` unfolding. -/
theorem matchAtomRel_self_compat :
    ∀ (σ₀ : Subst) (pat : Atom) (σ : Subst),
    σ₀.compatWith σ →
    isGroundAtom (applySubst σ pat) = true →
    ∃ σ', MatchAtomRel σ₀ pat (applySubst σ pat) σ' ∧
      σ'.compatWith σ ∧
      applySubst σ' pat = applySubst σ pat := by
  intro σ₀ pat σ hcompat hg
  match pat with
  | .var v =>
    simp only [applySubst] at hg ⊢
    cases hlookup : Subst.lookup σ v with
    | none => simp [hlookup, isGroundAtom] at hg
    | some b =>
      simp only [hlookup, Option.getD] at hg ⊢
      cases hlookup₀ : Subst.lookup σ₀ v with
      | none =>
        -- Fresh: use var_fresh, output σ' = (v,b) :: σ₀
        exact ⟨(v, b) :: σ₀,
          MatchAtomRel.var_fresh hlookup₀,
          fun w a hw => by
            -- Subst.lookup ((v,b) :: σ₀) w = some a
            -- If w = v, then a = b and applySubst σ (.var v) = b
            -- If w ≠ v, falls through to σ₀
            by_cases hvw : v = w
            · subst hvw
              have : Subst.lookup ((v, b) :: σ₀) v = some b := by
                simp [Subst.lookup]
              rw [this] at hw; cases hw
              simp [applySubst, hlookup]
            · have hneq : Subst.lookup ((v, b) :: σ₀) w = Subst.lookup σ₀ w := by
                simp [Subst.lookup, beq_eq_false_iff_ne.mpr hvw]
              rw [hneq] at hw; exact hcompat w a hw,
          by simp [Subst.lookup]⟩
      | some b' =>
        -- Already bound: b' must equal b by compatibility
        have hb : b = b' := by
          have := hcompat v b' hlookup₀
          simp [applySubst, hlookup] at this; exact this
        subst hb
        exact ⟨σ₀,
          MatchAtomRel.var_bound hlookup₀,
          hcompat,
          by simp [hlookup₀]⟩
  | .symbol s =>
    exact ⟨σ₀, MatchAtomRel.symbol, hcompat, rfl⟩
  | .grounded g =>
    exact ⟨σ₀, MatchAtomRel.grounded, hcompat, rfl⟩
  | .expression es =>
    simp only [applySubst] at hg ⊢
    obtain ⟨σ', hrel, hc, happly⟩ := matchAtomRelList_self_compat σ₀ es σ hcompat hg
    exact ⟨σ', hrel, hc, by congr 1⟩
where
  matchAtomRelList_self_compat :
      ∀ (σ₀ : Subst) (es : List Atom) (σ : Subst),
      σ₀.compatWith σ →
      isGroundAtom.isGroundList (applySubst.applySubstList σ es) = true →
      ∃ σ', MatchAtomRel σ₀ (.expression es) (.expression (applySubst.applySubstList σ es)) σ' ∧
        σ'.compatWith σ ∧
        applySubst.applySubstList σ' es = applySubst.applySubstList σ es := by
    intro σ₀ es σ hcompat hg
    match es with
    | [] =>
      exact ⟨σ₀, MatchAtomRel.expr_nil, hcompat, rfl⟩
    | e :: es =>
      simp only [applySubst.applySubstList] at hg ⊢
      simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at hg
      -- Head: match e against applySubst σ e
      obtain ⟨σ1, hrel1, hcompat1, happly1⟩ := matchAtomRel_self_compat σ₀ e σ hcompat hg.1
      -- Tail: match es against applySubst.applySubstList σ es, starting from σ1
      obtain ⟨σ2, hrel2, hcompat2, happly2⟩ := matchAtomRelList_self_compat σ1 es σ hcompat1 hg.2
      refine ⟨σ2, MatchAtomRel.expr_cons hrel1 hrel2, hcompat2, ?_⟩
      congr 1
      -- Head stable under extension from σ1 to σ2
      have hg1 : isGroundAtom (applySubst σ1 e) = true := by rw [happly1]; exact hg.1
      have hm2 := matchAtom_complete hrel2
      have hext := matchAtom_lookupExtends.matchAtomList_lookupExtends (by
        simp only [matchAtom] at hm2; exact hm2)
      rw [applySubst_ground_ext hext hg1, happly1]

/-- Self-matching from empty accumulator: a pattern matches its own ground substitution. -/
theorem matchAtom_self_ground (pat : Atom) (σ : Subst)
    (hg : isGroundAtom (applySubst σ pat) = true) :
    ∃ σ', matchAtom [] pat (applySubst σ pat) = some σ' ∧
      σ'.compatWith σ ∧
      applySubst σ' pat = applySubst σ pat := by
  have hempty : Subst.compatWith [] σ := by
    intro v a h; simp [Subst.lookup, List.find?] at h
  obtain ⟨σ', hrel, hc, happly⟩ := matchAtomRel_self_compat [] pat σ hempty hg
  exact ⟨σ', matchAtom_complete hrel, hc, happly⟩

/-- If σ' is compatible with σ (every binding in σ' agrees with σ),
    and `applySubst σ' a` is ground, then `applySubst σ' a = applySubst σ a`. -/
theorem applySubst_compatWith_ground (σ' σ : Subst) (a : Atom)
    (hc : σ'.compatWith σ) (hg : isGroundAtom (applySubst σ' a) = true) :
    applySubst σ' a = applySubst σ a := by
  match a with
  | .var v =>
    unfold applySubst at hg ⊢
    cases hlookup : Subst.lookup σ' v with
    | some b =>
      simp only [Option.getD] at hg ⊢
      exact (hc v b hlookup).symm
    | none =>
      rw [hlookup] at hg; simp [Option.getD, isGroundAtom] at hg
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression es =>
    simp only [applySubst] at hg ⊢
    congr 1
    exact applySubstList_compatWith_ground σ' σ es hc hg
where
  applySubstList_compatWith_ground (σ' σ : Subst) :
      (es : List Atom) → σ'.compatWith σ →
      isGroundAtom.isGroundList (applySubst.applySubstList σ' es) = true →
      applySubst.applySubstList σ' es = applySubst.applySubstList σ es := by
    intro es hc hg
    match es with
    | [] => rfl
    | e :: rest =>
      simp only [applySubst.applySubstList] at hg ⊢
      simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at hg
      congr 1
      · exact applySubst_compatWith_ground σ' σ e hc hg.1
      · exact applySubstList_compatWith_ground σ' σ rest hc hg.2

/-- If `applySubst σ a` is ground, then every free variable of `a` has a
    ground binding in σ. -/
theorem applySubst_ground_var_bound :
    ∀ (σ : Subst) (a : Atom),
    isGroundAtom (applySubst σ a) = true →
    ∀ v ∈ atomFreeVars a, ∃ b, Subst.lookup σ v = some b ∧ isGroundAtom b = true := by
  intro σ a hg v hv
  match a with
  | .var w =>
    simp only [atomFreeVars, List.mem_cons, List.mem_nil_iff, or_false] at hv
    subst hv
    unfold applySubst at hg
    cases hlookup : Subst.lookup σ v with
    | some b =>
      rw [hlookup] at hg; simp only [Option.getD] at hg
      exact ⟨b, rfl, hg⟩
    | none =>
      rw [hlookup] at hg; simp [Option.getD, isGroundAtom] at hg
  | .symbol _ => simp only [atomFreeVars, List.not_mem_nil] at hv
  | .grounded _ => simp only [atomFreeVars, List.not_mem_nil] at hv
  | .expression es =>
    simp only [applySubst, isGroundAtom] at hg
    simp only [atomFreeVars] at hv
    exact applySubstList_ground_var_bound σ es hg v hv
where
  applySubstList_ground_var_bound :
      ∀ (σ : Subst) (es : List Atom),
      isGroundAtom.isGroundList (applySubst.applySubstList σ es) = true →
      ∀ v ∈ atomFreeVars.atomFreeVarsList es,
      ∃ b, Subst.lookup σ v = some b ∧ isGroundAtom b = true := by
    intro σ es hg v hv
    match es with
    | [] => simp only [atomFreeVars.atomFreeVarsList, List.not_mem_nil] at hv
    | e :: rest =>
      simp only [applySubst.applySubstList, isGroundAtom.isGroundList, Bool.and_eq_true] at hg
      simp only [atomFreeVars.atomFreeVarsList, List.mem_append] at hv
      cases hv with
      | inl hv => exact applySubst_ground_var_bound σ e hg.1 v hv
      | inr hv => exact applySubstList_ground_var_bound σ rest hg.2 v hv

/-- If every free variable of `a` has a ground binding in σ, then
    `applySubst σ a` is ground. -/
theorem applySubst_ground_of_bindings :
    ∀ (σ : Subst) (a : Atom),
    (∀ v ∈ atomFreeVars a, ∃ b, Subst.lookup σ v = some b ∧ isGroundAtom b = true) →
    isGroundAtom (applySubst σ a) = true := by
  intro σ a hbinds
  match a with
  | .var v =>
    simp only [applySubst]
    obtain ⟨b, hlookup, hg⟩ := hbinds v (by simp [atomFreeVars])
    simp only [hlookup]; exact hg
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression es =>
    simp only [applySubst, isGroundAtom]
    exact applySubstList_ground_of_bindings σ es (by
      intro v hv; exact hbinds v (by simp [atomFreeVars]; exact hv))
where
  applySubstList_ground_of_bindings :
      ∀ (σ : Subst) (es : List Atom),
      (∀ v ∈ atomFreeVars.atomFreeVarsList es,
        ∃ b, Subst.lookup σ v = some b ∧ isGroundAtom b = true) →
      isGroundAtom.isGroundList (applySubst.applySubstList σ es) = true := by
    intro σ es hbinds
    match es with
    | [] => rfl
    | e :: rest =>
      simp only [applySubst.applySubstList, isGroundAtom.isGroundList, Bool.and_eq_true]
      constructor
      · exact applySubst_ground_of_bindings σ e (fun v hv =>
          hbinds v (by simp [atomFreeVars.atomFreeVarsList, List.mem_append]; left; exact hv))
      · exact applySubstList_ground_of_bindings σ rest (fun v hv =>
          hbinds v (by simp [atomFreeVars.atomFreeVarsList, List.mem_append]; right; exact hv))

/-- Equation-local base inversion: if a base equation forward-evaluates an input
    to produce output, then `reverseMatchBase` on that output recovers the input.

    Hypotheses:
    - Single LHS pattern
    - Forward match succeeds: `matchAtom [] lhsPat inputArg = some σ`
    - Input is ground
    - Output (`applySubst σ rhs`) is ground
    - All LHS variables appear in the RHS (so reverse-matching the RHS
      recovers enough bindings to reconstruct the LHS) -/
theorem reverseMatchBase_inverts_forward
    (eq : HeadEquation) (lhsPat inputArg : Atom) (σ : Subst)
    (hlhs : eq.lhsArgs = [lhsPat])
    (hmatch : matchAtom [] lhsPat inputArg = some σ)
    (hground_in : isGroundAtom inputArg = true)
    (hground_out : isGroundAtom (applySubst σ eq.rhs) = true)
    (hlhsVarsCovered : ∀ v ∈ atomFreeVars lhsPat, v ∈ atomFreeVars eq.rhs) :
    reverseMatchBase eq (applySubst σ eq.rhs) = some inputArg := by
  -- Forward: σ recovers inputArg from lhsPat
  have hinput : applySubst σ lhsPat = inputArg :=
    matchAtom_applySubst_ground [] lhsPat inputArg σ hmatch hground_in
  -- Reverse: matchAtom on RHS pattern against ground output, with compatibility
  obtain ⟨σ', hrev, hcompat, happly_rhs⟩ := matchAtom_self_ground eq.rhs σ hground_out
  -- Step 1: applySubst σ' rhs is ground (rewrite via happly_rhs)
  have hg_rhs' : isGroundAtom (applySubst σ' eq.rhs) = true := by
    rw [happly_rhs]; exact hground_out
  -- Step 2: σ' binds all RHS free vars to ground atoms
  have hbinds_rhs := applySubst_ground_var_bound σ' eq.rhs hg_rhs'
  -- Step 3: all lhsPat vars are in rhs, so σ' binds them too
  have hbinds_lhs : ∀ v ∈ atomFreeVars lhsPat,
      ∃ b, Subst.lookup σ' v = some b ∧ isGroundAtom b = true :=
    fun v hv => hbinds_rhs v (hlhsVarsCovered v hv)
  -- Step 4: applySubst σ' lhsPat is ground
  have hg_lhs' : isGroundAtom (applySubst σ' lhsPat) = true :=
    applySubst_ground_of_bindings σ' lhsPat hbinds_lhs
  -- Step 5: by compatibility, applySubst σ' lhsPat = applySubst σ lhsPat = inputArg
  have heq_lhs : applySubst σ' lhsPat = inputArg := by
    rw [applySubst_compatWith_ground σ' σ lhsPat hcompat hg_lhs', hinput]
  -- Step 6: reverseMatchBase uses matchAtom on rhs, which gives σ', yielding applySubst σ' lhsPat
  simp only [reverseMatchBase, hlhs, hrev, heq_lhs]

/-! ## Step 4c1: Step-local inversion theorem -/

/-- List indexing: `pre ++ [x] ++ post` at position `pre.length` gives `x`. -/
theorem listGetAt_middle {α : Type*} (pre : List α) (x : α) (post : List α) :
    listGetAt (pre ++ [x] ++ post) pre.length = some x := by
  induction pre with
  | nil => simp [listGetAt]
  | cons h t ih =>
    simp only [List.cons_append, List.length_cons, listGetAt]
    exact ih

/-- Applying a substitution to a list preserves length. -/
theorem applySubstList_length (σ : Subst) (ps : List Atom) :
    (applySubst.applySubstList σ ps).length = ps.length := by
  induction ps with
  | nil => rfl
  | cons p rest ih => simp [applySubst.applySubstList, ih]

/-- List version of `matchAtom_self_ground`: matching a list of patterns against
    their own ground substitution succeeds, and the result is compatible with σ. -/
theorem matchAtomList_self_ground (ps : List Atom) (σ : Subst)
    (hg : isGroundAtom.isGroundList (applySubst.applySubstList σ ps) = true) :
    ∃ σ', matchAtom.matchAtomList [] ps (applySubst.applySubstList σ ps) = some σ' ∧
      σ'.compatWith σ ∧
      applySubst.applySubstList σ' ps = applySubst.applySubstList σ ps := by
  have hempty : Subst.compatWith [] σ := fun v a h => by
    simp [Subst.lookup, List.find?] at h
  obtain ⟨σ', hrel, hcompat, happly⟩ :=
    matchAtomRel_self_compat [] (.expression ps) σ hempty hg
  refine ⟨σ', ?_, hcompat, ?_⟩
  · have hm := matchAtom_complete hrel
    simp only [matchAtom] at hm; exact hm
  · -- happly : .expression (applySubst.applySubstList σ' ps) = .expression (applySubst.applySubstList σ ps)
    simp only [applySubst] at happly
    exact Atom.expression.inj happly

/-- applySubstList distributes over append. -/
theorem applySubstList_append (σ : Subst) (as bs : List Atom) :
    applySubst.applySubstList σ (as ++ bs) =
    applySubst.applySubstList σ as ++ applySubst.applySubstList σ bs := by
  induction as with
  | nil => simp [applySubst.applySubstList]
  | cons h t ih => simp [applySubst.applySubstList, ih]

/-- `lhsArgVars` equals `atomFreeVars.atomFreeVarsList` pointwise — both collect free variables
    from each atom in a list and concatenate the results. -/
theorem lhsArgVars_eq_atomFreeVarsList (as : List Atom) :
    lhsArgVars as = atomFreeVars.atomFreeVarsList as := by
  induction as with
  | nil => rfl
  | cons h t ih => simp [lhsArgVars, atomFreeVars.atomFreeVarsList, ih]

/-- take of prefix length recovers the prefix. -/
theorem List.take_prefix {α : Type*} (as bs : List α) :
    (as ++ bs).take as.length = as := by
  induction as with
  | nil => simp
  | cons h t ih => simp [List.take_succ_cons, ih]

/-- drop middle: dropping pre.length + 1 from (pre ++ [x] ++ post) gives post. -/
theorem List.drop_middle {α : Type*} (pre : List α) (x : α) (post : List α) :
    (pre ++ [x] ++ post).drop (pre.length + 1) = post := by
  induction pre with
  | nil => simp
  | cons _ t ih => simp [List.drop_succ_cons]

theorem reverseMatchStep_inverts_forward
    (eq : HeadEquation) (funcName : String) (lhsPat arg : Atom) (σ : Subst)
    (ctor : String) (outerArgs pre post : List Atom) (recArgPat : Atom)
    (innerResult : Atom)
    (hlhs : eq.lhsArgs = [lhsPat])
    (hrhs : eq.rhs = .expression (.symbol ctor :: outerArgs))
    (hpos : findRecursiveCallPos funcName outerArgs = some (pre, [recArgPat], post))
    (hmatch : matchAtom [] lhsPat arg = some σ)
    (hground_arg : isGroundAtom arg = true)
    (_hground_inner : isGroundAtom innerResult = true)
    /- All vars in pre ++ post are LHS vars (from varsCovered, ensures outer shell is ground) -/
    (houter_vars : ∀ v ∈ lhsArgVars (pre ++ post), v ∈ lhsArgVars eq.lhsArgs) :
    let preS := applySubst.applySubstList σ pre
    let postS := applySubst.applySubstList σ post
    let result := .expression (.symbol ctor :: preS ++ [innerResult] ++ postS)
    ∃ σ_outer,
      reverseMatchStep eq funcName result = some (σ_outer, innerResult) ∧
      σ_outer.compatWith σ ∧
      applySubst.applySubstList σ_outer (pre ++ post) =
        applySubst.applySubstList σ (pre ++ post) := by
  simp only
  -- Shape facts
  have hspec := findRecursiveCallPos_spec funcName outerArgs pre [recArgPat] post hpos
  have hpreS_len : (applySubst.applySubstList σ pre).length = pre.length := applySubstList_length σ pre
  -- Length of queryOuter = length of outerArgs
  have hlen : (applySubst.applySubstList σ pre ++ [innerResult] ++ applySubst.applySubstList σ post).length
              = outerArgs.length := by
    simp only [List.length_append, List.length_singleton, hpreS_len, applySubstList_length]
    rw [hspec]; simp [List.length_append]; omega
  -- listGetAt at pre.length gives innerResult
  have hget : listGetAt (applySubst.applySubstList σ pre ++ [innerResult] ++ applySubst.applySubstList σ post)
              pre.length = some innerResult := by
    rw [← hpreS_len]; exact listGetAt_middle _ innerResult _
  -- take pre.length recovers σ(pre)
  have htake : (applySubst.applySubstList σ pre ++ [innerResult] ++ applySubst.applySubstList σ post).take
               pre.length = applySubst.applySubstList σ pre := by
    rw [← hpreS_len, List.append_assoc]; exact List.take_prefix _ _
  -- drop (pre.length + 1) recovers σ(post)
  have hdrop : (applySubst.applySubstList σ pre ++ [innerResult] ++ applySubst.applySubstList σ post).drop
               (pre.length + 1) = applySubst.applySubstList σ post := by
    rw [← hpreS_len]; exact List.drop_middle _ innerResult _
  -- σ binds all LHS vars to ground atoms
  have hlhsvars : ∀ v ∈ lhsArgVars eq.lhsArgs, ∃ b, Subst.lookup σ v = some b ∧ isGroundAtom b = true := by
    intro v hv
    simp only [lhsArgVars, hlhs, List.append_nil] at hv
    exact applySubst_ground_var_bound σ lhsPat
      (matchAtom_applySubst_ground [] lhsPat arg σ hmatch hground_arg ▸ hground_arg) v hv
  -- Outer shell σ(pre ++ post) is ground
  have hground_outer : isGroundAtom.isGroundList (applySubst.applySubstList σ (pre ++ post)) = true :=
    applySubst_ground_of_bindings.applySubstList_ground_of_bindings σ (pre ++ post)
      fun v hv => hlhsvars v (houter_vars v (lhsArgVars_eq_atomFreeVarsList _ ▸ hv))
  -- Self-match the outer shell pre ++ post against σ(pre ++ post)
  obtain ⟨σ_outer, hmatch_outer, hcompat, happly_outer⟩ :=
    matchAtomList_self_ground (pre ++ post) σ hground_outer
  rw [applySubstList_append σ pre post] at hmatch_outer
  -- Show reverseMatchStep produces the right result
  refine ⟨σ_outer, ?_, hcompat, ?_⟩
  simp only [reverseMatchStep, hrhs, hpos]
  -- The goal has `match Atom.expression X with | Atom.expression (Atom.symbol qctor :: qo) => ...`
  -- Reduce by definitional equality (iota on the constructor match).
  show (if (ctor == ctor &&
          (applySubst.applySubstList σ pre ++ [innerResult] ++
           applySubst.applySubstList σ post).length == outerArgs.length) = true then
         match listGetAt (applySubst.applySubstList σ pre ++ [innerResult] ++
               applySubst.applySubstList σ post) pre.length with
         | some innerQuery =>
           match matchAtom.matchAtomList [] (pre ++ post)
               (List.take pre.length (applySubst.applySubstList σ pre ++ [innerResult] ++
                  applySubst.applySubstList σ post) ++
                List.drop (pre.length + 1) (applySubst.applySubstList σ pre ++ [innerResult] ++
                  applySubst.applySubstList σ post)) with
           | some σ' => some (σ', innerQuery)
           | none => none
         | none => none
       else none) = some (σ_outer, innerResult)
  -- Prove the boolean guard condition
  have hcond : (ctor == ctor && (applySubst.applySubstList σ pre ++ [innerResult] ++
      applySubst.applySubstList σ post).length == outerArgs.length) = true := by
    rw [beq_self_eq_true, Bool.true_and, hlen, beq_self_eq_true]
  simp only [hcond, ite_true, hget, htake, hdrop, hmatch_outer]
  simpa [applySubstList_append] using happly_outer

/-! ## Canary: forward/reverse eval on recursive example -/

section RecCanary

-- mkRecDef: (= (mk 0) (z)),  (= (mk (S $n)) (s (mk $n)))
-- Forward: mk (S (S 0)) should give (s (s (z)))
-- Reverse: from (s (s (z))) should recover (S (S 0))

private def s0 : Atom := .symbol "0"
private def sS (a : Atom) : Atom := .expression [.symbol "S", a]
private def sz : Atom := .expression [.symbol "z"]
private def ss (a : Atom) : Atom := .expression [.symbol "s", a]

-- Forward: mk(0) = (z)
example : forwardEval mkRecDef 3 s0 = some sz := by decide
-- Forward: mk(S(0)) = (s (z))
example : forwardEval mkRecDef 3 (sS s0) = some (ss sz) := by decide
-- Forward: mk(S(S(0))) = (s (s (z)))
example : forwardEval mkRecDef 3 (sS (sS s0)) = some (ss (ss sz)) := by decide

-- Reverse: (z) → 0
example : reverseEval mkRecDef 3 sz = some s0 := by decide
-- Reverse: (s (z)) → S(0)
example : reverseEval mkRecDef 3 (ss sz) = some (sS s0) := by decide
-- Reverse: (s (s (z))) → S(S(0))
example : reverseEval mkRecDef 3 (ss (ss sz)) = some (sS (sS s0)) := by decide

end RecCanary

/-! ## Step 4c2: Helper lemmas for the roundtrip theorem -/

/-- If all elements map to either `none` or `some b`, and some element maps to `some b`,
    then `findSome?` returns `some b`. -/
theorem List.findSome?_unique {α β : Type*} {f : α → Option β} {l : List α} {b : β}
    (hmem : ∃ a ∈ l, f a = some b)
    (huniq : ∀ a ∈ l, f a = none ∨ f a = some b) :
    l.findSome? f = some b := by
  induction l with
  | nil =>
    obtain ⟨_, ha, _⟩ := hmem
    cases ha
  | cons x xs ih =>
    simp only [List.findSome?_cons]
    cases hfx : f x with
    | some val =>
      -- f x = some val, and huniq says f x = none ∨ f x = some b
      have := huniq x (by simp)
      rcases this with h | h
      · rw [hfx] at h; cases h
      · rw [hfx] at h; exact Option.some.inj h ▸ rfl
    | none =>
      exact ih
        (by obtain ⟨a, ha, hfa⟩ := hmem
            cases ha with
            | head => rw [hfa] at hfx; cases hfx
            | tail _ h => exact ⟨a, h, hfa⟩)
        (fun a ha => huniq a (List.mem_cons_of_mem _ ha))

/-- If `matchAtom [] (.expression (.symbol s :: ps)) (.expression (.symbol ctor :: qs))`
    succeeds, then `s = ctor`. -/
theorem matchAtom_expression_symbol_head {s ctor : String} {ps qs : List Atom} {σ : Subst}
    (h : matchAtom [] (.expression (.symbol s :: ps)) (.expression (.symbol ctor :: qs)) = some σ) :
    s = ctor := by
  by_cases hs : s = ctor
  · exact hs
  · simp [matchAtom] at h
    simp [matchAtom.matchAtomList, matchAtom, hs] at h

/-- Substitution preserves symbol heads: `applySubst σ (.expression (.symbol s :: args))`
    equals `.expression (.symbol s :: applySubstList σ args)`. -/
theorem applySubst_expression_symbol (σ : Subst) (s : String) (args : List Atom) :
    applySubst σ (.expression (.symbol s :: args)) =
    .expression (.symbol s :: applySubst.applySubstList σ args) := by
  simp [applySubst, applySubst.applySubstList]

/-- If `reverseMatchBase eq' queryArg = some x` and `eq'` is a base equation
    in an `InvertibleHead` with `queryArg = .expression (.symbol ctor :: _)`,
    then `eq'.rhs` has outer constructor `ctor`. -/
theorem reverseMatchBase_implies_same_ctor
    (def_ : HeadFuncDef) (hinv : InvertibleHead def_)
    (eq' : HeadEquation) (hbase' : eq'.isBase = true) (hmem' : eq' ∈ def_.equations)
    (ctor : String) (qargs : List Atom)
    (x : Atom)
    (hrm : reverseMatchBase eq' (.expression (.symbol ctor :: qargs)) = some x) :
    ∃ args, eq'.rhs = .expression (.symbol ctor :: args) := by
  obtain ⟨ctor', args', hrhs'⟩ := hinv.basesAreCtorApps eq' hmem' hbase'
  unfold reverseMatchBase at hrm
  rw [hrhs'] at hrm
  cases heq : eq'.lhsArgs with
  | nil => simp [heq] at hrm
  | cons lhsPat rest =>
    cases rest with
    | nil =>
      simp only [heq] at hrm
      cases hmatch : matchAtom [] (.expression (.symbol ctor' :: args'))
          (.expression (.symbol ctor :: qargs)) with
      | none => simp [hmatch] at hrm
      | some σ =>
        have := matchAtom_expression_symbol_head hmatch
        subst this; exact ⟨args', hrhs'⟩
    | cons _ _ => simp [heq] at hrm

/-- `isGroundList` distributes over append. -/
theorem isGroundList_append (xs ys : List Atom) :
    isGroundAtom.isGroundList (xs ++ ys) =
    (isGroundAtom.isGroundList xs && isGroundAtom.isGroundList ys) := by
  induction xs with
  | nil => simp [isGroundAtom.isGroundList]
  | cons x xs ih =>
    simp only [List.cons_append, isGroundAtom.isGroundList, ih, Bool.and_assoc]

/-- `atomFreeVarsList` distributes over append. -/
theorem atomFreeVarsList_append (xs ys : List Atom) :
    atomFreeVars.atomFreeVarsList (xs ++ ys) =
    atomFreeVars.atomFreeVarsList xs ++ atomFreeVars.atomFreeVarsList ys := by
  induction xs with
  | nil => simp [atomFreeVars.atomFreeVarsList]
  | cons x xs ih =>
    simp only [List.cons_append, atomFreeVars.atomFreeVarsList, ih, List.append_assoc]

/-- If `v ∈ atomFreeVars a` and `a ∈ as`, then `v ∈ atomFreeVarsList as`. -/
theorem mem_atomFreeVarsList_of_mem {v : String} {a : Atom} {as : List Atom}
    (ha : a ∈ as) (hv : v ∈ atomFreeVars a) :
    v ∈ atomFreeVars.atomFreeVarsList as := by
  induction as with
  | nil => exact absurd ha List.not_mem_nil
  | cons x xs ih =>
    simp only [atomFreeVars.atomFreeVarsList, List.mem_append]
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · left; exact hv
    · right; exact ih ha

/-- A recursive call variable appears in the free variables of the RHS.
    Specifically, if `findRecursiveCallPos` finds `(pre, recArgs, post)` in `outerArgs`,
    and `v ∈ lhsArgVars recArgs`, then `v ∈ atomFreeVarsList outerArgs`. -/
theorem recArgVar_in_outerFreeVars {funcName : String} {outerArgs pre recArgs post : List Atom}
    (hpos : findRecursiveCallPos funcName outerArgs = some (pre, recArgs, post))
    {v : String} (hv : v ∈ lhsArgVars recArgs) :
    v ∈ atomFreeVars.atomFreeVarsList outerArgs := by
  have hdecomp := findRecursiveCallPos_spec funcName outerArgs pre recArgs post hpos
  rw [hdecomp]
  -- outerArgs = pre ++ [.expression (.symbol funcName :: recArgs)] ++ post
  -- v ∈ atomFreeVarsList of the middle element
  apply mem_atomFreeVarsList_of_mem
  · simp [List.mem_append]; right; left; rfl
  · -- v ∈ atomFreeVars (.expression (.symbol funcName :: recArgs))
    simp only [atomFreeVars, atomFreeVars.atomFreeVarsList]
    -- = atomFreeVarsList (.symbol funcName :: recArgs)
    -- = atomFreeVars (.symbol funcName) ++ atomFreeVarsList recArgs
    -- = [] ++ atomFreeVarsList recArgs
    simp only [List.nil_append]
    exact lhsArgVars_eq_atomFreeVarsList recArgs ▸ hv

/-- If every element maps to `none`, then `findSome?` returns `none`. -/
theorem List.findSome?_eq_none_of_all {α β : Type*} {f : α → Option β} {l : List α}
    (h : ∀ a ∈ l, f a = none) : l.findSome? f = none := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.findSome?_cons]
    rw [h x List.mem_cons_self]
    exact ih fun a ha => h a (List.mem_cons_of_mem _ ha)

/-- A base equation's `reverseMatchBase` returns `none` when the query has a
    different outer constructor. -/
theorem reverseMatchBase_none_of_ctor_ne (eq' : HeadEquation)
    (hinv_base : ∃ bctor bargs, eq'.rhs = .expression (.symbol bctor :: bargs))
    (ctor : String) (queryParts : List Atom)
    (hne : ∀ bctor bargs, eq'.rhs = .expression (.symbol bctor :: bargs) → bctor ≠ ctor) :
    reverseMatchBase eq' (.expression (.symbol ctor :: queryParts)) = none := by
  obtain ⟨bctor, bargs, hrhs'⟩ := hinv_base
  unfold reverseMatchBase
  rw [hrhs']
  cases heq_lhs : eq'.lhsArgs with
  | nil => simp
  | cons lhsPat rest =>
    cases rest with
    | cons _ _ => simp
    | nil =>
      simp only []
      cases hmatch : matchAtom [] (.expression (.symbol bctor :: bargs))
          (.expression (.symbol ctor :: queryParts)) with
      | none => rfl
      | some σ' =>
        exfalso; exact hne bctor bargs hrhs' (matchAtom_expression_symbol_head hmatch)

theorem reverseEval_base_sweep_none_of_step_ctor
    (def_ : HeadFuncDef) (hinv : InvertibleHead def_)
    (ctor : String) (queryParts sargs : List Atom)
    (seq : HeadEquation) (hseq_mem : seq ∈ def_.equations) (hstep : seq.isStep = true)
    (hrhs : seq.rhs = .expression (.symbol ctor :: sargs)) :
    (def_.equations.findSome? fun eq' =>
      if eq'.isBase then reverseMatchBase eq' (.expression (.symbol ctor :: queryParts))
      else none) = none := by
  apply List.findSome?_eq_none_of_all
  intro eq' hmem'
  by_cases hbase' : eq'.isBase = true
  · simp only [hbase', ite_true]
    apply reverseMatchBase_none_of_ctor_ne eq'
      (hinv.basesAreCtorApps eq' hmem' hbase') ctor queryParts
    intro bctor bargs hrhs'
    exact hinv.baseStepCtorDisjoint eq' hmem' hbase' seq hseq_mem hstep bctor bargs
      ctor sargs hrhs' hrhs
  · simp [hbase']

/-- If `reverseMatchStep` succeeds on an expression with outer ctor `c`,
    then the equation's RHS also has outer ctor `c`. -/
theorem reverseMatchStep_implies_ctor (eq' : HeadEquation) (funcName : String)
    (c : String) (qs : List Atom) (σ' : Subst) (innerQ : Atom)
    (h : reverseMatchStep eq' funcName (.expression (.symbol c :: qs)) = some (σ', innerQ)) :
    ∃ outerArgs, eq'.rhs = .expression (.symbol c :: outerArgs) := by
  unfold reverseMatchStep at h
  cases hrhs' : eq'.rhs with
  | var _ => rw [hrhs'] at h; simp at h
  | symbol _ => rw [hrhs'] at h; simp at h
  | grounded _ => rw [hrhs'] at h; simp at h
  | expression es =>
    rw [hrhs'] at h
    cases es with
    | nil => simp at h
    | cons hd tl =>
      cases hd with
      | symbol s =>
        simp only [] at h
        cases hfr : findRecursiveCallPos funcName tl with
        | none => simp [hfr] at h
        | some val =>
          simp only [hfr] at h
          -- h has: if (s == c && ...) then ... else none = some ...
          split at h
          · rename_i hcond
            -- s == c is true
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            obtain ⟨hsc, _⟩ := hcond; subst hsc
            exact ⟨tl, rfl⟩
          · simp at h
      | _ => simp at h

/-! ## Step 4c2: Full roundtrip theorem

The main semantic correctness result: if `forwardEval` produces an output,
`reverseEval` recovers the original input.

### Hypotheses beyond `InvertibleHead`

- `singleLhsArg`: each equation has exactly one LHS pattern
- `distinctOuterCtors`: different equations have different outer RHS constructors,
  so the source equation can be uniquely identified from the output shape
- `singleRecArg`: step equations have a single recursive-call argument variable
  (matches the `[.var recVar]` case in `reverseEval`)

These are structural well-formedness conditions satisfied by every PoC example. -/

/-- Additional shape hypotheses making the current invertible fragment
explicitly deterministic and singleton-valued at the backend boundary.

`InvertibleHead` captures the core semantic invertibility conditions. This
structure packages the extra assumptions used by the current theorem stack:
- each equation has exactly one LHS pattern
- outer RHS constructors determine the source equation uniquely
- each recursive call carries exactly one recursive argument variable
- every equation is either a base case or a step case

Keeping these assumptions bundled makes the fragment boundary explicit and helps
avoid silently widening the current theorems beyond the intended deterministic
PoC fragment. -/
structure DeterministicInvertibleFragment (def_ : HeadFuncDef) : Prop where
  hinv : InvertibleHead def_
  singleLhsArg : ∀ eq ∈ def_.equations, ∃ lhsPat, eq.lhsArgs = [lhsPat]
  distinctOuterCtors : ∀ eq1 ∈ def_.equations, ∀ eq2 ∈ def_.equations,
      ∀ (ctor : String) (args1 args2 : List Atom),
      eq1.rhs = .expression (.symbol ctor :: args1) →
      eq2.rhs = .expression (.symbol ctor :: args2) →
      eq1 = eq2
  singleRecArg : ∀ eq ∈ def_.equations, eq.isStep = true →
      ∀ (ctor : String) (outerArgs pre recArgs post : List Atom),
      eq.rhs = .expression (.symbol ctor :: outerArgs) →
      findRecursiveCallPos def_.funcName outerArgs = some (pre, recArgs, post) →
      ∃ rv, recArgs = [.var rv]
  allBaseOrStep : ∀ eq ∈ def_.equations, eq.isBase = true ∨ eq.isStep = true

/-- Forward evaluation preserves groundness: if the input is ground and all equations
    have variables covered, then the output is ground. -/
theorem forwardEval_ground
    (def_ : HeadFuncDef) (hinv : InvertibleHead def_)
    (hsingle : ∀ eq ∈ def_.equations, ∃ lhsPat, eq.lhsArgs = [lhsPat])
    (fuel : Nat) (arg out : Atom)
    (hfwd : forwardEval def_ fuel arg = some out)
    (hground : isGroundAtom arg = true) :
    isGroundAtom out = true := by
  induction fuel generalizing arg out with
  | zero => simp [forwardEval] at hfwd
  | succ k ih =>
    simp only [forwardEval] at hfwd
    obtain ⟨eq, heq_mem, heq_match⟩ := List.exists_of_findSome?_eq_some hfwd
    obtain ⟨lhsPat, hlhs⟩ := hsingle eq heq_mem
    simp only [hlhs] at heq_match
    cases hm : matchAtom [] lhsPat arg with
    | none => simp [hm] at heq_match
    | some σ =>
      simp [hm] at heq_match
      have hinput : applySubst σ lhsPat = arg :=
        matchAtom_applySubst_ground [] lhsPat arg σ hm hground
      have hlhsvars : ∀ v ∈ lhsArgVars eq.lhsArgs,
          ∃ b, Subst.lookup σ v = some b ∧ isGroundAtom b = true := by
        intro v hv
        simp only [lhsArgVars, hlhs, List.append_nil] at hv
        exact applySubst_ground_var_bound σ lhsPat (hinput ▸ hground) v hv
      have hrhsvars : ∀ v ∈ atomFreeVars eq.rhs,
          ∃ b, Subst.lookup σ v = some b ∧ isGroundAtom b = true :=
        fun v hv => hlhsvars v (hinv.varsCovered eq heq_mem v hv)
      have hground_rhs : isGroundAtom (applySubst σ eq.rhs) = true :=
        applySubst_ground_of_bindings σ eq.rhs hrhsvars
      by_cases hbase : eq.isBase = true
      · -- BASE: out = applySubst σ eq.rhs which is ground
        simp [hbase] at heq_match; subst heq_match; exact hground_rhs
      · -- STEP: out = .expression (ctor :: preS ++ [innerResult] ++ postS)
        have hbase_false : eq.isBase = false := by cases h : eq.isBase <;> simp_all
        simp only [hbase_false] at heq_match
        -- Match on the structure of applySubst σ eq.rhs
        cases hrhs_eq : applySubst σ eq.rhs with
        | var => rw [hrhs_eq] at hground_rhs; simp [isGroundAtom] at hground_rhs
        | symbol s => rw [hrhs_eq] at heq_match; simp at heq_match
        | grounded => rw [hrhs_eq] at heq_match; simp at heq_match
        | expression es =>
          rw [hrhs_eq] at heq_match
          cases es with
          | nil => simp at heq_match
          | cons hd tl =>
            cases hd with
            | symbol ctor =>
              simp only [] at heq_match
              cases hfr : findRecursiveCallPos def_.funcName tl with
              | none => simp [hfr] at heq_match
              | some val =>
                simp only [hfr] at heq_match
                cases val with
                | mk pre rest =>
                  cases rest with
                  | mk recArgsVal post =>
                    cases recArgsVal with
                    | nil => simp at heq_match
                    | cons recArg rest =>
                      cases rest with
                      | cons _ _ => simp at heq_match
                      | nil =>
                        simp only [] at heq_match
                        cases hfwd' : forwardEval def_ k recArg with
                        | none => simp [hfwd', Option.map] at heq_match
                        | some innerResult =>
                          simp [hfwd', Option.map] at heq_match; subst heq_match
                          -- out = .expression (ctor :: pre ++ [innerResult] ++ post)
                          -- pre and post are ground (from hground_rhs decomposed)
                          rw [hrhs_eq] at hground_rhs
                          simp only [isGroundAtom, isGroundAtom.isGroundList] at hground_rhs ⊢
                          -- recArg is part of the ground substituted RHS
                          have hdecomp := findRecursiveCallPos_spec def_.funcName tl pre [recArg] post hfr
                          rw [hdecomp] at hground_rhs
                          -- Decompose groundness across the append
                          simp only [isGroundAtom, isGroundAtom.isGroundList,
                            isGroundList_append, Bool.and_eq_true] at hground_rhs ⊢
                          -- Extract recArg groundness
                          have hrecarg_ground : isGroundAtom recArg = true :=
                            hground_rhs.2.1.2.1.2.1
                          have hinner_ground := ih recArg innerResult hfwd' hrecarg_ground
                          exact ⟨trivial, hground_rhs.2.1.1, hinner_ground, hground_rhs.2.2⟩
            | _ => simp at heq_match

/-- If `forwardEval` produces a ground output from a ground input under an
    `InvertibleHead` function definition with distinct outer constructors,
    then `reverseEval` recovers the original input.

    This is the core soundness theorem for the staged inverse compilation. -/
theorem reverseEval_inverts_forwardEval
    (def_ : HeadFuncDef) (hinv : InvertibleHead def_)
    (hsingle : ∀ eq ∈ def_.equations, ∃ lhsPat, eq.lhsArgs = [lhsPat])
    (hdistinct : ∀ eq1 ∈ def_.equations, ∀ eq2 ∈ def_.equations,
      ∀ (ctor : String) (args1 args2 : List Atom),
      eq1.rhs = .expression (.symbol ctor :: args1) →
      eq2.rhs = .expression (.symbol ctor :: args2) →
      eq1 = eq2)
    (hsingleRec : ∀ eq ∈ def_.equations, eq.isStep = true →
      ∀ (ctor : String) (outerArgs pre recArgs post : List Atom),
      eq.rhs = .expression (.symbol ctor :: outerArgs) →
      findRecursiveCallPos def_.funcName outerArgs = some (pre, recArgs, post) →
      ∃ rv, recArgs = [.var rv])
    (hallBaseOrStep : ∀ eq ∈ def_.equations, eq.isBase = true ∨ eq.isStep = true)
    (fuel : Nat) (arg out : Atom)
    (hfwd : forwardEval def_ fuel arg = some out)
    (hground : isGroundAtom arg = true) :
    reverseEval def_ fuel out = some arg := by
  induction fuel generalizing arg out with
  | zero => simp [forwardEval] at hfwd
  | succ k ih =>
    -- forwardEval found some equation via findSome?
    simp only [forwardEval] at hfwd
    obtain ⟨eq, heq_mem, heq_match⟩ := List.exists_of_findSome?_eq_some hfwd
    -- eq has a single LHS pattern
    obtain ⟨lhsPat, hlhs⟩ := hsingle eq heq_mem
    simp only [hlhs] at heq_match
    -- matchAtom succeeded
    cases hm : matchAtom [] lhsPat arg with
    | none => simp [hm] at heq_match
    | some σ =>
      simp [hm] at heq_match
      -- The forward roundtrip: applySubst σ lhsPat = arg
      have hinput : applySubst σ lhsPat = arg :=
        matchAtom_applySubst_ground [] lhsPat arg σ hm hground
      -- σ binds all LHS vars to ground atoms
      have hlhsvars : ∀ v ∈ lhsArgVars eq.lhsArgs,
          ∃ b, Subst.lookup σ v = some b ∧ isGroundAtom b = true := by
        intro v hv
        simp only [lhsArgVars, hlhs, List.append_nil] at hv
        exact applySubst_ground_var_bound σ lhsPat (hinput ▸ hground) v hv
      -- σ binds all RHS free vars (by varsCovered)
      have hrhsvars : ∀ v ∈ atomFreeVars eq.rhs,
          ∃ b, Subst.lookup σ v = some b ∧ isGroundAtom b = true :=
        fun v hv => hlhsvars v (hinv.varsCovered eq heq_mem v hv)
      -- applySubst σ rhs is ground
      have hground_out : isGroundAtom (applySubst σ eq.rhs) = true :=
        applySubst_ground_of_bindings σ eq.rhs hrhsvars
      -- Split on base vs step
      by_cases hbase : eq.isBase = true
      · -- BASE CASE
        -- out = applySubst σ eq.rhs
        simp [hbase] at heq_match
        subst heq_match
        -- reverseMatchBase recovers arg
        have hrb := reverseMatchBase_inverts_forward eq lhsPat arg σ hlhs hm hground
          hground_out (hinv.lhsVarsRecoverableBase eq heq_mem hbase lhsPat
            (by simp [hlhs]))
        -- eq.rhs has constructor form
        obtain ⟨ctor, rhs_args, hrhs⟩ := hinv.basesAreCtorApps eq heq_mem hbase
        -- reverseEval's base sweep finds eq and returns arg
        simp only [reverseEval]
        suffices hsuff :
            (def_.equations.findSome? fun eq' =>
              if eq'.isBase then reverseMatchBase eq' (applySubst σ eq.rhs) else none) =
            some arg by
          simp [hsuff]
        -- Use findSome?_unique: all base eqs return none or some arg
        apply List.findSome?_unique
        · exact ⟨eq, heq_mem, by simp [hbase, hrb]⟩
        · intro eq' hmem'
          by_cases hbase' : eq'.isBase = true
          · simp only [hbase', ite_true]
            -- reverseMatchBase eq' (applySubst σ eq.rhs) is either none or some arg
            cases hrm' : reverseMatchBase eq' (applySubst σ eq.rhs) with
            | none => left; rfl
            | some x =>
              right
              -- Rewrite eq.rhs to expose its constructor form
              rw [hrhs, applySubst_expression_symbol] at hrm' hrb
              -- eq'.rhs must have the same outer ctor
              obtain ⟨args', hrhs'⟩ :=
                reverseMatchBase_implies_same_ctor def_ hinv eq' hbase' hmem'
                  ctor _ x hrm'
              -- By hdistinct, eq' = eq
              have heq_eq := hdistinct eq heq_mem eq' hmem' ctor rhs_args args' hrhs hrhs'
              subst heq_eq
              rw [hrb] at hrm'
              exact hrm'.symm
          · simp [hbase']
      · -- STEP CASE: eq is a step equation
        have hstep : eq.isStep = true := by
          rcases hallBaseOrStep eq heq_mem with h | h
          · exact absurd h hbase
          · exact h
        -- Extract RHS structure from stepsWrapRecursion
        obtain ⟨ctor, outerArgs, hrhs, hpos_ne⟩ :=
          hinv.stepsWrapRecursion eq heq_mem hstep
        -- findRecursiveCallPos succeeds
        obtain ⟨pre, recArgs, post, hpos⟩ : ∃ pre recArgs post,
            findRecursiveCallPos def_.funcName outerArgs = some (pre, recArgs, post) := by
          cases hfr : findRecursiveCallPos def_.funcName outerArgs with
          | none => exact (hpos_ne hfr).elim
          | some val => exact ⟨val.1, val.2.1, val.2.2, rfl⟩
        -- recArgs is a single variable
        obtain ⟨rv, hrv⟩ := hsingleRec eq heq_mem hstep ctor outerArgs pre recArgs post hrhs hpos
        subst hrv
        -- rv is an LHS variable (via varsCovered)
        have hrv_lhs : rv ∈ lhsArgVars eq.lhsArgs := by
          apply hinv.varsCovered eq heq_mem rv
          rw [hrhs]; simp only [atomFreeVars]
          exact recArgVar_in_outerFreeVars hpos
            (by simp [lhsArgVars, atomFreeVars])
        -- applySubst σ eq.rhs structure
        have hrhs_subst : applySubst σ eq.rhs =
            .expression (.symbol ctor :: applySubst.applySubstList σ outerArgs) := by
          rw [hrhs, applySubst_expression_symbol]
        -- positionStable on substituted args
        have hpos_subst : findRecursiveCallPos def_.funcName
            (applySubst.applySubstList σ outerArgs) =
            some (applySubst.applySubstList σ pre,
                  [applySubst σ (.var rv)],
                  applySubst.applySubstList σ post) := by
          have := hinv.positionStable eq heq_mem hstep ctor outerArgs pre [.var rv] post
            hrhs hpos σ hlhsvars
          simp only [applySubst.applySubstList] at this
          exact this
        -- Simplify heq_match: since ¬isBase, the else branch is taken
        have hbase_false : eq.isBase = false := by
          cases h : eq.isBase <;> simp_all
        simp only [hbase_false] at heq_match
        rw [hrhs_subst] at heq_match
        simp only [hpos_subst] at heq_match
        -- Now heq_match has: Option.map ... (forwardEval def_ k (applySubst σ (.var rv))) = some out
        cases hfwd_inner : forwardEval def_ k (applySubst σ (.var rv)) with
        | none => simp [hfwd_inner, Option.map] at heq_match
        | some innerResult =>
          simp [hfwd_inner, Option.map] at heq_match
          -- heq_match : Atom.expression (...) = out
          -- Substitute out
          subst heq_match
          -- Goal: reverseEval def_ (k+1) (.expression (.symbol ctor :: preS ++ innerResult :: postS)) = some arg
          -- Unfold reverseEval
          simp only [reverseEval]
          -- Base sweep returns none (step ctor ≠ any base ctor)
          have hbase_none := reverseEval_base_sweep_none_of_step_ctor def_ hinv
            ctor (applySubst.applySubstList σ pre ++ innerResult ::
              applySubst.applySubstList σ post)
            outerArgs eq heq_mem hstep hrhs
          rw [hbase_none]
          simp only []
          -- Outer shell vars are LHS vars
          have houter_vars : ∀ v ∈ lhsArgVars (pre ++ post), v ∈ lhsArgVars eq.lhsArgs := by
            intro v hv
            apply hinv.varsCovered eq heq_mem v
            rw [hrhs]
            -- atomFreeVars (.expression (.symbol ctor :: outerArgs)) = atomFreeVarsList outerArgs
            simp only [atomFreeVars, atomFreeVars.atomFreeVarsList, List.nil_append]
            have hdecomp := findRecursiveCallPos_spec def_.funcName outerArgs pre [.var rv] post hpos
            rw [hdecomp]
            -- atomFreeVarsList (pre ++ [...] ++ post) contains vars from pre and post
            simp only [atomFreeVarsList_append, List.mem_append]
            rw [lhsArgVars_eq_atomFreeVarsList] at hv
            simp only [atomFreeVarsList_append, List.mem_append] at hv
            rcases hv with hv | hv
            · left; left; exact hv
            · right; exact hv
          -- recArg is ground
          have hrecarg_ground : isGroundAtom (applySubst σ (.var rv)) = true := by
            obtain ⟨b, hlookup, hb⟩ := hlhsvars rv hrv_lhs
            simp only [applySubst, Subst.lookup] at hlookup ⊢
            rw [hlookup]; exact hb
          -- innerResult is ground (by forwardEval_ground)
          have hinner_ground : isGroundAtom innerResult = true :=
            forwardEval_ground def_ hinv hsingle k _ _ hfwd_inner hrecarg_ground
          -- Apply IH: reverseEval def_ k innerResult = some (applySubst σ (.var rv))
          have hih := ih (applySubst σ (.var rv)) innerResult hfwd_inner hrecarg_ground
          -- Use reverseMatchStep_inverts_forward
          obtain ⟨σ_outer, hrms, hcompat, houter_apply⟩ := reverseMatchStep_inverts_forward
            eq def_.funcName lhsPat arg σ ctor outerArgs pre post (.var rv) innerResult
            hlhs hrhs hpos hm hground hinner_ground houter_vars
          -- stepRecArgs eq def_.funcName = some [.var rv]
          have hstepRecArgs : stepRecArgs eq def_.funcName = some [.var rv] := by
            simp only [stepRecArgs, hrhs, hpos]
          have hground_input : isGroundAtom (applySubst σ lhsPat) = true := by
            simpa [hinput] using hground
          have hground_outer :
              isGroundAtom.isGroundList (applySubst.applySubstList σ (pre ++ post)) = true := by
            exact applySubst_ground_of_bindings.applySubstList_ground_of_bindings σ (pre ++ post)
              (fun v hv => hlhsvars v (houter_vars v (lhsArgVars_eq_atomFreeVarsList _ ▸ hv)))
          have houter_ground' :
              isGroundAtom (.expression (applySubst.applySubstList σ_outer (pre ++ post))) = true := by
            simpa [isGroundAtom, houter_apply] using hground_outer
          have houter_ext_binds :
              ∀ w ∈ lhsArgVars (pre ++ post),
                ∃ b, Subst.lookup ((rv, applySubst σ (.var rv)) :: σ_outer) w = some b ∧
                  isGroundAtom b = true := by
            intro w hw
            have hw_expr : w ∈ atomFreeVars (.expression (pre ++ post)) := by
              simpa [atomFreeVars, lhsArgVars_eq_atomFreeVarsList] using hw
            obtain ⟨b, hlookup, hb⟩ :=
              applySubst_ground_var_bound σ_outer (.expression (pre ++ post)) houter_ground' w hw_expr
            by_cases hwr : w = rv
            ·
              refine ⟨applySubst σ (.var rv), ?_, hrecarg_ground⟩
              simp [Subst.lookup, hwr]
            · refine ⟨b, ?_, hb⟩
              unfold Subst.lookup at hlookup
              unfold Subst.lookup
              simp only [List.find?_cons]
              have hneq : (rv == w) = false :=
                beq_eq_false_iff_ne.mpr (by intro h; exact hwr h.symm)
              simpa [hneq] using hlookup
          have hlhs_ext_binds :
              ∀ w ∈ atomFreeVars lhsPat,
                ∃ b, Subst.lookup ((rv, applySubst σ (.var rv)) :: σ_outer) w = some b ∧
                  isGroundAtom b = true := by
            intro w hw
            have hrecov :=
              hinv.lhsVarsRecoverableStep eq heq_mem hstep lhsPat (by simp [hlhs]) w hw
            rw [hrhs] at hrecov
            rw [hpos] at hrecov
            rcases hrecov with hw_outer | hw_rec
            · exact houter_ext_binds w hw_outer
            · have hw_eq_or : w = rv ∨ False := by
                simpa [lhsArgVars, atomFreeVars] using hw_rec
              have hw_eq : w = rv := hw_eq_or.elim id False.elim
              refine ⟨applySubst σ (.var rv), ?_, hrecarg_ground⟩
              simp [Subst.lookup, hw_eq]
          -- Extended compatibility: ((rv, σ(rv)) :: σ_outer) agrees with σ
          have hcompat_ext : Subst.compatWith ((rv, applySubst σ (.var rv)) :: σ_outer) σ := by
            intro w a hlook
            by_cases hwr : w = rv
            ·
              have hrv_lookup : Subst.lookup σ rv = some (applySubst σ (.var rv)) := by
                obtain ⟨b, hlookup, _hb⟩ := hlhsvars rv hrv_lhs
                rw [applySubst, hlookup]
                simp
              have ha : a = applySubst σ (.var rv) := by
                have ha' : applySubst σ (.var rv) = a := by
                  simpa [Subst.lookup, hwr] using hlook
                exact ha'.symm
              rw [hwr, ha]
            · have hlook_outer : Subst.lookup σ_outer w = some a := by
                unfold Subst.lookup at hlook ⊢
                simp only [List.find?_cons] at hlook ⊢
                have hneq : (rv == w) = false :=
                  beq_eq_false_iff_ne.mpr (by intro h; exact hwr h.symm)
                simp [hneq] at hlook ⊢
                exact hlook
              exact hcompat w a hlook_outer
          -- applySubst with extended compat gives same result as σ
          have hground_ext : isGroundAtom (applySubst ((rv, applySubst σ (.var rv)) :: σ_outer) lhsPat) = true := by
            exact applySubst_ground_of_bindings ((rv, applySubst σ (.var rv)) :: σ_outer) lhsPat hlhs_ext_binds
          have happly_eq : applySubst ((rv, applySubst σ (.var rv)) :: σ_outer) lhsPat = arg := by
            rw [applySubst_compatWith_ground _ σ lhsPat hcompat_ext hground_ext, hinput]
          -- Define the step sweep function for clarity
          let stepFn := fun (eq' : HeadEquation) =>
            if eq'.isStep then
              match reverseMatchStep eq' def_.funcName
                  (.expression (.symbol ctor :: applySubst.applySubstList σ pre ++
                    [innerResult] ++ applySubst.applySubstList σ post)) with
              | some (σ', innerQuery) =>
                match eq'.lhsArgs with
                | [lhsPat'] =>
                  (reverseEval def_ k innerQuery).bind fun innerInput =>
                    match stepRecArgs eq' def_.funcName with
                    | some [.var recVar] =>
                      some (applySubst ((recVar, innerInput) :: σ') lhsPat')
                    | _ => none
                | _ => none
              | none => none
            else none
          -- Show the function applied to eq gives some arg
          have hfeq : stepFn eq = some arg := by
            unfold stepFn
            rw [if_pos hstep, hrms, hlhs, hstepRecArgs]
            simp [Option.bind]
            rw [hih]
            simp [happly_eq]
          -- Step sweep: use findSome?_unique
          apply List.findSome?_unique
          · exact ⟨eq, heq_mem, by simpa [stepFn] using hfeq⟩
          · -- Uniqueness: any eq' that returns some must return some arg
            intro eq' hmem'
            by_cases hstep' : eq'.isStep = true
            · -- eq' is a step equation
              simp only [hstep', ite_true]
              cases hrms' : reverseMatchStep eq' def_.funcName
                  (.expression (.symbol ctor :: applySubst.applySubstList σ pre ++
                    [innerResult] ++ applySubst.applySubstList σ post)) with
              | none =>
                left
                rw [show
                  reverseMatchStep eq' def_.funcName
                      (.expression
                        (Atom.symbol ctor ::
                          (applySubst.applySubstList σ pre ++ innerResult ::
                            applySubst.applySubstList σ post))) = none by
                    simpa [List.cons_append, List.append_assoc] using hrms']
              | some val =>
                -- eq' matched, so eq'.rhs has ctor = ctor
                obtain ⟨outerArgs', hrhs'⟩ :=
                  reverseMatchStep_implies_ctor eq' def_.funcName ctor _ val.1 val.2 hrms'
                -- By hdistinct, eq' = eq
                have heq_eq := hdistinct eq heq_mem eq' hmem' ctor outerArgs outerArgs' hrhs hrhs'
                subst heq_eq
                -- Now eq' = eq, so the function gives the same result
                right
                rw [show
                  reverseMatchStep eq def_.funcName
                      (.expression
                        (Atom.symbol ctor ::
                          (applySubst.applySubstList σ pre ++ innerResult ::
                            applySubst.applySubstList σ post))) = some (σ_outer, innerResult) by
                    simpa [List.cons_append, List.append_assoc] using hrms]
                simp [hlhs, Option.bind, hih, hstepRecArgs, happly_eq]
            · left
              simp [hstep']


/-! ## Step 4d: staged inverse soundness over instantiated runtime steps

The `compile*Step` functions above record only the *shape* of the inverse
program.  To connect them to the now-stable semantic inverse `reverseEval`,
we instantiate those shapes with the concrete query/result atoms that arise
at runtime and then prove a staged execution trace exists.

This keeps the theorem honest:
- `compile*Step` remains query-agnostic shape compilation
- `instantiate*Step` supplies the runtime atoms
- `StagedInverseTrace` records that the instantiated UNFOLD/BASE/FOLD steps
  reconstruct the original input exactly
-/

/-- The canonical wait token shared by the compiled unfold/fold skeletons. -/
def defaultWaitAtom (eq : HeadEquation) : Atom :=
  (compileUnfoldStep eq).waitAtom

/-- The unfold/fold skeletons share the same wait token. -/
theorem defaultWaitAtom_eq_fold_wait (eq : HeadEquation) :
    defaultWaitAtom eq = (compileFoldStep eq).waitAtom := rfl

/-- Instantiate a compiled base step with the concrete query/result atoms seen
    at runtime. -/
def instantiateBaseStep (eq : HeadEquation) (queryArg inputArg : Atom) : BaseStep :=
  { compileBaseStep eq with
      qid := queryArg
      result := inputArg }

/-- Instantiate a compiled unfold step with the concrete outer query and the
    single recursive sub-query recovered by reverse matching. -/
def instantiateUnfoldStep (eq : HeadEquation) (queryArg innerQuery : Atom) : UnfoldStep :=
  { compileUnfoldStep eq with
      qid := queryArg
      subQids := [innerQuery] }

/-- Instantiate a compiled fold step with the concrete original query, the
    recursive inverse result, and the fully reconstructed input. -/
def instantiateFoldStep (eq : HeadEquation) (queryArg innerInput inputArg : Atom) : FoldStep :=
  { compileFoldStep eq with
      qid := queryArg
      subResults := [innerInput]
      assembled := inputArg }

/-- Encode an instantiated base step as an actual exec fact. -/
def instantiateBaseExecFact (execAtom : Atom) (step : BaseStep) : ExecFact :=
  { atom := execAtom
    loc := .expression [.grounded (.int step.priority), .symbol "inv-base"]
    rule := mkExecRule step.priority "inv-base"
      (mkPattern [step.qid])
      (mkTemplate [.remove step.qid, .add step.result]) }

/-- Encode an instantiated unfold step as an actual exec fact. -/
def instantiateUnfoldExecFact (execAtom : Atom) (step : UnfoldStep) : ExecFact :=
  { atom := execAtom
    loc := .expression [.grounded (.int step.priority), .symbol "inv-unfold"]
    rule := mkExecRule step.priority "inv-unfold"
      (mkPattern [step.qid])
      (mkTemplate ([.remove step.qid] ++ step.subQids.map .add ++ [.add step.waitAtom])) }

/-- Encode an instantiated fold step as an actual exec fact. -/
def instantiateFoldExecFact (execAtom : Atom) (step : FoldStep) : ExecFact :=
  { atom := execAtom
    loc := .expression [.grounded (.int step.priority), .symbol "inv-fold"]
    rule := mkExecRule step.priority "inv-fold"
      (mkPattern (step.waitAtom :: step.subResults))
      (mkTemplate ([.remove step.waitAtom] ++ step.subResults.map .remove ++ [.add step.assembled])) }

/-- The encoded base exec fact is recognized by `toBaseStep?`. -/
theorem instantiateBaseExecFact_toBaseStep?
    (execAtom : Atom) (step : BaseStep) :
    (instantiateBaseExecFact execAtom step).toBaseStep? = some step := by
  cases step with
  | mk qid result priority inBase =>
      have hd1 : Nat.decLe 32 priority = isTrue inBase.1 := by
        cases h : Nat.decLe 32 priority with
        | isTrue h' => simp
        | isFalse h' => exact (False.elim (h' inBase.1))
      have hd2 : Nat.decLe priority 63 = isTrue inBase.2 := by
        cases h : Nat.decLe priority 63 with
        | isTrue h' => simp
        | isFalse h' => exact (False.elim (h' inBase.2))
      simp [instantiateBaseExecFact, ExecFact.toBaseStep?, mkExecRule, mkPattern, mkTemplate, hd1, hd2]

/-- The encoded unfold exec fact has exactly the unfold template shape needed by
    `unfold_step_exactness`. -/
theorem instantiateUnfoldExecFact_tmpl
    (execAtom : Atom) (step : UnfoldStep) :
    (instantiateUnfoldExecFact execAtom step).rule.tmpl.sinks =
      [.remove step.qid] ++ step.subQids.map .add ++ [.add step.waitAtom] := by
  simp [instantiateUnfoldExecFact, mkExecRule, mkPattern, mkTemplate]

/-- The encoded fold exec fact has exactly the fold template shape needed by
    `fold_step_exactness`. -/
theorem instantiateFoldExecFact_tmpl
    (execAtom : Atom) (step : FoldStep) :
    (instantiateFoldExecFact execAtom step).rule.tmpl.sinks =
      [.remove step.waitAtom] ++ step.subResults.map .remove ++ [.add step.assembled] := by
  simp [instantiateFoldExecFact, mkExecRule, mkPattern, mkTemplate]

/-- Removing the encoded base exec fact from its singleton runtime workspace
    leaves only the query atom. -/
theorem consumeExec_instantiateBaseExecFact_singleton
    (execAtom : Atom) (step : BaseStep)
    (hneq : execAtom ≠ step.qid) :
    consumeExec ({execAtom, step.qid} : Space) (instantiateBaseExecFact execAtom step) = {step.qid} := by
  ext a
  simp [consumeExec, instantiateBaseExecFact, hneq]

/-- Removing the encoded unfold exec fact from its singleton runtime workspace
    leaves only the outer query atom. -/
theorem consumeExec_instantiateUnfoldExecFact_singleton
    (execAtom : Atom) (step : UnfoldStep)
    (hneq : execAtom ≠ step.qid) :
    consumeExec ({execAtom, step.qid} : Space) (instantiateUnfoldExecFact execAtom step) = {step.qid} := by
  ext a
  simp [consumeExec, instantiateUnfoldExecFact, hneq]

/-- Removing the encoded fold exec fact from its singleton runtime workspace
    leaves the wait token and the single sub-result. -/
theorem consumeExec_instantiateFoldExecFact_singleton
    (eq : HeadEquation) (queryArg innerInput inputArg execAtom : Atom)
    (hneq_wait : execAtom ≠ defaultWaitAtom eq)
    (hneq_inner : execAtom ≠ innerInput) :
    consumeExec ({execAtom, defaultWaitAtom eq, innerInput} : Space)
      (instantiateFoldExecFact execAtom (instantiateFoldStep eq queryArg innerInput inputArg)) =
        {defaultWaitAtom eq, innerInput} := by
  ext a
  simp [consumeExec, instantiateFoldExecFact, instantiateFoldStep, hneq_wait, hneq_inner]

/-- Scheduler-level exactness for the singleton instantiated base step. -/
theorem instantiateBaseStep_fireExecFact_exact
    (eq : HeadEquation) (queryArg inputArg execAtom : Atom)
    (hneq : execAtom ≠ queryArg)
    (hg_result : isGroundAtom inputArg = true)
    (consumed : Finset Atom)
    (hunique :
      matchPattern [] ({execAtom, queryArg} : Space)
        (instantiateBaseExecFact execAtom (instantiateBaseStep eq queryArg inputArg)).rule.pat =
          [([], consumed)]) :
    fireExecFact ({execAtom, queryArg} : Space)
      (instantiateBaseExecFact execAtom (instantiateBaseStep eq queryArg inputArg)) = {inputArg} := by
  let step := instantiateBaseStep eq queryArg inputArg
  let ef := instantiateBaseExecFact execAtom step
  have hm : ef.atom ∈ ({execAtom, queryArg} : Space) := by
    change execAtom ∈ ({execAtom, queryArg} : Space)
    simp
  have hstep : ef.toBaseStep? = some step := by
    simpa [ef, step] using instantiateBaseExecFact_toBaseStep? execAtom step
  have hexact :=
    base_step_exactness ({execAtom, queryArg} : Space) ef step hm hstep hg_result consumed hunique
  have hcons :
      consumeExec ({execAtom, queryArg} : Space) ef = {queryArg} := by
    simpa [ef, step, instantiateBaseStep] using
      consumeExec_instantiateBaseExecFact_singleton execAtom step hneq
  rw [hcons] at hexact
  simpa [step, instantiateBaseStep, applyBase, compileBaseStep] using hexact

/-- Scheduler-level exactness for the singleton instantiated unfold step. -/
theorem instantiateUnfoldStep_fireExecFact_exact
    (eq : HeadEquation) (queryArg innerQuery execAtom : Atom)
    (hneq : execAtom ≠ queryArg)
    (hg_inner : isGroundAtom innerQuery = true)
    (hg_wait : isGroundAtom (defaultWaitAtom eq) = true)
    (consumed : Finset Atom)
    (hunique :
      matchPattern [] ({execAtom, queryArg} : Space)
        (instantiateUnfoldExecFact execAtom (instantiateUnfoldStep eq queryArg innerQuery)).rule.pat =
          [([], consumed)]) :
    fireExecFact ({execAtom, queryArg} : Space)
      (instantiateUnfoldExecFact execAtom (instantiateUnfoldStep eq queryArg innerQuery)) =
        ({innerQuery} ∪ {defaultWaitAtom eq}) := by
  let step := instantiateUnfoldStep eq queryArg innerQuery
  let ef := instantiateUnfoldExecFact execAtom step
  have hm : ef.atom ∈ ({execAtom, queryArg} : Space) := by
    change execAtom ∈ ({execAtom, queryArg} : Space)
    simp
  have htmpl :
      ef.rule.tmpl.sinks =
        [.remove step.qid] ++ step.subQids.map .add ++ [.add step.waitAtom] := by
    simpa [ef, step] using instantiateUnfoldExecFact_tmpl execAtom step
  have hg_subs : ∀ a ∈ step.subQids, isGroundAtom a = true := by
    intro a ha
    simp [step, instantiateUnfoldStep] at ha
    rcases ha with rfl
    exact hg_inner
  have hexact :=
    unfold_step_exactness ({execAtom, queryArg} : Space) ef step hm htmpl hg_subs hg_wait consumed hunique
  have hcons :
      consumeExec ({execAtom, queryArg} : Space) ef = {queryArg} := by
    simpa [ef, step, instantiateUnfoldStep] using
      consumeExec_instantiateUnfoldExecFact_singleton execAtom step hneq
  rw [hcons] at hexact
  simpa [step, instantiateUnfoldStep, defaultWaitAtom, applyUnfold, compileUnfoldStep] using hexact

/-- Scheduler-level exactness for the singleton instantiated fold step. -/
theorem instantiateFoldStep_fireExecFact_exact
    (eq : HeadEquation) (queryArg innerInput inputArg execAtom : Atom)
    (hneq_wait : execAtom ≠ defaultWaitAtom eq)
    (hneq_inner : execAtom ≠ innerInput)
    (hg_assembled : isGroundAtom inputArg = true)
    (consumed : Finset Atom)
    (hunique :
      matchPattern [] ({execAtom, defaultWaitAtom eq, innerInput} : Space)
        (instantiateFoldExecFact execAtom (instantiateFoldStep eq queryArg innerInput inputArg)).rule.pat =
          [([], consumed)]) :
    fireExecFact ({execAtom, defaultWaitAtom eq, innerInput} : Space)
      (instantiateFoldExecFact execAtom (instantiateFoldStep eq queryArg innerInput inputArg)) =
        {inputArg} := by
  let step := instantiateFoldStep eq queryArg innerInput inputArg
  let ef := instantiateFoldExecFact execAtom step
  have hm : ef.atom ∈ ({execAtom, defaultWaitAtom eq, innerInput} : Space) := by
    change execAtom ∈ ({execAtom, defaultWaitAtom eq, innerInput} : Space)
    simp
  have htmpl :
      ef.rule.tmpl.sinks =
        [.remove step.waitAtom] ++ step.subResults.map .remove ++ [.add step.assembled] := by
    simpa [ef, step] using instantiateFoldExecFact_tmpl execAtom step
  have hbin : step.subResults.length = 1 := by
    simp [step, instantiateFoldStep]
  have hexact :=
    fold_step_exactness ({execAtom, defaultWaitAtom eq, innerInput} : Space) ef step hm htmpl hg_assembled consumed hunique
  have hcons :
      consumeExec ({execAtom, defaultWaitAtom eq, innerInput} : Space) ef =
        {defaultWaitAtom eq, innerInput} := by
    simpa [ef, step, instantiateFoldStep] using
      consumeExec_instantiateFoldExecFact_singleton eq queryArg innerInput inputArg execAtom hneq_wait hneq_inner
  rw [hcons] at hexact
  have happly :
      applyFold ({defaultWaitAtom eq, innerInput} : Space) step = ({inputArg} : Space) := by
    ext x
    simp [step, instantiateFoldStep, defaultWaitAtom, applyFold, compileFoldStep, compileUnfoldStep]
  exact hexact.trans happly

/-- Running an instantiated base step on a singleton query space produces the
    singleton recovered input space. -/
theorem instantiateBaseStep_apply_singleton
    (eq : HeadEquation) (queryArg inputArg : Atom) :
    applyBase {queryArg} (instantiateBaseStep eq queryArg inputArg) = {inputArg} := by
  simp [instantiateBaseStep, applyBase]

/-- Running an instantiated unfold step on a singleton query space removes the
    outer query and spawns the single recursive sub-query plus the wait token. -/
theorem instantiateUnfoldStep_apply_singleton
    (eq : HeadEquation) (queryArg innerQuery : Atom) :
    applyUnfold {queryArg} (instantiateUnfoldStep eq queryArg innerQuery) =
      ({innerQuery} ∪ {defaultWaitAtom eq}) := by
  simp [instantiateUnfoldStep, defaultWaitAtom, applyUnfold, compileUnfoldStep]

/-- Running an instantiated fold step after the recursive sub-result is
    available removes the wait/sub-result pair and produces the recovered input. -/
theorem instantiateFoldStep_apply_singleton
    (eq : HeadEquation) (queryArg innerInput inputArg : Atom) :
    applyFold ({defaultWaitAtom eq} ∪ {innerInput})
        (instantiateFoldStep eq queryArg innerInput inputArg) = {inputArg} := by
  rw [defaultWaitAtom_eq_fold_wait]
  ext a
  simp [instantiateFoldStep, applyFold, compileFoldStep]

/-- A staged inverse execution trace for one query/result pair.

This is the first local runtime-facing theorem layer above `reverseEval`:
it records that the compiled inverse skeletons can be instantiated with runtime
atoms so that BASE or UNFOLD+FOLD reconstruct the original input. -/
inductive StagedInverseTrace (def_ : HeadFuncDef) : Nat → Atom → Atom → Prop where
  | base (fuel : Nat) (eq : HeadEquation) (queryArg inputArg : Atom)
      (hmatch : reverseMatchBase eq queryArg = some inputArg)
      (hexec :
        applyBase {queryArg} (instantiateBaseStep eq queryArg inputArg) = {inputArg}) :
      StagedInverseTrace def_ (fuel + 1) queryArg inputArg
  | step (fuel : Nat) (eq : HeadEquation) (queryArg innerQuery innerInput inputArg : Atom)
      (hmatch : ∃ σ_outer, reverseMatchStep eq def_.funcName queryArg = some (σ_outer, innerQuery))
      (hunfold :
        applyUnfold {queryArg} (instantiateUnfoldStep eq queryArg innerQuery) =
          ({innerQuery} ∪ {defaultWaitAtom eq}))
      (hinner : StagedInverseTrace def_ fuel innerQuery innerInput)
      (hfold :
        applyFold ({defaultWaitAtom eq} ∪ {innerInput})
          (instantiateFoldStep eq queryArg innerInput inputArg) = {inputArg}) :
      StagedInverseTrace def_ (fuel + 1) queryArg inputArg

/-! ## Concrete exec witnesses for staged inverse traces

`StagedInverseTrace` records the abstract instantiated UNFOLD/BASE/FOLD story
using `applyBase` / `applyUnfold` / `applyFold`.  The following witness
structures package the remaining scheduler-side obligations needed to upgrade
that abstract trace to actual `fireExecFact` transitions:

- a chosen exec atom in the singleton workspace
- the unique singleton match result
- the groundness side-conditions required by the exactness theorems

We keep these obligations explicit rather than hiding them in automation, so
the current theorem layer stays honest about what is already proven and what is
still a separate freshness/uniqueness problem. -/

/-- Witness package for realizing one abstract base step as an actual fired exec
    fact on a singleton workspace. -/
structure BaseExecWitness (eq : HeadEquation) (queryArg inputArg : Atom) where
  execAtom : Atom
  consumed : Finset Atom
  execNeQuery : execAtom ≠ queryArg
  inputGround : isGroundAtom inputArg = true
  uniqueMatch :
    matchPattern [] ({execAtom, queryArg} : Space)
      (instantiateBaseExecFact execAtom (instantiateBaseStep eq queryArg inputArg)).rule.pat =
        [([], consumed)]

/-- Witness package for realizing one abstract unfold step as an actual fired
    exec fact on a singleton workspace. -/
structure UnfoldExecWitness (eq : HeadEquation) (queryArg innerQuery : Atom) where
  execAtom : Atom
  consumed : Finset Atom
  execNeQuery : execAtom ≠ queryArg
  innerGround : isGroundAtom innerQuery = true
  waitGround : isGroundAtom (defaultWaitAtom eq) = true
  uniqueMatch :
    matchPattern [] ({execAtom, queryArg} : Space)
      (instantiateUnfoldExecFact execAtom (instantiateUnfoldStep eq queryArg innerQuery)).rule.pat =
        [([], consumed)]

/-- Witness package for realizing one abstract fold step as an actual fired
    exec fact on the singleton wait/sub-result workspace. -/
structure FoldExecWitness (eq : HeadEquation) (queryArg innerInput inputArg : Atom) where
  execAtom : Atom
  consumed : Finset Atom
  execNeWait : execAtom ≠ defaultWaitAtom eq
  execNeInner : execAtom ≠ innerInput
  inputGround : isGroundAtom inputArg = true
  uniqueMatch :
    matchPattern [] ({execAtom, defaultWaitAtom eq, innerInput} : Space)
      (instantiateFoldExecFact execAtom (instantiateFoldStep eq queryArg innerInput inputArg)).rule.pat =
        [([], consumed)]

/-- Any base witness yields the exact singleton scheduler transition. -/
theorem BaseExecWitness.fire_exact
    (eq : HeadEquation) (queryArg inputArg : Atom) (w : BaseExecWitness eq queryArg inputArg) :
    fireExecFact ({w.execAtom, queryArg} : Space)
      (instantiateBaseExecFact w.execAtom (instantiateBaseStep eq queryArg inputArg)) =
        ({inputArg} : Space) :=
  instantiateBaseStep_fireExecFact_exact eq queryArg inputArg w.execAtom
    w.execNeQuery w.inputGround w.consumed w.uniqueMatch

/-- Any unfold witness yields the exact singleton scheduler transition. -/
theorem UnfoldExecWitness.fire_exact
    (eq : HeadEquation) (queryArg innerQuery : Atom) (w : UnfoldExecWitness eq queryArg innerQuery) :
    fireExecFact ({w.execAtom, queryArg} : Space)
      (instantiateUnfoldExecFact w.execAtom (instantiateUnfoldStep eq queryArg innerQuery)) =
        (({innerQuery} : Space) ∪ {defaultWaitAtom eq}) :=
  instantiateUnfoldStep_fireExecFact_exact eq queryArg innerQuery w.execAtom
    w.execNeQuery w.innerGround w.waitGround w.consumed w.uniqueMatch

/-- Any fold witness yields the exact singleton scheduler transition. -/
theorem FoldExecWitness.fire_exact
    (eq : HeadEquation) (queryArg innerInput inputArg : Atom) (w : FoldExecWitness eq queryArg innerInput inputArg) :
    fireExecFact ({w.execAtom, defaultWaitAtom eq, innerInput} : Space)
      (instantiateFoldExecFact w.execAtom (instantiateFoldStep eq queryArg innerInput inputArg)) =
        ({inputArg} : Space) :=
  instantiateFoldStep_fireExecFact_exact eq queryArg innerInput inputArg w.execAtom
    w.execNeWait w.execNeInner w.inputGround w.consumed w.uniqueMatch

/-- Concrete scheduler-facing refinement of `StagedInverseTrace`.

This is the first backend-facing trace relation for the deterministic
invertible fragment.  It still carries explicit singleton-match witnesses, but
it upgrades the abstract `applyBase`/`applyUnfold`/`applyFold` story to actual
`fireExecFact` transitions on the singleton workspaces used by the staged
inverse compilation. -/
inductive StagedInverseExecTrace (def_ : HeadFuncDef) : Nat → Atom → Atom → Prop where
  | base (fuel : Nat) (eq : HeadEquation) (queryArg inputArg : Atom)
      (hmatch : reverseMatchBase eq queryArg = some inputArg)
      (w : BaseExecWitness eq queryArg inputArg)
      (hexec :
        fireExecFact ({w.execAtom, queryArg} : Space)
          (instantiateBaseExecFact w.execAtom (instantiateBaseStep eq queryArg inputArg)) =
            {inputArg}) :
      StagedInverseExecTrace def_ (fuel + 1) queryArg inputArg
  | step (fuel : Nat) (eq : HeadEquation) (queryArg innerQuery innerInput inputArg : Atom)
      (hmatch : ∃ σ_outer, reverseMatchStep eq def_.funcName queryArg = some (σ_outer, innerQuery))
      (wu : UnfoldExecWitness eq queryArg innerQuery)
      (hunfoldExec :
        fireExecFact ({wu.execAtom, queryArg} : Space)
          (instantiateUnfoldExecFact wu.execAtom (instantiateUnfoldStep eq queryArg innerQuery)) =
            ({innerQuery} ∪ {defaultWaitAtom eq}))
      (hinner : StagedInverseExecTrace def_ fuel innerQuery innerInput)
      (wf : FoldExecWitness eq queryArg innerInput inputArg)
      (hfoldExec :
        fireExecFact ({wf.execAtom, defaultWaitAtom eq, innerInput} : Space)
          (instantiateFoldExecFact wf.execAtom (instantiateFoldStep eq queryArg innerInput inputArg)) =
            {inputArg}) :
      StagedInverseExecTrace def_ (fuel + 1) queryArg inputArg

/-- Any abstract staged inverse trace can be upgraded to a concrete
    scheduler-facing exec trace, provided explicit singleton exec witnesses are
    supplied for each base/unfold/fold node. -/
theorem stagedTrace_refines_exec
    (def_ : HeadFuncDef)
    (baseW :
      ∀ (_fuel : Nat) (eq : HeadEquation) (queryArg inputArg : Atom),
        reverseMatchBase eq queryArg = some inputArg →
        BaseExecWitness eq queryArg inputArg)
    (unfoldW :
      ∀ (fuel : Nat) (eq : HeadEquation) (queryArg innerQuery innerInput _inputArg : Atom),
        (∃ σ_outer, reverseMatchStep eq def_.funcName queryArg = some (σ_outer, innerQuery)) →
        StagedInverseTrace def_ fuel innerQuery innerInput →
        UnfoldExecWitness eq queryArg innerQuery)
    (foldW :
      ∀ (fuel : Nat) (eq : HeadEquation) (queryArg innerQuery innerInput inputArg : Atom),
        (∃ σ_outer, reverseMatchStep eq def_.funcName queryArg = some (σ_outer, innerQuery)) →
        StagedInverseTrace def_ fuel innerQuery innerInput →
        FoldExecWitness eq queryArg innerInput inputArg) :
    ∀ fuel queryArg inputArg,
      StagedInverseTrace def_ fuel queryArg inputArg →
      StagedInverseExecTrace def_ fuel queryArg inputArg
:= by
  intro fuel queryArg inputArg htrace
  induction htrace with
  | base fuel eq queryArg inputArg hmatch _ =>
      let w := baseW fuel eq queryArg inputArg hmatch
      exact StagedInverseExecTrace.base fuel eq queryArg inputArg hmatch w
        (BaseExecWitness.fire_exact eq queryArg inputArg w)
  | step fuel eq queryArg innerQuery innerInput inputArg hmatch _ hinner _ ih =>
      let wu := unfoldW fuel eq queryArg innerQuery innerInput inputArg hmatch hinner
      let wf := foldW fuel eq queryArg innerQuery innerInput inputArg hmatch hinner
      exact StagedInverseExecTrace.step fuel eq queryArg innerQuery innerInput inputArg hmatch wu
        (UnfoldExecWitness.fire_exact eq queryArg innerQuery wu)
        ih
        wf
        (FoldExecWitness.fire_exact eq queryArg innerInput inputArg wf)

/-- If the semantic inverse succeeds, there exists a staged UNFOLD/BASE/FOLD
    trace built from the compiled inverse skeletons. -/
theorem reverseEval_implies_stagedTrace (def_ : HeadFuncDef) :
    ∀ fuel queryArg inputArg,
      reverseEval def_ fuel queryArg = some inputArg →
      StagedInverseTrace def_ fuel queryArg inputArg
  | 0, _, _, h => by
      simp [reverseEval] at h
  | fuel + 1, queryArg, inputArg, hrev => by
      simp only [reverseEval] at hrev
      cases hbase : def_.equations.findSome? (fun eq =>
        if eq.isBase then reverseMatchBase eq queryArg else none) with
      | some baseArg =>
          simp [hbase] at hrev
          subst baseArg
          obtain ⟨eq, heq_mem, heq_match⟩ :=
            List.exists_of_findSome?_eq_some hbase
          have hbase_true : eq.isBase = true := by
            by_cases hb : eq.isBase = true
            · exact hb
            · simp [hb] at heq_match
          simp [hbase_true] at heq_match
          exact StagedInverseTrace.base fuel eq queryArg inputArg heq_match
            (instantiateBaseStep_apply_singleton eq queryArg inputArg)
      | none =>
          simp [hbase] at hrev
          obtain ⟨eq, heq_mem, heq_match⟩ :=
            List.exists_of_findSome?_eq_some hrev
          have hstep_true : eq.isStep = true := by
            by_cases hs : eq.isStep = true
            · exact hs
            · simp [hs] at heq_match
          simp [hstep_true] at heq_match
          cases hrms : reverseMatchStep eq def_.funcName queryArg with
          | none =>
              simp [hrms] at heq_match
          | some pair =>
              cases pair with
              | mk σ_outer innerQuery =>
                  simp [hrms] at heq_match
                  cases hlhs : eq.lhsArgs with
                  | nil =>
                      simp [hlhs] at heq_match
                  | cons lhsPat rest =>
                      cases rest with
                      | nil =>
                          simp [hlhs] at heq_match
                          cases hinner : reverseEval def_ fuel innerQuery with
                          | none =>
                              simp [hinner, Option.bind] at heq_match
                          | some innerInput =>
                              simp [hinner, Option.bind] at heq_match
                              cases hrec : stepRecArgs eq def_.funcName with
                              | none =>
                                  simp [hrec] at heq_match
                              | some recArgs =>
                                  cases recArgs with
                                  | nil =>
                                      simp [hrec] at heq_match
                                  | cons recArg rest' =>
                                      cases recArg with
                                      | symbol _ =>
                                          simp [hrec] at heq_match
                                      | grounded _ =>
                                          simp [hrec] at heq_match
                                      | expression _ =>
                                          simp [hrec] at heq_match
                                      | var recVar =>
                                          cases rest' with
                                          | nil =>
                                              simp [hrec] at heq_match
                                              have hinnerTrace :=
                                                reverseEval_implies_stagedTrace def_ fuel innerQuery innerInput hinner
                                              exact StagedInverseTrace.step fuel eq queryArg innerQuery innerInput inputArg
                                                ⟨σ_outer, hrms⟩
                                                (instantiateUnfoldStep_apply_singleton eq queryArg innerQuery)
                                                hinnerTrace
                                                (instantiateFoldStep_apply_singleton eq queryArg innerInput inputArg)
                                          | cons _ _ =>
                                              simp [hrec] at heq_match
                      | cons _ _ =>
                          simp [hlhs] at heq_match

/-- The staged inverse compilation is sound with respect to the semantic
    roundtrip layer: every successful forward evaluation gives rise to a staged
    UNFOLD/BASE/FOLD inverse trace recovering the original input. -/
theorem staged_inverse_sound
    (def_ : HeadFuncDef) (hinv : InvertibleHead def_)
    (hsingle : ∀ eq ∈ def_.equations, ∃ lhsPat, eq.lhsArgs = [lhsPat])
    (hdistinct : ∀ eq1 ∈ def_.equations, ∀ eq2 ∈ def_.equations,
      ∀ (ctor : String) (args1 args2 : List Atom),
      eq1.rhs = .expression (.symbol ctor :: args1) →
      eq2.rhs = .expression (.symbol ctor :: args2) →
      eq1 = eq2)
    (hsingleRec : ∀ eq ∈ def_.equations, eq.isStep = true →
      ∀ (ctor : String) (outerArgs pre recArgs post : List Atom),
      eq.rhs = .expression (.symbol ctor :: outerArgs) →
      findRecursiveCallPos def_.funcName outerArgs = some (pre, recArgs, post) →
      ∃ rv, recArgs = [.var rv])
    (hallBaseOrStep : ∀ eq ∈ def_.equations, eq.isBase = true ∨ eq.isStep = true)
    (fuel : Nat) (arg out : Atom)
    (hfwd : forwardEval def_ fuel arg = some out)
    (hground : isGroundAtom arg = true) :
    StagedInverseTrace def_ fuel out arg := by
  exact reverseEval_implies_stagedTrace def_ fuel out arg
    (reverseEval_inverts_forwardEval def_ hinv hsingle hdistinct hsingleRec
      hallBaseOrStep fuel arg out hfwd hground)

/-- Backend-facing soundness corollary for the deterministic invertible
    fragment: a successful forward evaluation can be refined all the way to a
    concrete scheduler-facing staged inverse exec trace, provided explicit
    singleton witnesses are supplied for each base/unfold/fold node. -/
theorem staged_inverse_exec_sound
    (def_ : HeadFuncDef) (hinv : InvertibleHead def_)
    (hsingle : ∀ eq ∈ def_.equations, ∃ lhsPat, eq.lhsArgs = [lhsPat])
    (hdistinct : ∀ eq1 ∈ def_.equations, ∀ eq2 ∈ def_.equations,
      ∀ (ctor : String) (args1 args2 : List Atom),
      eq1.rhs = .expression (.symbol ctor :: args1) →
      eq2.rhs = .expression (.symbol ctor :: args2) →
      eq1 = eq2)
    (hsingleRec : ∀ eq ∈ def_.equations, eq.isStep = true →
      ∀ (ctor : String) (outerArgs pre recArgs post : List Atom),
      eq.rhs = .expression (.symbol ctor :: outerArgs) →
      findRecursiveCallPos def_.funcName outerArgs = some (pre, recArgs, post) →
      ∃ rv, recArgs = [.var rv])
    (hallBaseOrStep : ∀ eq ∈ def_.equations, eq.isBase = true ∨ eq.isStep = true)
    (baseW :
      ∀ (_fuel : Nat) (eq : HeadEquation) (queryArg inputArg : Atom),
        reverseMatchBase eq queryArg = some inputArg →
        BaseExecWitness eq queryArg inputArg)
    (unfoldW :
      ∀ (fuel : Nat) (eq : HeadEquation) (queryArg innerQuery innerInput _inputArg : Atom),
        (∃ σ_outer, reverseMatchStep eq def_.funcName queryArg = some (σ_outer, innerQuery)) →
        StagedInverseTrace def_ fuel innerQuery innerInput →
        UnfoldExecWitness eq queryArg innerQuery)
    (foldW :
      ∀ (fuel : Nat) (eq : HeadEquation) (queryArg innerQuery innerInput inputArg : Atom),
        (∃ σ_outer, reverseMatchStep eq def_.funcName queryArg = some (σ_outer, innerQuery)) →
        StagedInverseTrace def_ fuel innerQuery innerInput →
        FoldExecWitness eq queryArg innerInput inputArg)
    (fuel : Nat) (arg out : Atom)
    (hfwd : forwardEval def_ fuel arg = some out)
    (hground : isGroundAtom arg = true) :
    StagedInverseExecTrace def_ fuel out arg := by
  exact stagedTrace_refines_exec def_ baseW unfoldW foldW fuel out arg
    (staged_inverse_sound def_ hinv hsingle hdistinct hsingleRec hallBaseOrStep
      fuel arg out hfwd hground)

/-- Bundled corollary form of `reverseEval_inverts_forwardEval` using an explicit
deterministic invertible fragment witness. -/
theorem reverseEval_inverts_forwardEval_of_fragment
    (def_ : HeadFuncDef) (hfrag : DeterministicInvertibleFragment def_)
    (fuel : Nat) (arg out : Atom)
    (hfwd : forwardEval def_ fuel arg = some out)
    (hground : isGroundAtom arg = true) :
    reverseEval def_ fuel out = some arg := by
  exact reverseEval_inverts_forwardEval def_ hfrag.hinv hfrag.singleLhsArg
    hfrag.distinctOuterCtors hfrag.singleRecArg hfrag.allBaseOrStep
    fuel arg out hfwd hground

/-- Bundled corollary form of `staged_inverse_sound` using an explicit
deterministic invertible fragment witness. -/
theorem staged_inverse_sound_of_fragment
    (def_ : HeadFuncDef) (hfrag : DeterministicInvertibleFragment def_)
    (fuel : Nat) (arg out : Atom)
    (hfwd : forwardEval def_ fuel arg = some out)
    (hground : isGroundAtom arg = true) :
    StagedInverseTrace def_ fuel out arg := by
  exact staged_inverse_sound def_ hfrag.hinv hfrag.singleLhsArg
    hfrag.distinctOuterCtors hfrag.singleRecArg hfrag.allBaseOrStep
    fuel arg out hfwd hground

/-- Bundled corollary form of `staged_inverse_exec_sound` using an explicit
deterministic invertible fragment witness. This is the clean backend-facing
entry point for the current singleton invertible fragment. -/
theorem staged_inverse_exec_sound_of_fragment
    (def_ : HeadFuncDef) (hfrag : DeterministicInvertibleFragment def_)
    (baseW :
      ∀ (_fuel : Nat) (eq : HeadEquation) (queryArg inputArg : Atom),
        reverseMatchBase eq queryArg = some inputArg →
        BaseExecWitness eq queryArg inputArg)
    (unfoldW :
      ∀ (fuel : Nat) (eq : HeadEquation) (queryArg innerQuery innerInput _inputArg : Atom),
        (∃ σ_outer, reverseMatchStep eq def_.funcName queryArg = some (σ_outer, innerQuery)) →
        StagedInverseTrace def_ fuel innerQuery innerInput →
        UnfoldExecWitness eq queryArg innerQuery)
    (foldW :
      ∀ (fuel : Nat) (eq : HeadEquation) (queryArg innerQuery innerInput inputArg : Atom),
        (∃ σ_outer, reverseMatchStep eq def_.funcName queryArg = some (σ_outer, innerQuery)) →
        StagedInverseTrace def_ fuel innerQuery innerInput →
        FoldExecWitness eq queryArg innerInput inputArg)
    (fuel : Nat) (arg out : Atom)
    (hfwd : forwardEval def_ fuel arg = some out)
    (hground : isGroundAtom arg = true) :
    StagedInverseExecTrace def_ fuel out arg := by
  exact staged_inverse_exec_sound def_ hfrag.hinv hfrag.singleLhsArg
    hfrag.distinctOuterCtors hfrag.singleRecArg hfrag.allBaseOrStep
    baseW unfoldW foldW fuel arg out hfwd hground


/-! ## Canary checks -/

section Canaries

#check @atomContainsSymbol
#check @atomHeadCallCount
#check @findRecursiveCallPos
#check @HeadEquation.isBase
#check @HeadEquation.isStep
#check @InvertibleHead
#check @StagedInverseCompilation
#check @forwardEval
#check @reverseMatchBase
#check @Subst.lookupExtends
#check @matchAtom_lookupExtends
#check @applySubst_ground_ext
#check @matchAtom_applySubst_ground
#check @reverseMatchBase_rhs_roundtrip
#check @base_forward_reverse_roundtrip
#check @compileInverse
#check @reverseEval
#check @reverseMatchStep
#check @findRecursiveCallPos_spec
#check @listGetAt_mem
#check @Subst.compatWith
#check @matchAtomRel_self_compat
#check @matchAtom_self_ground
#check @applySubst_compatWith_ground
#check @applySubst_ground_var_bound
#check @applySubst_ground_of_bindings
#check @reverseMatchBase_inverts_forward
#check @lhsArgVars_eq_atomFreeVarsList
#check @reverseMatchStep_inverts_forward
#check @defaultWaitAtom
#check @instantiateBaseStep
#check @instantiateUnfoldStep
#check @instantiateFoldStep
#check @StagedInverseTrace
#check @reverseEval_implies_stagedTrace
#check @staged_inverse_sound
#check @staged_inverse_exec_sound

end Canaries

end Mettapedia.Languages.ProcessCalculi.MORK
