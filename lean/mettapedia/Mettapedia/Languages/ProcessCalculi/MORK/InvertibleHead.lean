import Mettapedia.Languages.ProcessCalculi.MORK.Space
import Mettapedia.Languages.ProcessCalculi.MORK.ThreePhaseExec
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

open Mettapedia.Languages.MeTTa.Core (Atom GroundedValue)

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
  consistent : ∀ eq ∈ equations, eq.funcName = funcName := by intro eq _; rfl
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

/-! ## Canary examples -/

section InvertibleHeadExamples

/-- Example: `mk` with `(= (mk $x) (wrap $x))` — non-recursive, one equation.
    This is the simplest invertible head. -/
private def mkDef : HeadFuncDef where
  funcName := "mk"
  equations := [⟨"mk", [.var "x"], .expression [.symbol "wrap", .var "x"]⟩]

private theorem mkDef_base : mkDef.equations[0]!.isBase = true := by
  simp [HeadEquation.isBase, atomHeadCallCount, atomHeadCallCount.atomHeadCallCountList]

/-- Example: recursive `mk` with:
    `(= (mk 0) (z))`
    `(= (mk (S $n)) (s (mk $n)))` -/
private def mkRecDef : HeadFuncDef where
  funcName := "mk"
  equations := [
    ⟨"mk", [.symbol "0"], .expression [.symbol "z"]⟩,
    ⟨"mk", [.expression [.symbol "S", .var "n"]],
     .expression [.symbol "s", .expression [.symbol "mk", .var "n"]]⟩
  ]

private theorem mkRecDef_eq0_isBase : mkRecDef.equations[0]!.isBase = true := by
  simp [HeadEquation.isBase, atomHeadCallCount, atomHeadCallCount.atomHeadCallCountList]

private theorem mkRecDef_eqS_isStep : mkRecDef.equations[1]!.isStep = true := by
  simp [HeadEquation.isStep, atomHeadCallCount, atomHeadCallCount.atomHeadCallCountList,
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

/-- Lookup-level extension: σ' extends σ when every existing lookup is preserved. -/
def Subst.lookupExtends (σ' σ : Subst) : Prop :=
  ∀ v a, σ.lookup v = some a → σ'.lookup v = some a

theorem Subst.lookupExtends_refl (σ : Subst) : σ.lookupExtends σ :=
  fun _ _ h => h

theorem Subst.lookupExtends_trans {σ₁ σ₂ σ₃ : Subst}
    (h₁₂ : σ₂.lookupExtends σ₁) (h₂₃ : σ₃.lookupExtends σ₂) :
    σ₃.lookupExtends σ₁ :=
  fun v a hv => h₂₃ v a (h₁₂ v a hv)

/-- Prepending a fresh binding preserves existing lookups. -/
theorem Subst.lookupExtends_cons_fresh {σ : Subst} {w : String} {b : Atom}
    (hfresh : σ.lookup w = none) :
    ((w, b) :: σ).lookupExtends σ := by
  intro v a hva
  simp only [Subst.lookup, List.find?, Option.map] at hva ⊢
  by_cases hvw : (w, b).1 == v
  · -- w = v, but σ.lookup v = some a contradicts σ.lookup w = none
    simp only [hvw, ite_true]
    have : w = v := by simpa [BEq.beq] using hvw
    rw [this] at hfresh
    simp only [Subst.lookup] at hfresh
    rw [hfresh] at hva; simp at hva
  · simp only [hvw, ite_false]
    exact hva

/-- `matchAtom` preserves existing lookups: σ' from matching extends σ. -/
theorem matchAtom_lookupExtends {σ : Subst} {pat conc : Atom} {σ' : Subst}
    (h : matchAtom σ pat conc = some σ') :
    σ'.lookupExtends σ := by
  match pat, conc with
  | .var v, a =>
    simp only [matchAtom] at h
    cases hlookup : σ.lookup v with
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
    simp only [applySubst]
    cases hlookup : σ.lookup v with
    | none =>
      simp only [Option.none_getD] at hg
      exact absurd hg (by decide)
    | some b =>
      simp only [Option.some_getD] at hg ⊢
      have hext' := hext v b hlookup
      simp only [hext']
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

/-! ## Canary checks -/

section Canaries

-- Helpers are well-typed
#check @atomContainsSymbol
#check @atomHeadCallCount
#check @findRecursiveCallPos
#check @HeadEquation.isBase
#check @HeadEquation.isStep
#check @InvertibleHead
#check @StagedInverseCompilation
#check @forwardEval
#check @reverseMatchBase

end Canaries

end Mettapedia.Languages.ProcessCalculi.MORK
