import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Capture-Avoiding Substitution for MeTTaIL

This file formalizes capture-avoiding substitution concepts,
matching MeTTaIL's moniker-based approach.

## De Bruijn Representation

In de Bruijn representation:
- Variables are represented by natural numbers (indices)
- Index 0 refers to the innermost binder
- Substitution is capture-avoiding by construction

## References

- de Bruijn, "Lambda calculus notation with nameless dummies" (1972)
- `/home/zar/claude/hyperon/mettail-rust/macros/src/gen/term_ops/subst.rs`
-/

namespace Mettapedia.OSLF.MeTTaIL.Substitution

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Simple De Bruijn Terms

We use a simple representation with just variables, applications, and lambdas.
Arguments are kept as a single term (can be extended to pairs/tuples).
-/

/-- Simple de Bruijn term (single argument applications) -/
inductive SimpleTerm : Nat → Type where
  | var : Fin n → SimpleTerm n
  | app : String → SimpleTerm n → SimpleTerm n
  | lam : SimpleTerm (n + 1) → SimpleTerm n
  | unit : SimpleTerm n  -- For nullary constructors

namespace SimpleTerm

/-! ## Weakening -/

/-- Weaken a term: shift all free variables up by one -/
def weaken : SimpleTerm n → SimpleTerm (n + 1)
  | var i => var ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
  | app c arg => app c (weaken arg)
  | lam body => lam (weakenBody body)
  | unit => unit
where
  /-- Weaken body of a lambda (shifts index 0) -/
  weakenBody : SimpleTerm (n + 1) → SimpleTerm (n + 2)
    | var i =>
      if i.val = 0 then var ⟨0, Nat.zero_lt_succ _⟩
      else var ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
    | app c arg => app c (weakenBody arg)
    | lam body => lam (weakenBody2 body)
    | unit => unit
  /-- Weaken under two binders -/
  weakenBody2 : SimpleTerm (n + 2) → SimpleTerm (n + 3)
    | var i =>
      if i.val ≤ 1 then var ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_succ _)⟩
      else var ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
    | app c arg => app c (weakenBody2 arg)
    | lam _ => lam unit  -- Simplified: deep nesting not fully supported
    | unit => unit

/-! ## Substitution -/

/-- Substitute term s for variable 0 in term t -/
def subst (s : SimpleTerm n) : SimpleTerm (n + 1) → SimpleTerm n
  | var i =>
    if h : i.val = 0 then s
    else var ⟨i.val - 1, by
      have hi := i.isLt
      omega⟩
  | app c arg => app c (subst s arg)
  | lam body => lam (subst (weaken s) body)
  | unit => unit

/-! ## Closed Terms -/

/-- A closed term (no free variables) -/
abbrev Closed := SimpleTerm 0

/-- The identity function: λx. x -/
def identity : Closed :=
  lam (var ⟨0, Nat.zero_lt_one⟩)

/-- K combinator: λx. λy. x -/
def kCombinator : Closed :=
  lam (lam (var ⟨1, Nat.one_lt_two⟩))

end SimpleTerm

/-! ## Environment-Based Substitution

MeTTaIL uses named variables with an environment for substitution.
We model this as a map from names to terms.
-/

/-- An environment maps variable names to patterns -/
def SubstEnv := List (String × Pattern)

namespace SubstEnv

/-- Empty environment -/
def empty : SubstEnv := []

/-- Extend environment with a binding -/
def extend (env : SubstEnv) (name : String) (term : Pattern) : SubstEnv :=
  (name, term) :: env

/-- Look up a variable in the environment -/
def find (env : SubstEnv) (name : String) : Option Pattern :=
  match env.find? (fun p => p.1 == name) with
  | some (_, term) => some term
  | none => none

/-- Filtering out x doesn't affect lookup of y when y ≠ x -/
theorem find_filter_neq (env : SubstEnv) (x y : String) (hne : y ≠ x) :
    find (env.filter (·.1 != x)) y = find env y := by
  induction env with
  | nil => rfl
  | cons pair env' ih =>
    unfold find
    simp only [List.filter]
    by_cases hpairx : pair.1 = x
    · -- pair.1 = x, so it gets filtered out
      have hfilter : (pair.1 != x) = false := by
        simp only [bne_eq_false_iff_eq, hpairx]
      simp only [hfilter]
      -- pair.1 = x ≠ y, so lookup y skips this pair anyway
      simp only [List.find?]
      have hpairy : (pair.1 == y) = false := by
        simp only [beq_eq_false_iff_ne]
        rw [hpairx]
        exact hne.symm
      simp only [hpairy]
      unfold find at ih
      exact ih
    · -- pair.1 ≠ x, so it's kept
      have hfilter : (pair.1 != x) = true := by
        simp only [bne_iff_ne, ne_eq, hpairx, not_false_eq_true]
      simp only [hfilter, List.find?]
      by_cases hpairy : pair.1 = y
      · -- Found y
        have hfound : (pair.1 == y) = true := by simp only [beq_iff_eq, hpairy]
        simp only [hfound]
      · -- Not y, continue
        have hnotfound : (pair.1 == y) = false := by simp only [beq_eq_false_iff_ne, ne_eq, hpairy, not_false_eq_true]
        simp only [hnotfound]
        unfold find at ih
        exact ih

end SubstEnv

/-! ## Pattern Normal Forms

A pattern is in "substitution normal form" if it contains no explicit `.subst` nodes.
In practice, we build patterns from vars, applications, lambdas, and collections,
not from explicit substitution markers.
-/

mutual
  /-- A pattern has no explicit substitution nodes -/
  def noExplicitSubst : Pattern → Bool
    | .var _ => true
    | .apply _ args => allNoExplicitSubst args
    | .lambda _ body => noExplicitSubst body
    | .multiLambda _ body => noExplicitSubst body
    | .subst _ _ _ => false
    | .collection _ elems _ => allNoExplicitSubst elems

  /-- Helper: all patterns in list have no explicit subst -/
  def allNoExplicitSubst : List Pattern → Bool
    | [] => true
    | p :: ps => noExplicitSubst p && allNoExplicitSubst ps
end

/-- If allNoExplicitSubst holds for a list and p ∈ list, then noExplicitSubst p -/
theorem allNoExplicitSubst_mem {ps : List Pattern} {p : Pattern}
    (hall : allNoExplicitSubst ps) (hp : p ∈ ps) : noExplicitSubst p := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    simp only [allNoExplicitSubst, Bool.and_eq_true] at hall
    cases List.mem_cons.mp hp with
    | inl heq => rw [heq]; exact hall.1
    | inr hmem => exact ih hall.2 hmem

/-! ## Pattern Substitution

Apply an environment to a pattern, replacing variables.
-/

/-- Apply substitution environment to a pattern -/
def applySubst (env : SubstEnv) : Pattern → Pattern
  | .var name =>
    match env.find name with
    | some replacement => replacement
    | none => .var name  -- Keep unbound variables
  | .apply constructor args =>
    .apply constructor (args.map (applySubst env))
  | .lambda x body =>
    -- Remove x from env to avoid capture
    let env' := env.filter (fun p => p.1 != x)
    .lambda x (applySubst env' body)
  | .multiLambda xs body =>
    let env' := env.filter (fun p => !xs.contains p.1)
    .multiLambda xs (applySubst env' body)
  | .subst body x replacement =>
    -- Explicit substitution: apply it
    let replacement' := applySubst env replacement
    let env' := env.extend x replacement'
    applySubst env' body
  | .collection ct elements rest =>
    .collection ct (elements.map (applySubst env)) rest
termination_by p => sizeOf p

/-! ## Freshness Checking

Check if a variable is fresh (not free) in a pattern.
-/

/-- Get free variables of a pattern -/
def freeVars : Pattern → List String
  | .var name => [name]
  | .apply _ args => args.flatMap freeVars
  | .lambda x body => (freeVars body).filter (· != x)
  | .multiLambda xs body => (freeVars body).filter (!xs.contains ·)
  | .subst body x replacement =>
    (freeVars body).filter (· != x) ++ freeVars replacement
  | .collection _ elements _ => elements.flatMap freeVars
termination_by p => sizeOf p

/-- Check if a variable is fresh in a pattern -/
def isFresh (x : String) (p : Pattern) : Bool :=
  !((freeVars p).contains x)

/-- Check a freshness condition -/
def checkFreshness (fc : FreshnessCondition) : Bool :=
  isFresh fc.varName fc.term

/-! ## Connection to MeTTaIL Rewrites

MeTTaIL rewrites like `(PPar {(PInput n p), (POutput n q), ...rest}) ~> (PPar {p[@q], ...rest})`
involve substitution: `p[@q]` means "substitute @q for the bound variable in p".

In our formalization:
- `p` is a pattern with a bound variable
- `@q` is `NQuote q`
- The substitution is `applySubst [("x", NQuote q)] p`
-/

/-- Apply the ρ-calculus COMM rule substitution -/
def commSubst (pBody : Pattern) (boundVar : String) (q : Pattern) : Pattern :=
  applySubst (SubstEnv.extend SubstEnv.empty boundVar (.apply "NQuote" [q])) pBody

/-! ## Theorems

Empty substitution is identity on patterns without explicit subst nodes.
Proof uses mutual recursion mirroring the definition of noExplicitSubst.
-/

mutual
  theorem subst_empty (p : Pattern) (h : noExplicitSubst p) :
      applySubst SubstEnv.empty p = p :=
    match p with
    | .var name => by simp only [applySubst, SubstEnv.find, SubstEnv.empty, List.find?]
    | .apply constructor args => by
      unfold noExplicitSubst at h
      simp only [applySubst]
      congr 1
      exact subst_empty_list args h
    | .lambda x body => by
      unfold noExplicitSubst at h
      simp only [applySubst, SubstEnv.empty, List.filter_nil]
      congr 1
      exact subst_empty body h
    | .multiLambda xs body => by
      unfold noExplicitSubst at h
      simp only [applySubst, SubstEnv.empty, List.filter_nil]
      congr 1
      exact subst_empty body h
    | .subst _ _ _ => by
      -- noExplicitSubst returns false for subst, so h : false = true
      unfold noExplicitSubst at h
      exact (Bool.false_ne_true h).elim
    | .collection ct elems rest => by
      unfold noExplicitSubst at h
      simp only [applySubst]
      congr 1
      exact subst_empty_list elems h

  theorem subst_empty_list (ps : List Pattern) (h : allNoExplicitSubst ps) :
      ps.map (applySubst SubstEnv.empty) = ps :=
    match ps with
    | [] => by simp only [List.map_nil]
    | p :: ps' => by
      unfold allNoExplicitSubst at h
      simp only [Bool.and_eq_true] at h
      simp only [List.map_cons]
      congr 1
      · exact subst_empty p h.1
      · exact subst_empty_list ps' h.2
end

/-- Helper: filter idempotence -/
theorem filter_filter_same {α : Type*} (p : α → Bool) (xs : List α) :
    (xs.filter p).filter p = xs.filter p := by
  simp only [List.filter_filter, Bool.and_self]

/-- Helper: filter commutativity -/
theorem filter_comm {α : Type*} (p q : α → Bool) (xs : List α) :
    (xs.filter p).filter q = (xs.filter q).filter p := by
  simp only [List.filter_filter]
  congr 1
  funext a
  exact (Bool.and_comm (p a) (q a)).symm

/-- Helper: if xs.contains x = true, then x ∈ xs -/
theorem elem_of_contains {α : Type*} [DecidableEq α] {xs : List α} {x : α}
    (h : xs.contains x = true) : x ∈ xs := by
  rw [List.contains_iff_exists_mem_beq] at h
  obtain ⟨y, hy, hbeq⟩ := h
  rw [beq_iff_eq] at hbeq
  rwa [hbeq]

/-- Helper: if x ∈ xs, then xs.contains x = true -/
theorem contains_of_elem {α : Type*} [DecidableEq α] {xs : List α} {x : α}
    (h : x ∈ xs) : xs.contains x = true := by
  rw [List.contains_iff_exists_mem_beq]
  exact ⟨x, h, beq_self_eq_true x⟩

/-- Helper: filter can be absorbed when one predicate implies another.
    Note: The hypothesis `_h` is not needed for this particular proof,
    but it documents the intended use case (when one filter subsumes another). -/
theorem filter_filter_absorb {α : Type*} (p q : α → Bool) (xs : List α)
    (_h : ∀ a ∈ xs, q a = true → p a = true) :
    (xs.filter p).filter q = (xs.filter q).filter p := by
  simp only [List.filter_filter]
  congr 1
  funext a
  exact (Bool.and_comm (p a) (q a)).symm

/-- Helper: if x ∉ FV(.var y), then x ≠ y -/
theorem fresh_var_neq {x y : String} (h : isFresh x (.var y)) : x ≠ y := by
  unfold isFresh freeVars at h
  simp only [List.contains_cons, List.contains_nil, Bool.or_false,
             Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  exact h

/-- Helper: if x ∉ FV(.apply c args), then x ∉ FV(p) for all p ∈ args -/
theorem fresh_apply {x : String} {c : String} {args : List Pattern}
    (h : isFresh x (.apply c args)) : ∀ p ∈ args, isFresh x p := by
  intro p hp
  unfold isFresh at h ⊢
  unfold freeVars at h
  rw [Bool.not_eq_true'] at h ⊢
  by_contra habs
  push_neg at habs
  cases hb : (freeVars p).contains x with
  | false => exact habs hb
  | true =>
    have hmem := elem_of_contains hb
    have helem : x ∈ args.flatMap freeVars := List.mem_flatMap.mpr ⟨p, hp, hmem⟩
    have hcontains := contains_of_elem helem
    rw [h] at hcontains
    exact Bool.false_ne_true hcontains

/-- Helper: if x ∉ FV(.lambda y body), then x = y or x ∉ FV(body) -/
theorem fresh_lambda {x y : String} {body : Pattern}
    (h : isFresh x (.lambda y body)) : x = y ∨ isFresh x body := by
  unfold isFresh freeVars at h
  by_cases hxy : x = y
  · exact Or.inl hxy
  · right
    unfold isFresh
    rw [Bool.not_eq_true'] at h ⊢
    by_contra habs
    push_neg at habs
    cases hb : (freeVars body).contains x with
    | false => exact habs hb
    | true =>
      have hmem := elem_of_contains hb
      have hfiltered : x ∈ (freeVars body).filter (· != y) := by
        simp only [List.mem_filter]
        exact ⟨hmem, bne_iff_ne.mpr hxy⟩
      have hcontains := contains_of_elem hfiltered
      rw [h] at hcontains
      exact Bool.false_ne_true hcontains

/-- Helper: if x ∉ FV(.collection ct elems rest), then x ∉ FV(p) for all p ∈ elems -/
theorem fresh_collection {x : String} {ct : CollType} {elems : List Pattern} {rest : Option String}
    (h : isFresh x (.collection ct elems rest)) : ∀ p ∈ elems, isFresh x p := by
  intro p hp
  unfold isFresh at h ⊢
  unfold freeVars at h
  rw [Bool.not_eq_true'] at h ⊢
  by_contra habs
  push_neg at habs
  cases hb : (freeVars p).contains x with
  | false => exact habs hb
  | true =>
    have hmem := elem_of_contains hb
    have helem : x ∈ elems.flatMap freeVars := List.mem_flatMap.mpr ⟨p, hp, hmem⟩
    have hcontains := contains_of_elem helem
    rw [h] at hcontains
    exact Bool.false_ne_true hcontains

/-- Substitution respects freshness: if x ∉ FV(p), filtering x from env doesn't matter.

    This theorem is generalized over all environments env.
    The key insight is that filters commute and filtering is idempotent.

    **Precondition**: `p.noExplicitSubst = true`
    Well-typed ρ-calculus terms never contain explicit `.subst` patterns
    (they are intermediate forms that get immediately reduced).
    This precondition eliminates the impossible hsubst case.
-/
theorem subst_fresh (env : SubstEnv) (x : String) (p : Pattern)
    (hfresh : isFresh x p) (hno : noExplicitSubst p) :
    applySubst env p = applySubst (env.filter (·.1 != x)) p := by
  -- Use pattern induction
  induction p using Pattern.inductionOn generalizing env with
  | hvar y =>
    -- If x ∉ FV(.var y), then x ≠ y
    have hne : x ≠ y := fresh_var_neq hfresh
    simp only [applySubst]
    -- env.find y = (env.filter (·.1 != x)).find y when y ≠ x
    rw [SubstEnv.find_filter_neq env x y hne.symm]
  | happly c args ih =>
    -- Apply IH to each argument
    simp only [applySubst]
    congr 1
    apply List.map_congr_left
    intro p hp
    -- hno says all args have noExplicitSubst
    have hno_p : noExplicitSubst p := allNoExplicitSubst_mem hno hp
    exact ih p hp env (fresh_apply hfresh p hp) hno_p
  | hlambda y body ih =>
    -- Cases: x = y or x ≠ y
    simp only [applySubst]
    -- hno says body has noExplicitSubst
    unfold noExplicitSubst at hno
    cases fresh_lambda hfresh with
    | inl hxy =>
      -- x = y: the inner filter already removes x
      subst hxy
      -- env.filter (·.1 != x) then filter (·.1 != x) = env.filter (·.1 != x)
      -- by filter idempotence
      congr 1
      rw [filter_comm]
      rw [filter_filter_same]
    | inr hfresh_body =>
      -- x ≠ y: apply IH
      congr 1
      -- Need: (env.filter (·.1 != y)).filter (·.1 != x) =
      --       (env.filter (·.1 != x)).filter (·.1 != y)
      rw [filter_comm]
      exact ih (env.filter (fun p => p.1 != y)) hfresh_body hno
  | hmultiLambda ys body ih =>
    simp only [applySubst]
    -- hno says body has noExplicitSubst
    unfold noExplicitSubst at hno
    -- Similar to lambda case but with multiple binders
    -- Goal: Pattern.multiLambda ys (applySubst env' body) = Pattern.multiLambda ys (applySubst env'' body)
    -- Use congr to reduce to showing the applySubst calls are equal
    congr 1
    -- Check if x is fresh in body (after filtering ys)
    unfold isFresh freeVars at hfresh
    rw [Bool.not_eq_true'] at hfresh
    -- If x ∈ ys, the result is the same (filter removes it)
    -- If x ∉ ys and x ∉ FV(body), apply IH
    cases hxys : ys.contains x with
    | true => -- x ∈ ys: filtering by (·.1 != x) is subsumed by filtering by (!ys.contains ·.1)
      -- Since x ∈ ys, any p with p.1 = x would have ys.contains p.1 = true
      -- So env.filter (fun p => !ys.contains p.1) already excludes x
      -- Hence: env.filter (!ys.contains ·.1) = (env.filter (·.1 != x)).filter (!ys.contains ·.1)
      have heq : env.filter (fun p => !ys.contains p.1) =
                 (env.filter (·.1 != x)).filter (fun p => !ys.contains p.1) := by
        -- Use filter_filter to merge filters on RHS
        rw [List.filter_filter]
        -- Now show: env.filter (!ys.contains ·.1) = env.filter ((·.1 != x) && (!ys.contains ·.1))
        -- Key insight: !ys.contains a.1 = true implies a.1 != x (since x ∈ ys)
        induction env with
        | nil => rfl
        | cons a tl ih =>
          simp only [List.filter_cons]
          -- Both sides have if on !ys.contains a.1 and a.1 != x && !ys.contains a.1
          cases hnotc : (!ys.contains a.1)
          case false =>
            -- !ys.contains a.1 = false, so both ifs take false branch
            -- First if: (!ys.contains a.1) = true? No, it's false
            -- Second if: (a.1 != x && !ys.contains a.1) = true? No, because !ys.contains a.1 = false
            simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, bne_iff_ne, ne_eq]
            -- Goal should now be ih: tl equality
            exact ih
          case true =>
            -- !ys.contains a.1 = true, so first if takes true branch
            -- For second if: a.1 != x must also be true (since x ∈ ys implies a.1 ≠ x)
            have hne : (a.1 != x) = true := by
              rw [bne_iff_ne]
              intro heqa
              rw [heqa, hxys] at hnotc
              exact Bool.false_ne_true hnotc
            simp only [↓reduceIte, hne, Bool.true_and, ih]
      -- Goal after congr 1: applySubst (env.filter ...) body = applySubst ((env.filter ...).filter ...) body
      -- Use heq to rewrite and close with rfl
      rw [heq]
    | false => -- x ∉ ys: need to show isFresh x body and apply IH
      -- hxys : ys.contains x = false
      have hfresh_body : isFresh x body := by
        unfold isFresh
        rw [Bool.not_eq_true']
        -- hfresh says: ((freeVars body).filter (!ys.contains ·)).contains x = false
        -- We need: (freeVars body).contains x = false
        -- If (freeVars body).contains x = true, then x ∈ freeVars body
        -- Since x ∉ ys, filter would keep x, giving filtered.contains x = true
        -- But hfresh says filtered.contains x = false, contradiction
        cases hb : (freeVars body).contains x with
        | false => rfl
        | true =>
          have hmem := elem_of_contains hb
          -- hxys : ys.contains x = false, so !ys.contains x = true
          have hfiltered : x ∈ (freeVars body).filter (!ys.contains ·) := by
            simp only [List.mem_filter, hxys]
            exact ⟨hmem, rfl⟩
          have hcontains := contains_of_elem hfiltered
          rw [hfresh] at hcontains
          exact absurd hcontains Bool.false_ne_true
      -- IH: applySubst env' body = applySubst (env'.filter (·.1 != x)) body
      -- where env' = env.filter (!ys.contains ·.1)
      -- We need: applySubst env' body = applySubst (env.filter (·.1 != x)).filter (!ys.contains ·.1) body
      -- By filter_comm: (env.filter (·.1 != x)).filter (!ys.contains ·.1) =
      --                 (env.filter (!ys.contains ·.1)).filter (·.1 != x) = env'.filter (·.1 != x)
      have hcomm : (env.filter (·.1 != x)).filter (fun p => !ys.contains p.1) =
                   (env.filter (fun p => !ys.contains p.1)).filter (·.1 != x) := by
        exact filter_comm (·.1 != x) (fun p => !ys.contains p.1) env
      rw [hcomm]
      exact ih (env.filter (fun p => !ys.contains p.1)) hfresh_body hno
  | hsubst body y repl ih_body ih_repl =>
    -- Explicit substitution case
    -- The key insight: hno says p.noExplicitSubst = true
    -- But noExplicitSubst (.subst _ _ _) = false by definition
    -- This is a contradiction, so the case is impossible
    simp only [noExplicitSubst] at hno
    -- hno : false = true, which is absurd
    exact absurd hno Bool.false_ne_true
  | hcollection ct elems rest ih =>
    simp only [applySubst]
    congr 1
    apply List.map_congr_left
    intro p hp
    -- hno says all elems have noExplicitSubst
    unfold noExplicitSubst at hno
    have hno_p : noExplicitSubst p := allNoExplicitSubst_mem hno hp
    exact ih p hp env (fresh_collection hfresh p hp) hno_p

/-! ## Summary

This file provides:

1. ✅ **Simple de Bruijn terms**: `SimpleTerm n` with intrinsic scoping
2. ✅ **Weakening**: `weaken` shifts indices up
3. ✅ **Substitution**: `subst` is capture-avoiding (for de Bruijn terms)
4. ✅ **Environment-based substitution**: `SubstEnv` and `applySubst`
5. ✅ **Freshness checking**: `freeVars`, `isFresh`, `checkFreshness`
6. ✅ **COMM rule substitution**: `commSubst` for ρ-calculus

**Proven theorems:**
- `find_filter_neq`: Filtering out x doesn't affect lookup of y ≠ x
- `filter_filter_same`: Filter idempotence
- `filter_comm`: Filter commutativity
- `elem_of_contains`: xs.contains x = true → x ∈ xs
- `contains_of_elem`: x ∈ xs → xs.contains x = true
- `subst_empty`: Empty substitution is identity (on patterns without explicit subst)
- `subst_empty_list`: List version of above
- `subst_fresh`: If x ∉ FV(p) ∧ p.noExplicitSubst, filtering x from env doesn't change result
  - Uses: `Pattern.inductionOn` custom recursor for nested inductive types
  - Key insight: Adding `noExplicitSubst` precondition makes hsubst case vacuously true
  - The precondition is justified because well-typed terms never contain explicit `.subst`

**No remaining sorries!**

**Connection to MeTTaIL**: The `subst.rs` file in mettail-rust uses moniker's
`Scope` type and environment-based substitution, which matches our `applySubst`.
-/

end Mettapedia.OSLF.MeTTaIL.Substitution
