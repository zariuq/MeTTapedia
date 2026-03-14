import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine

/-!
# Generic MeTTaIL Rewrite Engine

Language-parametric rewrite engine that applies the rewrite rules from any
`LanguageDef` to concrete terms. This is the generic counterpart of the
specialized `RhoCalculus/Engine.lean`.

The engine uses the generic pattern matcher from `Match.lean` to:
1. Match concrete terms against rule LHS patterns
2. Produce variable bindings
3. Apply bindings to rule RHS patterns to produce reducts

## Architecture

```
LanguageDef (from Syntax.lean)
    |
    | .rewrites : List RewriteRule
    v
matchPattern (from Match.lean)  -- match rule.left against term
    |
    | bindings : List (String x Pattern)
    v
applyBindings (from Match.lean) -- apply bindings to rule.right
    |
    v
reducts : List Pattern
```

## Key Functions

- `rewriteStep` — apply all rules from a LanguageDef to a term
- `rewriteWithContext` — also try rules on subterms (congruence)
- `rewriteToNormalForm` — iterate to normal form

## Validation

The executable tests below demonstrate that `rewriteStep rhoCalc` produces
the same results as the specialized `RhoCalculus.Engine.reduceStep` for
all test cases.
-/

namespace Mettapedia.OSLF.MeTTaIL.Engine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine (patternToString)

instance : ToString Pattern := ⟨patternToString⟩

/-! ## No-Premise Baseline (for proof compatibility) -/

/-- Baseline top-level rewriting that ignores non-empty premise lists.
    This is the historical behavior from `Match.rewriteStep`. -/
abbrev rewriteStepNoPremises (lang : LanguageDef) (term : Pattern) : List Pattern :=
  rewriteStep lang term

/-! ## Congruence: Apply rules to subterms (No-Premise Baseline) -/

/-- Apply all rules to subterms of a collection (PAR/PAR_SET congruence).
    Returns all possible reducts where one element was rewritten. -/
def rewriteInCollectionNoPremises (lang : LanguageDef) (ct : CollType) (elems : List Pattern)
    (rest : Option String) : List Pattern :=
  if _hct : LanguageDef.allowsCongruenceIn lang ct then
    elems.zipIdx.flatMap fun (elem, i) =>
      let subReducts := rewriteStepNoPremises lang elem
      subReducts.map fun elem' =>
        .collection ct (elems.set i elem') rest
  else
    []

/-- Apply all rules to a term, including subterms (one level of congruence).
    This handles both top-level rewriting and PAR-like congruence. -/
def rewriteWithContextNoPremises (lang : LanguageDef) (term : Pattern) : List Pattern :=
  -- Top-level rewrites
  let topReducts := rewriteStepNoPremises lang term
  -- Subterm rewrites (congruence)
  let subReducts := match term with
    | .collection ct elems rest => rewriteInCollectionNoPremises lang ct elems rest
    | _ => []
  topReducts ++ subReducts

/-- Backward-compatible alias for the no-premise execution path.
    Existing proofs in `DeclReduces.lean` characterize this function. -/
abbrev rewriteWithContext (lang : LanguageDef) (term : Pattern) : List Pattern :=
  rewriteWithContextNoPremises lang term

/-! ## Premise-Aware Rule Application (mettail-rust style) -/

/-- Resolve the freshness variable name. If `x` is bound to an `fvar y`, use `y`;
    otherwise fall back to the literal `x`. Non-name bindings fail the premise. -/
private def resolveFreshVarName (bindings : Bindings) (x : String) : Option String :=
  match bindings.lookup x with
  | some (.fvar y) => some y
  | some _ => none
  | none => some x

/-- Pluggable relation environment for `relationQuery` premises.
    A relation name and concrete query arguments map to a finite table of tuples. -/
structure RelationEnv where
  tuples : String → List Pattern → List (List Pattern)

namespace RelationEnv

/-- Empty relation environment (no external relation tuples). -/
def empty : RelationEnv where
  tuples := fun _ _ => []

/-- Ordering on relation environments: `r₁ ≤ r₂` iff every tuple
    returned by `r₁` is also returned by `r₂`. -/
def le (r₁ r₂ : RelationEnv) : Prop :=
  ∀ rel args, r₁.tuples rel args ⊆ r₂.tuples rel args

instance : LE RelationEnv where le := RelationEnv.le

/-- The empty relation environment is the bottom element. -/
theorem empty_le (r : RelationEnv) : RelationEnv.empty ≤ r := by
  intro rel args row h
  simp [RelationEnv.empty] at h

end RelationEnv

/-- Built-in relation tuples derived from the executable engine.

    Design note:
    - `"reduces"` intentionally uses `rewriteWithContextNoPremises` as a one-step
      baseline. This avoids circular/self-referential premise evaluation when a
      rule queries reduction inside its own premise list.
    - External premise-aware behavior should be added through `RelationEnv`
      tables, where recursion/fuel policies can be controlled explicitly. -/
def builtinRelationTuples (lang : LanguageDef) (rel : String) (args : List Pattern) :
    List (List Pattern) :=
  match rel, args with
  | "reduces", [src, _] =>
      (rewriteWithContextNoPremises lang src).map fun tgt => [src, tgt]
  | "eq", [lhs, rhs] =>
      [[lhs, lhs], [rhs, rhs]]
  | _, _ => []

/-- Evaluate a relationQuery premise by matching query arguments against
    built-in and environment-provided relation tuples. -/
def relationQueryStep (relEnv : RelationEnv) (lang : LanguageDef)
    (bindings : Bindings) (rel : String) (args : List Pattern) : List Bindings :=
  let argPats := args.map (applyBindings bindings)
  let tuples := builtinRelationTuples lang rel argPats ++ relEnv.tuples rel argPats
  tuples.flatMap fun tuple =>
    (matchArgs argPats tuple).filterMap fun bPrem =>
      mergeBindings bindings bPrem

/-- Compute all binding extensions produced by one premise under current bindings.
    Congruence and relation premises may introduce fresh bindings. -/
def premiseStepWithEnv (relEnv : RelationEnv) (lang : LanguageDef) (bindings : Bindings) :
    Premise → List Bindings
  | .freshness fc =>
      let term' := applyBindings bindings fc.term
      match resolveFreshVarName bindings fc.varName with
      | some x =>
          if checkFreshness { varName := x, term := term' } then
            [bindings]
          else
            []
      | none => []
  | .congruence src tgt =>
      let src' := applyBindings bindings src
      (rewriteWithContextNoPremises lang src').flatMap fun cand =>
        (matchPattern tgt cand).filterMap fun bPrem =>
          mergeBindings bindings bPrem
  | .relationQuery rel args =>
      relationQueryStep relEnv lang bindings rel args

/-- Default premise step (built-ins only, no external relation environment). -/
def premiseStep (lang : LanguageDef) (bindings : Bindings) : Premise → List Bindings :=
  premiseStepWithEnv RelationEnv.empty lang bindings

/-- Any binding set produced by `premiseStepWithEnv` for a `relationQuery` premise
    arises from merging the original bindings with some auxiliary binding `bPrem`.
    This is the public key property of the otherwise-private `relationQueryStep`. -/
theorem premiseStepWithEnv_relationQuery_mem {relEnv : RelationEnv} {lang : LanguageDef}
    {bindings bs : Bindings} {rel : String} {args : List Pattern}
    (h : bs ∈ premiseStepWithEnv relEnv lang bindings (.relationQuery rel args)) :
    ∃ bPrem : Bindings, mergeBindings bindings bPrem = some bs := by
  simp only [premiseStepWithEnv, relationQueryStep] at h
  simp only [List.mem_flatMap] at h
  obtain ⟨tuple, _, h'⟩ := h
  simp only [List.mem_filterMap] at h'
  obtain ⟨bPrem, _, hmerge⟩ := h'
  exact ⟨bPrem, hmerge⟩

/-- Any binding set produced by `premiseStepWithEnv` for a `congruence` premise
    arises from merging the original bindings with some auxiliary binding `bPrem`. -/
theorem premiseStepWithEnv_congruence_mem {relEnv : RelationEnv} {lang : LanguageDef}
    {bindings bs : Bindings} {src tgt : Pattern}
    (h : bs ∈ premiseStepWithEnv relEnv lang bindings (.congruence src tgt)) :
    ∃ bPrem : Bindings, mergeBindings bindings bPrem = some bs := by
  simp only [premiseStepWithEnv] at h
  simp only [List.mem_flatMap] at h
  obtain ⟨cand, _, h'⟩ := h
  simp only [List.mem_filterMap] at h'
  obtain ⟨bPrem, _, hmerge⟩ := h'
  exact ⟨bPrem, hmerge⟩

/-- Any binding set produced by `premiseStepWithEnv` for a `freshness` premise
    is exactly the original bindings (unchanged). -/
theorem premiseStepWithEnv_freshness_mem {relEnv : RelationEnv} {lang : LanguageDef}
    {bindings bs : Bindings} {fc : FreshnessCondition}
    (h : bs ∈ premiseStepWithEnv relEnv lang bindings (.freshness fc)) :
    bs = bindings := by
  simp only [premiseStepWithEnv] at h
  split at h
  · split_ifs at h with hc
    · simp only [List.mem_singleton] at h; exact h
    · cases h
  · cases h

/-- When a freshness premise succeeds, some resolved variable `x` satisfies
    `isFresh x (applyBindings bindings fc.term)`. The resolution logic matches
    `Bindings.lookup`: `.fvar y` → `y`, non-fvar → impossible, unbound → `fc.varName`. -/
theorem premiseStepWithEnv_freshness_check {relEnv : RelationEnv} {lang : LanguageDef}
    {bindings bs : Bindings} {fc : FreshnessCondition}
    (h : bs ∈ premiseStepWithEnv relEnv lang bindings (.freshness fc)) :
    ∃ x, (match bindings.lookup fc.varName with
           | some (.fvar y) => some y
           | some _ => none
           | none => some fc.varName) = some x ∧
         isFresh x (applyBindings bindings fc.term) = true := by
  simp only [premiseStepWithEnv] at h
  unfold resolveFreshVarName at h
  split at h
  · -- case some x: resolution succeeded
    rename_i x heq
    split_ifs at h with hc
    · exact ⟨x, heq, by simp only [checkFreshness] at hc; exact hc⟩
    · cases h
  · -- case none: resolution failed, h : bs ∈ []
    cases h

/-- Apply all premises left-to-right, carrying all possible binding extensions. -/
def applyPremisesWithEnv (relEnv : RelationEnv) (lang : LanguageDef)
    (premises : List Premise) (seed : Bindings) : List Bindings :=
  premises.foldl
    (fun acc prem => acc.flatMap fun bs => premiseStepWithEnv relEnv lang bs prem)
    [seed]

/-- Default premise application (built-ins only). -/
def applyPremises (lang : LanguageDef) (premises : List Premise) (seed : Bindings) : List Bindings :=
  applyPremisesWithEnv RelationEnv.empty lang premises seed

/-- Boolean view with external relation environment. -/
def premiseHoldsWithEnv (relEnv : RelationEnv) (lang : LanguageDef)
    (bindings : Bindings) (premise : Premise) : Bool :=
  !(premiseStepWithEnv relEnv lang bindings premise).isEmpty

/-- Boolean view with external relation environment. -/
def premisesHoldWithEnv (relEnv : RelationEnv) (lang : LanguageDef)
    (bindings : Bindings) (premises : List Premise) : Bool :=
  !(applyPremisesWithEnv relEnv lang premises bindings).isEmpty

/-- Boolean view: whether a single premise has at least one satisfying extension. -/
def premiseHolds (lang : LanguageDef) (bindings : Bindings) (premise : Premise) : Bool :=
  premiseHoldsWithEnv RelationEnv.empty lang bindings premise

/-- Boolean view: whether the whole premise list has at least one satisfying extension. -/
def premisesHold (lang : LanguageDef) (bindings : Bindings) (premises : List Premise) : Bool :=
  premisesHoldWithEnv RelationEnv.empty lang bindings premises

/-! ## Monotonicity of Premise Evaluation

If `lang₁.rewrites ⊆ lang₂.rewrites` (every rule of `lang₁` is also a rule of `lang₂`)
and `lang₁.congruenceCollections = lang₂.congruenceCollections`, then premise evaluation
with `lang₁` produces a subset of premise evaluation with `lang₂`.

This is because `premiseStepWithEnv` depends on the language only through
`rewriteWithContextNoPremises` (via `.congruence` and `.relationQuery` premises),
and `rewriteWithContextNoPremises` is monotone in the rule set. -/

/-- `rewriteStepNoPremises` is monotone in the rule set. -/
theorem rewriteStepNoPremises_mono {lang₁ lang₂ : LanguageDef}
    (hrules : ∀ r, r ∈ lang₁.rewrites → r ∈ lang₂.rewrites)
    (term : Pattern) :
    ∀ p, p ∈ rewriteStepNoPremises lang₁ term → p ∈ rewriteStepNoPremises lang₂ term := by
  intro p hp
  simp only [rewriteStepNoPremises, rewriteStep] at hp ⊢
  rw [List.mem_flatMap] at hp ⊢
  obtain ⟨rule, hrmem, hpin⟩ := hp
  exact ⟨rule, hrules rule hrmem, hpin⟩

/-- `rewriteInCollectionNoPremises` is monotone in the rule set. -/
theorem rewriteInCollectionNoPremises_mono {lang₁ lang₂ : LanguageDef}
    (hrules : ∀ r, r ∈ lang₁.rewrites → r ∈ lang₂.rewrites)
    (hcong : lang₁.congruenceCollections = lang₂.congruenceCollections)
    (ct : CollType) (elems : List Pattern) (rest : Option String) :
    ∀ p, p ∈ rewriteInCollectionNoPremises lang₁ ct elems rest →
      p ∈ rewriteInCollectionNoPremises lang₂ ct elems rest := by
  intro p hp
  unfold rewriteInCollectionNoPremises at hp ⊢
  have hct₁ : LanguageDef.allowsCongruenceIn lang₁ ct := by
    by_contra h; rw [dif_neg h] at hp; cases hp
  have hct₂ : LanguageDef.allowsCongruenceIn lang₂ ct := by
    simp only [LanguageDef.allowsCongruenceIn] at hct₁ ⊢; rw [← hcong]; exact hct₁
  rw [dif_pos hct₁] at hp; rw [dif_pos hct₂]
  rw [List.mem_flatMap] at hp ⊢
  obtain ⟨⟨elem, i⟩, himem, hpin⟩ := hp
  refine ⟨⟨elem, i⟩, himem, ?_⟩
  rw [List.mem_map] at hpin ⊢
  obtain ⟨elem', helem', hpeq⟩ := hpin
  exact ⟨elem', rewriteStepNoPremises_mono hrules _ _ helem', hpeq⟩

/-- `rewriteWithContextNoPremises` is monotone in the rule set. -/
theorem rewriteWithContextNoPremises_mono {lang₁ lang₂ : LanguageDef}
    (hrules : ∀ r, r ∈ lang₁.rewrites → r ∈ lang₂.rewrites)
    (hcong : lang₁.congruenceCollections = lang₂.congruenceCollections)
    (term : Pattern) :
    ∀ p, p ∈ rewriteWithContextNoPremises lang₁ term →
      p ∈ rewriteWithContextNoPremises lang₂ term := by
  intro p hp
  unfold rewriteWithContextNoPremises at hp ⊢
  rw [List.mem_append] at hp ⊢
  rcases hp with htop | hsub
  · exact Or.inl (rewriteStepNoPremises_mono hrules term p htop)
  · right
    revert hsub
    cases term with
    | collection ct elems rest =>
        exact rewriteInCollectionNoPremises_mono hrules hcong ct elems rest p
    | _ => intro h; exact h

/-- Helper: `builtinRelationTuples` is monotone in the rule set.
    The only language-dependent case is `"reduces"`, which uses
    `rewriteWithContextNoPremises`. -/
private theorem builtinRelationTuples_mono {lang₁ lang₂ : LanguageDef}
    (hrules : ∀ r, r ∈ lang₁.rewrites → r ∈ lang₂.rewrites)
    (hcong : lang₁.congruenceCollections = lang₂.congruenceCollections)
    (rel : String) (args : List Pattern) :
    ∀ t, t ∈ builtinRelationTuples lang₁ rel args →
      t ∈ builtinRelationTuples lang₂ rel args := by
  intro t ht
  unfold builtinRelationTuples at ht ⊢
  -- Both ht and goal match on the same (rel, args), just different lang.
  -- Revert ht so split handles both simultaneously.
  revert ht; split
  · -- "reduces" case
    intro ht; rw [List.mem_map] at ht ⊢
    obtain ⟨tgt, htgt, hteq⟩ := ht
    exact ⟨tgt, rewriteWithContextNoPremises_mono hrules hcong _ _ htgt, hteq⟩
  · intro ht; exact ht  -- "eq" case: language-independent
  · intro ht; exact ht  -- default case: empty list

/-- `relationQueryStep` is monotone in the rule set. -/
private theorem relationQueryStep_mono {lang₁ lang₂ : LanguageDef}
    (hrules : ∀ r, r ∈ lang₁.rewrites → r ∈ lang₂.rewrites)
    (hcong : lang₁.congruenceCollections = lang₂.congruenceCollections)
    (relEnv : RelationEnv) (bindings : Bindings) (rel : String) (args : List Pattern) :
    ∀ bs, bs ∈ relationQueryStep relEnv lang₁ bindings rel args →
      bs ∈ relationQueryStep relEnv lang₂ bindings rel args := by
  intro bs hbs
  simp only [relationQueryStep] at hbs ⊢
  rw [List.mem_flatMap] at hbs ⊢
  obtain ⟨tuple, htmem, hbmem⟩ := hbs
  refine ⟨tuple, ?_, hbmem⟩
  rw [List.mem_append] at htmem ⊢
  rcases htmem with hbuiltin | hext
  · exact Or.inl (builtinRelationTuples_mono hrules hcong rel _ tuple hbuiltin)
  · exact Or.inr hext

/-- `premiseStepWithEnv` is monotone in the rule set. -/
theorem premiseStepWithEnv_mono {lang₁ lang₂ : LanguageDef}
    (hrules : ∀ r, r ∈ lang₁.rewrites → r ∈ lang₂.rewrites)
    (hcong : lang₁.congruenceCollections = lang₂.congruenceCollections)
    (relEnv : RelationEnv) (bindings : Bindings) (prem : Premise) :
    ∀ bs, bs ∈ premiseStepWithEnv relEnv lang₁ bindings prem →
      bs ∈ premiseStepWithEnv relEnv lang₂ bindings prem := by
  intro bs hbs
  match prem with
  | .freshness _ => exact hbs
  | .congruence src tgt =>
      simp only [premiseStepWithEnv] at hbs ⊢
      rw [List.mem_flatMap] at hbs ⊢
      obtain ⟨cand, hcmem, hbmem⟩ := hbs
      exact ⟨cand, rewriteWithContextNoPremises_mono hrules hcong _ cand hcmem, hbmem⟩
  | .relationQuery rel args =>
      simp only [premiseStepWithEnv] at hbs ⊢
      exact relationQueryStep_mono hrules hcong relEnv bindings rel args bs hbs

/-- `applyPremisesWithEnv` is monotone in the rule set:
    if every rule of `lang₁` is in `lang₂`, then any binding set
    produced by premise evaluation under `lang₁` is also produced
    under `lang₂`. -/
theorem applyPremisesWithEnv_mono {lang₁ lang₂ : LanguageDef}
    (hrules : ∀ r, r ∈ lang₁.rewrites → r ∈ lang₂.rewrites)
    (hcong : lang₁.congruenceCollections = lang₂.congruenceCollections)
    (relEnv : RelationEnv) (premises : List Premise) (seed : Bindings) :
    ∀ bs, bs ∈ applyPremisesWithEnv relEnv lang₁ premises seed →
      bs ∈ applyPremisesWithEnv relEnv lang₂ premises seed := by
  unfold applyPremisesWithEnv
  -- Strengthen: if acc₁ ⊆ acc₂ then foldl f₁ acc₁ ⊆ foldl f₂ acc₂
  suffices h : ∀ (acc₁ acc₂ : List Bindings),
      (∀ b, b ∈ acc₁ → b ∈ acc₂) →
      ∀ bs, bs ∈ premises.foldl
        (fun acc prem => acc.flatMap fun bs => premiseStepWithEnv relEnv lang₁ bs prem) acc₁ →
      bs ∈ premises.foldl
        (fun acc prem => acc.flatMap fun bs => premiseStepWithEnv relEnv lang₂ bs prem) acc₂ by
    exact h [seed] [seed] (fun b hb => hb)
  induction premises with
  | nil => intro acc₁ acc₂ hsub bs hbs; exact hsub bs hbs
  | cons prem prems ih =>
      intro acc₁ acc₂ hsub bs hbs
      simp only [List.foldl_cons] at hbs ⊢
      apply ih
      · -- Show: acc₁.flatMap (... lang₁ ...) ⊆ acc₂.flatMap (... lang₂ ...)
        intro b hb
        rw [List.mem_flatMap] at hb ⊢
        obtain ⟨a, hamem, hbmem⟩ := hb
        exact ⟨a, hsub a hamem, premiseStepWithEnv_mono hrules hcong relEnv a prem b hbmem⟩
      · exact hbs

/-! ## RelationEnv Monotonicity

If `relEnv₁ ≤ relEnv₂` (every tuple in `relEnv₁` is in `relEnv₂`),
then premise evaluation with `relEnv₁` produces a subset of the bindings
produced with `relEnv₂`. This is the relEnv-axis counterpart of the
rule-monotonicity chain above. -/

/-- `relationQueryStep` is monotone in the relation environment. -/
private theorem relationQueryStep_mono_relEnv {lang : LanguageDef}
    {relEnv₁ relEnv₂ : RelationEnv}
    (hle : relEnv₁ ≤ relEnv₂)
    (bindings : Bindings) (rel : String) (args : List Pattern) :
    ∀ bs, bs ∈ relationQueryStep relEnv₁ lang bindings rel args →
      bs ∈ relationQueryStep relEnv₂ lang bindings rel args := by
  intro bs hbs
  simp only [relationQueryStep] at hbs ⊢
  rw [List.mem_flatMap] at hbs ⊢
  obtain ⟨tuple, htmem, hbmem⟩ := hbs
  refine ⟨tuple, ?_, hbmem⟩
  rw [List.mem_append] at htmem ⊢
  rcases htmem with hbuiltin | hext
  · exact Or.inl hbuiltin
  · exact Or.inr (hle rel _ hext)

/-- `premiseStepWithEnv` is monotone in the relation environment. -/
theorem premiseStepWithEnv_mono_relEnv {lang : LanguageDef}
    {relEnv₁ relEnv₂ : RelationEnv}
    (hle : relEnv₁ ≤ relEnv₂)
    (bindings : Bindings) (prem : Premise) :
    ∀ bs, bs ∈ premiseStepWithEnv relEnv₁ lang bindings prem →
      bs ∈ premiseStepWithEnv relEnv₂ lang bindings prem := by
  intro bs hbs
  match prem with
  | .freshness _ => exact hbs
  | .congruence _ _ => exact hbs
  | .relationQuery rel args =>
      simp only [premiseStepWithEnv] at hbs ⊢
      exact relationQueryStep_mono_relEnv hle bindings rel args bs hbs

/-- `applyPremisesWithEnv` is monotone in the relation environment:
    if `relEnv₁ ≤ relEnv₂`, then any binding set produced by premise
    evaluation under `relEnv₁` is also produced under `relEnv₂`. -/
theorem applyPremisesWithEnv_mono_relEnv {lang : LanguageDef}
    {relEnv₁ relEnv₂ : RelationEnv}
    (hle : relEnv₁ ≤ relEnv₂)
    (premises : List Premise) (seed : Bindings) :
    ∀ bs, bs ∈ applyPremisesWithEnv relEnv₁ lang premises seed →
      bs ∈ applyPremisesWithEnv relEnv₂ lang premises seed := by
  unfold applyPremisesWithEnv
  suffices h : ∀ (acc₁ acc₂ : List Bindings),
      (∀ b, b ∈ acc₁ → b ∈ acc₂) →
      ∀ bs, bs ∈ premises.foldl
        (fun acc prem => acc.flatMap fun bs => premiseStepWithEnv relEnv₁ lang bs prem) acc₁ →
      bs ∈ premises.foldl
        (fun acc prem => acc.flatMap fun bs => premiseStepWithEnv relEnv₂ lang bs prem) acc₂ by
    exact h [seed] [seed] (fun b hb => hb)
  induction premises with
  | nil => intro acc₁ acc₂ hsub bs hbs; exact hsub bs hbs
  | cons prem prems ih =>
      intro acc₁ acc₂ hsub bs hbs
      simp only [List.foldl_cons] at hbs ⊢
      apply ih
      · intro b hb
        rw [List.mem_flatMap] at hb ⊢
        obtain ⟨a, hamem, hbmem⟩ := hb
        exact ⟨a, hsub a hamem, premiseStepWithEnv_mono_relEnv hle a prem b hbmem⟩
      · exact hbs

/-- Apply a single rule using premise-aware filtering on bindings, with a
    pluggable relation environment. -/
def applyRuleWithPremisesUsing (relEnv : RelationEnv) (lang : LanguageDef)
    (rule : RewriteRule) (term : Pattern) : List Pattern :=
  (matchPattern rule.left term).flatMap fun bs =>
    (applyPremisesWithEnv relEnv lang rule.premises bs).map fun bs' =>
      applyBindings bs' rule.right

/-- Apply a single rule using premise-aware filtering on bindings. -/
def applyRuleWithPremises (lang : LanguageDef) (rule : RewriteRule) (term : Pattern) : List Pattern :=
  applyRuleWithPremisesUsing RelationEnv.empty lang rule term

/-- Premise-aware top-level rewrite step with pluggable relation environment. -/
def rewriteStepWithPremisesUsing (relEnv : RelationEnv) (lang : LanguageDef)
    (term : Pattern) : List Pattern :=
  lang.rewrites.flatMap fun rule => applyRuleWithPremisesUsing relEnv lang rule term

/-- Premise-aware top-level rewrite step. -/
def rewriteStepWithPremises (lang : LanguageDef) (term : Pattern) : List Pattern :=
  rewriteStepWithPremisesUsing RelationEnv.empty lang term

/-- Premise-aware subterm rewriting in collections with pluggable
    relation environment. -/
def rewriteInCollectionWithPremisesUsing (relEnv : RelationEnv) (lang : LanguageDef)
    (ct : CollType) (elems : List Pattern) (rest : Option String) : List Pattern :=
  if _hct : LanguageDef.allowsCongruenceIn lang ct then
    elems.zipIdx.flatMap fun (elem, i) =>
      let subReducts := rewriteStepWithPremisesUsing relEnv lang elem
      subReducts.map fun elem' =>
        .collection ct (elems.set i elem') rest
  else
    []

/-- Premise-aware subterm rewriting in collections. -/
def rewriteInCollectionWithPremises (lang : LanguageDef) (ct : CollType) (elems : List Pattern)
    (rest : Option String) : List Pattern :=
  rewriteInCollectionWithPremisesUsing RelationEnv.empty lang ct elems rest

/-- Premise-aware one-step rewriting including one-level congruence,
    with pluggable relation environment. -/
def rewriteWithContextWithPremisesUsing (relEnv : RelationEnv) (lang : LanguageDef)
    (term : Pattern) : List Pattern :=
  let topReducts := rewriteStepWithPremisesUsing relEnv lang term
  let subReducts := match term with
    | .collection ct elems rest => rewriteInCollectionWithPremisesUsing relEnv lang ct elems rest
    | _ => []
  topReducts ++ subReducts

/-- Premise-aware one-step rewriting including one-level congruence. -/
def rewriteWithContextWithPremises (lang : LanguageDef) (term : Pattern) : List Pattern :=
  rewriteWithContextWithPremisesUsing RelationEnv.empty lang term

/-- Reduce to normal form with congruence (deterministic, with fuel). -/
def fullRewriteToNormalForm (lang : LanguageDef) (term : Pattern)
    (fuel : Nat := 1000) : Pattern :=
  match fuel with
  | 0 => term
  | fuel + 1 =>
    match rewriteWithContext lang term with
    | [] => term
    | q :: _ => fullRewriteToNormalForm lang q fuel

/-- Premise-aware normal-form reduction with pluggable relation
    environment (deterministic, with fuel). -/
def fullRewriteToNormalFormWithPremisesUsing (relEnv : RelationEnv) (lang : LanguageDef)
    (term : Pattern) (fuel : Nat := 1000) : Pattern :=
  match fuel with
  | 0 => term
  | fuel + 1 =>
    match rewriteWithContextWithPremisesUsing relEnv lang term with
    | [] => term
    | q :: _ => fullRewriteToNormalFormWithPremisesUsing relEnv lang q fuel

/-- Premise-aware normal-form reduction (deterministic, with fuel). -/
def fullRewriteToNormalFormWithPremises (lang : LanguageDef) (term : Pattern)
    (fuel : Nat := 1000) : Pattern :=
  fullRewriteToNormalFormWithPremisesUsing RelationEnv.empty lang term fuel

/-! ## Executable Tests: Generic Engine on rhoCalc -/

-- Helper: create common patterns (same as in RhoCalculus/Engine.lean)
private def pzero : Pattern := .apply "PZero" []
private def pdrop (n : Pattern) : Pattern := .apply "PDrop" [n]
private def nquote (p : Pattern) : Pattern := .apply "NQuote" [p]
private def poutput (n q : Pattern) : Pattern := .apply "POutput" [n, q]
private def pinput (n : Pattern) (body : Pattern) : Pattern :=
  .apply "PInput" [n, .lambda body]
private def ppar (elems : List Pattern) : Pattern :=
  .collection .hashBag elems none

-- Test 1: Generic COMM — same as specialized test
-- Generic COMM: {x!(0) | for(y<-x){y}} should reduce via rhoCalc COMM rule
#eval! do
  let x := Pattern.fvar "x"
  let term := ppar [poutput x pzero, pinput x (.bvar 0)]
  let reducts := rewriteStepNoPremises rhoCalc term
  IO.println s!"Generic COMM test: {term}"
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

-- Test 2: Generic COMM with congruence — nested reduction
-- Generic nested test: {*(@0) | x!(0)} — no top-level COMM, but DROP inside
#eval! do
  let term := ppar [pdrop (nquote pzero), poutput (.fvar "x") pzero]
  let topReducts := rewriteStepNoPremises rhoCalc term
  let fullReducts := rewriteWithContext rhoCalc term
  IO.println s!"Generic nested test: {term}"
  IO.println s!"  top-level reducts ({topReducts.length}): {if topReducts.isEmpty then "none" else "unexpected"}"
  IO.println s!"  with congruence ({fullReducts.length}):"
  for r in fullReducts do
    IO.println s!"    -> {r}"

-- Test 3: Race — two inputs competing
-- Generic race: {x!(0) | for(y<-x){y} | for(z<-x){*z}} should have 2 reducts
#eval! do
  let x := Pattern.fvar "x"
  let term := ppar [
    poutput x pzero,
    pinput x (.bvar 0),
    pinput x (pdrop (.bvar 0))
  ]
  let reducts := rewriteStepNoPremises rhoCalc term
  IO.println s!"Generic race test: {term}"
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"

-- Test 4: Multi-step using generic engine
-- Generic multi-step: {x!(*(@0)) | for(y<-x){*y}} should eventually reach 0
#eval! do
  let x := Pattern.fvar "x"
  let term := ppar [poutput x (pdrop (nquote pzero)), pinput x (pdrop (.bvar 0))]
  IO.println s!"Generic multi-step test: {term}"
  let result := fullRewriteToNormalForm rhoCalc term
  IO.println s!"  normal form: {result}"

-- Test 5: Comparison — show generic and specialized give same results
-- Comparison: generic rewriteStep vs specialized reduceStep
#eval! do
  let x := Pattern.fvar "x"
  let term := ppar [poutput x pzero, pinput x (.bvar 0)]
  let genericReducts := rewriteStepNoPremises rhoCalc term
  let specialReducts := Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine.reduceStep term
  IO.println s!"Comparison test: {term}"
  IO.println s!"  generic  ({genericReducts.length}): {genericReducts.map toString}"
  IO.println s!"  special  ({specialReducts.length}): {specialReducts.map toString}"
  IO.println s!"  match: {genericReducts.length == specialReducts.length}"

-- Test 6: Premise-aware top-level rewrite (ParCong premise is enforced)
#eval! do
  let term := ppar [pdrop (nquote pzero)]
  let noPrem := rewriteStepNoPremises rhoCalc term
  let withPrem := rewriteStepWithPremises rhoCalc term
  IO.println s!"Premise test: {term}"
  IO.println s!"  no-premise top-level ({noPrem.length}): {noPrem.map toString}"
  IO.println s!"  with-premise top-level ({withPrem.length}): {withPrem.map toString}"

-- Test 7: External relation environment for relationQuery premises
private def extA : Pattern := .apply "A" []
private def extB : Pattern := .apply "B" []

private def extRelationRule : RewriteRule := {
  name := "ExtRelationRule",
  typeContext := [],
  premises := [.relationQuery "allow" [extA]],
  left := extA,
  right := extB
}

private def extRelationLang : LanguageDef := {
  name := "ExtRelationLang",
  types := ["Proc"],
  terms := [],
  equations := [],
  rewrites := [extRelationRule]
}

private def extRelationEnv : RelationEnv where
  tuples := fun rel _args =>
    if rel == "allow" then
      [[extA]]
    else
      []

#eval! do
  let term := extA
  let noEnv := rewriteWithContextWithPremises extRelationLang term
  let withEnv := rewriteWithContextWithPremisesUsing extRelationEnv extRelationLang term
  IO.println s!"External relationQuery test: {term}"
  IO.println s!"  default env reducts ({noEnv.length}): {noEnv.map toString}"
  IO.println s!"  custom env reducts ({withEnv.length}): {withEnv.map toString}"

/-! ## Agreement Tests: Generic vs Specialized

Systematic comparison of `rewriteStep rhoCalc` (generic) against
`RhoCalculus.Engine.reduceStep` (specialized) on all test cases.
The generic engine handles COMM and DROP at top level; the specialized
engine also handles PAR (congruence). We compare `rewriteWithContext`
(generic + congruence) against `reduceStep` (specialized). -/

-- Agreement test: run both engines on a term and check equality
private def checkAgreement (label : String) (term : Pattern) : IO Unit := do
  let genericReducts := (rewriteWithContext rhoCalc term).map toString
  let specialReducts := (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine.reduceStep term).map toString
  -- Sort for order-independent comparison
  let gSorted := genericReducts.mergeSort (· < ·)
  let sSorted := specialReducts.mergeSort (· < ·)
  let agree := gSorted == sSorted
  IO.println s!"  {label}: generic={genericReducts.length} special={specialReducts.length} agree={agree}"
  unless agree do
    IO.println s!"    MISMATCH!"
    IO.println s!"    generic: {gSorted}"
    IO.println s!"    special: {sSorted}"

-- Agreement suite
#eval! do
  IO.println "=== Generic vs Specialized Agreement Suite ==="
  let x := Pattern.fvar "x"
  let y := Pattern.fvar "y"
  -- 1. Simple COMM
  checkAgreement "COMM" (ppar [poutput x pzero, pinput x (.bvar 0)])
  -- 2. Race (2 reducts)
  checkAgreement "Race" (ppar [poutput x pzero, pinput x (.bvar 0),
                                pinput x (pdrop (.bvar 0))])
  -- 3. DROP (top-level)
  checkAgreement "DROP" (pdrop (nquote pzero))
  -- 4. Normal form
  checkAgreement "NormalForm" pzero
  -- 5. Nested PAR (DROP inside bag)
  checkAgreement "NestedPAR" (ppar [pdrop (nquote pzero), poutput x pzero])
  -- 6. Pure bag, no redex
  checkAgreement "NoRedex" (ppar [poutput x pzero, poutput y pzero])
  -- 7. Empty bag
  checkAgreement "EmptyBag" (ppar [])
  -- 8. Single element bag
  checkAgreement "SingleBag" (ppar [pdrop (nquote pzero)])

end Mettapedia.OSLF.MeTTaIL.Engine
