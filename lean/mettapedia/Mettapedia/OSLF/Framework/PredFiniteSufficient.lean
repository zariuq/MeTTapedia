import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.SubstitutabilityTheorem1
import Mettapedia.Logic.OSLFImageFinite
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# Positive Sufficient Condition for Predecessor-Finiteness

Complements the negative result `not_global_hPredFinite_langReduces_rhoCalc`
(canonical ρ-calculus COMM erases the channel name, so predecessor-finiteness
fails globally) with a positive characterization:

A `LanguageDef` is **predecessor-finite-safe** when every rewrite rule has
`isMatchCorrect` LHS and RHS (no `.subst` or `.collection` nodes), is
variable-preserving (every LHS free variable appears in the RHS), has
no premises, and congruence descent is disabled.

Under this condition the predecessor set of any term is finite:
`matchPattern r.right q` gives a finite list of candidate binding sets,
and each determines a unique predecessor via `applyBindings bs r.left`.

## LLM Primer: WF-recursive equation lemmas
`applyBindings`, `freeVars`, `matchPattern` are WF-recursive. They do NOT
reduce via `rfl`, `decide`, or `simp [fn]`. Use `conv_lhs => rw [fn.eq_def]`
to unfold one level, then iota-reduce on concrete constructors.
`isMatchCorrectAux`/`isMatchCorrectListAux` are `mutual`-recursive and DO
reduce via `rfl`/`simp`/`decide` for concrete constructors.
-/

namespace Mettapedia.OSLF.Framework.PredFiniteSufficient

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises
open Mettapedia.OSLF.MeTTaIL.Substitution (freeVars)
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.Framework.TypeSynthesis

/-! ## Equation lemmas for WF-recursive functions -/

private theorem freeVars_fvar (x : String) : freeVars (.fvar x) = [x] := by
  conv_lhs => rw [freeVars.eq_def]

private theorem freeVars_bvar (k : Nat) : freeVars (.bvar k) = [] := by
  conv_lhs => rw [freeVars.eq_def]

private theorem freeVars_apply (c : String) (args : List Pattern) :
    freeVars (.apply c args) = args.flatMap freeVars := by
  conv_lhs => rw [freeVars.eq_def]

private theorem freeVars_lambda (nm : Option String) (body : Pattern) :
    freeVars (.lambda nm body) = freeVars body := by
  conv_lhs => rw [freeVars.eq_def]

private theorem freeVars_multiLambda (k : Nat) (nms : List String) (body : Pattern) :
    freeVars (.multiLambda k nms body) = freeVars body := by
  conv_lhs => rw [freeVars.eq_def]

private theorem applyBindings_bvar (bs : Bindings) (k : Nat) :
    applyBindings bs (.bvar k) = .bvar k := by
  conv_lhs => rw [applyBindings.eq_def]

private theorem applyBindings_apply (bs : Bindings) (c : String) (args : List Pattern) :
    applyBindings bs (.apply c args) = .apply c (args.map (applyBindings bs)) := by
  conv_lhs => rw [applyBindings.eq_def]

private theorem applyBindings_lambda (bs : Bindings) (nm : Option String) (body : Pattern) :
    applyBindings bs (.lambda nm body) = .lambda nm (applyBindings bs body) := by
  conv_lhs => rw [applyBindings.eq_def]

private theorem applyBindings_multiLambda (bs : Bindings) (k : Nat) (nms : List String) (body : Pattern) :
    applyBindings bs (.multiLambda k nms body) = .multiLambda k nms (applyBindings bs body) := by
  conv_lhs => rw [applyBindings.eq_def]

private theorem matchPattern_fvar (x : String) (t : Pattern) :
    matchPattern (.fvar x) t = [[(x, t)]] := by
  conv_lhs => rw [matchPattern.eq_def]

private theorem matchPattern_bvar (n m : Nat) :
    matchPattern (.bvar n) (.bvar m) = if (n == m) = true then [[]] else [] := by
  conv_lhs => rw [matchPattern.eq_def]

private theorem matchPattern_apply (c1 c2 : String) (pargs targs : List Pattern) :
    matchPattern (.apply c1 pargs) (.apply c2 targs) =
    if (c1 == c2 && pargs.length == targs.length) = true then matchArgs pargs targs else [] := by
  conv_lhs => rw [matchPattern.eq_def]

private theorem matchPattern_lambda (nm nm' : Option String) (bp bc : Pattern) :
    matchPattern (.lambda nm bp) (.lambda nm' bc) = matchPattern bp bc := by
  conv_lhs => rw [matchPattern.eq_def]

private theorem matchPattern_multiLambda (np nc : Nat) (nms nms' : List String) (bp bc : Pattern) :
    matchPattern (.multiLambda np nms bp) (.multiLambda nc nms' bc) =
    if (np == nc) = true then matchPattern bp bc else [] := by
  conv_lhs => rw [matchPattern.eq_def]

/-! ## isMatchCorrectListAux ↔ forall -/

private theorem isMatchCorrectListAux_iff (l : List Pattern) :
    isMatchCorrectListAux l = true ↔ ∀ p ∈ l, isMatchCorrectAux p = true := by
  induction l with
  | nil => simp [isMatchCorrectListAux]
  | cons p ps ih =>
    simp only [isMatchCorrectListAux, Bool.and_eq_true,
               List.mem_cons, forall_eq_or_imp]
    exact ⟨fun ⟨hp, hps⟩ => ⟨hp, ih.mp hps⟩, fun ⟨hp, hps⟩ => ⟨hp, ih.mpr hps⟩⟩

/-! ## Sufficient Condition -/

/-- A rewrite rule is predecessor-finite-safe:
1. Both LHS and RHS are `isMatchCorrect` (no `.subst`, no `.collection`).
2. Variable-preserving: every free variable in the LHS appears in the RHS.
3. No premises: binding expansion is trivial. -/
structure RulePredFiniteSafe (r : RewriteRule) : Prop where
  lhsMatchCorrect : isMatchCorrectAux r.left = true
  rhsMatchCorrect : isMatchCorrectAux r.right = true
  variablePreserving : ∀ x : String, x ∈ freeVars r.left → x ∈ freeVars r.right
  noPremises : r.premises = []

/-- A language definition is predecessor-finite-safe:
all rules are predFiniteSafe and congruence descent is disabled. -/
structure LangPredFiniteSafe (lang : LanguageDef) : Prop where
  rulesSafe : ∀ r ∈ lang.rewrites, RulePredFiniteSafe r
  noCongruence : lang.congruenceCollections = []

/-! ## Structural Decomposition Lemmas -/

theorem not_allowsCongruenceIn_of_empty
    (lang : LanguageDef) (hEmpty : lang.congruenceCollections = [])
    (ct : CollType) : ¬ LanguageDef.allowsCongruenceIn lang ct := by
  unfold LanguageDef.allowsCongruenceIn
  rw [hEmpty]
  simp

theorem topRule_only_of_noCongruence
    (lang : LanguageDef) (hEmpty : lang.congruenceCollections = [])
    (relEnv : RelationEnv) (p q : Pattern)
    (h : DeclReducesWithPremises relEnv lang p q) :
    ∃ (r : RewriteRule) (_ : r ∈ lang.rewrites)
      (bs0 : Bindings) (_ : bs0 ∈ matchPattern r.left p)
      (bs : Bindings) (_ : bs ∈ applyPremisesWithEnv relEnv lang r.premises bs0),
      applyBindings bs r.right = q := by
  cases h with
  | topRule r hr bs0 hbs0 bs hbs hq =>
    exact ⟨r, hr, bs0, hbs0, bs, hbs, hq⟩
  | congElem hct => exact absurd hct (not_allowsCongruenceIn_of_empty lang hEmpty _)

theorem applyPremisesWithEnv_nil
    (relEnv : RelationEnv) (lang : LanguageDef) (seed : Bindings) :
    applyPremisesWithEnv relEnv lang [] seed = [seed] := by
  simp [applyPremisesWithEnv]

theorem mem_applyPremisesWithEnv_nil
    (relEnv : RelationEnv) (lang : LanguageDef) (seed bs : Bindings) :
    bs ∈ applyPremisesWithEnv relEnv lang [] seed ↔ bs = seed := by
  simp [applyPremisesWithEnv_nil]

/-! ## Binding Lookup Helper -/

/-- `applyBindings bs (.fvar x)` — the value a binding set assigns to variable `x`. -/
def lookupOrFvar (bs : Bindings) (x : String) : Pattern :=
  applyBindings bs (.fvar x)

theorem applyBindings_fvar (bs : Bindings) (x : String) :
    applyBindings bs (.fvar x) = lookupOrFvar bs x := rfl

/-! ## mergeBindings Success Lemma -/

def BindingsValued (bs : Bindings) (f : String → Pattern) : Prop :=
  ∀ name val, (name, val) ∈ bs → val = f name

theorem mergeBindings_some_of_valued
    (b1 b2 : Bindings) (f : String → Pattern)
    (h1 : BindingsValued b1 f) (h2 : BindingsValued b2 f) :
    ∃ result, mergeBindings b1 b2 = some result ∧ BindingsValued result f := by
  induction b2 generalizing b1 with
  | nil => exact ⟨b1, rfl, h1⟩
  | cons entry rest ih =>
    obtain ⟨name, val⟩ := entry
    have hval : val = f name := h2 name val (List.mem_cons_self ..)
    have h2rest : BindingsValued rest f :=
      fun n v hmem => h2 n v (List.mem_cons_of_mem _ hmem)
    -- The fold step: case split on find?
    simp only [mergeBindings, List.foldlM]
    cases hfind : b1.find? (·.1 == name) with
    | none =>
      change ∃ result, mergeBindings ((name, val) :: b1) rest = some result ∧ _
      exact ih ((name, val) :: b1)
        (fun n v hmem => by cases hmem with | head => exact hval | tail _ h => exact h1 n v h)
        h2rest
    | some pair =>
      obtain ⟨n', existing⟩ := pair
      have hpred := List.find?_some hfind
      simp at hpred  -- hpred : n' = name
      subst hpred  -- now n' replaces name everywhere
      have hmem_acc : (n', existing) ∈ b1 := List.mem_of_find?_eq_some hfind
      have hexist : existing = val := by
        rw [h1 n' existing hmem_acc, hval]
      subst hexist
      simp only [beq_self_eq_true, ↓reduceIte]
      change ∃ result, mergeBindings b1 rest = some result ∧ _
      exact ih b1 h1 h2rest

/-! ## matchPattern Completeness for isMatchCorrect Patterns -/

private theorem sizeOf_pattern_pos' (p : Pattern) : 0 < sizeOf p := by
  cases p <;> simp [sizeOf, Pattern._sizeOf_1]

private theorem matchPattern_complete_aux (n : Nat) :
    (∀ (pat : Pattern) (bs : Bindings),
      sizeOf pat ≤ n →
      isMatchCorrectAux pat = true →
      ∃ bs', bs' ∈ matchPattern pat (applyBindings bs pat) ∧
        BindingsValued bs' (lookupOrFvar bs)) ∧
    (∀ (pats : List Pattern) (bs : Bindings),
      sizeOf pats ≤ n →
      (∀ p ∈ pats, isMatchCorrectAux p = true) →
      ∃ bs', bs' ∈ matchArgs pats (pats.map (applyBindings bs)) ∧
        BindingsValued bs' (lookupOrFvar bs)) := by
  induction n with
  | zero =>
    exact ⟨fun pat _ hle =>
      absurd hle (by have := sizeOf_pattern_pos' pat; omega),
    fun pats _ hle _ => by
      cases pats with
      | nil =>
        refine ⟨[], ?_, fun _ _ h => nomatch h⟩
        simp [matchArgs]
      | cons p _ =>
        exact absurd hle (by simp [sizeOf, List._sizeOf_1])⟩
  | succ m ih =>
    obtain ⟨ih_pat, ih_args⟩ := ih
    refine ⟨?_, ?_⟩
    -- Pattern case
    · intro pat bs hle hmc
      match pat with
      | .fvar x =>
        refine ⟨[(x, lookupOrFvar bs x)], ?_, ?_⟩
        · rw [matchPattern_fvar]; exact List.mem_cons_self ..
        · intro name val hmem
          cases hmem with
          | head => rfl
          | tail _ htl => exact nomatch htl
      | .bvar k =>
        refine ⟨[], ?_, fun _ _ h => nomatch h⟩
        rw [applyBindings_bvar, matchPattern_bvar, if_pos (beq_self_eq_true k)]
        exact List.mem_cons_self ..
      | .apply c args =>
        simp only [isMatchCorrectAux] at hmc
        have hargs_mc := (isMatchCorrectListAux_iff args).mp hmc
        rw [applyBindings_apply, matchPattern_apply, if_pos]
        · have hle' : sizeOf args ≤ m := by
            have : sizeOf args < sizeOf (Pattern.apply c args) := by
              decreasing_trivial
            omega
          exact ih_args args bs hle' hargs_mc
        · simp [List.length_map]
      | .lambda _ _ => simp [isMatchCorrectAux] at hmc
      | .multiLambda _ _ _ => simp [isMatchCorrectAux] at hmc
      | .subst _ _ => simp [isMatchCorrectAux] at hmc
      | .collection _ _ _ => simp [isMatchCorrectAux] at hmc
    -- Args case
    · intro pats bs hle hmc
      match pats with
      | [] =>
        refine ⟨[], ?_, fun _ _ h => nomatch h⟩
        simp [matchArgs]
      | a :: as =>
        have hmc_a := hmc a (List.mem_cons_self ..)
        have hmc_as := fun p hp => hmc p (List.mem_cons.mpr (Or.inr hp))
        have hle_a : sizeOf a ≤ m := by
          have : sizeOf a < sizeOf (a :: as) := by
            decreasing_trivial
          omega
        have hle_as : sizeOf as ≤ m := by
          have : sizeOf as < sizeOf (a :: as) := by
            simp [sizeOf, List._sizeOf_1]
          omega
        obtain ⟨hb, hhb_mem, hhb_val⟩ := ih_pat a bs hle_a hmc_a
        obtain ⟨tb, htb_mem, htb_val⟩ := ih_args as bs hle_as hmc_as
        obtain ⟨result, hmerge, hresult_val⟩ :=
          mergeBindings_some_of_valued hb tb (lookupOrFvar bs) hhb_val htb_val
        refine ⟨result, ?_, hresult_val⟩
        simp [matchArgs, List.map]
        exact ⟨hb, hhb_mem, tb, htb_mem, hmerge⟩

theorem matchPattern_applyBindings_complete
    {pat : Pattern} {bs : Bindings}
    (hmc : isMatchCorrectAux pat = true) :
    ∃ bs', bs' ∈ matchPattern pat (applyBindings bs pat) ∧
      BindingsValued bs' (lookupOrFvar bs) :=
  (matchPattern_complete_aux (sizeOf pat)).1 pat bs (Nat.le_refl _) hmc

/-! ## applyBindings Injectivity for isMatchCorrect Patterns -/

private theorem applyBindings_inj_aux (n : Nat) :
    (∀ (pat : Pattern) (bs1 bs2 : Bindings),
      sizeOf pat ≤ n →
      isMatchCorrectAux pat = true →
      applyBindings bs1 pat = applyBindings bs2 pat →
      ∀ x, x ∈ freeVars pat → lookupOrFvar bs1 x = lookupOrFvar bs2 x) ∧
    (∀ (pats : List Pattern) (bs1 bs2 : Bindings),
      sizeOf pats ≤ n →
      (∀ p ∈ pats, isMatchCorrectAux p = true) →
      pats.map (applyBindings bs1) = pats.map (applyBindings bs2) →
      ∀ x, x ∈ pats.flatMap freeVars →
        lookupOrFvar bs1 x = lookupOrFvar bs2 x) := by
  induction n with
  | zero =>
    exact ⟨fun pat _ _ hle =>
      absurd hle (by have := sizeOf_pattern_pos' pat; omega),
    fun pats _ _ hle _ _ => by
      cases pats with
      | nil => intro _ hmem; exact nomatch hmem
      | cons p _ =>
        exact absurd hle (by simp [sizeOf, List._sizeOf_1])⟩
  | succ m ih =>
    obtain ⟨ih_pat, ih_args⟩ := ih
    refine ⟨?_, ?_⟩
    -- Pattern case
    · intro pat bs1 bs2 hle hmc heq x hx
      match pat with
      | .fvar y =>
        rw [freeVars_fvar] at hx
        simp at hx; subst hx
        exact heq
      | .bvar _ =>
        rw [freeVars_bvar] at hx
        exact nomatch hx
      | .apply c args =>
        simp only [isMatchCorrectAux] at hmc
        rw [applyBindings_apply, applyBindings_apply] at heq
        have hargs_eq : args.map (applyBindings bs1) = args.map (applyBindings bs2) :=
          (Pattern.apply.inj heq).2
        rw [freeVars_apply] at hx
        have hle' : sizeOf args ≤ m := by
          have : sizeOf args < sizeOf (Pattern.apply c args) := by
            decreasing_trivial
          omega
        exact ih_args args bs1 bs2 hle'
          ((isMatchCorrectListAux_iff args).mp hmc) hargs_eq x hx
      | .lambda _ _ => simp [isMatchCorrectAux] at hmc
      | .multiLambda _ _ _ => simp [isMatchCorrectAux] at hmc
      | .subst _ _ => simp [isMatchCorrectAux] at hmc
      | .collection _ _ _ => simp [isMatchCorrectAux] at hmc
    -- Args case
    · intro pats bs1 bs2 hle hmc heq x hx
      match pats with
      | [] => simp [List.flatMap] at hx
      | a :: as =>
        simp only [List.map] at heq
        have ⟨heq_a, heq_as⟩ := List.cons.inj heq
        rcases List.mem_flatMap.mp hx with ⟨p, hp, hxp⟩
        cases List.mem_cons.mp hp with
        | inl hpa =>
          subst hpa
          have hle_a : sizeOf p ≤ m := by
            have : sizeOf p < sizeOf (p :: as) := by
              decreasing_trivial
            omega
          exact ih_pat p bs1 bs2 hle_a
            (hmc p (List.mem_cons_self ..)) heq_a x hxp
        | inr hpas =>
          have hle_as : sizeOf as ≤ m := by
            have : sizeOf as < sizeOf (a :: as) := by
              simp [sizeOf, List._sizeOf_1]
            omega
          exact ih_args as bs1 bs2 hle_as
            (fun p hp => hmc p (List.mem_cons.mpr (Or.inr hp))) heq_as x
            (List.mem_flatMap.mpr ⟨p, hpas, hxp⟩)

theorem applyBindings_injective_isMatchCorrect
    {pat : Pattern} {bs1 bs2 : Bindings}
    (hmc : isMatchCorrectAux pat = true)
    (heq : applyBindings bs1 pat = applyBindings bs2 pat) :
    ∀ x, x ∈ freeVars pat → lookupOrFvar bs1 x = lookupOrFvar bs2 x :=
  (applyBindings_inj_aux (sizeOf pat)).1 pat bs1 bs2 (Nat.le_refl _) hmc heq

/-! ## applyBindings Dependence on Free Variables -/

private theorem applyBindings_dep_aux (n : Nat) :
    (∀ (pat : Pattern) (bs1 bs2 : Bindings),
      sizeOf pat ≤ n →
      isMatchCorrectAux pat = true →
      (∀ x, x ∈ freeVars pat → lookupOrFvar bs1 x = lookupOrFvar bs2 x) →
      applyBindings bs1 pat = applyBindings bs2 pat) ∧
    (∀ (pats : List Pattern) (bs1 bs2 : Bindings),
      sizeOf pats ≤ n →
      (∀ p ∈ pats, isMatchCorrectAux p = true) →
      (∀ x, x ∈ pats.flatMap freeVars → lookupOrFvar bs1 x = lookupOrFvar bs2 x) →
      pats.map (applyBindings bs1) = pats.map (applyBindings bs2)) := by
  induction n with
  | zero =>
    exact ⟨fun pat _ _ hle =>
      absurd hle (by have := sizeOf_pattern_pos' pat; omega),
    fun pats _ _ hle _ _ => by
      cases pats with
      | nil => simp [List.map]
      | cons p _ =>
        exact absurd hle (by simp [sizeOf, List._sizeOf_1])⟩
  | succ m ih =>
    obtain ⟨ih_pat, ih_args⟩ := ih
    refine ⟨?_, ?_⟩
    -- Pattern case
    · intro pat bs1 bs2 hle hmc hagree
      match pat with
      | .fvar x =>
        show lookupOrFvar bs1 x = lookupOrFvar bs2 x
        exact hagree x (by rw [freeVars_fvar]; exact List.mem_cons_self ..)
      | .bvar k =>
        rw [applyBindings_bvar, applyBindings_bvar]
      | .apply c args =>
        simp only [isMatchCorrectAux] at hmc
        rw [applyBindings_apply, applyBindings_apply]
        congr 1
        have hle' : sizeOf args ≤ m := by
          have : sizeOf args < sizeOf (Pattern.apply c args) := by
            decreasing_trivial
          omega
        exact ih_args args bs1 bs2 hle'
          ((isMatchCorrectListAux_iff args).mp hmc)
          (fun x hx => hagree x (by rw [freeVars_apply]; exact hx))
      | .lambda _ _ => simp [isMatchCorrectAux] at hmc
      | .multiLambda _ _ _ => simp [isMatchCorrectAux] at hmc
      | .subst _ _ => simp [isMatchCorrectAux] at hmc
      | .collection _ _ _ => simp [isMatchCorrectAux] at hmc
    -- Args case
    · intro pats bs1 bs2 hle hmc hagree
      match pats with
      | [] => simp [List.map]
      | a :: as =>
        simp only [List.map]
        have hle_a : sizeOf a ≤ m := by
          have : sizeOf a < sizeOf (a :: as) := by
            decreasing_trivial
          omega
        have hle_as : sizeOf as ≤ m := by
          have : sizeOf as < sizeOf (a :: as) := by
            simp [sizeOf, List._sizeOf_1]
          omega
        have heq_a := ih_pat a bs1 bs2 hle_a
          (hmc a (List.mem_cons_self ..))
          (fun x hx => hagree x (List.mem_flatMap.mpr ⟨a, List.mem_cons_self .., hx⟩))
        have heq_as := ih_args as bs1 bs2 hle_as
          (fun p hp => hmc p (List.mem_cons.mpr (Or.inr hp)))
          (fun x hx => hagree x (by
            rcases List.mem_flatMap.mp hx with ⟨p, hp, hxp⟩
            exact List.mem_flatMap.mpr ⟨p, List.mem_cons.mpr (Or.inr hp), hxp⟩))
        exact congrArg₂ List.cons heq_a heq_as

theorem applyBindings_eq_of_agree_isMatchCorrect
    {pat : Pattern} {bs1 bs2 : Bindings}
    (hmc : isMatchCorrectAux pat = true)
    (h : ∀ x, x ∈ freeVars pat → lookupOrFvar bs1 x = lookupOrFvar bs2 x) :
    applyBindings bs1 pat = applyBindings bs2 pat :=
  (applyBindings_dep_aux (sizeOf pat)).1 pat bs1 bs2 (Nat.le_refl _) hmc h

/-! ## Main Predecessor-Finiteness Theorem -/

private theorem predSet_via_rule_finite
    (r : RewriteRule) (q : Pattern)
    (hSafe : RulePredFiniteSafe r) :
    Set.Finite {p : Pattern |
      ∃ bs ∈ matchPattern r.left p,
        applyBindings bs r.right = q} := by
  apply Set.Finite.subset
    (Set.Finite.image (fun bs => applyBindings bs r.left)
      (List.finite_toSet (matchPattern r.right q)))
  intro p ⟨bs, hbs_match, hbs_apply⟩
  simp only [Set.mem_image]
  have hp : applyBindings bs r.left = p :=
    matchPattern_correct hbs_match hSafe.lhsMatchCorrect
  have ⟨bs', hbs'_mem, hbs'_val⟩ :=
    matchPattern_applyBindings_complete (bs := bs) hSafe.rhsMatchCorrect
  rw [hbs_apply] at hbs'_mem
  have hbs'_correct := matchPattern_correct hbs'_mem hSafe.rhsMatchCorrect
  have heq_rhs : applyBindings bs' r.right = applyBindings bs r.right := by
    rw [hbs'_correct, hbs_apply]
  have hinj := applyBindings_injective_isMatchCorrect hSafe.rhsMatchCorrect heq_rhs
  have hagree : ∀ x, x ∈ freeVars r.left → lookupOrFvar bs' x = lookupOrFvar bs x :=
    fun x hx => hinj x (hSafe.variablePreserving x hx)
  have := applyBindings_eq_of_agree_isMatchCorrect hSafe.lhsMatchCorrect hagree
  exact ⟨bs', hbs'_mem, by rw [this, hp]⟩

theorem predFinite_langReduces_of_langPredFiniteSafe
    (lang : LanguageDef) (hSafe : LangPredFiniteSafe lang)
    (q : Pattern) :
    Set.Finite {p : Pattern | langReduces lang p q} := by
  unfold langReduces langReducesUsing
  apply Set.Finite.subset (s := ⋃ r ∈ lang.rewrites,
    {p | ∃ bs ∈ matchPattern r.left p, applyBindings bs r.right = q})
  · exact Set.Finite.biUnion (List.finite_toSet _) fun r hr =>
      predSet_via_rule_finite r q (hSafe.rulesSafe r hr)
  intro p hp
  obtain ⟨r, hr, bs0, hbs0, bs, hbs, hq⟩ :=
    topRule_only_of_noCongruence lang hSafe.noCongruence RelationEnv.empty p q hp
  simp only [Set.mem_iUnion]
  have hprem := (hSafe.rulesSafe r hr).noPremises
  rw [hprem] at hbs
  rw [mem_applyPremisesWithEnv_nil] at hbs
  rw [hbs] at hq
  exact ⟨r, ⟨hr, bs0, hbs0, hq⟩⟩

/-! ## Theorem 1 Corollary -/

theorem theorem1_substitutability_predFiniteSafe
    (lang : LanguageDef) (hSafe : LangPredFiniteSafe lang)
    (I : Mettapedia.OSLF.Formula.AtomSem) :
    Mettapedia.OSLF.Framework.Theorem1SubstitutabilityEquiv
      (langReduces lang) I :=
  Mettapedia.OSLF.Framework.theorem1_substitutability_imageFinite
    (Mettapedia.Logic.OSLFImageFinite.imageFinite_langReduces lang)
    (predFinite_langReduces_of_langPredFiniteSafe lang hSafe)

/-! ## Exclusion: rhoCalc fails the condition -/

theorem rhoCalc_not_langPredFiniteSafe :
    ¬ LangPredFiniteSafe rhoCalc := by
  intro hSafe
  have hComm := hSafe.rulesSafe _ (List.mem_cons.mpr (Or.inl rfl))
  exact absurd hComm.rhsMatchCorrect (by decide)

end Mettapedia.OSLF.Framework.PredFiniteSufficient
