import Mettapedia.Languages.ProcessCalculi.MORK.ThreePhaseExec
import Mettapedia.Languages.ProcessCalculi.Common.Star
import Mettapedia.OSLF.MeTTaIL.DeclReduces
import Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises

/-!
# MORK ↔ MeTTaIL Bridge

Connects MORK's execution model to MeTTaIL's declarative reduction semantics.

## Honest scope

MORK's match engine handles FLAT atoms (var/symbol/grounded) only.
This bridge is proved only for rules where:
  1. `r.left = .fvar x`  (MORK's `matchAtom` can unify a `.var` against anything)
  2. `morkTranslatable r.right = true`  (RHS has no beta-redex `.subst` nodes and
     no rest-variable `.collection _ _ (some _)` nodes)
  3. `isGroundAtom (morkPatternToAtom q) = true`  (result is ground)
  4. No `congElem` (collection-element) rewriting — MORK's flat Space does not
     model sub-collection rewrites

## LLM Notes
- `revert h_mt` before `induction rhs using Pattern.inductionOn` is REQUIRED so the
  motive is `fun rhs => morkTranslatable rhs = true → ...`. Without it, the IH
  would not carry `morkTranslatable a = true →` for sub-terms in happly/hcollection.
- `List.not_mem_nil` is ALL-implicit in 4.27: use `exact List.not_mem_nil ha` (applies
  the proof of `¬(a ∈ [])` to `ha : a ∈ []`) or just `simp at ha`.
- The `mutual` definition of `morkTranslatable`/`morkTranslatableList` avoids `where`
  clauses whose generated names are environment-dependent.
- `matchPattern` has a `let rec go` inside — unfold with
  `simp only [matchPattern, matchPattern.go]`. If `matchPattern.go` fails, try
  `delta matchPattern` then `simp only [matchPattern.go]`.
- CRITICAL: Do NOT open `MeTTaIL.Syntax`, `MeTTaIL.Match`, or `MeTTaIL.Substitution`.
  They conflict with MORK's own `Pattern`, `matchPattern`, `applySubst`.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## MeTTaIL type aliases (avoid name clashes with MORK names) -/

private abbrev ILP     := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
private abbrev ILCT    := Mettapedia.OSLF.MeTTaIL.Syntax.CollType
private abbrev ILRRule := Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule
private abbrev ILDL    := Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef
private abbrev ILBind  := Mettapedia.OSLF.MeTTaIL.Match.Bindings

private abbrev ilApplyBindings : ILBind → ILP → ILP :=
  Mettapedia.OSLF.MeTTaIL.Match.applyBindings
private abbrev ilMatchPattern : ILP → ILP → List ILBind :=
  Mettapedia.OSLF.MeTTaIL.Match.matchPattern

/-! ## Pattern → Atom Translation -/

def morkCollTypeSymbol : ILCT → String
  | .vec     => "Vec"
  | .hashBag => "Bag"
  | .hashSet => "Set"

/-- Translate a MeTTaIL Pattern to a MORK Atom (SYMBOLIC — `.subst` is NOT evaluated). -/
def morkPatternToAtom : ILP → Atom
  | .fvar x           => .var x
  | .bvar n           => .symbol s!"bvar{n}"
  | .apply c args     => .expression (.symbol c :: morkPatternToAtomList args)
  | .lambda body      => .expression [.symbol "λ", morkPatternToAtom body]
  | .multiLambda n body =>
      .expression (.symbol "λ*" :: .symbol (toString n) :: [morkPatternToAtom body])
  | .subst body repl  =>
      .expression [.symbol "subst", morkPatternToAtom body, morkPatternToAtom repl]
  | .collection ct elems _ =>
      .expression (.symbol (morkCollTypeSymbol ct) :: morkPatternToAtomList elems)
where
  morkPatternToAtomList : List ILP → List Atom
    | []      => []
    | p :: ps => morkPatternToAtom p :: morkPatternToAtomList ps

/-- `morkPatternToAtom` ignores the `rest` parameter of collections:
    the wildcard `_` in the `.collection ct elems _` branch drops it. -/
theorem morkPatternToAtom_rest_irrelevant (ct : Mettapedia.OSLF.MeTTaIL.Syntax.CollType)
    (elems : List ILP) (rest1 rest2 : Option String) :
    morkPatternToAtom (.collection ct elems rest1) =
    morkPatternToAtom (.collection ct elems rest2) := by
  simp [morkPatternToAtom]

/-! ## Translatability Predicate -/

/-! `morkTranslatable p` holds when `applySubst (translateBindings bs) ∘ morkPatternToAtom`
    and `morkPatternToAtom ∘ applyBindings bs` agree on `p`.
    Rules out `.subst` (beta-evaluating) and `.collection _ _ (some _)` (rest-expanding). -/
mutual
def morkTranslatable : ILP → Bool
  | .fvar _             => true
  | .bvar _             => true
  | .apply _ args       => morkTranslatableList args
  | .lambda body        => morkTranslatable body
  | .multiLambda _ body => morkTranslatable body
  | .subst _ _          => false
  | .collection _ elems none     => morkTranslatableList elems
  | .collection _ _    (some _) => false

def morkTranslatableList : List ILP → Bool
  | []      => true
  | p :: ps => morkTranslatable p && morkTranslatableList ps
end

private lemma morkTranslatableList_head {p : ILP} {ps : List ILP}
    (h : morkTranslatableList (p :: ps) = true) : morkTranslatable p = true := by
  simp only [morkTranslatableList, Bool.and_eq_true] at h; exact h.1

private lemma morkTranslatableList_tail {p : ILP} {ps : List ILP}
    (h : morkTranslatableList (p :: ps) = true) : morkTranslatableList ps = true := by
  simp only [morkTranslatableList, Bool.and_eq_true] at h; exact h.2

private lemma morkTranslatableList_mem {a : ILP} {args : List ILP}
    (h : morkTranslatableList args = true) (ha : a ∈ args) : morkTranslatable a = true := by
  induction args with
  | nil => simp at ha
  | cons p ps ih =>
    rw [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact morkTranslatableList_head h
    · exact ih (morkTranslatableList_tail h) ha

/-! ## Binding Translation -/

def translateBindings (bs : ILBind) : Subst :=
  bs.map fun (x, p) => (x, morkPatternToAtom p)

def patternToSpace (p : ILP) : Space := {morkPatternToAtom p}

/-! ## Binding Lookup Commutes -/

theorem translateBindings_lookup (bs : ILBind) (x : String) :
    (translateBindings bs).lookup x =
      (bs.find? (fun p => p.1 == x)).map (morkPatternToAtom ∘ Prod.snd) := by
  simp only [Subst.lookup, translateBindings]
  induction bs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.find?_cons]
    cases h : (hd.1 == x) with
    | true  => simp [Function.comp]
    | false => exact ih

/-! ## applySubstList commutes with morkPatternToAtomList

    Key helper: when all elements are morkTranslatable, applySubstList and
    morkPatternToAtomList commute with applyBindings. -/
private lemma applySubstList_commutes (bs : ILBind) :
    ∀ (elems : List ILP), morkTranslatableList elems = true →
    (∀ q ∈ elems, morkTranslatable q = true →
     applySubst (translateBindings bs) (morkPatternToAtom q) =
     morkPatternToAtom (ilApplyBindings bs q)) →
    applySubst.applySubstList (translateBindings bs)
        (morkPatternToAtom.morkPatternToAtomList elems) =
    morkPatternToAtom.morkPatternToAtomList (elems.map (ilApplyBindings bs)) := by
  intro elems
  induction elems with
  | nil => intros; rfl
  | cons e rest ihe =>
    intro h_mt ih
    simp only [morkPatternToAtom.morkPatternToAtomList, applySubst.applySubstList, List.map_cons]
    congr 1
    · exact ih e List.mem_cons_self (morkTranslatableList_head h_mt)
    · exact ihe (morkTranslatableList_tail h_mt)
               (fun q hq => ih q (List.mem_cons_of_mem e hq))

/-! ## applySubst commutes with morkPatternToAtom -/

/-- Helper: variable lookup. -/
private theorem applySubst_var (bs : ILBind) (x : String) :
    applySubst (translateBindings bs) (.var x) =
      morkPatternToAtom (ilApplyBindings bs (.fvar x)) := by
  change applySubst (translateBindings bs) (Atom.var x) =
    morkPatternToAtom (Mettapedia.OSLF.MeTTaIL.Match.applyBindings bs
      (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x))
  simp only [Mettapedia.OSLF.MeTTaIL.Match.applyBindings, applySubst]
  rw [translateBindings_lookup]
  cases h : bs.find? (fun p => p.1 == x) with
  | none => simp [morkPatternToAtom]
  | some pair => obtain ⟨_, val⟩ := pair; rfl

/-- `applySubst (translateBindings bs) ∘ morkPatternToAtom = morkPatternToAtom ∘ applyBindings bs`
    for `morkTranslatable` patterns (no `.subst` or `.collection _ _ (some _)` nodes).

    CRITICAL: use `revert h_mt` before `induction` so the motive is
    `fun rhs => morkTranslatable rhs = true → ...`, giving IH the form
    `∀ a ∈ args, morkTranslatable a = true → applySubst ... = ...`. -/
theorem applySubst_commutes (bs : ILBind) (rhs : ILP) (h_mt : morkTranslatable rhs = true) :
    applySubst (translateBindings bs) (morkPatternToAtom rhs) =
      morkPatternToAtom (ilApplyBindings bs rhs) := by
  -- revert h_mt so the induction motive includes `morkTranslatable rhs = true →`
  revert h_mt
  induction rhs using Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.inductionOn with
  | hbvar n =>
    intro _
    simp [morkPatternToAtom, ilApplyBindings,
          Mettapedia.OSLF.MeTTaIL.Match.applyBindings, applySubst]
  | hfvar x =>
    intro _
    exact applySubst_var bs x
  | happly c args ih =>
    -- ih : ∀ a ∈ args, morkTranslatable a = true → applySubst ... = ...
    intro h_mt
    have h_args : morkTranslatableList args = true := by
      simp only [morkTranslatable] at h_mt; exact h_mt
    simp only [morkPatternToAtom, ilApplyBindings,
               Mettapedia.OSLF.MeTTaIL.Match.applyBindings, applySubst, applySubst.applySubstList]
    congr 1; congr 1
    exact applySubstList_commutes bs args h_args ih
  | hlambda body ih =>
    intro h_mt
    have h_body : morkTranslatable body = true := by
      simp only [morkTranslatable] at h_mt; exact h_mt
    simp only [morkPatternToAtom, ilApplyBindings,
               Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
               applySubst, applySubst.applySubstList]
    exact congrArg (fun a => Atom.expression [Atom.symbol "λ", a]) (ih h_body)
  | hmultiLambda n body ih =>
    intro h_mt
    have h_body : morkTranslatable body = true := by
      simp only [morkTranslatable] at h_mt; exact h_mt
    simp only [morkPatternToAtom, ilApplyBindings,
               Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
               applySubst, applySubst.applySubstList]
    exact congrArg
      (fun a => Atom.expression [Atom.symbol "λ*", Atom.symbol (toString n), a]) (ih h_body)
  | hsubst body repl _ _ =>
    intro h_mt
    simp [morkTranslatable] at h_mt
  | hcollection ct elems rest ih =>
    intro h_mt
    cases rest with
    | some _ =>
      simp [morkTranslatable] at h_mt
    | none =>
      have h_elems : morkTranslatableList elems = true := by
        simp only [morkTranslatable] at h_mt; exact h_mt
      simp only [morkPatternToAtom, ilApplyBindings,
                 Mettapedia.OSLF.MeTTaIL.Match.applyBindings,
                 applySubst, applySubst.applySubstList,
                 List.append_nil]
      congr 1; congr 1
      exact applySubstList_commutes bs elems h_elems ih

/-! ## languageDefToExecRules -/

def rewriteRuleToExecRule (r : ILRRule) : ExecRule :=
  { priority := 40
    name     := "rule:" ++ r.name
    pat      := mkPattern [morkPatternToAtom r.left]
    tmpl     := mkTemplate [mkRemove (morkPatternToAtom r.left),
                             mkAdd    (morkPatternToAtom r.right)] }

def languageDefToExecRules (lang : ILDL) : List ExecRule :=
  lang.rewrites.filterMap fun r =>
    if r.premises.isEmpty then some (rewriteRuleToExecRule r) else none

/-! ## Core Bridge Lemmas -/

/-- `ilMatchPattern (.fvar x) p` returns exactly `[[(x, p)]]`. -/
private lemma ilMatchPattern_fvar (x : String) (p : ILP) :
    ilMatchPattern (.fvar x) p = [[(x, p)]] := by
  change Mettapedia.OSLF.MeTTaIL.Match.matchPattern
    (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x) p = [[(x, p)]]
  simp [Mettapedia.OSLF.MeTTaIL.Match.matchPattern]

/-- From `bs ∈ ilMatchPattern (.fvar x) p`, derive `bs = [(x, p)]`. -/
private lemma ilMatchPattern_fvar_unique (x : String) (p : ILP) (bs : ILBind)
    (hbs : bs ∈ ilMatchPattern (.fvar x) p) : bs = [(x, p)] :=
  List.mem_singleton.mp (ilMatchPattern_fvar x p ▸ hbs)

/-- `translateBindings [(x, p)] = [(x, morkPatternToAtom p)]`. -/
private lemma translateBindings_singleton (x : String) (p : ILP) :
    translateBindings [(x, p)] = [(x, morkPatternToAtom p)] := by
  simp [translateBindings]

/-- MORK `matchAtom [] (.var x) a = some [(x, a)]`. -/
private lemma matchAtom_var_fresh (x : String) (a : Atom) :
    matchAtom [] (.var x) a = some [(x, a)] := by
  simp [matchAtom, Subst.lookup]

/-- Membership in `matchOneInSpace [] (.var x) {a}`. -/
private lemma matchOneInSpace_var_singleton_mem (x : String) (a : Atom) :
    ([(x, a)], a) ∈ matchOneInSpace [] (.var x) ({a} : Finset Atom) := by
  simp only [matchOneInSpace, List.mem_filterMap]
  exact ⟨a, Finset.mem_toList.mpr (Finset.mem_singleton_self a),
         by simp [matchAtom_var_fresh]⟩

/-- When we apply `applySubst [(x, a)] (.var x)`, we get `a`. -/
private lemma applySubst_var_singleton (x : String) (a : Atom) :
    applySubst [(x, a)] (Atom.var x) = a := by
  simp [applySubst, Subst.lookup]

/-- `{a}.erase a = ∅`. -/
private lemma finset_singleton_erase_self (a : Atom) :
    ({a} : Finset Atom).erase a = ∅ := by
  simp [Finset.erase_eq]

/-! ## Top-Rule Bridge Theorem -/

/-- `patternToSpace q ∈ fireRule (patternToSpace p) (rewriteRuleToExecRule r)` when:
    - `r.left = .fvar x` (MORK can match any atom against a var pattern)
    - `morkTranslatable r.right = true` (applySubst_commutes applies)
    - `isGroundAtom (morkPatternToAtom q) = true` (applySink .add succeeds)
    - `bs ∈ ilMatchPattern r.left p` and `ilApplyBindings bs r.right = q` -/
theorem declReduces_topRule_fvar_mork_fire
    (p q : ILP) (x : String)
    (r : ILRRule)
    (hlhs : r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x)
    (htrans : morkTranslatable r.right = true)
    (bs : ILBind) (hbs : bs ∈ ilMatchPattern r.left p)
    (hrhs : ilApplyBindings bs r.right = q)
    (hground : isGroundAtom (morkPatternToAtom q) = true) :
    patternToSpace q ∈ fireRule (patternToSpace p) (rewriteRuleToExecRule r) := by
  -- Step 1: bs = [(x, p)]
  rw [hlhs] at hbs
  have hbs_eq : bs = [(x, p)] := ilMatchPattern_fvar_unique x p bs hbs
  -- Step 2: translateBindings bs = [(x, morkPatternToAtom p)]
  have hσ : translateBindings bs = [(x, morkPatternToAtom p)] := by
    rw [hbs_eq]; exact translateBindings_singleton x p
  -- Step 3: applySubst [(x, morkPatternToAtom p)] (morkPatternToAtom r.right) = morkPatternToAtom q
  have hrhs_atom : applySubst [(x, morkPatternToAtom p)] (morkPatternToAtom r.right) =
      morkPatternToAtom q := by
    have hcomm := applySubst_commutes bs r.right htrans
    rw [hσ] at hcomm
    rw [hrhs] at hcomm
    exact hcomm
  -- Step 4: show patternToSpace q ∈ fireRule (patternToSpace p) (rewriteRuleToExecRule r)
  simp only [fireRule, rewriteRuleToExecRule, patternToSpace]
  rw [List.mem_map]
  -- Witness: ([(x, morkPatternToAtom p)], {morkPatternToAtom p})
  refine ⟨([(x, morkPatternToAtom p)], {morkPatternToAtom p}), ?_, ?_⟩
  · -- Show witness is in matchPattern [] {morkPatternToAtom p} (mkPattern [.var x])
    -- matchPattern unfolds to go [.var x] [] ∅ which uses matchOneInSpace
    simp only [matchPattern, mkPattern, hlhs, morkPatternToAtom]
    apply List.mem_flatMap.mpr
    exact ⟨([(x, morkPatternToAtom p)], morkPatternToAtom p),
           matchOneInSpace_var_singleton_mem x (morkPatternToAtom p),
           List.mem_singleton.mpr rfl⟩
  · -- Show applySinks produces {morkPatternToAtom q}
    -- Template: [mkRemove (.var x), mkAdd (morkPatternToAtom r.right)]
    -- Binding:  σ = [(x, morkPatternToAtom p)]
    simp only [mkTemplate, applySinks, List.foldl_cons, List.foldl_nil]
    -- Step 4a: remove step — erase morkPatternToAtom p
    simp only [applySink, mkRemove, hlhs, morkPatternToAtom, applySubst_var_singleton,
               finset_singleton_erase_self]
    -- Step 4b: add step — add morkPatternToAtom q
    simp only [mkAdd, hrhs_atom, hground, ite_true, Finset.empty_union]

/-! ## Source-aware bridge (DeclReducesWithPremises → SourceExecRule)

A MeTTaIL `Premise.relationQuery rel args` checks whether an atom matching
`(rel arg₁ arg₂ ...)` exists in the relation environment. When the relation
environment IS the MORK workspace (common in flat-space models), this is
equivalent to a `SourceFactor.btm` workspace match.

This section defines the translation for rules where:
- The LHS is `.fvar x` (MORK can match against a variable)
- All premises are `relationQuery` (workspace lookups)
- All premise patterns are `morkTranslatable`
- The RHS is `morkTranslatable`
-/

private abbrev ILPremise := Mettapedia.OSLF.MeTTaIL.Syntax.Premise

/-- Translate a single MeTTaIL premise to a MORK source factor.
    Only `relationQuery` with a single-argument pattern maps cleanly to `btm`. -/
def premiseToSourceFactor : ILPremise → Option SourceFactor
  | .relationQuery rel args =>
    some (.btm (morkPatternToAtom (.apply rel args)))
  | _ => none

/-- All premises are translatable to MORK source factors. -/
def allPremisesTranslatable (premises : List ILPremise) : Bool :=
  premises.all (premiseToSourceFactor · |>.isSome)

/-- Extract the source factors from translatable premises. -/
def premisesToSourceFactors (premises : List ILPremise) : List SourceFactor :=
  premises.filterMap premiseToSourceFactor

/-- Translate a MeTTaIL rewrite rule (with translatable premises) to a
    MORK `SourceExecRule` using explicit source mode.
    The LHS becomes the first `btm` factor; premise queries become additional factors. -/
def rewriteRuleToSourceExecRule (r : ILRRule) : SourceExecRule :=
  let lhsFactor := SourceFactor.btm (morkPatternToAtom r.left)
  { priority := 40
    name     := "rule:" ++ r.name
    input    := .explicit (lhsFactor :: premisesToSourceFactors r.premises)
    tmpl     := mkTemplate [mkRemove (morkPatternToAtom r.left),
                             mkAdd    (morkPatternToAtom r.right)] }

/-- `rewriteRuleToSourceExecRule` produces rules with empty guards. -/
theorem rewriteRuleToSourceExecRule_guards (r : ILRRule) :
    (rewriteRuleToSourceExecRule r).guards = [] := rfl

/-! ### Extended premise classification (relationQuery + freshness) -/

/-- Classify a premise as either a source factor (workspace-facing) or
    a source guard (substitution-level condition).
    - `relationQuery` → `SourceFactor.btm`
    - `freshness` → `SourceGuard.freshness`
    - others → not yet translatable -/
def premiseToFactorOrGuard : ILPremise → Option (Sum SourceFactor SourceGuard)
  | .relationQuery rel args =>
    some (.inl (.btm (morkPatternToAtom (.apply rel args))))
  | .freshness fc =>
    some (.inr (.freshness fc.varName (morkPatternToAtom fc.term)))
  | _ => none

/-- Extended translatability: accepts `relationQuery` AND `freshness` premises. -/
def allPremisesTranslatableExt (premises : List ILPremise) : Bool :=
  premises.all (premiseToFactorOrGuard · |>.isSome)

/-- Extract source factors from a premise list (only `relationQuery` premises). -/
def premisesToSourceFactorsExt (premises : List ILPremise) : List SourceFactor :=
  premises.filterMap fun p => match premiseToFactorOrGuard p with
    | some (.inl f) => some f | _ => none

/-- Extract source guards from a premise list (only `freshness` premises). -/
def premisesToSourceGuards (premises : List ILPremise) : List SourceGuard :=
  premises.filterMap fun p => match premiseToFactorOrGuard p with
    | some (.inr g) => some g | _ => none

/-- Extended rule translation: populates both source factors and guards. -/
def rewriteRuleToSourceExecRuleExt (r : ILRRule) : SourceExecRule :=
  let lhsFactor := SourceFactor.btm (morkPatternToAtom r.left)
  { priority := 40
    name     := "rule:" ++ r.name
    input    := .explicit (lhsFactor :: premisesToSourceFactorsExt r.premises)
    guards   := premisesToSourceGuards r.premises
    tmpl     := mkTemplate [mkRemove (morkPatternToAtom r.left),
                             mkAdd    (morkPatternToAtom r.right)] }

/-- For `relationQuery`-only premise lists, `premisesToSourceFactorsExt` agrees with
    `premisesToSourceFactors` and guards are empty. -/
theorem premisesToSourceFactorsExt_compat (premises : List ILPremise)
    (hall : allPremisesTranslatable premises = true) :
    premisesToSourceFactorsExt premises = premisesToSourceFactors premises := by
  induction premises with
  | nil => rfl
  | cons p ps ih =>
    have htail : allPremisesTranslatable ps = true := by
      simp only [allPremisesTranslatable, List.all_eq_true] at hall ⊢
      exact fun q hq => hall q (List.mem_cons.mpr (.inr hq))
    have hp : (premiseToSourceFactor p).isSome = true := by
      simp only [allPremisesTranslatable, List.all_eq_true] at hall
      exact hall p List.mem_cons_self
    match p with
    | .relationQuery rel args =>
      show premisesToSourceFactorsExt (.relationQuery rel args :: ps) =
           premisesToSourceFactors (.relationQuery rel args :: ps)
      simp only [premisesToSourceFactorsExt, premisesToSourceFactors,
        List.filterMap_cons, premiseToFactorOrGuard, premiseToSourceFactor]
      congr 1
      exact ih htail
    | .freshness _ => simp [premiseToSourceFactor] at hp
    | .congruence _ _ => simp [premiseToSourceFactor] at hp

/-- For `relationQuery`-only premise lists, guards are empty. -/
theorem premisesToSourceGuards_compat (premises : List ILPremise)
    (hall : allPremisesTranslatable premises = true) :
    premisesToSourceGuards premises = [] := by
  induction premises with
  | nil => rfl
  | cons p ps ih =>
    have htail : allPremisesTranslatable ps = true := by
      simp only [allPremisesTranslatable, List.all_eq_true] at hall ⊢
      exact fun q hq => hall q (List.mem_cons.mpr (.inr hq))
    have hp : (premiseToSourceFactor p).isSome = true := by
      simp only [allPremisesTranslatable, List.all_eq_true] at hall
      exact hall p List.mem_cons_self
    match p with
    | .relationQuery _ _ =>
      show premisesToSourceGuards (.relationQuery _ _ :: ps) = []
      simp only [premisesToSourceGuards, List.filterMap_cons, premiseToFactorOrGuard]
      exact ih htail
    | .freshness _ => simp [premiseToSourceFactor] at hp
    | .congruence _ _ => simp [premiseToSourceFactor] at hp

/-- When all premises are `relationQuery`, `premisesToSourceFactors` has the
    same length as the premise list. -/
theorem premisesToSourceFactors_length (premises : List ILPremise)
    (hall : allPremisesTranslatable premises = true) :
    (premisesToSourceFactors premises).length = premises.length := by
  simp only [premisesToSourceFactors, allPremisesTranslatable, List.all_eq_true] at *
  induction premises with
  | nil => simp [List.filterMap]
  | cons p ps ih =>
    simp only [List.filterMap]
    have hp := hall p List.mem_cons_self
    match hpf : premiseToSourceFactor p with
    | some sf => simp [ih (fun q hq => hall q (List.mem_cons_of_mem p hq))]
    | none => simp [hpf] at hp

/-! ## Semantic bridge infrastructure -/

private abbrev ilMergeBindings := Mettapedia.OSLF.MeTTaIL.Match.mergeBindings
private abbrev ilPremiseStepWithEnv := Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv
private abbrev ilApplyPremisesWithEnv := Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv
private abbrev ILRelEnv := Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv

/-- Convert MeTTaIL `Bindings` to MORK `Subst` by translating each bound
    pattern to its atom representation. -/
def bindingsToSubst (bs : ILBind) : Subst :=
  bs.map fun (x, p) => (x, morkPatternToAtom p)

/-- Extract the MORK atom corresponding to a translatable premise.
    Returns `morkPatternToAtom (.apply rel args)` for `relationQuery`. -/
def premiseToAtom : ILPremise → Option Atom
  | .relationQuery rel args => some (morkPatternToAtom (.apply rel args))
  | _ => none

/-- Translate all rewrite rules in a language definition to MORK `SourceExecRule`s,
    filtering to only translatable rules. -/
def languageDefToSourceExecRules (lang : ILDL) : List SourceExecRule :=
  lang.rewrites.filterMap fun r =>
    if allPremisesTranslatable r.premises then
      some (rewriteRuleToSourceExecRule r)
    else none

/-- `bindingsToSubst` on a singleton. -/
theorem bindingsToSubst_singleton (x : String) (p : ILP) :
    bindingsToSubst [(x, p)] = [(x, morkPatternToAtom p)] := by
  simp [bindingsToSubst, List.map]

/-- `translateBindings` and `bindingsToSubst` agree. -/
theorem translateBindings_eq_bindingsToSubst (bs : ILBind) :
    translateBindings bs = bindingsToSubst bs := by
  simp [translateBindings, bindingsToSubst]

/-! ## mergeBindings ↔ matchAtom correspondence

These lemmas connect MeTTaIL's `mergeBindings` (Match.lean) to MORK's `matchAtom`
(Space.lean) under the `bindingsToSubst` translation. They enable automatic
derivation of `PremiseChain` witnesses from MeTTaIL reduction proofs.

The key structural parallel:
- `mergeBindings` checks `acc.find? (·.1 == name)` then adds or checks consistency
- `matchAtom (.var v) a` checks `σ.lookup v` then adds or checks consistency
- `bindingsToSubst` maps both to the same structure, preserving keys -/

/-- `bindingsToSubst` preserves lookup: if a key is absent in bindings,
    it's absent in the translated substitution. -/
theorem bindingsToSubst_lookup_none (bs : ILBind) (x : String)
    (h : bs.find? (·.1 == x) = none) :
    (bindingsToSubst bs).lookup x = none := by
  rw [← translateBindings_eq_bindingsToSubst, translateBindings_lookup, h]
  rfl

/-- `bindingsToSubst` preserves lookup: if a key maps to `p` in bindings,
    it maps to `morkPatternToAtom p` in the substitution. -/
theorem bindingsToSubst_lookup_some (bs : ILBind) (x : String) (p : ILP)
    (h : bs.find? (·.1 == x) = some (x, p)) :
    (bindingsToSubst bs).lookup x = some (morkPatternToAtom p) := by
  rw [← translateBindings_eq_bindingsToSubst, translateBindings_lookup, h]
  rfl

/-- `bindingsToSubst` preserves lookup (general): if a key maps to some pair
    in bindings, the second component translates. -/
theorem bindingsToSubst_lookup_some' (bs : ILBind) (x : String) (k : String) (p : ILP)
    (h : bs.find? (·.1 == x) = some (k, p)) :
    (bindingsToSubst bs).lookup x = some (morkPatternToAtom p) := by
  rw [← translateBindings_eq_bindingsToSubst, translateBindings_lookup, h]
  rfl

/-- New binding: `matchAtom` on `.var x` with no prior binding for `x`
    produces the same result as `mergeBindings` adding `(x, p)`. -/
theorem matchAtom_var_bindingsToSubst_new (bs : ILBind) (x : String) (p : ILP)
    (hnone : bs.find? (·.1 == x) = none) :
    matchAtom (bindingsToSubst bs) (.var x) (morkPatternToAtom p) =
      some (bindingsToSubst ((x, p) :: bs)) := by
  rw [matchAtom, bindingsToSubst_lookup_none bs x hnone]
  simp [bindingsToSubst]

/-- Existing consistent binding: `matchAtom` on `.var x` when `x` already maps
    to the same pattern preserves the substitution. -/
theorem matchAtom_var_bindingsToSubst_existing (bs : ILBind) (x : String) (p : ILP)
    (hsome : bs.find? (·.1 == x) = some (x, p)) :
    matchAtom (bindingsToSubst bs) (.var x) (morkPatternToAtom p) =
      some (bindingsToSubst bs) := by
  simp only [matchAtom, bindingsToSubst_lookup_some bs x p hsome, beq_self_eq_true, ite_true]

/-- Single-step correspondence: one step of `mergeBindings` (adding `(name, val)`)
    corresponds to `matchAtom` on `.var name` against `morkPatternToAtom val`.

    This is the crux lemma connecting MeTTaIL's binding merging to MORK's
    pattern matching at the granularity of a single variable. -/
theorem mergeBindings_step_matchAtom_correspond (bs : ILBind) (name : String) (val : ILP)
    (result : ILBind)
    (hmerge : (match bs.find? (·.1 == name) with
      | none => some ((name, val) :: bs)
      | some (_, existing) =>
          if existing == val then some bs else none) = some result) :
    matchAtom (bindingsToSubst bs) (.var name) (morkPatternToAtom val) =
      some (bindingsToSubst result) := by
  cases hf : bs.find? (·.1 == name) with
  | none =>
    rw [hf] at hmerge
    simp at hmerge
    rw [← hmerge]
    exact matchAtom_var_bindingsToSubst_new bs name val hf
  | some pair =>
    rw [hf] at hmerge
    obtain ⟨k, existing⟩ := pair
    simp only at hmerge
    split at hmerge
    · -- existing == val, so result = bs
      rename_i heq
      simp at hmerge
      rw [← hmerge]
      have heq' : existing = val := by
        rwa [beq_iff_eq] at heq
      have hlookup := bindingsToSubst_lookup_some' bs name k existing hf
      rw [matchAtom, hlookup]
      simp [heq', bindingsToSubst]
    · -- existing ≠ val, contradiction (none = some result)
      simp at hmerge

/-- Full `mergeBindings` → `matchAtomList` correspondence:
    if `mergeBindings bs newBindings = some result`, then MORK's `matchAtomList`
    on the corresponding `.var` patterns and translated atoms produces the
    same result under `bindingsToSubst`.

    This is the crux theorem enabling automatic derivation of `PremiseChain`
    witnesses: given a MeTTaIL binding merge, the MORK match is guaranteed
    to succeed with the corresponding substitution. -/
theorem mergeBindings_matchAtomList_correspond (bs : ILBind)
    (newBindings : List (String × ILP))
    (result : ILBind)
    (hmerge : ilMergeBindings bs newBindings = some result) :
    matchAtom.matchAtomList (bindingsToSubst bs)
      (newBindings.map (fun p => Atom.var p.1))
      (newBindings.map (fun p => morkPatternToAtom p.2)) =
      some (bindingsToSubst result) := by
  induction newBindings generalizing bs with
  | nil =>
    simp [ilMergeBindings, Mettapedia.OSLF.MeTTaIL.Match.mergeBindings] at hmerge
    simp [matchAtom.matchAtomList, hmerge]
  | cons entry rest ih =>
    obtain ⟨name, val⟩ := entry
    -- foldlM (a :: rest) = step >>= foldlM rest
    simp only [ilMergeBindings, Mettapedia.OSLF.MeTTaIL.Match.mergeBindings,
      List.foldlM_cons] at hmerge
    -- Extract the single step result
    simp only [List.map_cons, matchAtom.matchAtomList]
    cases hf : bs.find? (·.1 == name) with
    | none =>
      -- New binding: matchAtom produces ((name, atom) :: σ)
      rw [matchAtom_var_bindingsToSubst_new bs name val hf]
      -- mergeBindings step: some ((name, val) :: bs)
      simp only [hf] at hmerge
      exact ih ((name, val) :: bs) hmerge
    | some pair =>
      obtain ⟨k, existing⟩ := pair
      simp only [hf] at hmerge
      split at hmerge
      · -- existing == val: matchAtom returns some (bindingsToSubst bs)
        rename_i heq
        have heq' : existing = val := by rwa [beq_iff_eq] at heq
        subst heq'
        have hk : k = name := by
          have := List.find?_some hf; simp [BEq.beq] at this; exact this
        subst hk
        rw [matchAtom_var_bindingsToSubst_existing bs k existing hf]
        -- match some σ with | some σ' => f σ' | none => g  reduces to  f σ
        change matchAtom.matchAtomList (bindingsToSubst bs)
          (List.map (fun p => Atom.var p.1) rest)
          (List.map (fun p => morkPatternToAtom p.2) rest) = some (bindingsToSubst result)
        -- hmerge: do { let init ← some bs; foldlM ... init rest } = some result
        -- which simplifies to ilMergeBindings bs rest = some result
        have hmerge' : ilMergeBindings bs rest = some result := by
          simp only [ilMergeBindings, Mettapedia.OSLF.MeTTaIL.Match.mergeBindings] at hmerge ⊢
          exact hmerge
        exact ih bs hmerge'
      · -- existing ≠ val: contradiction
        simp at hmerge

/-! ## Freshness correspondence

The crux theorems connecting MeTTaIL's freshness semantics to MORK's `SourceGuard.freshness`.
MeTTaIL checks `isFresh x (applyBindings bs term)` while MORK checks
`isAtomFresh v (applySubst σ pat)`. These agree under `bindingsToSubst`. -/

private abbrev ilFreeVars := Mettapedia.OSLF.MeTTaIL.Substitution.freeVars
private abbrev ilIsFresh := Mettapedia.OSLF.MeTTaIL.Substitution.isFresh

/-- Free variables are preserved by `morkPatternToAtom` (for translatable patterns).
    MeTTaIL `freeVars p` = MORK `atomFreeVars (morkPatternToAtom p)`. -/
theorem morkPatternToAtom_freeVars (p : ILP) (h : morkTranslatable p = true) :
    atomFreeVars (morkPatternToAtom p) = ilFreeVars p := by
  revert h
  induction p using Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.inductionOn with
  | hbvar n =>
    intro _; simp [morkPatternToAtom, ilFreeVars,
      Mettapedia.OSLF.MeTTaIL.Substitution.freeVars, atomFreeVars]
  | hfvar x =>
    intro _; simp [morkPatternToAtom, ilFreeVars,
      Mettapedia.OSLF.MeTTaIL.Substitution.freeVars, atomFreeVars]
  | happly c args ih =>
    intro h
    simp only [morkTranslatable] at h
    simp only [morkPatternToAtom, ilFreeVars,
      Mettapedia.OSLF.MeTTaIL.Substitution.freeVars]
    simp only [atomFreeVars, atomFreeVars.atomFreeVarsList]
    congr 1
    induction args with
    | nil => rfl
    | cons a as ih_as =>
      simp only [morkTranslatableList] at h
      have ⟨ha, has⟩ : morkTranslatable a = true ∧ morkTranslatableList as = true := by
        revert h; cases morkTranslatable a <;> cases morkTranslatableList as <;> simp
      simp only [morkPatternToAtom.morkPatternToAtomList,
        atomFreeVars.atomFreeVarsList, List.flatMap_cons]
      have ha_mem : a ∈ a :: as := by simp
      rw [ih a ha_mem ha]
      simp only [List.nil_append]
      simpa using ih_as (fun q hq => ih q (List.mem_cons.mpr (.inr hq))) has
  | hlambda body ih =>
    intro h
    simp only [morkTranslatable] at h
    simp only [morkPatternToAtom, ilFreeVars,
      Mettapedia.OSLF.MeTTaIL.Substitution.freeVars]
    simp only [atomFreeVars, atomFreeVars.atomFreeVarsList]
    simp only [List.append_nil]
    exact ih h
  | hmultiLambda n body ih =>
    intro h
    simp only [morkTranslatable] at h
    simp only [morkPatternToAtom, ilFreeVars,
      Mettapedia.OSLF.MeTTaIL.Substitution.freeVars]
    simp only [atomFreeVars, atomFreeVars.atomFreeVarsList]
    simp only [List.append_nil]
    exact ih h
  | hsubst body repl _ _ =>
    intro h; simp [morkTranslatable] at h
  | hcollection ct elems rest ih =>
    intro h
    match rest with
    | some _ => simp [morkTranslatable] at h
    | none =>
      simp only [morkTranslatable] at h
      simp only [morkPatternToAtom, ilFreeVars,
        Mettapedia.OSLF.MeTTaIL.Substitution.freeVars]
      simp only [atomFreeVars, atomFreeVars.atomFreeVarsList]
      congr 1
      induction elems with
      | nil => rfl
      | cons a as ih_as =>
        simp only [morkTranslatableList] at h
        have ⟨ha, has⟩ : morkTranslatable a = true ∧ morkTranslatableList as = true := by
          revert h; cases morkTranslatable a <;> cases morkTranslatableList as <;> simp
        simp only [morkPatternToAtom.morkPatternToAtomList,
          atomFreeVars.atomFreeVarsList, List.flatMap_cons]
        have ha_mem : a ∈ a :: as := by simp
        rw [ih a ha_mem ha]
        simp only [List.nil_append]
        simpa using ih_as (fun q hq => ih q (List.mem_cons_of_mem _ hq)) has

/-- Freshness is preserved by `morkPatternToAtom`:
    `isFresh x p ↔ isAtomFresh x (morkPatternToAtom p)` for translatable `p`. -/
theorem isFresh_iff_isAtomFresh (x : String) (p : ILP) (h : morkTranslatable p = true) :
    ilIsFresh x p = isAtomFresh x (morkPatternToAtom p) := by
  simp only [ilIsFresh, Mettapedia.OSLF.MeTTaIL.Substitution.isFresh,
    isAtomFresh, morkPatternToAtom_freeVars p h]

/-- Main freshness correspondence: if MeTTaIL's freshness premise succeeds
    (bindings `bs` pass the freshness check), then MORK's `matchSourceGuard`
    with the translated guard also succeeds.

    Requires that both `fc.term` and `ilApplyBindings bs fc.term` are translatable.
    The first is a precondition on the rule; the second ensures the substituted
    term stays within MORK's executable fragment. -/
theorem freshness_premise_correspond
    {relEnv : ILRelEnv} {lang : ILDL}
    (bs : ILBind) (fc : Mettapedia.OSLF.MeTTaIL.Syntax.FreshnessCondition)
    (hfresh : bs ∈ ilPremiseStepWithEnv relEnv lang bs
      (Mettapedia.OSLF.MeTTaIL.Syntax.Premise.freshness fc))
    (htrans : morkTranslatable fc.term = true)
    (htrans_applied : morkTranslatable (ilApplyBindings bs fc.term) = true) :
    matchSourceGuard (bindingsToSubst bs)
      (.freshness fc.varName (morkPatternToAtom fc.term)) = true := by
  -- Extract resolution result and freshness check from MeTTaIL
  have ⟨x, hresolved, hfreshCheck⟩ :=
    Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv_freshness_check hfresh
  -- applySubst ↔ applyBindings correspondence
  have happly : applySubst (bindingsToSubst bs) (morkPatternToAtom fc.term) =
      morkPatternToAtom (ilApplyBindings bs fc.term) := by
    rw [← translateBindings_eq_bindingsToSubst]; exact applySubst_commutes bs fc.term htrans
  -- isFresh ↔ isAtomFresh on applied term
  have hfreshCorr : ilIsFresh x (ilApplyBindings bs fc.term) =
      isAtomFresh x (morkPatternToAtom (ilApplyBindings bs fc.term)) :=
    isFresh_iff_isAtomFresh x (ilApplyBindings bs fc.term) htrans_applied
  have hlookupSubst :
      (bindingsToSubst bs).lookup fc.varName =
        (Mettapedia.OSLF.MeTTaIL.Match.Bindings.lookup bs fc.varName).map
          morkPatternToAtom := by
    rw [← translateBindings_eq_bindingsToSubst, translateBindings_lookup]
    simp [Mettapedia.OSLF.MeTTaIL.Match.Bindings.lookup, Function.comp]
  cases hlookup : Mettapedia.OSLF.MeTTaIL.Match.Bindings.lookup bs fc.varName with
  | none =>
    have hlu : (bindingsToSubst bs).lookup fc.varName = none := by
      simpa [hlookup] using hlookupSubst
    have hx : x = fc.varName := by
      symm
      simpa [hlookup] using hresolved
    rw [matchSourceGuard, hlu, happly]
    simpa [hx] using (hfreshCorr.symm.trans hfreshCheck)
  | some p =>
    cases p with
    | fvar y =>
      have hlu : (bindingsToSubst bs).lookup fc.varName = some (.var y) := by
        simpa [hlookup, morkPatternToAtom] using hlookupSubst
      have hx : x = y := by
        symm
        simpa [hlookup] using hresolved
      rw [matchSourceGuard, hlu, happly]
      simpa [hx] using (hfreshCorr.symm.trans hfreshCheck)
    | bvar n =>
      have : False := by
        simpa [hlookup] using hresolved
      cases this
    | apply f args =>
      have : False := by
        simpa [hlookup] using hresolved
      cases this
    | lambda body =>
      have : False := by
        simpa [hlookup] using hresolved
      cases this
    | multiLambda n body =>
      have : False := by
        simpa [hlookup] using hresolved
      cases this
    | subst body repl =>
      have : False := by
        simpa [hlookup] using hresolved
      cases this
    | collection ct elems rest =>
      have : False := by
        simpa [hlookup] using hresolved
      cases this

/-! ## Workspace representation

The key predicate connecting MeTTaIL premise satisfaction to MORK source-factor
matching. For each `relationQuery` premise that succeeds (extending bindings
from `bs₀` to `bs`), the workspace must contain an atom that MORK's `matchAtom`
would match against, producing the corresponding substitution extension.

This is an explicit, honestly-scoped hypothesis — it makes the "workspace
faithfully represents the relation environment" assumption visible. -/

/-- The workspace contains a matching atom for every binding extension that
    a single `premiseStepWithEnv` call produces for a `relationQuery` premise.

    For non-`relationQuery` premises, this is vacuously true (they are not
    translatable and thus not part of the MORK source fragment). -/
def WorkspaceRepresentsPremise (relEnv : ILRelEnv) (lang : ILDL)
    (s : Space) (bs₀ : ILBind) (prem : ILPremise) : Prop :=
  match prem with
  | .relationQuery rel args =>
    ∀ bs ∈ ilPremiseStepWithEnv relEnv lang bs₀ prem,
      ∃ a ∈ s, matchAtom (bindingsToSubst bs₀)
        (morkPatternToAtom (.apply rel args)) a = some (bindingsToSubst bs)
  | _ => True

/-- Multi-premise workspace representation: at every step of the premise chain,
    the workspace represents the current premise under the current bindings.

    This threads through the foldl structure of `applyPremisesWithEnv`:
    at step `i`, the accumulated bindings from steps `0..i-1` serve as the
    "current bindings" for premise `i`. -/
def WorkspaceRepresentsPremises (relEnv : ILRelEnv) (lang : ILDL)
    (s : Space) (bs₀ : ILBind)
    (premises : List ILPremise) : Prop :=
  ∀ (i : Fin premises.length) (bs_mid : ILBind),
    bs_mid ∈ (premises.take i).foldl
      (fun acc prem => acc.flatMap fun b => ilPremiseStepWithEnv relEnv lang b prem)
      [bs₀] →
    WorkspaceRepresentsPremise relEnv lang s bs_mid premises[i]

/-! ## PremiseChain: step-by-step premise-witness correspondence

A `PremiseChain` inductively captures the step-by-step correspondence between
MeTTaIL premise evaluation (via `premiseStepWithEnv`) and MORK source-factor
matching (via `matchAtom`). Each step links a premise to a workspace witness atom
that MORK can match against. -/

/-- Extract atom from a `relationQuery` premise. For other premise kinds,
    returns a dummy atom (they are filtered out by `allPremisesTranslatable`). -/
def premiseToAtomTotal : ILPremise → Atom
  | .relationQuery rel args => morkPatternToAtom (.apply rel args)
  | _ => .symbol "⊥"

/-- `premiseToAtomTotal` for `relationQuery` matches `premiseToAtom`. -/
theorem premiseToAtomTotal_relationQuery (rel : String) (args : List ILP) :
    premiseToAtomTotal (.relationQuery rel args) = morkPatternToAtom (.apply rel args) := by
  simp [premiseToAtomTotal]

/-- A chain of premise-witness correspondences linking MeTTaIL bindings
    to MORK substitutions through a list of premises.

    The `guard` constructor handles premises (like freshness) that don't consume
    workspace atoms — they filter substitutions but don't add to the witness list. -/
inductive PremiseChain (relEnv : ILRelEnv) (lang : ILDL) (s : Space)
    : ILBind → List ILPremise → List Atom → ILBind → Prop where
  | nil : PremiseChain relEnv lang s bs [] [] bs
  | cons :
      {bs0 bs_mid bs_final : ILBind} →
      {prems : List ILPremise} → {witnesses : List Atom} →
      (prem : ILPremise) → (a : Atom) →
      a ∈ s →
      matchAtom (bindingsToSubst bs0) (premiseToAtomTotal prem) a =
        some (bindingsToSubst bs_mid) →
      bs_mid ∈ ilPremiseStepWithEnv relEnv lang bs0 prem →
      PremiseChain relEnv lang s bs_mid prems witnesses bs_final →
      PremiseChain relEnv lang s bs0 (prem :: prems) (a :: witnesses) bs_final
  | guard :
      {bs0 bs_final : ILBind} →
      {prems : List ILPremise} → {witnesses : List Atom} →
      (prem : ILPremise) →
      premiseToSourceFactor prem = none →
      bs0 ∈ ilPremiseStepWithEnv relEnv lang bs0 prem →
      PremiseChain relEnv lang s bs0 prems witnesses bs_final →
      PremiseChain relEnv lang s bs0 (prem :: prems) witnesses bs_final

/-- Subset-monotonicity of foldl-flatMap: if `xs ⊆ ys` then
    `foldl flatMap-step xs ⊆ foldl flatMap-step ys`. -/
private theorem foldl_flatMap_subset {α β : Type*} (f : α → β → List α) (steps : List β)
    {xs ys : List α} (h : ∀ a ∈ xs, a ∈ ys) :
    ∀ a ∈ steps.foldl (fun acc s => acc.flatMap (f · s)) xs,
      a ∈ steps.foldl (fun acc s => acc.flatMap (f · s)) ys := by
  induction steps generalizing xs ys with
  | nil => exact h
  | cons s rest ih =>
    simp only [List.foldl_cons]
    apply ih
    intro a ha
    rw [List.mem_flatMap] at ha ⊢
    obtain ⟨b, hb, hab⟩ := ha
    exact ⟨b, h b hb, hab⟩

/-- A `PremiseChain` implies the final bindings are reachable via `applyPremisesWithEnv`. -/
theorem premiseChain_implies_applyPremises {relEnv : ILRelEnv} {lang : ILDL}
    {s : Space} {bs0 bs : ILBind} {prems : List ILPremise} {witnesses : List Atom}
    (hchain : PremiseChain relEnv lang s bs0 prems witnesses bs) :
    bs ∈ ilApplyPremisesWithEnv relEnv lang prems bs0 := by
  induction hchain with
  | nil => simp [ilApplyPremisesWithEnv, Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv]
  | cons prem a ha_in ha_match hstep _htail ih =>
    simp only [ilApplyPremisesWithEnv, Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv,
      List.foldl_cons, List.flatMap_singleton] at ih ⊢
    exact foldl_flatMap_subset _ _ (fun b hb => by
      rw [List.mem_singleton.mp hb]; exact hstep) _ ih
  | guard prem _hnotfactor hstep _htail ih =>
    simp only [ilApplyPremisesWithEnv, Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv,
      List.foldl_cons, List.flatMap_singleton] at ih ⊢
    exact foldl_flatMap_subset _ _ (fun b hb => by
      rw [List.mem_singleton.mp hb]; exact hstep) _ ih

/-- `premisesToSourceFactors` on a cons list with translatable head. -/
theorem premisesToSourceFactors_cons_translatable (prem : ILPremise)
    (rest : List ILPremise) (f : SourceFactor) (hf : premiseToSourceFactor prem = some f) :
    premisesToSourceFactors (prem :: rest) = f :: premisesToSourceFactors rest := by
  simp [premisesToSourceFactors, List.filterMap, hf]

/-- Core lemma (auxiliary): `PremiseChain` implies membership in `matchSourceFactors.go`
    with an arbitrary initial consumed set. -/
private theorem premiseChain_matchSourceFactors_go_aux {relEnv : ILRelEnv} {lang : ILDL}
    {s : Space} {bs0 bs : ILBind} {prems : List ILPremise} {witnesses : List Atom}
    (hchain : PremiseChain relEnv lang s bs0 prems witnesses bs)
    (htrans : allPremisesTranslatable prems = true)
    (hnodup : witnesses.Nodup)
    (consumed : Finset Atom)
    (hwit_not_consumed : ∀ a ∈ witnesses, a ∉ consumed) :
    ∃ consumed', (bindingsToSubst bs, consumed') ∈
        matchSourceFactors.go s (premisesToSourceFactors prems)
          (bindingsToSubst bs0) consumed := by
  induction hchain generalizing consumed with
  | nil =>
    exact ⟨consumed, by simp [premisesToSourceFactors, matchSourceFactors.go]⟩
  | @cons bs0' bs_mid' bs_final' prems' witnesses' prem a ha_in ha_match hstep htail ih =>
    rw [List.nodup_cons] at hnodup
    obtain ⟨ha_notin, hnodup_rest⟩ := hnodup
    have htrans_head : (premiseToSourceFactor prem).isSome = true := by
      simp [allPremisesTranslatable, List.all_cons] at htrans; exact htrans.1
    have htrans_rest : allPremisesTranslatable prems' = true := by
      simp [allPremisesTranslatable, List.all_cons] at htrans
      exact List.all_eq_true.mpr htrans.2
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp htrans_head
    rw [premisesToSourceFactors_cons_translatable prem prems' f hf]
    simp only [matchSourceFactors.go]
    -- Factor f matches witness a in s \ consumed
    have hmatch_factor : (bindingsToSubst bs_mid', a) ∈
        matchSourceFactor (bindingsToSubst bs0') (s \ consumed) f := by
      cases prem with
      | relationQuery rel args =>
        simp [premiseToSourceFactor] at hf; rw [← hf]
        simp only [matchSourceFactor, matchOneInSpace, List.mem_filterMap]
        exact ⟨a, Finset.mem_toList.mpr (Finset.mem_sdiff.mpr
          ⟨ha_in, hwit_not_consumed a List.mem_cons_self⟩),
          by simp [premiseToAtomTotal] at ha_match; simp [ha_match]⟩
      | _ => simp [premiseToSourceFactor] at hf
    -- Recurse with consumed ∪ {a}
    have ⟨c', hc'⟩ := ih htrans_rest hnodup_rest (consumed ∪ {a}) fun a' ha' => by
      simp only [Finset.mem_union, Finset.mem_singleton, not_or]
      exact ⟨hwit_not_consumed a' (List.mem_cons_of_mem a ha'),
             fun h => ha_notin (h ▸ ha')⟩
    exact ⟨c', List.mem_flatMap.mpr ⟨(bindingsToSubst bs_mid', a), hmatch_factor, hc'⟩⟩
  | guard prem hnotfactor _hstep _htail ih =>
    exfalso
    have hhead : (premiseToSourceFactor prem).isSome = true := by
      simp [allPremisesTranslatable, List.all_cons] at htrans
      exact htrans.1
    rw [hnotfactor] at hhead; simp at hhead

/-- Core lemma: `PremiseChain` implies membership in `matchSourceFactors`. -/
theorem premiseChain_matchSourceFactors {relEnv : ILRelEnv} {lang : ILDL}
    {s : Space} {bs0 bs : ILBind} {prems : List ILPremise} {witnesses : List Atom}
    (hchain : PremiseChain relEnv lang s bs0 prems witnesses bs)
    (htrans : allPremisesTranslatable prems = true)
    (hnodup : witnesses.Nodup) :
    ∃ consumed, (bindingsToSubst bs, consumed) ∈
        matchSourceFactors (bindingsToSubst bs0) s (premisesToSourceFactors prems) := by
  have ⟨c', hc'⟩ := premiseChain_matchSourceFactors_go_aux hchain htrans hnodup ∅ (by simp)
  exact ⟨c', by simp [matchSourceFactors]; exact hc'⟩

/-! ### Guarded PremiseChain → matchSourceFactors + matchSourceGuards

The extended version handles premise lists containing both `relationQuery` (source
factors) and `freshness` (source guards). The key invariant:
- `cons` advances `matchSourceFactors.go` (same as non-guarded version)
- `guard` leaves `matchSourceFactors.go` unchanged but collects a guard satisfaction -/

private theorem premisesToSourceFactorsExt_cons_relationQuery (rel : String)
    (args : List ILP) (rest : List ILPremise) :
    premisesToSourceFactorsExt (.relationQuery rel args :: rest) =
      .btm (morkPatternToAtom (.apply rel args)) :: premisesToSourceFactorsExt rest := by
  simp [premisesToSourceFactorsExt, List.filterMap_cons, premiseToFactorOrGuard]

private theorem premisesToSourceGuards_cons_relationQuery (rel : String)
    (args : List ILP) (rest : List ILPremise) :
    premisesToSourceGuards (.relationQuery rel args :: rest) =
      premisesToSourceGuards rest := by
  simp [premisesToSourceGuards, List.filterMap_cons, premiseToFactorOrGuard]

private theorem premisesToSourceFactorsExt_cons_freshness
    (fc : Mettapedia.OSLF.MeTTaIL.Syntax.FreshnessCondition) (rest : List ILPremise) :
    premisesToSourceFactorsExt (.freshness fc :: rest) =
      premisesToSourceFactorsExt rest := by
  simp [premisesToSourceFactorsExt, List.filterMap_cons, premiseToFactorOrGuard]

private theorem premisesToSourceGuards_cons_freshness
    (fc : Mettapedia.OSLF.MeTTaIL.Syntax.FreshnessCondition) (rest : List ILPremise) :
    premisesToSourceGuards (.freshness fc :: rest) =
      .freshness fc.varName (morkPatternToAtom fc.term) :: premisesToSourceGuards rest := by
  simp [premisesToSourceGuards, List.filterMap_cons, premiseToFactorOrGuard]

/-- Core lemma (ext): `PremiseChain` implies membership in
    `matchSourceFactors.go` for the extended factor list.

    Handles both `cons` and `guard` constructors of `PremiseChain`.
    Freshness premises produce no factors (skipped in `matchSourceFactors.go`)
    and don't change bindings. Guard satisfaction is NOT proven here —
    it is provided as a separate hypothesis in the bridge theorem. -/
private theorem premiseChain_matchSourceFactorsExt_go_aux {relEnv : ILRelEnv} {lang : ILDL}
    {s : Space} {bs0 bs : ILBind} {prems : List ILPremise} {witnesses : List Atom}
    (hchain : PremiseChain relEnv lang s bs0 prems witnesses bs)
    (htrans : allPremisesTranslatableExt prems = true)
    (hnodup : witnesses.Nodup)
    (consumed : Finset Atom)
    (hwit_not_consumed : ∀ a ∈ witnesses, a ∉ consumed) :
    ∃ consumed', (bindingsToSubst bs, consumed') ∈
        matchSourceFactors.go s (premisesToSourceFactorsExt prems)
          (bindingsToSubst bs0) consumed := by
  induction hchain generalizing consumed with
  | nil =>
    exact ⟨consumed, by simp [premisesToSourceFactorsExt, matchSourceFactors.go]⟩
  | @cons bs0' bs_mid' bs_final' prems' witnesses' prem a ha_in ha_match hstep htail ih =>
    rw [List.nodup_cons] at hnodup
    obtain ⟨ha_notin, hnodup_rest⟩ := hnodup
    have htrans_rest : allPremisesTranslatableExt prems' = true := by
      simp only [allPremisesTranslatableExt, List.all_eq_true] at htrans ⊢
      exact fun q hq => htrans q (List.mem_cons.mpr (.inr hq))
    cases prem with
    | relationQuery rel args =>
      rw [premisesToSourceFactorsExt_cons_relationQuery]
      simp only [matchSourceFactors.go]
      have hmatch_factor : (bindingsToSubst bs_mid', a) ∈
          matchSourceFactor (bindingsToSubst bs0') (s \ consumed)
            (.btm (morkPatternToAtom (.apply rel args))) := by
        simp only [matchSourceFactor, matchOneInSpace, List.mem_filterMap]
        exact ⟨a, Finset.mem_toList.mpr (Finset.mem_sdiff.mpr
          ⟨ha_in, hwit_not_consumed a List.mem_cons_self⟩),
          by simp [premiseToAtomTotal] at ha_match; simp [ha_match]⟩
      have ⟨c', hc'⟩ := ih htrans_rest hnodup_rest (consumed ∪ {a})
        (fun a' ha' => by
          simp only [Finset.mem_union, Finset.mem_singleton, not_or]
          exact ⟨hwit_not_consumed a' (List.mem_cons_of_mem a ha'),
                 fun h => ha_notin (h ▸ ha')⟩)
      exact ⟨c', List.mem_flatMap.mpr ⟨(bindingsToSubst bs_mid', a), hmatch_factor, hc'⟩⟩
    | freshness fc =>
      -- Freshness in cons: bindings unchanged, factor list skips this premise
      rw [premisesToSourceFactorsExt_cons_freshness]
      have hbs_eq : bs_mid' = bs0' :=
        Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv_freshness_mem hstep
      rw [hbs_eq] at ih htail
      exact ih htrans_rest hnodup_rest consumed
        (fun a' ha' => hwit_not_consumed a' (List.mem_cons_of_mem a ha'))
    | congruence _ _ =>
      simp [allPremisesTranslatableExt, List.all_cons, premiseToFactorOrGuard] at htrans
  | @guard bs0' bs_final' prems' witnesses' prem hnotfactor hstep htail ih =>
    have htrans_rest : allPremisesTranslatableExt prems' = true := by
      simp only [allPremisesTranslatableExt, List.all_eq_true] at htrans ⊢
      exact fun q hq => htrans q (List.mem_cons.mpr (.inr hq))
    cases prem with
    | relationQuery rel args =>
      simp [premiseToSourceFactor] at hnotfactor
    | congruence _ _ =>
      simp [allPremisesTranslatableExt, List.all_cons, premiseToFactorOrGuard] at htrans
    | freshness fc =>
      rw [premisesToSourceFactorsExt_cons_freshness]
      exact ih htrans_rest hnodup consumed hwit_not_consumed

/-- Core lemma (ext): `PremiseChain` implies membership in `matchSourceFactors`
    for the extended factor list. -/
theorem premiseChain_matchSourceFactorsExt {relEnv : ILRelEnv} {lang : ILDL}
    {s : Space} {bs0 bs : ILBind} {prems : List ILPremise} {witnesses : List Atom}
    (hchain : PremiseChain relEnv lang s bs0 prems witnesses bs)
    (htrans : allPremisesTranslatableExt prems = true)
    (hnodup : witnesses.Nodup) :
    ∃ consumed, (bindingsToSubst bs, consumed) ∈
        matchSourceFactors (bindingsToSubst bs0) s (premisesToSourceFactorsExt prems) := by
  have ⟨c', hc'⟩ := premiseChain_matchSourceFactorsExt_go_aux
    hchain htrans hnodup ∅ (by simp)
  exact ⟨c', by simp [matchSourceFactors]; exact hc'⟩

/-! ## Per-rule source bridge theorems -/

/-- Bridge for rules with `fvar` LHS and zero premises — connects
    `DeclReducesWithPremises.topRule` to `fireSourceRule`.
    This is a strengthening of `declReduces_topRule_fvar_mork_fire`
    that uses `fireSourceRule` instead of `fireRule` and works with
    an arbitrary workspace (not just `patternToSpace p`). -/
theorem declReducesWithPremises_noPremise_fvar_mork_fireSourceRule
    (p q : ILP) (x : String)
    (r : ILRRule) (relEnv : ILRelEnv) (lang : ILDL)
    (hlhs : r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x)
    (htrans_rhs : morkTranslatable r.right = true)
    (hnoprem : r.premises = [])
    (bs : ILBind) (hbs : bs ∈ ilMatchPattern r.left p)
    (hrhs : ilApplyBindings bs r.right = q)
    (hground : isGroundAtom (morkPatternToAtom q) = true)
    (s : Space)
    (hp_in : morkPatternToAtom p ∈ s) :
    applySinks s (bindingsToSubst bs) (rewriteRuleToSourceExecRule r).tmpl ∈
        fireSourceRule s (rewriteRuleToSourceExecRule r) := by
  -- bs = [(x, p)]
  rw [hlhs] at hbs
  have hbs_eq := ilMatchPattern_fvar_unique x p bs hbs
  -- fireSourceRule with no guards reduces to matchInputSpec → applySinks
  rw [fireSourceRule_no_guards _ _ (rewriteRuleToSourceExecRule_guards r)]
  simp only [rewriteRuleToSourceExecRule, matchInputSpec, hnoprem,
    premisesToSourceFactors, List.filterMap]
  -- matchSourceFactors with just the LHS factor
  rw [List.mem_map]
  -- Witness: σ = [(x, morkPatternToAtom p)], consumed = {morkPatternToAtom p}
  refine ⟨(bindingsToSubst bs, {morkPatternToAtom p}), ?_, ?_⟩
  · -- Show (σ, consumed) ∈ matchSourceFactors [] s [btm (.var x)]
    simp only [matchSourceFactors, hlhs, morkPatternToAtom]
    simp only [matchSourceFactors.go, matchSourceFactor, matchOneInSpace]
    apply List.mem_flatMap.mpr
    refine ⟨([(x, morkPatternToAtom p)], morkPatternToAtom p), ?_, ?_⟩
    · -- matchAtom [] (.var x) (morkPatternToAtom p) = some [...]
      simp only [List.mem_filterMap]
      refine ⟨morkPatternToAtom p, ?_, ?_⟩
      · exact Finset.mem_toList.mpr (by simp [hp_in])
      · simp [matchAtom_var_fresh]
    · -- go [] σ₁ consumed = [(σ₁, consumed)]
      simp only [matchSourceFactors.go, List.mem_singleton]
      rw [hbs_eq]; simp [bindingsToSubst]
  · -- Show applySinks s σ tmpl = applySinks s (bindingsToSubst bs) tmpl
    rfl

/-- Bridge for rules with `fvar` LHS and exactly one `relationQuery` premise.
    This is the core single-premise semantic bridge.

    The workspace must contain:
    1. The input pattern `morkPatternToAtom p` (for the LHS match)
    2. An atom that matches the premise pattern (for the premise factor match)

    The `WorkspaceRepresentsPremise` hypothesis ensures (2). The `hdisjoint`
    hypothesis ensures the premise atom is distinct from the LHS atom (so it
    won't be filtered out by consumed-atom tracking). -/
theorem declReducesWithPremises_singlePremise_fvar_mork_fireSourceRule
    (p q : ILP) (x : String)
    (r : ILRRule) (relEnv : ILRelEnv) (lang : ILDL)
    (rel : String) (args : List ILP)
    (hlhs : r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x)
    (htrans_rhs : morkTranslatable r.right = true)
    (hprem : r.premises = [Mettapedia.OSLF.MeTTaIL.Syntax.Premise.relationQuery rel args])
    (bs0 : ILBind) (hbs0 : bs0 ∈ ilMatchPattern r.left p)
    (bs : ILBind)
    (hbs : bs ∈ ilApplyPremisesWithEnv relEnv lang r.premises bs0)
    (hrhs : ilApplyBindings bs r.right = q)
    (hground : isGroundAtom (morkPatternToAtom q) = true)
    (s : Space)
    (hp_in : morkPatternToAtom p ∈ s)
    -- Workspace faithfulness: there exists a matching atom for the premise
    (a_prem : Atom)
    (ha_in : a_prem ∈ s)
    (ha_ne : a_prem ≠ morkPatternToAtom p)
    (ha_match : matchAtom (bindingsToSubst bs0)
        (morkPatternToAtom (.apply rel args)) a_prem = some (bindingsToSubst bs)) :
    applySinks s (bindingsToSubst bs) (rewriteRuleToSourceExecRule r).tmpl ∈
        fireSourceRule s (rewriteRuleToSourceExecRule r) := by
  -- bs0 = [(x, p)]
  rw [hlhs] at hbs0
  have hbs0_eq := ilMatchPattern_fvar_unique x p bs0 hbs0
  -- Unfold fireSourceRule (no guards)
  rw [fireSourceRule_no_guards _ _ (rewriteRuleToSourceExecRule_guards r)]
  simp only [rewriteRuleToSourceExecRule, matchInputSpec, hprem,
    premisesToSourceFactors, List.filterMap, premiseToSourceFactor]
  rw [List.mem_map]
  -- We need (bindingsToSubst bs, consumed) ∈ matchSourceFactors [] s [btm (.var x), btm premAtom]
  refine ⟨(bindingsToSubst bs, {morkPatternToAtom p, a_prem}), ?_, ?_⟩
  · -- Show the pair is in matchSourceFactors
    simp only [matchSourceFactors, hlhs, morkPatternToAtom]
    simp only [matchSourceFactors.go, matchSourceFactor, matchOneInSpace]
    -- First factor: btm (.var x) → match against morkPatternToAtom p
    apply List.mem_flatMap.mpr
    refine ⟨([(x, morkPatternToAtom p)], morkPatternToAtom p), ?_, ?_⟩
    · simp only [List.mem_filterMap]
      refine ⟨morkPatternToAtom p, ?_, ?_⟩
      · exact Finset.mem_toList.mpr (by simp [hp_in])
      · simp [matchAtom_var_fresh]
    · -- Second factor: btm premAtom → match against a_prem in s \ {lhs_atom}
      simp only [matchSourceFactors.go, matchSourceFactor, matchOneInSpace]
      apply List.mem_flatMap.mpr
      refine ⟨(bindingsToSubst bs, a_prem), ?_, ?_⟩
      · simp only [List.mem_filterMap]
        refine ⟨a_prem, ?_, ?_⟩
        · -- a_prem ∈ (s \ {morkPatternToAtom p}).toList
          exact Finset.mem_toList.mpr (Finset.mem_sdiff.mpr
            ⟨ha_in, by simp [ha_ne]⟩)
        · -- matchAtom succeeds
          rw [hbs0_eq, bindingsToSubst_singleton] at ha_match
          simpa using ha_match
      · -- go [] σ_final consumed = [(σ_final, consumed)]
        simp only [List.mem_singleton, Prod.mk.injEq]
        exact ⟨trivial, by ext a; simp [Finset.mem_insert, Finset.mem_singleton]⟩
  · rfl

/-! ## Multi-premise bridge

Generalizes the single-premise bridge to N `relationQuery` premises via
`PremiseChain`. The workspace representation is captured by the chain itself:
each step provides a witness atom that MORK's `matchAtom` matches against. -/

/-- Multi-premise per-rule bridge: if we have a `PremiseChain` linking
    MeTTaIL bindings to MORK substitutions through all premises, then
    `fireSourceRule` produces the corresponding result.

    This is the N-premise generalization of
    `declReducesWithPremises_singlePremise_fvar_mork_fireSourceRule`. -/
theorem declReducesWithPremises_multiPremise_fvar_mork_fireSourceRule
    (p q : ILP) (x : String) (r : ILRRule) (relEnv : ILRelEnv) (lang : ILDL)
    (hlhs : r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x)
    (htrans_rhs : morkTranslatable r.right = true)
    (htrans_prem : allPremisesTranslatable r.premises = true)
    (bs0 : ILBind) (hbs0 : bs0 ∈ ilMatchPattern r.left p)
    (bs : ILBind)
    (hrhs : ilApplyBindings bs r.right = q)
    (hground : isGroundAtom (morkPatternToAtom q) = true)
    (s : Space) (hp_in : morkPatternToAtom p ∈ s)
    -- PremiseChain witness
    (witnesses : List Atom)
    (hchain : PremiseChain relEnv lang s bs0 r.premises witnesses bs)
    (hnodup : witnesses.Nodup)
    (hwit_ne_p : ∀ a ∈ witnesses, a ≠ morkPatternToAtom p) :
    applySinks s (bindingsToSubst bs) (rewriteRuleToSourceExecRule r).tmpl ∈
        fireSourceRule s (rewriteRuleToSourceExecRule r) := by
  -- bs0 = [(x, p)]
  rw [hlhs] at hbs0
  have hbs0_eq := ilMatchPattern_fvar_unique x p bs0 hbs0
  -- fireSourceRule with no guards = (matchInputSpec []).map (fun (σ, _) => applySinks ...)
  rw [fireSourceRule_no_guards _ _ (rewriteRuleToSourceExecRule_guards r)]
  simp only [rewriteRuleToSourceExecRule, matchInputSpec]
  rw [List.mem_map]
  -- matchSourceFactors [] s (lhsFactor :: premiseFactors)
  -- = go (btm (.var x) :: premisesToSourceFactors r.premises) [] ∅
  -- Step 1: btm (.var x) matches morkPatternToAtom p → σ₁ = [(x, morkPatternToAtom p)]
  -- Step 2: premiseFactors matched by PremiseChain from σ₁ with consumed = {morkPatternToAtom p}
  -- Use premiseChain_matchSourceFactors_go_aux for step 2
  have hchain' : PremiseChain relEnv lang s [(x, p)] r.premises witnesses bs := by
    rw [hbs0_eq] at hchain; exact hchain
  have ⟨c_prem, hc_prem⟩ := premiseChain_matchSourceFactors_go_aux
    hchain' htrans_prem hnodup {morkPatternToAtom p}
    (fun a ha => by simp [hwit_ne_p a ha])
  -- Now compose with the LHS factor match
  -- go (btm (.var x) :: premFactors) [] ∅ flatMaps through the LHS match first
  refine ⟨(bindingsToSubst bs, c_prem), ?_, rfl⟩
  simp only [matchSourceFactors, hlhs, morkPatternToAtom, matchSourceFactors.go,
    matchSourceFactor, matchOneInSpace]
  apply List.mem_flatMap.mpr
  refine ⟨([(x, morkPatternToAtom p)], morkPatternToAtom p), ?_, ?_⟩
  · simp only [List.mem_filterMap]
    exact ⟨morkPatternToAtom p, Finset.mem_toList.mpr (by simp [hp_in]),
           by simp [matchAtom_var_fresh]⟩
  · -- Need: (bindingsToSubst bs, c_prem) ∈ go premFactors [(x, morkPatternToAtom p)] {morkPatternToAtom p}
    convert hc_prem using 2

/-! ## Multi-step closure

`DeclReducesWithPremisesStar` is the reflexive-transitive closure of
`DeclReducesWithPremises`, representing multi-step MeTTaIL reductions
where each step may use `relationQuery` premises. -/

/-- Multi-step reduction using `DeclReducesWithPremises`. -/
abbrev DeclReducesWithPremisesStar (relEnv : ILRelEnv) (lang : ILDL) :=
  ProcessCalculi.RTClosureProp
    (Mettapedia.OSLF.MeTTaIL.DeclReducesPremises.DeclReducesWithPremises relEnv lang)

/-- Single step → multi-step embedding. -/
theorem declReducesStar_single {relEnv : ILRelEnv} {lang : ILDL} {p q : ILP}
    (h : Mettapedia.OSLF.MeTTaIL.DeclReducesPremises.DeclReducesWithPremises relEnv lang p q) :
    DeclReducesWithPremisesStar relEnv lang p q :=
  ProcessCalculi.RTClosureProp.single h

/-- Transitivity for multi-step reductions. -/
theorem declReducesStar_trans {relEnv : ILRelEnv} {lang : ILDL} {p q r : ILP}
    (h1 : DeclReducesWithPremisesStar relEnv lang p q)
    (h2 : DeclReducesWithPremisesStar relEnv lang q r) :
    DeclReducesWithPremisesStar relEnv lang p r :=
  ProcessCalculi.RTClosureProp.trans h1 h2

/-! ## Extended bridge (mixed relationQuery + freshness premises)

The ext bridge uses `rewriteRuleToSourceExecRuleExt` (which populates guards)
and `premiseChain_matchSourceFactorsExt` (which handles the `guard` constructor).
Guard satisfaction at the final substitution is provided as a hypothesis — the
MeTTaIL-to-MORK freshness correspondence guarantees guards pass at the point
they fire, but `fireSourceRule` checks guards at the FINAL substitution. For
rules where guard variables are fully bound by earlier factors (the typical
case), the user can easily discharge this hypothesis. -/

/-- Translate all rewrite rules in a language definition to MORK `SourceExecRule`s
    using the extended translator (includes freshness guards). -/
def languageDefToSourceExecRulesExt (lang : ILDL) : List SourceExecRule :=
  lang.rewrites.filterMap fun r =>
    if allPremisesTranslatableExt r.premises then
      some (rewriteRuleToSourceExecRuleExt r)
    else none

/-- Multi-premise per-rule ext bridge: if we have a `PremiseChain` linking
    MeTTaIL bindings to MORK substitutions through all premises (including
    freshness guards), and the guards pass at the final substitution, then
    `fireSourceRule` produces the corresponding result. -/
theorem declReducesWithPremises_multiPremise_fvar_mork_fireSourceRuleExt
    (p q : ILP) (x : String) (r : ILRRule) (relEnv : ILRelEnv) (lang : ILDL)
    (hlhs : r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x)
    (htrans_rhs : morkTranslatable r.right = true)
    (htrans_prem : allPremisesTranslatableExt r.premises = true)
    (bs0 : ILBind) (hbs0 : bs0 ∈ ilMatchPattern r.left p)
    (bs : ILBind)
    (hrhs : ilApplyBindings bs r.right = q)
    (hground : isGroundAtom (morkPatternToAtom q) = true)
    (s : Space) (hp_in : morkPatternToAtom p ∈ s)
    (witnesses : List Atom)
    (hchain : PremiseChain relEnv lang s bs0 r.premises witnesses bs)
    (hnodup : witnesses.Nodup)
    (hwit_ne_p : ∀ a ∈ witnesses, a ≠ morkPatternToAtom p)
    -- Guard satisfaction at the final substitution
    (hguards : matchSourceGuards (bindingsToSubst bs)
        (premisesToSourceGuards r.premises) = true) :
    applySinks s (bindingsToSubst bs) (rewriteRuleToSourceExecRuleExt r).tmpl ∈
        fireSourceRule s (rewriteRuleToSourceExecRuleExt r) := by
  rw [hlhs] at hbs0
  have hbs0_eq := ilMatchPattern_fvar_unique x p bs0 hbs0
  simp only [fireSourceRule, rewriteRuleToSourceExecRuleExt, matchInputSpec]
  rw [List.mem_map]
  -- Show (bindingsToSubst bs, consumed) passes filter and produces the result
  have hchain' : PremiseChain relEnv lang s [(x, p)] r.premises witnesses bs := by
    rw [hbs0_eq] at hchain; exact hchain
  have ⟨c_prem, hc_prem⟩ := premiseChain_matchSourceFactorsExt_go_aux
    hchain' htrans_prem hnodup {morkPatternToAtom p}
    (fun a ha => by simp [hwit_ne_p a ha])
  -- The pair (σ, consumed) passes the guard filter
  refine ⟨(bindingsToSubst bs, c_prem), ?_, rfl⟩
  simp only [List.mem_filter]
  constructor
  · -- Membership in matchInputSpec
    simp only [matchSourceFactors, hlhs, morkPatternToAtom, matchSourceFactors.go,
      matchSourceFactor, matchOneInSpace]
    apply List.mem_flatMap.mpr
    refine ⟨([(x, morkPatternToAtom p)], morkPatternToAtom p), ?_, ?_⟩
    · simp only [List.mem_filterMap]
      exact ⟨morkPatternToAtom p, Finset.mem_toList.mpr (by simp [hp_in]),
             by simp [matchAtom_var_fresh]⟩
    · convert hc_prem using 2
  · -- Guards pass
    exact hguards

/-! ## Canary -/

section Canaries
#check @morkTranslatable
#check @translateBindings
#check @patternToSpace
#check @languageDefToExecRules
#check @applySubst_commutes
#check @declReduces_topRule_fvar_mork_fire
#check @rewriteRuleToSourceExecRule
#check @premisesToSourceFactors_length
#check @bindingsToSubst
#check @languageDefToSourceExecRules
#check @languageDefToSourceExecRulesExt
#check @WorkspaceRepresentsPremise
#check @WorkspaceRepresentsPremises
#check @premiseChain_matchSourceFactorsExt
#check @declReducesWithPremises_multiPremise_fvar_mork_fireSourceRuleExt
end Canaries

end Mettapedia.Languages.ProcessCalculi.MORK
