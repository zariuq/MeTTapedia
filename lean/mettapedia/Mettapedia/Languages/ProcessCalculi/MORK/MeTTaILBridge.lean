import Mettapedia.Languages.ProcessCalculi.MORK.ThreePhaseExec
import Mettapedia.OSLF.MeTTaIL.DeclReduces

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

open Mettapedia.OSLF.MeTTaCore (Atom)

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

/-! ## Full Bridge Theorem (restricted to MORK-compatible reductions) -/

/-- **Bridge theorem** for `DeclReduces` reductions within MORK's execution scope.

    Preconditions:
    1. `p` is not a collection (rules out `congElem` — MORK's flat Space cannot
       express sub-collection rewriting as a single exec-rule firing)
    2. Every applicable rule has `r.left = .fvar x` for some `x`
    3. Every applicable rule's RHS is `morkTranslatable`
    4. The result `q` has a ground atom translation -/
theorem declReduces_implies_mork_fire (lang : ILDL) (p q : ILP)
    (h : Mettapedia.OSLF.MeTTaIL.DeclReductions.DeclReduces lang p q)
    (hnotcollection : ∀ ct elems rest,
        p ≠ Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.collection ct elems rest)
    (hlhs : ∀ r ∈ lang.rewrites, r.premises = [] →
        ∃ x, r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x)
    (htrans : ∀ r ∈ lang.rewrites, r.premises = [] → morkTranslatable r.right = true)
    (hground : isGroundAtom (morkPatternToAtom q) = true) :
    ∃ r ∈ languageDefToExecRules lang,
      patternToSpace q ∈ fireRule (patternToSpace p) r := by
  cases h with
  | topRule r hr hrprem bs hbs hrhs =>
    obtain ⟨x, hlhs_x⟩ := hlhs r hr hrprem
    exact ⟨rewriteRuleToExecRule r,
           by simp only [languageDefToExecRules, List.mem_filterMap]; exact ⟨r, hr, by simp [hrprem]⟩,
           declReduces_topRule_fvar_mork_fire p q x r hlhs_x
             (htrans r hr hrprem) bs hbs hrhs hground⟩
  | congElem hct i hi r hr hrprem bs hbs hrhs =>
    -- p = .collection ct elems rest, contradicting hnotcollection
    exact absurd rfl (hnotcollection _ _ _)

/-! ## Canary -/

section Canaries
#check @morkPatternToAtom
#check @morkTranslatable
#check @translateBindings
#check @patternToSpace
#check @languageDefToExecRules
#check @applySubst_commutes
#check @declReduces_topRule_fvar_mork_fire
#check @declReduces_implies_mork_fire
end Canaries

end Mettapedia.Languages.ProcessCalculi.MORK
