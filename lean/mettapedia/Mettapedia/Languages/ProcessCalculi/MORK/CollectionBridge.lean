import Mettapedia.Languages.ProcessCalculi.MORK.AtomZipper

/-!
# MORK Collection Congruence Bridge

Proves that MeTTaIL's `congElem` reduction (rewriting one element inside a collection)
corresponds to a MORK-side space update via a principled zipper/lens factorization.

## Architecture

The bridge is organized in layers, with the **zipper-based theorem** as the primary
congruence surface:

### Structural infrastructure (Layers A-B)
- **Layer A**: Translation commutation — `morkPatternToAtomList` commutes with `List.set`
- **Layer B**: Ground atom self-matching — `matchAtom σ a a = some σ` for ground `a`

### Operational core (Layer C)
- **Layer C**: Ad-hoc collection-replace exec rule + `fireRule` proof

### Congruence theorems (Layers D-F)
- **Layer D** (primary): `congElem_implies_mork_zipper_fire` — the canonical congruence
  theorem. Proves that collection element replacement factors through `LensRel`
  (AtomZipper-based focused sub-expression update) AND that a MORK exec rule fires.
- **Layer E**: `congElem_implies_mork_fire` — semantic-only view. Proves exec rule
  firing without the structural lens factorization.
- **Layer F**: `declReduces_implies_mork_fire_full` — full `DeclReduces` bridge handling
  both `topRule` and `congElem`.

### Source-aware bridges (Layers G-H)
- **Layer G**: `collectionReplaceSourceRule` — source-level encoding of collection
  replacement. `languageDefToSourceExecRulesWithCongr` extends the base source-rule
  set with this congruence rule.
- **Layer H**: `DeclReducesWithPremises` → `fireSourceRule` bridges for single-premise,
  multi-premise, multi-step, and ext (mixed relationQuery + freshness) variants. All
  handle both `topRule` and `congElem` via the extended rule set.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.OSLF.MeTTaIL.Syntax

private abbrev ILP := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
private abbrev ILCT := Mettapedia.OSLF.MeTTaIL.Syntax.CollType

/-! ## Layer A: Translation commutation with List.set -/

/-- `morkPatternToAtomList` is `List.map morkPatternToAtom`. -/
theorem morkPatternToAtomList_eq_map (elems : List ILP) :
    morkPatternToAtom.morkPatternToAtomList elems = elems.map morkPatternToAtom := by
  induction elems with
  | nil => rfl
  | cons p ps ih =>
    simp only [morkPatternToAtom.morkPatternToAtomList, List.map_cons, ih]

/-- `morkPatternToAtomList` commutes with `List.set`. -/
theorem morkPatternToAtomList_set (elems : List ILP) (i : Nat) (q' : ILP) :
    morkPatternToAtom.morkPatternToAtomList (elems.set i q') =
    (morkPatternToAtom.morkPatternToAtomList elems).set i (morkPatternToAtom q') := by
  rw [morkPatternToAtomList_eq_map, morkPatternToAtomList_eq_map, List.map_set]

/-- Translating a collection with `elems.set i q'` equals replacing the i-th element
    in the translated atom list. -/
theorem morkPatternToAtom_collection_set (ct : ILCT) (elems : List ILP)
    (i : Nat) (q' : ILP) (rest : Option String) :
    morkPatternToAtom (.collection ct (elems.set i q') rest) =
    .expression (.symbol (morkCollTypeSymbol ct) ::
      (morkPatternToAtom.morkPatternToAtomList elems).set i (morkPatternToAtom q')) := by
  simp only [morkPatternToAtom, morkPatternToAtomList_set]

/-! ## Layer A (cont.): MORK-side collection atom replacement -/

/-- Replace the i-th element in a collection atom (the first child is the type symbol). -/
def replaceElemInCollectionAtom (a : Atom) (i : Nat) (newElem : Atom) : Option Atom :=
  match a with
  | .expression (hd :: tl) => some (.expression (hd :: tl.set i newElem))
  | _ => none

/-- For well-formed collection atoms, `replaceElemInCollectionAtom` returns `some`. -/
theorem replaceElemInCollectionAtom_collection (ct : ILCT) (elems : List ILP)
    (rest : Option String) (i : Nat) (newElem : Atom) :
    replaceElemInCollectionAtom (morkPatternToAtom (.collection ct elems rest)) i newElem =
    some (.expression (.symbol (morkCollTypeSymbol ct) ::
      (morkPatternToAtom.morkPatternToAtomList elems).set i newElem)) := by
  simp [replaceElemInCollectionAtom, morkPatternToAtom]

/-- Round-trip: replacing via `replaceElemInCollectionAtom` on a translated collection
    equals translating the `List.set`-modified collection. -/
theorem replaceElemInCollectionAtom_roundtrip (ct : ILCT) (elems : List ILP)
    (rest : Option String) (i : Nat) (q' : ILP) :
    replaceElemInCollectionAtom (morkPatternToAtom (.collection ct elems rest)) i
        (morkPatternToAtom q') =
    some (morkPatternToAtom (.collection ct (elems.set i q') rest)) := by
  rw [replaceElemInCollectionAtom_collection, morkPatternToAtom_collection_set]

/-! ## Layer B: Ground atom self-matching -/

/-- Ground atoms are identity under `applySubst`. -/
theorem applySubst_ground (σ : Subst) (a : Atom) (hg : isGroundAtom a = true) :
    applySubst σ a = a := by
  match a with
  | .var v => simp [isGroundAtom] at hg
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression es =>
    simp only [applySubst]; congr 1
    have hgl : isGroundAtom.isGroundList es = true := by
      simp only [isGroundAtom] at hg; exact hg
    exact applySubstList_ground σ es hgl
where
  applySubstList_ground (σ : Subst) (as : List Atom)
      (hg : isGroundAtom.isGroundList as = true) :
      applySubst.applySubstList σ as = as := by
    match as with
    | [] => rfl
    | e :: rest =>
      simp only [applySubst.applySubstList]
      have hge : isGroundAtom e = true := by
        simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at hg; exact hg.1
      have hgr : isGroundAtom.isGroundList rest = true := by
        simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at hg; exact hg.2
      congr 1
      · exact applySubst_ground σ e hge
      · exact applySubstList_ground σ rest hgr

/-- A ground atom matches itself under any substitution, leaving σ unchanged. -/
theorem matchAtom_ground_self (σ : Subst) (a : Atom) (hg : isGroundAtom a = true) :
    matchAtom σ a a = some σ := by
  match a with
  | .var v => simp [isGroundAtom] at hg
  | .symbol s => simp [matchAtom]
  | .grounded g => simp [matchAtom]
  | .expression es =>
    simp only [matchAtom]
    have hgl : isGroundAtom.isGroundList es = true := by
      simp only [isGroundAtom] at hg; exact hg
    exact matchAtomList_ground_self σ es hgl
where
  matchAtomList_ground_self (σ : Subst) (as : List Atom)
      (hg : isGroundAtom.isGroundList as = true) :
      matchAtom.matchAtomList σ as as = some σ := by
    match as with
    | [] => simp [matchAtom.matchAtomList]
    | e :: rest =>
      simp only [matchAtom.matchAtomList]
      have hge : isGroundAtom e = true := by
        simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at hg; exact hg.1
      have hgr : isGroundAtom.isGroundList rest = true := by
        simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at hg; exact hg.2
      rw [matchAtom_ground_self σ e hge]
      exact matchAtomList_ground_self σ rest hgr

/-- A ground atom in a space is found by `matchOneInSpace`. -/
theorem matchOneInSpace_ground_mem (σ : Subst) (a : Atom)
    (hg : isGroundAtom a = true) (s : Space) (ha : a ∈ s) :
    (σ, a) ∈ matchOneInSpace σ a s := by
  simp only [matchOneInSpace, List.mem_filterMap]
  exact ⟨a, Finset.mem_toList.mpr ha, by simp [matchAtom_ground_self σ a hg]⟩

/-! ## Layer C: Ad-hoc collection replace rule -/

/-- An exec rule that replaces one atom with another in the space. -/
def collectionReplaceRule (oldAtom newAtom : Atom) : ExecRule :=
  { priority := 40
    name     := "congElem"
    pat      := mkPattern [oldAtom]
    tmpl     := mkTemplate [mkRemove oldAtom, mkAdd newAtom] }

/-- Firing the collection-replace rule produces the expected space update. -/
theorem fireRule_collectionReplace (s : Space) (oldAtom newAtom : Atom)
    (hold : oldAtom ∈ s) (hg_old : isGroundAtom oldAtom = true)
    (hg_new : isGroundAtom newAtom = true) :
    (s.erase oldAtom ∪ {newAtom}) ∈ fireRule s (collectionReplaceRule oldAtom newAtom) := by
  simp only [fireRule, collectionReplaceRule, List.mem_map]
  -- Witness: ([], {oldAtom}) ∈ matchPattern [] s (mkPattern [oldAtom])
  refine ⟨([], {oldAtom}), ?mem, ?sink⟩
  case mem =>
    -- matchPattern [] s (mkPattern [oldAtom])
    -- = matchPattern.go [oldAtom] [] ∅
    -- matchOneInSpace [] oldAtom (s \ ∅) returns ([], oldAtom) since ground self-match
    -- then go [] [] ({oldAtom}) = [([], {oldAtom})]
    simp only [matchPattern, mkPattern]
    simp only [matchPattern.go, Finset.sdiff_empty]
    rw [List.mem_flatMap]
    refine ⟨([], oldAtom), matchOneInSpace_ground_mem [] oldAtom hg_old s hold, ?_⟩
    simp
  case sink =>
    -- applySinks s [] (mkTemplate [mkRemove oldAtom, mkAdd newAtom])
    -- = applySink (applySink s [] (.remove oldAtom)) [] (.add newAtom)
    -- = applySink (s.erase (applySubst [] oldAtom)) [] (.add newAtom)
    -- = applySink (s.erase oldAtom) [] (.add newAtom)
    -- = (s.erase oldAtom) ∪ {applySubst [] newAtom}   (if ground)
    -- = s.erase oldAtom ∪ {newAtom}
    simp only [applySinks, mkTemplate, List.foldl, applySink, mkRemove, mkAdd,
               applySubst_ground [] oldAtom hg_old,
               applySubst_ground [] newAtom hg_new,
               hg_new, ite_true]

/-! ## Layer E: Semantic-only congruence (exec rule firing) -/

/-- **Semantic congruence bridge**: when MeTTaIL rewrites element `i` inside a
    collection (via `congElem`), there exists a MORK exec rule whose firing produces
    the space with the old collection atom replaced by the new one.

    The exec rule is constructed ad-hoc from the concrete old/new collection atoms.
    It is NOT drawn from `languageDefToExecRules lang`.

    For the canonical structural version with `LensRel` factorization, see
    `congElem_implies_mork_zipper_fire` (Layer D). -/
theorem congElem_implies_mork_fire
    (ct : ILCT) (elems : List ILP)
    (i : Nat) (q' : ILP)
    -- MORK-side space preconditions
    (s : Space)
    (hp_in : morkPatternToAtom (.collection ct elems none) ∈ s)
    (hground_old : isGroundAtom (morkPatternToAtom (.collection ct elems none)) = true)
    (hground_new : isGroundAtom (morkPatternToAtom (.collection ct (elems.set i q') none)) = true) :
    ∃ rule : ExecRule,
      (s.erase (morkPatternToAtom (.collection ct elems none)) ∪
        {morkPatternToAtom (.collection ct (elems.set i q') none)}) ∈
      fireRule s rule :=
  ⟨collectionReplaceRule
      (morkPatternToAtom (.collection ct elems none))
      (morkPatternToAtom (.collection ct (elems.set i q') none)),
   fireRule_collectionReplace s _ _ hp_in hground_old hground_new⟩

/-! ## Layer D (primary): Zipper-based congElem bridge -/

/-- **Canonical collection congruence bridge**: the congElem update factors through
    a principled `LensRel` (zipper-based focus/replacement), AND there exists a MORK
    exec rule whose firing produces the updated space.

    This is the primary congruence theorem. The `LensRel` component witnesses that the
    update is a focused sub-expression replacement (not an arbitrary atom swap).
    The exec rule is ad-hoc (`collectionReplaceRule`), not from the language definition.

    For the semantic-only view (without `LensRel`), see `congElem_implies_mork_fire`. -/
theorem congElem_implies_mork_zipper_fire
    (ct : ILCT) (elems : List ILP)
    (i : Nat) (hi : i < elems.length) (q' : ILP)
    (s : Space)
    (hp_in : morkPatternToAtom (.collection ct elems none) ∈ s)
    (hground_old : isGroundAtom (morkPatternToAtom (.collection ct elems none)) = true)
    (hground_new : isGroundAtom (morkPatternToAtom (.collection ct (elems.set i q') none)) = true) :
    LensRel
      (morkPatternToAtom (.collection ct elems none))
      (morkPatternToAtom elems[i])
      (morkPatternToAtom q')
      (morkPatternToAtom (.collection ct (elems.set i q') none)) ∧
    ∃ rule : ExecRule,
      (s.erase (morkPatternToAtom (.collection ct elems none)) ∪
        {morkPatternToAtom (.collection ct (elems.set i q') none)}) ∈
      fireRule s rule :=
  ⟨collection_lensRel ct elems i hi q',
   congElem_implies_mork_fire ct elems i q' s hp_in hground_old hground_new⟩

/-! ## Layer F: Full DeclReduces bridge -/

/-- Singleton space replace: firing the ad-hoc replace rule on `{old}` yields `{new}`. -/
private theorem singleton_replace_fire (old new : Atom)
    (hg_old : isGroundAtom old = true) (hg_new : isGroundAtom new = true) :
    {new} ∈ fireRule {old} (collectionReplaceRule old new) := by
  have := fireRule_collectionReplace {old} old new (Finset.mem_singleton_self _) hg_old hg_new
  simp [Finset.erase_eq] at this
  exact this

private abbrev ILDL := Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef
private abbrev ILRelEnv := Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv
private abbrev ILBind := Mettapedia.OSLF.MeTTaIL.Match.Bindings
open Mettapedia.OSLF.MeTTaIL.DeclReductions (DeclReduces)

/-- **Full bridge theorem** for `DeclReduces`: handles both `topRule` and `congElem`.

    For `topRule`: the exec rule comes from `languageDefToExecRules lang`.
    For `congElem`: an ad-hoc `collectionReplaceRule` is constructed from the
    concrete old/new collection atoms (NOT from `languageDefToExecRules`).

    The conclusion uses the weaker `∃ r : ExecRule` (no lang membership).

    The `hground_coll` hypothesis is vacuously true when `p` is not a collection
    (i.e., all `topRule` applications). It provides the old-collection groundness
    needed by `fireRule_collectionReplace` in the `congElem` case.

    `morkPatternToAtom` ignores the `rest` parameter of collections, so this
    theorem works for ANY `rest : Option String`. -/
theorem declReduces_implies_mork_fire_full (lang : ILDL) (p q : ILP)
    (h : DeclReduces lang p q)
    (hlhs : ∀ r ∈ lang.rewrites, r.premises = [] →
        ∃ x, r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x)
    (htrans : ∀ r ∈ lang.rewrites, r.premises = [] → morkTranslatable r.right = true)
    (hground_q : isGroundAtom (morkPatternToAtom q) = true)
    (hground_coll : ∀ ct elems rest, p = .collection ct elems rest →
        isGroundAtom (morkPatternToAtom p) = true) :
    ∃ r : ExecRule,
      patternToSpace q ∈ fireRule (patternToSpace p) r := by
  cases h with
  | topRule r hr hrprem bs hbs hrhs =>
    obtain ⟨x, hlhs_x⟩ := hlhs r hr hrprem
    exact ⟨rewriteRuleToExecRule r,
           declReduces_topRule_fvar_mork_fire p q x r hlhs_x
             (htrans r hr hrprem) bs hbs hrhs hground_q⟩
  | congElem hct i hi r hr hrprem bs hbs hrhs =>
    simp only [patternToSpace]
    exact ⟨collectionReplaceRule _ _,
           singleton_replace_fire _ _ (hground_coll _ _ _ rfl) hground_q⟩

/-! ## Layer G: Source-level collection congruence

Promotes the ad-hoc `collectionReplaceRule` to a `SourceExecRule` using BTM-only
matching, and proves it fires via `fireSourceRule`. Source-aware bridges use
`languageDefToSourceExecRulesWithCongr` to extend the base rule set with this rule.

The BTM-only encoding matches the *entire* old collection atom against the workspace
(no sub-expression navigation at the source level). A future extension could use
`SourceFactor.focus` with zipper-based path navigation for genuine positional matching. -/

/-- Source-level encoding of collection element replacement.
    Uses a single BTM source factor matching the entire old collection atom. -/
def collectionReplaceSourceRule (oldAtom newAtom : Atom) : SourceExecRule :=
  { priority := 40
    name     := "congElem"
    input    := .explicit [.btm oldAtom]
    guards   := []
    tmpl     := mkTemplate [mkRemove oldAtom, mkAdd newAtom] }

/-- The source-level collection replace rule fires via `fireSourceRule`,
    producing the expected space update (erase old, insert new). -/
theorem fireSourceRule_collectionReplaceSource (s : Space) (old new : Atom)
    (hp : old ∈ s) (hg_old : isGroundAtom old = true) (hg_new : isGroundAtom new = true) :
    (s.erase old ∪ {new}) ∈ fireSourceRule s (collectionReplaceSourceRule old new) := by
  -- No guards → fireSourceRule = matchInputSpec followed by applySinks
  rw [fireSourceRule_no_guards _ _ rfl]
  rw [List.mem_map]
  refine ⟨([], {old}), ?mem, ?sink⟩
  case sink =>
    simp only [collectionReplaceSourceRule, applySinks, mkTemplate, List.foldl,
      applySink, mkRemove, mkAdd,
      applySubst_ground [] old hg_old, applySubst_ground [] new hg_new,
      hg_new, ite_true]
  case mem =>
    -- matchInputSpec [] s (.explicit [.btm old])
    simp only [collectionReplaceSourceRule, matchInputSpec, matchSourceFactors,
      matchSourceFactors.go, Finset.sdiff_empty, matchSourceFactor]
    rw [List.mem_flatMap]
    exact ⟨([], old), matchOneInSpace_ground_mem [] old hg_old s hp,
      by simp⟩

/-- Extend a language definition's source exec rules with congruence rules.
    The congruence rules are parameterized to allow different rule sets
    for different congruence scenarios. -/
def languageDefToSourceExecRulesWithCongr (lang : ILDL) (congrRules : List SourceExecRule) :
    List SourceExecRule :=
  languageDefToSourceExecRules lang ++ congrRules

/-- **Source-aware congruence bridge**: handles both `topRule` and `congElem` with a
    source-level rule set extended by congruence rules.

    Unlike `declReduces_implies_mork_fire_full` (Layer F) which concludes with an
    untyped `∃ r : ExecRule`, this theorem concludes with membership in a named
    source-rule set — enabling downstream consumers to track provenance.

    The congElem case produces a rule in the congruence extension
    (second part of `++`). -/
theorem declReduces_implies_mork_fireSourceRule (lang : ILDL) (p q : ILP)
    (h : DeclReduces lang p q)
    (hlhs : ∀ r ∈ lang.rewrites, r.premises = [] →
        ∃ x, r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x)
    (htrans : ∀ r ∈ lang.rewrites, r.premises = [] → morkTranslatable r.right = true)
    (hground_q : isGroundAtom (morkPatternToAtom q) = true)
    (hground_coll : ∀ ct elems rest, p = .collection ct elems rest →
        isGroundAtom (morkPatternToAtom p) = true) :
    ∃ r ∈ languageDefToSourceExecRulesWithCongr lang
             [collectionReplaceSourceRule (morkPatternToAtom p) (morkPatternToAtom q)],
      ∃ σ : Subst, applySinks (patternToSpace p) σ r.tmpl ∈
        fireSourceRule (patternToSpace p) r := by
  cases h with
  | topRule r hr hrprem bs hbs hrhs =>
    obtain ⟨x, hlhs_x⟩ := hlhs r hr hrprem
    refine ⟨rewriteRuleToSourceExecRule r, ?mem, bindingsToSubst bs, ?fire⟩
    case mem =>
      simp only [languageDefToSourceExecRulesWithCongr, List.mem_append]
      left
      simp only [languageDefToSourceExecRules, List.mem_filterMap]
      exact ⟨r, hr, by simp [hrprem, allPremisesTranslatable, premiseToSourceFactor]⟩
    case fire =>
      exact declReducesWithPremises_noPremise_fvar_mork_fireSourceRule
        p q x r Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv.empty lang
        hlhs_x (htrans r hr hrprem) hrprem bs hbs hrhs hground_q
        (patternToSpace p) (by simp [patternToSpace])
  | congElem hct i hi r hr hrprem bs hbs hrhs =>
    rename_i elems ct rest q'
    simp only [patternToSpace]
    have hg_old := hground_coll ct elems rest rfl
    refine ⟨collectionReplaceSourceRule
              (morkPatternToAtom (.collection ct elems rest))
              (morkPatternToAtom (.collection ct (elems.set i q') rest)),
            ?mem, ([] : Subst), ?fire⟩
    case mem =>
      simp only [languageDefToSourceExecRulesWithCongr, List.mem_append]
      right
      exact List.mem_cons_self ..
    case fire =>
      -- applySinks {old} [] tmpl = {old}.erase old ∪ {new}  (for ground old, new)
      have key := fireSourceRule_collectionReplaceSource
        {morkPatternToAtom (.collection ct elems rest)}
        (morkPatternToAtom (.collection ct elems rest))
        (morkPatternToAtom (.collection ct (elems.set i q') rest))
        (Finset.mem_singleton_self _) hg_old hground_q
      -- Show applySinks ... [] ... = erase ∪ insert
      simp only [collectionReplaceSourceRule, applySinks, mkTemplate, List.foldl,
        applySink, mkRemove, mkAdd,
        applySubst_ground [] _ hg_old, applySubst_ground [] _ hground_q,
        hground_q, ite_true] at key ⊢
      exact key

/-! ## Layer H: Premise-bearing source bridges

These variants extend the no-premise `declReduces_implies_mork_fireSourceRule`
to `DeclReducesWithPremises`, handling both `topRule` (via the existing per-rule bridge)
and `congElem` (via `collectionReplaceSourceRule`). -/

open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises (DeclReducesWithPremises)

/-- Single-premise `DeclReducesWithPremises` → `fireSourceRule`.
    Combines `languageDefToSourceExecRules` (for topRule) with congruence rules
    (for congElem) into an extended source-rule set. -/
theorem declReducesWithPremises_single_implies_mork_fireSourceRule
    (relEnv : ILRelEnv) (lang : ILDL) (p q : ILP)
    (h : DeclReducesWithPremises relEnv lang p q)
    (hlhs : ∀ r ∈ lang.rewrites,
        ∃ x, r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x)
    (htrans : ∀ r ∈ lang.rewrites, morkTranslatable r.right = true)
    (hprem_single : ∀ r ∈ lang.rewrites, ∃ rel args,
        r.premises = [Mettapedia.OSLF.MeTTaIL.Syntax.Premise.relationQuery rel args])
    (hground : isGroundAtom (morkPatternToAtom q) = true)
    (hground_coll : ∀ ct elems rest, p = .collection ct elems rest →
        isGroundAtom (morkPatternToAtom p) = true)
    (s : Space) (hp_in : morkPatternToAtom p ∈ s)
    (hws : ∀ r ∈ lang.rewrites,
        ∀ bs0 ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern r.left p,
        ∀ bs ∈ Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv relEnv lang r.premises bs0,
        ∃ a_prem ∈ s, a_prem ≠ morkPatternToAtom p ∧
          ∀ rel args, r.premises = [Mettapedia.OSLF.MeTTaIL.Syntax.Premise.relationQuery rel args] →
            matchAtom (bindingsToSubst bs0) (morkPatternToAtom (.apply rel args)) a_prem =
              some (bindingsToSubst bs)) :
    ∃ r_source ∈ languageDefToSourceExecRulesWithCongr lang
        [collectionReplaceSourceRule (morkPatternToAtom p) (morkPatternToAtom q)],
      ∃ σ : Subst, applySinks s σ r_source.tmpl ∈ fireSourceRule s r_source := by
  cases h with
  | topRule r hr bs0 hbs0 bs hbs hrhs =>
    obtain ⟨x, hlhs_r⟩ := hlhs r hr
    obtain ⟨rel, args, hprem_r⟩ := hprem_single r hr
    obtain ⟨a_prem, ha_in, ha_ne, ha_match⟩ := hws r hr bs0 hbs0 bs hbs
    have ha_match' := ha_match rel args hprem_r
    refine ⟨rewriteRuleToSourceExecRule r, ?_, bindingsToSubst bs, ?_⟩
    · simp only [languageDefToSourceExecRulesWithCongr, List.mem_append]
      left
      simp only [languageDefToSourceExecRules, List.mem_filterMap]
      refine ⟨r, hr, ?_⟩
      simp only [hprem_r, allPremisesTranslatable, List.all_cons, List.all_nil,
        Bool.and_true, premiseToSourceFactor, Option.isSome, ite_true]
    · exact declReducesWithPremises_singlePremise_fvar_mork_fireSourceRule
        p q x r relEnv lang rel args hlhs_r (htrans r hr) hprem_r bs0 hbs0 bs hbs
        hrhs hground s hp_in a_prem ha_in ha_ne ha_match'
  | congElem hct i hi r hr bs0 hbs0 bs hbs hq =>
    rename_i elems ct rest q'
    have hg_old := hground_coll ct elems rest rfl
    refine ⟨collectionReplaceSourceRule (morkPatternToAtom (.collection ct elems rest))
              (morkPatternToAtom (.collection ct (elems.set i q') rest)),
            ?mem, ([] : Subst), ?fire⟩
    case mem =>
      simp only [languageDefToSourceExecRulesWithCongr, List.mem_append]
      right; exact List.mem_cons_self ..
    case fire =>
      have key := fireSourceRule_collectionReplaceSource s
        (morkPatternToAtom (.collection ct elems rest))
        (morkPatternToAtom (.collection ct (elems.set i q') rest))
        hp_in hg_old hground
      simp only [collectionReplaceSourceRule, applySinks, mkTemplate, List.foldl,
        applySink, mkRemove, mkAdd,
        applySubst_ground [] _ hg_old, applySubst_ground [] _ hground,
        hground, ite_true] at key ⊢
      exact key

/-- Multi-premise `DeclReducesWithPremises` → `fireSourceRule`. -/
theorem declReducesWithPremises_multi_implies_mork_fireSourceRule
    (relEnv : ILRelEnv) (lang : ILDL) (p q : ILP)
    (h : DeclReducesWithPremises relEnv lang p q)
    (hlhs : ∀ r ∈ lang.rewrites,
        ∃ x, r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x)
    (htrans : ∀ r ∈ lang.rewrites, morkTranslatable r.right = true)
    (htrans_prem : ∀ r ∈ lang.rewrites, allPremisesTranslatable r.premises = true)
    (hground : isGroundAtom (morkPatternToAtom q) = true)
    (hground_coll : ∀ ct elems rest, p = .collection ct elems rest →
        isGroundAtom (morkPatternToAtom p) = true)
    (s : Space) (hp_in : morkPatternToAtom p ∈ s)
    (hchain : ∀ r ∈ lang.rewrites,
        ∀ bs0 ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern r.left p,
        ∀ bs ∈ Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv relEnv lang r.premises bs0,
        ∃ witnesses : List Atom,
          PremiseChain relEnv lang s bs0 r.premises witnesses bs ∧
          witnesses.Nodup ∧
          ∀ a ∈ witnesses, a ≠ morkPatternToAtom p) :
    ∃ r_source ∈ languageDefToSourceExecRulesWithCongr lang
        [collectionReplaceSourceRule (morkPatternToAtom p) (morkPatternToAtom q)],
      ∃ σ : Subst, applySinks s σ r_source.tmpl ∈ fireSourceRule s r_source := by
  cases h with
  | topRule r hr bs0 hbs0 bs hbs hrhs =>
    obtain ⟨x, hlhs_r⟩ := hlhs r hr
    obtain ⟨witnesses, hpc, hnd, hne⟩ := hchain r hr bs0 hbs0 bs hbs
    refine ⟨rewriteRuleToSourceExecRule r, ?_, bindingsToSubst bs, ?_⟩
    · simp only [languageDefToSourceExecRulesWithCongr, List.mem_append]
      left
      simp only [languageDefToSourceExecRules, List.mem_filterMap]
      exact ⟨r, hr, by simp [htrans_prem r hr]⟩
    · exact declReducesWithPremises_multiPremise_fvar_mork_fireSourceRule
        p q x r relEnv lang hlhs_r (htrans r hr) (htrans_prem r hr)
        bs0 hbs0 bs hrhs hground s hp_in witnesses hpc hnd hne
  | congElem hct i hi r hr bs0 hbs0 bs hbs hq =>
    rename_i elems ct rest q'
    have hg_old := hground_coll ct elems rest rfl
    refine ⟨collectionReplaceSourceRule (morkPatternToAtom (.collection ct elems rest))
              (morkPatternToAtom (.collection ct (elems.set i q') rest)),
            ?mem, ([] : Subst), ?fire⟩
    case mem =>
      simp only [languageDefToSourceExecRulesWithCongr, List.mem_append]
      right; exact List.mem_cons_self ..
    case fire =>
      have key := fireSourceRule_collectionReplaceSource s
        (morkPatternToAtom (.collection ct elems rest))
        (morkPatternToAtom (.collection ct (elems.set i q') rest))
        hp_in hg_old hground
      simp only [collectionReplaceSourceRule, applySinks, mkTemplate, List.foldl,
        applySink, mkRemove, mkAdd,
        applySubst_ground [] _ hg_old, applySubst_ground [] _ hground,
        hground, ite_true] at key ⊢
      exact key

/-- Multi-step bridge: for each step in `DeclReducesWithPremises`,
    there exists a source rule in the congruence-extended set whose
    `fireSourceRule` produces a result. -/
theorem declReducesStar_each_step_fires
    {relEnv : ILRelEnv} {lang : ILDL} {p q : ILP}
    (hstep : DeclReducesWithPremises relEnv lang p q)
    (hlhs : ∀ r ∈ lang.rewrites,
        ∃ x, r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x)
    (htrans : ∀ r ∈ lang.rewrites, morkTranslatable r.right = true)
    (htrans_prem : ∀ r ∈ lang.rewrites, allPremisesTranslatable r.premises = true)
    (hground : isGroundAtom (morkPatternToAtom q) = true)
    (hground_coll : ∀ ct elems rest, p = .collection ct elems rest →
        isGroundAtom (morkPatternToAtom p) = true)
    (s : Space) (hp_in : morkPatternToAtom p ∈ s)
    (hchain : ∀ r ∈ lang.rewrites,
        ∀ bs0 ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern r.left p,
        ∀ bs ∈ Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv relEnv lang r.premises bs0,
        ∃ witnesses : List Atom,
          PremiseChain relEnv lang s bs0 r.premises witnesses bs ∧
          witnesses.Nodup ∧
          ∀ a ∈ witnesses, a ≠ morkPatternToAtom p) :
    ∃ r_source ∈ languageDefToSourceExecRulesWithCongr lang
        [collectionReplaceSourceRule (morkPatternToAtom p) (morkPatternToAtom q)],
      ∃ σ : Subst, applySinks s σ r_source.tmpl ∈ fireSourceRule s r_source :=
  declReducesWithPremises_multi_implies_mork_fireSourceRule
    relEnv lang p q hstep hlhs htrans htrans_prem hground hground_coll s hp_in hchain

/-- Extend a language definition's ext source exec rules with congruence rules. -/
def languageDefToSourceExecRulesExtWithCongr (lang : ILDL) (congrRules : List SourceExecRule) :
    List SourceExecRule :=
  languageDefToSourceExecRulesExt lang ++ congrRules

/-- Extended (mixed relationQuery + freshness) bridge. -/
theorem declReducesWithPremises_ext_implies_mork_fireSourceRule
    (relEnv : ILRelEnv) (lang : ILDL) (p q : ILP)
    (h : DeclReducesWithPremises relEnv lang p q)
    (hlhs : ∀ r ∈ lang.rewrites,
        ∃ x, r.left = Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar x)
    (htrans : ∀ r ∈ lang.rewrites, morkTranslatable r.right = true)
    (htrans_prem : ∀ r ∈ lang.rewrites, allPremisesTranslatableExt r.premises = true)
    (hground : isGroundAtom (morkPatternToAtom q) = true)
    (hground_coll : ∀ ct elems rest, p = .collection ct elems rest →
        isGroundAtom (morkPatternToAtom p) = true)
    (s : Space) (hp_in : morkPatternToAtom p ∈ s)
    (hchain : ∀ r ∈ lang.rewrites,
        ∀ bs0 ∈ Mettapedia.OSLF.MeTTaIL.Match.matchPattern r.left p,
        ∀ bs ∈ Mettapedia.OSLF.MeTTaIL.Engine.applyPremisesWithEnv relEnv lang r.premises bs0,
        ∃ witnesses : List Atom,
          PremiseChain relEnv lang s bs0 r.premises witnesses bs ∧
          witnesses.Nodup ∧
          (∀ a ∈ witnesses, a ≠ morkPatternToAtom p) ∧
          matchSourceGuards (bindingsToSubst bs)
            (premisesToSourceGuards r.premises) = true) :
    ∃ r_source ∈ languageDefToSourceExecRulesExtWithCongr lang
        [collectionReplaceSourceRule (morkPatternToAtom p) (morkPatternToAtom q)],
      ∃ σ : Subst, applySinks s σ r_source.tmpl ∈ fireSourceRule s r_source := by
  cases h with
  | topRule r hr bs0 hbs0 bs hbs hrhs =>
    obtain ⟨x, hlhs_r⟩ := hlhs r hr
    obtain ⟨witnesses, hpc, hnd, hne, hg⟩ := hchain r hr bs0 hbs0 bs hbs
    refine ⟨rewriteRuleToSourceExecRuleExt r, ?_, bindingsToSubst bs, ?_⟩
    · simp only [languageDefToSourceExecRulesExtWithCongr, List.mem_append]
      left
      simp only [languageDefToSourceExecRulesExt, List.mem_filterMap]
      exact ⟨r, hr, by simp [htrans_prem r hr]⟩
    · exact declReducesWithPremises_multiPremise_fvar_mork_fireSourceRuleExt
        p q x r relEnv lang hlhs_r (htrans r hr) (htrans_prem r hr)
        bs0 hbs0 bs hrhs hground s hp_in witnesses hpc hnd hne hg
  | congElem hct i hi r hr bs0 hbs0 bs hbs hq =>
    rename_i elems ct rest q'
    have hg_old := hground_coll ct elems rest rfl
    refine ⟨collectionReplaceSourceRule (morkPatternToAtom (.collection ct elems rest))
              (morkPatternToAtom (.collection ct (elems.set i q') rest)),
            ?mem, ([] : Subst), ?fire⟩
    case mem =>
      simp only [languageDefToSourceExecRulesExtWithCongr, List.mem_append]
      right; exact List.mem_cons_self ..
    case fire =>
      have key := fireSourceRule_collectionReplaceSource s
        (morkPatternToAtom (.collection ct elems rest))
        (morkPatternToAtom (.collection ct (elems.set i q') rest))
        hp_in hg_old hground
      simp only [collectionReplaceSourceRule, applySinks, mkTemplate, List.foldl,
        applySink, mkRemove, mkAdd,
        applySubst_ground [] _ hg_old, applySubst_ground [] _ hground,
        hground, ite_true] at key ⊢
      exact key

/-! ## Future: Source-level positional collection rule

To enable genuine path-aware source matching (rather than whole-atom BTM),
one would extend `SourceFactor` with a `focus` constructor:
- `SourceFactor.focus (path : List Nat) (subPattern : Atom)` — navigate to child
  at `path` via `AtomZipper`, match `subPattern` against the focused sub-expression
- `SinkAction.replaceAtPath (path : List Nat) (newAtom : Atom)` — replace at path

This would use `AtomZipper` as the semantic spec for source-level positional congruence. -/

end Mettapedia.Languages.ProcessCalculi.MORK
