import Mettapedia.GSLT.LanguageDef.MapLanguageDef
import Mettapedia.OSLF.Framework.DerivedTyping

/-!
# Transport of constructor roles along presentation-symbol actions

The OSLF constructor analysis classifies each unary sort-crossing
constructor of a `LanguageDef` relative to a designated reduction sort:
`quoting` when its domain is the reduction sort, `reflecting` when only its
codomain is, and `neutral` otherwise (`classifyArrow`).  This module proves
that the classification is a structural invariant of the presentation: it
transports along the symbol actions of `mapLanguageDef`.

Main results:
- `mapLangSort` / `mapSortArrow`: sorts and sort-crossing arrows of a
  presentation transport to its image (arrows additionally require an
  injective sort action).
- `unaryCrossings_mapLanguageDef`: for an injective sort action, the crossing
  table of the image is exactly the mapped crossing table of the source.
- `classifyArrow_mapLanguageDef`: when the sort action moreover reflects the
  designated reduction sort (`symbols.sort s = mappedProcSort ↔ s = procSort`),
  the transported arrow receives the same `ConstructorRole` as the original.

Each hypothesis is necessary, witnessed on an inline three-sort canary
language with one quoting, one reflecting, and one neutral crossing:
- `classifyArrow_not_preserved_without_reduction_reflection`: an injective
  sort swap that moves a neutral sort onto the target reduction-sort name
  flips a `.neutral` arrow to a modal role.
- `unaryCrossings_not_transported_without_injectivity`: a collapsing sort
  action identifies a crossing's domain with its codomain, erasing every
  crossing of the image, so the crossing-table equality fails.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.DerivedTyping

/-! ## Transport of sorts -/

/-- A sort of a presentation transports to a sort of its image under any
symbol action. -/
def mapLangSort (symbols : LanguageDefSymbolMap) {language : LanguageDef}
    (sort : LangSort language) : LangSort (mapLanguageDef symbols language) :=
  ⟨symbols.sort sort.val, sortName_mem_mapLanguageDef symbols sort.property⟩

@[simp] theorem mapLangSort_val (symbols : LanguageDefSymbolMap)
    {language : LanguageDef} (sort : LangSort language) :
    (mapLangSort symbols sort).val = symbols.sort sort.val := rfl

/-! ## The crossing table of an image presentation -/

/-- The per-rule computation performed by `unaryCrossings`. -/
private def crossingOf (rule : GrammarRule) : Option (String × String × String) :=
  match rule.params with
  | [.simple _ typeExpr] =>
    match baseSortOf typeExpr with
    | some domSort =>
      if domSort ≠ rule.category then
        some (rule.label, domSort, rule.category)
      else none
    | none => none
  | _ => none

private theorem unaryCrossings_eq_filterMap (language : LanguageDef) :
    unaryCrossings language = language.terms.filterMap crossingOf := rfl

/-- One rule of the crossing computation, transported.  Injectivity of the
sort action is exactly what keeps a genuine crossing (`domSort ≠ category`)
from being collapsed in the image. -/
private theorem crossingOf_mapGrammarRule (symbols : LanguageDefSymbolMap)
    (sortInjective : Function.Injective symbols.sort) (rule : GrammarRule) :
    crossingOf (mapGrammarRule symbols rule) =
      (crossingOf rule).map (fun entry =>
        (symbols.constructor entry.1, symbols.sort entry.2.1,
          symbols.sort entry.2.2)) := by
  rcases rule with ⟨label, category, params, syntaxPattern, evalPolicy⟩
  cases params with
  | nil => rfl
  | cons param rest =>
    cases rest with
    | cons second tail => cases param <;> rfl
    | nil =>
      cases param with
      | abstractionNamed binder body type => rfl
      | multiAbstractionNamed binders body type => rfl
      | simple parameterName typeExpr =>
        cases typeExpr with
        | arrow domain codomain => rfl
        | multiBinder body => rfl
        | collection collectionType element => rfl
        | base sort =>
          by_cases sortEq : sort = category
          · subst sortEq
            simp [crossingOf, mapGrammarRule, mapTermParam, mapTypeExpr,
              baseSortOf]
          · have mappedNe : symbols.sort sort ≠ symbols.sort category :=
              fun collapsed => sortEq (sortInjective collapsed)
            simp [crossingOf, mapGrammarRule, mapTermParam, mapTypeExpr,
              baseSortOf, sortEq, mappedNe]

/-- **Crossing-table transport.**  For an injective sort action, the unary
sort-crossing table of the image presentation is the entrywise image of the
source table: each crossing `(label, dom, cod)` becomes
`(constructor label, sort dom, sort cod)`.  Injectivity is necessary
(`unaryCrossings_not_transported_without_injectivity` below). -/
theorem unaryCrossings_mapLanguageDef (symbols : LanguageDefSymbolMap)
    (language : LanguageDef)
    (sortInjective : Function.Injective symbols.sort) :
    unaryCrossings (mapLanguageDef symbols language) =
      (unaryCrossings language).map (fun entry =>
        (symbols.constructor entry.1, symbols.sort entry.2.1,
          symbols.sort entry.2.2)) := by
  rw [unaryCrossings_eq_filterMap, unaryCrossings_eq_filterMap,
    mapLanguageDef_terms, List.filterMap_map, List.map_filterMap]
  congr 1
  funext rule
  exact crossingOf_mapGrammarRule symbols sortInjective rule

/-! ## Transport of sort-crossing arrows -/

/-- A sort-crossing arrow of a presentation transports to a sort-crossing
arrow of its image, provided the sort action is injective. -/
def mapSortArrow (symbols : LanguageDefSymbolMap) {language : LanguageDef}
    {dom cod : LangSort language}
    (sortInjective : Function.Injective symbols.sort)
    (arrow : SortArrow language dom cod) :
    SortArrow (mapLanguageDef symbols language)
      (mapLangSort symbols dom) (mapLangSort symbols cod) where
  label := symbols.constructor arrow.label
  valid := by
    rw [unaryCrossings_mapLanguageDef symbols language sortInjective]
    exact List.mem_map_of_mem arrow.valid

@[simp] theorem mapSortArrow_label (symbols : LanguageDefSymbolMap)
    {language : LanguageDef} {dom cod : LangSort language}
    (sortInjective : Function.Injective symbols.sort)
    (arrow : SortArrow language dom cod) :
    (mapSortArrow symbols sortInjective arrow).label =
      symbols.constructor arrow.label := rfl

/-! ## Transport of constructor-role classification -/

/-- Completes the characterization triple of `classifyArrow_eq_quoting_iff`
and `classifyArrow_eq_reflecting_iff`: an arrow is neutral exactly when
neither endpoint is the reduction sort. -/
theorem classifyArrow_eq_neutral_iff (language : LanguageDef)
    (procSort : String) {dom cod : LangSort language}
    (arrow : SortArrow language dom cod) :
    classifyArrow language procSort arrow = .neutral ↔
      dom.val ≠ procSort ∧ cod.val ≠ procSort := by
  unfold classifyArrow
  by_cases domainEq : dom.val = procSort
  · simp [domainEq]
  · by_cases codomainEq : cod.val = procSort <;> simp [domainEq, codomainEq]

/-- **Classification transport.**  If the sort action is injective and
reflects the designated reduction sort — `symbols.sort s = mappedProcSort`
exactly when `s = procSort` — then the transported arrow is classified in the
image (relative to `mappedProcSort`) exactly as the original arrow is in the
source (relative to `procSort`).

Both hypotheses are necessary: dropping reduction-sort reflection flips a
neutral arrow (`classifyArrow_not_preserved_without_reduction_reflection`),
and dropping injectivity already destroys the crossing table
(`unaryCrossings_not_transported_without_injectivity`). -/
theorem classifyArrow_mapLanguageDef (symbols : LanguageDefSymbolMap)
    {language : LanguageDef} {dom cod : LangSort language}
    (sortInjective : Function.Injective symbols.sort)
    {procSort mappedProcSort : String}
    (procReflects : ∀ sortName,
      symbols.sort sortName = mappedProcSort ↔ sortName = procSort)
    (arrow : SortArrow language dom cod) :
    classifyArrow (mapLanguageDef symbols language) mappedProcSort
        (mapSortArrow symbols sortInjective arrow) =
      classifyArrow language procSort arrow := by
  by_cases domainEq : dom.val = procSort
  · rw [(classifyArrow_eq_quoting_iff language procSort arrow).mpr domainEq]
    exact (classifyArrow_eq_quoting_iff _ _ _).mpr
      ((procReflects dom.val).mpr domainEq)
  · by_cases codomainEq : cod.val = procSort
    · rw [(classifyArrow_eq_reflecting_iff language procSort arrow).mpr
        ⟨domainEq, codomainEq⟩]
      exact (classifyArrow_eq_reflecting_iff _ _ _).mpr
        ⟨fun mapped => domainEq ((procReflects dom.val).mp mapped),
          (procReflects cod.val).mpr codomainEq⟩
    · rw [(classifyArrow_eq_neutral_iff language procSort arrow).mpr
        ⟨domainEq, codomainEq⟩]
      exact (classifyArrow_eq_neutral_iff _ _ _).mpr
        ⟨fun mapped => domainEq ((procReflects dom.val).mp mapped),
          fun mapped => codomainEq ((procReflects cod.val).mp mapped)⟩

/-! ## Canary language

A three-sort language with reduction sort `"Act"` and crossings
`Freeze : Act → Sig` (quoting), `Thaw : Sig → Act` (reflecting), and
`Pack : Sig → Tok` (neutral). -/

private def tinyLang : LanguageDef :=
  { name := "constructor-role-transport-canary"
    types := [TypeDecl.plain "Act", TypeDecl.plain "Sig", TypeDecl.plain "Tok"]
    terms :=
      [ { label := "Freeze", category := "Sig",
          params := [.simple "process" (.base "Act")],
          syntaxPattern := [] },
        { label := "Thaw", category := "Act",
          params := [.simple "signal" (.base "Sig")],
          syntaxPattern := [] },
        { label := "Pack", category := "Tok",
          params := [.simple "signal" (.base "Sig")],
          syntaxPattern := [] } ]
    equations := []
    rewrites := [] }

private def actSort : LangSort tinyLang := ⟨"Act", by decide⟩
private def sigSort : LangSort tinyLang := ⟨"Sig", by decide⟩
private def tokSort : LangSort tinyLang := ⟨"Tok", by decide⟩

private def freezeArrow : SortArrow tinyLang actSort sigSort :=
  ⟨"Freeze", by decide⟩
private def thawArrow : SortArrow tinyLang sigSort actSort :=
  ⟨"Thaw", by decide⟩
private def packArrow : SortArrow tinyLang sigSort tokSort :=
  ⟨"Pack", by decide⟩

/-- An injective sort action: swap `"Act"` and `"Sig"`, fix everything else. -/
private def swapActSig (sortName : String) : String :=
  if sortName = "Act" then "Sig"
  else if sortName = "Sig" then "Act"
  else sortName

private def swapSymbols : LanguageDefSymbolMap :=
  { LanguageDefSymbolMap.id with
    sort := swapActSig
    constructor := fun constructorName => constructorName ++ "'" }

private theorem swapActSig_injective : Function.Injective swapActSig := by
  intro left right equal
  unfold swapActSig at equal
  split_ifs at equal <;> simp_all

private theorem swapSymbols_sort_injective :
    Function.Injective swapSymbols.sort := swapActSig_injective

/-- The swap reflects the reduction sort: the image reduction sort is
`"Sig"`, and only `"Act"` lands on it. -/
private theorem swapSymbols_reflects_reduction_sort :
    ∀ sortName, swapSymbols.sort sortName = "Sig" ↔ sortName = "Act" := by
  intro sortName
  show swapActSig sortName = "Sig" ↔ sortName = "Act"
  unfold swapActSig
  split_ifs <;> simp_all

/-! ## Positive canary: both hypotheses hold, classification transports -/

/-- **Positive canary.**  Under the injective, reduction-sort-reflecting swap,
every sort-crossing arrow of the canary language keeps its classification. -/
theorem constructorRoleCanary_classifyArrow_transport
    {dom cod : LangSort tinyLang}
    (arrow : SortArrow tinyLang dom cod) :
    classifyArrow (mapLanguageDef swapSymbols tinyLang) "Sig"
        (mapSortArrow swapSymbols swapSymbols_sort_injective arrow) =
      classifyArrow tinyLang "Act" arrow :=
  classifyArrow_mapLanguageDef swapSymbols swapSymbols_sort_injective
    swapSymbols_reflects_reduction_sort arrow

theorem constructorRoleCanary_freeze_is_quoting :
    classifyArrow tinyLang "Act" freezeArrow = .quoting := by decide

theorem constructorRoleCanary_freeze_mapped_is_quoting :
    classifyArrow (mapLanguageDef swapSymbols tinyLang) "Sig"
      (mapSortArrow swapSymbols swapSymbols_sort_injective freezeArrow) =
      .quoting := by decide

theorem constructorRoleCanary_thaw_is_reflecting :
    classifyArrow tinyLang "Act" thawArrow = .reflecting := by decide

theorem constructorRoleCanary_thaw_mapped_is_reflecting :
    classifyArrow (mapLanguageDef swapSymbols tinyLang) "Sig"
      (mapSortArrow swapSymbols swapSymbols_sort_injective thawArrow) =
      .reflecting := by decide

/-! ## Negative canary (a): reduction-sort reflection is necessary -/

theorem constructorRoleCanary_pack_is_neutral :
    classifyArrow tinyLang "Act" packArrow = .neutral := by decide

/-- The swap does not reflect the choice `"Act"` of image reduction sort: it
sends the neutral sort `"Sig"` onto that name. -/
private theorem swapSymbols_not_reflecting_for_Act :
    ¬ (∀ sortName, swapSymbols.sort sortName = "Act" ↔ sortName = "Act") := by
  intro reflects
  exact absurd ((reflects "Sig").mp (by decide)) (by decide)

/-- **Negative canary (a).**  Reduction-sort reflection is necessary in
`classifyArrow_mapLanguageDef`.  The swap is injective, yet with image
reduction sort `"Act"` (which the neutral sort `"Sig"` is mapped onto, so
reflection fails) the neutral arrow `Pack` is reclassified as quoting: the
transported classification differs from the original. -/
theorem classifyArrow_not_preserved_without_reduction_reflection :
    classifyArrow (mapLanguageDef swapSymbols tinyLang) "Act"
        (mapSortArrow swapSymbols swapSymbols_sort_injective packArrow) ≠
      classifyArrow tinyLang "Act" packArrow := by decide

/-! ## Negative canary (b): sort injectivity is necessary -/

private def collapseSymbols : LanguageDefSymbolMap :=
  { LanguageDefSymbolMap.id with sort := fun _ => "Pt" }

private theorem collapseSymbols_sort_not_injective :
    ¬ Function.Injective collapseSymbols.sort := by
  intro injective
  exact absurd (injective (a₁ := "Act") (a₂ := "Sig") rfl) (by decide)

/-- **Negative canary (b).**  Sort injectivity is necessary in
`unaryCrossings_mapLanguageDef`.  Collapsing every sort onto one name
identifies each crossing's domain with its codomain, so the image has no
crossings at all, while the mapped source table is nonempty. -/
theorem unaryCrossings_not_transported_without_injectivity :
    unaryCrossings (mapLanguageDef collapseSymbols tinyLang) ≠
      (unaryCrossings tinyLang).map (fun entry =>
        (collapseSymbols.constructor entry.1, collapseSymbols.sort entry.2.1,
          collapseSymbols.sort entry.2.2)) := by decide

/-! ## Axiom audit -/

#print axioms unaryCrossings_mapLanguageDef
#print axioms classifyArrow_mapLanguageDef
#print axioms constructorRoleCanary_classifyArrow_transport
#print axioms classifyArrow_not_preserved_without_reduction_reflection
#print axioms unaryCrossings_not_transported_without_injectivity

end Mettapedia.GSLT.LanguageDef
