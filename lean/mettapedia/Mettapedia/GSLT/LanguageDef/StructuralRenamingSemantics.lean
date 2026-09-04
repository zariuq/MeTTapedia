import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Operational semantics of injective presentation renaming

An injective action on constructor symbols preserves the executable matcher,
binding application, and premise-free root rewriting exactly, including list
order and multiplicity.  These lemmas are independent of coproducts; they are
the semantic action required by any presentation transformation that renames
constructors.
-/

namespace Mettapedia.GSLT.LanguageDef.StructuralRenamingSemantics

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

/-- Injectivity of the sort action lifts structurally to type expressions. -/
theorem mapTypeExpr_injective
    (symbols : LanguageDefSymbolMap)
    (sortInjective : Function.Injective symbols.sort) :
    Function.Injective (mapTypeExpr symbols) := by
  intro first second
  induction first generalizing second with
  | base firstSort =>
      cases second with
      | base secondSort =>
          simp only [mapTypeExpr, TypeExpr.base.injEq]
          exact fun equality => sortInjective equality
      | arrow domain codomain => simp [mapTypeExpr]
      | multiBinder body => simp [mapTypeExpr]
      | collection collectionType element => simp [mapTypeExpr]
  | arrow firstDomain firstCodomain domainHypothesis codomainHypothesis =>
      cases second with
      | base sort => simp [mapTypeExpr]
      | arrow secondDomain secondCodomain =>
          simp only [mapTypeExpr, TypeExpr.arrow.injEq]
          exact fun equality => ⟨domainHypothesis equality.1,
            codomainHypothesis equality.2⟩
      | multiBinder body => simp [mapTypeExpr]
      | collection collectionType element => simp [mapTypeExpr]
  | multiBinder firstBody bodyHypothesis =>
      cases second with
      | base sort => simp [mapTypeExpr]
      | arrow domain codomain => simp [mapTypeExpr]
      | multiBinder secondBody =>
          simp only [mapTypeExpr, TypeExpr.multiBinder.injEq]
          exact fun equality => bodyHypothesis equality
      | collection collectionType element => simp [mapTypeExpr]
  | collection firstCollectionType firstElement elementHypothesis =>
      cases second with
      | base sort => simp [mapTypeExpr]
      | arrow domain codomain => simp [mapTypeExpr]
      | multiBinder body => simp [mapTypeExpr]
      | collection secondCollectionType secondElement =>
          simp only [mapTypeExpr, TypeExpr.collection.injEq]
          exact fun equality => ⟨equality.1,
            elementHypothesis equality.2⟩

/-- Map the concrete values of a matcher environment while preserving schema
variable names and their order. -/
def mapBindings (symbols : LanguageDefSymbolMap) : Bindings → Bindings :=
  List.map fun entry => (entry.1, mapPattern symbols entry.2)

@[simp]
theorem mapBindings_nil (symbols : LanguageDefSymbolMap) :
    mapBindings symbols [] = [] :=
  rfl

@[simp]
theorem mapBindings_cons (symbols : LanguageDefSymbolMap)
    (name : String) (value : Pattern) (bindings : Bindings) :
    mapBindings symbols ((name, value) :: bindings) =
      (name, mapPattern symbols value) :: mapBindings symbols bindings :=
  rfl

/-- Injectivity of the constructor action lifts to the entire shared pattern
carrier. -/
theorem mapPattern_injective
    (symbols : LanguageDefSymbolMap)
    (constructorInjective : Function.Injective symbols.constructor) :
    Function.Injective (mapPattern symbols) := by
  let inverseSymbols : LanguageDefSymbolMap :=
    { LanguageDefSymbolMap.id with
      constructor := Function.invFun symbols.constructor }
  have leftInverse : ∀ pattern,
      mapPattern inverseSymbols (mapPattern symbols pattern) = pattern := by
    intro pattern
    induction pattern using Pattern.inductionOn with
    | hbvar index => rfl
    | hfvar name => rfl
    | happly constructor arguments inductionHypothesis =>
        simp only [mapPattern, mapPatternList_eq_map, List.map_map]
        change Pattern.apply
            (Function.invFun symbols.constructor
              (symbols.constructor constructor)) _ = _
        rw [Function.leftInverse_invFun constructorInjective constructor]
        congr 1
        simpa [Function.comp_def] using
          List.map_congr_left (f := fun argument =>
              mapPattern inverseSymbols (mapPattern symbols argument))
            (g := _root_.id) (l := arguments)
            (fun argument membership => inductionHypothesis argument membership)
    | hlambda binder body inductionHypothesis =>
        simp [mapPattern, inductionHypothesis]
    | hmultiLambda arity binders body inductionHypothesis =>
        simp [mapPattern, inductionHypothesis]
    | hsubst body replacement bodyHypothesis replacementHypothesis =>
        simp [mapPattern, bodyHypothesis, replacementHypothesis]
    | hcollection collectionType elements rest inductionHypothesis =>
        simp only [mapPattern, mapPatternList_eq_map, List.map_map]
        congr 1
        simpa [Function.comp_def] using
          List.map_congr_left (f := fun element =>
              mapPattern inverseSymbols (mapPattern symbols element))
            (g := _root_.id) (l := elements)
            (fun element membership => inductionHypothesis element membership)
  exact Function.LeftInverse.injective leftInverse

/-- Binding lookup commutes with constructor translation because schema keys
are unchanged. -/
theorem find?_mapBindings (symbols : LanguageDefSymbolMap)
    (bindings : Bindings) (name : String) :
    (mapBindings symbols bindings).find? (·.1 == name) =
      (bindings.find? (·.1 == name)).map fun entry =>
        (entry.1, mapPattern symbols entry.2) := by
  induction bindings with
  | nil => rfl
  | cons entry bindings inductionHypothesis =>
      rcases entry with ⟨entryName, entryValue⟩
      by_cases equality : entryName = name
      · subst entryName
        simp [mapBindings]
      · simpa [mapBindings, equality] using inductionHypothesis

/-- Binding merge commutes exactly with an injective constructor renaming.
The injectivity premise is load-bearing when repeated metavariables compare
their previously bound values. -/
theorem mergeBindings_mapBindings
    (symbols : LanguageDefSymbolMap)
    (constructorInjective : Function.Injective symbols.constructor)
    (left right : Bindings) :
    (mergeBindings left right).map (mapBindings symbols) =
      mergeBindings (mapBindings symbols left) (mapBindings symbols right) := by
  induction right generalizing left with
  | nil => simp [mergeBindings]
  | cons entry right inductionHypothesis =>
      rcases entry with ⟨name, value⟩
      unfold mergeBindings
      rw [mapBindings_cons, List.foldlM_cons, List.foldlM_cons]
      have lookup := find?_mapBindings symbols left name
      cases found : left.find? (fun entry => entry.1 == name) with
      | none =>
          rw [found] at lookup
          simp only [Option.map_none] at lookup
          simp only [found, lookup]
          simpa [mergeBindings] using
            inductionHypothesis ((name, value) :: left)
      | some existingEntry =>
          rcases existingEntry with ⟨existingName, existingValue⟩
          rw [found] at lookup
          simp only [Option.map_some] at lookup
          by_cases equality : existingValue = value
          · subst existingValue
            simp only [found, lookup, beq_self_eq_true, if_true]
            simpa [mergeBindings] using inductionHypothesis left
          · have mappedInequality :
                mapPattern symbols existingValue ≠ mapPattern symbols value :=
              fun mappedEquality => equality
                (mapPattern_injective symbols constructorInjective mappedEquality)
            simp [found, lookup, equality, mappedInequality]

/-- Constructor translation commutes with de Bruijn lifting. -/
theorem mapPattern_liftBVars
    (symbols : LanguageDefSymbolMap) (cutoff shift : Nat) (pattern : Pattern) :
    mapPattern symbols
        (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars cutoff shift pattern) =
      Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars cutoff shift
        (mapPattern symbols pattern) := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index =>
      by_cases shifted : index ≥ cutoff <;>
        simp [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars,
          mapPattern, shifted]
  | hfvar name =>
      simp [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars, mapPattern]
  | happly constructor arguments inductionHypothesis =>
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars,
        mapPattern, mapPatternList_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro argument membership
      exact inductionHypothesis argument membership cutoff
  | hlambda binder body inductionHypothesis =>
      simp [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars,
        mapPattern, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars,
        mapPattern, inductionHypothesis]
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars,
        mapPattern, bodyHypothesis, replacementHypothesis]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars,
        mapPattern, mapPatternList_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro element membership
      exact inductionHypothesis element membership cutoff

/-- Structural constructor renaming commutes with locally nameless
instantiation. -/
theorem mapPattern_instantiateBVarAt
    (symbols : LanguageDefSymbolMap) (depth : Nat)
    (replacement body : Pattern) :
    mapPattern symbols
        (Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt
          depth replacement body) =
      Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt depth
        (mapPattern symbols replacement) (mapPattern symbols body) := by
  induction body using Pattern.inductionOn generalizing depth with
  | hbvar index =>
      by_cases below : index < depth
      · simp [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt,
          mapPattern, below]
      · by_cases equal : index = depth
        · subst index
          simp [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt,
            mapPattern, mapPattern_liftBVars]
        · simp [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt,
            mapPattern, below, equal]
  | hfvar name =>
      simp [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt, mapPattern]
  | happly constructor arguments inductionHypothesis =>
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt,
        mapPattern, mapPatternList_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro argument membership
      exact inductionHypothesis argument membership depth
  | hlambda binder nestedBody inductionHypothesis =>
      simp [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt,
        mapPattern, inductionHypothesis]
  | hmultiLambda arity binders nestedBody inductionHypothesis =>
      simp [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt,
        mapPattern, inductionHypothesis]
  | hsubst nestedBody nestedReplacement bodyHypothesis replacementHypothesis =>
      simp [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt,
        mapPattern, bodyHypothesis, replacementHypothesis]
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVarAt,
        mapPattern, mapPatternList_eq_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro element membership
      exact inductionHypothesis element membership depth

@[simp]
theorem mapPattern_instantiateBVar
    (symbols : LanguageDefSymbolMap) (replacement body : Pattern) :
    mapPattern symbols
        (Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVar replacement body) =
      Mettapedia.OSLF.MeTTaIL.Substitution.instantiateBVar
        (mapPattern symbols replacement) (mapPattern symbols body) :=
  mapPattern_instantiateBVarAt symbols 0 replacement body

/-- Gradual binding application commutes with constructor renaming.  Unlike
schema-key renamings, this requires no coverage side condition because matcher
variable names are preserved. -/
theorem applyBindings_mapPattern
    (symbols : LanguageDefSymbolMap) (bindings : Bindings) (pattern : Pattern) :
    applyBindings (mapBindings symbols bindings) (mapPattern symbols pattern) =
      mapPattern symbols (applyBindings bindings pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [applyBindings, mapPattern]
  | hfvar name =>
      have lookup := find?_mapBindings symbols bindings name
      cases found : bindings.find? (fun entry => entry.1 == name) with
      | none =>
          rw [found] at lookup
          simp [applyBindings, mapPattern, lookup, found]
      | some entry =>
          rcases entry with ⟨entryName, entryValue⟩
          rw [found] at lookup
          simp [applyBindings, mapPattern, lookup, found]
  | happly constructor arguments inductionHypothesis =>
      simp only [mapPattern, mapPatternList_eq_map, applyBindings, List.map_map]
      congr 1
      exact List.map_congr_left fun argument membership =>
        inductionHypothesis argument membership
  | hlambda binder body inductionHypothesis =>
      simp [mapPattern, applyBindings, inductionHypothesis]
  | hmultiLambda arity binders body inductionHypothesis =>
      simp [mapPattern, applyBindings, inductionHypothesis]
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp [mapPattern, applyBindings, bodyHypothesis, replacementHypothesis,
        mapPattern_instantiateBVar]
  | hcollection collectionType elements rest inductionHypothesis =>
      have elementsEquality :
          (elements.map (mapPattern symbols)).map
              (applyBindings (mapBindings symbols bindings)) =
            (elements.map (applyBindings bindings)).map
              (mapPattern symbols) := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro element membership
        exact inductionHypothesis element membership
      cases rest with
      | none =>
          simpa [mapPattern, mapPatternList_eq_map, applyBindings] using
            congrArg (fun mappedElements =>
              Pattern.collection collectionType mappedElements none)
              elementsEquality
      | some restName =>
          have lookup := find?_mapBindings symbols bindings restName
          cases found : bindings.find? (fun entry => entry.1 == restName) with
          | none =>
              rw [found] at lookup
              simp only [Option.map_none] at lookup
              simpa [mapPattern, mapPatternList_eq_map, applyBindings,
                found, lookup] using
                congrArg (fun mappedElements =>
                  Pattern.collection collectionType mappedElements (some restName))
                  elementsEquality
          | some entry =>
              rcases entry with ⟨entryName, entryValue⟩
              rw [found] at lookup
              simp only [Option.map_some] at lookup
              have unresolvedEquality :=
                congrArg (fun mappedElements =>
                  Pattern.collection collectionType mappedElements (some restName))
                  elementsEquality
              cases entryValue with
              | bvar index =>
                  simpa [mapPattern, mapPatternList_eq_map, applyBindings,
                    found, lookup] using unresolvedEquality
              | fvar name =>
                  simpa [mapPattern, mapPatternList_eq_map, applyBindings,
                    found, lookup] using unresolvedEquality
              | apply constructor arguments =>
                  simpa [mapPattern, mapPatternList_eq_map, applyBindings,
                    found, lookup] using unresolvedEquality
              | lambda binder body =>
                  simpa [mapPattern, mapPatternList_eq_map, applyBindings,
                    found, lookup] using unresolvedEquality
              | multiLambda arity binders body =>
                  simpa [mapPattern, mapPatternList_eq_map, applyBindings,
                    found, lookup] using unresolvedEquality
              | subst body replacement =>
                  simpa [mapPattern, mapPatternList_eq_map, applyBindings,
                    found, lookup] using unresolvedEquality
              | collection boundType restElements boundRest =>
                by_cases sameType : boundType = collectionType
                · subst boundType
                  cases boundRest with
                  | none =>
                      simpa [mapPattern, mapPatternList_eq_map, applyBindings,
                        found, lookup, List.map_append] using
                        congrArg (fun mappedElements =>
                          Pattern.collection collectionType
                            (mappedElements ++
                              restElements.map (mapPattern symbols)) none)
                          elementsEquality
                  | some nestedRest =>
                      simpa [mapPattern, mapPatternList_eq_map, applyBindings,
                        found, lookup] using
                        congrArg (fun mappedElements =>
                          Pattern.collection collectionType mappedElements
                            (some restName)) elementsEquality
                · cases boundRest <;>
                    simpa [mapPattern, mapPatternList_eq_map, applyBindings,
                      found, lookup, sameType] using
                      unresolvedEquality

theorem filterMap_merge_mapBindings
    (symbols : LanguageDefSymbolMap)
    (constructorInjective : Function.Injective symbols.constructor)
    (left : Bindings) (rights : List Bindings) :
    ((rights.map (mapBindings symbols)).filterMap fun right =>
        mergeBindings (mapBindings symbols left) right) =
      (rights.filterMap fun right => mergeBindings left right).map
        (mapBindings symbols) := by
  induction rights with
  | nil => rfl
  | cons right rights inductionHypothesis =>
      simp only [List.map_cons, List.filterMap_cons]
      rw [← mergeBindings_mapBindings symbols constructorInjective left right]
      cases mergeBindings left right <;> simp [inductionHypothesis]

theorem flatMap_merge_mapBindings
    (symbols : LanguageDefSymbolMap)
    (constructorInjective : Function.Injective symbols.constructor)
    (lefts rights : List Bindings) :
    (lefts.map (mapBindings symbols)).flatMap (fun left =>
        (rights.map (mapBindings symbols)).filterMap fun right =>
          mergeBindings left right) =
      (lefts.flatMap fun left =>
        rights.filterMap fun right => mergeBindings left right).map
          (mapBindings symbols) := by
  induction lefts with
  | nil => rfl
  | cons left lefts inductionHypothesis =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append]
      rw [filterMap_merge_mapBindings symbols constructorInjective left rights,
        inductionHypothesis]

theorem filterMap_merge_mappedBindings
    (symbols : LanguageDefSymbolMap)
    (constructorInjective : Function.Injective symbols.constructor)
    (left : Bindings) (rights : List Bindings) :
    (rights.filterMap fun right =>
        mergeBindings (mapBindings symbols left) (mapBindings symbols right)) =
      (rights.filterMap fun right => mergeBindings left right).map
        (mapBindings symbols) := by
  simpa only [List.filterMap_map, Function.comp_def] using
    filterMap_merge_mapBindings symbols constructorInjective left rights

theorem flatMap_merge_mappedBindings
    (symbols : LanguageDefSymbolMap)
    (constructorInjective : Function.Injective symbols.constructor)
    (lefts rights : List Bindings) :
    (lefts.map (mapBindings symbols)).flatMap (fun left =>
        rights.filterMap fun right =>
          mergeBindings left (mapBindings symbols right)) =
      (lefts.flatMap fun left =>
        rights.filterMap fun right => mergeBindings left right).map
          (mapBindings symbols) := by
  simpa only [List.filterMap_map, Function.comp_def] using
    flatMap_merge_mapBindings symbols constructorInjective lefts rights

theorem eraseIdx_map {alpha beta : Type*} (function : alpha → beta)
    (elements : List alpha) (index : Nat) :
    (elements.map function).eraseIdx index =
      (elements.eraseIdx index).map function := by
  induction elements generalizing index with
  | nil => simp
  | cons element elements inductionHypothesis =>
      cases index <;> simp [inductionHypothesis]

theorem flatMap_map_transport {alpha beta gamma delta : Type*}
    (outer : alpha → beta) (inner : gamma → delta)
    (source : alpha → List gamma) (target : beta → List delta)
    (elements : List alpha)
    (commutes : ∀ element ∈ elements,
      target (outer element) = (source element).map inner) :
    (elements.map outer).flatMap target =
      (elements.flatMap source).map inner := by
  induction elements with
  | nil => rfl
  | cons element elements inductionHypothesis =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append]
      rw [commutes element (by simp), inductionHypothesis]
      intro nested membership
      exact commutes nested (by simp [membership])

/-- The three mutually recursive matcher passes commute with an injective
constructor renaming.  The equalities are list equalities: search order and
multiplicity are preserved, not merely existence of a matching result. -/
theorem matcher_equivariance
    (symbols : LanguageDefSymbolMap)
    (constructorInjective : Function.Injective symbols.constructor) :
    (∀ patterns terms,
      matchArgs (patterns.map (mapPattern symbols))
          (terms.map (mapPattern symbols)) =
        (matchArgs patterns terms).map (mapBindings symbols)) ∧
    (∀ pattern term,
      matchPattern (mapPattern symbols pattern) (mapPattern symbols term) =
        (matchPattern pattern term).map (mapBindings symbols)) ∧
    (∀ patterns rest collectionType terms,
      matchBag (patterns.map (mapPattern symbols)) rest collectionType
          (terms.map (mapPattern symbols)) =
        (matchBag patterns rest collectionType terms).map
          (mapBindings symbols)) := by
  apply matchArgs.mutual_induct
  case case2 =>
    intro pattern patterns term terms argumentsHypothesis patternHypothesis
    simp only [List.map_cons, matchArgs, argumentsHypothesis,
      patternHypothesis]
    exact flatMap_merge_mapBindings symbols constructorInjective
      (matchPattern pattern term) (matchArgs patterns terms)
  case case3 =>
    intro left right noNil noCons
    cases left with
    | nil => cases right <;> simp [matchArgs]
    | cons leftHead leftTail =>
        cases right with
        | nil => simp [matchArgs]
        | cons rightHead rightTail =>
            exact False.elim
              (noCons leftHead leftTail rightHead rightTail rfl rfl)
  case case8 =>
    intro leftConstructor leftArguments rightConstructor rightArguments failed
    by_cases equal : leftConstructor = rightConstructor
    · subst rightConstructor
      have lengthNotEqual :
          leftArguments.length ≠ rightArguments.length := by
        intro lengthEqual
        apply failed
        simp [lengthEqual]
      simp [matchPattern, mapPattern, lengthNotEqual]
    · have mappedNotEqual :
          symbols.constructor leftConstructor ≠
            symbols.constructor rightConstructor :=
        fun mappedEqual => equal (constructorInjective mappedEqual)
      simp [matchPattern, mapPattern, equal, mappedNotEqual]
  case case14 =>
    intro patternBody patternReplacement termBody termReplacement
      replacementHypothesis bodyHypothesis
    simp only [mapPattern, matchPattern, replacementHypothesis,
      bodyHypothesis]
    exact flatMap_merge_mapBindings symbols constructorInjective
      (matchPattern patternBody termBody)
      (matchPattern patternReplacement termReplacement)
  case case15 =>
    intro pattern term notFvar notBvar notApply notLambda notMultiLambda
      notCollection notSubst
    cases pattern <;> cases term
    all_goals first
      | exact False.elim (notFvar _ rfl)
      | exact False.elim (notBvar _ _ rfl rfl)
      | exact False.elim (notApply _ _ _ _ rfl rfl)
      | exact False.elim (notLambda _ _ _ _ rfl rfl)
      | exact False.elim (notMultiLambda _ _ _ _ _ _ rfl rfl)
      | exact False.elim (notCollection _ _ _ _ _ _ rfl rfl)
      | exact False.elim (notSubst _ _ _ _ rfl rfl)
      | simp [matchPattern, mapPattern]
  case case19 =>
    intro pattern patterns rest collectionType terms bagHypothesis patternHypothesis
    let sourceStep : Pattern × Nat → List Bindings := fun entry =>
      (matchPattern pattern entry.1).flatMap fun headBindings =>
        (matchBag patterns rest collectionType
            (terms.eraseIdx entry.2)).filterMap fun tailBindings =>
          mergeBindings headBindings tailBindings
    let targetStep : Pattern × Nat → List Bindings := fun entry =>
      (matchPattern (mapPattern symbols pattern) entry.1).flatMap
        fun headBindings =>
          (matchBag (patterns.map (mapPattern symbols)) rest collectionType
              ((terms.map (mapPattern symbols)).eraseIdx entry.2)).filterMap
            fun tailBindings => mergeBindings headBindings tailBindings
    have stepCommutes : ∀ entry ∈ terms.zipIdx,
        targetStep (Prod.map (mapPattern symbols) _root_.id entry) =
          (sourceStep entry).map (mapBindings symbols) := by
      intro entry membership
      rcases entry with ⟨term, index⟩
      simp only [targetStep, sourceStep, Prod.map, id_eq]
      rw [eraseIdx_map, bagHypothesis index, patternHypothesis term]
      exact flatMap_merge_mapBindings symbols constructorInjective
        (matchPattern pattern term)
        (matchBag patterns rest collectionType (terms.eraseIdx index))
    simpa only [matchBag, List.map_cons, List.zipIdx_map, targetStep,
      sourceStep] using
      flatMap_map_transport (Prod.map (mapPattern symbols) _root_.id)
        (mapBindings symbols) sourceStep targetStep terms.zipIdx stepCommutes
  all_goals
    intros
    simp_all [matchArgs, matchPattern, matchBag, mapBindings,
      mapPattern, mapPatternList_eq_map]

theorem matchPattern_equivariance
    (symbols : LanguageDefSymbolMap)
    (constructorInjective : Function.Injective symbols.constructor)
    (pattern term : Pattern) :
    matchPattern (mapPattern symbols pattern) (mapPattern symbols term) =
      (matchPattern pattern term).map (mapBindings symbols) :=
  (matcher_equivariance symbols constructorInjective).2.1 pattern term

theorem applyRule_equivariance
    (symbols : LanguageDefSymbolMap)
    (constructorInjective : Function.Injective symbols.constructor)
    (rule : RewriteRule) (term : Pattern) :
    applyRule (mapRewriteRule symbols rule) (mapPattern symbols term) =
      (applyRule rule term).map (mapPattern symbols) := by
  unfold applyRule mapRewriteRule
  simp only [List.isEmpty_map]
  by_cases premiseFree : rule.premises.isEmpty
  · simp only [premiseFree, if_true,
      matchPattern_equivariance symbols constructorInjective]
    simp only [List.map_map]
    apply List.map_congr_left
    intro bindings membership
    exact applyBindings_mapPattern symbols bindings rule.right
  · simp [premiseFree]

#print axioms matcher_equivariance
#print axioms applyRule_equivariance

end Mettapedia.GSLT.LanguageDef.StructuralRenamingSemantics
