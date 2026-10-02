import Mettapedia.GSLT.LanguageDef.MapLanguageDef
import Mettapedia.GSLT.LanguageDef.StructuralRenamingSemantics
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Reduction along an arbitrary map of symbols

Carrying a reduction forward requires that the matcher loses no result.
That holds of every map of symbols.  The stronger statement that the
matcher returns exactly the images of its results requires constructor
injectivity and remains in `StructuralRenamingSemantics`.

* Matching has no negative test.  A constructor is compared for equality, a
  repeated metavariable compares its two values for equality, and a bag
  pattern chooses elements; each succeeds on the image when it succeeds on
  the source.  A map that identifies two constructors can create matches and
  loses none.
* One bounded transport theorem carries premises and rules directly between
  the source and target presentations.  Symbol renaming and extension of the
  rule set are its two special cases, rather than separate inductions.
* The evaluator with no external relation is carried too.  A freshness
  condition reads the free variables of a term, which a map of symbols does
  not change, and the built-in relation compares two terms for equality.  The
  one condition is on a name: the relation map fixes the built-in relation
  `"eq"`.

So one-step reduction is preserved along every structural presentation
morphism that fixes the built-in relation name.  The statements with an
injective constructor map are the special case.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.StructuralSimulation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralRenamingSemantics

/-- A change-of-base square for non-contextual premise evidence along a
symbol action: every result produced by `base` at a source presentation is
produced, in mapped form, by `base'` at the image presentation.  Unlike an
exact equality of result lists, this membership law permits additional
results in the target. -/
def MapsBasePremiseResults (symbols : LanguageDefSymbolMap)
    (base base' : BasePremiseEvaluator) : Prop :=
  ∀ (language : LanguageDef) (bindings : Bindings) (premise : Premise)
    (result : Bindings),
    result ∈ base language bindings premise →
      mapBindings symbols result ∈
        base' (mapLanguageDef symbols language) (mapBindings symbols bindings)
          (mapPremise symbols premise)

/-- Premise-result transport between two specified presentations.  Both
renaming and inclusion of declarations can be discharged at this boundary. -/
def MapsBasePremiseResultsAt (symbols : LanguageDefSymbolMap)
    (base base' : BasePremiseEvaluator) (source target : LanguageDef) : Prop :=
  ∀ (bindings : Bindings) (premise : Premise) (result : Bindings),
    result ∈ base source bindings premise →
      mapBindings symbols result ∈
        base' target (mapBindings symbols bindings) (mapPremise symbols premise)

/-- A uniform result-transport law specializes to the chosen source. -/
theorem MapsBasePremiseResults.at {symbols : LanguageDefSymbolMap}
    {base base' : BasePremiseEvaluator}
    (maps : MapsBasePremiseResults symbols base base') (source : LanguageDef) :
    MapsBasePremiseResultsAt symbols base base' source (mapLanguageDef symbols source) :=
  maps source

/-- Transport to the image, followed by inclusion into the target, is a
direct transport law between the two presentations. -/
theorem MapsBasePremiseResults.toTarget {symbols : LanguageDefSymbolMap}
    {base base' : BasePremiseEvaluator}
    (maps : MapsBasePremiseResults symbols base base') (source target : LanguageDef)
    (mono : ∀ bindings premise result,
      result ∈ base' (mapLanguageDef symbols source) bindings premise →
        result ∈ base' target bindings premise) :
    MapsBasePremiseResultsAt symbols base base' source target :=
  fun bindings premise result member => mono _ _ _ (maps source bindings premise result member)

/-- The default evaluator does not consult the language argument. -/
theorem engineBasePremises_language_agnostic
    (relEnv : RelationEnv) (firstLanguage secondLanguage : LanguageDef)
    (bindings : Bindings) (premise : Premise) :
    engineBasePremises relEnv firstLanguage bindings premise =
      engineBasePremises relEnv secondLanguage bindings premise := by
  cases premise <;> rfl

end Mettapedia.GSLT.LanguageDef.StructuralSimulation

namespace Mettapedia.GSLT.LanguageDef.SymbolMapSimulation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralRenamingSemantics
open Mettapedia.GSLT.LanguageDef.StructuralSimulation

/-- The identity symbol action leaves the ordered bindings unchanged. -/
@[simp] theorem mapBindings_id (bindings : Bindings) :
    mapBindings LanguageDefSymbolMap.id bindings = bindings := by
  simp [mapBindings]

/-- A composite symbol action acts on bindings by consecutive mapping. -/
@[simp] theorem mapBindings_comp (first second : LanguageDefSymbolMap) (bindings : Bindings) :
    mapBindings (first.comp second) bindings =
      mapBindings second (mapBindings first bindings) := by
  simp [mapBindings, List.map_map, Function.comp_def]

/-! ## Matching -/

/-- **A successful merge of bindings is carried by every map of symbols.** -/
theorem mergeBindings_mapBindings_of_some (symbols : LanguageDefSymbolMap)
    {left right result : Bindings} (merged : mergeBindings left right = some result) :
    mergeBindings (mapBindings symbols left) (mapBindings symbols right) =
      some (mapBindings symbols result) := by
  induction right generalizing left with
  | nil =>
      simp only [mergeBindings, List.foldlM_nil] at merged
      obtain rfl : left = result := by simpa using merged
      simp [mergeBindings]
  | cons entry right recurse =>
      rcases entry with ⟨name, value⟩
      unfold mergeBindings at merged ⊢
      rw [mapBindings_cons, List.foldlM_cons]
      rw [List.foldlM_cons] at merged
      have lookup := find?_mapBindings symbols left name
      cases found : left.find? (fun entry => entry.1 == name) with
      | none =>
          rw [found] at lookup
          simp only [Option.map_none] at lookup
          simp only [found] at merged
          simp only [lookup]
          have step := recurse (left := (name, value) :: left)
            (by simpa [mergeBindings] using merged)
          simpa [mergeBindings] using step
      | some existingEntry =>
          rcases existingEntry with ⟨existingName, existingValue⟩
          rw [found] at lookup
          simp only [Option.map_some] at lookup
          simp only [found] at merged
          by_cases equality : existingValue = value
          · subst existingValue
            simp only [beq_self_eq_true, if_true] at merged
            simp only [lookup, beq_self_eq_true, if_true]
            have step := recurse (left := left) (by simpa [mergeBindings] using merged)
            simpa [mergeBindings] using step
          · simp [equality] at merged

mutual
  /-- A match is carried by every map of symbols. -/
  theorem matchRel_map (symbols : LanguageDefSymbolMap) :
      ∀ {pattern term : Pattern} {bindings : Bindings}, MatchRel pattern term bindings →
        MatchRel (mapPattern symbols pattern) (mapPattern symbols term)
          (mapBindings symbols bindings)
    | _, _, _, .fvar => by
        simp only [mapPattern, mapBindings, List.map_cons, List.map_nil]
        exact .fvar
    | _, _, _, .bvar => by
        simp only [mapPattern, mapBindings, List.map_nil]
        exact .bvar
    | _, _, _, .apply arguments lengths => by
        simp only [mapPattern, mapPatternList_eq_map]
        exact .apply (matchArgsRel_map symbols arguments) (by simpa using lengths)
    | _, _, _, .lambda body => by
        simp only [mapPattern]
        exact .lambda (matchRel_map symbols body)
    | _, _, _, .multiLambda body => by
        simp only [mapPattern]
        exact .multiLambda (matchRel_map symbols body)
    | _, _, _, .collection notVector elements => by
        simp only [mapPattern, mapPatternList_eq_map]
        exact .collection notVector (matchBagRel_map symbols elements)
    | _, _, _, .vector elements => by
        simp only [mapPattern, mapPatternList_eq_map]
        exact .vector (matchArgsRel_map symbols elements)
    | _, _, _, @MatchRel.vectorRest patterns prefixBindings restName result terms other
        elements merged => by
        simp only [mapPattern, mapPatternList_eq_map]
        refine .vectorRest (prefixBindings := mapBindings symbols prefixBindings) ?_ ?_
        · have mapped := matchArgsRel_map symbols elements
          simpa [List.map_take] using mapped
        · have mapped := mergeBindings_mapBindings_of_some symbols merged
          simpa [mapBindings, mapPattern, mapPatternList_eq_map, List.map_drop] using mapped
    | _, _, _, .subst body replacement merged => by
        simp only [mapPattern]
        exact .subst (matchRel_map symbols body) (matchRel_map symbols replacement)
          (mergeBindings_mapBindings_of_some symbols merged)

  /-- A match of argument lists is carried by every map of symbols. -/
  theorem matchArgsRel_map (symbols : LanguageDefSymbolMap) :
      ∀ {patterns terms : List Pattern} {bindings : Bindings},
        MatchArgsRel patterns terms bindings →
        MatchArgsRel (patterns.map (mapPattern symbols)) (terms.map (mapPattern symbols))
          (mapBindings symbols bindings)
    | _, _, _, .nil => by
        simp only [List.map_nil, mapBindings]
        exact .nil
    | _, _, _, .cons head tail merged => by
        simp only [List.map_cons]
        exact .cons (matchRel_map symbols head) (matchArgsRel_map symbols tail)
          (mergeBindings_mapBindings_of_some symbols merged)

  /-- A match of a bag is carried by every map of symbols. -/
  theorem matchBagRel_map (symbols : LanguageDefSymbolMap) :
      ∀ {patterns : List Pattern} {rest : Option String} {kind : CollType}
        {terms : List Pattern} {bindings : Bindings},
        MatchBagRel patterns rest kind terms bindings →
        MatchBagRel (patterns.map (mapPattern symbols)) rest kind
          (terms.map (mapPattern symbols)) (mapBindings symbols bindings)
    | _, _, _, _, _, .nilNoRest => by
        simp only [List.map_nil, mapBindings]
        exact .nilNoRest
    | _, _, _, _, _, .nilRest => by
        simp only [List.map_nil, mapBindings, List.map_cons, mapPattern, mapPatternList_eq_map]
        exact .nilRest
    | _, _, _, _, _, .cons index bound head tail merged => by
        simp only [List.map_cons]
        refine .cons index (by simpa using bound) ?_ ?_
          (mergeBindings_mapBindings_of_some symbols merged)
        · have mapped := matchRel_map symbols head
          simpa using mapped
        · have mapped := matchBagRel_map symbols tail
          simpa [eraseIdx_map] using mapped
end

/-- **Matching is carried by every map of symbols.**  No injectivity is
needed: a map that identifies constructors may create matches and loses
none. -/
theorem mem_matchPattern_mapPattern (symbols : LanguageDefSymbolMap) {pattern term : Pattern}
    {bindings : Bindings} (matched : bindings ∈ matchPattern pattern term) :
    mapBindings symbols bindings ∈
      matchPattern (mapPattern symbols pattern) (mapPattern symbols term) :=
  matchRel_complete (matchRel_map symbols (matchPattern_sound matched))

/-! ## Premises and bounded steps -/

/-- Evidence for one premise maps along a symbol action, given that bounded
steps at the same depth do. -/
theorem premiseAt_map_of_stepAt_to {symbols : LanguageDefSymbolMap}
    {base base' : BasePremiseEvaluator} {language language' : LanguageDef}
    (mapsBaseResults : MapsBasePremiseResultsAt symbols base base' language language') {fuel : Nat}
    (steps : ∀ {source target : Pattern}, StepAt base language fuel source target →
      StepAt base' language' fuel (mapPattern symbols source)
        (mapPattern symbols target))
    {initial final : Bindings} {premise : Premise}
    (evidence : PremiseAt base language fuel initial premise final) :
    PremiseAt base' language' fuel
      (mapBindings symbols initial) (mapPremise symbols premise)
      (mapBindings symbols final) := by
  cases evidence with
  | freshness member => exact .freshness (mapsBaseResults _ _ _ member)
  | relationQuery member => exact .relationQuery (mapsBaseResults _ _ _ member)
  | forAll member => exact .forAll (mapsBaseResults _ _ _ member)
  | congruence recursive matched merged =>
      rename_i premiseBindings premiseSource premiseTarget candidate
      refine PremiseAt.congruence
        (premiseBindings := mapBindings symbols premiseBindings)
        (candidate := mapPattern symbols candidate) ?_ ?_ ?_
      · rw [applyBindings_mapPattern]
        exact steps recursive
      · exact mem_matchPattern_mapPattern symbols matched
      · exact mergeBindings_mapBindings_of_some symbols merged
  | scopedRoot empty recursive matched merged =>
      rename_i premiseBindings step candidate
      refine PremiseAt.scopedRoot
        (premiseBindings := mapBindings symbols premiseBindings)
        (candidate := mapPattern symbols candidate)
        (by simp [empty]) ?_ ?_ ?_
      · rw [applyBindings_mapPattern]
        exact steps recursive
      · exact mem_matchPattern_mapPattern symbols matched
      · exact mergeBindings_mapBindings_of_some symbols merged

/-- Evidence for a list of premises maps along a symbol action, given that
bounded steps at the same depth do. -/
theorem premisesAt_map_of_stepAt_to {symbols : LanguageDefSymbolMap}
    {base base' : BasePremiseEvaluator} {language language' : LanguageDef}
    (mapsBaseResults : MapsBasePremiseResultsAt symbols base base' language language') {fuel : Nat}
    (steps : ∀ {source target : Pattern}, StepAt base language fuel source target →
      StepAt base' language' fuel (mapPattern symbols source)
        (mapPattern symbols target))
    {initial final : Bindings} {premises : List Premise}
    (evidence : PremisesAt base language fuel initial premises final) :
    PremisesAt base' language' fuel
      (mapBindings symbols initial) (premises.map (mapPremise symbols))
      (mapBindings symbols final) := by
  induction premises generalizing initial final with
  | nil =>
      cases evidence
      exact .nil _
  | cons premise premises recurse =>
      cases evidence with
      | cons first rest =>
          exact .cons (premiseAt_map_of_stepAt_to mapsBaseResults steps first) (recurse rest)

/-- Bounded contextual derivations map between presentations whose rules and
non-contextual premise results map forward, at the same depth.  No
injectivity is required. -/
theorem stepAt_map_of_rewrites {symbols : LanguageDefSymbolMap} {base base' : BasePremiseEvaluator}
    {language language' : LanguageDef}
    (mapsRules : ∀ rule, List.Mem rule language.rewrites →
      List.Mem (mapRewriteRule symbols rule) language'.rewrites)
    (mapsBaseResults : MapsBasePremiseResultsAt symbols base base' language language')
    {fuel : Nat} {source target : Pattern}
    (evidence : StepAt base language fuel source target) :
    StepAt base' language' fuel
      (mapPattern symbols source) (mapPattern symbols target) := by
  induction fuel generalizing source target with
  | zero => cases evidence
  | succ fuel recurse =>
      cases evidence with
      | @rule stepFuel stepSource stepTarget authoredRule initialBindings
          finalBindings ruleMember matched premisesEvidence targetEq =>
          have matchedSyntactic :
              initialBindings ∈ matchPattern authoredRule.left source := by
            simpa using matched
          have targetSyntactic :
              Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings authoredRule finalBindings
                = target := by
            simpa using targetEq
          refine StepAt.rule (rule := mapRewriteRule symbols authoredRule)
            (initialBindings := mapBindings symbols initialBindings)
            (finalBindings := mapBindings symbols finalBindings)
            (mapsRules authoredRule ruleMember) ?_ ?_ ?_
          · simp only [matchPatternForRule_eq_syntactic, mapRewriteRule]
            exact mem_matchPattern_mapPattern symbols matchedSyntactic
          · simpa only [mapRewriteRule] using
              premisesAt_map_of_stepAt_to mapsBaseResults (fun step => recurse step)
                premisesEvidence
          · simp only [applyBindingsForRule_eq_syntactic, mapRewriteRule,
              Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings]
            rw [applyBindingsScoped_mapPattern]
            exact congrArg (mapPattern symbols) targetSyntactic

/-- Evidence for one premise maps to the image presentation, given that
bounded steps at the same depth do. -/
theorem premiseAt_map_of_stepAt {symbols : LanguageDefSymbolMap}
    {base base' : BasePremiseEvaluator} {language : LanguageDef}
    (mapsBaseResults : MapsBasePremiseResults symbols base base') {fuel : Nat}
    (steps : ∀ {source target : Pattern}, StepAt base language fuel source target →
      StepAt base' (mapLanguageDef symbols language) fuel (mapPattern symbols source)
        (mapPattern symbols target))
    {initial final : Bindings} {premise : Premise}
    (evidence : PremiseAt base language fuel initial premise final) :
    PremiseAt base' (mapLanguageDef symbols language) fuel
      (mapBindings symbols initial) (mapPremise symbols premise)
      (mapBindings symbols final) :=
  premiseAt_map_of_stepAt_to (mapsBaseResults.at language) steps evidence

/-- Evidence for a list of premises maps to the image presentation, given
that bounded steps at the same depth do. -/
theorem premisesAt_map_of_stepAt {symbols : LanguageDefSymbolMap}
    {base base' : BasePremiseEvaluator} {language : LanguageDef}
    (mapsBaseResults : MapsBasePremiseResults symbols base base') {fuel : Nat}
    (steps : ∀ {source target : Pattern}, StepAt base language fuel source target →
      StepAt base' (mapLanguageDef symbols language) fuel (mapPattern symbols source)
        (mapPattern symbols target))
    {initial final : Bindings} {premises : List Premise}
    (evidence : PremisesAt base language fuel initial premises final) :
    PremisesAt base' (mapLanguageDef symbols language) fuel
      (mapBindings symbols initial) (premises.map (mapPremise symbols))
      (mapBindings symbols final) :=
  premisesAt_map_of_stepAt_to (mapsBaseResults.at language) steps evidence

/-- **Bounded contextual derivations map along every symbol action** whose
base evaluators are related, at the same depth. -/
theorem stepAt_map {symbols : LanguageDefSymbolMap} {base base' : BasePremiseEvaluator}
    {language : LanguageDef} (mapsBaseResults : MapsBasePremiseResults symbols base base')
    {fuel : Nat} {source target : Pattern}
    (evidence : StepAt base language fuel source target) :
    StepAt base' (mapLanguageDef symbols language) fuel
      (mapPattern symbols source) (mapPattern symbols target) :=
  stepAt_map_of_rewrites (fun _ member => mem_rewrites_mapLanguageDef symbols member)
    (mapsBaseResults.at language) evidence

/-- Premise evidence maps directly between presentations whose rules and
non-contextual premise results map forward. -/
theorem premisesAt_map_of_rewrites {symbols : LanguageDefSymbolMap}
    {base base' : BasePremiseEvaluator} {language language' : LanguageDef}
    (mapsRules : ∀ rule, List.Mem rule language.rewrites →
      List.Mem (mapRewriteRule symbols rule) language'.rewrites)
    (mapsBaseResults : MapsBasePremiseResultsAt symbols base base' language language')
    {fuel : Nat} {initial final : Bindings} {premises : List Premise}
    (evidence : PremisesAt base language fuel initial premises final) :
    PremisesAt base' language' fuel (mapBindings symbols initial)
      (premises.map (mapPremise symbols)) (mapBindings symbols final) :=
  premisesAt_map_of_stepAt_to mapsBaseResults
    (fun step => stepAt_map_of_rewrites mapsRules mapsBaseResults step) evidence

/-- Evidence for a list of premises maps along every symbol action whose base
evaluators are related. -/
theorem premisesAt_map {symbols : LanguageDefSymbolMap} {base base' : BasePremiseEvaluator}
    {language : LanguageDef} (mapsBaseResults : MapsBasePremiseResults symbols base base')
    {fuel : Nat} {initial final : Bindings} {premises : List Premise}
    (evidence : PremisesAt base language fuel initial premises final) :
    PremisesAt base' (mapLanguageDef symbols language) fuel
      (mapBindings symbols initial) (premises.map (mapPremise symbols))
      (mapBindings symbols final) :=
  premisesAt_map_of_stepAt mapsBaseResults (fun step => stepAt_map mapsBaseResults step)
    evidence

/-! ## Adding rules -/

end Mettapedia.GSLT.LanguageDef.SymbolMapSimulation

namespace Mettapedia.GSLT.LanguageDef.StructuralSimulation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralRenamingSemantics
open Mettapedia.GSLT.LanguageDef.SymbolMapSimulation

/-- Direct premise-result transport composes without constructing an
intermediate mapped presentation. -/
theorem MapsBasePremiseResultsAt.comp
    {first second : LanguageDefSymbolMap}
    {base middleBase targetBase : BasePremiseEvaluator}
    {source middle target : LanguageDef}
    (firstMaps : MapsBasePremiseResultsAt first base middleBase source middle)
    (secondMaps : MapsBasePremiseResultsAt second middleBase targetBase middle target) :
    MapsBasePremiseResultsAt (first.comp second) base targetBase source target := by
  intro bindings premise result member
  have mapped := secondMaps (mapBindings first bindings) (mapPremise first premise)
    (mapBindings first result) (firstMaps bindings premise result member)
  simpa only [mapBindings_comp, mapPremise_comp] using mapped

/-- At the identity symbol map, result transport is precisely monotonicity
of the base evaluator between the two presentations. -/
theorem mapsBasePremiseResultsAt_id {base : BasePremiseEvaluator}
    {language language' : LanguageDef}
    (baseMono : ∀ bindings premise result,
      result ∈ base language bindings premise →
        result ∈ base language' bindings premise) :
    MapsBasePremiseResultsAt LanguageDefSymbolMap.id base base language language' := by
  intro bindings premise result member
  simpa only [mapBindings_id, mapPremise_id] using baseMono bindings premise result member

/-- Rule-set inclusion is the identity-map instance of bounded transport.
The base evaluator may depend on the language, provided its results map
forward along the inclusion. -/
theorem stepAt_of_rewrites_mem
    {base : BasePremiseEvaluator} {language language' : LanguageDef}
    (rulesMem : ∀ rule, List.Mem rule language.rewrites →
      List.Mem rule language'.rewrites)
    (baseMono : ∀ bindings premise result,
      result ∈ base language bindings premise →
        result ∈ base language' bindings premise)
    {fuel : Nat} {source target : Pattern}
    (evidence : StepAt base language fuel source target) :
    StepAt base language' fuel source target := by
  simpa only [mapPattern_id] using
    stepAt_map_of_rewrites (symbols := LanguageDefSymbolMap.id)
      (fun rule member => by simpa only [mapRewriteRule_id] using rulesMem rule member)
      (mapsBasePremiseResultsAt_id baseMono) evidence

end Mettapedia.GSLT.LanguageDef.StructuralSimulation

namespace Mettapedia.GSLT.LanguageDef.SymbolMapSimulation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralRenamingSemantics
open Mettapedia.GSLT.LanguageDef.StructuralSimulation

/-- Premise evidence is retained when rules are added: the identity-map
instance of direct transport. -/
theorem premisesAt_of_rewrites_mem
    {base : BasePremiseEvaluator} {language language' : LanguageDef}
    (rulesMem : ∀ rule, List.Mem rule language.rewrites →
      List.Mem rule language'.rewrites)
    (baseMono : ∀ bindings premise result,
      result ∈ base language bindings premise →
        result ∈ base language' bindings premise)
    {fuel : Nat} {initial final : Bindings} {premises : List Premise}
    (evidence : PremisesAt base language fuel initial premises final) :
    PremisesAt base language' fuel initial premises final := by
  have premisesFixed : mapPremise LanguageDefSymbolMap.id = id := funext mapPremise_id
  simpa only [mapBindings_id, premisesFixed, List.map_id] using
    premisesAt_map_of_rewrites (symbols := LanguageDefSymbolMap.id)
      (fun rule member => by simpa only [mapRewriteRule_id] using rulesMem rule member)
      (mapsBasePremiseResultsAt_id baseMono) evidence

/-! ## Structural presentation morphisms -/

/-- **One-step reduction is preserved along every structural presentation
morphism** whose base evaluators are related. -/
theorem step_map_of_structuralMorphism {base base' : BasePremiseEvaluator}
    {source target : ValidatedLanguageDef} (morphism : StructuralMorphism source target)
    (mapsBaseResults : MapsBasePremiseResults morphism.symbols base base')
    (baseMono : ∀ bindings premise result,
      result ∈ base' (mapLanguageDef morphism.symbols source.language)
          bindings premise →
        result ∈ base' target.language bindings premise)
    {pattern next : Pattern} (step : Step base source.language pattern next) :
    Step base' target.language (mapPattern morphism.symbols pattern)
      (mapPattern morphism.symbols next) := by
  obtain ⟨fuel, bounded⟩ := step
  exact ⟨fuel, stepAt_map_of_rewrites morphism.mapsRewrites
    (mapsBaseResults.toTarget source.language target.language baseMono) bounded⟩

/-- Premises map along a structural presentation morphism: evidence for the
premises of a source schema is evidence, in the target, for the premises of
its image. -/
theorem premisesAt_map_of_structuralMorphism {base base' : BasePremiseEvaluator}
    {source target : ValidatedLanguageDef} (morphism : StructuralMorphism source target)
    (mapsBaseResults : MapsBasePremiseResults morphism.symbols base base')
    (baseMono : ∀ bindings premise result,
      result ∈ base' (mapLanguageDef morphism.symbols source.language)
          bindings premise →
        result ∈ base' target.language bindings premise)
    {fuel : Nat} {initial final : Bindings} {premises : List Premise}
    (evidence : PremisesAt base source.language fuel initial premises final) :
    PremisesAt base' target.language fuel (mapBindings morphism.symbols initial)
      (premises.map (mapPremise morphism.symbols))
      (mapBindings morphism.symbols final) := by
  exact premisesAt_map_of_rewrites morphism.mapsRewrites
    (mapsBaseResults.toTarget source.language target.language baseMono) evidence

/-! ## The evaluator with no external relation -/

private theorem lookup_mapBindings (symbols : LanguageDefSymbolMap)
    (bindings : Bindings) (name : String) :
    (mapBindings symbols bindings).lookup name =
      (bindings.lookup name).map (mapPattern symbols) := by
  simp only [Bindings.lookup, find?_mapBindings, Option.map_map]
  rfl

private theorem freeVars_mapPattern (symbols : LanguageDefSymbolMap) (pattern : Pattern) :
    freeVars (mapPattern symbols pattern) = freeVars pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly constructor arguments recurse =>
      simp only [mapPattern, mapPatternList_eq_map, freeVars, List.flatMap_map]
      exact List.flatMap_congr recurse
  | hlambda binder body recurse => simp [mapPattern, freeVars, recurse]
  | hmultiLambda arity binders body recurse => simp [mapPattern, freeVars, recurse]
  | hsubst body replacement bodyRecurse replacementRecurse =>
      simp [mapPattern, freeVars, bodyRecurse, replacementRecurse]
  | hcollection collectionType elements rest recurse =>
      simp only [mapPattern, mapPatternList_eq_map, freeVars, List.flatMap_map]
      exact List.flatMap_congr recurse

private theorem checkFreshness_mapPattern (symbols : LanguageDefSymbolMap)
    (varName : String) (term : Pattern) :
    checkFreshness ⟨varName, mapPattern symbols term⟩ = checkFreshness ⟨varName, term⟩ := by
  simp [checkFreshness, isFresh, freeVars_mapPattern]

/-- The variable a freshness condition speaks of: a metavariable bound to a
name resolves to that name, an unbound one to itself, and one bound to
anything else fails. -/
private def resolveFreshName (bindings : Bindings) (varName : String) : Option String :=
  match bindings.lookup varName with
  | some (.fvar boundName) => some boundName
  | some _ => none
  | none => some varName

private theorem premiseStepWithEnv_freshness_eq (relEnv : RelationEnv) (language : LanguageDef)
    (bindings : Bindings) (condition : FreshnessCondition) :
    premiseStepWithEnv relEnv language bindings (.freshness condition) =
      match resolveFreshName bindings condition.varName with
      | some resolved =>
          if checkFreshness ⟨resolved, applyBindings bindings condition.term⟩
          then [bindings]
          else []
      | none => [] := rfl

private theorem resolveFreshName_mapBindings (symbols : LanguageDefSymbolMap)
    (bindings : Bindings) (varName : String) :
    resolveFreshName (mapBindings symbols bindings) varName =
      resolveFreshName bindings varName := by
  unfold resolveFreshName
  rw [lookup_mapBindings]
  cases found : bindings.lookup varName with
  | none => rfl
  | some value => cases value <;> simp [mapPattern]

/-- A match of one relation argument is carried by every map of symbols. -/
theorem mem_matchRelationArgument_map (symbols : LanguageDefSymbolMap) {seed : Bindings}
    {argument value : Pattern} {result : Bindings}
    (member : result ∈ matchRelationArgument seed argument value) :
    mapBindings symbols result ∈
      matchRelationArgument (mapBindings symbols seed) (mapPattern symbols argument)
        (mapPattern symbols value) := by
  cases argument with
  | fvar name =>
      simp only [mapPattern, matchRelationArgument, lookup_mapBindings] at member ⊢
      cases found : seed.lookup name with
      | none =>
          rw [found] at member
          obtain rfl := List.mem_singleton.mp member
          simp [mapBindings]
      | some existing =>
          rw [found] at member
          by_cases equal : existing = value
          · subst equal
            simp only [if_true] at member
            obtain rfl := List.mem_singleton.mp member
            simp [mapBindings]
          · simp [equal] at member
  | bvar index => exact mem_matchPattern_mapPattern symbols member
  | apply constructor arguments => exact mem_matchPattern_mapPattern symbols member
  | lambda binder body => exact mem_matchPattern_mapPattern symbols member
  | multiLambda arity binders body => exact mem_matchPattern_mapPattern symbols member
  | subst body replacement => exact mem_matchPattern_mapPattern symbols member
  | collection kind elements rest => exact mem_matchPattern_mapPattern symbols member

/-- A match of a relation row is carried by every map of symbols. -/
theorem mem_matchRelationArgs_map (symbols : LanguageDefSymbolMap) (arguments : List Pattern) :
    ∀ (seed : Bindings) (values : List Pattern) {result : Bindings},
      result ∈ matchRelationArgs seed arguments values →
        mapBindings symbols result ∈
          matchRelationArgs (mapBindings symbols seed) (arguments.map (mapPattern symbols))
            (values.map (mapPattern symbols)) := by
  induction arguments with
  | nil =>
      intro seed values result member
      cases values with
      | nil =>
          simp only [matchRelationArgs, List.mem_singleton] at member
          subst member
          simp [matchRelationArgs]
      | cons value values => simp [matchRelationArgs] at member
  | cons argument arguments recurse =>
      intro seed values result member
      cases values with
      | nil => simp [matchRelationArgs] at member
      | cons value values =>
          simp only [matchRelationArgs, List.mem_flatMap] at member
          obtain ⟨headBindings, headMember, inner⟩ := member
          cases merged : mergeBindings seed headBindings with
          | none => simp [merged] at inner
          | some extended =>
              rw [merged] at inner
              obtain ⟨tailBindings, tailMember, joined⟩ := List.mem_filterMap.mp inner
              simp only [List.map_cons, matchRelationArgs, List.mem_flatMap]
              refine ⟨mapBindings symbols headBindings,
                mem_matchRelationArgument_map symbols headMember, ?_⟩
              rw [mergeBindings_mapBindings_of_some symbols merged]
              exact List.mem_filterMap.mpr ⟨mapBindings symbols tailBindings,
                recurse extended values tailMember,
                mergeBindings_mapBindings_of_some symbols joined⟩

private theorem builtinRelationTuples_map (symbols : LanguageDefSymbolMap)
    (relationFixesEq : symbols.relation "eq" = "eq")
    (sourceLanguage targetLanguage : LanguageDef)
    (relation : String) (argumentPatterns : List Pattern) {tuple : List Pattern}
    (member : tuple ∈ builtinRelationTuples sourceLanguage relation argumentPatterns) :
    tuple.map (mapPattern symbols) ∈
      builtinRelationTuples targetLanguage (symbols.relation relation)
        (argumentPatterns.map (mapPattern symbols)) := by
  unfold builtinRelationTuples at member ⊢
  split at member
  · rw [relationFixesEq]
    simp only [List.map_cons, List.map_nil]
    rcases List.mem_cons.mp member with rfl | member
    · simp +decide
    · rcases List.mem_singleton.mp member with rfl
      simp +decide
  · cases member

/-- A result of a query of the built-in relation is carried by every map of
symbols that fixes its name. -/
theorem mem_relationQueryStep_empty_map (symbols : LanguageDefSymbolMap)
    (relationFixesEq : symbols.relation "eq" = "eq")
    (sourceLanguage targetLanguage : LanguageDef)
    (bindings : Bindings) (relation : String) (arguments : List Pattern) {result : Bindings}
    (member : result ∈ relationQueryStep RelationEnv.empty sourceLanguage
      bindings relation arguments) :
    mapBindings symbols result ∈
      relationQueryStep RelationEnv.empty targetLanguage
        (mapBindings symbols bindings) (symbols.relation relation)
        (arguments.map (mapPattern symbols)) := by
  simp only [relationQueryStep, RelationEnv.empty, List.append_nil,
    List.mem_flatMap, List.mem_filterMap] at member ⊢
  obtain ⟨tuple, tupleMember, premiseBindings, argsMember, merged⟩ := member
  have argumentPatterns :
      (arguments.map (mapPattern symbols)).map
          (applyBindings (mapBindings symbols bindings)) =
        (arguments.map (applyBindings bindings)).map (mapPattern symbols) := by
    simp only [List.map_map]
    exact List.map_congr_left fun argument _ =>
      applyBindings_mapPattern symbols bindings argument
  refine ⟨tuple.map (mapPattern symbols), ?_,
    mapBindings symbols premiseBindings, ?_, ?_⟩
  · rw [argumentPatterns]
    exact builtinRelationTuples_map symbols relationFixesEq
      sourceLanguage targetLanguage relation _ tupleMember
  · exact mem_matchRelationArgs_map symbols arguments bindings tuple argsMember
  · exact mergeBindings_mapBindings_of_some symbols merged

/-- **The evaluator with no external relation maps its results along every
symbol action that fixes the built-in relation name `"eq"`.**  The
constructor part need not be injective. -/
theorem engineBasePremises_empty_maps_results (symbols : LanguageDefSymbolMap)
    (relationFixesEq : symbols.relation "eq" = "eq") :
    MapsBasePremiseResults symbols (engineBasePremises RelationEnv.empty)
      (engineBasePremises RelationEnv.empty) := by
  intro language bindings premise result member
  cases premise with
  | congruence left right =>
      simp [engineBasePremises] at member
  | scopedStep step =>
      simp [engineBasePremises, premiseStepWithEnv] at member
  | forAll collection parameter body =>
      simp [engineBasePremises, premiseStepWithEnv] at member
  | freshness condition =>
      have memberEval : result ∈ premiseStepWithEnv RelationEnv.empty
          language bindings (.freshness condition) := member
      rw [premiseStepWithEnv_freshness_eq] at memberEval
      show mapBindings symbols result ∈
        premiseStepWithEnv RelationEnv.empty (mapLanguageDef symbols language)
          (mapBindings symbols bindings)
          (.freshness ⟨condition.varName, mapPattern symbols condition.term⟩)
      rw [premiseStepWithEnv_freshness_eq]
      cases resolved : resolveFreshName bindings condition.varName with
      | none =>
          simp only [resolved] at memberEval
          cases memberEval
      | some resolvedName =>
          simp only [resolved] at memberEval
          by_cases fresh :
              checkFreshness ⟨resolvedName, applyBindings bindings condition.term⟩
          · rw [if_pos fresh] at memberEval
            have resultEq : result = bindings :=
              List.mem_singleton.mp memberEval
            subst resultEq
            simp only [resolveFreshName_mapBindings, resolved,
              applyBindings_mapPattern, checkFreshness_mapPattern]
            rw [if_pos fresh]
            exact List.mem_singleton.mpr rfl
          · rw [if_neg fresh] at memberEval
            cases memberEval
  | relationQuery relation arguments =>
      have memberEval : result ∈ relationQueryStep RelationEnv.empty
          language bindings relation arguments := member
      exact mem_relationQueryStep_empty_map symbols relationFixesEq language
        (mapLanguageDef symbols language) bindings relation arguments memberEval

/-- The evaluator with no external relation does not read its language
argument, so it is monotone from the image of the source into the target. -/
theorem engineBasePremises_empty_mono (first second : LanguageDef)
    (bindings : Bindings) (premise : Premise) (result : Bindings)
    (member : result ∈ engineBasePremises RelationEnv.empty first bindings premise) :
    result ∈ engineBasePremises RelationEnv.empty second bindings premise :=
  engineBasePremises_language_agnostic RelationEnv.empty first second bindings premise ▸ member

/-- **One-step reduction is preserved along every structural presentation
morphism that fixes the built-in relation name**, for the evaluator with no
external relation. -/
theorem step_map_default {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    (relationFixesEq : morphism.symbols.relation "eq" = "eq")
    {pattern next : Pattern}
    (step : Step (engineBasePremises RelationEnv.empty) source.language pattern next) :
    Step (engineBasePremises RelationEnv.empty) target.language
      (mapPattern morphism.symbols pattern) (mapPattern morphism.symbols next) :=
  step_map_of_structuralMorphism morphism
    (engineBasePremises_empty_maps_results morphism.symbols relationFixesEq)
    (engineBasePremises_empty_mono _ _) step

end Mettapedia.GSLT.LanguageDef.SymbolMapSimulation
