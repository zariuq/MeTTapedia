import Mettapedia.OSLF.MeTTaIL.ReferenceStepDisciplines
import Mettapedia.GSLT.LanguageDef.BindingCollectionEquationFamily
import Mettapedia.GSLT.LanguageDef.WellSortedOccurrenceReplacement
import Mathlib.Data.List.Forall2
import Mettapedia.OSLF.MeTTaIL.CanonicalRenaming
import Mettapedia.OSLF.MeTTaIL.ReferenceStepEquations
import Mettapedia.GSLT.LanguageDef.BagNormalFormSection
import Mettapedia.GSLT.LanguageDef.TypedPartialSpineRecovery
import Mathlib.Logic.Relation
import Mathlib.Data.List.Permutation
import Mettapedia.OSLF.MeTTaIL.Complete.Coherence
import Mettapedia.OSLF.MeTTaIL.LawNormalTyping

/-!
# Deciding the declared equations of a bag presentation

For admissible open terms, equality of the computed normal forms is equivalent
to the generated equation relation. Both implications use the actual declared
bag laws: generator invariance and the normalization path.

The final namespace also treats retained authored equations whose matching
and substitutions preserve that normal form. Its exact source agreement is
on the admissible fibre. A separate invariant covers all raw intermediates
and establishes agreement with the unrestricted raw source relation at
admissible endpoints. The actual source rows remain retained throughout.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.BagNormalForm
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics

variable {language : LanguageDef} {bag : GrammarRule} {unit : Option String}

/-- Two or more surviving components retain their bag wrapper. -/
theorem collapse_eq_bag_of_length (unit : String) (elements : List Pattern)
    (many : 2 ≤ elements.length) :
    collapse unit elements = .collection .hashBag elements none := by
  cases elements with
  | nil => simp at many
  | cons first rest =>
      cases rest with
      | nil => simp at many
      | cons second tail => rfl

/-- Bag shape depends on multiplicity, without evaluating the sorting order. -/
theorem normalizeBag_isBagNode_of_length (unit : String) (elements : List Pattern)
    (many : 2 ≤ (bagContents unit elements).length) :
    IsBagNode (normalizeBag (some unit) elements) := by
  refine ⟨Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns (bagContents unit elements), ?_⟩
  exact collapse_eq_bag_of_length unit _ (by simpa using many)

/-- The constructive normalization path is an equation derivation. -/
theorem equationEquiv_normalForm (laws : BareBagTheory language bag unit)
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {pattern : Pattern}
    (admissible : Admissible language free bound type pattern)
    (collectionless : collectionFree type = true) :
    EquationEquiv base language pattern (normalForm unit pattern) := by
  exact Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
    (path_normalForm laws base pattern admissible collectionless)

/-- Exact equation adequacy of normalization, including open binding contexts. -/
theorem equationEquiv_iff_normalForm_eq (laws : BareBagTheory language bag unit)
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {left right : Pattern}
    (leftAdmissible : Admissible language free bound type left)
    (rightAdmissible : Admissible language free bound type right)
    (collectionless : collectionFree type = true) :
    EquationEquiv base language left right ↔ normalForm unit left = normalForm unit right := by
  constructor
  · exact normalForm_eq_of_equationEquiv laws.toBagTheory
  · intro equal
    exact .trans _ _ _ (equationEquiv_normalForm laws base leftAdmissible collectionless)
      (equal ▸ (equationEquiv_normalForm laws base rightAdmissible collectionless).symm)

/-- A decision procedure for the authored equation theory on its admissible terms. -/
def decideEquationEquiv (laws : BareBagTheory language bag unit)
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {left right : Pattern}
    (leftAdmissible : Admissible language free bound type left)
    (rightAdmissible : Admissible language free bound type right)
    (collectionless : collectionFree type = true) : Decidable (EquationEquiv base language left right) :=
  decidable_of_iff (normalForm unit left = normalForm unit right)
    (equationEquiv_iff_normalForm_eq laws base leftAdmissible rightAdmissible collectionless).symm

end Mettapedia.GSLT.LanguageDef.BagNormalForm

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.WellSorted Mettapedia.GSLT.LanguageDef.EquationSemantics

mutual
  private theorem grammar_hasType {source target : LanguageDef}
      (same : target.terms = source.terms) {free : FreeTypeContext} {bound : List TypeExpr}
      {pattern : Pattern} {type : TypeExpr} (typed : HasType source free bound pattern type) :
      HasType target free bound pattern type := by
    cases typed with
    | bvar lookup => exact .bvar lookup
    | fvar lookup => exact .fvar lookup
    | constructor member ordinary arguments =>
        exact .constructor (same ▸ member) ordinary (grammar_arguments same arguments)
    | lambda body => exact .lambda (grammar_hasType same body)
    | multiLambda body => exact .multiLambda (grammar_hasType same body)
    | subst body replacement => exact .subst (grammar_hasType same body) (grammar_hasType same replacement)
    | collection elements => exact .collection (grammar_elements same elements)
    | collectionConstructor member shape elements =>
        exact .collectionConstructor (same ▸ member) shape (grammar_elements same elements)

  private theorem grammar_arguments {source target : LanguageDef}
      (same : target.terms = source.terms) {free : FreeTypeContext} {bound : List TypeExpr}
      {patterns : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes source free bound patterns parameters) :
      ArgumentsHaveTypes target free bound patterns parameters := by
    cases typed with
    | nil => exact .nil
    | cons represented type first rest =>
        exact .cons represented type (grammar_hasType same first) (grammar_arguments same rest)

  private theorem grammar_elements {source target : LanguageDef}
      (same : target.terms = source.terms) {free : FreeTypeContext} {bound : List TypeExpr}
      {patterns : List Pattern} {type : TypeExpr}
      (typed : ElementsHaveType source free bound patterns type) :
      ElementsHaveType target free bound patterns type := by
    cases typed with
    | nil bound type => exact .nil bound type
    | cons first rest => exact .cons (grammar_hasType same first) (grammar_elements same rest)
end

private theorem grammar_admissible {source target : LanguageDef}
    (same : target.terms = source.terms) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {pattern : Pattern} (good : Admissible source free bound type pattern) :
    Admissible target free bound type pattern :=
  ⟨grammar_hasType same good.typed,good.canonical,good.object⟩

private theorem grammar_carrier {source target : LanguageDef}
    (same : target.terms = source.terms) {rule : GrammarRule} {kind : CollType}
    (declaration : CollectionCarrierRule source rule kind) :
    CollectionCarrierRule target rule kind :=
  ⟨same ▸ declaration.authored,declaration.selfSorted⟩

private theorem grammar_algebra {source target : LanguageDef}
    (same : target.terms = source.terms) {rule : GrammarRule} {kind : CollType}
    {algebra : CollectionAlgebra} (declaration : AlgebraRule source rule kind algebra) :
    AlgebraRule target rule kind algebra := by
  refine ⟨same ▸ declaration.authored,declaration.declared,declaration.selfSorted,?_⟩
  intro unit present
  obtain ⟨unitRule,member,label,category,parameters⟩ := declaration.unitAuthored unit present
  exact ⟨unitRule,same ▸ member,label,category,parameters⟩

private theorem grammar_sorted {source target : LanguageDef}
    (same : target.terms = source.terms) {pattern : Pattern} {sort : String}
    (typed : SortedAt source pattern sort) : SortedAt target pattern sort := by
  obtain ⟨free,bound,typed⟩ := typed
  exact ⟨free,bound,grammar_hasType same typed⟩

private theorem grammar_collectionTyped {source target : LanguageDef}
    (same : target.terms = source.terms) {rule : GrammarRule} {kind : CollType}
    {elements : List Pattern}
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.CollectionTypedAt source rule kind elements) :
    Mettapedia.GSLT.LanguageDef.WellSorted.CollectionTypedAt target rule kind elements := by
  obtain ⟨parameter,member,elementType,occurs,free,bound,body⟩ := typed
  exact ⟨parameter,member,elementType,occurs,free,bound,grammar_hasType same body⟩

private theorem grammar_derived {source target : LanguageDef}
    (same : target.terms = source.terms) {first second : Pattern}
    (step : DerivedInstance source first second) : DerivedInstance target first second := by
  cases step with
  | bagPerm declaration sorted permutation =>
      exact .bagPerm (same ▸ declaration) (grammar_collectionTyped same sorted) permutation
  | setPerm declaration sorted permutation =>
      exact .setPerm (same ▸ declaration) (grammar_collectionTyped same sorted) permutation
  | setDedup declaration sorted =>
      exact .setDedup (same ▸ declaration) (grammar_collectionTyped same sorted)
  | flatten declaration flat sorted =>
      exact .flatten (grammar_algebra same declaration) flat (grammar_sorted same sorted)
  | singleton declaration flat sorted =>
      exact .singleton (grammar_algebra same declaration) flat (grammar_sorted same sorted)
  | unitElim declaration unit sorted =>
      exact .unitElim (grammar_algebra same declaration) unit (grammar_sorted same sorted)
  | emptyUnit declaration unit sorted =>
      exact .emptyUnit (grammar_algebra same declaration) unit (grammar_sorted same sorted)

private theorem comparison_step {language : LanguageDef} {base : BasePremiseEvaluator}
    {left right : Pattern}
    (step : EquationContextStep base {language with equations := []} left right) :
    EquationContextStep base language left right := by
  cases step with
  | inContext context generator =>
      rcases generator with authoredInstance | derived
      · exact False.elim (no_equationInstance_of_equations_eq_nil rfl _ _ authoredInstance)
      · exact .inContext context (.inr (grammar_derived (source := {language with equations := []}) (target := language) rfl derived))

private theorem comparison_path {language : LanguageDef} {base : BasePremiseEvaluator}
    {left right : Pattern}
    (path : Path base {language with equations := []} left right) :
    Path base language left right := by
  induction path with
  | refl => exact .refl
  | tail _ step earlier => exact earlier.tail (comparison_step step)

/-- An admissible source term reaches the normal form by the actual source's
own derived laws, with every retained authored row still present. -/
theorem source_equiv_normalForm {language : LanguageDef} {bag : GrammarRule} {unit : Option String}
    (laws : BareBagTheory {language with equations := []} bag unit)
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {pattern : Pattern} (good : Admissible language free bound type pattern)
    (collectionless : collectionFree type = true) :
    EquationEquiv base language pattern (normalForm unit pattern) := by
  exact Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
    (comparison_path (path_normalForm laws base pattern (grammar_admissible (source := language) (target := {language with equations := []}) rfl good) collectionless))



open Mettapedia.OSLF.MeTTaIL.Match Mettapedia.OSLF.MeTTaIL.MatchSpec

/-- Ordinary bag matching reconstructs the selected elements up to the
existing list permutation relation. Ambient consistent bindings are retained. -/
theorem matchBag_reconstruct {patterns terms : List Pattern} {bindings extended : Bindings}
    (matched : MatchBagRel patterns none .hashBag terms bindings)
    (correct : ∀ pattern ∈ patterns, Pattern.isMatchCorrect pattern = true)
    (extension : BindingsExtends bindings extended) :
    (patterns.map (applyBindings extended)).Perm terms := by
  induction patterns generalizing terms bindings with
  | nil => cases matched; exact .refl _
  | cons pattern patterns recurse =>
      cases matched with
      | cons index within head tail merged =>
        have headExtended : BindingsExtends _ extended :=
          fun key value found => extension key value (mergeBindings_subsumed_left merged found)
        have tailExtended : BindingsExtends _ extended :=
          fun key value found => extension key value (mergeBindings_subsumed_right merged found)
        have reconstructed := matchRel_correct_of_extends head (correct pattern (by simp)) headExtended
        have later := recurse tail (fun next member => correct next (by simp [member])) tailExtended
        simp only [List.map_cons,reconstructed]
        exact (List.Perm.cons _ later).trans (List.getElem_cons_eraseIdx_perm within)

/-- A first-order value pattern, or a closed bag of such patterns, is enough
for the actual unit rows. This is a row proof condition, not admission authority. -/
def RowPattern (pattern : Pattern) : Prop :=
  Pattern.isMatchCorrect pattern = true ∨
    ∃ elements, pattern = .collection .hashBag elements none ∧
      ∀ element ∈ elements, Pattern.isMatchCorrect element = true

/-- A row pattern holds no binder. -/
theorem RowPattern.binderFree {pattern : Pattern} (row : RowPattern pattern) :
    Mettapedia.OSLF.MeTTaIL.Match.binderFree pattern = true := by
  rcases row with exact | ⟨elements, rfl, correct⟩
  · exact Mettapedia.OSLF.MeTTaIL.Match.binderFree_of_isMatchCorrectAux _ exact
  · have every : ∀ items : List Pattern, (∀ item ∈ items, Pattern.isMatchCorrect item = true) →
        Mettapedia.OSLF.MeTTaIL.Match.binderFreeList items = true := by
      intro items
      induction items with
      | nil => intro _; rfl
      | cons item items inductionHypothesis =>
          intro all
          simp only [Mettapedia.OSLF.MeTTaIL.Match.binderFreeList, Bool.and_eq_true]
          exact ⟨Mettapedia.OSLF.MeTTaIL.Match.binderFree_of_isMatchCorrectAux _ (all item (by simp)),
            inductionHypothesis fun other member => all other (by simp [member])⟩
    simpa [Mettapedia.OSLF.MeTTaIL.Match.binderFree] using every elements correct

/-- On object sources, actual ordinary matching reconstructs the normal form.
The object premise is essential: raw matching ignores the target tail field. -/
theorem match_normalForm {unit : Option String} {pattern subject : Pattern} {bindings : Bindings}
    (row : RowPattern pattern) (matched : bindings ∈ matchPattern pattern subject)
    (object : isObjectPattern subject = true) :
    normalForm unit subject = normalForm unit (applyBindings bindings pattern) := by
  rcases row with exactPattern | ⟨elements,rfl,correct⟩
  · rw [matchPattern_correct matched exactPattern]
  · have relational := matchPattern_sound matched
    cases relational with
    | collection _ bagMatch =>
      simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_iff_eq_none] at object
      obtain ⟨rfl,_⟩ := object
      have permutation := matchBag_reconstruct bagMatch correct (fun _ _ found => found)
      simp only [applyBindings, normalForm_bag, List.append_nil]
      exact (normalizeBag_perm unit (permutation.map (normalForm unit))).symm

/-- Concrete premise-free rows are checked both for matching reconstruction
and for their substitution-level normal-form equation. -/
theorem equationInstance_normalForm {language : LanguageDef} {unit : Option String}
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm unit (applyBindings bindings row.left) =
          normalForm unit (applyBindings bindings row.right))
    {base : BasePremiseEvaluator} {source target : Pattern}
    (object : isObjectPattern source = true) (step : EquationInstance base language source target) :
    normalForm unit source = normalForm unit target := by
  obtain ⟨fuel,step⟩ := step
  cases step with
  | forward member _ matched premises applied =>
    obtain ⟨empty,leftRow,_,invariant⟩ := rows _ member
    rw [empty] at premises
    cases premises
    rw [← applied]
    exact (match_normalForm leftRow matched object).trans (invariant _)
  | reverse member _ matched premises applied =>
    obtain ⟨empty,_,rightRow,invariant⟩ := rows _ member
    rw [empty] at premises
    cases premises
    rw [← applied]
    exact (match_normalForm rightRow matched object).trans (invariant _).symm
  | declared member notRaw _ =>
    obtain ⟨-,leftRow,rightRow,-⟩ := rows _ member
    simp [readsRaw, leftRow.binderFree, rightRow.binderFree] at notRaw



private theorem object_of_fill (context : Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext)
    (pattern : Pattern) (object : isObjectPattern (context.fill pattern) = true) :
    isObjectPattern pattern = true := by
  induction context with
  | hole => exact object
  | apply label before inner after recurse =>
    simp only [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,
      isObjectPattern,isObjectPatternList_iff] at object
    exact recurse (object _ (by simp))
  | lambda binder inner recurse =>
    exact recurse (by simpa only [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,isObjectPattern] using object)
  | multiLambda arity binders inner recurse =>
    exact recurse (by simpa only [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,isObjectPattern] using object)
  | substBody inner replacement recurse =>
    simp [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,isObjectPattern] at object
  | substReplacement body inner recurse =>
    simp [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,isObjectPattern] at object
  | collection kind before inner after rest recurse =>
    simp only [Mettapedia.OSLF.MeTTaIL.DerivedContexts.OneHoleContext.fill,
      isObjectPattern,Bool.and_eq_true,isObjectPatternList_iff] at object
    exact recurse (object.2 _ (by simp))

/-- The actual contextual source generator preserves normal forms on object
sources. No reconstruction property is asserted for raw open-tail subjects. -/
theorem source_step_normalForm {language : LanguageDef} {bag : GrammarRule} {unit : Option String}
    (laws : BareBagTheory {language with equations := []} bag unit)
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm unit (applyBindings bindings row.left) =
          normalForm unit (applyBindings bindings row.right))
    {base : BasePremiseEvaluator} {left right : Pattern}
    (step : EquationContextStep base language left right) (object : isObjectPattern left = true) :
    normalForm unit left = normalForm unit right := by
  cases step with
  | inContext context generator =>
    apply normalForm_fill_congr unit context
    rcases generator with authoredInstance | derived
    · exact equationInstance_normalForm rows (object_of_fill context _ object) authoredInstance
    · exact normalForm_derived laws.toBagTheory
        (grammar_derived (source := language) (target := {language with equations := []}) rfl derived)

/-- The existing normalization path transports the complete typing derivation
back to the source grammar; actual source rows remain untouched. -/
theorem normalized_admissible {language : LanguageDef} {bag : GrammarRule} {unit : Option String}
    (laws : BareBagTheory {language with equations := []} bag unit)
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {pattern : Pattern} (good : Admissible language free bound type pattern)
    (collectionless : collectionFree type = true) :
    Admissible language free bound type (normalForm unit pattern) := by
  have comparisonGood := grammar_admissible (source := language)
    (target := {language with equations := []}) rfl good
  have path := path_normalForm laws base pattern comparisonGood collectionless
  exact grammar_admissible (source := {language with equations := []}) (target := language) rfl
    (path_admissible laws path comparisonGood collectionless)

/-- Normalization on the genuine admissible source fibre uses the existing
bag normal form, including empty and singleton collapse. -/
def normalizeSource {language : LanguageDef} {bag : GrammarRule} {unit : Option String}
    (laws : BareBagTheory {language with equations := []} bag unit)
    (base : BasePremiseEvaluator) (free : FreeTypeContext) (bound : List TypeExpr)
    (type : TypeExpr) (collectionless : collectionFree type = true)
    (term : {pattern // Admissible language free bound type pattern}) :
    {pattern // Admissible language free bound type pattern} :=
  ⟨normalForm unit term.1,normalized_admissible laws base term.2 collectionless⟩

private theorem fibre_path {language : LanguageDef} {bag : GrammarRule} {unit : Option String}
    (laws : BareBagTheory {language with equations := []} bag unit)
    {base : BasePremiseEvaluator} {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} (collectionless : collectionFree type = true) {left right : Pattern}
    (path : Path base {language with equations := []} left right)
    (firstGood : Admissible language free bound type left)
    (lastGood : Admissible language free bound type right) :
    Relation.ReflTransGen
      (fun (first second : {pattern // Admissible language free bound type pattern}) =>
        EquationContextStep base language first.1 second.1)
      ⟨left,firstGood⟩ ⟨right,lastGood⟩ := by
  revert lastGood
  induction path with
  | refl => intro lastGood; exact .refl
  | @tail middle last previous step earlier =>
    intro lastGood
    have middleGood := grammar_admissible
      (source := {language with equations := []}) (target := language) rfl
      (path_admissible laws previous
        (grammar_admissible (source := language) (target := {language with equations := []}) rfl firstGood)
        collectionless)
    exact (earlier middleGood).tail (comparison_step step)

/-- A source-equational realization of the existing coherence interface on
its actual admissible fibre. The relation is the source's own contextual
step, restricted to that fibre; no raw/fibre equivalence is asserted. -/
theorem sourceNormalizer {language : LanguageDef} {bag : GrammarRule} {unit : Option String}
    (laws : BareBagTheory {language with equations := []} bag unit)
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm unit (applyBindings bindings row.left) =
          normalForm unit (applyBindings bindings row.right))
    (base : BasePremiseEvaluator) (free : FreeTypeContext) (bound : List TypeExpr)
    (type : TypeExpr) (collectionless : collectionFree type = true) :
    Mettapedia.OSLF.MeTTaIL.Complete.Coherence.Normalizer
      (fun (first second : {pattern // Admissible language free bound type pattern}) =>
        EquationContextStep base language first.1 second.1)
      (normalizeSource laws base free bound type collectionless) where
  sound term := by
    have comparisonGood := grammar_admissible (source := language)
      (target := {language with equations := []}) rfl term.2
    exact Relation.EqvGen.reflTransGen_le_eqvGen _ _ _
      (fibre_path laws collectionless (path_normalForm laws base term.1 comparisonGood collectionless)
        term.2 (normalized_admissible laws base term.2 collectionless))
  canonical first second step :=
    Subtype.ext (source_step_normalForm laws rows step first.2.object)

/-- Normal-form equality exactly decides the equivalence generated by actual
source steps within the admissible fibre. -/
theorem source_fibre_equiv_iff_normalForm_eq {language : LanguageDef} {bag : GrammarRule}
    {unit : Option String} (laws : BareBagTheory {language with equations := []} bag unit)
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm unit (applyBindings bindings row.left) =
          normalForm unit (applyBindings bindings row.right))
    (base : BasePremiseEvaluator) (free : FreeTypeContext) (bound : List TypeExpr)
    (type : TypeExpr) (collectionless : collectionFree type = true)
    (left right : {pattern // Admissible language free bound type pattern}) :
    Relation.EqvGen
      (fun (first second : {pattern // Admissible language free bound type pattern}) =>
        EquationContextStep base language first.1 second.1) left right ↔
      normalForm unit left.1 = normalForm unit right.1 := by
  let certified := sourceNormalizer laws rows base free bound type collectionless
  constructor
  · intro related
    exact congrArg Subtype.val (certified.eqvGen_eq related)
  · intro same
    have sameNormal : normalizeSource laws base free bound type collectionless left =
        normalizeSource laws base free bound type collectionless right := Subtype.ext same
    exact .trans _ _ _ (certified.sound left) (sameNormal ▸ (certified.sound right).symm)

/-- Singleton collapse is the same existing bag normal form on arbitrary
components; no typing or interpretation hypothesis is used here. -/
theorem normalForm_singleton (unit : String) (pattern : Pattern) :
    normalForm (some unit) (.collection .hashBag [pattern] none) =
      normalForm (some unit) pattern := by
  rw [normalForm_bag]
  simp only [List.map_cons,List.map_nil,normalizeBag]
  have normal := rootNormal_normalForm unit pattern
  generalize normalForm (some unit) pattern = image at normal ⊢
  by_cases isUnit : image = .apply unit []
  · subst isUnit
    simp [bagContents,splice,collapse]
  · by_cases isBag : IsBagNode image
    · obtain ⟨components,rfl⟩ := isBag
      obtain ⟨sorted,long,plain⟩ := normal components rfl
      have contents : bagContents unit [.collection .hashBag components none] = components := by
        simp only [bagContents,List.flatMap_cons,List.flatMap_nil,List.append_nil,splice_bag]
        apply List.filter_eq_self.mpr
        intro component member
        simpa using (plain component member).1
      rw [contents,sorted]
      match components,long with
      | first :: second :: rest,_ => rfl
    · have contents : bagContents unit [image] = [image] := by
        simp [bagContents,splice_of_not_bag isBag,isUnit]
      rw [contents,sortPatterns_singleton]
      rfl

/-- The two actual retained wrapper-unit rows are invariant under every
binding substitution, including substitutions containing arbitrary terms. -/
theorem normalForm_insert_unit (unit : String) (before after : List Pattern) :
    normalForm (some unit) (.collection .hashBag (before ++ .apply unit [] :: after) none) =
      normalForm (some unit) (.collection .hashBag (before ++ after) none) := by
  rw [normalForm_bag,normalForm_bag]
  apply normalizeBag_contents_perm
  simp only [List.map_append,List.map_cons,bagContents_append]
  rw [bagContents_cons unit (normalForm (some unit) (.apply unit []))]
  have noUnit : bagContents unit [normalForm (some unit) (.apply unit [])] = [] := by
    simp [normalForm,normalFormList,bagContents,splice]
  rw [noUnit,List.nil_append]

#print axioms normalForm_singleton
#print axioms normalForm_insert_unit

#print axioms source_equiv_normalForm
#print axioms matchBag_reconstruct
#print axioms match_normalForm
#print axioms equationInstance_normalForm
#print axioms source_step_normalForm
#print axioms normalized_admissible
#print axioms sourceNormalizer
#print axioms source_fibre_equiv_iff_normalForm_eq
end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations
open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.WellSorted Mettapedia.GSLT.LanguageDef.EquationSemantics

/- The projection below is an internal observer for the raw equation
relation. It is not installed as a source or execution normalization pass. -/
mutual
  private def eraseTails : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar metavariable => .fvar metavariable
    | .apply label arguments => .apply label (eraseTailsList arguments)
    | .lambda binder body => .lambda binder (eraseTails body)
    | .multiLambda arity binders body => .multiLambda arity binders (eraseTails body)
    | .subst body replacement => .subst (eraseTails body) (eraseTails replacement)
    | .collection kind elements _ => .collection kind (eraseTailsList elements) none
  private def eraseTailsList : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => eraseTails pattern :: eraseTailsList patterns
end

@[simp] private theorem eraseTailsList_map (patterns : List Pattern) :
    eraseTailsList patterns = patterns.map eraseTails := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns recurse => simp only [eraseTailsList,List.map_cons,recurse]

private theorem eraseTails_object {pattern : Pattern}
    (object : isObjectPattern pattern = true) : eraseTails pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar metavariable => rfl
  | happly label arguments recurse =>
      simp only [isObjectPattern,isObjectPatternList_iff] at object
      simp only [eraseTails,eraseTailsList_map]
      congr 1
      have fixed : arguments.map eraseTails = arguments.map id :=
        List.map_congr_left (fun pattern member => recurse pattern member (object pattern member))
      simpa only [List.map_id] using fixed
  | hlambda binder body recurse =>
      exact congrArg (Pattern.lambda binder) (recurse object)
  | hmultiLambda arity binders body recurse =>
      exact congrArg (Pattern.multiLambda arity binders) (recurse object)
  | hsubst body replacement bodyIH replacementIH => simp [isObjectPattern] at object
  | hcollection kind elements rest recurse =>
      simp only [isObjectPattern,Bool.and_eq_true,Option.isNone_iff_eq_none,isObjectPatternList_iff] at object
      rcases object with ⟨rfl,objects⟩
      simp only [eraseTails,eraseTailsList_map]
      congr 1
      have fixed : elements.map eraseTails = elements.map id :=
        List.map_congr_left (fun pattern member => recurse pattern member (objects pattern member))
      simpa only [List.map_id] using fixed

private theorem representation_eraseTails {parameter : TermParam} {argument : Pattern}
    (represented : MatchesParameterRepresentation parameter argument) :
    MatchesParameterRepresentation parameter (eraseTails argument) := by
  cases parameter with
  | simple bodyName type => trivial
  | abstractionNamed binderName bodyName type =>
      obtain ⟨body,rfl⟩ := (matchesParameterRepresentation_abstractionNamed_iff _ _ _ _).mp represented
      simp only [eraseTails,MatchesParameterRepresentation]
  | multiAbstractionNamed binderNames bodyName type =>
      obtain ⟨arity,body,rfl⟩ := (matchesParameterRepresentation_multiAbstractionNamed_iff _ _ _ _).mp represented
      simp only [eraseTails,MatchesParameterRepresentation]

mutual
  private theorem typed_eraseTails {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language free bound pattern type) :
      HasType language free bound (eraseTails pattern) type := by
    cases typed with
    | bvar found => exact .bvar found
    | fvar found => exact .fvar found
    | constructor authored ordinary arguments =>
        simpa only [eraseTails,eraseTailsList_map] using
          HasType.constructor authored ordinary (arguments_eraseTails arguments)
    | lambda body =>
        simpa only [eraseTails] using HasType.lambda (typed_eraseTails body)
    | multiLambda body =>
        simpa only [eraseTails] using HasType.multiLambda (typed_eraseTails body)
    | subst body replacement =>
        simpa only [eraseTails] using HasType.subst (typed_eraseTails body) (typed_eraseTails replacement)
    | collection elements =>
        simpa only [eraseTails,eraseTailsList_map] using
          HasType.collection (rest := none) (elements_eraseTails elements)
    | collectionConstructor authored shape elements =>
        simpa only [eraseTails,eraseTailsList_map] using
          HasType.collectionConstructor (rest := none) authored shape (elements_eraseTails elements)
  private theorem arguments_eraseTails {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {arguments : List Pattern} {parameters : List TermParam}
      (typed : ArgumentsHaveTypes language free bound arguments parameters) :
      ArgumentsHaveTypes language free bound (arguments.map eraseTails) parameters := by
    cases typed with
    | nil => exact .nil
    | cons represented expected head tail =>
        exact .cons (representation_eraseTails represented) expected (typed_eraseTails head)
          (arguments_eraseTails tail)
  private theorem elements_eraseTails {language : LanguageDef} {free : FreeTypeContext}
      {bound : List TypeExpr} {elements : List Pattern} {type : TypeExpr}
      (typed : ElementsHaveType language free bound elements type) :
      ElementsHaveType language free bound (elements.map eraseTails) type := by
    cases typed with
    | nil bound type => exact .nil bound type
    | cons head tail => exact .cons (typed_eraseTails head) (elements_eraseTails tail)
end

private theorem sorted_eraseTails {language : LanguageDef} {pattern : Pattern} {sort : String}
    (sorted : SortedAt language pattern sort) : SortedAt language (eraseTails pattern) sort := by
  obtain ⟨free,bound,typed⟩ := sorted
  exact ⟨free,bound,typed_eraseTails typed⟩

private theorem collectionTyped_eraseTails {language : LanguageDef} {rule : GrammarRule}
    {kind : CollType} {elements : List Pattern}
    (typed : Mettapedia.GSLT.LanguageDef.WellSorted.CollectionTypedAt language rule kind elements) :
    Mettapedia.GSLT.LanguageDef.WellSorted.CollectionTypedAt language rule kind (elements.map eraseTails) := by
  obtain ⟨parameter,member,elementType,occurs,free,bound,body⟩ := typed
  refine ⟨parameter,member,elementType,occurs,free,bound,?_⟩
  simpa only [eraseTails,eraseTailsList_map] using typed_eraseTails body

private theorem derived_eraseTails {language : LanguageDef} {source target : Pattern}
    (step : DerivedInstance language source target) :
    DerivedInstance language (eraseTails source) (eraseTails target) := by
  cases step with
  | bagPerm declaration sorted permutation =>
      have mapped := collectionTyped_eraseTails sorted
      simp only [eraseTails,eraseTailsList_map] at mapped ⊢
      exact .bagPerm declaration mapped (permutation.map eraseTails)
  | setPerm declaration sorted permutation =>
      have mapped := collectionTyped_eraseTails sorted
      simp only [eraseTails,eraseTailsList_map] at mapped ⊢
      exact .setPerm declaration mapped (permutation.map eraseTails)
  | setDedup declaration sorted =>
      have mapped := collectionTyped_eraseTails sorted
      simp only [eraseTails,eraseTailsList_map,List.map_cons] at mapped ⊢
      exact .setDedup declaration mapped
  | flatten declaration flat sorted =>
      have mapped := sorted_eraseTails sorted
      simp only [eraseTails,eraseTailsList_map,List.map_append,List.map_cons] at mapped ⊢
      exact .flatten declaration flat mapped
  | singleton declaration flat sorted =>
      have mapped := sorted_eraseTails sorted
      simp only [eraseTails,eraseTailsList_map,List.map_cons,List.map_nil] at mapped ⊢
      exact .singleton declaration flat mapped
  | unitElim declaration unit sorted =>
      have mapped := sorted_eraseTails sorted
      simp only [eraseTails,eraseTailsList_map,List.map_append,List.map_cons,List.map_nil] at mapped ⊢
      exact .unitElim declaration unit mapped
  | emptyUnit declaration unit sorted =>
      have mapped := sorted_eraseTails sorted
      simp only [eraseTails,eraseTailsList_map,List.map_nil] at mapped ⊢
      exact .emptyUnit declaration unit mapped

private def eraseTailsContext : OneHoleContext → OneHoleContext
  | .hole => .hole
  | .apply label before inner after =>
      .apply label (before.map eraseTails) (eraseTailsContext inner) (after.map eraseTails)
  | .lambda binder inner => .lambda binder (eraseTailsContext inner)
  | .multiLambda arity binders inner => .multiLambda arity binders (eraseTailsContext inner)
  | .substBody inner replacement => .substBody (eraseTailsContext inner) (eraseTails replacement)
  | .substReplacement body inner => .substReplacement (eraseTails body) (eraseTailsContext inner)
  | .collection kind before inner after _ =>
      .collection kind (before.map eraseTails) (eraseTailsContext inner) (after.map eraseTails) none

private theorem eraseTails_fill (context : OneHoleContext) (pattern : Pattern) :
    eraseTails (context.fill pattern) = (eraseTailsContext context).fill (eraseTails pattern) := by
  induction context with
  | hole => rfl
  | apply label before inner after recurse =>
      simp only [OneHoleContext.fill,eraseTails,eraseTailsList_map,eraseTailsContext,
        List.map_append,List.map_cons,recurse]
  | lambda binder inner recurse => simp only [OneHoleContext.fill,eraseTails,eraseTailsContext,recurse]
  | multiLambda arity binders inner recurse => simp only [OneHoleContext.fill,eraseTails,eraseTailsContext,recurse]
  | substBody inner replacement recurse => simp only [OneHoleContext.fill,eraseTails,eraseTailsContext,recurse]
  | substReplacement body inner recurse => simp only [OneHoleContext.fill,eraseTails,eraseTailsContext,recurse]
  | collection kind before inner after rest recurse =>
      simp only [OneHoleContext.fill,eraseTails,eraseTailsList_map,eraseTailsContext,
        List.map_append,List.map_cons,recurse]

open Mettapedia.OSLF.MeTTaIL.MatchSpec

private def eraseBindings (bindings : Bindings) : Bindings :=
  bindings.map fun entry => (entry.1,eraseTails entry.2)

private theorem eraseBindings_find (bindings : Bindings) (metavariable : String) :
    (eraseBindings bindings).find? (·.1 == metavariable) =
      (bindings.find? (·.1 == metavariable)).map (fun entry => (entry.1,eraseTails entry.2)) := by
  simp only [eraseBindings,List.find?_map,Function.comp_def]

private theorem erase_applyBindings_fvar (bindings : Bindings) (metavariable : String) :
    eraseTails (applyBindings bindings (.fvar metavariable)) =
      applyBindings (eraseBindings bindings) (.fvar metavariable) := by
  simp only [applyBindings,eraseBindings_find]
  cases found : bindings.find? (·.1 == metavariable) with
  | none => simp only [Option.map_none,eraseTails]
  | some entry => cases entry; simp only [Option.map_some]

private theorem correctList_members (patterns : List Pattern) :
    isMatchCorrectListAux patterns = true ↔
      ∀ pattern ∈ patterns, Pattern.isMatchCorrect pattern = true := by
  induction patterns with
  | nil => simp [isMatchCorrectListAux]
  | cons pattern patterns recurse =>
      simp only [isMatchCorrectListAux,Bool.and_eq_true,Pattern.isMatchCorrect,
        List.forall_mem_cons] at recurse ⊢
      exact and_congr_right (fun _ => recurse)

private theorem erase_applyBindings_correct (bindings : Bindings) {pattern : Pattern}
    (correct : Pattern.isMatchCorrect pattern = true) :
    eraseTails (applyBindings bindings pattern) = applyBindings (eraseBindings bindings) pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp only [applyBindings,eraseTails]
  | hfvar metavariable => exact erase_applyBindings_fvar bindings metavariable
  | happly label arguments recurse =>
      have each := (correctList_members arguments).mp correct
      simp only [applyBindings,eraseTails,eraseTailsList_map,List.map_map]
      congr 1
      exact List.map_congr_left (fun pattern member => recurse pattern member (each pattern member))
  | hlambda binder body recurse => simp [Pattern.isMatchCorrect,isMatchCorrectAux] at correct
  | hmultiLambda arity binders body recurse => simp [Pattern.isMatchCorrect,isMatchCorrectAux] at correct
  | hsubst body replacement bodyIH replacementIH => simp [Pattern.isMatchCorrect,isMatchCorrectAux] at correct
  | hcollection kind elements rest recurse => simp [Pattern.isMatchCorrect,isMatchCorrectAux] at correct

private theorem erase_applyBindings_row (bindings : Bindings) {pattern : Pattern}
    (row : RowPattern pattern) :
    eraseTails (applyBindings bindings pattern) = applyBindings (eraseBindings bindings) pattern := by
  rcases row with correct | ⟨elements,rfl,correct⟩
  · exact erase_applyBindings_correct bindings correct
  · simp only [applyBindings,eraseTails,eraseTailsList_map,List.append_nil,List.map_map]
    congr 1
    exact List.map_congr_left (fun pattern member => erase_applyBindings_correct bindings (correct pattern member))

/-- The actual matcher preserves the internal observer even on raw subjects
whose tail annotation is ignored by ordinary bag matching. -/
private theorem match_tailInvariant {unit : Option String} {pattern subject : Pattern} {bindings : Bindings}
    (row : RowPattern pattern) (matched : bindings ∈ matchPattern pattern subject) :
    normalForm unit (eraseTails subject) =
      normalForm unit (eraseTails (applyBindings bindings pattern)) := by
  rcases row with correct | ⟨elements,rfl,correct⟩
  · rw [matchPattern_correct matched correct]
  · have relational := matchPattern_sound matched
    cases relational with
    | collection _ bagMatch =>
      have permutation := matchBag_reconstruct bagMatch correct (fun _ _ found => found)
      simp only [eraseTails,eraseTailsList_map,applyBindings,List.append_nil,normalForm_bag,List.map_map]
      simpa only [List.map_map,Function.comp_def] using
        (normalizeBag_perm unit (permutation.map (fun pattern => normalForm unit (eraseTails pattern)))).symm

private theorem equationInstance_tailInvariant {language : LanguageDef} {unit : Option String}
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm unit (applyBindings bindings row.left) =
          normalForm unit (applyBindings bindings row.right))
    {base : BasePremiseEvaluator} {source target : Pattern}
    (step : EquationInstance base language source target) :
    normalForm unit (eraseTails source) = normalForm unit (eraseTails target) := by
  obtain ⟨fuel,step⟩ := step
  cases step with
  | forward member _ matched premises applied =>
      obtain ⟨empty,leftRow,rightRow,invariant⟩ := rows _ member
      rw [empty] at premises
      cases premises
      rw [← applied]
      apply (match_tailInvariant leftRow matched).trans
      rw [erase_applyBindings_row _ leftRow,erase_applyBindings_row _ rightRow]
      exact invariant _
  | reverse member _ matched premises applied =>
      obtain ⟨empty,leftRow,rightRow,invariant⟩ := rows _ member
      rw [empty] at premises
      cases premises
      rw [← applied]
      apply (match_tailInvariant rightRow matched).trans
      rw [erase_applyBindings_row _ rightRow,erase_applyBindings_row _ leftRow]
      exact (invariant _).symm
  | declared member notRaw _ =>
      obtain ⟨-,leftRow,rightRow,-⟩ := rows _ member
      simp [readsRaw, leftRow.binderFree, rightRow.binderFree] at notRaw

/-- Actual raw equation equivalence preserves the existing normal form at
object endpoints. The proof uses an internal invariant on all intermediates;
it does not alter the matcher or install tail erasure operationally. -/
theorem source_normalForm_eq_of_equationEquiv {language : LanguageDef} {bag : GrammarRule}
    {unit : Option String} (laws : BagTheory {language with equations := []} bag unit)
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm unit (applyBindings bindings row.left) =
          normalForm unit (applyBindings bindings row.right))
    {base : BasePremiseEvaluator} {left right : Pattern}
    (leftObject : isObjectPattern left = true) (rightObject : isObjectPattern right = true)
    (related : EquationEquiv base language left right) :
    normalForm unit left = normalForm unit right := by
  have invariant := equationEquiv_invariant (fun pattern => normalForm unit (eraseTails pattern))
    (fun context first second same => by
      rw [eraseTails_fill,eraseTails_fill]
      exact normalForm_fill_congr unit (eraseTailsContext context) same)
    (fun source target generator => by
      rcases generator with authored | derived
      · exact equationInstance_tailInvariant rows authored
      · exact normalForm_derived laws
          (grammar_derived (source := language) (target := {language with equations := []}) rfl
            (derived_eraseTails derived))) related
  simpa only [eraseTails_object leftObject,eraseTails_object rightObject] using invariant

/-- Soundness and reflection against the actual unrestricted raw source
relation, for admissible endpoints of a collection-free result type. -/
theorem source_equationEquiv_iff_normalForm_eq {language : LanguageDef} {bag : GrammarRule}
    {unit : Option String} (laws : BareBagTheory {language with equations := []} bag unit)
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm unit (applyBindings bindings row.left) =
          normalForm unit (applyBindings bindings row.right))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {type : TypeExpr} {left right : Pattern}
    (leftGood : Admissible language free bound type left)
    (rightGood : Admissible language free bound type right)
    (collectionless : collectionFree type = true) :
    EquationEquiv base language left right ↔ normalForm unit left = normalForm unit right := by
  constructor
  · exact source_normalForm_eq_of_equationEquiv laws.toBagTheory rows leftGood.object rightGood.object
  · intro same
    exact .trans _ _ _ (source_equiv_normalForm laws base leftGood collectionless)
      (same ▸ (source_equiv_normalForm laws base rightGood collectionless).symm)

#print axioms erase_applyBindings_row
#print axioms match_tailInvariant
#print axioms equationInstance_tailInvariant
#print axioms source_normalForm_eq_of_equationEquiv
#print axioms source_equationEquiv_iff_normalForm_eq

#print axioms eraseTails_object
#print axioms typed_eraseTails
#print axioms derived_eraseTails
#print axioms eraseTails_fill
end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.OSLF.MeTTaIL.Match Mettapedia.OSLF.MeTTaIL.MatchSpec

/-- A proof view at the homogeneous algebra's base-sort focus. Empty and
singleton views retain a carrier for matching; this is not data normalization. -/
def view (unitLabel : String) (focus : Pattern) : Pattern :=
  .collection .hashBag (bagContents unitLabel [focus]) none

/-- Reading a root-normal algebra value into components and rebuilding by the
existing algebra collapse returns that value, including the declared unit. -/
theorem collapse_contents {unitLabel : String} {focus : Pattern}
    (normal : RootNormal unitLabel focus) :
    collapse unitLabel (bagContents unitLabel [focus]) = focus := by
  by_cases bagNode : IsBagNode focus
  · obtain ⟨elements, rfl⟩ := bagNode
    obtain ⟨_, many, plain⟩ := normal elements rfl
    have contents : bagContents unitLabel [.collection .hashBag elements none] = elements := by
      simp only [bagContents, List.flatMap_cons, List.flatMap_nil, List.append_nil, splice_bag]
      apply List.filter_eq_self.mpr
      intro element member
      simpa using (plain element member).1
    rw [contents, collapse_eq_bag_of_length unitLabel elements many]
  · by_cases isUnit : focus = .apply unitLabel []
    · subst focus
      simp [bagContents, splice, collapse]
    · simp [bagContents, splice_of_not_bag bagNode, isUnit, collapse]

/-- Each selected component has the same complete local typing and metadata
as the homogeneous focus. The residual's outer carrier is not collapsed. -/
theorem component_admissible {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {focus component : Pattern}
    (good : Admissible language free bound (.base bag.category) focus)
    (member : component ∈ bagContents unitLabel [focus]) :
    Admissible language free bound (.base bag.category) component := by
  have selected : component ∈ splice focus := by
    exact (List.mem_filter.mp (by simpa only [bagContents, List.flatMap_cons,
      List.flatMap_nil, List.append_nil] using member)).1
  by_cases bagNode : IsBagNode focus
  · obtain ⟨elements, rfl⟩ := bagNode
    have inElements : component ∈ elements := by simpa using selected
    have comparisonGood := grammar_admissible (source := language)
      (target := {language with equations := []}) rfl good
    obtain ⟨_, _, typed⟩ := bag_typing laws.toBareBagPresentation comparisonGood.typed rfl
    refine ⟨grammar_hasType (source := {language with equations := []}) (target := language) rfl
      (elementsHaveType_iff.mp typed component inElements), ?_, ?_⟩
    · have all : Pattern.hasCanonicalBinderMetadataList elements = true := by
        simpa [Pattern.hasCanonicalBinderMetadata] using good.canonical
      exact hasCanonicalBinderMetadataList_iff.mp all component inElements
    · have all : isObjectPatternList elements = true := by
        simpa [isObjectPattern] using good.object
      exact isObjectPatternList_iff.mp all component inElements
  · rw [splice_of_not_bag bagNode] at selected
    exact List.mem_singleton.mp selected ▸ good

/-- Reading the full normal form of a bag as components returns its existing
sorted flattened contents; no outer data carrier is normalized here. -/
theorem normalForm_bag_contents (unitLabel : String) (elements : List Pattern) :
    bagContents unitLabel [normalForm (some unitLabel) (.collection .hashBag elements none)] =
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns
        (bagContents unitLabel (elements.map (normalForm (some unitLabel)))) := by
  rw [normalForm_bag]
  simp only [normalizeBag]
  apply bagContents_collapse
  intro component member
  apply bagContents_spec (elements := elements.map (normalForm (some unitLabel)))
  · intro element inElements
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp inElements
    exact rootNormal_normalForm unitLabel original
  · exact mem_sortPatterns.mp member

private theorem source_bag_element {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern} {element : Pattern}
    (good : Admissible language free bound (.base bag.category) (.collection .hashBag elements none))
    (member : element ∈ elements) :
    Admissible language free bound (.base bag.category) element := by
  have comparisonGood := grammar_admissible (source := language)
    (target := {language with equations := []}) rfl good
  obtain ⟨_, _, typed⟩ := bag_typing laws.toBareBagPresentation comparisonGood.typed rfl
  refine ⟨grammar_hasType (source := {language with equations := []}) (target := language) rfl
    (elementsHaveType_iff.mp typed element member), ?_, ?_⟩
  · exact hasCanonicalBinderMetadataList_iff.mp
      (by simpa [Pattern.hasCanonicalBinderMetadata] using good.canonical) element member
  · exact isObjectPatternList_iff.mp (by simpa [isObjectPattern] using good.object) element member

/-- Each flattened component is read from an actual original subterm, not
from an invented canonical child index. Its source zipper crosses only bag
carriers; local scopes, constructor boundaries and complete typing remain. -/
theorem component_source_origin {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} :
    ∀ (source : Pattern) {component : Pattern},
      Admissible language free bound (.base bag.category) source →
      component ∈ bagContents unitLabel [normalForm (some unitLabel) source] →
      ∃ (original : Pattern) (context : OneHoleContext), Admissible language free bound (.base bag.category) original ∧
        context.fill original = source ∧ normalForm (some unitLabel) original = component ∧
        ∀ replacement, HasType language free bound replacement (.base bag.category) →
          HasType language free bound (context.fill replacement) (.base bag.category)
  | source, component, good, member => by
    by_cases isBag : IsBagNode source
    · obtain ⟨elements, rfl⟩ := isBag
      rw [normalForm_bag_contents] at member
      have contentMember := mem_sortPatterns.mp member
      simp only [bagContents, List.mem_filter, List.mem_flatMap, List.mem_map,
        decide_eq_true_eq] at contentMember
      obtain ⟨⟨_, ⟨element, elementMember, rfl⟩, spliced⟩, notUnit⟩ := contentMember
      have inside : component ∈ bagContents unitLabel [normalForm (some unitLabel) element] := by
        simp only [bagContents, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_filter,
          decide_eq_true_eq]
        exact ⟨spliced, notUnit⟩
      obtain ⟨original, inner, originalGood, innerFill, image, rebuild⟩ :=
        component_source_origin laws element (source_bag_element laws good elementMember) inside
      obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp elementMember
      have within := (List.getElem?_eq_some_iff.mp selected).1
      have split : elements.take index ++ element :: elements.drop (index + 1) = elements := by
        rw [← (List.getElem?_eq_some_iff.mp selected).2, List.getElem_cons_drop within]
        exact List.take_append_drop index elements
      refine ⟨original, .collection .hashBag (elements.take index) inner (elements.drop (index + 1)) none,
        originalGood, ?_, image, ?_⟩
      · simp only [OneHoleContext.fill, innerFill, split]
      · intro replacement replacementTyped
        apply grammar_hasType (source := {language with equations := []}) (target := language) rfl
        apply bag_hasType laws.toBareBagPresentation
        apply grammar_elements (source := language) (target := {language with equations := []}) rfl
        apply elementsHaveType_iff.mpr
        intro item itemMember
        simp only [List.mem_append, List.mem_cons] at itemMember
        rcases itemMember with earlier | replaced | later
        · exact (source_bag_element laws good (List.mem_of_mem_take earlier)).typed
        · subst item
          exact rebuild replacement replacementTyped
        · exact (source_bag_element laws good (List.mem_of_mem_drop later)).typed
    · have normalizedNotBag : ¬ IsBagNode (normalForm (some unitLabel) source) := by
        cases source with
        | collection kind elements rest =>
          cases kind <;> cases rest <;>
            simp_all [IsBagNode, normalForm]
        | _ => simp_all [IsBagNode, normalForm]
      have selected : component ∈ splice (normalForm (some unitLabel) source) := by
        exact (List.mem_filter.mp (by simpa only [bagContents, List.flatMap_cons,
          List.flatMap_nil, List.append_nil] using member)).1
      rw [splice_of_not_bag normalizedNotBag] at selected
      have same := List.mem_singleton.mp selected
      exact ⟨source, .hole, good, rfl, same.symm, fun _ typed => typed⟩
termination_by source => sizeOf source

/-- The view is admissible as the declared algebra's base-sort value. -/
theorem view_admissible {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {focus : Pattern}
    (good : Admissible language free bound (.base bag.category) focus) :
    Admissible language free bound (.base bag.category) (view unitLabel focus) := by
  have typed : ElementsHaveType language free bound (bagContents unitLabel [focus])
      (.base bag.category) := elementsHaveType_iff.mpr
    (fun component member => (component_admissible laws good member).typed)
  refine ⟨grammar_hasType (source := {language with equations := []}) (target := language) rfl
    (bag_hasType laws.toBareBagPresentation (grammar_elements (source := language)
      (target := {language with equations := []}) rfl typed)), ?_, ?_⟩
  · change Pattern.hasCanonicalBinderMetadataList _ = true
    exact hasCanonicalBinderMetadataList_iff.mpr
      (fun component member => (component_admissible laws good member).canonical)
  · change (true && isObjectPatternList _) = true
    simp only [Bool.true_and]
    exact isObjectPatternList_iff.mpr
      (fun component member => (component_admissible laws good member).object)

/-- Deleting a selected occurrence leaves collection data, even when no
component or only one component remains. -/
theorem residual_admissible {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {focus : Pattern}
    (good : Admissible language free bound (.base bag.category) focus) (index : Nat) :
    Admissible language free bound (.collection .hashBag (.base bag.category))
      (.collection .hashBag ((bagContents unitLabel [focus]).eraseIdx index) none) := by
  have each : ∀ component ∈ (bagContents unitLabel [focus]).eraseIdx index,
      Admissible language free bound (.base bag.category) component :=
    fun component member => component_admissible laws good (List.mem_of_mem_eraseIdx member)
  refine ⟨.collection (elementsHaveType_iff.mpr fun component member => (each component member).typed), ?_, ?_⟩
  · change Pattern.hasCanonicalBinderMetadataList _ = true
    exact hasCanonicalBinderMetadataList_iff.mpr fun component member => (each component member).canonical
  · change (true && isObjectPatternList _) = true
    simp only [Bool.true_and]
    exact isObjectPatternList_iff.mpr fun component member => (each component member).object

/-- The virtual carrier is a representative obtained by the source's own
empty/singleton laws. This statement requires the actual base-sort role. -/
theorem view_equivalent {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {focus : Pattern}
    (good : Admissible language free bound (.base bag.category) focus)
    (normal : RootNormal unitLabel focus) :
    EquationEquiv base language focus (view unitLabel focus) := by
  have viewGood := view_admissible laws good
  have comparisonGood := grammar_admissible (source := language)
    (target := {language with equations := []}) rfl viewGood
  have path := path_collapse (base := base) laws rfl comparisonGood
  have sourcePath := comparison_path (language := language) path
  rw [collapse_contents normal] at sourcePath
  exact (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ sourcePath).symm

/-- Every admissible source focus has a typed matching representative, with
all retained equation rows still present. -/
theorem normalized_view_equivalent {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source) :
    EquationEquiv base language source (view unitLabel (normalForm (some unitLabel) source)) := by
  exact .trans _ _ _ (source_equiv_normalForm laws base good rfl)
    (view_equivalent laws base (normalized_admissible laws base good rfl)
      (rootNormal_normalForm unitLabel source))

/-- A component position of the virtual carrier is a real occurrence of the
root-normal source focus. The unit has none; a scalar component is at the
root, not at a fabricated collection child. -/
theorem component_origin {unitLabel : String} {focus component : Pattern} {index : Nat}
    (normal : RootNormal unitLabel focus)
    (selected : (bagContents unitLabel [focus])[index]? = some component) :
    ∃ context : OneHoleContext, context.fill component = focus ∧
      ((context = .hole ∧ component = focus ∧ index = 0) ∨
        ∃ elements, focus = .collection .hashBag elements none ∧
          elements[index]? = some component ∧
          context = .collection .hashBag (elements.take index) .hole (elements.drop (index + 1)) none) := by
  by_cases bagNode : IsBagNode focus
  · obtain ⟨elements, rfl⟩ := bagNode
    obtain ⟨_, _, plain⟩ := normal elements rfl
    have contents : bagContents unitLabel [.collection .hashBag elements none] = elements := by
      simp only [bagContents, List.flatMap_cons, List.flatMap_nil, List.append_nil, splice_bag]
      apply List.filter_eq_self.mpr
      intro element member
      simpa using (plain element member).1
    rw [contents] at selected
    refine ⟨.collection .hashBag (elements.take index) .hole (elements.drop (index + 1)) none, ?_,
      .inr ⟨elements, rfl, selected, rfl⟩⟩
    simp only [OneHoleContext.fill]
    exact congrArg (fun values => Pattern.collection .hashBag values none)
      (by rw [← (List.getElem?_eq_some_iff.mp selected).2,
        List.getElem_cons_drop (List.getElem?_eq_some_iff.mp selected).1]
          exact List.take_append_drop index elements)
  · by_cases isUnit : focus = .apply unitLabel []
    · subst focus
      simp [bagContents, splice] at selected
    · have contents : bagContents unitLabel [focus] = [focus] := by
        simp [bagContents, splice_of_not_bag bagNode, isUnit]
      rw [contents] at selected
      have within := (List.getElem?_eq_some_iff.mp selected).1
      have atZero : index = 0 := by simp at within; omega
      subst index
      simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
      subst component
      exact ⟨.hole, rfl, .inl ⟨rfl, rfl, rfl⟩⟩

/-- Matching one component and the exact residual uses the existing ordinary
bag relation. It does not collapse the rest capture into its sole element. -/
theorem match_view_single_rest {unitLabel : String} {focus schema : Pattern} {index : Nat}
    {restName : String} {headBindings bindings : Bindings}
    (within : index < (bagContents unitLabel [focus]).length)
    (head : MatchRel schema (bagContents unitLabel [focus])[index] headBindings)
    (merged : mergeBindings headBindings [(restName,
      .collection .hashBag ((bagContents unitLabel [focus]).eraseIdx index) none)] = some bindings) :
    MatchRel (.collection .hashBag [schema] (some restName)) (view unitLabel focus) bindings := by
  exact .collection (by decide) (.cons index within head .nilRest merged)

/-- Recover an ordinary collection match as an actual typed source
representative. The input is the existing independent bag-matching judgment,
not a certificate asserting source completeness or firing coherence. -/
theorem recover_representative {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {schemas : List Pattern} {rest : Option String} {bindings : Bindings}
    (matched : MatchBagRel schemas rest .hashBag
      (bagContents unitLabel [normalForm (some unitLabel) source]) bindings) :
    ∃ representative, EquationEquiv base language source representative ∧
      Admissible language free bound (.base bag.category) representative ∧
      MatchRel (.collection .hashBag schemas rest) representative bindings := by
  refine ⟨view unitLabel (normalForm (some unitLabel) source),
    normalized_view_equivalent laws base good,
    view_admissible laws (normalized_admissible laws base good rfl), ?_⟩
  exact .collection (by decide) matched

/-- A step performed at the recovered typed carrier is a step modulo the
actual source equations. No converse firing-normalization premise is assumed. -/
theorem stepModulo_of_view_step {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {source target : Pattern} (good : Admissible language free bound (.base bag.category) source)
    (step : Step base language (view unitLabel (normalForm (some unitLabel) source)) target) :
    StepModuloEquations base language source target :=
  ⟨_, target, normalized_view_equivalent laws base good, step, .refl _⟩

/-- Origin transport composes with the existing structural zipper. All outer
constructor and binder frames remain exactly those supplied by that context. -/
theorem component_origin_in_context {unitLabel : String} {focus component : Pattern} {index : Nat}
    (normal : RootNormal unitLabel focus)
    (selected : (bagContents unitLabel [focus])[index]? = some component)
    (outer : OneHoleContext) :
    ∃ context : OneHoleContext,
      (outer.comp context).fill component = outer.fill focus ∧
      Selects component (outer.comp context) (outer.fill focus) := by
  obtain ⟨context, fills, _⟩ := component_origin normal selected
  refine ⟨context, by rw [OneHoleContext.fill_comp, fills], ?_⟩
  rw [← fills, ← OneHoleContext.fill_comp]
  exact Selects.of_fill _ _

#print axioms collapse_contents
#print axioms component_admissible
#print axioms normalForm_bag_contents
#print axioms source_bag_element
#print axioms component_source_origin
#print axioms view_admissible
#print axioms residual_admissible
#print axioms view_equivalent
#print axioms normalized_view_equivalent
#print axioms component_origin
#print axioms match_view_single_rest
#print axioms recover_representative
#print axioms stepModulo_of_view_step
#print axioms component_origin_in_context

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics

/-- A physical source occurrence, with its actual syntax and zipper retained
beside the value read by the existing normalizer. Equal values do not identify
these records or their source addresses. -/
structure SourceOccurrence where
  original : Pattern
  address : List Nat
  context : OneHoleContext
  value : Pattern
  deriving DecidableEq, Repr

namespace SourceOccurrence

def leaf (unitLabel : String) (source : Pattern) : SourceOccurrence :=
  ⟨source, [], .hole, normalForm (some unitLabel) source⟩

def wrap (elements : List Pattern) (index : Nat) (inner : SourceOccurrence) : SourceOccurrence :=
  { inner with
    address := index :: inner.address
    context := .collection .hashBag (elements.take index) inner.context (elements.drop (index + 1)) none }

end SourceOccurrence

/-- Enumerate physical algebra components in source order. Only closed bag
carriers are traversed; constructors, binders and data boundaries stay intact.
Actual unit leaves remain here and are accounted for separately below. -/
def sourceOccurrences (unitLabel : String) : Pattern → List SourceOccurrence
  | .collection .hashBag elements none =>
      elements.attach.zipIdx.flatMap fun pair =>
        (sourceOccurrences unitLabel pair.1.val).map (SourceOccurrence.wrap elements pair.2)
  | source => [SourceOccurrence.leaf unitLabel source]
termination_by source => sizeOf source
decreasing_by
  have smaller := List.sizeOf_lt_of_mem pair.1.property
  simp_wf
  omega

private theorem zipIdx_mapValues {α β : Type} (f : α → β) :
    ∀ (items : List α) (start : Nat),
      (items.map f).zipIdx start = (items.zipIdx start).map (fun pair => (f pair.1,pair.2))
  | [], _ => rfl
  | head :: tail, start => by
      simp only [List.map_cons, List.zipIdx_cons, List.map_cons, zipIdx_mapValues f tail (start + 1)]

private theorem attach_zipIdx_flatMap {α β : Type} (items : List α) (f : α → Nat → List β) :
    items.attach.zipIdx.flatMap (fun pair => f pair.1.val pair.2) =
      items.zipIdx.flatMap (fun pair => f pair.1 pair.2) := by
  have mapped : items.attach.map (fun entry => entry.val) = items := by
    exact List.attach_map_subtype_val items
  conv_rhs => rw [← mapped, zipIdx_mapValues]
  simp only [List.flatMap_map]

/-- The source traversal's child indices are the actual original list
indices, independent of the termination proof's attached membership data. -/
theorem sourceOccurrences_bag (unitLabel : String) (elements : List Pattern) :
    sourceOccurrences unitLabel (.collection .hashBag elements none) =
      elements.zipIdx.flatMap (fun pair =>
        (sourceOccurrences unitLabel pair.1).map (SourceOccurrence.wrap elements pair.2)) := by
  rw [sourceOccurrences]
  exact attach_zipIdx_flatMap elements (fun element index =>
    (sourceOccurrences unitLabel element).map (SourceOccurrence.wrap elements index))

theorem sourceOccurrences_nonbag {unitLabel : String} {source : Pattern}
    (notBag : ¬ IsBagNode source) :
    sourceOccurrences unitLabel source = [SourceOccurrence.leaf unitLabel source] := by
  cases source with
  | collection kind elements rest => cases kind <;> cases rest <;> simp_all [sourceOccurrences, IsBagNode]
  | _ => simp only [sourceOccurrences]


/-- Traversal distinguishes physical addresses before any value sorting or
unit filtering, even when several source leaves have the same value. -/
theorem sourceOccurrences_distinct (unitLabel : String) :
    ∀ source, (sourceOccurrences unitLabel source).Pairwise
      (fun first second => first.address ≠ second.address)
  | source => by
    by_cases isBag : IsBagNode source
    · obtain ⟨elements, rfl⟩ := isBag
      rw [sourceOccurrences_bag, List.pairwise_flatMap]
      constructor
      · intro pair selected
        apply List.pairwise_map.mpr
        have inside := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp selected)
        exact (sourceOccurrences_distinct unitLabel pair.1).imp
          (fun {_ _} different same => different (List.cons.inj same).2)
      · have distinct : (elements.zipIdx).Pairwise
            (fun first second => first.2 ≠ second.2) := by
          apply List.pairwise_map.mp
          change (elements.zipIdx.map Prod.snd).Nodup
          rw [List.zipIdx_map_snd]
          exact List.nodup_range'
        apply distinct.imp
        intro first second different left leftMember right rightMember same
        obtain ⟨firstTag, _, rfl⟩ := List.mem_map.mp leftMember
        obtain ⟨secondTag, _, rfl⟩ := List.mem_map.mp rightMember
        exact different (List.cons.inj same).1
    · rw [sourceOccurrences_nonbag isBag]
      simp
termination_by source => sizeOf source

/-- Every enumerated record carries its real original typed subterm and
source zipper, with no change to the local free or bound typing context. -/
theorem sourceOccurrences_sound {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} :
    ∀ (source : Pattern), Admissible language free bound (.base bag.category) source →
      ∀ occurrence ∈ sourceOccurrences unitLabel source,
        Admissible language free bound (.base bag.category) occurrence.original ∧
          occurrence.context.fill occurrence.original = source ∧
          occurrence.value = normalForm (some unitLabel) occurrence.original ∧
          contextAddress occurrence.context = occurrence.address ∧
          ∀ replacement, HasType language free bound replacement (.base bag.category) →
            HasType language free bound (occurrence.context.fill replacement) (.base bag.category)
  | source, good, occurrence, member => by
    by_cases isBag : IsBagNode source
    · obtain ⟨elements, rfl⟩ := isBag
      rw [sourceOccurrences_bag] at member
      obtain ⟨⟨element, index⟩, selected, mapped⟩ := List.mem_flatMap.mp member
      obtain ⟨inner, inInner, rfl⟩ := List.mem_map.mp mapped
      have atIndex := List.mk_mem_zipIdx_iff_getElem?.mp selected
      have within := (List.getElem?_eq_some_iff.mp atIndex).1
      have elementGood := source_bag_element laws good (List.mem_of_getElem? atIndex)
      obtain ⟨originalGood, fills, image, address, rebuild⟩ :=
        sourceOccurrences_sound laws element elementGood inner inInner
      have split : elements.take index ++ element :: elements.drop (index + 1) = elements := by
        rw [← (List.getElem?_eq_some_iff.mp atIndex).2, List.getElem_cons_drop within]
        exact List.take_append_drop index elements
      refine ⟨originalGood, ?_, image, ?_, ?_⟩
      · simp only [SourceOccurrence.wrap, OneHoleContext.fill, fills, split]
      · simp only [SourceOccurrence.wrap, contextAddress, address, List.length_take,
          Nat.min_eq_left (Nat.le_of_lt within)]
      · intro replacement replacementTyped
        apply grammar_hasType (source := {language with equations := []}) (target := language) rfl
        apply bag_hasType laws.toBareBagPresentation
        apply grammar_elements (source := language) (target := {language with equations := []}) rfl
        apply elementsHaveType_iff.mpr
        intro item itemMember
        simp only [List.mem_append, List.mem_cons] at itemMember
        rcases itemMember with earlier | replaced | later
        · exact (source_bag_element laws good (List.mem_of_mem_take earlier)).typed
        · subst item
          exact rebuild replacement replacementTyped
        · exact (source_bag_element laws good (List.mem_of_mem_drop later)).typed
    · rw [sourceOccurrences_nonbag isBag] at member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨good, rfl, rfl, rfl, fun _ typed => typed⟩
termination_by source => sizeOf source
decreasing_by
  all_goals
    subst_vars
    have smaller := List.sizeOf_lt_of_mem (List.mem_of_getElem? atIndex)
    simp_all
    omega

/-- Physical components omit actual unit leaves, while preserving their
source records in the separate administrative account. -/
def componentOccurrences (unitLabel : String) (source : Pattern) : List SourceOccurrence :=
  (sourceOccurrences unitLabel source).filter fun occurrence => decide (occurrence.value ≠ .apply unitLabel [])

def unitOccurrences (unitLabel : String) (source : Pattern) : List SourceOccurrence :=
  (sourceOccurrences unitLabel source).filter fun occurrence => decide (occurrence.value = .apply unitLabel [])

/-- Sorting transports complete source records, not their values alone. -/
def sortOccurrences (occurrences : List SourceOccurrence) : List SourceOccurrence :=
  occurrences.mergeSort fun first second => decide (patternCode first.value ≤ patternCode second.value)

def normalizedOccurrences (unitLabel : String) (source : Pattern) : List SourceOccurrence :=
  sortOccurrences (componentOccurrences unitLabel source)

theorem sortOccurrences_perm (occurrences : List SourceOccurrence) :
    (sortOccurrences occurrences).Perm occurrences := List.mergeSort_perm _ _

/-- Erasing the sorted tags gives exactly the existing value sorter. -/
theorem sortOccurrences_values (occurrences : List SourceOccurrence) :
    (sortOccurrences occurrences).map SourceOccurrence.value =
      sortPatterns (occurrences.map SourceOccurrence.value) := by
  have ordered : (sortOccurrences occurrences).Pairwise
      (fun first second => patternCode first.value ≤ patternCode second.value) := by
    have sorted := List.pairwise_mergeSort
      (le := fun first second : SourceOccurrence => decide (patternCode first.value ≤ patternCode second.value))
      (fun first second third earlier later => by
        simp only [decide_eq_true_eq] at earlier later ⊢
        exact Nat.le_trans earlier later)
      (fun first second => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Nat.le_total _ _) occurrences
    simpa [sortOccurrences] using sorted
  have imageOrdered : ((sortOccurrences occurrences).map SourceOccurrence.value).Pairwise
      (fun first second => patternCode first ≤ patternCode second) := List.pairwise_map.mpr ordered
  calc
    _ = sortPatterns ((sortOccurrences occurrences).map SourceOccurrence.value) :=
      (sortPatterns_of_sorted imageOrdered).symm
    _ = _ := sortPatterns_eq_of_perm ((sortOccurrences_perm occurrences).map SourceOccurrence.value)

/-- Sorting preserves every source tag and address, including duplicates in
value. This theorem does not identify operational receipt keys. -/
theorem sortOccurrences_addresses (occurrences : List SourceOccurrence) :
    ((sortOccurrences occurrences).map SourceOccurrence.address).Perm
      (occurrences.map SourceOccurrence.address) :=
  (sortOccurrences_perm occurrences).map SourceOccurrence.address


/-- Removing source units commutes with the physical child traversal, and
wrapping a source zipper leaves its value unchanged. -/
theorem componentOccurrences_bag (unitLabel : String) (elements : List Pattern) :
    componentOccurrences unitLabel (.collection .hashBag elements none) =
      elements.zipIdx.flatMap (fun pair =>
        (componentOccurrences unitLabel pair.1).map (SourceOccurrence.wrap elements pair.2)) := by
  rw [componentOccurrences, sourceOccurrences_bag, List.filter_flatMap]
  apply List.flatMap_congr
  intro pair _
  rw [List.filter_map]
  rfl

private theorem flatMap_zipIdx_fst {α β : Type} (items : List α) (f : α → List β) :
    items.zipIdx.flatMap (fun pair => f pair.1) = items.flatMap f := by
  rw [← List.flatMap_map (f := Prod.fst) (g := f), List.zipIdx_map_fst]

private theorem bagContents_flatMap (unitLabel : String) (elements : List Pattern) :
    elements.flatMap (fun element => bagContents unitLabel [normalForm (some unitLabel) element]) =
      bagContents unitLabel (elements.map (normalForm (some unitLabel))) := by
  simp only [bagContents, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.flatMap_map, List.filter_flatMap]

private theorem normalForm_nonbag {unitLabel : String} {source : Pattern}
    (notBag : ¬ IsBagNode source) : ¬ IsBagNode (normalForm (some unitLabel) source) := by
  cases source with
  | collection kind elements rest => cases kind <;> cases rest <;> simp_all [IsBagNode, normalForm]
  | _ => simp_all [IsBagNode, normalForm]

/-- Erasing source tags recovers exactly the multiset of existing normalized
components. Flattening is not allowed to erase duplicate source occurrences. -/
theorem componentOccurrences_values (unitLabel : String) :
    ∀ source, ((componentOccurrences unitLabel source).map SourceOccurrence.value).Perm
      (bagContents unitLabel [normalForm (some unitLabel) source])
  | source => by
    by_cases isBag : IsBagNode source
    · obtain ⟨elements, rfl⟩ := isBag
      rw [componentOccurrences_bag, List.map_flatMap, normalForm_bag_contents]
      have transformed := List.Perm.flatMap_left elements.zipIdx
        (f := fun pair => ((componentOccurrences unitLabel pair.1).map
          (SourceOccurrence.wrap elements pair.2)).map SourceOccurrence.value)
        (g := fun pair => bagContents unitLabel [normalForm (some unitLabel) pair.1])
        (fun pair selected => by
          have inside := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp selected)
          simpa only [List.map_map, SourceOccurrence.wrap, Function.comp_def] using
            componentOccurrences_values unitLabel pair.1)
      apply transformed.trans
      rw [flatMap_zipIdx_fst elements (fun element =>
        bagContents unitLabel [normalForm (some unitLabel) element]), bagContents_flatMap]
      exact (sortPatterns_perm _).symm
    · have normalizedNotBag := normalForm_nonbag (unitLabel := unitLabel) isBag
      rw [componentOccurrences, sourceOccurrences_nonbag isBag]
      rw [bagContents]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [splice_of_not_bag normalizedNotBag]
      simp only [SourceOccurrence.leaf, List.filter_cons, List.filter_nil]
      split <;> simp_all
termination_by source => sizeOf source

private theorem rootContents_sorted {unitLabel : String} {focus : Pattern}
    (normal : RootNormal unitLabel focus) :
    sortPatterns (bagContents unitLabel [focus]) = bagContents unitLabel [focus] := by
  by_cases isBag : IsBagNode focus
  · obtain ⟨elements, rfl⟩ := isBag
    obtain ⟨sorted, _, plain⟩ := normal elements rfl
    have contents : bagContents unitLabel [.collection .hashBag elements none] = elements := by
      simp only [bagContents, List.flatMap_cons, List.flatMap_nil, List.append_nil, splice_bag]
      apply List.filter_eq_self.mpr
      intro component member
      simpa using (plain component member).1
    rw [contents, sorted]
  · by_cases isUnit : focus = .apply unitLabel []
    · subst focus
      simp [bagContents, splice]
    · simp [bagContents, splice_of_not_bag isBag, isUnit]

/-- Sorting complete tags yields the exact existing canonical component
list, with multiplicity; it is not a second value normalizer. -/
theorem normalizedOccurrences_values (unitLabel : String) (source : Pattern) :
    (normalizedOccurrences unitLabel source).map SourceOccurrence.value =
      bagContents unitLabel [normalForm (some unitLabel) source] := by
  rw [normalizedOccurrences, sortOccurrences_values,
    sortPatterns_eq_of_perm (componentOccurrences_values unitLabel source),
    rootContents_sorted (rootNormal_normalForm unitLabel source)]

/-- Every sorted component still has a different physical source address. -/
theorem normalizedOccurrences_distinct (unitLabel : String) (source : Pattern) :
    ((normalizedOccurrences unitLabel source).map SourceOccurrence.address).Nodup := by
  apply (sortOccurrences_addresses (componentOccurrences unitLabel source)).nodup_iff.mpr
  apply List.pairwise_map.mpr
  exact (sourceOccurrences_distinct unitLabel source).filter _

/-- The sorted physical components and actual source-unit administration
partition the original occurrence account without adding a source leaf. -/
theorem occurrence_account (unitLabel : String) (source : Pattern) :
    (normalizedOccurrences unitLabel source ++ unitOccurrences unitLabel source).Perm
      (sourceOccurrences unitLabel source) := by
  apply ((sortOccurrences_perm (componentOccurrences unitLabel source)).append_right
    (unitOccurrences unitLabel source)).trans
  have complement : (fun occurrence : SourceOccurrence => !decide (occurrence.value ≠ .apply unitLabel [])) =
      (fun occurrence => decide (occurrence.value = .apply unitLabel [])) := by
    funext occurrence
    by_cases same : occurrence.value = .apply unitLabel [] <;> simp [same]
  simpa only [componentOccurrences, unitOccurrences, complement] using
    List.filter_append_perm (fun occurrence : SourceOccurrence =>
      decide (occurrence.value ≠ .apply unitLabel [])) (sourceOccurrences unitLabel source)


/-- Every emitted component index has its own source address. Two equal
values at different indices cannot reuse one physical source occurrence. -/
theorem normalizedOccurrences_index_injective (unitLabel : String) (source : Pattern)
    {firstIndex secondIndex : Nat}
    (firstWithin : firstIndex < (normalizedOccurrences unitLabel source).length)
    (secondWithin : secondIndex < (normalizedOccurrences unitLabel source).length) :
    (normalizedOccurrences unitLabel source)[firstIndex].address =
      (normalizedOccurrences unitLabel source)[secondIndex].address ↔ firstIndex = secondIndex := by
  constructor
  · intro same
    have sameAt : ((normalizedOccurrences unitLabel source).map SourceOccurrence.address)[firstIndex]'(by simpa) =
        ((normalizedOccurrences unitLabel source).map SourceOccurrence.address)[secondIndex]'(by simpa) := by
      simpa only [List.getElem_map] using same
    exact (normalizedOccurrences_distinct unitLabel source).getElem_inj_iff.mp sameAt
  · intro same
    subst secondIndex
    rfl

/-- The component count and every value multiplicity are those of the
existing normal-form component list, with no identification of equal tags. -/
theorem normalizedOccurrences_counts (unitLabel : String) (source : Pattern) :
    (normalizedOccurrences unitLabel source).length =
      (bagContents unitLabel [normalForm (some unitLabel) source]).length ∧
      ∀ component, ((normalizedOccurrences unitLabel source).map SourceOccurrence.value).count component =
        (bagContents unitLabel [normalForm (some unitLabel) source]).count component := by
  have values := normalizedOccurrences_values unitLabel source
  exact ⟨by simpa only [List.length_map] using congrArg List.length values,
    fun component => congrArg (List.count component) values⟩

/-- Actual source units remain in the administrative account. They do not
appear as physical components just because matching can insert a unit view. -/
theorem unitOccurrences_value {unitLabel : String} {source : Pattern} {occurrence : SourceOccurrence}
    (member : occurrence ∈ unitOccurrences unitLabel source) : occurrence.value = .apply unitLabel [] :=
  of_decide_eq_true (List.mem_filter.mp member).2

theorem normalizedOccurrences_nonunit {unitLabel : String} {source : Pattern} {occurrence : SourceOccurrence}
    (member : occurrence ∈ normalizedOccurrences unitLabel source) : occurrence.value ≠ .apply unitLabel [] := by
  have before := (sortOccurrences_perm (componentOccurrences unitLabel source)).mem_iff.mp member
  exact of_decide_eq_true (List.mem_filter.mp before).2

/-- Sorted source records retain original and normalized typing, exact
zipper readback and unchanged local scope. This is not a firing certificate. -/
theorem normalizedOccurrences_sound {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {occurrence : SourceOccurrence} (member : occurrence ∈ normalizedOccurrences unitLabel source) :
    Admissible language free bound (.base bag.category) occurrence.original ∧
      Admissible language free bound (.base bag.category) occurrence.value ∧
      occurrence.context.fill occurrence.original = source ∧
      occurrence.value = normalForm (some unitLabel) occurrence.original ∧
      contextAddress occurrence.context = occurrence.address ∧
      ∀ replacement, HasType language free bound replacement (.base bag.category) →
        HasType language free bound (occurrence.context.fill replacement) (.base bag.category) := by
  have before := (sortOccurrences_perm (componentOccurrences unitLabel source)).mem_iff.mp member
  obtain ⟨originalGood, fills, image, address, rebuild⟩ :=
    sourceOccurrences_sound laws source good occurrence (List.mem_filter.mp before).1
  have valueGood := normalized_admissible laws defaultBasePremises originalGood rfl
  rw [← image] at valueGood
  exact ⟨originalGood, valueGood, fills, image, address, rebuild⟩

/-- Source occurrences are conserved exactly when source-unit administration
is included. No derivation identity is selected by this accounting theorem. -/
theorem occurrence_account_length (unitLabel : String) (source : Pattern) :
    (normalizedOccurrences unitLabel source).length + (unitOccurrences unitLabel source).length =
      (sourceOccurrences unitLabel source).length := by
  simpa only [List.length_append] using (occurrence_account unitLabel source).length_eq



/-- Source records stop at physical non-bag leaves. Their stored value is
read from that original syntax by the existing normalizer. -/
theorem sourceOccurrences_leaf_value (unitLabel : String) :
    ∀ source occurrence, occurrence ∈ sourceOccurrences unitLabel source →
      ¬ IsBagNode occurrence.original ∧ occurrence.value = normalForm (some unitLabel) occurrence.original
  | source, occurrence, member => by
    by_cases isBag : IsBagNode source
    · obtain ⟨elements, rfl⟩ := isBag
      rw [sourceOccurrences_bag] at member
      obtain ⟨⟨element,index⟩, selected, mapped⟩ := List.mem_flatMap.mp member
      obtain ⟨inner, inside, rfl⟩ := List.mem_map.mp mapped
      have elementMember := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp selected)
      exact sourceOccurrences_leaf_value unitLabel element inner inside
    · rw [sourceOccurrences_nonbag isBag] at member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨isBag,rfl⟩
termination_by source => sizeOf source

private theorem original_unit_of_nonbag {unitLabel : String} {source : Pattern}
    (notBag : ¬ IsBagNode source)
    (image : normalForm (some unitLabel) source = .apply unitLabel []) : source = .apply unitLabel [] := by
  cases source with
  | apply constructor arguments => cases arguments <;> simp_all [normalForm, normalFormList]
  | collection kind elements rest => cases kind <;> cases rest <;> simp_all [normalForm, IsBagNode]
  | _ => simp_all [normalForm]

/-- The source-unit administration consists of actual original unit leaves,
not source occurrences created to justify a virtual matching representative. -/
theorem unitOccurrences_original {unitLabel : String} {source : Pattern} {occurrence : SourceOccurrence}
    (member : occurrence ∈ unitOccurrences unitLabel source) : occurrence.original = .apply unitLabel [] := by
  obtain ⟨leaf, image⟩ := sourceOccurrences_leaf_value unitLabel source occurrence (List.mem_filter.mp member).1
  apply original_unit_of_nonbag leaf
  exact image.symm.trans (unitOccurrences_value member)

/-- Equal values preserve their two physical source addresses after sorting. -/
theorem duplicate_occurrence_control :
    let source := Pattern.collection .hashBag [.fvar "a",.fvar "a"] none
    (normalizedOccurrences "unit" source).map SourceOccurrence.value = [.fvar "a",.fvar "a"] ∧
      (normalizedOccurrences "unit" source).map SourceOccurrence.address = [[0],[1]] := by cbv

/-- A sorting permutation moves the source tags together with their values. -/
theorem reordered_occurrence_control :
    let source := Pattern.collection .hashBag [.fvar "b",.fvar "a"] none
    (normalizedOccurrences "unit" source).map SourceOccurrence.value = [.fvar "a",.fvar "b"] ∧
      (normalizedOccurrences "unit" source).map SourceOccurrence.address = [[1],[0]] := by cbv

/-- Flattening nested equal values keeps their original paths; the actual
source unit is present only in the separate administrative account. -/
theorem nested_duplicate_unit_control :
    let source := Pattern.collection .hashBag
      [.apply "unit" [], .collection .hashBag [.fvar "a",.fvar "a"] none] none
    (normalizedOccurrences "unit" source).map SourceOccurrence.address = [[1,0],[1,1]] ∧
      (unitOccurrences "unit" source).map SourceOccurrence.address = [[0]] ∧
      (sourceOccurrences "unit" source).length = 3 := by cbv

/-- Empty and unit presentations have equal values but different physical
source accounts. Normalization cannot fabricate a source leaf for the empty
presentation's virtual unit. -/
theorem empty_unit_origin_separator :
    normalForm (some "unit") (.collection .hashBag [] none) = .apply "unit" [] ∧
      sourceOccurrences "unit" (.collection .hashBag [] none) = [] ∧
      normalizedOccurrences "unit" (.apply "unit" []) = [] ∧
      (unitOccurrences "unit" (.apply "unit" [])).length = 1 := by cbv

/-- The physical account does not descend through a constructor boundary. -/
theorem constructor_occurrence_boundary (unitLabel constructorLabel : String) (arguments : List Pattern) :
    sourceOccurrences unitLabel (.apply constructorLabel arguments) =
      [SourceOccurrence.leaf unitLabel (.apply constructorLabel arguments)] :=
  sourceOccurrences_nonbag (by simp [IsBagNode])

#print axioms sourceOccurrences_distinct
#print axioms sourceOccurrences_sound
#print axioms sourceOccurrences_bag
#print axioms sourceOccurrences_nonbag
#print axioms sortOccurrences_perm
#print axioms sortOccurrences_values
#print axioms sortOccurrences_addresses
#print axioms componentOccurrences_bag
#print axioms componentOccurrences_values
#print axioms normalizedOccurrences_values
#print axioms normalizedOccurrences_distinct
#print axioms occurrence_account
#print axioms normalizedOccurrences_index_injective
#print axioms normalizedOccurrences_counts
#print axioms unitOccurrences_value
#print axioms normalizedOccurrences_nonunit
#print axioms normalizedOccurrences_sound
#print axioms occurrence_account_length
#print axioms duplicate_occurrence_control
#print axioms reordered_occurrence_control
#print axioms nested_duplicate_unit_control
#print axioms empty_unit_origin_separator
#print axioms constructor_occurrence_boundary
#print axioms sourceOccurrences_leaf_value
#print axioms unitOccurrences_original

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep Match
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

/-- The existing source-derived normalizer is a normalizer for the original
reference-equation hub on the same admissible fibre. Directed rule premises
need no additional restriction when equation rows are unconditional. -/
theorem reference_sourceNormalizer {language : LanguageDef} {bag : GrammarRule} {unit : Option String}
    (laws : BareBagTheory {language with equations := []} bag unit)
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm unit (applyBindings bindings row.left) =
          normalForm unit (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    (free : FreeTypeContext) (bound : List TypeExpr) (type : TypeExpr)
    (collectionless : collectionFree type = true) :
    Complete.Coherence.Normalizer
      (fun (first second : {pattern // Admissible language free bound type pattern}) =>
        ReferenceStep.EquationStep relEnv language first.1 second.1)
      (normalizeSource laws (engineBasePremises relEnv) free bound type collectionless) := by
  have unconditional : ReferenceStep.UnconditionalEquations language := fun row member => (rows row member).1
  have original := sourceNormalizer laws rows (engineBasePremises relEnv) free bound type collectionless
  refine ⟨?_,?_⟩
  · intro subject
    exact Relation.EqvGen.mono
      (fun _ _ step => (ReferenceStep.equationStep_iff_unconditional unconditional aligned).mp step)
      _ _ (original.sound subject)
  · intro first second step
    exact original.canonical first second
      ((ReferenceStep.equationStep_iff_unconditional unconditional aligned).mpr step)

/-- Soundness and reflection for the actual unrestricted reference
Equivalence at admissible endpoints, retaining the authored equation rows. -/
theorem reference_equivalent_iff_normalForm_eq {language : LanguageDef} {bag : GrammarRule} {unit : Option String}
    (laws : BareBagTheory {language with equations := []} bag unit)
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm unit (applyBindings bindings row.left) =
          normalForm unit (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr} {left right : Pattern}
    (leftGood : Admissible language free bound type left) (rightGood : Admissible language free bound type right)
    (collectionless : collectionFree type = true) :
    ReferenceStep.Equivalent relEnv language left right ↔ normalForm unit left = normalForm unit right :=
  (ReferenceStep.equivalent_iff_unconditional (fun row member => (rows row member).1) aligned).symm.trans
    (source_equationEquiv_iff_normalForm_eq laws rows (engineBasePremises relEnv)
      leftGood rightGood collectionless)

#print axioms reference_sourceNormalizer
#print axioms reference_equivalent_iff_normalForm_eq

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep Match DerivedContexts GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

/-- The existing independent bag match recovers an actual reference-source
presentation. This is sound recovery, not completeness of a component view
for unit-sensitive schemas. -/
theorem recover_reference_presentation {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (unconditional : ReferenceStep.UnconditionalEquations language)
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {schemas : List Pattern} {rest : Option String} {bindings : Bindings}
    (matched : MatchSpec.MatchBagRel schemas rest .hashBag
      (bagContents unitLabel [normalForm (some unitLabel) source]) bindings) :
    ∃ representative,ReferenceStep.Equivalent relEnv language source representative ∧
      Admissible language free bound (.base bag.category) representative ∧
      bindings ∈ matchPattern (.collection .hashBag schemas rest) representative := by
  obtain ⟨representative,converted,typed,ordinary⟩ :=
    recover_representative laws (engineBasePremises relEnv) good matched
  exact ⟨representative,(ReferenceStep.equivalent_iff_unconditional unconditional aligned).mp converted,
    typed,MatchSpec.matchRel_complete ordinary⟩

/-- A normalized component keeps its actual typed source leaf and zipper.
Its value is related to that leaf by original reference equations, rather
than by a fresh semantic relation or an invented occurrence. -/
theorem normalizedOccurrence_reference_source {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (unconditional : ReferenceStep.UnconditionalEquations language)
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {occurrence : SourceOccurrence} (member : occurrence ∈ normalizedOccurrences unitLabel source) :
    Admissible language free bound (.base bag.category) occurrence.original ∧
      Admissible language free bound (.base bag.category) occurrence.value ∧
      occurrence.context.fill occurrence.original = source ∧
      ReferenceStep.Equivalent relEnv language occurrence.original occurrence.value ∧
      contextAddress occurrence.context = occurrence.address ∧
      ∀ replacement,HasType language free bound replacement (.base bag.category) →
        HasType language free bound (occurrence.context.fill replacement) (.base bag.category) := by
  obtain ⟨originalGood,valueGood,fills,image,address,rebuild⟩ := normalizedOccurrences_sound laws good member
  have converted := source_equiv_normalForm laws (engineBasePremises relEnv) originalGood rfl
  rw [← image] at converted
  exact ⟨originalGood,valueGood,fills,
    (ReferenceStep.equivalent_iff_unconditional unconditional aligned).mp converted,address,rebuild⟩

/-- Selecting a tagged component and its exact residual earns both ordinary
source matching at an equivalent representative and the selected physical
source occurrence. Equal component values keep their separate tagged indices. -/
theorem tagged_reference_presentation {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (unconditional : ReferenceStep.UnconditionalEquations language)
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source schema : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {index : Nat} {occurrence : SourceOccurrence} {restName : String} {headBindings bindings : Bindings}
    (selected : (normalizedOccurrences unitLabel source)[index]? = some occurrence)
    (head : MatchSpec.MatchRel schema occurrence.value headBindings)
    (merged : mergeBindings headBindings [(restName,.collection .hashBag
      ((bagContents unitLabel [normalForm (some unitLabel) source]).eraseIdx index) none)] = some bindings) :
    ReferenceStep.PresentedMatch (ReferenceStep.equivalentSetoid relEnv language)
        (.collection .hashBag [schema] (some restName)) source bindings ∧
      Admissible language free bound (.base bag.category) occurrence.original ∧
      occurrence.context.fill occurrence.original = source ∧
      ReferenceStep.Equivalent relEnv language occurrence.original occurrence.value ∧
      contextAddress occurrence.context = occurrence.address := by
  have selectedValue : (bagContents unitLabel [normalForm (some unitLabel) source])[index]? =
      some occurrence.value := by
    rw [← normalizedOccurrences_values,List.getElem?_map,selected]
    rfl
  obtain ⟨within,atPosition⟩ := List.getElem?_eq_some_iff.mp selectedValue
  have headAt : MatchSpec.MatchRel schema (bagContents unitLabel [normalForm (some unitLabel) source])[index]
      headBindings := by rw [atPosition]; exact head
  have matched : MatchSpec.MatchBagRel [schema] (some restName) .hashBag
      (bagContents unitLabel [normalForm (some unitLabel) source]) bindings :=
    .cons index within headAt .nilRest merged
  obtain ⟨representative,converted,_,ordinary⟩ :=
    recover_reference_presentation laws unconditional aligned relEnv good matched
  obtain ⟨originalGood,_,fills,originalEquivalent,address,_⟩ :=
    normalizedOccurrence_reference_source laws unconditional aligned relEnv good (List.mem_of_getElem? selected)
  exact ⟨⟨representative,converted,ordinary⟩,originalGood,fills,originalEquivalent,address⟩

/-- A genuine rule witness at the existing algebra view transports to a
source step modulo the actual equations, retaining its original rule index,
initial bindings and complete premise witness list. -/
theorem stepModulo_of_reference_view_rule {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (unconditional : ReferenceStep.UnconditionalEquations language)
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source target : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {index : Nat} {initial : Bindings} {witnesses : List ReferenceStep.Witness}
    (fired : ReferenceStep.StepValid relEnv language (view unitLabel (normalForm (some unitLabel) source))
      (.rule index initial witnesses) target) :
    ReferenceStep.StepModulo relEnv language source target ∧
      ∃ representative,ReferenceStep.Equivalent relEnv language source representative ∧
        ReferenceStep.StepValid relEnv language representative (.rule index initial witnesses) target := by
  have converted := (ReferenceStep.equivalent_iff_unconditional unconditional aligned).mp
    (normalized_view_equivalent laws (engineBasePremises relEnv) good)
  exact ⟨⟨_,target,converted,⟨.rule index initial witnesses,fired⟩,.refl _⟩,
    _,converted,fired⟩

#print axioms recover_reference_presentation
#print axioms normalizedOccurrence_reference_source
#print axioms tagged_reference_presentation
#print axioms stepModulo_of_reference_view_rule

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep Match MatchSpec
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

/-- One actual unit-law expansion of the algebra view. Its leading unit is
administrative; it does not name or consume a physical source component. -/
def unitExpansion (unitLabel : String) (focus : Pattern) : Pattern :=
  .collection .hashBag (.apply unitLabel [] :: bagContents unitLabel [focus]) none

/-- The selected law supplies a genuine nullary unit of the homogeneous
base sort; no new source typing declaration is postulated. -/
theorem declared_unit_admissible {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) (free : FreeTypeContext) (bound : List TypeExpr) :
    Admissible language free bound (.base bag.category) (.apply unitLabel []) := by
  have emptyTyped : HasType {language with equations := []} free bound
      (.collection .hashBag [] none) (.base bag.category) := bag_hasType laws.toBareBagPresentation (.nil _ _)
  have emptyGood : Admissible language free bound (.base bag.category) (.collection .hashBag [] none) :=
    ⟨grammar_hasType (source := {language with equations := []}) (target := language) rfl emptyTyped,rfl,rfl⟩
  simpa [normalForm,normalizeBag,bagContents,PatternCode.sortPatterns,collapse] using
    normalized_admissible laws base emptyGood rfl

/-- The entire component row is collection data. A zero-component selection
keeps this outer carrier even when the row is empty or a singleton. -/
theorem contents_data_admissible {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {focus : Pattern}
    (good : Admissible language free bound (.base bag.category) focus) :
    Admissible language free bound (.collection .hashBag (.base bag.category)) (view unitLabel focus) := by
  have viewGood := view_admissible laws good
  have comparisonGood := grammar_admissible (source := language)
    (target := {language with equations := []}) rfl viewGood
  obtain ⟨_,_,elementsTyped⟩ := bag_typing laws.toBareBagPresentation comparisonGood.typed rfl
  exact ⟨.collection (grammar_elements (source := {language with equations := []})
    (target := language) rfl elementsTyped),viewGood.canonical,viewGood.object⟩

theorem unitExpansion_admissible {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {focus : Pattern}
    (good : Admissible language free bound (.base bag.category) focus) :
    Admissible language free bound (.base bag.category) (unitExpansion unitLabel focus) := by
  have unitGood := declared_unit_admissible laws base free bound
  have viewGood := view_admissible laws good
  have comparisonGood := grammar_admissible (source := language)
    (target := {language with equations := []}) rfl viewGood
  obtain ⟨_,_,elementsTyped⟩ := bag_typing laws.toBareBagPresentation comparisonGood.typed rfl
  refine ⟨grammar_hasType (source := {language with equations := []}) (target := language) rfl
    (bag_hasType laws.toBareBagPresentation (.cons (grammar_hasType (source := language)
      (target := {language with equations := []}) rfl unitGood.typed) elementsTyped)),?_,?_⟩
  · simpa only [unitExpansion,view,Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList,Bool.true_and] using viewGood.canonical
  · simpa only [unitExpansion,view,isObjectPattern,isObjectPatternList,Bool.true_and] using viewGood.object

/-- A virtual-unit match is supported by the actual declared unit equation.
The source path retains all authored rows; no alternative equivalence or
normalization-only firing assumption is introduced. -/
theorem unitExpansion_equivalent {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source) :
    EquationEquiv base language source (unitExpansion unitLabel (normalForm (some unitLabel) source)) := by
  have normalizedGood := normalized_admissible laws base good rfl
  have expandedGood := grammar_admissible (source := language)
    (target := {language with equations := []}) rfl (unitExpansion_admissible laws base normalizedGood)
  have removed : DerivedInstance {language with equations := []}
      (unitExpansion unitLabel (normalForm (some unitLabel) source))
      (view unitLabel (normalForm (some unitLabel) source)) := by
    change DerivedInstance {language with equations := []}
      (.collection .hashBag ([] ++ .apply unitLabel [] :: bagContents unitLabel [normalForm (some unitLabel) source]) none)
      (.collection .hashBag ([] ++ bagContents unitLabel [normalForm (some unitLabel) source]) none)
    exact .unitElim laws.bagAlgebraRule rfl (sortedAt_of_admissible laws expandedGood rfl)
  have comparisonPath := path_of_derived (base := base) removed
  have sourcePath := comparison_path (language := language) comparisonPath
  exact .trans _ _ _ (normalized_view_equivalent laws base good)
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ sourcePath))

/-- Selecting the virtual unit uses the ordinary matcher at an equivalent
source presentation. The residual contains every live source component in
its existing tagged order and retains its collection-data type. -/
theorem zero_component_reference_presentation {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (unconditional : ReferenceStep.UnconditionalEquations language)
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source schema : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {restName : String} {headBindings bindings : Bindings}
    (head : MatchRel schema (.apply unitLabel []) headBindings)
    (merged : mergeBindings headBindings [(restName,view unitLabel (normalForm (some unitLabel) source))] =
      some bindings) :
    ReferenceStep.PresentedMatch (ReferenceStep.equivalentSetoid relEnv language)
        (.collection .hashBag [schema] (some restName)) source bindings ∧
      Admissible language free bound (.collection .hashBag (.base bag.category))
        (view unitLabel (normalForm (some unitLabel) source)) ∧
      bagContents unitLabel [normalForm (some unitLabel) source] =
        (normalizedOccurrences unitLabel source).map SourceOccurrence.value := by
  have sourceEquivalent := (ReferenceStep.equivalent_iff_unconditional unconditional aligned).mp
    (unitExpansion_equivalent laws (engineBasePremises relEnv) good)
  have ordinary : MatchRel (.collection .hashBag [schema] (some restName))
      (unitExpansion unitLabel (normalForm (some unitLabel) source)) bindings :=
    .collection (by decide) (.cons 0 (by simp) head .nilRest merged)
  exact ⟨⟨_,sourceEquivalent,matchRel_complete ordinary⟩,
    contents_data_admissible laws (normalized_admissible laws (engineBasePremises relEnv) good rfl),
    (normalizedOccurrences_values unitLabel source).symm⟩

#print axioms declared_unit_admissible
#print axioms contents_data_admissible
#print axioms unitExpansion_admissible
#print axioms unitExpansion_equivalent
#print axioms zero_component_reference_presentation

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep Match MatchSpec PatternTreeSize GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics


/-- Finite ordered splits retain the source records themselves. The empty
selection is included; its algebra value is an administrative unit. -/
def occurrenceSplits {α : Type} (occurrences : List α) : List (List α × List α) :=
  occurrences.permutations.flatMap fun reordered =>
    (List.range (occurrences.length + 1)).map fun cut =>
      (reordered.take cut,reordered.drop cut)

/-- Every split is included exactly at the level of permutation and
multiplicity. Equal-valued source occurrences remain distinct records. -/
theorem mem_occurrenceSplits {α : Type} {occurrences selected residual : List α} :
    (selected,residual) ∈ occurrenceSplits occurrences ↔
      (selected ++ residual).Perm occurrences := by
  constructor
  · intro member
    obtain ⟨reordered,inPermutations,inside⟩ := List.mem_flatMap.mp member
    obtain ⟨cut,_,equal⟩ := List.mem_map.mp inside
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
    simpa only [List.take_append_drop] using List.mem_permutations.mp inPermutations
  · intro permutation
    apply List.mem_flatMap.mpr
    refine ⟨selected ++ residual,List.mem_permutations.mpr permutation,?_⟩
    apply List.mem_map.mpr
    refine ⟨selected.length,List.mem_range.mpr ?_,?_⟩
    · have lengths := permutation.length_eq
      simp only [List.length_append] at lengths
      omega
    · simp

/-- Allocate a fixed number of groups and a residual. Empty groups are
represented without a physical source occurrence. -/
def groupedOccurrences {α : Type} : Nat → List α → List (List (List α) × List α)
  | 0,occurrences => occurrences.permutations.map fun reordered => ([],reordered)
  | count + 1,occurrences =>
      (occurrenceSplits occurrences).flatMap fun split =>
        (groupedOccurrences count split.2).map fun remaining =>
          (split.1 :: remaining.1,remaining.2)

/-- Group enumeration covers all finite allocations and conserves the
entire flattened physical occurrence account. -/
theorem mem_groupedOccurrences {α : Type} (count : Nat)
    {occurrences : List α} {groups : List (List α)} {residual : List α} :
    (groups,residual) ∈ groupedOccurrences count occurrences ↔
      groups.length = count ∧ (groups.flatten ++ residual).Perm occurrences := by
  induction count generalizing occurrences groups residual with
  | zero =>
    cases groups with
    | nil => simp [groupedOccurrences,List.mem_permutations]
    | cons head tail => simp [groupedOccurrences]
  | succ count recurse =>
    constructor
    · intro member
      obtain ⟨⟨selected,remaining⟩,splitMember,inside⟩ := List.mem_flatMap.mp member
      obtain ⟨⟨later,last⟩,laterMember,equal⟩ := List.mem_map.mp inside
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
      obtain ⟨lengths,account⟩ := recurse.mp laterMember
      refine ⟨by simpa using lengths,?_⟩
      have laterAccount : ((selected :: later).flatten ++ last).Perm (selected ++ remaining) := by
        simpa only [List.flatten_cons,List.append_assoc] using account.append_left selected
      exact laterAccount.trans (mem_occurrenceSplits.mp splitMember)
    · rintro ⟨lengths,account⟩
      cases groups with
      | nil => simp at lengths
      | cons selected later =>
        apply List.mem_flatMap.mpr
        refine ⟨(selected,later.flatten ++ residual),?_,?_⟩
        · apply mem_occurrenceSplits.mpr
          simpa only [List.flatten_cons,List.append_assoc] using account
        · apply List.mem_map.mpr
          refine ⟨(later,residual),recurse.mpr ⟨by simpa using lengths,.refl _⟩,rfl⟩

/-- A permutation of erased values can be lifted to the original records.
This does not pick one equal-valued source occurrence twice. -/
theorem split_occurrences_of_values {α β : Type} (value : α → β)
    {occurrences : List α} {selected residual : List β}
    (account : (selected ++ residual).Perm (occurrences.map value)) :
    ∃ selectedTags residualTags,
      (selectedTags,residualTags) ∈ occurrenceSplits occurrences ∧
      selectedTags.map value = selected ∧ residualTags.map value = residual := by
  have lifted : ∃ reordered : List α, selected ++ residual = reordered.map value ∧
      reordered.Perm occurrences := by
    change (Relation.Comp (fun (row : List β) (tags : List α) => row = tags.map value)
      List.Perm) (selected ++ residual) occurrences
    rw [List.eq_map_comp_perm]
    exact account
  obtain ⟨reordered,values,permutation⟩ := lifted
  obtain ⟨selectedTags,residualTags,split,first,last⟩ := List.append_eq_map_iff.mp values
  exact ⟨selectedTags,residualTags,mem_occurrenceSplits.mpr (split ▸ permutation),first,last⟩

/-- A well-typed homogeneous component row is both an algebra value and
collection data. This statement does not normalize a data boundary. -/
theorem component_row_admissible {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {components : List Pattern}
    (each : ∀ component ∈ components,
      Admissible language free bound (.base bag.category) component) :
    Admissible language free bound (.base bag.category) (.collection .hashBag components none) ∧
    Admissible language free bound (.collection .hashBag (.base bag.category))
      (.collection .hashBag components none) := by
  have elementsTyped := elementsHaveType_iff.mpr fun component member => (each component member).typed
  have canonical : Pattern.hasCanonicalBinderMetadataList components = true :=
    hasCanonicalBinderMetadataList_iff.mpr fun component member => (each component member).canonical
  have objects : isObjectPatternList components = true :=
    isObjectPatternList_iff.mpr fun component member => (each component member).object
  exact ⟨⟨grammar_hasType (source := {language with equations := []}) (target := language) rfl
      (bag_hasType laws.toBareBagPresentation (grammar_elements (source := language)
        (target := {language with equations := []}) rfl elementsTyped)),canonical,by simpa [isObjectPattern] using objects⟩,
    ⟨.collection elementsTyped,canonical,by simpa [isObjectPattern] using objects⟩⟩

/-- A selected group is the existing algebra collapse of its assigned
components. In particular an empty group is the declared unit, not a token. -/
theorem collapsed_row_admissible {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {components : List Pattern}
    (each : ∀ component ∈ components,
      Admissible language free bound (.base bag.category) component) :
    Admissible language free bound (.base bag.category) (collapse unitLabel components) := by
  cases components with
  | nil => exact declared_unit_admissible laws base free bound
  | cons first rest =>
    cases rest with
    | nil => exact each first (by simp)
    | cons second later => exact (component_row_admissible laws each).1

/-- Components assigned to any group retain the actual source typing,
normal value, and original zipper. -/
theorem grouped_occurrence_origins {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {count : Nat} {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (allocation : (groups,residual) ∈ groupedOccurrences count (normalizedOccurrences unitLabel source)) :
    (groups.flatten ++ residual).Pairwise (fun first second => first.address ≠ second.address) ∧
      ∀ occurrence ∈ groups.flatten ++ residual,
        Admissible language free bound (.base bag.category) occurrence.original ∧
        Admissible language free bound (.base bag.category) occurrence.value ∧
        occurrence.context.fill occurrence.original = source ∧
        normalForm (some unitLabel) occurrence.original = occurrence.value ∧
        contextAddress occurrence.context = occurrence.address := by
  have account := (mem_groupedOccurrences count).mp allocation |>.2
  constructor
  · apply List.pairwise_map.mp
    exact (account.map SourceOccurrence.address).nodup_iff.mpr
      (normalizedOccurrences_distinct unitLabel source)
  · intro occurrence member
    have original := normalizedOccurrences_sound laws good (account.mem_iff.mp member)
    exact ⟨original.1,original.2.1,original.2.2.1,original.2.2.2.1.symm,original.2.2.2.2.1⟩

#print axioms mem_occurrenceSplits
#print axioms mem_groupedOccurrences
#print axioms split_occurrences_of_values
#print axioms component_row_admissible
#print axioms collapsed_row_admissible
#print axioms grouped_occurrence_origins




/-- Group boundaries are source presentations, not collection-data
normalizations. The residual retains its ordinary outer bag carrier. -/
def groupedView (unitLabel : String) (groups : List (List SourceOccurrence))
    (residual : List SourceOccurrence) : Pattern :=
  .collection .hashBag
    (groups.map (fun group => collapse unitLabel (group.map SourceOccurrence.value)) ++
      residual.map SourceOccurrence.value) none

/-- A physical component has neither a bag boundary nor the declared unit
at its normalized root. -/
theorem normalizedOccurrence_plain {unitLabel : String} {source : Pattern}
    {occurrence : SourceOccurrence} (member : occurrence ∈ normalizedOccurrences unitLabel source) :
    occurrence.value ≠ .apply unitLabel [] ∧ ¬ IsBagNode occurrence.value := by
  have valueMember : occurrence.value ∈ bagContents unitLabel [normalForm (some unitLabel) source] := by
    rw [← normalizedOccurrences_values]
    exact List.mem_map.mpr ⟨occurrence,member,rfl⟩
  exact bagContents_spec (fun element member =>
    (List.mem_singleton.mp member) ▸ rootNormal_normalForm unitLabel source) valueMember

private theorem bagContents_plain {unitLabel : String} {components : List Pattern}
    (plain : ∀ component ∈ components, component ≠ .apply unitLabel [] ∧ ¬ IsBagNode component) :
    bagContents unitLabel components = components := by
  induction components with
  | nil => rfl
  | cons head tail recurse =>
    have first := plain head (by simp)
    rw [bagContents_cons,bagContents, List.flatMap_cons,List.flatMap_nil,List.append_nil,
      splice_of_not_bag first.2]
    simp only [List.filter_cons,decide_eq_true first.1,if_true,List.filter_nil]
    change head :: bagContents unitLabel tail = head :: tail
    rw [recurse (fun component member => plain component (by simp [member]))]

private theorem bagContents_grouped {unitLabel : String} {groups : List (List Pattern)}
    {residual : List Pattern}
    (plain : ∀ component ∈ groups.flatten ++ residual,
      component ≠ .apply unitLabel [] ∧ ¬ IsBagNode component) :
    bagContents unitLabel (groups.map (collapse unitLabel) ++ residual) = groups.flatten ++ residual := by
  induction groups with
  | nil => simpa using bagContents_plain plain
  | cons group groups recurse =>
    have firstPlain : ∀ component ∈ group,
        component ≠ .apply unitLabel [] ∧ ¬ IsBagNode component := by
      intro component member
      exact plain component (by simp [member])
    have laterPlain : ∀ component ∈ groups.flatten ++ residual,
        component ≠ .apply unitLabel [] ∧ ¬ IsBagNode component := by
      intro component member
      apply plain component
      simpa only [List.flatten_cons,List.append_assoc,List.mem_append] using Or.inr member
    rw [List.map_cons,List.cons_append,bagContents_cons,bagContents_collapse firstPlain,
      recurse laterPlain,List.flatten_cons,List.append_assoc]

/-- Group and residual values exhaust exactly the existing physical
components; group boundaries and empty groups add no component. -/
theorem groupedView_contents {unitLabel : String} {source : Pattern} {count : Nat}
    {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (allocation : (groups,residual) ∈ groupedOccurrences count (normalizedOccurrences unitLabel source)) :
    bagContents unitLabel
      (groups.map (fun group => collapse unitLabel (group.map SourceOccurrence.value)) ++
        residual.map SourceOccurrence.value) = (groups.flatten ++ residual).map SourceOccurrence.value := by
  have account := (mem_groupedOccurrences count).mp allocation |>.2
  have mapped : (groups.map (List.map SourceOccurrence.value)).flatten =
      groups.flatten.map SourceOccurrence.value := List.map_flatten.symm
  rw [List.map_append,← mapped]
  simpa only [List.map_map,Function.comp_def] using
    bagContents_grouped (groups := groups.map (List.map SourceOccurrence.value))
    (residual := residual.map SourceOccurrence.value) (by
      intro component member
      rw [mapped,← List.map_append] at member
      obtain ⟨occurrence,inside,rfl⟩ := List.mem_map.mp member
      exact normalizedOccurrence_plain (account.mem_iff.mp inside))

/-- Every constructed group has the homogeneous base sort; the residual
also keeps its separate collection-data typing. -/
theorem groupedView_admissible {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {count : Nat} {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (allocation : (groups,residual) ∈ groupedOccurrences count (normalizedOccurrences unitLabel source)) :
    Admissible language free bound (.base bag.category) (groupedView unitLabel groups residual) ∧
      Admissible language free bound (.collection .hashBag (.base bag.category))
        (.collection .hashBag (residual.map SourceOccurrence.value) none) := by
  have account := (mem_groupedOccurrences count).mp allocation |>.2
  have each : ∀ occurrence ∈ groups.flatten ++ residual,
      Admissible language free bound (.base bag.category) occurrence.value :=
    fun occurrence member => (normalizedOccurrences_sound laws good (account.mem_iff.mp member)).2.1
  constructor
  · apply (component_row_admissible laws ?_).1
    intro component member
    rcases List.mem_append.mp member with grouped | retained
    · obtain ⟨group,inGroups,rfl⟩ := List.mem_map.mp grouped
      apply collapsed_row_admissible laws base
      intro value valueMember
      obtain ⟨occurrence,inGroup,rfl⟩ := List.mem_map.mp valueMember
      exact each occurrence (List.mem_append_left _ (List.mem_flatten.mpr ⟨group,inGroups,inGroup⟩))
    · obtain ⟨occurrence,inResidual,rfl⟩ := List.mem_map.mp retained
      exact each occurrence (List.mem_append_right _ inResidual)
  · apply (component_row_admissible laws ?_).2
    intro value member
    obtain ⟨occurrence,inResidual,rfl⟩ := List.mem_map.mp member
    exact each occurrence (List.mem_append_right _ inResidual)

/-- Finite grouping is justified by the actual typed flattening and unit
laws. All authored equation rows remain in the source language. -/
theorem groupedView_equivalent {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {count : Nat} {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (allocation : (groups,residual) ∈ groupedOccurrences count (normalizedOccurrences unitLabel source)) :
    EquationEquiv base language source (groupedView unitLabel groups residual) := by
  have account := (mem_groupedOccurrences count).mp allocation |>.2
  have groupedGood := (groupedView_admissible laws base good allocation).1
  have comparisonGood := grammar_admissible (source := language)
    (target := {language with equations := []}) rfl groupedGood
  let terms := groups.map (fun group => collapse unitLabel (group.map SourceOccurrence.value)) ++
    residual.map SourceOccurrence.value
  have spliced := path_splice (base := base) laws (type := .base bag.category) rfl terms [] comparisonGood
  simp only [List.nil_append] at spliced
  have afterSplice := path_admissible laws spliced comparisonGood rfl
  have dropped := path_dropUnits (base := base) laws rfl (terms.flatMap splice) [] afterSplice
  simp only [List.nil_append] at dropped
  have flattened : Path base {language with equations := []} (groupedView unitLabel groups residual)
      (.collection .hashBag ((groups.flatten ++ residual).map SourceOccurrence.value) none) := by
    have combined := spliced.trans dropped
    change Path base {language with equations := []} (.collection .hashBag terms none)
      (.collection .hashBag (bagContents unitLabel terms) none) at combined
    simpa only [terms,groupedView,groupedView_contents allocation] using combined
  have groupedPath := comparison_path (language := language) flattened
  have normalizedGood := normalized_admissible laws base good rfl
  have normalViewGood := grammar_admissible (source := language)
    (target := {language with equations := []}) rfl (view_admissible laws normalizedGood)
  have permuted : ((groups.flatten ++ residual).map SourceOccurrence.value).Perm
      (bagContents unitLabel [normalForm (some unitLabel) source]) := by
    rw [← normalizedOccurrences_values]
    exact account.map SourceOccurrence.value
  have permutation := path_of_derived (base := base)
    (DerivedInstance.bagPerm_of_sorted (sortedAt_of_admissible laws normalViewGood rfl) permuted.symm)
  have permutationPath := comparison_path (language := language) permutation
  exact .trans _ _ _ (normalized_view_equivalent laws base good)
    (.trans _ _ _ (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ permutationPath)
      (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ groupedPath).symm)

/-- Any ordinary match of a listed grouped presentation is an actual
reference match at an equivalent representative, including empty groups. -/
theorem grouped_reference_presentation {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (unconditional : ReferenceStep.UnconditionalEquations language)
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source schema : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {count : Nat} {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (allocation : (groups,residual) ∈ groupedOccurrences count (normalizedOccurrences unitLabel source))
    {bindings : Bindings}
    (matched : MatchRel schema (groupedView unitLabel groups residual) bindings) :
    ReferenceStep.PresentedMatch (ReferenceStep.equivalentSetoid relEnv language) schema source bindings := by
  exact ⟨_,(ReferenceStep.equivalent_iff_unconditional unconditional aligned).mp
    (groupedView_equivalent laws (engineBasePremises relEnv) good allocation),matchRel_complete matched⟩

/-- Flattening group tags together with the residual and physical source
units gives exactly the original source occurrence account. -/
theorem grouped_occurrence_account {unitLabel : String} {source : Pattern} {count : Nat}
    {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (allocation : (groups,residual) ∈ groupedOccurrences count (normalizedOccurrences unitLabel source)) :
    ((groups.flatten ++ residual) ++ unitOccurrences unitLabel source).Perm
      (sourceOccurrences unitLabel source) :=
  (((mem_groupedOccurrences count).mp allocation).2.append_right _).trans
    (occurrence_account unitLabel source)

#print axioms groupedView_contents
#print axioms groupedView_admissible
#print axioms groupedView_equivalent
#print axioms grouped_reference_presentation
#print axioms grouped_occurrence_account




private theorem listNodes_map_sum (components : List Pattern) :
    listNodes components = (components.map nodes).sum := by
  induction components with
  | nil => rfl
  | cons first rest recurse => simp only [listNodes,List.map_cons,List.sum_cons,recurse]

private theorem listNodes_append (first second : List Pattern) :
    listNodes (first ++ second) = listNodes first + listNodes second := by
  simp only [listNodes_map_sum,List.map_append,List.sum_append]

private theorem listNodes_perm {first second : List Pattern} (permutation : first.Perm second) :
    listNodes first = listNodes second := by
  simp only [listNodes_map_sum]
  exact (permutation.map nodes).sum_eq

private theorem listNodes_positive {components : List Pattern} (nonempty : components ≠ []) :
    0 < listNodes components := by
  cases components with
  | nil => exact (nonempty rfl).elim
  | cons first rest => have positive := nodes_positive first; simp only [listNodes]; omega

/-- A group can contain every source component, or no component. Its
collapsed algebra value has a non-strict source-node bound. -/
theorem collapse_nodes_le (unitLabel : String) {selected residual whole : List Pattern}
    (account : (selected ++ residual).Perm whole) :
    nodes (collapse unitLabel selected) ≤ nodes (collapse unitLabel whole) := by
  have lengths := account.length_eq
  simp only [List.length_append] at lengths
  have sizes := listNodes_perm account
  rw [listNodes_append] at sizes
  cases selected with
  | nil =>
    change 1 ≤ nodes (collapse unitLabel whole)
    have positive := nodes_positive (collapse unitLabel whole)
    omega
  | cons first selected =>
    cases whole with
    | nil => simp only [List.length_cons,List.length_nil] at lengths; omega
    | cons head whole =>
      cases selected with
      | nil =>
        cases whole with
        | nil => simp only [collapse,listNodes] at *; omega
        | cons second later => simp only [collapse,nodes,listNodes] at *; omega
      | cons second later =>
        cases whole with
        | nil => simp only [List.length_cons,List.length_nil] at lengths; omega
        | cons next remaining => simp only [collapse,nodes,listNodes] at *; omega

/-- Genuine positive consumption with a nonempty residual gives strict
source descent. Unit padding and whole-group selection are deliberately
outside this stronger statement. -/
theorem collapse_nodes_lt (unitLabel : String) {selected residual whole : List Pattern}
    (account : (selected ++ residual).Perm whole)
    (selectedNonempty : selected ≠ []) (residualNonempty : residual ≠ []) :
    nodes (collapse unitLabel selected) < nodes (collapse unitLabel whole) := by
  have lengths := account.length_eq
  have selectedLength : 0 < selected.length := List.length_pos_iff.mpr selectedNonempty
  have residualLength : 0 < residual.length := List.length_pos_iff.mpr residualNonempty
  simp only [List.length_append] at lengths
  have sizes := listNodes_perm account
  rw [listNodes_append] at sizes
  have positive := listNodes_positive residualNonempty
  cases whole with
  | nil => simp only [List.length_nil] at lengths; omega
  | cons head whole =>
    cases whole with
    | nil => simp only [List.length_cons,List.length_nil] at lengths; omega
    | cons next remaining =>
      cases selected with
      | nil => exact (selectedNonempty rfl).elim
      | cons first selected =>
        cases selected <;> simp only [collapse,nodes,listNodes] at * <;> omega

/-- Every finite physical group has a bounded algebra value, including the
whole-source and zero-component cases. The measure is the existing source
normal form's tree size, not an arbitrary presentation size. -/
theorem split_group_nodes_le {unitLabel : String} {source : Pattern}
    {selected residual : List SourceOccurrence}
    (allocation : (selected,residual) ∈ occurrenceSplits (normalizedOccurrences unitLabel source)) :
    nodes (collapse unitLabel (selected.map SourceOccurrence.value)) ≤
      nodes (normalForm (some unitLabel) source) := by
  have account := (mem_occurrenceSplits.mp allocation).map SourceOccurrence.value
  rw [List.map_append,normalizedOccurrences_values] at account
  have bounded := collapse_nodes_le unitLabel account
  rw [collapse_contents (rootNormal_normalForm unitLabel source)] at bounded
  exact bounded

/-- The strict bound has an explicit physical progress condition. Neither
an administrative unit nor a group equal to the whole source earns it. -/
theorem split_group_nodes_lt {unitLabel : String} {source : Pattern}
    {selected residual : List SourceOccurrence}
    (allocation : (selected,residual) ∈ occurrenceSplits (normalizedOccurrences unitLabel source))
    (selectedNonempty : selected ≠ []) (residualNonempty : residual ≠ []) :
    nodes (collapse unitLabel (selected.map SourceOccurrence.value)) <
      nodes (normalForm (some unitLabel) source) := by
  have account := (mem_occurrenceSplits.mp allocation).map SourceOccurrence.value
  rw [List.map_append,normalizedOccurrences_values] at account
  have bounded := collapse_nodes_lt unitLabel account
    (by simpa using selectedNonempty) (by simpa using residualNonempty)
  rw [collapse_contents (rootNormal_normalForm unitLabel source)] at bounded
  exact bounded

/-- Every actual selected member of an admissible source presentation
allocates a finite group of the original source's tagged components. The
converse uses the existing source equation normalizer, not a matching oracle. -/
theorem source_selection_covered {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings,normalForm (some unitLabel) (applyBindings bindings row.left) =
          normalForm (some unitLabel) (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern} {elements : List Pattern}
    (sourceGood : Admissible language free bound (.base bag.category) source)
    (representativeGood : Admissible language free bound (.base bag.category)
      (.collection .hashBag elements none))
    (equivalent : ReferenceStep.Equivalent relEnv language source (.collection .hashBag elements none))
    (index : Nat) (within : index < elements.length) :
    ∃ selected residual,
      (selected,residual) ∈ occurrenceSplits (normalizedOccurrences unitLabel source) ∧
      selected.map SourceOccurrence.value = bagContents unitLabel [normalForm (some unitLabel) elements[index]] ∧
      residual.map SourceOccurrence.value =
        bagContents unitLabel ((elements.eraseIdx index).map (normalForm (some unitLabel))) ∧
      collapse unitLabel (selected.map SourceOccurrence.value) = normalForm (some unitLabel) elements[index] ∧
      nodes (normalForm (some unitLabel) elements[index]) ≤ nodes (normalForm (some unitLabel) source) := by
  have normalEqual := (reference_equivalent_iff_normalForm_eq laws rows aligned relEnv
    sourceGood representativeGood rfl).mp equivalent
  have reordered := (List.getElem_cons_eraseIdx_perm within).map (normalForm (some unitLabel))
  have components := (reordered.flatMap_right splice).filter
    (fun pattern => decide (pattern ≠ .apply unitLabel []))
  change (bagContents unitLabel (normalForm (some unitLabel) elements[index] ::
    (elements.eraseIdx index).map (normalForm (some unitLabel)))).Perm
      (bagContents unitLabel (elements.map (normalForm (some unitLabel)))) at components
  rw [bagContents_cons] at components
  have sortedAccount : (bagContents unitLabel (elements.map (normalForm (some unitLabel)))).Perm
      (bagContents unitLabel [normalForm (some unitLabel) source]) := by
    rw [normalEqual,normalForm_bag_contents]
    exact (sortPatterns_perm _).symm
  have fullAccount := components.trans sortedAccount
  rw [← normalizedOccurrences_values unitLabel source] at fullAccount
  obtain ⟨selected,residual,allocation,first,last⟩ :=
    split_occurrences_of_values SourceOccurrence.value fullAccount
  have selectedValue : collapse unitLabel (selected.map SourceOccurrence.value) =
      normalForm (some unitLabel) elements[index] := by
    rw [first,collapse_contents (rootNormal_normalForm unitLabel elements[index])]
  exact ⟨selected,residual,allocation,first,last,selectedValue,
    selectedValue ▸ split_group_nodes_le allocation⟩

#print axioms collapse_nodes_le
#print axioms collapse_nodes_lt
#print axioms split_group_nodes_le
#print axioms split_group_nodes_lt
#print axioms source_selection_covered




/-- The ordinary matcher realizes every finite one-group allocation. The
selected algebra value and residual collection data occupy distinct roles. -/
theorem single_group_capture_match (unitLabel selectedName restName : String)
    (different : selectedName ≠ restName) (selected residual : List SourceOccurrence) :
    MatchRel (.collection .hashBag [.fvar selectedName] (some restName))
      (groupedView unitLabel [selected] residual)
      [(restName,.collection .hashBag (residual.map SourceOccurrence.value) none),
       (selectedName,collapse unitLabel (selected.map SourceOccurrence.value))] := by
  apply MatchRel.collection (by decide)
  apply MatchBagRel.cons 0 (by simp) MatchRel.fvar MatchBagRel.nilRest
  simp [mergeBindings,different]

private theorem source_row_contents_equivalent {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern}
    (good : Admissible language free bound (.base bag.category) (.collection .hashBag elements none)) :
    EquationEquiv base language (.collection .hashBag elements none)
      (.collection .hashBag (bagContents unitLabel (elements.map (normalForm (some unitLabel)))) none) := by
  have viewGood := view_admissible laws (normalized_admissible laws base good rfl)
  have comparisonGood := grammar_admissible (source := language)
    (target := {language with equations := []}) rfl viewGood
  have permuted : (bagContents unitLabel [normalForm (some unitLabel)
      (.collection .hashBag elements none)]).Perm
      (bagContents unitLabel (elements.map (normalForm (some unitLabel)))) := by
    rw [normalForm_bag_contents]
    exact sortPatterns_perm _
  have permutation := path_of_derived (base := base)
    (DerivedInstance.bagPerm_of_sorted (sortedAt_of_admissible laws comparisonGood rfl) permuted)
  exact .trans _ _ _ (normalized_view_equivalent laws base good)
    (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ (comparison_path (language := language) permutation))

/-- Every actual one-variable/rest source match at an admissible equivalent
presentation is recovered by a finite physical grouping, with actual source
equivalence for both captures and a typed residual data boundary. This does
not transport arbitrary literal provider predicates or rule conclusions. -/
theorem source_capture_covered {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings,normalForm (some unitLabel) (applyBindings bindings row.left) =
          normalForm (some unitLabel) (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern} {elements : List Pattern}
    (sourceGood : Admissible language free bound (.base bag.category) source)
    (representativeGood : Admissible language free bound (.base bag.category)
      (.collection .hashBag elements none))
    (equivalent : ReferenceStep.Equivalent relEnv language source (.collection .hashBag elements none))
    {selectedName restName : String} (different : selectedName ≠ restName) {bindings : Bindings}
    (matched : MatchBagRel [.fvar selectedName] (some restName) .hashBag elements bindings) :
    ∃ selected residual originalSelected originalResidual,
      (selected,residual) ∈ occurrenceSplits (normalizedOccurrences unitLabel source) ∧
      bindings.lookup selectedName = some originalSelected ∧
      bindings.lookup restName = some originalResidual ∧
      ReferenceStep.Equivalent relEnv language originalSelected
        (collapse unitLabel (selected.map SourceOccurrence.value)) ∧
      ReferenceStep.Equivalent relEnv language originalResidual
        (.collection .hashBag (residual.map SourceOccurrence.value) none) ∧
      ReferenceStep.PresentedMatch (ReferenceStep.equivalentSetoid relEnv language)
        (.collection .hashBag [.fvar selectedName] (some restName)) source
        [(restName,.collection .hashBag (residual.map SourceOccurrence.value) none),
         (selectedName,collapse unitLabel (selected.map SourceOccurrence.value))] ∧
      Admissible language free bound (.collection .hashBag (.base bag.category))
        (.collection .hashBag (residual.map SourceOccurrence.value) none) ∧
      nodes (collapse unitLabel (selected.map SourceOccurrence.value)) ≤
        nodes (normalForm (some unitLabel) source) := by
  have inversion : ∃ (index : Nat) (within : index < elements.length),
      bindings = [(restName,.collection .hashBag (elements.eraseIdx index) none),
        (selectedName,elements[index])] := by
    cases matched with
    | cons index within head later merged =>
      cases head
      cases later
      exact ⟨index,within,by simpa [mergeBindings,different] using merged.symm⟩
  obtain ⟨index,within,rfl⟩ := inversion
  obtain ⟨selected,residual,allocation,_,last,selectedValue,_⟩ :=
    source_selection_covered laws rows aligned relEnv sourceGood representativeGood equivalent index within
  have grouped : ([selected],residual) ∈ groupedOccurrences 1 (normalizedOccurrences unitLabel source) :=
    (mem_groupedOccurrences 1).mpr ⟨rfl,by simpa using mem_occurrenceSplits.mp allocation⟩
  have selectedGood := source_bag_element laws representativeGood (List.getElem_mem within)
  have residualGood : Admissible language free bound (.base bag.category)
      (.collection .hashBag (elements.eraseIdx index) none) :=
    (component_row_admissible laws (fun component member =>
      source_bag_element laws representativeGood (List.mem_of_mem_eraseIdx member))).1
  have selectedEquivalent : ReferenceStep.Equivalent relEnv language elements[index]
      (collapse unitLabel (selected.map SourceOccurrence.value)) := by
    rw [selectedValue]
    exact (ReferenceStep.equivalent_iff_unconditional (fun row member => (rows row member).1) aligned).mp
      (source_equiv_normalForm laws (engineBasePremises relEnv) selectedGood rfl)
  have residualEquivalent : ReferenceStep.Equivalent relEnv language
      (.collection .hashBag (elements.eraseIdx index) none)
      (.collection .hashBag (residual.map SourceOccurrence.value) none) := by
    rw [last]
    exact (ReferenceStep.equivalent_iff_unconditional (fun row member => (rows row member).1) aligned).mp
      (source_row_contents_equivalent laws (engineBasePremises relEnv) residualGood)
  refine ⟨selected,residual,elements[index],.collection .hashBag (elements.eraseIdx index) none,
    allocation,?_,?_,selectedEquivalent,residualEquivalent,?_,?_,split_group_nodes_le allocation⟩
  · simp [Bindings.lookup,different.symm]
  · simp [Bindings.lookup]
  · exact grouped_reference_presentation laws (fun row member => (rows row member).1) aligned relEnv
      sourceGood grouped (single_group_capture_match unitLabel selectedName restName different selected residual)
  · exact (groupedView_admissible laws (engineBasePremises relEnv) sourceGood grouped).2

#print axioms single_group_capture_match
#print axioms source_capture_covered




/-- A rule firing at a finite grouped presentation is an actual original
source step modulo the declared equations. Group administration changes
neither the rule index nor its bindings or premise witness history. -/
theorem stepModulo_of_grouped_rule {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (unconditional : ReferenceStep.UnconditionalEquations language)
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source target : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {count : Nat} {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (allocation : (groups,residual) ∈ groupedOccurrences count (normalizedOccurrences unitLabel source))
    {index : Nat} {initial : Bindings} {witnesses : List ReferenceStep.Witness}
    (fired : ReferenceStep.StepValid relEnv language (groupedView unitLabel groups residual)
      (.rule index initial witnesses) target) :
    ReferenceStep.StepModulo relEnv language source target ∧
      Admissible language free bound (.base bag.category) (groupedView unitLabel groups residual) ∧
      ReferenceStep.Equivalent relEnv language source (groupedView unitLabel groups residual) ∧
      ReferenceStep.StepValid relEnv language (groupedView unitLabel groups residual)
        (.rule index initial witnesses) target ∧
      ((groups.flatten ++ residual) ++ unitOccurrences unitLabel source).Perm
        (sourceOccurrences unitLabel source) := by
  have converted := (ReferenceStep.equivalent_iff_unconditional unconditional aligned).mp
    (groupedView_equivalent laws (engineBasePremises relEnv) good allocation)
  exact ⟨⟨_,target,converted,⟨.rule index initial witnesses,fired⟩,.refl _⟩,
    (groupedView_admissible laws (engineBasePremises relEnv) good allocation).1,
    converted,fired,grouped_occurrence_account allocation⟩

#print axioms stepModulo_of_grouped_rule


end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep DerivedContexts Match MatchSpec GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

private theorem contextAddress_comp (outer inner : OneHoleContext) :
    contextAddress (outer.comp inner) = contextAddress outer ++ contextAddress inner := by
  induction outer <;> simp_all only [OneHoleContext.comp,contextAddress,List.nil_append,List.cons_append]

/-- Rebase a real physical source record along the existing outer zipper.
Its original and normalized values are retained unchanged. -/
def SourceOccurrence.underContext (outer : OneHoleContext) (occurrence : SourceOccurrence) : SourceOccurrence :=
  { occurrence with
    address := contextAddress outer ++ occurrence.address
    context := outer.comp occurrence.context }

/-- Rebasing maps a whole physical account; it does not select or duplicate
individual equal-valued occurrences. -/
theorem underContext_account (outer : OneHoleContext) {first second : List SourceOccurrence}
    (account : first.Perm second) :
    (first.map (SourceOccurrence.underContext outer)).Perm
      (second.map (SourceOccurrence.underContext outer)) := account.map _

theorem underContext_distinct (outer : OneHoleContext) {occurrences : List SourceOccurrence}
    (distinct : (occurrences.map SourceOccurrence.address).Nodup) :
    ((occurrences.map (SourceOccurrence.underContext outer)).map SourceOccurrence.address).Nodup := by
  apply List.pairwise_map.mpr
  apply List.pairwise_map.mpr
  apply (List.pairwise_map.mp distinct).imp
  intro first second different same
  exact different ((List.append_right_inj _).mp same)

/-- Every physical algebra leaf carries actual typed descent from its
original source, with the exact local context and declaring carrier. -/
theorem sourceOccurrences_typedAt {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} :
    ∀ source,Admissible language free bound (.base bag.category) source →
      ∀ occurrence,occurrence ∈ sourceOccurrences unitLabel source →
      TypedAt language free occurrence.original occurrence.context bound (.base bag.category)
        bound (.base bag.category)
  | source,good,occurrence,member => by
    by_cases isBag : IsBagNode source
    · obtain ⟨elements,rfl⟩ := isBag
      rw [sourceOccurrences_bag] at member
      obtain ⟨⟨element,index⟩,indexed,mapped⟩ := List.mem_flatMap.mp member
      obtain ⟨inside,inChild,rfl⟩ := List.mem_map.mp mapped
      have selected := List.mk_mem_zipIdx_iff_getElem?.mp indexed
      have within := (List.getElem?_eq_some_iff.mp selected).1
      have elementMember := List.mem_of_getElem? selected
      have elementGood := source_bag_element laws good elementMember
      have childTyped := sourceOccurrences_typedAt laws element elementGood inside inChild
      have childFilled := (sourceOccurrences_sound laws element elementGood inside inChild).2.1
      have split : elements.take index ++ element :: elements.drop (index + 1) = elements := by
        rw [← (List.getElem?_eq_some_iff.mp selected).2,List.getElem_cons_drop within]
        exact List.take_append_drop index elements
      have comparisonGood := grammar_admissible (source := language)
        (target := {language with equations := []}) rfl good
      have elementsTyped := (bag_typing laws.toBareBagPresentation comparisonGood.typed rfl).2.2
      obtain ⟨parameterName,shape⟩ := laws.bareShape
      apply TypedAt.collectionConstructor (language := language) laws.bagAuthored shape ?_ childTyped
      rw [childFilled,split]
      exact grammar_elements (source := {language with equations := []}) (target := language) rfl elementsTyped
    · rw [sourceOccurrences_nonbag isBag] at member
      obtain rfl := List.mem_singleton.mp member
      exact .here good.typed
termination_by source => sizeOf source

/-- Sorting and unit filtering preserve the real typed occurrence, not only
its endpoint type. -/
theorem normalizedOccurrences_typedAt {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {occurrence : SourceOccurrence} (member : occurrence ∈ normalizedOccurrences unitLabel source) :
    TypedAt language free occurrence.original occurrence.context bound (.base bag.category)
      bound (.base bag.category) := by
  have filtered := (sortOccurrences_perm (componentOccurrences unitLabel source)).mem_iff.mp member
  exact sourceOccurrences_typedAt laws source good occurrence (List.mem_filter.mp filtered).1

/-- A full original typed occurrence transports every tagged component
through its real constructor/binder zipper. No new operational context
permission is inferred from this typing descent. -/
theorem normalizedOccurrence_under_typed_context {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound rootBound : List TypeExpr} {rootType : TypeExpr}
    {source : Pattern} {outer : OneHoleContext}
    (good : Admissible language free bound (.base bag.category) source)
    (selected : TypedAt language free source outer rootBound rootType bound (.base bag.category))
    {occurrence : SourceOccurrence} (member : occurrence ∈ normalizedOccurrences unitLabel source) :
    TypedAt language free occurrence.original (SourceOccurrence.underContext outer occurrence).context
        rootBound rootType bound (.base bag.category) ∧
      (SourceOccurrence.underContext outer occurrence).context.fill occurrence.original = outer.fill source ∧
      contextAddress (SourceOccurrence.underContext outer occurrence).context =
        (SourceOccurrence.underContext outer occurrence).address := by
  have inside := normalizedOccurrences_typedAt laws good member
  have sourceAccount := normalizedOccurrences_sound laws good member
  have outerTyped : TypedAt language free (occurrence.context.fill occurrence.original) outer
      rootBound rootType bound (.base bag.category) := sourceAccount.2.2.1 ▸ selected
  refine ⟨TypedAt.comp outerTyped inside,?_,?_⟩
  · rw [SourceOccurrence.underContext,OneHoleContext.fill_comp,sourceAccount.2.2.1]
  · simp only [SourceOccurrence.underContext,contextAddress_comp,sourceAccount.2.2.2.2.1]

/-- At most one physical component supports a scalar head. The unit has an
explicit virtual case, with no manufactured source occurrence. -/
inductive SourceHead where
  | unit
  | physical (occurrence : SourceOccurrence)
  deriving Repr,DecidableEq

def sourceHead? : List SourceOccurrence → Option SourceHead
  | [] => some .unit
  | [occurrence] => some (.physical occurrence)
  | _ => none

def SourceHead.original (unitLabel : String) : SourceHead → Pattern
  | .unit => .apply unitLabel []
  | .physical occurrence => occurrence.original

/-- Scalar and constructor spines retain their actual local type. A bag
node can occur at a collection-free type only at the homogeneous base sort. -/
theorem normalizedOccurrences_sound_at {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    (good : Admissible language free bound expected source) (collectionless : collectionFree expected = true)
    {occurrence : SourceOccurrence} (member : occurrence ∈ normalizedOccurrences unitLabel source) :
    Admissible language free bound expected occurrence.original ∧
      Admissible language free bound expected occurrence.value ∧
      occurrence.context.fill occurrence.original = source ∧
      occurrence.value = normalForm (some unitLabel) occurrence.original ∧
      contextAddress occurrence.context = occurrence.address ∧
      ∀ replacement,HasType language free bound replacement expected →
        HasType language free bound (occurrence.context.fill replacement) expected := by
  by_cases isBag : IsBagNode source
  · obtain ⟨elements,rfl⟩ := isBag
    have compared := grammar_admissible (source := language)
      (target := {language with equations := []}) rfl good
    have same := (bag_typing laws.toBareBagPresentation compared.typed collectionless).2.1
    subst expected
    exact normalizedOccurrences_sound laws good member
  · have filtered := (sortOccurrences_perm (componentOccurrences unitLabel source)).mem_iff.mp member
    have original := (List.mem_filter.mp filtered).1
    rw [sourceOccurrences_nonbag isBag] at original
    obtain rfl := List.mem_singleton.mp original
    exact ⟨good,normalized_admissible laws base good collectionless,rfl,rfl,rfl,fun _ typed => typed⟩

/-- A source scalar head is an actual original leaf or an explicit unit
presentation. It has the exact original source normal value. -/
theorem sourceHead_readback {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    (good : Admissible language free bound expected source) (collectionless : collectionFree expected = true)
    {head : SourceHead} (found : sourceHead? (normalizedOccurrences unitLabel source) = some head) :
    Admissible language free bound expected (head.original unitLabel) ∧
      normalForm (some unitLabel) (head.original unitLabel) = normalForm (some unitLabel) source ∧
      EquationEquiv base language source (head.original unitLabel) := by
  have shape : ∀ (occurrences : List SourceOccurrence),sourceHead? occurrences = some head →
      (head = .unit ∧ occurrences = []) ∨ ∃ occurrence,head = .physical occurrence ∧ occurrences = [occurrence] := by
    intro occurrences selected
    cases occurrences with
    | nil => exact .inl ⟨Option.some.inj selected.symm,rfl⟩
    | cons first rest =>
      cases rest with
      | nil => exact .inr ⟨first,Option.some.inj selected.symm,rfl⟩
      | cons next later => cases selected
  rcases shape _ found with ⟨rfl,empty⟩ | ⟨occurrence,rfl,singleton⟩
  · have unitGood := declared_unit_admissible laws base free bound
    have contents : bagContents unitLabel [normalForm (some unitLabel) source] = [] := by
      rw [← normalizedOccurrences_values,empty]
      rfl
    have image : normalForm (some unitLabel) source = .apply unitLabel [] := by
      rw [← collapse_contents (rootNormal_normalForm unitLabel source),contents]
      rfl
    have unitGood : Admissible language free bound expected (.apply unitLabel []) := by
      simpa only [image] using normalized_admissible laws base good collectionless
    refine ⟨unitGood,?_,?_⟩
    · simpa only [SourceHead.original,image,List.map_nil] using normalForm_apply (some unitLabel) unitLabel []
    · simpa only [SourceHead.original,image] using source_equiv_normalForm laws base good collectionless
  · have member : occurrence ∈ normalizedOccurrences unitLabel source := by rw [singleton]; exact .head _
    have original := normalizedOccurrences_sound_at laws base good collectionless member
    have contents : bagContents unitLabel [normalForm (some unitLabel) source] = [occurrence.value] := by
      rw [← normalizedOccurrences_values,singleton]
      rfl
    have image : normalForm (some unitLabel) occurrence.original = normalForm (some unitLabel) source := by
      rw [← original.2.2.2.1,← collapse_contents (rootNormal_normalForm unitLabel source),contents]
      rfl
    refine ⟨original.1,image,?_⟩
    exact .trans _ _ _ (source_equiv_normalForm laws base good collectionless)
      (image ▸ (source_equiv_normalForm laws base original.1 collectionless).symm)

#print axioms underContext_account
#print axioms underContext_distinct
#print axioms sourceOccurrences_typedAt
#print axioms normalizedOccurrences_typedAt
#print axioms normalizedOccurrence_under_typed_context
#print axioms normalizedOccurrences_sound_at
#print axioms sourceHead_readback

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep DerivedContexts Match MatchSpec GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

/-- A scalar normal value has a finite head readback. The empty component
row is the virtual unit case rather than a missing physical token. -/
theorem sourceHead_isSome_of_scalar {unitLabel : String} {source : Pattern}
    (scalar : ¬ IsBagNode (normalForm (some unitLabel) source)) :
    (sourceHead? (normalizedOccurrences unitLabel source)).isSome = true := by
  have length : (normalizedOccurrences unitLabel source).length ≤ 1 := by
    rw [← List.length_map (f := SourceOccurrence.value),normalizedOccurrences_values]
    by_cases unit : normalForm (some unitLabel) source = .apply unitLabel []
    · simp [unit,bagContents,splice]
    · simp [bagContents,splice_of_not_bag scalar,unit]
  cases found : normalizedOccurrences unitLabel source with
  | nil => rfl
  | cons occurrence rest =>
    cases rest with
    | nil => rfl
    | cons next later => simp only [found,List.length_cons] at length; omega

/-- Scalar readback never introduces a bag node as an original physical
leaf; such nodes belong to the exact grouped allocation account. -/
theorem sourceHead_nonbag {unitLabel : String} {source : Pattern} {head : SourceHead}
    (found : sourceHead? (normalizedOccurrences unitLabel source) = some head) :
    ¬ IsBagNode (head.original unitLabel) := by
  cases occurrences : normalizedOccurrences unitLabel source with
  | nil =>
    rw [occurrences,sourceHead?] at found
    cases Option.some.inj found
    simp [SourceHead.original,IsBagNode]
  | cons occurrence rest =>
    cases rest with
    | nil =>
      rw [occurrences,sourceHead?] at found
      cases Option.some.inj found
      have member : occurrence ∈ normalizedOccurrences unitLabel source := by rw [occurrences]; exact .head _
      have filtered := (sortOccurrences_perm (componentOccurrences unitLabel source)).mem_iff.mp member
      exact (sourceOccurrences_leaf_value unitLabel source occurrence (List.mem_filter.mp filtered).1).1
    | cons next later => simp [occurrences,sourceHead?] at found

private theorem normalForm_apply_inverse {unitLabel label : String} {source : Pattern} {targets : List Pattern}
    (nonbag : ¬ IsBagNode source)
    (image : normalForm (some unitLabel) source = .apply label targets) :
    ∃ arguments,source = .apply label arguments ∧ arguments.map (normalForm (some unitLabel)) = targets := by
  cases source with
  | apply actual arguments =>
    rw [normalForm_apply] at image
    obtain ⟨rfl,values⟩ := Pattern.apply.inj image
    exact ⟨arguments,rfl,values⟩
  | collection kind elements rest =>
    cases kind <;> cases rest <;> simp_all [normalForm,IsBagNode]
  | _ => simp only [normalForm] at image; cases image

private theorem normalForm_lambda_inverse {unitLabel : String} {source target : Pattern} {binder : Option String}
    (nonbag : ¬ IsBagNode source)
    (image : normalForm (some unitLabel) source = .lambda binder target) :
    ∃ body,source = .lambda binder body ∧ normalForm (some unitLabel) body = target := by
  cases source with
  | lambda actual body =>
    simp only [normalForm,Pattern.lambda.injEq] at image
    obtain ⟨rfl,bodyImage⟩ := image
    exact ⟨body,rfl,bodyImage⟩
  | collection kind elements rest =>
    cases kind <;> cases rest <;> simp_all [normalForm,IsBagNode]
  | _ => simp only [normalForm] at image; cases image

private theorem normalForm_multiLambda_inverse {unitLabel : String} {source target : Pattern}
    {arity : Nat} {binders : List String}
    (nonbag : ¬ IsBagNode source)
    (image : normalForm (some unitLabel) source = .multiLambda arity binders target) :
    ∃ body,source = .multiLambda arity binders body ∧ normalForm (some unitLabel) body = target := by
  cases source with
  | multiLambda actual actualNames body =>
    simp only [normalForm,Pattern.multiLambda.injEq] at image
    obtain ⟨rfl,rfl,bodyImage⟩ := image
    exact ⟨body,rfl,bodyImage⟩
  | collection kind elements rest =>
    cases kind <;> cases rest <;> simp_all [normalForm,IsBagNode]
  | _ => simp only [normalForm] at image; cases image

/-- Constructor descent recovers the actual original argument spine and
its authored declaration index. Temporary normalized children are not
mistaken for physical source occurrences. -/
theorem sourceHead_constructor {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {expected : TypeExpr} {source : Pattern}
    (good : Admissible language free bound expected source) (collectionless : collectionFree expected = true)
    {head : SourceHead} (found : sourceHead? (normalizedOccurrences unitLabel source) = some head)
    {label : String} {targets : List Pattern}
    (image : normalForm (some unitLabel) source = .apply label targets) :
    ∃ (arguments : List Pattern) (declarationIndex : Nat) (rule : GrammarRule),
      head.original unitLabel = .apply label arguments ∧
      arguments.map (normalForm (some unitLabel)) = targets ∧
      language.terms[declarationIndex]? = some rule ∧ rule.label = label ∧
      (.base rule.category : TypeExpr) = expected ∧ ¬ UsesBareCollection rule ∧
      ArgumentsHaveTypes language free bound arguments rule.params := by
  obtain ⟨originalGood,normalEq,_⟩ := sourceHead_readback laws base good collectionless found
  obtain ⟨arguments,spine,values⟩ := normalForm_apply_inverse (sourceHead_nonbag found) (normalEq.trans image)
  have typed := originalGood.typed
  rw [spine] at typed
  cases typed with
  | constructor member ordinary argumentsTyped =>
    obtain ⟨index,selected⟩ := List.mem_iff_getElem?.mp member
    exact ⟨arguments,index,_,spine,values,selected,rfl,rfl,ordinary,argumentsTyped⟩

/-- Binder descent keeps a genuine function role, its original body and
the complete extended local context. -/
theorem sourceHead_lambda {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    (good : Admissible language free bound expected source) (collectionless : collectionFree expected = true)
    {head : SourceHead} (found : sourceHead? (normalizedOccurrences unitLabel source) = some head)
    {binder : Option String} {target : Pattern}
    (image : normalForm (some unitLabel) source = .lambda binder target) :
    ∃ domain codomain body,expected = .arrow domain codomain ∧
      head.original unitLabel = .lambda binder body ∧ normalForm (some unitLabel) body = target ∧
      Admissible language free (domain :: bound) codomain body := by
  obtain ⟨originalGood,normalEq,_⟩ := sourceHead_readback laws base good collectionless found
  obtain ⟨body,spine,values⟩ := normalForm_lambda_inverse (sourceHead_nonbag found) (normalEq.trans image)
  have typed := originalGood.typed
  rw [spine] at typed
  cases typed with
  | lambda bodyTyped =>
    refine ⟨_,_,body,rfl,spine,values,bodyTyped,?_,?_⟩
    · have canonical := originalGood.canonical
      rw [spine] at canonical
      simp only [Pattern.hasCanonicalBinderMetadata,Bool.and_eq_true] at canonical
      exact canonical.2
    · have object := originalGood.object
      rw [spine] at object
      simpa only [isObjectPattern] using object

/-- Multi-binder readback retains the authored arity, original body and
actual repeated domain prefix. -/
theorem sourceHead_multiLambda {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}
    (good : Admissible language free bound expected source) (collectionless : collectionFree expected = true)
    {head : SourceHead} (found : sourceHead? (normalizedOccurrences unitLabel source) = some head)
    {arity : Nat} {binders : List String} {target : Pattern}
    (image : normalForm (some unitLabel) source = .multiLambda arity binders target) :
    ∃ domain codomain body,expected = .arrow (.multiBinder domain) codomain ∧
      head.original unitLabel = .multiLambda arity binders body ∧
      normalForm (some unitLabel) body = target ∧
      Admissible language free (List.replicate arity domain ++ bound) codomain body := by
  obtain ⟨originalGood,normalEq,_⟩ := sourceHead_readback laws base good collectionless found
  obtain ⟨body,spine,values⟩ := normalForm_multiLambda_inverse (sourceHead_nonbag found) (normalEq.trans image)
  have typed := originalGood.typed
  rw [spine] at typed
  cases typed with
  | multiLambda bodyTyped =>
    refine ⟨_,_,body,rfl,spine,values,bodyTyped,?_,?_⟩
    · have canonical := originalGood.canonical
      rw [spine] at canonical
      simp only [Pattern.hasCanonicalBinderMetadata,Bool.and_eq_true] at canonical
      exact canonical.2
    · have object := originalGood.object
      rw [spine] at object
      simpa only [isObjectPattern] using object

#print axioms sourceHead_isSome_of_scalar
#print axioms sourceHead_nonbag
#print axioms sourceHead_constructor
#print axioms sourceHead_lambda
#print axioms sourceHead_multiLambda

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep DerivedContexts Match MatchSpec GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

/-- Lift all schema slots together, conserving the original physical
records globally. Empty slot groups require no physical source occurrence. -/
theorem grouped_occurrences_of_values {α β : Type} (value : α → β)
    {occurrences : List α} :
    ∀ (groups : List (List β)) (residual : List β),
      (groups.flatten ++ residual).Perm (occurrences.map value) →
      ∃ physicalGroups physicalResidual,
        (physicalGroups,physicalResidual) ∈ groupedOccurrences groups.length occurrences ∧
        physicalGroups.map (List.map value) = groups ∧ physicalResidual.map value = residual
  | [],residual,account => by
    obtain ⟨selected,remaining,allocation,empty,last⟩ :=
      split_occurrences_of_values value (selected := []) (residual := residual) (by simpa using account)
    have selectedEmpty : selected = [] := List.map_eq_nil_iff.mp empty
    subst selected
    exact ⟨[],remaining,(mem_groupedOccurrences 0).mpr ⟨rfl,by simpa using mem_occurrenceSplits.mp allocation⟩,rfl,last⟩
  | group :: groups,residual,account => by
    obtain ⟨first,remaining,allocation,firstValues,remainingValues⟩ :=
      split_occurrences_of_values value (selected := group) (residual := groups.flatten ++ residual)
        (by simpa only [List.flatten_cons,List.append_assoc] using account)
    obtain ⟨later,last,laterAllocation,laterValues,lastValues⟩ :=
      grouped_occurrences_of_values value (occurrences := remaining) groups residual
        (by rw [remainingValues])
    have remainingAccount := (mem_groupedOccurrences groups.length).mp laterAllocation
    refine ⟨first :: later,last,(mem_groupedOccurrences (group :: groups).length).mpr ⟨?_,?_⟩,?_,lastValues⟩
    · simp only [List.length_cons,remainingAccount.1]
    · have combined := (remainingAccount.2.append_left first).trans (mem_occurrenceSplits.mp allocation)
      simpa only [List.flatten_cons,List.append_assoc] using combined
    · simp only [List.map_cons,firstValues,laterValues]

/-- The existing independent bag relation selects one row per schema slot
and leaves an exact residual. This inversion does not define a second
matching relation or change binding merge order. -/
theorem bag_selected_values {schemas targets : List Pattern} {rest : Option String}
    {kind : CollType} {bindings : Bindings}
    (matched : MatchBagRel schemas rest kind targets bindings) :
    ∃ selected residual,
      (selected ++ residual).Perm targets ∧
      List.Forall₂ (fun schema target => ∃ captured,MatchRel schema target captured) schemas selected ∧
      (rest = none → residual = []) ∧
      ∀ name,rest = some name → bindings.find? (fun entry => entry.1 == name) = some (name,.collection kind residual none) := by
  induction schemas generalizing targets bindings with
  | nil =>
    cases matched with
    | nilNoRest =>
      refine ⟨[],[],.refl _,.nil,fun _ => rfl,?_⟩
      intro name impossible
      cases impossible
    | nilRest =>
      refine ⟨[],_,.refl _,.nil,?_,?_⟩
      · intro impossible
        cases impossible
      · intro name equal
        cases Option.some.inj equal
        simp
  | cons schema schemas recurse =>
    cases matched with
    | cons index within head tail merged =>
      obtain ⟨selected,residual,account,rows,noRest,restRead⟩ := recurse tail
      refine ⟨_ :: selected,residual,?_,.cons ⟨_,head⟩ rows,noRest,?_⟩
      · exact (account.cons _).trans (List.getElem_cons_eraseIdx_perm within)
      · intro name restEq
        exact mergeBindings_subsumed_right merged (restRead name restEq)

#print axioms grouped_occurrences_of_values
#print axioms bag_selected_values

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep DerivedContexts Match MatchSpec GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

/-- Every finite ordinary bag match, at any schema arity, recovers one
physical group per selected source member and the exact source residual.
Nested member schemas retain their independent ordinary matching witnesses. -/
theorem source_groups_covered {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings,normalForm (some unitLabel) (applyBindings bindings row.left) =
          normalForm (some unitLabel) (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern} {elements schemas : List Pattern}
    (sourceGood : Admissible language free bound (.base bag.category) source)
    (representativeGood : Admissible language free bound (.base bag.category)
      (.collection .hashBag elements none))
    (equivalent : ReferenceStep.Equivalent relEnv language source (.collection .hashBag elements none))
    {rest : Option String} {bindings : Bindings}
    (matched : MatchBagRel schemas rest .hashBag elements bindings) :
    ∃ groups residual selected originalResidual,
      (groups,residual) ∈ groupedOccurrences schemas.length (normalizedOccurrences unitLabel source) ∧
      List.Forall₂ (fun schema target => ∃ captured,MatchRel schema target captured) schemas selected ∧
      groups.map (fun group => collapse unitLabel (group.map SourceOccurrence.value)) =
        selected.map (normalForm (some unitLabel)) ∧
      residual.map SourceOccurrence.value =
        bagContents unitLabel (originalResidual.map (normalForm (some unitLabel))) ∧
      (rest = none → originalResidual = []) ∧
      (∀ name,rest = some name → bindings.find? (fun entry => entry.1 == name) =
        some (name,.collection .hashBag originalResidual none)) ∧
      ((groups.flatten ++ residual) ++ unitOccurrences unitLabel source).Perm
        (sourceOccurrences unitLabel source) := by
  obtain ⟨selected,originalResidual,selectedAccount,selectedMatches,noRest,restRead⟩ := bag_selected_values matched
  have normalEqual := (reference_equivalent_iff_normalForm_eq laws rows aligned relEnv
    sourceGood representativeGood rfl).mp equivalent
  let valueGroups := selected.map (fun element => bagContents unitLabel [normalForm (some unitLabel) element])
  have groupContents : valueGroups.flatten = bagContents unitLabel (selected.map (normalForm (some unitLabel))) := by
    simpa only [valueGroups,List.flatMap] using bagContents_flatMap unitLabel selected
  have components := ((selectedAccount.map (normalForm (some unitLabel))).flatMap_right splice).filter
    (fun pattern => decide (pattern ≠ .apply unitLabel []))
  change (bagContents unitLabel ((selected ++ originalResidual).map (normalForm (some unitLabel)))).Perm
    (bagContents unitLabel (elements.map (normalForm (some unitLabel)))) at components
  rw [List.map_append,bagContents_append] at components
  have sortedAccount : (bagContents unitLabel (elements.map (normalForm (some unitLabel)))).Perm
      ((normalizedOccurrences unitLabel source).map SourceOccurrence.value) := by
    rw [normalizedOccurrences_values,normalEqual,normalForm_bag_contents]
    exact (sortPatterns_perm _).symm
  have account := components.trans sortedAccount
  rw [← groupContents] at account
  obtain ⟨groups,residual,allocation,groupValues,residualValues⟩ :=
    grouped_occurrences_of_values SourceOccurrence.value valueGroups
      (bagContents unitLabel (originalResidual.map (normalForm (some unitLabel)))) account
  have realAllocation : (groups,residual) ∈ groupedOccurrences schemas.length (normalizedOccurrences unitLabel source) := by
    have lengths : valueGroups.length = schemas.length := by simpa only [valueGroups,List.length_map] using selectedMatches.length_eq.symm
    simpa only [lengths] using allocation
  have values : groups.map (fun group => collapse unitLabel (group.map SourceOccurrence.value)) =
      selected.map (normalForm (some unitLabel)) := by
    have collapsed := congrArg (List.map (collapse unitLabel)) groupValues
    simp only [valueGroups,List.map_map,Function.comp_def] at collapsed
    refine collapsed.trans ?_
    exact List.map_congr_left (fun element _ => collapse_contents (rootNormal_normalForm unitLabel element))
  exact ⟨groups,residual,selected,originalResidual,realAllocation,selectedMatches,values,residualValues,
    noRest,restRead,grouped_occurrence_account realAllocation⟩

#print axioms source_groups_covered

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.ScopeBoundary

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

private def proc : TypeExpr := .base "Proc"
private def carrier : GrammarRule where
  label := "Parallel"
  category := "Proc"
  params := [.simple "processes" (.collection .hashBag proc)]
  syntaxPattern := []
  algebra? := some {flatten := true, unit := some "PZero"}

private def sourceLanguage : LanguageDef where
  name := "ScopedCaptureBoundary"
  types := [TypeDecl.plain "Proc"]
  terms := [
    {label := "PZero", category := "Proc", params := [], syntaxPattern := []},
    carrier,
    {label := "Pair", category := "Proc", params :=
      [.simple "first" (.arrow proc proc),
       .simple "later" (.arrow proc (.arrow proc (.arrow proc proc)))], syntaxPattern := []}]
  equations := []
  rewrites := []

private def free : FreeTypeContext := fun identifier =>
  if identifier == "" then some proc else none
private def schemaFree : FreeTypeContext := fun identifier =>
  if identifier == "F" then some proc else none
private def bag (elements : List Pattern) : Pattern := .collection .hashBag elements none
private def shallow : Pattern := bag [.bvar 0, .fvar ""]
private def deep : Pattern := bag [.bvar 2, .fvar ""]
private def value : ContextualValue := {dependencies := [proc], ambient := 0, body := shallow}
private def reversedValue : ContextualValue :=
  {dependencies := [proc], ambient := 0, body := bag [.fvar "", .bvar 0]}

private def specification : RuleBindingSpec where
  dependencies := [("F", [proc])]
  occurrences := [
    {name := "F", site := .left, path := [0, 0], arguments := [.bvar 0]},
    {name := "F", site := .left, path := [1, 0, 0, 0], arguments := [.bvar 2]}]
private def schema : Pattern :=
  .apply "Pair" [.lambda none (.fvar "F"),
    .lambda none (.lambda none (.lambda none (.fvar "F")))]
private def source : Pattern :=
  .apply "Pair" [.lambda none shallow, .lambda none (.lambda none (.lambda none deep))]
private def rule : RewriteRule where
  name := "ScopedPair"
  typeContext := [("F", proc)]
  premises := []
  left := schema
  right := .apply "PZero" []
  bindings := some specification

/-- The numeric ordering changes when the same dependency is represented
by a different local index, despite both occurrence spines being increasing. -/
theorem increasing_spine_order_separator :
    PatternCode.patternCode (.bvar 0) < PatternCode.patternCode (.fvar "") ∧
      PatternCode.patternCode (.fvar "") < PatternCode.patternCode (.bvar 2) ∧
      variableSpine? 1 [.bvar 0] = some [0] ∧
      variableSpine? 3 [.bvar 2] = some [2] ∧
      ([0] : List Nat).Pairwise (· < ·) ∧ ([2] : List Nat).Pairwise (· < ·) := by
  decide +kernel

private theorem short_spine_increasing {arguments : List Pattern} {depth : Nat} {indices : List Nat}
    (short : arguments.length ≤ 1)
    (spine : variableSpine? depth arguments = some indices) : indices.Pairwise (· < ·) := by
  have shape := CanonicalBags.variableSpine?_arguments spine
  have length : indices.length ≤ 1 := by
    simpa only [shape, List.length_map] using short
  cases indices with
  | nil => simp
  | cons first remaining =>
      cases remaining with
      | nil => simp
      | cons second later => simp only [List.length_cons] at length; omega

/-- The actual lookup contract supplies increasing spines at every site
and every usable depth, rather than only at the two displayed occurrences. -/
theorem all_spines_increasing : CanonicalBags.IncreasingSpines rule specification := by
  intro identifier site path arguments found depth indices spine
  unfold RuleBinding.arguments? at found
  simp only [bind, Option.bind_eq_some_iff, guard, pure] at found
  obtain ⟨dependencies, _, _, _, rest⟩ := found
  apply short_spine_increasing (arguments := arguments) ?_ spine
  cases rowsEq : specification.occurrences.filter
      (fun row => row.name == identifier && row.site == site && row.path == path) with
  | nil =>
      rw [rowsEq] at rest
      change (if dependencies.isEmpty then some [] else none) = some arguments at rest
      split at rest
      · cases rest; decide
      · cases rest
  | cons row rows =>
      cases rows with
      | nil =>
          rw [rowsEq] at rest
          change (if occurrenceDeclared rule row && row.arguments.length == dependencies.length
            then some row.arguments else none) = some arguments at rest
          split at rest
          · cases rest
            have member : row ∈ specification.occurrences := List.mem_of_mem_filter
              (by rw [rowsEq]; exact List.mem_cons_self)
            simp only [specification, List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl <;> decide
          · cases rest
      | cons other rows => simp [rowsEq] at rest

/-- These are genuine declared bag roles with fully typed local contexts. -/
theorem source_roles :
    BareBagTheory sourceLanguage carrier (some "PZero") ∧
      Admissible sourceLanguage free [proc] proc shallow ∧
      Admissible sourceLanguage free [proc, proc, proc] proc deep ∧
      Admissible sourceLanguage free [] proc source ∧
      Admissible sourceLanguage schemaFree [] proc schema := by
  refine ⟨(bagTheory_of_check (by decide +kernel)).asBare rfl, ?_, ?_, ?_, ?_⟩
  all_goals exact ⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩

theorem binding_metadata_admitted :
    admittedFor rule specification = true ∧ dependencySortsDeclared sourceLanguage specification = true := by
  decide +kernel

private theorem explicit_normal_forms :
    normalForm (some "PZero") shallow = shallow ∧
      normalForm (some "PZero") deep = bag [.fvar "", .bvar 2] ∧
      normalForm (some "PZero") source =
        .apply "Pair" [.lambda none shallow,
          .lambda none (.lambda none (.lambda none (bag [.fvar "", .bvar 2])))] := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp only [source, shallow, deep, bag, normalForm, normalFormList, true_and, ite_true]
    simp [normalizeBag, bagContents, splice, collapse, PatternCode.sortPatterns,
      List.mergeSort, List.MergeSort.Internal.splitInTwo,
      PatternCode.patternCode, PatternCode.stringCode, PatternCode.charListCode, Nat.pair]

/-- Both original targets recover one identical contextual value. Numeric
normalization changes the second recovered body and literal assignment fails. -/
theorem recovering_after_normalization_disagrees :
    recoverValue? [proc] 0 1 [.bvar 0] shallow = some value ∧
      recoverValue? [proc] 0 3 [.bvar 2] deep = some value ∧
      recoverValue? [proc] 0 1 [.bvar 0] (normalForm (some "PZero") shallow) = some value ∧
      recoverValue? [proc] 0 3 [.bvar 2] (normalForm (some "PZero") deep) = some reversedValue ∧
      assign [("F", value)] "F" reversedValue = none := by
  rw [explicit_normal_forms.1, explicit_normal_forms.2.1]
  decide +kernel

/-- The existing independent scoped matching judgment has the raw repeated
capture, while ordinary matching of the numeric-normalized target fails. -/
theorem scoped_matching_separator :
    GeneralScopedMatch.Matches rule specification 0 .left [] 0 [] schema source [("F", value)] ∧
      matchAt rule specification 0 .left [] 0 [] schema (normalForm (some "PZero") source) = [] := by
  constructor
  · exact GeneralScopedMatch.matchAt_iff.mp (by decide +kernel)
  · rw [explicit_normal_forms.2.2]
    decide +kernel

/-- The existing increasing-spine theorem still yields the intrinsic
lexical-root specialization and its actual canonical contextual captures. -/
theorem intrinsic_canonical_matching_positive :
    CanonicalBags.canonAssignment [("F", value)] ∈
      matchAt rule specification 0 .left [] 0 [] schema (CanonicalBags.canon source) := by
  apply GeneralScopedMatch.matchAt_iff.mpr
  simpa only [CanonicalBags.canonAssignment, List.map_nil] using
    CanonicalBags.matches_canon all_spines_increasing (by decide +kernel)
      scoped_matching_separator.1

#print axioms increasing_spine_order_separator
#print axioms all_spines_increasing
#print axioms source_roles
#print axioms binding_metadata_admitted
#print axioms recovering_after_normalization_disagrees
#print axioms scoped_matching_separator
#print axioms intrinsic_canonical_matching_positive

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.ScopeBoundary

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep DerivedContexts GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

def normalBodyComparison (unitLabel : String) (_identifier : String) (first second : Pattern) : Bool :=
  normalForm (some unitLabel) first == normalForm (some unitLabel) second

/-- The comparison's authority is the actual original source equivalence
on its admissible role, derived from the existing normalizer certificate.
This is a primitive body law, not a premise or whole-firing equivalence field. -/
theorem normalBodyComparison_iff_source {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings,normalForm (some unitLabel) (Match.applyBindings bindings row.left) =
          normalForm (some unitLabel) (Match.applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {expected : TypeExpr} {first second : Pattern}
    (firstGood : Admissible language free bound expected first)
    (secondGood : Admissible language free bound expected second)
    (collectionless : collectionFree expected = true) (identifier : String) :
    normalBodyComparison unitLabel identifier first second = true ↔ ReferenceStep.Equivalent relEnv language first second := by
  exact (beq_iff_eq : (normalForm (some unitLabel) first == normalForm (some unitLabel) second) = true ↔ _).trans
    (reference_equivalent_iff_normalForm_eq laws rows aligned relEnv firstGood secondGood collectionless).symm

open RuleBinding ScopedRuleMatching

/-- Repeated assignment checks its exact dependency and ambient headers
before admitting equality under the actual declared source equations. The
first raw contextual value remains stored on every successful repeat. -/
theorem assignWith_normal_repeat_iff_source
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unitLabel) (Match.applyBindings bindings row.left) =
          normalForm (some unitLabel) (Match.applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {dependencies ambient : List TypeExpr} {expected : TypeExpr}
    {initial : ScopedRuleMatching.Assignment} {identifier : String} {prior recovered : ContextualValue}
    (stored : lookup initial identifier = some prior)
    (priorGood : Admissible language free (dependencies ++ ambient) expected prior.body)
    (recoveredGood : Admissible language free (dependencies ++ ambient) expected recovered.body)
    (collectionless : collectionFree expected = true) :
    assignWith (normalBodyComparison unitLabel) initial identifier recovered = some initial ↔
      prior.dependencies = recovered.dependencies ∧ prior.ambient = recovered.ambient ∧
        ReferenceStep.Equivalent relEnv language prior.body recovered.body := by
  have bodyAuthority := normalBodyComparison_iff_source laws rows aligned relEnv
    priorGood recoveredGood collectionless identifier
  simp only [assignWith, stored]
  constructor
  · intro accepted
    split at accepted
    · rename_i checked
      obtain ⟨headers, compared⟩ := Bool.and_eq_true_iff.mp checked
      obtain ⟨dependenciesEqual, ambientEqual⟩ := Bool.and_eq_true_iff.mp headers
      exact ⟨beq_iff_eq.mp dependenciesEqual, beq_iff_eq.mp ambientEqual,
        bodyAuthority.mp compared⟩
    · cases accepted
  · rintro ⟨dependenciesEqual, ambientEqual, equivalent⟩
    simp only [dependenciesEqual, ambientEqual, beq_self_eq_true, Bool.true_and,
      bodyAuthority.mpr equivalent, ite_true]

/-- Actual occurrence lookup and inverse recovery feed the same source
comparison. This primitive does not assume matching or firing coherence. -/
theorem captureWith_normal_repeat_iff_source
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unitLabel) (Match.applyBindings bindings row.left) =
          normalForm (some unitLabel) (Match.applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {dependencies ambient locals : List TypeExpr} {expected : TypeExpr}
    {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite} {path : List Nat}
    {initial : ScopedRuleMatching.Assignment} {identifier : String}
    {arguments : List Pattern} {target : Pattern} {prior recovered : ContextualValue}
    (declared : dependencies? spec identifier = some dependencies)
    (atSite : arguments? rule spec identifier site path = some arguments)
    (recovery : recoverValue? dependencies ambient.length locals.length arguments target = some recovered)
    (stored : lookup initial identifier = some prior)
    (priorGood : Admissible language free (dependencies ++ ambient) expected prior.body)
    (recoveredGood : Admissible language free (dependencies ++ ambient) expected recovered.body)
    (collectionless : collectionFree expected = true) :
    captureWith? (normalBodyComparison unitLabel) rule spec ambient.length locals.length site path
        initial identifier target = some initial ↔
      prior.dependencies = recovered.dependencies ∧ prior.ambient = recovered.ambient ∧
        ReferenceStep.Equivalent relEnv language prior.body recovered.body := by
  simp only [captureWith?, declared, atSite, Option.bind_eq_bind, Option.bind_some, recovery]
  exact assignWith_normal_repeat_iff_source laws rows aligned relEnv stored
    priorGood recoveredGood collectionless

/-- Source-equivalent bodies cannot override a mismatched dependency
or ambient header. No equation certificate is needed for this rejection. -/
theorem assignWith_normal_wrong_header {unitLabel : String}
    {initial : ScopedRuleMatching.Assignment} {identifier : String} {prior recovered : ContextualValue}
    (stored : lookup initial identifier = some prior)
    (different : prior.dependencies ≠ recovered.dependencies ∨ prior.ambient ≠ recovered.ambient) :
    assignWith (normalBodyComparison unitLabel) initial identifier recovered = none := by
  unfold assignWith
  rw [stored]
  rcases different with dependenciesDifferent | ambientDifferent
  · have rejected : (prior.dependencies == recovered.dependencies) = false := by
      simp [dependenciesDifferent]
    simp only [rejected, Bool.false_and, Bool.false_eq_true, ite_false]
  · have rejected : (prior.ambient == recovered.ambient) = false := by
      simp [ambientDifferent]
    simp only [rejected, Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false]

#print axioms assignWith_normal_wrong_header
#print axioms assignWith_normal_repeat_iff_source
#print axioms captureWith_normal_repeat_iff_source

#print axioms normalBodyComparison_iff_source

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- The actual inverse occurrence substitution earns every admissibility
field from the original typed object and its sort-compatible partial spine.
No bound on dependency count or binder depth is imposed. -/
theorem recoverValue?_admissible_from_success
    {language : LanguageDef} {free : FreeTypeContext}
    {dependencies locals ambient : List TypeExpr} {expected : TypeExpr}
    {arguments : List Pattern} {indices : List Nat} {target : Pattern} {value : ContextualValue}
    (spineCheck : variableSpine? locals.length arguments = some indices)
    (spine : Mettapedia.GSLT.LanguageDef.RestAwareTyping.PartialSortedSpine dependencies locals indices)
    (targetGood : Admissible language free (locals ++ ambient) expected target)
    (recovered : recoverValue? dependencies ambient.length locals.length arguments target = some value) :
    value.dependencies = dependencies ∧ value.ambient = ambient.length ∧
      Admissible language free (dependencies ++ ambient) expected value.body := by
  have schemaTyped := Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType.ofObject
    targetGood.typed targetGood.object
  have typed := Mettapedia.GSLT.LanguageDef.RestAwareTyping.recoverValue?_partialSortedSpine_typed_from_success
    language free dependencies locals ambient arguments indices target expected value
    spineCheck spine schemaTyped recovered
  exact ⟨typed.1, typed.2.1, ⟨typed.2.2.forget,
    GeneralPremise.recoverValue?_canonical targetGood.canonical recovered,
    GeneralPremise.recoverValue?_objects targetGood.object recovered⟩⟩

/-- The new recovered body's admissibility is derived from its actual
caller target. The source repeat-check keeps the exact old headers and the
first stored value, with the existing declared-equation authority. -/
theorem captureWith_normal_typed_repeat_iff_source
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unitLabel) (Match.applyBindings bindings row.left) =
          normalForm (some unitLabel) (Match.applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {dependencies ambient locals : List TypeExpr} {expected : TypeExpr}
    {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite} {path : List Nat}
    {initial : ScopedRuleMatching.Assignment} {identifier : String}
    {arguments : List Pattern} {indices : List Nat} {target : Pattern} {prior recovered : ContextualValue}
    (declared : dependencies? spec identifier = some dependencies)
    (atSite : arguments? rule spec identifier site path = some arguments)
    (spineCheck : variableSpine? locals.length arguments = some indices)
    (spine : Mettapedia.GSLT.LanguageDef.RestAwareTyping.PartialSortedSpine dependencies locals indices)
    (targetGood : Admissible language free (locals ++ ambient) expected target)
    (recovery : recoverValue? dependencies ambient.length locals.length arguments target = some recovered)
    (stored : lookup initial identifier = some prior)
    (priorGood : Admissible language free (dependencies ++ ambient) expected prior.body)
    (collectionless : collectionFree expected = true) :
    captureWith? (normalBodyComparison unitLabel) rule spec ambient.length locals.length site path
        initial identifier target = some initial ↔
      prior.dependencies = dependencies ∧ prior.ambient = ambient.length ∧
        ReferenceStep.Equivalent relEnv language prior.body recovered.body := by
  have good := recoverValue?_admissible_from_success spineCheck spine targetGood recovery
  simpa only [good.1, good.2.1] using
    captureWith_normal_repeat_iff_source laws rows aligned relEnv declared atSite recovery stored
      priorGood good.2.2 collectionless

#print axioms recoverValue?_admissible_from_success
#print axioms captureWith_normal_typed_repeat_iff_source

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.ScopeBoundary

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- A proper partial spine with two dependencies and four local binders
recovers its actual two-variable body with the declared base sort. -/
theorem two_dependency_partial_recovery_admissible :
    ∃ captured,
      recoverValue? [proc, proc] 0 4 [.bvar 0, .bvar 2]
        (bag [.bvar 0, .bvar 2]) = some captured ∧
      captured.dependencies = [proc, proc] ∧ captured.ambient = 0 ∧
      Admissible sourceLanguage free [proc, proc] proc captured.body := by
  let captured : ContextualValue :=
    {dependencies := [proc, proc], ambient := 0, body := bag [.bvar 0, .bvar 1]}
  have recovered : recoverValue? [proc, proc] 0 4 [.bvar 0, .bvar 2]
      (bag [.bvar 0, .bvar 2]) = some captured := by decide +kernel
  have spineCheck : variableSpine? ([proc, proc, proc, proc] : List TypeExpr).length
      [.bvar 0, .bvar 2] = some [0, 2] := by decide +kernel
  have spine : Mettapedia.GSLT.LanguageDef.RestAwareTyping.PartialSortedSpine
      [proc, proc] [proc, proc, proc, proc] [0, 2] := by
    refine ⟨rfl, ?_, ?_⟩
    · intro index member
      rcases (by simpa using member : index = 0 ∨ index = 2) with rfl | rfl <;> decide
    · intro index member
      rcases (by simpa using member : index = 0 ∨ index = 2) with rfl | rfl <;> decide
  have targetGood : Admissible sourceLanguage free
      ([proc, proc, proc, proc] ++ []) proc (bag [.bvar 0, .bvar 2]) :=
    ⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩
  exact ⟨captured, recovered, recoverValue?_admissible_from_success spineCheck spine targetGood recovered⟩

private def other : TypeExpr := .base "Other"
private def mismatchLanguage : LanguageDef :=
  {sourceLanguage with types := [TypeDecl.plain "Proc", TypeDecl.plain "Other"]}
private def mismatchedValue : ContextualValue :=
  {dependencies := [other], ambient := 0, body := .bvar 0}

/-- Raw inverse recovery ignores the dependency sorts. Actual target typing
and admitted sorts therefore do not replace the sorted-spine obligation. -/
theorem wrong_dependency_sort_separator :
    Admissible mismatchLanguage free [proc] proc (.bvar 0) ∧
      recoverValue? [other] 0 1 [.bvar 0] (.bvar 0) = some mismatchedValue ∧
      ¬ Mettapedia.GSLT.LanguageDef.RestAwareTyping.PartialSortedSpine [other] [proc] [0] ∧
      ¬ Admissible mismatchLanguage free [other] proc mismatchedValue.body := by
  refine ⟨⟨HasType.bvar rfl, rfl, rfl⟩, by decide +kernel, ?_, ?_⟩
  · intro spine
    have mismatch := spine.sorts 0 (by simp)
    simp [other, proc] at mismatch
  · intro good
    have typed := good.typed
    change HasType mismatchLanguage free [other] (.bvar 0) proc at typed
    cases typed with
    | bvar lookup => simp [other, proc] at lookup

#print axioms two_dependency_partial_recovery_admissible
#print axioms wrong_dependency_sort_separator

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.ScopeBoundary

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations

open Mettapedia.OSLF.MeTTaIL Syntax

/-- Flattening is invariant under the existing numeric bag normal form. -/
theorem normalForm_flatten (unit : String) (before inner after : List Pattern) :
    normalForm (some unit) (.collection .hashBag (before ++ .collection .hashBag inner none :: after) none) =
      normalForm (some unit) (.collection .hashBag (before ++ inner ++ after) none) := by
  rw [normalForm_bag, normalForm_bag]
  apply normalizeBag_contents_perm
  simp only [List.map_append, List.map_cons, bagContents_append, List.append_assoc]
  rw [bagContents_cons unit (normalForm (some unit) (.collection .hashBag inner none))]
  refine List.Perm.append_left _ (List.Perm.append_right _ ?_)
  rw [normalForm_bag]
  simp only [normalizeBag]
  rw [bagContents_collapse]
  · exact sortPatterns_perm _
  · intro component membership
    apply bagContents_spec (elements := inner.map (normalForm (some unit)))
    · intro element elementMember
      obtain ⟨original, _, rfl⟩ := List.mem_map.mp elementMember
      exact rootNormal_normalForm unit original
    · exact mem_sortPatterns.mp membership

private theorem substitute_bag_perm (unit : String) (assignment : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment)
    {first second : List Pattern} (permutation : first.Perm second) :
    normalForm (some unit) (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment (.collection .hashBag first none)) =
      normalForm (some unit) (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment (.collection .hashBag second none)) := by
  simp only [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList_eq_map, normalForm_bag]
  exact normalizeBag_perm _ ((permutation.map (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment)).map (normalForm (some unit)))

private theorem substitute_bag_flatten (unit : String) (assignment : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment)
    (before inner after : List Pattern) :
    normalForm (some unit) (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment
      (.collection .hashBag (before ++ .collection .hashBag inner none :: after) none)) =
      normalForm (some unit) (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment
        (.collection .hashBag (before ++ inner ++ after) none)) := by
  simpa only [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList_eq_map,
    List.map_append, List.map_cons] using
    normalForm_flatten unit (before.map (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment))
      (inner.map (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment)) (after.map (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment))

private theorem substitute_bag_unit (unit : String) (assignment : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment)
    (before after : List Pattern) :
    normalForm (some unit) (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment
      (.collection .hashBag (before ++ .apply unit [] :: after) none)) =
      normalForm (some unit) (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment
        (.collection .hashBag (before ++ after) none)) := by
  simpa only [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList_eq_map,
    List.map_append, List.map_cons, List.map_nil] using
    normalForm_insert_unit unit (before.map (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment))
      (after.map (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment))

private theorem substitute_collapse (unit : String) (assignment : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment)
    (elements : List Pattern) :
    normalForm (some unit) (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment (collapse unit elements)) =
      normalForm (some unit) (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment (.collection .hashBag elements none)) := by
  cases elements with
  | nil =>
      simp [collapse, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList,
        normalForm, normalFormList, normalizeBag]
  | cons first later =>
      cases later with
      | nil =>
          simp only [collapse, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList]
          exact (normalForm_singleton unit (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment first)).symm
      | cons second rest => rfl

private theorem substitute_bagContents (unit : String) (assignment : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment)
    (elements : List Pattern) (normal : ∀ element ∈ elements, RootNormal unit element)
    (before after : List Pattern) :
    normalForm (some unit) (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment
      (.collection .hashBag (before ++ bagContents unit elements ++ after) none)) =
      normalForm (some unit) (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment
        (.collection .hashBag (before ++ elements ++ after) none)) := by
  induction elements generalizing before with
  | nil => simp
  | cons head tail recurse =>
      have tailNormal : ∀ element ∈ tail, RootNormal unit element :=
        fun element member => normal element (by simp [member])
      by_cases unitHead : head = .apply unit []
      · subst head
        have contents : bagContents unit [.apply unit []] = [] := by simp [bagContents, splice]
        rw [bagContents_cons, contents, List.nil_append]
        refine (recurse tailNormal before).trans ?_
        simpa only [List.append_assoc, List.cons_append] using (substitute_bag_unit unit assignment before (tail ++ after)).symm
      · by_cases bagHead : IsBagNode head
        · obtain ⟨inner, rfl⟩ := bagHead
          have plain := (normal _ (by simp) inner rfl).2.2
          have contents : bagContents unit [.collection .hashBag inner none] = inner := by
            simp only [bagContents, List.flatMap_cons, List.flatMap_nil, List.append_nil, splice_bag]
            apply List.filter_eq_self.mpr
            intro element member
            simpa using (plain element member).1
          rw [bagContents_cons, contents]
          calc
            _ = normalForm (some unit) (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment
                (.collection .hashBag ((before ++ inner) ++ bagContents unit tail ++ after) none)) := by
                  simp only [List.append_assoc]
            _ = normalForm (some unit) (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment
                (.collection .hashBag ((before ++ inner) ++ tail ++ after) none)) := recurse tailNormal (before ++ inner)
            _ = _ := by
              simpa only [List.append_assoc, List.cons_append] using
                (substitute_bag_flatten unit assignment before inner (tail ++ after)).symm
        · have contents : bagContents unit [head] = [head] := by
            simp [bagContents, splice_of_not_bag bagHead, unitHead]
          rw [bagContents_cons, contents]
          simpa only [List.append_assoc, List.singleton_append] using recurse tailNormal (before ++ [head])

private theorem substitute_normalizeBag (unit : String) (assignment : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment)
    (elements : List Pattern) (normal : ∀ element ∈ elements, RootNormal unit element) :
    normalForm (some unit) (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment (normalizeBag (some unit) elements)) =
      normalForm (some unit) (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment (.collection .hashBag elements none)) := by
  change normalForm (some unit) (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment
    (collapse unit (PatternCode.sortPatterns (bagContents unit elements)))) = _
  rw [substitute_collapse]
  refine (substitute_bag_perm unit assignment (sortPatterns_perm _)).trans ?_
  simpa using substitute_bagContents unit assignment elements normal [] []

/-- Normalizing after actual forward context substitution is compositional.
Assignments are arbitrary and binder cases use the executable lifted action;
this does not assert that inverse recovery commutes with numeric sorting. -/
theorem normalForm_substitute_normalForm (unit : String) (assignment : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment)
    (pattern : Pattern) :
    normalForm (some unit) (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment (normalForm (some unit) pattern)) =
      normalForm (some unit) (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment pattern) := by
  induction pattern using Pattern.inductionOn generalizing assignment with
  | hbvar index => simp only [normalForm]
  | hfvar identifier => simp only [normalForm]
  | happly label arguments recurse =>
      simp only [normalForm_apply, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList_eq_map,
        List.map_map, Function.comp_def]
      apply congrArg (Pattern.apply label)
      exact List.map_congr_left (fun element member => recurse element member assignment)
  | hlambda binder body recurse =>
      simp only [normalForm, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, recurse]
  | hmultiLambda arity binders body recurse =>
      simp only [normalForm, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, recurse]
  | hsubst body replacement bodyRecurse replacementRecurse =>
      simp only [normalForm, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, bodyRecurse, replacementRecurse]
  | hcollection kind elements rest recurse =>
      by_cases closedBag : kind = .hashBag ∧ rest = none
      · obtain ⟨rfl, rfl⟩ := closedBag
        have normal : ∀ element ∈ elements.map (normalForm (some unit)), RootNormal unit element := by
          intro element member
          obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
          exact rootNormal_normalForm unit original
        rw [normalForm_bag, substitute_normalizeBag unit assignment _ normal]
        simp only [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList_eq_map,
          normalForm_bag, List.map_map, Function.comp_def]
        congr 1
        exact List.map_congr_left (fun element member => recurse element member assignment)
      · simp only [normalForm, closedBag, if_false, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute,
          Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substituteList_eq_map, normalFormList_eq_map, List.map_map, Function.comp_def]
        apply congrArg (fun values => Pattern.collection kind values rest)
        exact List.map_congr_left (fun element member => recurse element member assignment)

/-- Equality in the existing algebra normal form survives the same actual
forward bound substitution, even when that substitution changes sort order. -/
theorem normalForm_substitute_congr (unit : String) (assignment : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment)
    {first second : Pattern}
    (equal : normalForm (some unit) first = normalForm (some unit) second) :
    normalForm (some unit) (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment first) =
      normalForm (some unit) (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment second) := by
  rw [← normalForm_substitute_normalForm unit assignment first,
    ← normalForm_substitute_normalForm unit assignment second, equal]

open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem admissible_argument_properties
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {arguments : List Pattern} {dependencies : List TypeExpr}
    (good : List.Forall₂ (fun argument dependency => Admissible language free bound dependency argument)
      arguments dependencies) :
    ∀ argument ∈ arguments,
      argument.hasCanonicalBinderMetadata = true ∧ isObjectPattern argument = true := by
  induction good with
  | nil => intro argument member; cases member
  | cons first later recurse =>
      intro argument member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨first.canonical, first.object⟩
      · exact recurse argument member

private theorem occurrenceAssignment_properties (dependencies depth : Nat) (arguments : List Pattern)
    (good : ∀ argument ∈ arguments,
      argument.hasCanonicalBinderMetadata = true ∧ isObjectPattern argument = true) :
    ∀ index, ((RuleBinding.occurrenceAssignment dependencies depth arguments) index).hasCanonicalBinderMetadata = true ∧
      isObjectPattern ((RuleBinding.occurrenceAssignment dependencies depth arguments) index) = true := by
  intro index
  unfold RuleBinding.occurrenceAssignment
  split
  · rw [List.getD_eq_getElem?_getD]
    cases entry : arguments[index]? with
    | none => exact ⟨rfl, rfl⟩
    | some argument => exact good argument (List.mem_of_getElem? entry)
  · exact ⟨rfl, rfl⟩

/-- The actual forward occurrence action preserves typing, objecthood and
canonical metadata using the declared types of its complete argument spine. -/
theorem occurrence_substitution_admissible
    {language : LanguageDef} {free : FreeTypeContext}
    {dependencies ambient locals : List TypeExpr} {body : Pattern} {expected : TypeExpr}
    {arguments : List Pattern}
    (bodyGood : Admissible language free (dependencies ++ ambient) expected body)
    (argumentsGood : List.Forall₂
      (fun argument dependency => Admissible language free (locals ++ ambient) dependency argument)
      arguments dependencies) :
    Admissible language free (locals ++ ambient) expected
      (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
        (RuleBinding.occurrenceAssignment dependencies.length locals.length arguments) body) := by
  have argumentsTyped := List.Forall₂.imp (fun _ _ good => good.typed) argumentsGood
  have images := occurrenceAssignment_properties dependencies.length locals.length arguments
    (admissible_argument_properties argumentsGood)
  exact ⟨bodyGood.typed.substituteOccurrenceList argumentsTyped,
    GeneralPremise.contextSubstitute_canonical bodyGood.canonical (fun index => (images index).1),
    GeneralPremise.contextSubstitute_objects bodyGood.object (fun index => (images index).2)⟩

private theorem instantiateValue?_recorded_typed
    {language : LanguageDef} {free : FreeTypeContext}
    {dependencies ambient locals : List TypeExpr} {expected : TypeExpr}
    {value : RuleBinding.ContextualValue} {arguments : List Pattern}
    (headers : value.dependencies = dependencies ∧ value.ambient = ambient.length)
    (bodyTyped : HasType language free (dependencies ++ ambient) value.body expected)
    (argumentsTyped : List.Forall₂
      (fun argument dependency => HasType language free (locals ++ ambient) argument dependency)
      arguments dependencies) :
    RuleBinding.instantiateValue? value ambient.length locals.length arguments =
      some (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute
        (RuleBinding.occurrenceAssignment dependencies.length locals.length arguments) value.body) := by
  cases value with
  | mk valueDependencies valueAmbient body =>
      dsimp only at headers bodyTyped ⊢
      obtain ⟨dependenciesEqual, ambientEqual⟩ := headers
      subst valueDependencies
      subst valueAmbient
      exact instantiateValue?_typedList bodyTyped argumentsTyped

/-- Source-equivalent typed captured bodies yield source-equivalent actual
occurrence results. All result fields come from the real checked action,
including dependency arguments and ambient-to-local rebasing under binders. -/
theorem source_equivalent_instantiated_values
    {language : LanguageDef} {bag : GrammarRule} {unit : String}
    (laws : BareBagTheory {language with equations := []} bag (some unit))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unit) (Match.applyBindings bindings row.left) =
          normalForm (some unit) (Match.applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {dependencies ambient locals : List TypeExpr} {expected : TypeExpr}
    {first second : RuleBinding.ContextualValue} {arguments : List Pattern}
    (firstHeaders : first.dependencies = dependencies ∧ first.ambient = ambient.length)
    (secondHeaders : second.dependencies = dependencies ∧ second.ambient = ambient.length)
    (firstGood : Admissible language free (dependencies ++ ambient) expected first.body)
    (secondGood : Admissible language free (dependencies ++ ambient) expected second.body)
    (argumentsGood : List.Forall₂
      (fun argument dependency => Admissible language free (locals ++ ambient) dependency argument)
      arguments dependencies)
    (collectionless : collectionFree expected = true)
    (equivalent : ReferenceStep.Equivalent relEnv language first.body second.body) :
    ∃ firstTarget secondTarget,
      RuleBinding.instantiateValue? first ambient.length locals.length arguments = some firstTarget ∧
      RuleBinding.instantiateValue? second ambient.length locals.length arguments = some secondTarget ∧
      Admissible language free (locals ++ ambient) expected firstTarget ∧
      Admissible language free (locals ++ ambient) expected secondTarget ∧
      ReferenceStep.Equivalent relEnv language firstTarget secondTarget := by
  have argumentsTyped := List.Forall₂.imp (fun _ _ good => good.typed) argumentsGood
  let assignment := RuleBinding.occurrenceAssignment dependencies.length locals.length arguments
  let firstTarget := Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment first.body
  let secondTarget := Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment second.body
  have firstTargetGood := occurrence_substitution_admissible firstGood argumentsGood
  have secondTargetGood := occurrence_substitution_admissible secondGood argumentsGood
  have bodiesEqual := (reference_equivalent_iff_normalForm_eq laws rows aligned relEnv
    firstGood secondGood collectionless).mp equivalent
  have targetsEqual := normalForm_substitute_congr unit assignment bodiesEqual
  refine ⟨firstTarget, secondTarget,
    instantiateValue?_recorded_typed firstHeaders firstGood.typed argumentsTyped,
    instantiateValue?_recorded_typed secondHeaders secondGood.typed argumentsTyped,
    firstTargetGood, secondTargetGood, ?_⟩
  exact (reference_equivalent_iff_normalForm_eq laws rows aligned relEnv
    firstTargetGood secondTargetGood collectionless).mpr targetsEqual

#print axioms occurrence_substitution_admissible
#print axioms source_equivalent_instantiated_values

#print axioms normalForm_flatten
#print axioms normalForm_substitute_normalForm
#print axioms normalForm_substitute_congr

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.ForwardScopeControls

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding
open Mettapedia.GSLT.LanguageDef.WellSorted

private def proc : TypeExpr := .base "P"
private def bag (elements : List Pattern) : Pattern := .collection .hashBag elements none
private def carrier : GrammarRule where
  label := "Par"
  category := "P"
  params := [.simple "items" (.collection .hashBag proc)]
  syntaxPattern := []
  algebra? := some {flatten := true, unit := some "Z"}
private def language : LanguageDef where
  name := "ForwardScope"
  types := [TypeDecl.plain "P"]
  terms := [{label := "Z", category := "P", params := [], syntaxPattern := []}, carrier]
  equations := []
  rewrites := []
private def firstBody : Pattern := .lambda none
  (bag [.bvar 0, bag [.bvar 2], .apply "Z" [], .bvar 1, .bvar 3])
private def secondBody : Pattern := .lambda none (bag [.bvar 3, .bvar 2, .bvar 1, .bvar 0])
private def firstValue : ContextualValue := {dependencies := [proc, proc], ambient := 1, body := firstBody}
private def secondValue : ContextualValue := {dependencies := [proc, proc], ambient := 1, body := secondBody}
private def arguments : List Pattern := [bag [.bvar 0, .apply "Z" []], .bvar 2]
private def firstResult : Pattern := .lambda none
  (bag [.bvar 0, bag [.bvar 3], .apply "Z" [], bag [.bvar 1, .apply "Z" []], .bvar 4])
private def secondResult : Pattern := .lambda none
  (bag [.bvar 4, .bvar 3, bag [.bvar 1, .apply "Z" []], .bvar 0])

private theorem body_normals_equal : normalForm (some "Z") firstBody = normalForm (some "Z") secondBody := by
  have inner :
      normalForm (some "Z") (bag [.bvar 0, bag [.bvar 2], .apply "Z" [], .bvar 1, .bvar 3]) =
        normalForm (some "Z") (bag [.bvar 3, .bvar 2, .bvar 1, .bvar 0]) := by
    calc
      _ = normalForm (some "Z") (bag [.bvar 0, .bvar 2, .apply "Z" [], .bvar 1, .bvar 3]) :=
        normalForm_flatten "Z" [.bvar 0] [.bvar 2] [.apply "Z" [], .bvar 1, .bvar 3]
      _ = normalForm (some "Z") (bag [.bvar 0, .bvar 2, .bvar 1, .bvar 3]) :=
        normalForm_insert_unit "Z" [.bvar 0, .bvar 2] [.bvar 1, .bvar 3]
      _ = _ := by
        rw [show bag [.bvar 0, .bvar 2, .bvar 1, .bvar 3] =
          .collection .hashBag [.bvar 0, .bvar 2, .bvar 1, .bvar 3] none from rfl]
        rw [show bag [.bvar 3, .bvar 2, .bvar 1, .bvar 0] =
          .collection .hashBag [.bvar 3, .bvar 2, .bvar 1, .bvar 0] none from rfl]
        rw [normalForm_bag, normalForm_bag]
        exact normalizeBag_perm _ ((by decide +kernel :
          ([.bvar 0, .bvar 2, .bvar 1, .bvar 3] : List Pattern).Perm [.bvar 3, .bvar 2, .bvar 1, .bvar 0]).map _)
  simpa only [firstBody, secondBody, normalForm] using congrArg (Pattern.lambda none) inner

/-- Two dependencies include a nonvariable argument containing the unit.
The real action moves the ambient index from three to four beneath a binder,
retains the raw grouped/unit presentations, and earns source equivalence. -/
theorem typed_rebased_unit_results (relEnv : Engine.RelationEnv) :
    instantiateValue? firstValue 1 3 arguments = some firstResult ∧
      instantiateValue? secondValue 1 3 arguments = some secondResult ∧
      Admissible language FreeTypeContext.empty [proc, proc, proc, proc] (.arrow proc proc) firstResult ∧
      Admissible language FreeTypeContext.empty [proc, proc, proc, proc] (.arrow proc proc) secondResult ∧
      ReferenceStep.Equivalent relEnv language firstResult secondResult := by
  have laws : BareBagTheory {language with equations := []} carrier (some "Z") :=
    (bagTheory_of_check (by decide +kernel)).asBare rfl
  have firstGood : Admissible language FreeTypeContext.empty ([proc, proc] ++ [proc])
      (.arrow proc proc) firstBody :=
    ⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩
  have secondGood : Admissible language FreeTypeContext.empty ([proc, proc] ++ [proc])
      (.arrow proc proc) secondBody :=
    ⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩
  have argsGood : List.Forall₂
      (fun argument dependency => Admissible language FreeTypeContext.empty
        ([proc, proc, proc] ++ [proc]) dependency argument) arguments [proc, proc] := by
    refine .cons ?_ (.cons ?_ .nil)
    all_goals exact ⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩
  have bodyEquivalent := (reference_equivalent_iff_normalForm_eq laws
    (by intro row member; cases member) (by intro row member; cases member) relEnv firstGood secondGood (by rfl)).mpr body_normals_equal
  obtain ⟨firstTarget, secondTarget, firstRun, secondRun, firstTyped, secondTyped, equivalent⟩ :=
    source_equivalent_instantiated_values laws (by intro row member; cases member)
      (by intro row member; cases member) relEnv
      (dependencies := [proc, proc]) (ambient := [proc]) (locals := [proc, proc, proc])
      (expected := .arrow proc proc) (first := firstValue) (second := secondValue) (arguments := arguments)
      (by exact ⟨rfl, rfl⟩) (by exact ⟨rfl, rfl⟩) firstGood secondGood argsGood (by rfl) bodyEquivalent
  have firstComputed : instantiateValue? firstValue 1 3 arguments = some firstResult := by decide +kernel
  have secondComputed : instantiateValue? secondValue 1 3 arguments = some secondResult := by decide +kernel
  have firstEq : firstResult = firstTarget := Option.some.inj (firstComputed.symm.trans firstRun)
  have secondEq : secondResult = secondTarget := Option.some.inj (secondComputed.symm.trans secondRun)
  subst firstTarget
  subst secondTarget
  exact ⟨firstComputed, secondComputed, firstTyped, secondTyped, equivalent⟩

/-- The operational scope guard rejects an escaped supplied argument. -/
theorem escaped_argument_rejected :
    instantiateValue? {dependencies := [proc], ambient := 0, body := .bvar 0}
      0 1 [.bvar 1] = none := by decide +kernel

private def other : TypeExpr := .base "Q"
private def twoSorts : LanguageDef := {language with types := [TypeDecl.plain "P", TypeDecl.plain "Q"]}

/-- Scope and arity checks alone accept this wrong-sort argument. The typed
argument premise rules it out, and the raw result has the wrong endpoint type. -/
theorem wrong_sort_forward_separator :
    Admissible twoSorts FreeTypeContext.empty [proc] proc (.bvar 0) ∧
      instantiateValue? {dependencies := [proc], ambient := 0, body := .bvar 0}
        0 1 [.bvar 0] = some (.bvar 0) ∧
      ¬ Admissible twoSorts FreeTypeContext.empty [other] proc (.bvar 0) := by
  refine ⟨⟨HasType.bvar rfl, rfl, rfl⟩, by decide +kernel, ?_⟩
  intro good
  have typed := good.typed
  cases typed with
  | bvar lookup => simp [proc, other] at lookup

#print axioms typed_rebased_unit_results
#print axioms escaped_argument_rejected
#print axioms wrong_sort_forward_separator

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.ForwardScopeControls

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem homogeneous_data_root {language : LanguageDef} {bag : GrammarRule} {unit : Option String}
    (laws : BareBagTheory {language with equations := []} bag unit)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern}
    (good : Admissible language free bound (.collection .hashBag (.base bag.category)) pattern) :
    ((∃ index, pattern = .bvar index) ∨ (∃ identifier, pattern = .fvar identifier)) ∨
      Admissible language free bound (.base bag.category) pattern := by
  obtain ⟨typed, canonical, object⟩ := good
  cases typed with
  | bvar lookup => exact .inl (.inl ⟨_, rfl⟩)
  | fvar lookup => exact .inl (.inr ⟨_, rfl⟩)
  | collection elements =>
      obtain ⟨parameter, shape⟩ := laws.bareShape
      exact .inr ⟨HasType.collectionConstructor (by simpa using laws.bagAuthored) shape elements,
        canonical, object⟩
  | subst body replacement => simp [isObjectPattern] at object

private theorem normalForm_variable {unit : Option String} {pattern : Pattern}
    (isVariable : (∃ index, pattern = .bvar index) ∨ (∃ identifier, pattern = .fvar identifier)) :
    normalForm unit pattern = pattern := by
  rcases isVariable with ⟨index, rfl⟩ | ⟨identifier, rfl⟩ <;> simp only [normalForm]

private theorem data_variable_not_carrier {language : LanguageDef} {bag : GrammarRule}
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern}
    (isVariable : (∃ index, pattern = .bvar index) ∨ (∃ identifier, pattern = .fvar identifier))
    (dataTyped : HasType language free bound pattern (.collection .hashBag (.base bag.category)))
    (carrierTyped : HasType language free bound pattern (.base bag.category)) : False := by
  rcases isVariable with ⟨index, rfl⟩ | ⟨identifier, rfl⟩
  · cases dataTyped with
    | bvar first =>
        cases carrierTyped with
        | bvar second =>
            have impossible := Option.some.inj (first.symm.trans second)
            cases impossible
  · cases dataTyped with
    | fvar first =>
        cases carrierTyped with
        | fvar second =>
            have impossible := Option.some.inj (first.symm.trans second)
            cases impossible

/-- On the actual homogeneous bag-data fibre, equality is decided by the
existing source normal form. This is comparison authority, not a typed
normalization section: both original outer containers remain unchanged. -/
theorem reference_equivalent_iff_normalForm_eq_data
    {language : LanguageDef} {bag : GrammarRule} {unit : Option String}
    (laws : BareBagTheory {language with equations := []} bag unit)
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm unit (Match.applyBindings bindings row.left) =
          normalForm unit (Match.applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {first second : Pattern}
    (firstGood : Admissible language free bound (.collection .hashBag (.base bag.category)) first)
    (secondGood : Admissible language free bound (.collection .hashBag (.base bag.category)) second) :
    ReferenceStep.Equivalent relEnv language first second ↔ normalForm unit first = normalForm unit second := by
  constructor
  · intro related
    exact source_normalForm_eq_of_equationEquiv laws.toBagTheory rows firstGood.object secondGood.object
      ((ReferenceStep.equivalent_iff_unconditional (fun row member => (rows row member).1) aligned).mpr related)
  · intro same
    rcases homogeneous_data_root laws firstGood with firstVariable | firstCarrier
    · rcases homogeneous_data_root laws secondGood with secondVariable | secondCarrier
      · rw [normalForm_variable firstVariable, normalForm_variable secondVariable] at same
        subst second
        exact .refl _
      · rw [normalForm_variable firstVariable] at same
        have normalized := normalized_admissible laws (ContextualStep.engineBasePremises relEnv) secondCarrier rfl
        exact (data_variable_not_carrier firstVariable firstGood.typed (same.symm ▸ normalized.typed)).elim
    · rcases homogeneous_data_root laws secondGood with secondVariable | secondCarrier
      · rw [normalForm_variable secondVariable] at same
        have normalized := normalized_admissible laws (ContextualStep.engineBasePremises relEnv) firstCarrier rfl
        exact (data_variable_not_carrier secondVariable secondGood.typed (same ▸ normalized.typed)).elim
      · exact (reference_equivalent_iff_normalForm_eq laws rows aligned relEnv firstCarrier secondCarrier rfl).mpr same

/-- A repeated data capture keeps its data role. The normal-form comparison
is justified on those original typed endpoints without replacing either body. -/
theorem normalBodyComparison_iff_source_data
    {language : LanguageDef} {bag : GrammarRule} {unit : String}
    (laws : BareBagTheory {language with equations := []} bag (some unit))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unit) (Match.applyBindings bindings row.left) =
          normalForm (some unit) (Match.applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {first second : Pattern}
    (firstGood : Admissible language free bound (.collection .hashBag (.base bag.category)) first)
    (secondGood : Admissible language free bound (.collection .hashBag (.base bag.category)) second)
    (identifier : String) :
    AlgebraFocus.RecursiveView.normalBodyComparison unit identifier first second = true ↔
      ReferenceStep.Equivalent relEnv language first second := by
  exact (beq_iff_eq : (normalForm (some unit) first == normalForm (some unit) second) = true ↔ _).trans
    (reference_equivalent_iff_normalForm_eq_data laws rows aligned relEnv firstGood secondGood).symm

/-- Successful repeated assignment at a bag-data role requires the exact
stored headers and actual source equality of its original data endpoints. -/
theorem assignWith_normal_data_repeat_iff_source
    {language : LanguageDef} {bag : GrammarRule} {unit : String}
    (laws : BareBagTheory {language with equations := []} bag (some unit))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unit) (Match.applyBindings bindings row.left) =
          normalForm (some unit) (Match.applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr}
    {initial : ScopedRuleMatching.Assignment} {identifier : String} {prior recovered : ContextualValue}
    (stored : lookup initial identifier = some prior)
    (priorGood : Admissible language free bound (.collection .hashBag (.base bag.category)) prior.body)
    (recoveredGood : Admissible language free bound (.collection .hashBag (.base bag.category)) recovered.body) :
    assignWith (AlgebraFocus.RecursiveView.normalBodyComparison unit) initial identifier recovered = some initial ↔
      prior.dependencies = recovered.dependencies ∧ prior.ambient = recovered.ambient ∧
        ReferenceStep.Equivalent relEnv language prior.body recovered.body := by
  have authority := normalBodyComparison_iff_source_data laws rows aligned relEnv
    priorGood recoveredGood identifier
  simp only [assignWith, stored]
  constructor
  · intro accepted
    split at accepted
    · rename_i checked
      obtain ⟨headers, compared⟩ := Bool.and_eq_true_iff.mp checked
      obtain ⟨dependenciesEqual, ambientEqual⟩ := Bool.and_eq_true_iff.mp headers
      exact ⟨beq_iff_eq.mp dependenciesEqual, beq_iff_eq.mp ambientEqual, authority.mp compared⟩
    · cases accepted
  · rintro ⟨dependenciesEqual, ambientEqual, equivalent⟩
    simp only [dependenciesEqual, ambientEqual, beq_self_eq_true, Bool.true_and, authority.mpr equivalent, ite_true]

/-- Actual rest/data recovery earns the same data role in the dependency
context; comparison never replaces it by an assumed scalar capture. -/
theorem captureWith_normal_typed_data_repeat_iff_source
    {language : LanguageDef} {bag : GrammarRule} {unit : String}
    (laws : BareBagTheory {language with equations := []} bag (some unit))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unit) (Match.applyBindings bindings row.left) =
          normalForm (some unit) (Match.applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {dependencies ambient locals : List TypeExpr}
    {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite} {path : List Nat}
    {initial : ScopedRuleMatching.Assignment} {identifier : String}
    {arguments : List Pattern} {indices : List Nat} {target : Pattern} {prior recovered : ContextualValue}
    (declared : dependencies? spec identifier = some dependencies)
    (atSite : arguments? rule spec identifier site path = some arguments)
    (spineCheck : variableSpine? locals.length arguments = some indices)
    (spine : Mettapedia.GSLT.LanguageDef.RestAwareTyping.PartialSortedSpine dependencies locals indices)
    (targetGood : Admissible language free (locals ++ ambient) (.collection .hashBag (.base bag.category)) target)
    (recovery : recoverValue? dependencies ambient.length locals.length arguments target = some recovered)
    (stored : lookup initial identifier = some prior)
    (priorGood : Admissible language free (dependencies ++ ambient)
      (.collection .hashBag (.base bag.category)) prior.body) :
    captureWith? (AlgebraFocus.RecursiveView.normalBodyComparison unit) rule spec ambient.length locals.length
        site path initial identifier target = some initial ↔
      prior.dependencies = dependencies ∧ prior.ambient = ambient.length ∧
        ReferenceStep.Equivalent relEnv language prior.body recovered.body := by
  have good := AlgebraFocus.RecursiveView.recoverValue?_admissible_from_success spineCheck spine targetGood recovery
  simp only [captureWith?, declared, atSite, Option.bind_eq_bind, Option.bind_some, recovery]
  simpa only [good.1, good.2.1] using
    assignWith_normal_data_repeat_iff_source laws rows aligned relEnv stored priorGood good.2.2

#print axioms assignWith_normal_data_repeat_iff_source
#print axioms captureWith_normal_typed_data_repeat_iff_source

#print axioms reference_equivalent_iff_normalForm_eq_data
#print axioms normalBodyComparison_iff_source_data

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.DataRestControls

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

private def proc : TypeExpr := .base "P"
private def dataType : TypeExpr := .collection .hashBag proc
private def bag (elements : List Pattern) : Pattern := .collection .hashBag elements none
private def schema : Pattern := .apply "Pair"
  [.collection .hashBag [] (some "R"), .collection .hashBag [] (some "R")]
private def specification : RuleBindingSpec where
  dependencies := [("R", [])]
  occurrences := [
    {name := "R", site := .left, path := [0, 0], arguments := []},
    {name := "R", site := .left, path := [1, 0], arguments := []}]
private def rule : RewriteRule where
  name := "UseRest"
  typeContext := [("R", dataType)]
  left := schema
  right := .apply "Z" []
  premises := []
  bindings := some specification
private def carrier : GrammarRule where
  label := "Par"
  category := "P"
  params := [.simple "items" dataType]
  syntaxPattern := []
  algebra? := some {flatten := true, unit := some "Z"}
private def language : LanguageDef where
  name := "DataRest"
  types := [TypeDecl.plain "P"]
  terms := [
    {label := "Z", category := "P", params := [], syntaxPattern := []},
    carrier,
    {label := "Pair", category := "P", params := [.simple "first" proc, .simple "second" proc], syntaxPattern := []}]
  equations := []
  rewrites := [rule]
private def subject : Pattern := .apply "Pair" [bag [], bag [.apply "Z" []]]
private def presentation : Pattern := .apply "Pair" [bag [], bag []]
private def emptyValue : ContextualValue := {dependencies := [], ambient := 0, body := bag []}
private def unitValue : ContextualValue := {dependencies := [], ambient := 0, body := bag [.apply "Z" []]}
private def captured : ScopedRuleMatching.Assignment := [("R", emptyValue)]
private def compare := AlgebraFocus.RecursiveView.normalBodyComparison "Z"
private def schemaFree : FreeTypeContext := fun identifier => if identifier == "R" then some dataType else none

private theorem laws : BareBagTheory {language with equations := []} carrier (some "Z") :=
  (bagTheory_of_check (by decide +kernel)).asBare rfl

private theorem emptyGood : Admissible language FreeTypeContext.empty [] dataType emptyValue.body :=
  ⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩
private theorem unitGood : Admissible language FreeTypeContext.empty [] dataType unitValue.body :=
  ⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩

private theorem unit_empty_normal : normalForm (some "Z") emptyValue.body = normalForm (some "Z") unitValue.body := by
  simp [emptyValue, unitValue, bag, normalForm, normalFormList, normalizeBag, bagContents, splice, collapse]

/-- The rule's repeated rest has its actual collection-data type, checked
by the rest-aware source judgment and the real binding declaration. -/
theorem rest_has_data_role :
    rule.typeContext = [("R", dataType)] ∧ admittedFor rule specification = true ∧
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.HasType language schemaFree [] schema proc := by
  exact ⟨rfl, by decide +kernel,
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType_sound (by decide +kernel)⟩

private theorem firstCapture :
    captureRestWith? compare rule specification 0 0 .left [0, 0] [] "R" .hashBag [] = some captured := by
  decide +kernel

private theorem secondCapture (relEnv : Engine.RelationEnv) :
    captureRestWith? compare rule specification 0 0 .left [1, 0] captured "R" .hashBag [.apply "Z" []] = some captured := by
  have equivalent := (reference_equivalent_iff_normalForm_eq_data laws
    (by intro row member; cases member) (by intro row member; cases member) relEnv emptyGood unitGood).mpr unit_empty_normal
  have assigned := (assignWith_normal_data_repeat_iff_source laws
    (by intro row member; cases member) (by intro row member; cases member) relEnv
    (by decide +kernel : lookup captured "R" = some emptyValue) emptyGood unitGood).mpr
      ⟨rfl, rfl, equivalent⟩
  have dependenciesRead : dependencies? specification "R" = some [] := by decide +kernel
  have argumentsRead : arguments? rule specification "R" .left [1, 0] = some [] := by decide +kernel
  have recovered : recoverValue? [] 0 0 [] (bag [.apply "Z" []]) = some unitValue := by decide +kernel
  dsimp only [bag] at recovered
  simpa only [compare, captureRestWith?, captureWith?, dependenciesRead, argumentsRead,
    Option.bind_eq_bind, Option.bind_some, recovered] using assigned

/-- Declared-equation comparison succeeds on two literal rest spellings,
retains the original empty data container, and has an independent ordinary
source match at an actual source-equivalent presentation. -/
theorem repeated_rest_source_control (relEnv : Engine.RelationEnv) :
    matchAtWith compare rule specification 0 .left [] 0 [] schema subject = [captured] ∧
      matchAt rule specification 0 .left [] 0 [] schema subject = [] ∧
      GeneralScopedMatch.Matches rule specification 0 .left [] 0 [] schema presentation captured ∧
      ReferenceStep.Equivalent relEnv language subject presentation ∧
      Admissible language FreeTypeContext.empty [] dataType emptyValue.body := by
  have comparatorMatch : matchAtWith compare rule specification 0 .left [] 0 [] schema subject = [captured] := by
    simp [schema, subject, bag, matchAtWith, matchArgsAtWith, matchBagAtWith, firstCapture, secondCapture relEnv]
  have ordinaryMatch : GeneralScopedMatch.Matches rule specification 0 .left [] 0 [] schema presentation captured :=
    GeneralScopedMatch.matchAt_iff.mp (by decide +kernel)
  have subjectGood : Admissible language FreeTypeContext.empty [] proc subject :=
    ⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩
  have presentationGood : Admissible language FreeTypeContext.empty [] proc presentation :=
    ⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩
  have normalEqual : normalForm (some "Z") subject = normalForm (some "Z") presentation := by
    simp [subject, presentation, bag, normalForm, normalFormList, normalizeBag, bagContents, splice, collapse]
  exact ⟨comparatorMatch, by decide +kernel, ordinaryMatch,
    (reference_equivalent_iff_normalForm_eq laws (by intro row member; cases member)
      (by intro row member; cases member) relEnv subjectGood presentationGood rfl).mpr normalEqual, emptyGood⟩

/-- Comparison authority does not imply that its numeric representative
is itself a typed data value. The original container must remain stored. -/
theorem normal_form_is_not_data_readback :
    Admissible language FreeTypeContext.empty [] dataType unitValue.body ∧
      normalForm (some "Z") unitValue.body = .apply "Z" [] ∧
      ¬ HasType language FreeTypeContext.empty [] (normalForm (some "Z") unitValue.body) dataType := by
  have image : normalForm (some "Z") unitValue.body = .apply "Z" [] := by
    simp [unitValue, bag, normalForm, normalFormList, normalizeBag, bagContents, splice, collapse]
  refine ⟨unitGood, image, ?_⟩
  rw [image]
  intro typed
  change HasType language FreeTypeContext.empty [] (.apply "Z" []) (.collection .hashBag proc) at typed
  obtain ⟨declaration, _, _, impossible⟩ := declared_constructor_of_hasType_apply typed
  cases impossible

private def dataFree : FreeTypeContext := fun identifier => if identifier == "D" then some dataType else none

/-- An opaque data variable keeps its declared collection type. The source
decision proof handles it by lookup inversion, not a scalar retyping. -/
theorem data_variable_keeps_its_role :
    Admissible language dataFree [] dataType (.fvar "D") ∧
      ¬ HasType language dataFree [] (.fvar "D") proc := by
  refine ⟨⟨HasType.fvar (by simp [dataFree]), rfl, rfl⟩, ?_⟩
  intro typed
  cases typed with
  | fvar lookup => simp [dataFree, dataType, proc] at lookup

#print axioms rest_has_data_role
#print axioms repeated_rest_source_control
#print axioms normal_form_is_not_data_readback
#print axioms data_variable_keeps_its_role

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.DataRestControls

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- The data-fibre source certificate transports through the very same
actual typed occurrence action as the collection-free case. Both original
values and both returned data containers retain their declared roles. -/
theorem source_equivalent_instantiated_data_values
    {language : LanguageDef} {bag : GrammarRule} {unit : String}
    (laws : BareBagTheory {language with equations := []} bag (some unit))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unit) (Match.applyBindings bindings row.left) =
          normalForm (some unit) (Match.applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {dependencies ambient locals : List TypeExpr}
    {first second : ContextualValue} {arguments : List Pattern}
    (firstHeaders : first.dependencies = dependencies ∧ first.ambient = ambient.length)
    (secondHeaders : second.dependencies = dependencies ∧ second.ambient = ambient.length)
    (firstGood : Admissible language free (dependencies ++ ambient)
      (.collection .hashBag (.base bag.category)) first.body)
    (secondGood : Admissible language free (dependencies ++ ambient)
      (.collection .hashBag (.base bag.category)) second.body)
    (argumentsGood : List.Forall₂
      (fun argument dependency => Admissible language free (locals ++ ambient) dependency argument)
      arguments dependencies)
    (equivalent : ReferenceStep.Equivalent relEnv language first.body second.body) :
    ∃ firstTarget secondTarget,
      instantiateValue? first ambient.length locals.length arguments = some firstTarget ∧
      instantiateValue? second ambient.length locals.length arguments = some secondTarget ∧
      Admissible language free (locals ++ ambient) (.collection .hashBag (.base bag.category)) firstTarget ∧
      Admissible language free (locals ++ ambient) (.collection .hashBag (.base bag.category)) secondTarget ∧
      ReferenceStep.Equivalent relEnv language firstTarget secondTarget := by
  have argumentsTyped := List.Forall₂.imp (fun _ _ good => good.typed) argumentsGood
  let assignment := occurrenceAssignment dependencies.length locals.length arguments
  let firstTarget := Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment first.body
  let secondTarget := Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment second.body
  have firstTargetGood := occurrence_substitution_admissible firstGood argumentsGood
  have secondTargetGood := occurrence_substitution_admissible secondGood argumentsGood
  have bodiesEqual := (reference_equivalent_iff_normalForm_eq_data laws rows aligned relEnv
    firstGood secondGood).mp equivalent
  have targetsEqual := normalForm_substitute_congr unit assignment bodiesEqual
  refine ⟨firstTarget, secondTarget,
    instantiateValue?_recorded_typed firstHeaders firstGood.typed argumentsTyped,
    instantiateValue?_recorded_typed secondHeaders secondGood.typed argumentsTyped,
    firstTargetGood, secondTargetGood, ?_⟩
  exact (reference_equivalent_iff_normalForm_eq_data laws rows aligned relEnv
    firstTargetGood secondTargetGood).mpr targetsEqual

#print axioms source_equivalent_instantiated_data_values

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- A successful declared-equation repeat has an actual typed source-equivalent
presentation with the ordinary independent capture witness. The first raw
contextual value and its exact headers are retained. -/
theorem captureWith_normal_repeat_source_presentation
    {language : LanguageDef} {bag : GrammarRule} {unit : String}
    (laws : BareBagTheory {language with equations := []} bag (some unit))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unit) (Match.applyBindings bindings row.left) =
          normalForm (some unit) (Match.applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {dependencies ambient locals : List TypeExpr} {expected : TypeExpr}
    {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite} {path : List Nat}
    {initial : ScopedRuleMatching.Assignment} {identifier : String}
    {arguments : List Pattern} {indices : List Nat} {target : Pattern} {prior : ContextualValue}
    (declared : dependencies? spec identifier = some dependencies)
    (atSite : arguments? rule spec identifier site path = some arguments)
    (spineCheck : variableSpine? locals.length arguments = some indices)
    (spine : Mettapedia.GSLT.LanguageDef.RestAwareTyping.PartialSortedSpine dependencies locals indices)
    (targetGood : Admissible language free (locals ++ ambient) expected target)
    (stored : lookup initial identifier = some prior)
    (priorGood : Admissible language free (dependencies ++ ambient) expected prior.body)
    (argumentsGood : List.Forall₂
      (fun argument dependency => Admissible language free (locals ++ ambient) dependency argument)
      arguments dependencies)
    (role : collectionFree expected = true ∨ expected = .collection .hashBag (.base bag.category))
    (accepted : captureWith? (normalBodyComparison unit) rule spec ambient.length locals.length
      site path initial identifier target = some initial) :
    ∃ presentation,
      Admissible language free (locals ++ ambient) expected presentation ∧
      ReferenceStep.Equivalent relEnv language target presentation ∧
      recoverValue? dependencies ambient.length locals.length arguments presentation = some prior ∧
      capture? rule spec ambient.length locals.length site path initial identifier presentation = some initial ∧
      GeneralScopedMatch.Matches rule spec ambient.length site path locals.length initial
        (.fvar identifier) presentation initial := by
  simp only [captureWith?, declared, atSite, Option.bind_eq_bind,
    Option.bind_some, Option.bind_eq_some_iff] at accepted
  obtain ⟨recovered, recoveredAtTarget, assigned⟩ := accepted
  have recoveredGood := recoverValue?_admissible_from_success spineCheck spine targetGood recoveredAtTarget
  have compared : prior.dependencies = recovered.dependencies ∧ prior.ambient = recovered.ambient ∧
      ReferenceStep.Equivalent relEnv language prior.body recovered.body := by
    rcases role with collectionless | rfl
    · exact (assignWith_normal_repeat_iff_source laws rows aligned relEnv stored
        priorGood recoveredGood.2.2 collectionless).mp assigned
    · exact (assignWith_normal_data_repeat_iff_source laws rows aligned relEnv stored
        priorGood recoveredGood.2.2).mp assigned
  have priorHeaders : prior.dependencies = dependencies ∧ prior.ambient = ambient.length :=
    ⟨compared.1.trans recoveredGood.1, compared.2.1.trans recoveredGood.2.1⟩
  have transported : ∃ firstTarget secondTarget,
      instantiateValue? prior ambient.length locals.length arguments = some firstTarget ∧
      instantiateValue? recovered ambient.length locals.length arguments = some secondTarget ∧
      Admissible language free (locals ++ ambient) expected firstTarget ∧
      Admissible language free (locals ++ ambient) expected secondTarget ∧
      ReferenceStep.Equivalent relEnv language firstTarget secondTarget := by
    rcases role with collectionless | rfl
    · exact source_equivalent_instantiated_values laws rows aligned relEnv priorHeaders
        ⟨recoveredGood.1, recoveredGood.2.1⟩ priorGood recoveredGood.2.2 argumentsGood
        collectionless compared.2.2
    · exact source_equivalent_instantiated_data_values laws rows aligned relEnv priorHeaders
        ⟨recoveredGood.1, recoveredGood.2.1⟩ priorGood recoveredGood.2.2 argumentsGood compared.2.2
  obtain ⟨presentation, secondTarget, firstRead, secondRead, presentationGood, _, equivalent⟩ := transported
  have secondSame : secondTarget = target := Option.some.inj
    (secondRead.symm.trans (recoverValue?_forward _ _ _ _ _ _ recoveredAtTarget))
  subst secondTarget
  have recoveredPrior :
      recoverValue? dependencies ambient.length locals.length arguments presentation = some prior := by
    simpa only [priorHeaders.1] using CanonicalBags.recoverValue?_instantiateValue? spineCheck firstRead
  have literalCapture : capture? rule spec ambient.length locals.length site path
      initial identifier presentation = some initial := by
    simp only [capture?, declared, atSite, Option.bind_eq_bind, Option.bind_some, recoveredPrior,
      assign, stored, beq_self_eq_true, ite_true]
  exact ⟨presentation, presentationGood, .symm _ _ equivalent, recoveredPrior, literalCapture,
    .capture literalCapture⟩

#print axioms captureWith_normal_repeat_source_presentation

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.OpaqueDataBoundary

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

private def proc : TypeExpr := .base "P"
private def dataType : TypeExpr := .collection .hashBag proc
private def bag (elements : List Pattern) : Pattern := .collection .hashBag elements none
private def zero : GrammarRule where
  label := "Zero"
  category := "P"
  params := []
  syntaxPattern := []
private def carrier : GrammarRule where
  label := "Par"
  category := "P"
  params := [.simple "items" dataType]
  syntaxPattern := []
  algebra? := some {flatten := true, unit := some "Zero"}
private def wrapper : GrammarRule where
  label := "F"
  category := "P"
  params := [.simple "data" dataType]
  syntaxPattern := []
  collectionRepresentation := .wrapped
private def specification : RuleBindingSpec where
  dependencies := [("R", [])]
  occurrences := []
private def rule : RewriteRule where
  name := "ConsumeData"
  typeContext := [("R", dataType)]
  premises := []
  left := .apply "F" [.collection .hashBag [] (some "R")]
  right := .apply "Zero" []
  bindings := some specification
private def baseLanguage : LanguageDef where
  name := "OpaqueDataBase"
  types := [TypeDecl.plain "P"]
  terms := [zero, carrier]
  equations := []
  rewrites := []
private def language : LanguageDef :=
  {baseLanguage with terms := [zero, carrier, wrapper], rewrites := [rule]}
private def source : Pattern := .apply "F" [.bvar 0]
private def redex : Pattern := .apply "F" [bag [.bvar 0]]
private def result : Pattern := .apply "Zero" []

/-- The larger language and its rest schema pass the actual static checks.
The caller's collection-valued binder is a typed object, not a malformed term. -/
theorem checked_rule_and_endpoints :
    language.validate = [] ∧
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkRewriteHasType language rule = true ∧
      admittedFor rule specification = true ∧
      Admissible language FreeTypeContext.empty [dataType] proc source ∧
      Admissible language FreeTypeContext.empty [dataType] proc result := by
  refine ⟨by cbv, by decide +kernel, by decide +kernel, ?_, ?_⟩
  all_goals exact ⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩

/-- The existing one-bag profile already excludes a second collection-bearing
constructor. The extension must not be reported as a BareBagTheory instance. -/
theorem bare_profile_excludes_extension :
    BareBagTheory baseLanguage carrier (some "Zero") ∧
      bagTheoryCheck language carrier (some "Zero") = false ∧
      ¬ BareBagTheory language carrier (some "Zero") := by
  refine ⟨(bagTheory_of_check (by decide +kernel)).asBare rfl, by decide +kernel, ?_⟩
  intro laws
  have impossible := laws.otherParameters wrapper (by decide +kernel) (by decide +kernel)
    (.simple "data" dataType) (by decide +kernel)
  change false = true at impossible
  cases impossible

private theorem algebra : Mettapedia.GSLT.LanguageDef.EquationSemantics.AlgebraRule
    language carrier .hashBag {flatten := true, unit := some "Zero"} := by
  refine ⟨by decide +kernel, rfl, ⟨"items", rfl⟩, ?_⟩
  intro identifier declared
  cases Option.some.inj declared
  exact ⟨zero, by decide +kernel, rfl, rfl, rfl⟩

private theorem generator : Mettapedia.GSLT.LanguageDef.EquationSemantics.DerivedInstance
    language (bag [.bvar 0]) (.bvar 0) := by
  exact .singleton algebra rfl ⟨FreeTypeContext.empty, [proc], checkHasType_sound (by decide +kernel)⟩

/-- The existential sorting witness for the declared singleton law uses P;
it is not the caller's actual HashBag(P) binder context. -/
theorem different_sorting_context :
    checkHasType language FreeTypeContext.empty [proc] (bag [.bvar 0]) proc = true ∧
      checkHasType language FreeTypeContext.empty [dataType] (bag [.bvar 0]) proc = false ∧
      ¬ HasType language FreeTypeContext.empty [dataType] redex proc := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro typed
  have checked := checkHasType_complete_of_object typed (by decide +kernel)
  have rejected : checkHasType language FreeTypeContext.empty [dataType] redex proc = false := by
    decide +kernel
  rw [rejected] at checked
  cases checked

private theorem source_equivalent_redex (relEnv : Engine.RelationEnv) :
    ReferenceStep.Equivalent relEnv language source redex := by
  have step : ReferenceStep.EquationStep relEnv language redex source :=
    .inContext (.apply "F" [] .hole []) (.inr generator)
  exact .symm _ _ (.rel _ _ step)

private theorem reference_redex (relEnv : Engine.RelationEnv) :
    ReferenceStep.Step relEnv language redex result := by
  have matched : [("R", bag [.bvar 0])] ∈
      ReflectiveCanonical.matchPatternForRule language rule redex := by decide +kernel
  exact ⟨_, ReferenceStep.StepValid.rule (index := 0) (rule := rule) rfl matched (.nil _)⟩

/-- Actual raw StepModulo fires through an ill-typed representative even
though both endpoints and the authored rest rule are typed. The literal
finite matcher cannot decompose the opaque collection-valued input. -/
theorem opaque_data_step_modulo (relEnv : Engine.RelationEnv) :
    ReferenceStep.StepModulo relEnv language source result ∧
      matchAt rule specification 1 .left [] 0 [] rule.left source = [] ∧
      ¬ HasType language FreeTypeContext.empty [dataType] redex proc := by
  exact ⟨⟨redex, result, source_equivalent_redex relEnv, reference_redex relEnv, .refl _⟩,
    by decide +kernel, different_sorting_context.2.2⟩

/-- A concrete collection at the same data port remains directly matchable
with its original typed empty rest. -/
theorem concrete_data_positive :
    Admissible language FreeTypeContext.empty [dataType] proc (.apply "F" [bag []]) ∧
      matchAt rule specification 1 .left [] 0 [] rule.left (.apply "F" [bag []]) =
        [[("R", ⟨[], 1, bag []⟩)]] := by
  exact ⟨⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩,
    by decide +kernel⟩

#print axioms checked_rule_and_endpoints
#print axioms bare_profile_excludes_extension
#print axioms different_sorting_context
#print axioms opaque_data_step_modulo
#print axioms concrete_data_positive

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.OpaqueDataBoundary


namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.ScopeBoundary

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- The original increasing-spine discriminator now has an ordinary typed
source witness at the repeated capture point. Literal comparison of the
numeric target still fails, while the first raw contextual body is retained. -/
theorem normalized_capture_recovers_source_presentation (relEnv : Engine.RelationEnv) :
    CanonicalBags.IncreasingSpines rule specification ∧
      capture? rule specification 0 3 .left [1, 0, 0, 0] [("F", value)] "F"
        (normalForm (some "PZero") deep) = none ∧
      captureWith? (normalBodyComparison "PZero") rule specification 0 3 .left [1, 0, 0, 0]
        [("F", value)] "F" (normalForm (some "PZero") deep) = some [("F", value)] ∧
      ∃ presentation,
        Admissible sourceLanguage free [proc, proc, proc] proc presentation ∧
        ReferenceStep.Equivalent relEnv sourceLanguage (normalForm (some "PZero") deep) presentation ∧
        recoverValue? [proc] 0 3 [.bvar 2] presentation = some value ∧
        GeneralScopedMatch.Matches rule specification 0 .left [1, 0, 0, 0] 3 [("F", value)]
          (.fvar "F") presentation [("F", value)] := by
  have targetGood : Admissible sourceLanguage free ([proc, proc, proc] ++ []) proc
      (normalForm (some "PZero") deep) := by
    rw [explicit_normal_forms.2.1]
    exact ⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩
  have spineCheck : variableSpine? ([proc, proc, proc] : List TypeExpr).length
      [.bvar 2] = some [2] := by decide +kernel
  have spine : Mettapedia.GSLT.LanguageDef.RestAwareTyping.PartialSortedSpine
      [proc] [proc, proc, proc] [2] := by
    refine ⟨rfl, ?_, ?_⟩
    all_goals
      intro index member
      obtain rfl := List.mem_singleton.mp member
      decide +kernel
  have argumentsGood : List.Forall₂
      (fun argument dependency => Admissible sourceLanguage free
        ([proc, proc, proc] ++ []) dependency argument) [.bvar 2] [proc] :=
    .cons ⟨HasType.bvar rfl, rfl, rfl⟩ .nil
  have accepted : captureWith? (normalBodyComparison "PZero") rule specification 0 3
      .left [1, 0, 0, 0] [("F", value)] "F" (normalForm (some "PZero") deep) =
      some [("F", value)] := by
    have recoveredGood : Admissible sourceLanguage free ([proc] ++ []) proc reversedValue.body :=
      ⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩
    have bodiesSame : normalForm (some "PZero") value.body =
        normalForm (some "PZero") reversedValue.body := by
      change normalForm (some "PZero") (.collection .hashBag [.bvar 0, .fvar ""] none) =
        normalForm (some "PZero") (.collection .hashBag [.fvar "", .bvar 0] none)
      rw [normalForm_bag, normalForm_bag]
      exact normalizeBag_perm _ ((by decide +kernel :
        ([.bvar 0, .fvar ""] : List Pattern).Perm [.fvar "", .bvar 0]).map _)
    have bodyEquivalent := (reference_equivalent_iff_normalForm_eq source_roles.1
      (by intro row member; cases member) (by intro row member; cases member) relEnv
      source_roles.2.1 recoveredGood rfl).mpr bodiesSame
    exact (captureWith_normal_repeat_iff_source source_roles.1
      (by intro row member; cases member) (by intro row member; cases member) relEnv
      (dependencies := [proc]) (ambient := []) (locals := [proc, proc, proc]) (expected := proc)
      (rule := rule) (spec := specification) (site := .left) (path := [1, 0, 0, 0])
      (initial := [("F", value)]) (identifier := "F") (arguments := [.bvar 2])
      (target := normalForm (some "PZero") deep) (prior := value) (recovered := reversedValue)
      (by decide +kernel) (by decide +kernel)
      recovering_after_normalization_disagrees.2.2.2.1 (by decide +kernel)
      source_roles.2.1 recoveredGood rfl).mpr ⟨rfl, rfl, bodyEquivalent⟩
  obtain ⟨presentation, good, equivalent, recovered, _, matched⟩ :=
    captureWith_normal_repeat_source_presentation source_roles.1
      (by intro row member; cases member) (by intro row member; cases member) relEnv
      (dependencies := [proc]) (ambient := []) (locals := [proc, proc, proc]) (expected := proc)
      (rule := rule) (spec := specification) (site := .left) (path := [1, 0, 0, 0])
      (initial := [("F", value)]) (identifier := "F") (arguments := [.bvar 2])
      (indices := [2]) (target := normalForm (some "PZero") deep) (prior := value)
      (by decide +kernel) (by decide +kernel) spineCheck spine targetGood
      (by decide +kernel) source_roles.2.1 argumentsGood (.inl rfl) accepted
  refine ⟨all_spines_increasing, ?_, accepted, presentation, good, equivalent, recovered, matched⟩
  rw [explicit_normal_forms.2.1]
  decide +kernel

#print axioms normalized_capture_recovers_source_presentation

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.ScopeBoundary

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- A checked sorted partial spine earns the actual argument types in the
whole caller context. Dependency arity and omitted locals are unrestricted. -/
theorem partial_spine_arguments_admissible
    {language : LanguageDef} {free : FreeTypeContext}
    {dependencies ambient locals : List TypeExpr} {arguments : List Pattern} {indices : List Nat}
    (checked : variableSpine? locals.length arguments = some indices)
    (spine : Mettapedia.GSLT.LanguageDef.RestAwareTyping.PartialSortedSpine dependencies locals indices) :
    List.Forall₂
      (fun argument dependency => Admissible language free (locals ++ ambient) dependency argument)
      arguments dependencies := by
  rw [CanonicalBags.variableSpine?_arguments checked]
  apply List.forall₂_of_length_eq_of_get
  · simpa only [List.length_map] using spine.length
  · intro position inArguments inDependencies
    have inIndices : position < indices.length := by simpa only [List.length_map] using inArguments
    have member : indices[position] ∈ indices := List.getElem_mem inIndices
    have bounded := spine.bounded _ member
    have sorted := spine.sorts _ member
    rw [(CanonicalBags.variableSpine?_nodup checked).idxOf_getElem position inIndices] at sorted
    have lookup : (locals ++ ambient)[indices[position]]? = some dependencies[position] := by
      rw [List.getElem?_append_left bounded]
      exact sorted.symm.trans (List.getElem?_eq_getElem inDependencies)
    simpa only [List.get_eq_getElem, List.getElem_map] using
      (show Admissible language free (locals ++ ambient) dependencies[position] (.bvar indices[position]) from
        ⟨HasType.bvar lookup, rfl, rfl⟩)

/-- Source equality to a concrete homogeneous data bag cannot turn a typed
data variable into a bag. This is an admissible-endpoint theorem, not a claim
that all raw source-equivalent intermediates keep the caller's type. -/
theorem reference_equivalent_data_bag_shape
    {language : LanguageDef} {bag : GrammarRule} {unit : Option String}
    (laws : BareBagTheory {language with equations := []} bag unit)
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm unit (Match.applyBindings bindings row.left) =
          normalForm unit (Match.applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {first : Pattern} {elements : List Pattern}
    (firstGood : Admissible language free bound (.collection .hashBag (.base bag.category)) first)
    (bagGood : Admissible language free bound (.collection .hashBag (.base bag.category))
      (.collection .hashBag elements none))
    (equivalent : ReferenceStep.Equivalent relEnv language first (.collection .hashBag elements none)) :
    ∃ firstElements, first = .collection .hashBag firstElements none := by
  have carrierGood : Admissible language free bound (.base bag.category)
      (.collection .hashBag elements none) := by
    rcases homogeneous_data_root laws bagGood with variableShape | carrierGood
    · rcases variableShape with ⟨_, impossible⟩ | ⟨_, impossible⟩ <;> cases impossible
    · exact carrierGood
  have same := (reference_equivalent_iff_normalForm_eq_data laws rows aligned relEnv firstGood bagGood).mp equivalent
  have normalized := normalized_admissible laws (ContextualStep.engineBasePremises relEnv) carrierGood rfl
  have typed := firstGood.typed
  have object := firstGood.object
  cases typed with
  | bvar lookup =>
      have baseTyped := normalized.typed
      rw [← same] at baseTyped
      exact (data_variable_not_carrier (.inl ⟨_, rfl⟩) firstGood.typed baseTyped).elim
  | fvar lookup =>
      have baseTyped := normalized.typed
      rw [← same] at baseTyped
      exact (data_variable_not_carrier (.inr ⟨_, rfl⟩) firstGood.typed baseTyped).elim
  | @collection _ _ firstElements tail _ elementsTyped =>
      have closed : tail = none := by
        exact Option.isNone_iff_eq_none.mp (Bool.and_eq_true_iff.mp object).1
      subst tail
      exact ⟨firstElements, rfl⟩
  | subst body replacement => simp only [isObjectPattern, Bool.false_eq_true] at object

#print axioms partial_spine_arguments_admissible
#print axioms reference_equivalent_data_bag_shape

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- A successful repeated rest has an ordinary rest match at a concrete typed
data presentation. Its collection boundary and exact original capture survive;
the spine itself earns the forward argument typing used in reconstruction. -/
theorem captureRestWith_normal_repeat_source_presentation
    {language : LanguageDef} {bag : GrammarRule} {unit : String}
    (laws : BareBagTheory {language with equations := []} bag (some unit))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unit) (Match.applyBindings bindings row.left) =
          normalForm (some unit) (Match.applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {dependencies ambient locals : List TypeExpr}
    {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite} {path : List Nat} {index : Nat}
    {initial : ScopedRuleMatching.Assignment} {identifier : String}
    {arguments : List Pattern} {indices : List Nat} {elements : List Pattern} {prior : ContextualValue}
    (declared : dependencies? spec identifier = some dependencies)
    (atSite : arguments? rule spec identifier site (path ++ [index]) = some arguments)
    (spineCheck : variableSpine? locals.length arguments = some indices)
    (spine : Mettapedia.GSLT.LanguageDef.RestAwareTyping.PartialSortedSpine dependencies locals indices)
    (targetGood : Admissible language free (locals ++ ambient) (.collection .hashBag (.base bag.category))
      (.collection .hashBag elements none))
    (stored : lookup initial identifier = some prior)
    (priorGood : Admissible language free (dependencies ++ ambient)
      (.collection .hashBag (.base bag.category)) prior.body)
    (accepted : captureRestWith? (normalBodyComparison unit) rule spec ambient.length locals.length
      site (path ++ [index]) initial identifier .hashBag elements = some initial) :
    ∃ presentedElements,
      Admissible language free (locals ++ ambient) (.collection .hashBag (.base bag.category))
        (.collection .hashBag presentedElements none) ∧
      ReferenceStep.Equivalent relEnv language (.collection .hashBag elements none)
        (.collection .hashBag presentedElements none) ∧
      recoverValue? dependencies ambient.length locals.length arguments
        (.collection .hashBag presentedElements none) = some prior ∧
      captureRest? rule spec ambient.length locals.length site (path ++ [index])
        initial identifier .hashBag presentedElements = some initial ∧
      GeneralScopedMatch.Bag rule spec ambient.length site path locals.length initial index
        [] (some identifier) .hashBag presentedElements initial := by
  have argumentsGood := partial_spine_arguments_admissible (language := language) (free := free)
    (ambient := ambient) spineCheck spine
  obtain ⟨presentation, good, equivalent, recovered, captured, _⟩ :=
    captureWith_normal_repeat_source_presentation laws rows aligned relEnv
      declared atSite spineCheck spine targetGood stored priorGood argumentsGood (.inr rfl) accepted
  obtain ⟨presentedElements, shape⟩ := reference_equivalent_data_bag_shape laws rows aligned relEnv
    good targetGood (.symm _ _ equivalent)
  subst presentation
  exact ⟨presentedElements, good, equivalent, recovered, captured, .rest captured⟩

#print axioms captureRestWith_normal_repeat_source_presentation

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.DataRestControls

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- The actual repeated empty/unit rest reconstructs a concrete typed
collection and an independent ordinary residual judgment at its real path. -/
theorem typed_rest_source_readback (relEnv : Engine.RelationEnv) :
    ∃ elements,
      Admissible language FreeTypeContext.empty [] dataType (bag elements) ∧
      ReferenceStep.Equivalent relEnv language (bag [.apply "Z" []]) (bag elements) ∧
      recoverValue? [] 0 0 [] (bag elements) = some emptyValue ∧
      captureRest? rule specification 0 0 .left [1, 0] captured "R" .hashBag elements = some captured ∧
      GeneralScopedMatch.Bag rule specification 0 .left [1] 0 captured 0 [] (some "R")
        .hashBag elements captured := by
  have spine : Mettapedia.GSLT.LanguageDef.RestAwareTyping.PartialSortedSpine [] [] [] := by
    refine ⟨rfl, ?_, ?_⟩
    all_goals intro index member; cases member
  exact AlgebraFocus.RecursiveView.captureRestWith_normal_repeat_source_presentation laws
    (by intro row member; cases member) (by intro row member; cases member) relEnv
    (dependencies := []) (ambient := []) (locals := []) (rule := rule) (spec := specification)
    (site := .left) (path := [1]) (index := 0) (initial := captured) (identifier := "R")
    (arguments := []) (indices := []) (elements := [.apply "Z" []]) (prior := emptyValue)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) spine unitGood
    (by decide +kernel) emptyGood (secondCapture relEnv)

#print axioms typed_rest_source_readback

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.DataRestControls

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations

open Mettapedia.OSLF.MeTTaIL Syntax

private theorem scoped_list_all (depth : Nat) (elements : List Pattern) :
    Pattern.isWellScopedListAt depth elements = elements.all (Pattern.isWellScopedAt depth) := by
  induction elements with
  | nil => rfl
  | cons first remaining recurse => simp only [Pattern.isWellScopedListAt, List.all_cons, recurse]

private theorem scoped_splice (depth : Nat) (pattern : Pattern) :
    (splice pattern).all (Pattern.isWellScopedAt depth) = pattern.isWellScopedAt depth := by
  cases pattern with
  | collection kind elements tail =>
      cases kind <;> cases tail <;>
        simp only [splice, List.all_cons, List.all_nil, Bool.and_true,
          Pattern.isWellScopedAt, scoped_list_all]
  | _ => simp only [splice, List.all_cons, List.all_nil, Bool.and_true]

private theorem scoped_filter_unit (unit : String) (depth : Nat) (elements : List Pattern) :
    (elements.filter fun pattern => decide (pattern ≠ .apply unit [])).all (Pattern.isWellScopedAt depth) =
      elements.all (Pattern.isWellScopedAt depth) := by
  induction elements with
  | nil => rfl
  | cons first remaining recurse =>
      by_cases isUnit : first = .apply unit []
      · subst first
        simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
          ite_false, List.all_cons, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
          Bool.true_and, recurse]
      · simp only [List.filter_cons, ne_eq, isUnit, not_false_eq_true, decide_true, ite_true,
          List.all_cons, recurse]

private theorem scoped_bagContents (unit : String) (depth : Nat) (elements : List Pattern) :
    (bagContents unit elements).all (Pattern.isWellScopedAt depth) =
      elements.all (Pattern.isWellScopedAt depth) := by
  rw [bagContents, scoped_filter_unit, List.all_flatMap]
  exact List.all_congr rfl (scoped_splice depth)

private theorem scoped_collapse (unit : String) (depth : Nat) (elements : List Pattern) :
    (collapse unit elements).isWellScopedAt depth = elements.all (Pattern.isWellScopedAt depth) := by
  cases elements with
  | nil => rfl
  | cons first remaining =>
      cases remaining with
      | nil => simp only [collapse, List.all_cons, List.all_nil, Bool.and_true]
      | cons second later =>
          exact scoped_list_all depth (first :: second :: later)

private theorem scoped_normalizeBag (unit : Option String) (depth : Nat) (elements : List Pattern) :
    (normalizeBag unit elements).isWellScopedAt depth = elements.all (Pattern.isWellScopedAt depth) := by
  cases unit with
  | none =>
      simp only [normalizeBag, Pattern.isWellScopedAt, scoped_list_all]
      exact (sortPatterns_perm elements).all_eq
  | some unit =>
      rw [normalizeBag, scoped_collapse, (sortPatterns_perm _).all_eq,
        scoped_bagContents]

private theorem scoped_normalized_list (unit : Option String) (depth : Nat) (elements : List Pattern)
    (each : ∀ element ∈ elements,
      (normalForm unit element).isWellScopedAt depth = element.isWellScopedAt depth) :
    Pattern.isWellScopedListAt depth (normalFormList unit elements) =
      Pattern.isWellScopedListAt depth elements := by
  simp only [normalFormList_eq_map, scoped_list_all, List.all_map]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, Function.comp_apply]
  constructor
  · intro normalized element member
    rw [← each element member]
    exact normalized element member
  · intro original element member
    rw [each element member]
    exact original element member

/-- Algebra normalization preserves the actual scope check on every raw
pattern. This includes binder lifts, explicit substitutions and open-tail
metadata; it does not assert objecthood or typed normalization at data roles. -/
theorem normalForm_isWellScopedAt (unit : Option String) (depth : Nat) (pattern : Pattern) :
    (normalForm unit pattern).isWellScopedAt depth = pattern.isWellScopedAt depth := by
  induction pattern using Pattern.inductionOn generalizing depth with
  | hbvar index => rfl
  | hfvar identifier => rfl
  | happly label arguments recurse =>
      exact scoped_normalized_list unit depth arguments (fun child member => recurse child member depth)
  | hlambda display body recurse =>
      exact recurse (depth + 1)
  | hmultiLambda arity displays body recurse =>
      exact recurse (depth + arity)
  | hsubst body replacement bodyRecurse replacementRecurse =>
      simp only [normalForm, Pattern.isWellScopedAt, bodyRecurse, replacementRecurse]
  | hcollection kind elements tail recurse =>
      by_cases closedBag : kind = .hashBag ∧ tail = none
      · obtain ⟨rfl, rfl⟩ := closedBag
        rw [normalForm_bag, scoped_normalizeBag, ← scoped_list_all,
          ← normalFormList_eq_map]
        exact scoped_normalized_list unit depth elements (fun child member => recurse child member depth)
      · simp only [normalForm, closedBag, if_false, Pattern.isWellScopedAt]
        exact scoped_normalized_list unit depth elements (fun child member => recurse child member depth)

#print axioms normalForm_isWellScopedAt

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Actual source equality at admissible capture roles transports recovery
success along the same checked partial spine. The recovered raw bodies may
differ; their source equality and exact contextual headers are retained. -/
theorem recoverValue?_source_transport
    {language : LanguageDef} {bag : GrammarRule} {unit : String}
    (laws : BareBagTheory {language with equations := []} bag (some unit))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unit) (Match.applyBindings bindings row.left) =
          normalForm (some unit) (Match.applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {dependencies ambient locals : List TypeExpr} {expected : TypeExpr}
    {arguments : List Pattern} {indices : List Nat} {first second : Pattern} {firstValue : ContextualValue}
    (spineCheck : variableSpine? locals.length arguments = some indices)
    (spine : Mettapedia.GSLT.LanguageDef.RestAwareTyping.PartialSortedSpine dependencies locals indices)
    (firstGood : Admissible language free (locals ++ ambient) expected first)
    (secondGood : Admissible language free (locals ++ ambient) expected second)
    (role : collectionFree expected = true ∨ expected = .collection .hashBag (.base bag.category))
    (equivalent : ReferenceStep.Equivalent relEnv language first second)
    (firstFound : recoverValue? dependencies ambient.length locals.length arguments first = some firstValue) :
    ∃ secondValue,
      recoverValue? dependencies ambient.length locals.length arguments second = some secondValue ∧
      firstValue.dependencies = secondValue.dependencies ∧ firstValue.ambient = secondValue.ambient ∧
      Admissible language free (dependencies ++ ambient) expected secondValue.body ∧
      ReferenceStep.Equivalent relEnv language firstValue.body secondValue.body ∧
      ∀ identifier, normalBodyComparison unit identifier firstValue.body secondValue.body = true := by
  have firstRecovered := recoverValue?_admissible_from_success spineCheck spine firstGood firstFound
  have sourceNormal : normalForm (some unit) first = normalForm (some unit) second := by
    rcases role with collectionless | rfl
    · exact (reference_equivalent_iff_normalForm_eq laws rows aligned relEnv
        firstGood secondGood collectionless).mp equivalent
    · exact (reference_equivalent_iff_normalForm_eq_data laws rows aligned relEnv
        firstGood secondGood).mp equivalent
  let inverse := recoveryAssignment locals.length dependencies.length ambient.length indices
  have bodyRead : firstValue.body =
      Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute inverse first :=
    Mettapedia.GSLT.LanguageDef.RestAwareTyping.recoverValue?_body_of_spine
      dependencies ambient.length locals.length arguments first indices firstValue spineCheck firstFound
  have bodyNormal := normalForm_substitute_congr unit inverse sourceNormal
  have firstScoped : Pattern.isWellScopedAt (dependencies.length + ambient.length)
      (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute inverse first) = true := by
    rw [← bodyRead]
    simpa only [List.length_append] using firstRecovered.2.2.typed.isWellScopedAt
  have secondScoped : Pattern.isWellScopedAt (dependencies.length + ambient.length)
      (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute inverse second) = true := by
    rw [← normalForm_isWellScopedAt (some unit) (dependencies.length + ambient.length)
      (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute inverse second), ← bodyNormal,
      normalForm_isWellScopedAt]
    exact firstScoped
  let secondValue : ContextualValue := ⟨dependencies, ambient.length,
    Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute inverse second⟩
  have secondFound : recoverValue? dependencies ambient.length locals.length arguments second = some secondValue :=
    CanonicalBags.recoverValue?_of_inverse_scoped spineCheck spine.length
      (by simpa only [List.length_append] using secondGood.typed.isWellScopedAt) secondScoped
  have secondRecovered := recoverValue?_admissible_from_success spineCheck spine secondGood secondFound
  have bodiesNormal : normalForm (some unit) firstValue.body = normalForm (some unit) secondValue.body := by
    rw [bodyRead]
    exact bodyNormal
  have bodiesEquivalent : ReferenceStep.Equivalent relEnv language firstValue.body secondValue.body := by
    rcases role with collectionless | rfl
    · exact (reference_equivalent_iff_normalForm_eq laws rows aligned relEnv
        firstRecovered.2.2 secondRecovered.2.2 collectionless).mpr bodiesNormal
    · exact (reference_equivalent_iff_normalForm_eq_data laws rows aligned relEnv
        firstRecovered.2.2 secondRecovered.2.2).mpr bodiesNormal
  exact ⟨secondValue, secondFound, firstRecovered.1.trans secondRecovered.1.symm,
    firstRecovered.2.1.trans secondRecovered.2.1.symm, secondRecovered.2.2, bodiesEquivalent,
    fun _ => beq_iff_eq.mpr bodiesNormal⟩

#print axioms recoverValue?_source_transport

/-- Every ordinary source capture is covered on a typed equivalent view by
the recovered-body comparison. Fresh captures may retain different raw
bodies; the complete ordered assignment account keeps names, headers and
actual source-equivalent values. Repeated captures retain the incoming list. -/
theorem capture?_source_transport
    {language : LanguageDef} {bag : GrammarRule} {unit : String}
    (laws : BareBagTheory {language with equations := []} bag (some unit))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unit) (Match.applyBindings bindings row.left) =
          normalForm (some unit) (Match.applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {dependencies ambient locals : List TypeExpr} {expected : TypeExpr}
    {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite} {path : List Nat}
    {identifier : String} {arguments : List Pattern} {indices : List Nat}
    {initial firstFinal : ScopedRuleMatching.Assignment} {first second : Pattern}
    (declared : dependencies? spec identifier = some dependencies)
    (atSite : arguments? rule spec identifier site path = some arguments)
    (spineCheck : variableSpine? locals.length arguments = some indices)
    (spine : Mettapedia.GSLT.LanguageDef.RestAwareTyping.PartialSortedSpine dependencies locals indices)
    (firstGood : Admissible language free (locals ++ ambient) expected first)
    (secondGood : Admissible language free (locals ++ ambient) expected second)
    (role : collectionFree expected = true ∨ expected = .collection .hashBag (.base bag.category))
    (equivalent : ReferenceStep.Equivalent relEnv language first second)
    (captured : capture? rule spec ambient.length locals.length site path initial identifier first = some firstFinal) :
    ∃ secondFinal,
      captureWith? (normalBodyComparison unit) rule spec ambient.length locals.length site path
        initial identifier second = some secondFinal ∧
      List.Forall₂ (fun (old current : String × ContextualValue) =>
        old.1 = current.1 ∧ old.2.dependencies = current.2.dependencies ∧
          old.2.ambient = current.2.ambient ∧
            ReferenceStep.Equivalent relEnv language old.2.body current.2.body)
        firstFinal secondFinal := by
  simp only [capture?, declared, atSite, Option.bind_eq_bind,
    Option.bind_some, Option.bind_eq_some_iff] at captured
  obtain ⟨firstValue, firstFound, firstAssigned⟩ := captured
  obtain ⟨secondValue, secondFound, dependenciesSame, ambientSame, _, bodiesEquivalent, compared⟩ :=
    recoverValue?_source_transport laws rows aligned relEnv spineCheck spine firstGood secondGood role equivalent firstFound
  have diagonal : ∀ values : ScopedRuleMatching.Assignment,
      List.Forall₂ (fun (old current : String × ContextualValue) =>
        old.1 = current.1 ∧ old.2.dependencies = current.2.dependencies ∧
          old.2.ambient = current.2.ambient ∧
            ReferenceStep.Equivalent relEnv language old.2.body current.2.body)
      values values := by
    intro values
    induction values with
    | nil => exact .nil
    | cons entry remaining recurse => exact .cons ⟨rfl, rfl, rfl, .refl _⟩ recurse
  cases stored : lookup initial identifier with
  | none =>
      simp only [assign, stored, Option.some.injEq] at firstAssigned
      subst firstFinal
      refine ⟨(identifier, secondValue) :: initial, ?_, .cons ⟨rfl, dependenciesSame, ambientSame, bodiesEquivalent⟩ (diagonal initial)⟩
      simp only [captureWith?, declared, atSite, Option.bind_eq_bind, Option.bind_some,
        secondFound, assignWith, stored]
  | some prior =>
      by_cases same : prior = firstValue
      · subst prior
        simp only [assign, stored, beq_self_eq_true, if_true, Option.some.injEq] at firstAssigned
        subst firstFinal
        refine ⟨initial, ?_, diagonal initial⟩
        simp only [captureWith?, declared, atSite, Option.bind_eq_bind, Option.bind_some,
          secondFound, assignWith, stored, ← dependenciesSame, ← ambientSame,
          beq_self_eq_true, Bool.true_and, compared identifier, if_true]
      · simp [assign, stored, same] at firstAssigned

#print axioms capture?_source_transport

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.ScopeBoundary

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Fresh capture on the normalized view really keeps a different raw body.
The coverage proof retains the complete ordered source-value account and the
actual named-free, increasing partial-spine instance. -/
theorem fresh_normal_view_capture_covered (relEnv : Engine.RelationEnv) :
    CanonicalBags.IncreasingSpines rule specification ∧
      capture? rule specification 0 3 .left [1, 0, 0, 0] [] "F" deep = some [("F", value)] ∧
      captureWith? (normalBodyComparison "PZero") rule specification 0 3 .left [1, 0, 0, 0]
        [] "F" (normalForm (some "PZero") deep) = some [("F", reversedValue)] ∧
      value ≠ reversedValue ∧
      List.Forall₂ (fun (old current : String × ContextualValue) =>
        old.1 = current.1 ∧ old.2.dependencies = current.2.dependencies ∧
          old.2.ambient = current.2.ambient ∧
            ReferenceStep.Equivalent relEnv sourceLanguage old.2.body current.2.body)
        [("F", value)] [("F", reversedValue)] := by
  have targetGood : Admissible sourceLanguage free ([proc, proc, proc] ++ []) proc
      (normalForm (some "PZero") deep) := by
    rw [explicit_normal_forms.2.1]
    exact ⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩
  have spineCheck : variableSpine? ([proc, proc, proc] : List TypeExpr).length
      [.bvar 2] = some [2] := by decide +kernel
  have spine : Mettapedia.GSLT.LanguageDef.RestAwareTyping.PartialSortedSpine
      [proc] [proc, proc, proc] [2] := by
    refine ⟨rfl, ?_, ?_⟩
    all_goals
      intro index member
      obtain rfl := List.mem_singleton.mp member
      decide +kernel
  have equivalent : ReferenceStep.Equivalent relEnv sourceLanguage deep
      (normalForm (some "PZero") deep) := by
    rw [explicit_normal_forms.2.1]
    exact .rel _ _ (.inContext .hole (.inr
      (Mettapedia.GSLT.LanguageDef.EquationSemantics.DerivedInstance.bagPerm_of_sorted
        ⟨free, [proc, proc, proc], source_roles.2.2.1.typed⟩ (by decide +kernel))))
  have ordinary : capture? rule specification 0 3 .left [1, 0, 0, 0] [] "F" deep =
      some [("F", value)] := by decide +kernel
  have viewed : captureWith? (normalBodyComparison "PZero") rule specification 0 3
      .left [1, 0, 0, 0] [] "F" (normalForm (some "PZero") deep) =
      some [("F", reversedValue)] := by
    rw [explicit_normal_forms.2.1]
    decide +kernel
  obtain ⟨final, captured, account⟩ := capture?_source_transport source_roles.1
    (by intro row member; cases member) (by intro row member; cases member) relEnv
    (dependencies := [proc]) (ambient := []) (locals := [proc, proc, proc]) (expected := proc)
    (rule := rule) (spec := specification) (site := .left) (path := [1, 0, 0, 0])
    (identifier := "F") (arguments := [.bvar 2]) (indices := [2])
    (initial := []) (firstFinal := [("F", value)])
    (first := deep) (second := normalForm (some "PZero") deep)
    (by decide +kernel) (by decide +kernel) spineCheck spine source_roles.2.2.1 targetGood
    (.inl rfl) equivalent ordinary
  have exactFinal : final = [("F", reversedValue)] := Option.some.inj (captured.symm.trans viewed)
  subst final
  exact ⟨all_spines_increasing, ordinary, viewed, by decide +kernel, account⟩

#print axioms fresh_normal_view_capture_covered

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.ScopeBoundary



set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

open Mettapedia.OSLF.MeTTaIL Syntax GeneralTypedSites

namespace GroupedCursor

/-- Group selection retains its unfinished bucket and next physical index.
Neither initialization nor expansion enumerates a permutation list. -/
inductive Work where
  | groups (slots : Nat) (closed : List (List SourceOccurrence))
      (selectedRev remaining : List SourceOccurrence)
  | selectGroup (slots : Nat) (closed : List (List SourceOccurrence))
      (selectedRev remaining : List SourceOccurrence) (cursor : Nat)
  | residual (closed : List (List SourceOccurrence))
      (selectedRev remaining : List SourceOccurrence)
  | selectResidual (closed : List (List SourceOccurrence))
      (selectedRev remaining : List SourceOccurrence) (cursor : Nat)
  deriving Repr,DecidableEq

def Work.account : Work → List SourceOccurrence
  | .groups _ closed selected remaining | .selectGroup _ closed selected remaining _
  | .residual closed selected remaining | .selectResidual closed selected remaining _ =>
      closed.flatten ++ selected.reverse ++ remaining

def Work.groupCount : Work → Nat
  | .groups slots closed _ _ | .selectGroup slots closed _ _ _ => closed.length + slots
  | .residual closed _ _ | .selectResidual closed _ _ _ => closed.length

def Work.finished? : Work → Option (List (List SourceOccurrence) × List SourceOccurrence)
  | .residual closed selected [] => some (closed,selected.reverse)
  | _ => none

/-- One group close or one indexed physical selection is exposed at a time.
The skip branch is a retained cursor, not an eager scan of alternatives. -/
def expand : Work → List Work
  | .groups 0 _ _ _ => []
  | .groups (slots + 1) closed selected remaining =>
      let next := if slots = 0 then Work.residual (closed ++ [selected.reverse]) [] remaining
        else Work.groups slots (closed ++ [selected.reverse]) [] remaining
      [next,.selectGroup (slots + 1) closed selected remaining 0]
  | .selectGroup slots closed selected remaining cursor =>
      match remaining[cursor]? with
      | none => []
      | some occurrence =>
          [.groups slots closed (occurrence :: selected) (remaining.eraseIdx cursor),
           .selectGroup slots closed selected remaining (cursor + 1)]
  | .residual _ _ [] => []
  | .residual closed selected remaining => [.selectResidual closed selected remaining 0]
  | .selectResidual closed selected remaining cursor =>
      match remaining[cursor]? with
      | none => []
      | some occurrence =>
          [.residual closed (occurrence :: selected) (remaining.eraseIdx cursor),
           .selectResidual closed selected remaining (cursor + 1)]

structure State where
  agenda : List Work
  answers : List (List (List SourceOccurrence) × List SourceOccurrence) := []
  deriving Repr,DecidableEq

/-- Initialization retains one unfinished task, including the zero-group
case. No complete allocation is materialized here. -/
def start (count : Nat) (occurrences : List SourceOccurrence) : State :=
  ⟨[if count = 0 then .residual [] [] occurrences else .groups count [] [] occurrences],[]⟩

def tick (state : State) : State :=
  match state.agenda with
  | [] => state
  | work :: pending =>
      match work.finished? with
      | some allocation => ⟨pending,state.answers ++ [allocation]⟩
      | none => ⟨expand work ++ pending,state.answers⟩

def run : Nat → State → State
  | 0,state => state
  | steps + 1,state => run steps (tick state)

def complete (state : State) : Bool := state.agenda.isEmpty

/-- Publication is append-only, and each tick publishes at most one
complete physical allocation. -/
theorem tick_answers_prefix (state : State) : state.answers <+: (tick state).answers := by
  cases state with
  | mk agenda answers =>
    cases agenda with
    | nil => exact List.prefix_refl _
    | cons work pending =>
      cases done : work.finished? <;> simp only [tick,done]
      · exact List.prefix_refl _
      · exact List.prefix_append _ _

theorem tick_publication_bound (state : State) :
    (tick state).answers.length ≤ state.answers.length + 1 := by
  cases state with
  | mk agenda answers =>
    cases agenda with
    | nil => simp [tick]
    | cons work pending =>
      cases done : work.finished? <;> simp [tick,done]

theorem start_pending (count : Nat) (occurrences : List SourceOccurrence) :
    (start count occurrences).agenda.length = 1 ∧ (start count occurrences).answers = [] := by
  simp [start]

private theorem selected_account {remaining : List SourceOccurrence} {cursor : Nat}
    {occurrence : SourceOccurrence} (selected : remaining[cursor]? = some occurrence)
    (closed selectedRev : List SourceOccurrence) :
    (closed ++ (occurrence :: selectedRev).reverse ++ remaining.eraseIdx cursor).Perm
      (closed ++ selectedRev.reverse ++ remaining) := by
  have within := (List.getElem?_eq_some_iff.mp selected).1
  have item := (List.getElem?_eq_some_iff.mp selected).2
  have permuted := List.getElem_cons_eraseIdx_perm within
  rw [item] at permuted
  simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using
    permuted.append_left (closed ++ selectedRev.reverse)

/-- Expansion moves original records between buckets without changing
multiplicity, and retains the exact number of requested group slots. -/
theorem expand_account {work branch : Work} (member : branch ∈ expand work) :
    branch.account.Perm work.account ∧ branch.groupCount = work.groupCount := by
  cases work with
  | groups slots closed selected remaining =>
    cases slots with
    | zero => simp [expand] at member
    | succ slots =>
      simp only [expand,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · split
        · rename_i zero
          simp only [Work.account,Work.groupCount,List.flatten_append,List.flatten_singleton,
            List.reverse_nil,List.append_nil,List.length_append,List.length_singleton,List.append_assoc]
          subst slots
          exact ⟨.refl _,by omega⟩
        · simp only [Work.account,Work.groupCount,List.flatten_append,List.flatten_singleton,
            List.reverse_nil,List.append_nil,List.length_append,List.length_singleton,List.append_assoc]
          exact ⟨.refl _,by omega⟩
      · exact ⟨.refl _,rfl⟩
  | selectGroup slots closed selected remaining cursor =>
    cases selectedEq : remaining[cursor]? with
    | none => simp [expand,selectedEq] at member
    | some occurrence =>
      simp only [expand,selectedEq,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact ⟨selected_account selectedEq closed.flatten selected,rfl⟩
      · exact ⟨.refl _,rfl⟩
  | residual closed selected remaining =>
    cases remaining with
    | nil => simp [expand] at member
    | cons first later =>
      simp only [expand,List.mem_singleton] at member
      subst branch
      exact ⟨.refl _,rfl⟩
  | selectResidual closed selected remaining cursor =>
    cases selectedEq : remaining[cursor]? with
    | none => simp [expand,selectedEq] at member
    | some occurrence =>
      simp only [expand,selectedEq,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · exact ⟨selected_account selectedEq closed.flatten selected,rfl⟩
      · exact ⟨.refl _,rfl⟩

theorem finished_account {work : Work} {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (finished : work.finished? = some (groups,residual)) :
    groups.flatten ++ residual = work.account ∧ groups.length = work.groupCount := by
  cases work <;> try cases finished
  case residual closed selected remaining =>
    cases remaining with
    | cons first later => cases finished
    | nil =>
      simp only [Work.finished?,Option.some.injEq,Prod.mk.injEq] at finished
      obtain ⟨rfl,rfl⟩ := finished
      exact ⟨by simp [Work.account],rfl⟩

/-- The invariant is the existing allocation account, stated for pending
work and publications alike. Original unit administration is external to
these live-component buckets. -/
def Valid (count : Nat) (occurrences : List SourceOccurrence) (state : State) : Prop :=
  (∀ work ∈ state.agenda,work.account.Perm occurrences ∧ work.groupCount = count) ∧
    ∀ allocation ∈ state.answers,allocation.1.length = count ∧
      (allocation.1.flatten ++ allocation.2).Perm occurrences

theorem start_valid (count : Nat) (occurrences : List SourceOccurrence) : Valid count occurrences (start count occurrences) := by
  constructor
  · intro work member
    simp only [start,List.mem_singleton] at member
    subst work
    by_cases zero : count = 0
    · simp [zero,Work.account,Work.groupCount]
    · simp [zero,Work.account,Work.groupCount]
  · simp [start]

theorem tick_valid {count : Nat} {occurrences : List SourceOccurrence} {state : State}
    (valid : Valid count occurrences state) : Valid count occurrences (tick state) := by
  cases state with
  | mk agenda answers =>
    cases agenda with
    | nil => exact valid
    | cons work pending =>
      have first := valid.1 work (by simp)
      cases done : work.finished? with
      | none =>
        simp only [tick,done,Valid]
        constructor
        · intro branch member
          rcases List.mem_append.mp member with expanded | retained
          · have conserved := expand_account expanded
            exact ⟨conserved.1.trans first.1,conserved.2.trans first.2⟩
          · exact valid.1 branch (by simp [retained])
        · exact valid.2
      | some allocation =>
        have finished := finished_account done
        simp only [tick,done,Valid]
        constructor
        · intro branch member
          exact valid.1 branch (by simp [member])
        · intro result member
          rcases List.mem_append.mp member with retained | published
          · exact valid.2 result retained
          · obtain rfl := List.mem_singleton.mp published
            refine ⟨finished.2.trans first.2,?_⟩
            rw [finished.1]
            exact first.1

theorem run_valid {count : Nat} {occurrences : List SourceOccurrence} {state : State}
    (valid : Valid count occurrences state) (steps : Nat) : Valid count occurrences (run steps state) := by
  induction steps generalizing state with
  | zero => exact valid
  | succ steps recurse => exact recurse (tick_valid valid)

/-- Every published cursor allocation belongs to the original finite group
specification. No separate collection equivalence is introduced. -/
theorem publication_sound (count steps : Nat) (occurrences : List SourceOccurrence)
    {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (member : (groups,residual) ∈ (run steps (start count occurrences)).answers) :
    (groups,residual) ∈ groupedOccurrences count occurrences :=
  (mem_groupedOccurrences count).mpr ((run_valid (start_valid count occurrences) steps).2 _ member)

#print axioms tick_answers_prefix
#print axioms tick_publication_bound
#print axioms start_pending
#print axioms expand_account
#print axioms finished_account
#print axioms start_valid
#print axioms tick_valid
#print axioms run_valid
#print axioms publication_sound


/-- The remaining source allocation problem after a prefix of one bucket
has already been selected. This is stated by prefixes and permutation,
independently of the transition function. -/
def groupPending (slots : Nat) (closed : List (List SourceOccurrence))
    (selectedRev remaining : List SourceOccurrence)
    (groups : List (List SourceOccurrence)) (residual : List SourceOccurrence) : Prop :=
  ∃ suffix later,groups = closed ++ (selectedRev.reverse ++ suffix) :: later ∧
    later.length + 1 = slots ∧ (suffix ++ later.flatten ++ residual).Perm remaining

def residualPending (closed : List (List SourceOccurrence))
    (selectedRev remaining : List SourceOccurrence)
    (groups : List (List SourceOccurrence)) (residual : List SourceOccurrence) : Prop :=
  groups = closed ∧ ∃ suffix,residual = selectedRev.reverse ++ suffix ∧ suffix.Perm remaining

/-- An unfinished cursor denotes only real source positions at or after
its cursor. No finite-list computation defines this pending-work meaning. -/
def Work.pending : Work → List (List SourceOccurrence) → List SourceOccurrence → Prop
  | .groups slots closed selected remaining,wantedGroups,wantedResidual =>
      groupPending slots closed selected remaining wantedGroups wantedResidual
  | .selectGroup slots closed selected remaining cursor,wantedGroups,wantedResidual =>
      ∃ index occurrence,cursor ≤ index ∧ remaining[index]? = some occurrence ∧
        groupPending slots closed (occurrence :: selected) (remaining.eraseIdx index) wantedGroups wantedResidual
  | .residual closed selected remaining,wantedGroups,wantedResidual =>
      residualPending closed selected remaining wantedGroups wantedResidual
  | .selectResidual closed selected remaining cursor,wantedGroups,wantedResidual =>
      ∃ index occurrence,cursor ≤ index ∧ remaining[index]? = some occurrence ∧
        residualPending closed (occurrence :: selected) (remaining.eraseIdx index) wantedGroups wantedResidual

/-- The one retained initialization task denotes exactly the established
finite source group relation, including empty groups and zero groups. -/
theorem start_pending_iff (count : Nat) (occurrences : List SourceOccurrence)
    {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence} :
    (if count = 0 then Work.residual [] [] occurrences else Work.groups count [] [] occurrences).pending groups residual ↔
      (groups,residual) ∈ groupedOccurrences count occurrences := by
  rw [mem_groupedOccurrences]
  cases count with
  | zero =>
    cases groups with
    | nil => simp [Work.pending,residualPending]
    | cons first later => simp [Work.pending,residualPending]
  | succ count =>
    simp only [Work.pending,groupPending]
    constructor
    · rintro ⟨first,later,rfl,lengths,account⟩
      exact ⟨by simpa using lengths,by
        simpa only [List.flatten_cons,List.append_assoc,List.reverse_nil,List.nil_append] using account⟩
    · rintro ⟨lengths,account⟩
      cases groups with
      | nil => simp at lengths
      | cons first later =>
        exact ⟨first,later,rfl,by simpa using lengths,
          by simpa only [List.flatten_cons,List.append_assoc] using account⟩

#print axioms start_pending_iff

abbrev Rank := Nat × Nat × Nat × Nat

def Work.rank : Work → Rank
  | .groups slots _ _ remaining => (remaining.length,slots,2,0)
  | .selectGroup slots _ _ remaining cursor => (remaining.length,slots,1,remaining.length - cursor)
  | .residual _ _ remaining => (remaining.length,0,2,0)
  | .selectResidual _ _ remaining cursor => (remaining.length,0,1,remaining.length - cursor)

abbrev RankSmaller : Rank → Rank → Prop :=
  Prod.Lex ((· < ·) : Nat → Nat → Prop)
    (Prod.Lex ((· < ·) : Nat → Nat → Prop)
      (Prod.Lex ((· < ·) : Nat → Nat → Prop) ((· < ·) : Nat → Nat → Prop)))

theorem expand_decreases {work branch : Work} (member : branch ∈ expand work) :
    RankSmaller branch.rank work.rank := by
  cases work with
  | groups slots closed selected remaining =>
    cases slots with
    | zero => simp [expand] at member
    | succ slots =>
      simp only [expand,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · split
        · subst slots
          exact Prod.Lex.right _ (Prod.Lex.left _ _ (by decide))
        · exact Prod.Lex.right _ (Prod.Lex.left _ _ (Nat.lt_succ_self _))
      · exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.left _ _ (by decide)))
  | selectGroup slots closed selected remaining cursor =>
    cases found : remaining[cursor]? with
    | none => simp [expand,found] at member
    | some occurrence =>
      have within := (List.getElem?_eq_some_iff.mp found).1
      simp only [expand,found,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · apply Prod.Lex.left
        simp only [List.length_eraseIdx,if_pos within]
        omega
      · apply Prod.Lex.right
        apply Prod.Lex.right
        apply Prod.Lex.right
        omega
  | residual closed selected remaining =>
    cases remaining with
    | nil => simp [expand] at member
    | cons first later =>
      simp only [expand,List.mem_singleton] at member
      subst branch
      exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.left _ _ (by decide)))
  | selectResidual closed selected remaining cursor =>
    cases found : remaining[cursor]? with
    | none => simp [expand,found] at member
    | some occurrence =>
      have within := (List.getElem?_eq_some_iff.mp found).1
      simp only [expand,found,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · apply Prod.Lex.left
        simp only [List.length_eraseIdx,if_pos within]
        omega
      · apply Prod.Lex.right
        apply Prod.Lex.right
        apply Prod.Lex.right
        omega

#print axioms expand_decreases

def workCost (work : Work) : Nat :=
  1 + ((expand work).attach.map fun child => workCost child.val).sum
termination_by work.rank
decreasing_by exact expand_decreases child.property

def agendaCost (agenda : List Work) : Nat := (agenda.map workCost).sum

theorem workCost_eq (work : Work) : workCost work = 1 + agendaCost (expand work) := by
  rw [workCost.eq_def]
  have same := congrArg (fun tasks : List Work => (tasks.map workCost).sum)
    (List.attach_map_subtype_val (expand work))
  apply congrArg (fun cost : Nat => 1 + cost)
  simpa only [agendaCost,List.map_map,Function.comp_def] using same

theorem workCost_positive (work : Work) : 0 < workCost work := by
  rw [workCost_eq]
  omega

theorem agendaCost_append (first second : List Work) :
    agendaCost (first ++ second) = agendaCost first + agendaCost second := by
  simp only [agendaCost,List.map_append,List.sum_append]

theorem finished_expand {work : Work} {answer : List (List SourceOccurrence) × List SourceOccurrence}
    (finished : work.finished? = some answer) : expand work = [] := by
  cases work <;> try cases finished
  case residual closed selected remaining =>
    cases remaining with
    | nil => rfl
    | cons first later => cases finished

theorem tick_cost (state : State) (pending : state.agenda ≠ []) :
    agendaCost (tick state).agenda + 1 = agendaCost state.agenda := by
  cases state with
  | mk agenda answers =>
    cases agenda with
    | nil => exact False.elim (pending rfl)
    | cons work tasks =>
      cases finished : work.finished? with
      | none =>
        simp only [tick,finished]
        change agendaCost (expand work ++ tasks) + 1 = workCost work + agendaCost tasks
        rw [agendaCost_append,workCost_eq]
        omega
      | some allocation =>
        simp only [tick,finished]
        change agendaCost tasks + 1 = workCost work + agendaCost tasks
        rw [workCost_eq,finished_expand finished]
        change agendaCost tasks + 1 = 1 + 0 + agendaCost tasks
        omega

theorem run_add (first second : Nat) (state : State) :
    run (first + second) state = run second (run first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add,run]
  | succ first ih => simpa only [Nat.succ_add,run] using ih (tick state)

theorem run_idle (steps : Nat) (state : State) (finished : state.agenda = []) :
    run steps state = state := by
  induction steps with
  | zero => rfl
  | succ steps ih => simpa only [run,tick,finished] using ih

/-- Every interrupted physical grouping agenda has finite remaining work.
The measure counts the actual expansion tree; it is not run during start. -/
theorem finiteDrain (state : State) : ∃ steps, (run steps state).agenda = [] := by
  by_cases finished : state.agenda = []
  · exact ⟨0,finished⟩
  · obtain ⟨steps,drained⟩ := finiteDrain (tick state)
    exact ⟨steps + 1,drained⟩
termination_by agendaCost state.agenda
decreasing_by have decreased := tick_cost state finished; omega

#print axioms workCost
#print axioms workCost_eq
#print axioms tick_cost
#print axioms run_add
#print axioms run_idle
#print axioms finiteDrain

private theorem select_head {head : SourceOccurrence} {tail remaining : List SourceOccurrence}
    (account : (head :: tail).Perm remaining) :
    ∃ index, remaining[index]? = some head ∧ tail.Perm (remaining.eraseIdx index) := by
  have present : head ∈ remaining := account.mem_iff.mp List.mem_cons_self
  obtain ⟨index,found⟩ := List.mem_iff_getElem?.mp present
  obtain ⟨within,same⟩ := List.getElem?_eq_some_iff.mp found
  have located := List.getElem_cons_eraseIdx_perm within
  rw [same] at located
  exact ⟨index,found,(account.trans located.symm).cons_inv⟩

/-- Pending denotation survives one real cursor transition, or becomes its
actual publication. No execution function is used to define denotation. -/
theorem expand_covers {work : Work} {groups : List (List SourceOccurrence)}
    {residual : List SourceOccurrence} (pending : work.pending groups residual) :
    work.finished? = some (groups,residual) ∨
      ∃ branch ∈ expand work, branch.pending groups residual := by
  cases work with
  | groups slots closed selected remaining =>
    obtain ⟨suffix,later,shape,lengths,account⟩ := pending
    cases slots with
    | zero => omega
    | succ slots =>
      right
      cases suffix with
      | nil =>
        by_cases last : slots = 0
        · have noLater : later = [] := List.length_eq_zero_iff.mp (by omega)
          subst later
          refine ⟨.residual (closed ++ [selected.reverse]) [] remaining,
            by simp [expand,last],?_,residual,by simp,?_⟩
          · simpa only [List.append_nil] using shape
          · simpa using account
        · cases later with
          | nil => simp at lengths; omega
          | cons next rest =>
            refine ⟨.groups slots (closed ++ [selected.reverse]) [] remaining,?_,next,rest,?_,?_,?_⟩
            · simp only [expand,last,if_false,List.mem_cons_self]
            · simpa only [List.append_nil,List.reverse_nil,List.nil_append,List.append_assoc,List.singleton_append] using shape
            · simp only [List.length_cons] at lengths
              omega
            · simpa only [List.flatten_cons,List.nil_append] using account
      | cons occurrence suffix =>
        obtain ⟨index,found,restAccount⟩ := select_head
          (by simpa only [List.cons_append] using account)
        refine ⟨.selectGroup (slots + 1) closed selected remaining 0,?_,index,occurrence,
          Nat.zero_le _,found,suffix,later,?_,lengths,restAccount⟩
        · simp [expand]
        · simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using shape
  | selectGroup slots closed selected remaining cursor =>
    obtain ⟨index,occurrence,after,found,meaning⟩ := pending
    have existsCurrent : cursor < remaining.length := by
      have selectedWithin := (List.getElem?_eq_some_iff.mp found).1
      omega
    have currentFound : remaining[cursor]? = some (remaining[cursor]'existsCurrent) :=
      List.getElem?_eq_some_iff.mpr ⟨existsCurrent,rfl⟩
    right
    by_cases now : cursor = index
    · subst index
      exact ⟨.groups slots closed (occurrence :: selected) (remaining.eraseIdx cursor),
        by simp [expand,found],meaning⟩
    · exact ⟨.selectGroup slots closed selected remaining (cursor + 1),
        by simp [expand,currentFound],
        index,occurrence,by omega,found,meaning⟩
  | residual closed selected remaining =>
    obtain ⟨same,suffix,shape,account⟩ := pending
    cases suffix with
    | nil =>
      have empty : remaining = [] := List.length_eq_zero_iff.mp (by
        have length := account.length_eq
        simp only [List.length_nil] at length
        omega)
      subst remaining
      left
      simp only [Work.finished?,Option.some.injEq,Prod.mk.injEq]
      exact ⟨same.symm,by simpa only [List.append_nil] using shape.symm⟩
    | cons occurrence suffix =>
      obtain ⟨index,found,restAccount⟩ := select_head account
      have nonempty : remaining ≠ [] := by intro empty; simp [empty] at found
      right
      refine ⟨.selectResidual closed selected remaining 0,?_,index,occurrence,
        Nat.zero_le _,found,same,suffix,?_,restAccount⟩
      · cases remaining with
        | nil => exact False.elim (nonempty rfl)
        | cons first rest => simp only [expand,List.mem_singleton]
      · simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using shape
  | selectResidual closed selected remaining cursor =>
    obtain ⟨index,occurrence,after,found,meaning⟩ := pending
    have existsCurrent : cursor < remaining.length := by
      have selectedWithin := (List.getElem?_eq_some_iff.mp found).1
      omega
    have currentFound : remaining[cursor]? = some (remaining[cursor]'existsCurrent) :=
      List.getElem?_eq_some_iff.mpr ⟨existsCurrent,rfl⟩
    right
    by_cases now : cursor = index
    · subst index
      exact ⟨.residual closed (occurrence :: selected) (remaining.eraseIdx cursor),
        by simp [expand,found],meaning⟩
    · exact ⟨.selectResidual closed selected remaining (cursor + 1),
        by simp [expand,currentFound],
        index,occurrence,by omega,found,meaning⟩

#print axioms expand_covers

def Accepts (state : State) (groups : List (List SourceOccurrence))
    (residual : List SourceOccurrence) : Prop :=
  (groups,residual) ∈ state.answers ∨ ∃ work ∈ state.agenda,work.pending groups residual

theorem tick_covers {state : State} {groups : List (List SourceOccurrence)}
    {residual : List SourceOccurrence} (accepted : Accepts state groups residual) :
    Accepts (tick state) groups residual := by
  rcases accepted with published | ⟨work,present,meaning⟩
  · left
    obtain ⟨suffix,same⟩ := tick_answers_prefix state
    rw [← same]
    exact List.mem_append_left _ published
  · cases state with
    | mk agenda answers =>
      cases agenda with
      | nil => cases present
      | cons first tasks =>
        rcases List.mem_cons.mp present with rfl | retained
        · rcases expand_covers meaning with finished | ⟨branch,member,childMeaning⟩
          · left
            simp only [tick,finished,List.mem_append,List.mem_singleton]
            exact Or.inr trivial
          · cases finished : work.finished? with
            | none =>
              right
              refine ⟨branch,?_,childMeaning⟩
              simp only [tick,finished]
              exact List.mem_append_left _ member
            | some allocation =>
              rw [finished_expand finished] at member
              cases member
        · right
          refine ⟨work,?_,meaning⟩
          cases finished : first.finished? with
          | none =>
              simp only [tick,finished]
              exact List.mem_append_right _ retained
          | some allocation => simpa only [tick,finished] using retained

theorem run_covers (steps : Nat) {state : State} {groups : List (List SourceOccurrence)}
    {residual : List SourceOccurrence} (accepted : Accepts state groups residual) :
    Accepts (run steps state) groups residual := by
  induction steps generalizing state with
  | zero => exact accepted
  | succ steps ih => exact ih (tick_covers accepted)

theorem publication_complete_of_drained (count steps : Nat) (occurrences : List SourceOccurrence)
    (drained : (run steps (start count occurrences)).agenda = [])
    {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (specified : (groups,residual) ∈ groupedOccurrences count occurrences) :
    (groups,residual) ∈ (run steps (start count occurrences)).answers := by
  have initial : Accepts (start count occurrences) groups residual := by
    right
    exact ⟨_,List.mem_singleton_self _,(start_pending_iff count occurrences).mpr specified⟩
  rcases run_covers steps initial with published | ⟨work,present,_⟩
  · exact published
  · rw [drained] at present
    cases present

/-- Completed execution has exactly the specified physical allocations.
This compares membership, not administrative permutation multiplicities. -/
theorem completed_membership_iff (count steps : Nat) (occurrences : List SourceOccurrence)
    (drained : (run steps (start count occurrences)).agenda = [])
    (groups : List (List SourceOccurrence)) (residual : List SourceOccurrence) :
    (groups,residual) ∈ (run steps (start count occurrences)).answers ↔
      (groups,residual) ∈ groupedOccurrences count occurrences :=
  ⟨publication_sound count steps occurrences,
    publication_complete_of_drained count steps occurrences drained⟩

theorem completes_with_exact_allocations (count : Nat) (occurrences : List SourceOccurrence) :
    ∃ steps,complete (run steps (start count occurrences)) = true ∧
      ∀ groups residual,(groups,residual) ∈ (run steps (start count occurrences)).answers ↔
        (groups,residual) ∈ groupedOccurrences count occurrences := by
  obtain ⟨steps,drained⟩ := finiteDrain (start count occurrences)
  refine ⟨steps,?_,fun groups residual => completed_membership_iff count steps occurrences drained groups residual⟩
  simp only [complete,drained,List.isEmpty_nil]

theorem every_allocation_published (count : Nat) (occurrences : List SourceOccurrence)
    {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (specified : (groups,residual) ∈ groupedOccurrences count occurrences) :
    ∃ steps,(groups,residual) ∈ (run steps (start count occurrences)).answers := by
  obtain ⟨steps,drained⟩ := finiteDrain (start count occurrences)
  exact ⟨steps,publication_complete_of_drained count steps occurrences drained specified⟩

theorem interrupted_publication_complete (state : State)
    (groups : List (List SourceOccurrence)) (residual : List SourceOccurrence)
    (accepted : Accepts state groups residual) :
    ∃ steps,(groups,residual) ∈ (run steps state).answers ∧ (run steps state).agenda = [] := by
  obtain ⟨steps,drained⟩ := finiteDrain state
  refine ⟨steps,?_,drained⟩
  rcases run_covers steps accepted with published | ⟨work,present,_⟩
  · exact published
  · rw [drained] at present
    cases present

theorem run_answers_prefix (steps : Nat) (state : State) :
    state.answers <+: (run steps state).answers := by
  induction steps generalizing state with
  | zero => exact List.prefix_refl _
  | succ steps ih => exact (tick_answers_prefix state).trans (ih (tick state))

#print axioms tick_covers
#print axioms run_covers
#print axioms publication_complete_of_drained
#print axioms completed_membership_iff
#print axioms completes_with_exact_allocations
#print axioms every_allocation_published
#print axioms interrupted_publication_complete
#print axioms run_answers_prefix

theorem publication_source_account (count steps : Nat) (unitLabel : String) (source : Pattern)
    {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (published : (groups,residual) ∈
      (run steps (start count (normalizedOccurrences unitLabel source))).answers) :
    ((groups.flatten ++ residual) ++ unitOccurrences unitLabel source).Perm
      (sourceOccurrences unitLabel source) :=
  grouped_occurrence_account (publication_sound count steps _ published)

theorem publication_origins {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext} {bound : List TypeExpr}
    {source : Pattern} (typed : Admissible language free bound (.base bag.category) source)
    {count steps : Nat} {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (published : (groups,residual) ∈
      (run steps (start count (normalizedOccurrences unitLabel source))).answers) :
    (groups.flatten ++ residual).Pairwise (fun first second => first.address ≠ second.address) ∧
      ∀ occurrence ∈ groups.flatten ++ residual,
        Admissible language free bound (.base bag.category) occurrence.original ∧
        Admissible language free bound (.base bag.category) occurrence.value ∧
        occurrence.context.fill occurrence.original = source ∧
        normalForm (some unitLabel) occurrence.original = occurrence.value ∧
        contextAddress occurrence.context = occurrence.address :=
  grouped_occurrence_origins laws typed (publication_sound count steps _ published)

namespace Controls

private def source : Pattern := .collection .hashBag
  [.collection .hashBag [.fvar "a",.fvar "a"] none,.apply "unit" []] none
private def occurrences := normalizedOccurrences "unit" source
private def initial := start 1 occurrences
private def finished := run 128 initial

theorem nested_equal_values_keep_physical_origins :
    occurrences.map SourceOccurrence.value = [.fvar "a",.fvar "a"] ∧
      occurrences.map SourceOccurrence.address = [[0,0],[0,1]] ∧
      (unitOccurrences "unit" source).map SourceOccurrence.address = [[1]] := by
  cbv

theorem initialization_does_not_publish :
    initial.agenda.length = 1 ∧ initial.answers = [] ∧ (run 1 initial).answers = [] := by
  decide +kernel

theorem all_six_physical_allocations :
    finished.agenda = [] ∧ finished.answers.length = 6 ∧
      ([],occurrences) ∉ finished.answers ∧
      ([[]],occurrences) ∈ finished.answers ∧
      ([occurrences],[]) ∈ finished.answers := by
  have drained : finished.agenda = [] := by cbv
  refine ⟨drained,by cbv,?_,?_,?_⟩
  · intro published
    have length := (mem_groupedOccurrences 1).mp (publication_sound 1 128 occurrences published) |>.1
    simp at length
  · apply publication_complete_of_drained 1 128 occurrences drained
    apply (mem_groupedOccurrences 1).mpr
    exact ⟨rfl,by simp⟩
  · apply publication_complete_of_drained 1 128 occurrences drained
    apply (mem_groupedOccurrences 1).mpr
    exact ⟨rfl,by simp⟩

theorem zero_groups_and_virtual_empty_group :
    (run 128 (start 0 occurrences)).answers.length = 2 ∧
      (run 4 (start 1 [])).answers = [([[]],[])] ∧
      (run 4 (start 1 [])).agenda = [] := by
  cbv

theorem exact_split_resume : run 121 (run 7 initial) = finished :=
  (run_add 7 121 initial).symm

theorem completed_resume_does_not_republish : run 31 finished = finished :=
  run_idle 31 finished all_six_physical_allocations.1

theorem fabricated_duplicate_origin_refused :
    let first := occurrences.getD 0 (SourceOccurrence.leaf "unit" (.fvar "a"))
    ([[first,first]],[]) ∉ finished.answers := by
  dsimp only
  intro published
  have account := (mem_groupedOccurrences 1).mp (publication_sound 1 128 occurrences published) |>.2
  have unique := (account.map SourceOccurrence.address).nodup_iff.mpr
    (normalizedOccurrences_distinct "unit" source)
  simp at unique

#print axioms nested_equal_values_keep_physical_origins
#print axioms initialization_does_not_publish
#print axioms all_six_physical_allocations
#print axioms zero_groups_and_virtual_empty_group
#print axioms exact_split_resume
#print axioms completed_resume_does_not_republish
#print axioms fabricated_duplicate_origin_refused

end Controls

#print axioms publication_source_account
#print axioms publication_origins

end GroupedCursor

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView


set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted
open CanonicalBags (mapValue mapAssignment lookup_mapAssignment)

/-- Ordered raw assignments can differ after fresh captures. Ordinary source
assignment transports through the actual normal-body comparison, retaining
the original headers and the complete source-value correspondence. -/
theorem assignWith_normal_source_transport
    {language : LanguageDef} (relEnv : Engine.RelationEnv) (unit : String)
    {firstInitial secondInitial firstFinal : ScopedRuleMatching.Assignment}
    {identifier : String} {firstValue secondValue : ContextualValue}
    (initialNormal : mapAssignment (normalForm (some unit)) firstInitial =
      mapAssignment (normalForm (some unit)) secondInitial)
    (initialSource : List.Forall₂ (fun (first second : String × ContextualValue) =>
      first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
        first.2.ambient = second.2.ambient ∧
          ReferenceStep.Equivalent relEnv language first.2.body second.2.body)
      firstInitial secondInitial)
    (valueHeaders : firstValue.dependencies = secondValue.dependencies ∧
      firstValue.ambient = secondValue.ambient)
    (valueNormal : normalForm (some unit) firstValue.body = normalForm (some unit) secondValue.body)
    (valueSource : ReferenceStep.Equivalent relEnv language firstValue.body secondValue.body)
    (assigned : assign firstInitial identifier firstValue = some firstFinal) :
    ∃ secondFinal,
      assignWith (normalBodyComparison unit) secondInitial identifier secondValue = some secondFinal ∧
      mapAssignment (normalForm (some unit)) firstFinal =
        mapAssignment (normalForm (some unit)) secondFinal ∧
      List.Forall₂ (fun (first second : String × ContextualValue) =>
        first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
          first.2.ambient = second.2.ambient ∧
            ReferenceStep.Equivalent relEnv language first.2.body second.2.body)
        firstFinal secondFinal := by
  have mappedValues : mapValue (normalForm (some unit)) firstValue =
      mapValue (normalForm (some unit)) secondValue := by
    cases firstValue with
    | mk firstDependencies firstAmbient firstBody =>
      cases secondValue with
      | mk secondDependencies secondAmbient secondBody =>
        change firstDependencies = secondDependencies ∧ firstAmbient = secondAmbient at valueHeaders
        change normalForm (some unit) firstBody = normalForm (some unit) secondBody at valueNormal
        change ContextualValue.mk firstDependencies firstAmbient (normalForm (some unit) firstBody) =
          ContextualValue.mk secondDependencies secondAmbient (normalForm (some unit) secondBody)
        rw [valueHeaders.1, valueHeaders.2, valueNormal]
  have sameLookup : (lookup firstInitial identifier).map (mapValue (normalForm (some unit))) =
      (lookup secondInitial identifier).map (mapValue (normalForm (some unit))) := by
    rw [← lookup_mapAssignment, ← lookup_mapAssignment, initialNormal]
  cases firstStored : lookup firstInitial identifier with
  | none =>
    simp only [assign, firstStored, Option.some.injEq] at assigned
    subst firstFinal
    cases secondStored : lookup secondInitial identifier with
    | none =>
      refine ⟨(identifier, secondValue) :: secondInitial, ?_, ?_, ?_⟩
      · simp only [assignWith, secondStored]
      · change (identifier, mapValue (normalForm (some unit)) firstValue) ::
          mapAssignment (normalForm (some unit)) firstInitial =
            (identifier, mapValue (normalForm (some unit)) secondValue) ::
              mapAssignment (normalForm (some unit)) secondInitial
        rw [mappedValues, initialNormal]
      · exact .cons ⟨rfl, valueHeaders.1, valueHeaders.2, valueSource⟩ initialSource
    | some prior =>
      simp only [firstStored, secondStored, Option.map_none, Option.map_some] at sameLookup
      cases sameLookup
  | some prior =>
    by_cases priorIsValue : prior = firstValue
    · subst prior
      simp only [assign, firstStored, beq_self_eq_true, if_true, Option.some.injEq] at assigned
      subst firstFinal
      cases secondStored : lookup secondInitial identifier with
      | none =>
        simp only [firstStored, secondStored, Option.map_none, Option.map_some] at sameLookup
        cases sameLookup
      | some secondPrior =>
        simp only [firstStored, secondStored, Option.map_some, Option.some.injEq] at sameLookup
        have priorMapped : mapValue (normalForm (some unit)) secondPrior =
            mapValue (normalForm (some unit)) secondValue := sameLookup.symm.trans mappedValues
        have dependenciesSame := congrArg ContextualValue.dependencies priorMapped
        have ambientSame := congrArg ContextualValue.ambient priorMapped
        have bodiesSame := congrArg ContextualValue.body priorMapped
        change secondPrior.dependencies = secondValue.dependencies at dependenciesSame
        change secondPrior.ambient = secondValue.ambient at ambientSame
        change normalForm (some unit) secondPrior.body = normalForm (some unit) secondValue.body at bodiesSame
        refine ⟨secondInitial, ?_, initialNormal, initialSource⟩
        simp only [assignWith, secondStored, normalBodyComparison, dependenciesSame,
          ambientSame, bodiesSame, beq_self_eq_true, Bool.true_and, if_true]
    · simp [assign, firstStored, priorIsValue] at assigned

#print axioms assignWith_normal_source_transport

/-- Source capture coverage threads two genuinely different incoming raw
assignments. Both the actual comparison readout and the independent source
body account survive, so later children need not share literal captures. -/
theorem capture?_source_transport_assignments
    {language : LanguageDef} {bag : GrammarRule} {unit : String}
    (laws : BareBagTheory {language with equations := []} bag (some unit))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unit) (Match.applyBindings bindings row.left) =
          normalForm (some unit) (Match.applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {dependencies ambient locals : List TypeExpr} {expected : TypeExpr}
    {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite} {path : List Nat}
    {identifier : String} {arguments : List Pattern} {indices : List Nat}
    {firstInitial secondInitial firstFinal : ScopedRuleMatching.Assignment} {first second : Pattern}
    (declared : dependencies? spec identifier = some dependencies)
    (atSite : arguments? rule spec identifier site path = some arguments)
    (spineCheck : variableSpine? locals.length arguments = some indices)
    (spine : Mettapedia.GSLT.LanguageDef.RestAwareTyping.PartialSortedSpine dependencies locals indices)
    (firstGood : Admissible language free (locals ++ ambient) expected first)
    (secondGood : Admissible language free (locals ++ ambient) expected second)
    (role : collectionFree expected = true ∨ expected = .collection .hashBag (.base bag.category))
    (equivalent : ReferenceStep.Equivalent relEnv language first second)
    (initialNormal : mapAssignment (normalForm (some unit)) firstInitial =
      mapAssignment (normalForm (some unit)) secondInitial)
    (initialSource : List.Forall₂ (fun (old current : String × ContextualValue) =>
      old.1 = current.1 ∧ old.2.dependencies = current.2.dependencies ∧
        old.2.ambient = current.2.ambient ∧
          ReferenceStep.Equivalent relEnv language old.2.body current.2.body)
      firstInitial secondInitial)
    (captured : capture? rule spec ambient.length locals.length site path
      firstInitial identifier first = some firstFinal) :
    ∃ secondFinal,
      captureWith? (normalBodyComparison unit) rule spec ambient.length locals.length site path
        secondInitial identifier second = some secondFinal ∧
      mapAssignment (normalForm (some unit)) firstFinal =
        mapAssignment (normalForm (some unit)) secondFinal ∧
      List.Forall₂ (fun (old current : String × ContextualValue) =>
        old.1 = current.1 ∧ old.2.dependencies = current.2.dependencies ∧
          old.2.ambient = current.2.ambient ∧
            ReferenceStep.Equivalent relEnv language old.2.body current.2.body)
        firstFinal secondFinal := by
  simp only [capture?, declared, atSite, Option.bind_eq_bind,
    Option.bind_some, Option.bind_eq_some_iff] at captured
  obtain ⟨firstValue, firstFound, firstAssigned⟩ := captured
  obtain ⟨secondValue, secondFound, dependenciesSame, ambientSame, _, bodySource, compared⟩ :=
    recoverValue?_source_transport laws rows aligned relEnv spineCheck spine firstGood secondGood role equivalent firstFound
  have bodyNormal : normalForm (some unit) firstValue.body = normalForm (some unit) secondValue.body :=
    beq_iff_eq.mp (compared identifier)
  obtain ⟨secondFinal, secondAssigned, finalNormal, finalSource⟩ :=
    assignWith_normal_source_transport relEnv unit initialNormal initialSource
      ⟨dependenciesSame, ambientSame⟩ bodyNormal bodySource firstAssigned
  refine ⟨secondFinal, ?_, finalNormal, finalSource⟩
  simp only [captureWith?, declared, atSite, Option.bind_eq_bind, Option.bind_some,
    secondFound, secondAssigned]

#print axioms capture?_source_transport_assignments

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching Match
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- An independent scoped bag derivation keeps its exact ordered capture
flow when the selected members are read as an argument spine. The final
residual judgment retains the real rest address and caller context. -/
theorem scoped_bag_selected_values
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth index : Nat}
    {site : RulePatternSite} {path : List Nat}
    {initial final : ScopedRuleMatching.Assignment} {schemas targets : List Pattern}
    {rest : Option String} {kind : CollType}
    (matched : GeneralScopedMatch.Bag rule spec ambient site path depth initial index
      schemas rest kind targets final) :
    ∃ selected residual middle,
      selected.length = schemas.length ∧
      (selected ++ residual).Perm targets ∧
      GeneralScopedMatch.Arguments rule spec ambient site path depth initial index
        schemas selected middle ∧
      GeneralScopedMatch.Bag rule spec ambient site path depth middle (index + schemas.length)
        [] rest kind residual final := by
  induction schemas generalizing targets initial index with
  | nil =>
    cases matched with
    | nil => exact ⟨[], [], _, rfl, .refl _, .nil, by simpa using GeneralScopedMatch.Bag.nil⟩
    | rest captured =>
      exact ⟨[], _, initial, rfl, .refl _, .nil, by simpa using GeneralScopedMatch.Bag.rest captured⟩
  | cons schema schemas recurse =>
    cases matched with
    | cons selectedIndex within head tail =>
      obtain ⟨selected, residual, middle, length, account, arguments, finished⟩ := recurse tail
      refine ⟨targets[selectedIndex] :: selected, residual, middle, ?_, ?_, .cons head arguments, ?_⟩
      · simp only [List.length_cons, length]
      · exact (account.cons _).trans (List.getElem_cons_eraseIdx_perm within)
      · convert finished using 1
        simp only [List.length_cons]
        omega

#print axioms scoped_bag_selected_values

/-- Actual scoped source matches, at every schema arity, recover finite
physical groups with their complete recursive matching and rest witnesses.
Equal-valued original records remain separate in the global permutation. -/
theorem scoped_source_groups_covered
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unitLabel) (applyBindings bindings row.left) =
          normalForm (some unitLabel) (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern} {elements schemas : List Pattern}
    (sourceGood : Admissible language free bound (.base bag.category) source)
    (representativeGood : Admissible language free bound (.base bag.category)
      (.collection .hashBag elements none))
    (equivalent : ReferenceStep.Equivalent relEnv language source (.collection .hashBag elements none))
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth index : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final : ScopedRuleMatching.Assignment}
    {rest : Option String}
    (matched : GeneralScopedMatch.Bag rule spec ambient site path depth initial index
      schemas rest .hashBag elements final) :
    ∃ groups residual selected originalResidual middle,
      (groups, residual) ∈ groupedOccurrences schemas.length (normalizedOccurrences unitLabel source) ∧
      GeneralScopedMatch.Arguments rule spec ambient site path depth initial index schemas selected middle ∧
      GeneralScopedMatch.Bag rule spec ambient site path depth middle (index + schemas.length)
        [] rest .hashBag originalResidual final ∧
      groups.map (fun group => collapse unitLabel (group.map SourceOccurrence.value)) =
        selected.map (normalForm (some unitLabel)) ∧
      residual.map SourceOccurrence.value =
        bagContents unitLabel (originalResidual.map (normalForm (some unitLabel))) ∧
      List.Forall₂ (fun original group =>
        Admissible language free bound (.base bag.category) original ∧
        Admissible language free bound (.base bag.category)
          (collapse unitLabel (group.map SourceOccurrence.value)) ∧
        ReferenceStep.Equivalent relEnv language original
          (collapse unitLabel (group.map SourceOccurrence.value))) selected groups ∧
      Admissible language free bound (.collection .hashBag (.base bag.category))
        (.collection .hashBag originalResidual none) ∧
      ((groups.flatten ++ residual) ++ unitOccurrences unitLabel source).Perm
        (sourceOccurrences unitLabel source) := by
  obtain ⟨selected, originalResidual, middle, selectedLength, selectedAccount,
    selectedMatches, restRead⟩ := scoped_bag_selected_values matched
  have normalEqual := (reference_equivalent_iff_normalForm_eq laws rows aligned relEnv
    sourceGood representativeGood rfl).mp equivalent
  let valueGroups := selected.map (fun element => bagContents unitLabel [normalForm (some unitLabel) element])
  have groupContents : valueGroups.flatten = bagContents unitLabel (selected.map (normalForm (some unitLabel))) := by
    simpa only [valueGroups, List.flatMap] using bagContents_flatMap unitLabel selected
  have components := ((selectedAccount.map (normalForm (some unitLabel))).flatMap_right splice).filter
    (fun pattern => decide (pattern ≠ .apply unitLabel []))
  change (bagContents unitLabel ((selected ++ originalResidual).map (normalForm (some unitLabel)))).Perm
    (bagContents unitLabel (elements.map (normalForm (some unitLabel)))) at components
  rw [List.map_append, bagContents_append] at components
  have sortedAccount : (bagContents unitLabel (elements.map (normalForm (some unitLabel)))).Perm
      ((normalizedOccurrences unitLabel source).map SourceOccurrence.value) := by
    rw [normalizedOccurrences_values, normalEqual, normalForm_bag_contents]
    exact (sortPatterns_perm _).symm
  have account := components.trans sortedAccount
  rw [← groupContents] at account
  obtain ⟨groups, residual, allocation, groupValues, residualValues⟩ :=
    grouped_occurrences_of_values SourceOccurrence.value valueGroups
      (bagContents unitLabel (originalResidual.map (normalForm (some unitLabel)))) account
  have realAllocation : (groups, residual) ∈
      groupedOccurrences schemas.length (normalizedOccurrences unitLabel source) := by
    have lengths : valueGroups.length = schemas.length := by
      simpa only [valueGroups, List.length_map] using selectedLength
    simpa only [lengths] using allocation
  have values : groups.map (fun group => collapse unitLabel (group.map SourceOccurrence.value)) =
      selected.map (normalForm (some unitLabel)) := by
    have collapsed := congrArg (List.map (collapse unitLabel)) groupValues
    simp only [valueGroups, List.map_map, Function.comp_def] at collapsed
    refine collapsed.trans ?_
    exact List.map_congr_left (fun element _ => collapse_contents (rootNormal_normalForm unitLabel element))
  have selectedGood : ∀ element ∈ selected,
      Admissible language free bound (.base bag.category) element := by
    intro element member
    exact source_bag_element laws representativeGood
      (selectedAccount.mem_iff.mp (List.mem_append_left _ member))
  have residualGood : Admissible language free bound (.collection .hashBag (.base bag.category))
      (.collection .hashBag originalResidual none) :=
    (component_row_admissible laws (fun element member => source_bag_element laws representativeGood
      (selectedAccount.mem_iff.mp (List.mem_append_right _ member)))).2
  have mappedPairs : List.Forall₂ (· = ·)
      (groups.map (fun group => collapse unitLabel (group.map SourceOccurrence.value)))
      (selected.map (normalForm (some unitLabel))) := by
    simpa only [List.forall₂_eq_eq_eq] using values
  have groupPairs : List.Forall₂ (fun group original =>
      collapse unitLabel (group.map SourceOccurrence.value) = normalForm (some unitLabel) original)
      groups selected := List.forall₂_map_right_iff.mp (List.forall₂_map_left_iff.mp mappedPairs)
  have sourcePairs : List.Forall₂ (fun original group =>
      Admissible language free bound (.base bag.category) original ∧
        collapse unitLabel (group.map SourceOccurrence.value) = normalForm (some unitLabel) original)
      selected groups :=
    (List.forall₂_and_left selected groups).mpr ⟨selectedGood, groupPairs.flip⟩
  have typedSourcePairs : List.Forall₂ (fun original group =>
      Admissible language free bound (.base bag.category) original ∧
      Admissible language free bound (.base bag.category)
        (collapse unitLabel (group.map SourceOccurrence.value)) ∧
      ReferenceStep.Equivalent relEnv language original
        (collapse unitLabel (group.map SourceOccurrence.value))) selected groups :=
    List.Forall₂.imp (fun original group ⟨good, image⟩ => by
    refine ⟨good, ?_, ?_⟩
    · rw [image]
      exact normalized_admissible laws (ContextualStep.engineBasePremises relEnv) good rfl
    · rw [image]
      exact (ReferenceStep.equivalent_iff_unconditional (fun row member => (rows row member).1) aligned).mp
        (source_equiv_normalForm laws (ContextualStep.engineBasePremises relEnv) good rfl)) sourcePairs
  exact ⟨groups, residual, selected, originalResidual, middle, realAllocation, selectedMatches,
    restRead, values, residualValues, typedSourcePairs, residualGood, grouped_occurrence_account realAllocation⟩

#print axioms scoped_source_groups_covered

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.ScopeBoundary

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted
open CanonicalBags (mapAssignment mapValue)

/-- A later ordinary repeat is covered even when the earlier fresh capture
stored a different raw body in the compared execution. Literal comparison
rejects that body; the actual source account keeps both exact captures. -/
theorem different_raw_assignments_thread (relEnv : Engine.RelationEnv) :
    CanonicalBags.IncreasingSpines rule specification ∧
      value ≠ reversedValue ∧
      capture? rule specification 0 1 .left [0, 0]
        [("F", value)] "F" shallow = some [("F", value)] ∧
      capture? rule specification 0 1 .left [0, 0]
        [("F", reversedValue)] "F" shallow = none ∧
      captureWith? (normalBodyComparison "PZero") rule specification 0 1 .left [0, 0]
        [("F", reversedValue)] "F" shallow = some [("F", reversedValue)] ∧
      mapAssignment (normalForm (some "PZero")) [("F", value)] =
        mapAssignment (normalForm (some "PZero")) [("F", reversedValue)] ∧
      List.Forall₂ (fun (old current : String × ContextualValue) =>
        old.1 = current.1 ∧ old.2.dependencies = current.2.dependencies ∧
          old.2.ambient = current.2.ambient ∧
            ReferenceStep.Equivalent relEnv sourceLanguage old.2.body current.2.body)
        [("F", value)] [("F", reversedValue)] := by
  obtain ⟨increasing, _, _, different, account⟩ := fresh_normal_view_capture_covered relEnv
  have normalBodies : normalForm (some "PZero") value.body =
      normalForm (some "PZero") reversedValue.body := by
    change normalForm (some "PZero") (.collection .hashBag [.bvar 0, .fvar ""] none) =
      normalForm (some "PZero") (.collection .hashBag [.fvar "", .bvar 0] none)
    rw [normalForm_bag, normalForm_bag]
    exact normalizeBag_perm _ ((by decide +kernel :
      ([.bvar 0, .fvar ""] : List Pattern).Perm [.fvar "", .bvar 0]).map _)
  have initialNormal : mapAssignment (normalForm (some "PZero")) [("F", value)] =
      mapAssignment (normalForm (some "PZero")) [("F", reversedValue)] := by
    change [("F", ContextualValue.mk [proc] 0 (normalForm (some "PZero") value.body))] =
      [("F", ContextualValue.mk [proc] 0 (normalForm (some "PZero") reversedValue.body))]
    rw [normalBodies]
  have ordinary : capture? rule specification 0 1 .left [0, 0]
      [("F", value)] "F" shallow = some [("F", value)] := by decide +kernel
  have compared : normalBodyComparison "PZero" "F" reversedValue.body value.body = true :=
    beq_iff_eq.mpr normalBodies.symm
  have viewed : captureWith? (normalBodyComparison "PZero") rule specification 0 1 .left [0, 0]
      [("F", reversedValue)] "F" shallow = some [("F", reversedValue)] := by
    change assignWith (normalBodyComparison "PZero") [("F", reversedValue)] "F" value = _
    have headers : reversedValue.dependencies = value.dependencies ∧
        reversedValue.ambient = value.ambient := ⟨rfl, rfl⟩
    simp only [assignWith, lookup, List.find?_cons, Option.map_some,
      headers.1, headers.2, beq_self_eq_true, compared, Bool.true_and, if_true]
  have spineCheck : variableSpine? ([proc] : List TypeExpr).length [.bvar 0] = some [0] := by
    decide +kernel
  have spine : Mettapedia.GSLT.LanguageDef.RestAwareTyping.PartialSortedSpine [proc] [proc] [0] := by
    refine ⟨rfl, ?_, ?_⟩
    all_goals
      intro index member
      obtain rfl := List.mem_singleton.mp member
      decide +kernel
  obtain ⟨final, captured, finalNormal, finalSource⟩ :=
    capture?_source_transport_assignments source_roles.1
      (by intro row member; cases member) (by intro row member; cases member) relEnv
      (dependencies := [proc]) (ambient := []) (locals := [proc]) (expected := proc)
      (rule := rule) (spec := specification) (site := .left) (path := [0, 0])
      (identifier := "F") (arguments := [.bvar 0]) (indices := [0])
      (firstInitial := [("F", value)]) (secondInitial := [("F", reversedValue)])
      (firstFinal := [("F", value)]) (first := shallow) (second := shallow)
      (by decide +kernel) (by decide +kernel) spineCheck spine source_roles.2.1 source_roles.2.1
      (.inl rfl) (.refl _) initialNormal account ordinary
  have exactFinal : final = [("F", reversedValue)] := Option.some.inj (captured.symm.trans viewed)
  subst final
  exact ⟨increasing, different, ordinary, by decide +kernel, viewed, finalNormal, finalSource⟩

#print axioms different_raw_assignments_thread

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.ScopeBoundary


set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem schema_objects_take {targets : List Pattern} (count : Nat)
    (objects : isObjectPatternList targets = true) :
    isObjectPatternList (targets.take count) = true :=
  isObjectPatternList_iff.mpr fun target member =>
    isObjectPatternList_iff.mp objects target (List.mem_of_mem_take member)

mutual
/-- A real object-source match earns the executable schema guard from the
independent rest-aware typing derivation. No literal substitution node can
match an object target, so compound substitution domains need no oracle. -/
theorem schema_checked_of_source_match
    {language : LanguageDef} {schemaFree : FreeTypeContext} {bound : List TypeExpr}
    {schema target : Pattern} {expected : TypeExpr}
    (typed : RestAwareTyping.HasType language schemaFree bound schema expected)
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final : ScopedRuleMatching.Assignment}
    (matched : GeneralScopedMatch.Matches rule spec ambient site path depth initial schema target final)
    (object : isObjectPattern target = true) :
    RestAwareTyping.checkSchemaHasType language schemaFree bound schema expected = true := by
  cases typed with
  | bvar lookup => simpa only [RestAwareTyping.checkSchemaHasType, beq_iff_eq] using lookup
  | fvar lookup => simpa only [RestAwareTyping.checkSchemaHasType, beq_iff_eq] using lookup
  | @constructor bound declaration schemas declared ordinary argumentsTyped =>
    cases matched with
    | constructor arguments =>
      have notBare : usesBareCollection? declaration = false := by
        apply Bool.eq_false_of_not_eq_true
        intro bare
        exact ordinary ((usesBareCollection?_eq_true_iff declaration).mp bare)
      have checked := schemaArguments_checked_of_source_match argumentsTyped arguments object
      simp only [RestAwareTyping.checkSchemaHasType, List.any_eq_true]
      exact ⟨declaration, declared, by simp [notBare, checked]⟩
  | lambda bodyTyped =>
    cases matched with
    | binder body =>
      have checked := schema_checked_of_source_match bodyTyped body object
      exact checked
  | multiLambda bodyTyped =>
    cases matched with
    | binders body =>
      have checked := schema_checked_of_source_match bodyTyped body object
      exact checked
  | subst bodyTyped replacementTyped =>
    cases matched with
    | substitution body replacement => simp only [isObjectPattern, Bool.false_eq_true] at object
  | @collection bound kind elements rest elementType elementsTyped restTyped =>
    have checkedElements : RestAwareTyping.checkSchemaElements language schemaFree bound elements elementType = true := by
      cases matched with
      | bag notVector bagMatch =>
        exact schemaElements_checked_of_source_bag elementsTyped bagMatch
          (by simpa only [isObjectPattern, Option.isNone, Bool.true_and] using object)
      | vector arguments =>
        exact schemaElements_checked_of_source_arguments elementsTyped arguments
          (by simpa only [isObjectPattern, Option.isNone, Bool.true_and] using object)
      | vectorRest arguments captured =>
        exact schemaElements_checked_of_source_arguments elementsTyped arguments
          (schema_objects_take _ (by simpa only [isObjectPattern, Option.isNone, Bool.true_and] using object))
    have checkedRest : RestAwareTyping.checkRestHasType schemaFree kind elementType rest = true := by
      cases rest with
      | none => rfl
      | some identifier => simpa only [RestAwareTyping.RestHasType,
          RestAwareTyping.checkRestHasType, beq_iff_eq] using restTyped
    simp [RestAwareTyping.checkSchemaHasType, checkedElements, checkedRest]
  | @collectionConstructor bound declaration parameterName kind elements rest elementType
      declared shape elementsTyped restTyped =>
    have checkedElements : RestAwareTyping.checkSchemaElements language schemaFree bound elements elementType = true := by
      cases matched with
      | bag notVector bagMatch =>
        exact schemaElements_checked_of_source_bag elementsTyped bagMatch
          (by simpa only [isObjectPattern, Option.isNone, Bool.true_and] using object)
      | vector arguments =>
        exact schemaElements_checked_of_source_arguments elementsTyped arguments
          (by simpa only [isObjectPattern, Option.isNone, Bool.true_and] using object)
      | vectorRest arguments captured =>
        exact schemaElements_checked_of_source_arguments elementsTyped arguments
          (schema_objects_take _ (by simpa only [isObjectPattern, Option.isNone, Bool.true_and] using object))
    have checkedRest : RestAwareTyping.checkRestHasType schemaFree kind elementType rest = true := by
      cases rest with
      | none => rfl
      | some identifier => simpa only [RestAwareTyping.RestHasType,
          RestAwareTyping.checkRestHasType, beq_iff_eq] using restTyped
    have elementRead : bareCollectionElementType? declaration kind (.base declaration.category) =
        some elementType :=
      (bareCollectionElementType?_eq_some_iff declaration kind (.base declaration.category) elementType).mpr
        ⟨rfl, parameterName, shape⟩
    simp only [RestAwareTyping.checkSchemaHasType, Bool.or_eq_true]
    exact .inr (List.any_eq_true.mpr ⟨declaration, declared, by
      rw [elementRead]
      change (RestAwareTyping.checkSchemaElements language schemaFree bound elements elementType &&
        RestAwareTyping.checkRestHasType schemaFree kind elementType rest) = true
      rw [checkedElements, checkedRest]
      rfl⟩)
termination_by sizeOf schema
decreasing_by all_goals sizeOf_pattern_dec

theorem schemaArguments_checked_of_source_match
    {language : LanguageDef} {schemaFree : FreeTypeContext} {bound : List TypeExpr}
    {schemas targets : List Pattern} {parameters : List TermParam}
    (typed : RestAwareTyping.ArgumentsHaveTypes language schemaFree bound schemas parameters)
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth index : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final : ScopedRuleMatching.Assignment}
    (matched : GeneralScopedMatch.Arguments rule spec ambient site path depth initial index schemas targets final)
    (objects : isObjectPatternList targets = true) :
    RestAwareTyping.checkSchemaArguments language schemaFree bound schemas parameters = true := by
  cases typed with
  | nil => rfl
  | cons represented parameterType firstTyped restTyped =>
    cases matched with
    | cons first rest =>
      simp only [isObjectPatternList, Bool.and_eq_true] at objects
      simp only [RestAwareTyping.checkSchemaArguments, parameterType, Bool.and_eq_true]
      exact ⟨⟨(matchesParameterRepresentation?_eq_true_iff _ _).mpr represented,
        schema_checked_of_source_match firstTyped first objects.1⟩,
        schemaArguments_checked_of_source_match restTyped rest objects.2⟩
termination_by sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec

theorem schemaElements_checked_of_source_arguments
    {language : LanguageDef} {schemaFree : FreeTypeContext} {bound : List TypeExpr}
    {schemas targets : List Pattern} {elementType : TypeExpr}
    (typed : RestAwareTyping.ElementsHaveType language schemaFree bound schemas elementType)
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth index : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final : ScopedRuleMatching.Assignment}
    (matched : GeneralScopedMatch.Arguments rule spec ambient site path depth initial index schemas targets final)
    (objects : isObjectPatternList targets = true) :
    RestAwareTyping.checkSchemaElements language schemaFree bound schemas elementType = true := by
  cases typed with
  | nil => rfl
  | cons firstTyped restTyped =>
    cases matched with
    | cons first rest =>
      simp only [isObjectPatternList, Bool.and_eq_true] at objects
      simp only [RestAwareTyping.checkSchemaElements, Bool.and_eq_true]
      exact ⟨schema_checked_of_source_match firstTyped first objects.1,
        schemaElements_checked_of_source_arguments restTyped rest objects.2⟩
termination_by sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec

theorem schemaElements_checked_of_source_bag
    {language : LanguageDef} {schemaFree : FreeTypeContext} {bound : List TypeExpr}
    {schemas targets : List Pattern} {elementType : TypeExpr}
    (typed : RestAwareTyping.ElementsHaveType language schemaFree bound schemas elementType)
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth index : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final : ScopedRuleMatching.Assignment}
    {rest : Option String} {kind : CollType}
    (matched : GeneralScopedMatch.Bag rule spec ambient site path depth initial index schemas rest kind targets final)
    (objects : isObjectPatternList targets = true) :
    RestAwareTyping.checkSchemaElements language schemaFree bound schemas elementType = true := by
  cases typed with
  | nil => rfl
  | cons firstTyped restTyped =>
    cases matched with
    | cons selected within first rest =>
      have each := isObjectPatternList_iff.mp objects
      simp only [RestAwareTyping.checkSchemaElements, Bool.and_eq_true]
      exact ⟨schema_checked_of_source_match firstTyped first (each _ (List.getElem_mem within)),
        schemaElements_checked_of_source_bag restTyped rest
          (isObjectPatternList_iff.mpr fun target member => each target (List.mem_of_mem_eraseIdx member))⟩
termination_by sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec
end

#print axioms schema_checked_of_source_match
#print axioms schemaArguments_checked_of_source_match
#print axioms schemaElements_checked_of_source_arguments
#print axioms schemaElements_checked_of_source_bag

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView


set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open CanonicalBags (mapAssignment)

/-- The ordinary source capture is included in the compared traversal on
the same presentation, even with different incoming raw assignments. -/
theorem capture_normal_on_source
    {language : LanguageDef} (relEnv : Engine.RelationEnv) (unit : String)
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
    {site : RulePatternSite} {path : List Nat} {identifier : String} {target : Pattern}
    {firstInitial secondInitial firstFinal : ScopedRuleMatching.Assignment}
    (initialNormal : mapAssignment (normalForm (some unit)) firstInitial =
      mapAssignment (normalForm (some unit)) secondInitial)
    (initialSource : List.Forall₂ (fun (old current : String × ContextualValue) =>
        old.1 = current.1 ∧ old.2.dependencies = current.2.dependencies ∧
          old.2.ambient = current.2.ambient ∧
            ReferenceStep.Equivalent relEnv language old.2.body current.2.body)
      firstInitial secondInitial)
    (captured : capture? rule spec ambient depth site path firstInitial identifier target = some firstFinal) :
    ∃ secondFinal,
      captureWith? (normalBodyComparison unit) rule spec ambient depth site path
        secondInitial identifier target = some secondFinal ∧
      mapAssignment (normalForm (some unit)) firstFinal =
        mapAssignment (normalForm (some unit)) secondFinal ∧
      List.Forall₂ (fun (old current : String × ContextualValue) =>
        old.1 = current.1 ∧ old.2.dependencies = current.2.dependencies ∧
          old.2.ambient = current.2.ambient ∧
            ReferenceStep.Equivalent relEnv language old.2.body current.2.body)
        firstFinal secondFinal := by
  simp only [capture?, Option.bind_eq_bind, Option.bind_eq_some_iff] at captured
  obtain ⟨dependencies, declared, arguments, atSite, value, recovered, assigned⟩ := captured
  obtain ⟨secondFinal, secondAssigned, finalNormal, finalSource⟩ :=
    assignWith_normal_source_transport relEnv unit initialNormal initialSource
      (firstValue := value) (secondValue := value) ⟨rfl, rfl⟩ rfl (.refl _) assigned
  refine ⟨secondFinal, ?_, finalNormal, finalSource⟩
  simp only [captureWith?, declared, atSite, Option.bind_eq_bind, Option.bind_some,
    recovered, secondAssigned]

#print axioms capture_normal_on_source

mutual
/-- Full recursive ordinary matching transports different incoming assignments on the same presentation. The target is not silently replaced by an algebra normal form. -/
theorem matching_normal_on_source
    {language : LanguageDef} (relEnv : Engine.RelationEnv) (unit : String)
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
    {site : RulePatternSite} {path : List Nat}
    {firstInitial secondInitial firstFinal : ScopedRuleMatching.Assignment}
    {schema target : Pattern}
    (initialNormal : mapAssignment (normalForm (some unit)) firstInitial =
      mapAssignment (normalForm (some unit)) secondInitial)
    (initialSource : List.Forall₂ (fun (old current : String × ContextualValue) =>
        old.1 = current.1 ∧ old.2.dependencies = current.2.dependencies ∧
          old.2.ambient = current.2.ambient ∧
            ReferenceStep.Equivalent relEnv language old.2.body current.2.body)
      firstInitial secondInitial)
    (matched : GeneralScopedMatch.Matches rule spec ambient site path depth firstInitial schema target firstFinal) :
    ∃ secondFinal,
      secondFinal ∈ matchAtWith (normalBodyComparison unit) rule spec ambient site path depth secondInitial schema target ∧
      mapAssignment (normalForm (some unit)) firstFinal =
        mapAssignment (normalForm (some unit)) secondFinal ∧
      List.Forall₂ (fun (old current : String × ContextualValue) =>
        old.1 = current.1 ∧ old.2.dependencies = current.2.dependencies ∧
          old.2.ambient = current.2.ambient ∧
            ReferenceStep.Equivalent relEnv language old.2.body current.2.body)
        firstFinal secondFinal := by
  cases matched with
  | capture captured =>
    obtain ⟨secondFinal, secondCaptured, normal, source⟩ :=
      capture_normal_on_source relEnv unit initialNormal initialSource captured
    exact ⟨secondFinal, by simpa only [matchAtWith, Option.mem_toList] using secondCaptured, normal, source⟩
  | bound =>
    exact ⟨secondInitial, by simp only [matchAtWith, beq_self_eq_true, if_true, List.mem_singleton], initialNormal, initialSource⟩
  | constructor arguments =>
    obtain ⟨secondFinal, member, normal, source⟩ :=
      matchingArguments_normal_on_source relEnv unit initialNormal initialSource arguments
    exact ⟨secondFinal, by simpa only [matchAtWith, beq_self_eq_true, if_true] using member, normal, source⟩
  | binder body =>
    obtain ⟨secondFinal, member, normal, source⟩ :=
      matching_normal_on_source relEnv unit initialNormal initialSource body
    exact ⟨secondFinal, by simpa only [matchAtWith] using member, normal, source⟩
  | binders body =>
    obtain ⟨secondFinal, member, normal, source⟩ :=
      matching_normal_on_source relEnv unit initialNormal initialSource body
    exact ⟨secondFinal, by simpa only [matchAtWith, beq_self_eq_true, if_true] using member, normal, source⟩
  | substitution body replacement =>
    obtain ⟨secondMiddle, bodyMember, middleNormal, middleSource⟩ :=
      matching_normal_on_source relEnv unit initialNormal initialSource body
    obtain ⟨secondFinal, replacementMember, finalNormal, finalSource⟩ :=
      matching_normal_on_source relEnv unit middleNormal middleSource replacement
    exact ⟨secondFinal, by
      simp only [matchAtWith, List.mem_flatMap]
      exact ⟨secondMiddle, bodyMember, replacementMember⟩, finalNormal, finalSource⟩
  | bag notVector bagMatch =>
    obtain ⟨secondFinal, member, normal, source⟩ :=
      matchingBag_normal_on_source relEnv unit initialNormal initialSource bagMatch
    exact ⟨secondFinal, by
      unfold matchAtWith
      simpa only [beq_self_eq_true, Option.isNone_none, Bool.and_self,
        beq_iff_eq, notVector, if_false, if_true] using member, normal, source⟩
  | vector arguments =>
    obtain ⟨secondFinal, member, normal, source⟩ :=
      matchingArguments_normal_on_source relEnv unit initialNormal initialSource arguments
    exact ⟨secondFinal, by
      simpa only [matchAtWith, beq_self_eq_true, Option.isNone_none, Bool.and_self,
        if_true] using member, normal, source⟩
  | vectorRest arguments captured =>
    obtain ⟨secondMiddle, member, middleNormal, middleSource⟩ :=
      matchingArguments_normal_on_source relEnv unit initialNormal initialSource arguments
    obtain ⟨secondFinal, secondCaptured, finalNormal, finalSource⟩ :=
      capture_normal_on_source relEnv unit middleNormal middleSource captured
    exact ⟨secondFinal, by
      simp only [matchAtWith, beq_self_eq_true, Option.isNone_none, Bool.and_self,
        if_true, List.mem_filterMap]
      exact ⟨secondMiddle, member, secondCaptured⟩, finalNormal, finalSource⟩
termination_by sizeOf schema

/-- Ordered arguments thread every captured body and complete contextual header through the shared compared traversal. -/
theorem matchingArguments_normal_on_source
    {language : LanguageDef} (relEnv : Engine.RelationEnv) (unit : String)
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
    {site : RulePatternSite} {path : List Nat}
    {firstInitial secondInitial firstFinal : ScopedRuleMatching.Assignment}
    {index : Nat} {schemas targets : List Pattern}
    (initialNormal : mapAssignment (normalForm (some unit)) firstInitial =
      mapAssignment (normalForm (some unit)) secondInitial)
    (initialSource : List.Forall₂ (fun (old current : String × ContextualValue) =>
        old.1 = current.1 ∧ old.2.dependencies = current.2.dependencies ∧
          old.2.ambient = current.2.ambient ∧
            ReferenceStep.Equivalent relEnv language old.2.body current.2.body)
      firstInitial secondInitial)
    (matched : GeneralScopedMatch.Arguments rule spec ambient site path depth firstInitial index schemas targets firstFinal) :
    ∃ secondFinal,
      secondFinal ∈ matchArgsAtWith (normalBodyComparison unit) rule spec ambient site path depth secondInitial index schemas targets ∧
      mapAssignment (normalForm (some unit)) firstFinal =
        mapAssignment (normalForm (some unit)) secondFinal ∧
      List.Forall₂ (fun (old current : String × ContextualValue) =>
        old.1 = current.1 ∧ old.2.dependencies = current.2.dependencies ∧
          old.2.ambient = current.2.ambient ∧
            ReferenceStep.Equivalent relEnv language old.2.body current.2.body)
        firstFinal secondFinal := by
  cases matched with
  | nil => exact ⟨secondInitial, by simp only [matchArgsAtWith, List.mem_singleton], initialNormal, initialSource⟩
  | cons head tail =>
    obtain ⟨secondMiddle, headMember, middleNormal, middleSource⟩ :=
      matching_normal_on_source relEnv unit initialNormal initialSource head
    obtain ⟨secondFinal, tailMember, finalNormal, finalSource⟩ :=
      matchingArguments_normal_on_source relEnv unit middleNormal middleSource tail
    exact ⟨secondFinal, by
      simp only [matchArgsAtWith, List.mem_flatMap]
      exact ⟨secondMiddle, headMember, tailMember⟩, finalNormal, finalSource⟩
termination_by sizeOf schemas

/-- The actual bag/set position and erased residual are preserved at each source selection. This result grants no virtual representative or extra origin. -/
theorem matchingBag_normal_on_source
    {language : LanguageDef} (relEnv : Engine.RelationEnv) (unit : String)
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
    {site : RulePatternSite} {path : List Nat}
    {firstInitial secondInitial firstFinal : ScopedRuleMatching.Assignment}
    {index : Nat} {schemas targets : List Pattern}
    {rest : Option String} {kind : CollType}
    (initialNormal : mapAssignment (normalForm (some unit)) firstInitial =
      mapAssignment (normalForm (some unit)) secondInitial)
    (initialSource : List.Forall₂ (fun (old current : String × ContextualValue) =>
        old.1 = current.1 ∧ old.2.dependencies = current.2.dependencies ∧
          old.2.ambient = current.2.ambient ∧
            ReferenceStep.Equivalent relEnv language old.2.body current.2.body)
      firstInitial secondInitial)
    (matched : GeneralScopedMatch.Bag rule spec ambient site path depth firstInitial index schemas rest kind targets firstFinal) :
    ∃ secondFinal,
      secondFinal ∈ matchBagAtWith (normalBodyComparison unit) rule spec ambient site path depth secondInitial index schemas rest kind targets ∧
      mapAssignment (normalForm (some unit)) firstFinal =
        mapAssignment (normalForm (some unit)) secondFinal ∧
      List.Forall₂ (fun (old current : String × ContextualValue) =>
        old.1 = current.1 ∧ old.2.dependencies = current.2.dependencies ∧
          old.2.ambient = current.2.ambient ∧
            ReferenceStep.Equivalent relEnv language old.2.body current.2.body)
        firstFinal secondFinal := by
  cases matched with
  | nil => exact ⟨secondInitial, by simp only [matchBagAtWith, List.isEmpty_nil, if_true, List.mem_singleton], initialNormal, initialSource⟩
  | rest captured =>
    obtain ⟨secondFinal, secondCaptured, normal, source⟩ :=
      capture_normal_on_source relEnv unit initialNormal initialSource captured
    exact ⟨secondFinal, by simpa only [matchBagAtWith, captureRestWith?, Option.mem_toList] using secondCaptured, normal, source⟩
  | cons selected within head tail =>
    obtain ⟨secondMiddle, headMember, middleNormal, middleSource⟩ :=
      matching_normal_on_source relEnv unit initialNormal initialSource head
    obtain ⟨secondFinal, tailMember, finalNormal, finalSource⟩ :=
      matchingBag_normal_on_source relEnv unit middleNormal middleSource tail
    have selectedPresent : (targets[selected], selected) ∈ targets.zipIdx := by
      have selectedBound : selected < targets.zipIdx.length := by simpa using within
      simpa using List.getElem_mem selectedBound
    exact ⟨secondFinal, by
      simp only [matchBagAtWith, List.mem_flatMap]
      exact ⟨(targets[selected], selected), selectedPresent, secondMiddle, headMember, tailMember⟩,
      finalNormal, finalSource⟩
termination_by sizeOf schemas
end

#print axioms matching_normal_on_source
#print axioms matchingArguments_normal_on_source
#print axioms matchingBag_normal_on_source

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.ScopeBoundary

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted
open CanonicalBags (mapAssignment)

/-- The actual typed binder schema earns its executable constructor guard
from the independent whole source match; no guard Boolean is postulated. -/
theorem schema_guard_from_source :
    RestAwareTyping.checkSchemaHasType sourceLanguage schemaFree [] schema proc = true := by
  exact schema_checked_of_source_match
    (RestAwareTyping.HasType.ofObject source_roles.2.2.2.2.typed source_roles.2.2.2.2.object)
    scoped_matching_separator.1 source_roles.2.2.2.1.object

/-- Unrestricted schema-checker completeness is false for a compound
substitution domain. The independent matching domain excludes this literal
node only because an object subject cannot contain a pending substitution. -/
theorem compound_substitution_guard_boundary :
    RestAwareTyping.HasType sourceLanguage schemaFree []
      (.subst (.bvar 0) (.lambda none (.bvar 0))) (.arrow proc proc) ∧
      RestAwareTyping.checkSchemaHasType sourceLanguage schemaFree []
        (.subst (.bvar 0) (.lambda none (.bvar 0))) (.arrow proc proc) = false ∧
      ∀ target initial final, isObjectPattern target = true →
        ¬ GeneralScopedMatch.Matches rule specification 0 .left [] 0 initial
          (.subst (.bvar 0) (.lambda none (.bvar 0))) target final := by
  refine ⟨.subst (.bvar rfl) (.lambda (.bvar rfl)), by decide +kernel, ?_⟩
  intro target initial final object matched
  cases matched with
  | substitution body replacement => simp only [isObjectPattern, Bool.false_eq_true] at object

/-- The complete original increasing-spine example is repaired in the
actual shared compared matcher, while its old literal counterexample stays
visible. The normalized target belongs to the actual authored source class. -/
theorem whole_normal_view_matching (relEnv : Engine.RelationEnv) :
    CanonicalBags.IncreasingSpines rule specification ∧
      GeneralScopedMatch.Matches rule specification 0 .left [] 0 [] schema source [("F", value)] ∧
      matchAt rule specification 0 .left [] 0 [] schema (normalForm (some "PZero") source) = [] ∧
      matchAtWith (normalBodyComparison "PZero") rule specification 0 .left [] 0 []
        schema (normalForm (some "PZero") source) = [[("F", value)]] ∧
      ReferenceStep.Equivalent relEnv sourceLanguage source (normalForm (some "PZero") source) := by
  have firstCapture : captureWith? (normalBodyComparison "PZero") rule specification 0 1 .left [0, 0]
      [] "F" shallow = some [("F", value)] := by decide +kernel
  have secondCapture := (normalized_capture_recovers_source_presentation relEnv).2.2.1
  rw [explicit_normal_forms.2.1] at secondCapture
  have whole : matchAtWith (normalBodyComparison "PZero") rule specification 0 .left [] 0 []
      schema (normalForm (some "PZero") source) = [[("F", value)]] := by
    rw [explicit_normal_forms.2.2]
    simp only [schema, matchAtWith, matchArgsAtWith, beq_self_eq_true, if_true,
      Nat.reduceAdd, List.cons_append, List.nil_append, firstCapture, secondCapture,
      Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have sourceEquivalent : ReferenceStep.Equivalent relEnv sourceLanguage source
      (normalForm (some "PZero") source) :=
    (ReferenceStep.equivalent_iff_unconditional (by intro row member; cases member)
      (by intro row member; cases member)).mp
      (source_equiv_normalForm source_roles.1 (ContextualStep.engineBasePremises relEnv)
        source_roles.2.2.2.1 rfl)
  exact ⟨all_spines_increasing, scoped_matching_separator.1, scoped_matching_separator.2,
    whole, sourceEquivalent⟩

#print axioms schema_guard_from_source
#print axioms compound_substitution_guard_boundary
#print axioms whole_normal_view_matching

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.ScopeBoundary


namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

open Mettapedia.OSLF.MeTTaIL Syntax ContextualStep DerivedContexts GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

/-- An original typed focus and a virtual group have different origin data.
A group retains the existing physical records instead of traversing a new
normalized copy to manufacture replacement addresses. -/
inductive Focus where
  | original (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) (context : OneHoleContext)
  | grouped (bound : List TypeExpr) (components : List SourceOccurrence)
  deriving Repr,DecidableEq

namespace Focus

def bound : Focus → List TypeExpr
  | .original bound _ _ _ => bound
  | .grouped bound _ => bound

def expected (category : String) : Focus → TypeExpr
  | .original _ expected _ _ => expected
  | .grouped _ _ => .base category

def value (unitLabel : String) : Focus → Pattern
  | .original _ _ source _ => source
  | .grouped _ components => collapse unitLabel (components.map SourceOccurrence.value)

def components (unitLabel : String) : Focus → List SourceOccurrence
  | .original _ _ source context =>
      (normalizedOccurrences unitLabel source).map (SourceOccurrence.underContext context)
  | .grouped _ components => components

def units (unitLabel category : String) : Focus → List SourceOccurrence
  | .original _ expected source context =>
      if expected == .base category then
        (unitOccurrences unitLabel source).map (SourceOccurrence.underContext context)
      else []
  | .grouped _ _ => []

def scalar? (unitLabel category : String) : Focus → Option SourceHead
  | focus@(.original _ expected source context) =>
      if expected == .base category then sourceHead? (focus.components unitLabel)
      else some (.physical ((SourceOccurrence.leaf unitLabel source).underContext context))
  | .grouped _ components => sourceHead? components

/-- The role and complete local context are those already recorded by the
original typed occurrence. This adds no operational descent permission. -/
def ofSite (site : SiteData) : Focus :=
  .original site.focusBound site.focusType site.focus site.context

end Focus

def headContext? : SourceHead → Option OneHoleContext
  | .unit => none
  | .physical occurrence => some occurrence.context

/-- One retained presentation frame, with actual constructor declaration
position or physical group allocation when applicable. -/
structure Frame where
  path : List Nat
  schemaBound : List TypeExpr
  focus : Focus
  declaration : Option Nat := none
  grouping : Option (List (List SourceOccurrence) × List SourceOccurrence) := none
  deriving Repr,DecidableEq

structure Spelling where
  target : Pattern
  frames : List Frame
  deriving Repr,DecidableEq

/-- Constructor roles come from actual declarations checked against both
spines. Source ambient variables and schema-local binders are kept separate. -/
def constructorChoices (language : LanguageDef) (free schemaFree : FreeTypeContext)
    (sourceBound schemaBound : List TypeExpr) (expected : TypeExpr)
    (label : String) (schemas sources : List Pattern) : List (GrammarRule × Nat) :=
  language.terms.zipIdx.filter fun entry =>
    entry.1.label == label && expected == .base entry.1.category && !usesBareCollection? entry.1 &&
      checkArgumentsHaveTypes language free sourceBound sources entry.1.params &&
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaArguments
        language schemaFree schemaBound schemas entry.1.params


/-- Every constructor choice retains its actual declaration position and
both independently checked typing spines. -/
theorem constructorChoices_sound {language : LanguageDef} {free schemaFree : FreeTypeContext}
    {sourceBound schemaBound : List TypeExpr} {expected : TypeExpr} {label : String}
    {schemas sources : List Pattern} {rule : GrammarRule} {index : Nat}
    (member : (rule,index) ∈ constructorChoices language free schemaFree
      sourceBound schemaBound expected label schemas sources) :
    language.terms[index]? = some rule ∧ rule.label = label ∧ expected = .base rule.category ∧
      ¬ UsesBareCollection rule ∧
      ArgumentsHaveTypes language free sourceBound sources rule.params ∧
      Mettapedia.GSLT.LanguageDef.RestAwareTyping.ArgumentsHaveTypes
        language schemaFree schemaBound schemas rule.params := by
  obtain ⟨indexed,checked⟩ := List.mem_filter.mp member
  simp only [Bool.and_eq_true,beq_iff_eq] at checked
  rcases checked with ⟨⟨⟨⟨labelEq,typeEq⟩,notBare⟩,sourceChecked⟩,schemaChecked⟩
  refine ⟨List.mk_mem_zipIdx_iff_getElem?.mp indexed,labelEq,typeEq,?_,?_,?_⟩
  · intro bare
    have yes := (usesBareCollection?_eq_true_iff rule).mpr bare
    simp only [yes] at notBare
    contradiction
  · exact checkArgumentsHaveTypes_sound_of
      (fun _ _ _ valid => checkHasType_sound valid) sourceChecked
  · exact Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaArguments_sound_of
      (fun _ _ _ valid => Mettapedia.GSLT.LanguageDef.RestAwareTyping.checkSchemaHasType_sound valid)
      schemaChecked

#print axioms constructorChoices_sound

mutual
/-- Generate finite source spellings and their retained origin frames.
Ordinary matching remains in the shared scoped matcher; this function only
constructs schema-directed presentation alternatives. -/
def presentAt (language : LanguageDef) (free schemaFree : FreeTypeContext)
    (category unitLabel : String) (schemaBound : List TypeExpr) (path : List Nat)
    (schema : Pattern) (focus : Focus) : List Spelling :=
  match schema with
  | .fvar _ =>
      [⟨normalForm (some unitLabel) (focus.value unitLabel),[⟨path,schemaBound,focus,none,none⟩]⟩]
  | .collection .hashBag schemas rest =>
      if focus.expected category == .base category then
        (groupedOccurrences schemas.length (focus.components unitLabel)).flatMap fun allocation =>
          let residual := sortOccurrences allocation.2
          if rest.isNone && !residual.isEmpty then [] else
          (presentGroups language free schemaFree category unitLabel schemaBound path focus.bound
            0 schemas allocation.1).map fun children =>
              ⟨.collection .hashBag (children.1 ++ residual.map SourceOccurrence.value) none,
                ⟨path,schemaBound,focus,none,some (allocation.1,residual)⟩ :: children.2⟩
      else []
  | .collection _ _ _ => []
  | .bvar expected =>
      match focus.scalar? unitLabel category with
      | some head =>
          match head.original unitLabel with
          | .bvar actual =>
              if expected == actual then [⟨.bvar actual,[⟨path,schemaBound,focus,none,none⟩]⟩] else []
          | _ => []
      | none => []
  | .apply label schemas =>
      match focus.scalar? unitLabel category with
      | some head =>
          match head.original unitLabel with
          | .apply actual sources =>
              if label == actual then
                (constructorChoices language free schemaFree focus.bound schemaBound (focus.expected category)
                  actual schemas sources).flatMap fun entry =>
                    (presentArguments language free schemaFree category unitLabel schemaBound path focus.bound
                      actual (headContext? head) sources 0 schemas sources entry.1.params).map fun children =>
                        ⟨.apply actual children.1,
                          ⟨path,schemaBound,focus,some entry.2,none⟩ :: children.2⟩
              else []
          | _ => []
      | none => []
  | .lambda _ schemaBody =>
      match focus.scalar? unitLabel category,focus.expected category with
      | some head,.arrow domain codomain =>
          match head.original unitLabel,(headContext? head) with
          | .lambda binder sourceBody,some outer =>
              (presentAt language free schemaFree category unitLabel (domain :: schemaBound) (path ++ [0])
                schemaBody (.original (domain :: focus.bound) codomain sourceBody
                  (outer.comp (.lambda binder .hole)))).map fun body =>
                    ⟨.lambda binder body.target,⟨path,schemaBound,focus,none,none⟩ :: body.frames⟩
          | _,_ => []
      | _,_ => []
  | .multiLambda arity _ schemaBody =>
      match focus.scalar? unitLabel category,focus.expected category with
      | some head,.arrow (.multiBinder domain) codomain =>
          match head.original unitLabel,(headContext? head) with
          | .multiLambda actual binders sourceBody,some outer =>
              if arity == actual then
                (presentAt language free schemaFree category unitLabel
                  (List.replicate arity domain ++ schemaBound) (path ++ [0]) schemaBody
                  (.original (List.replicate arity domain ++ focus.bound) codomain sourceBody
                    (outer.comp (.multiLambda arity binders .hole)))).map fun body =>
                      ⟨.multiLambda arity binders body.target,⟨path,schemaBound,focus,none,none⟩ :: body.frames⟩
              else []
          | _,_ => []
      | _,_ => []
  | .subst _ _ => []
termination_by sizeOf schema
decreasing_by all_goals sizeOf_pattern_dec

def presentArguments (language : LanguageDef) (free schemaFree : FreeTypeContext)
    (category unitLabel : String) (schemaBound : List TypeExpr) (path : List Nat)
    (bound : List TypeExpr) (label : String) (outer : Option OneHoleContext)
    (originals : List Pattern) (index : Nat) :
    List Pattern → List Pattern → List TermParam → List (List Pattern × List Frame)
  | [],[],[] => [([],[])]
  | schema :: schemas,source :: sources,parameter :: parameters =>
      match outer,parameterType? parameter with
      | some context,some expected =>
          (presentAt language free schemaFree category unitLabel schemaBound (path ++ [index]) schema
            (.original bound expected source
              (context.comp (.apply label (originals.take index) .hole (originals.drop (index + 1)))))).flatMap fun head =>
                (presentArguments language free schemaFree category unitLabel schemaBound path bound label outer originals
                  (index + 1) schemas sources parameters).map fun later =>
                    (head.target :: later.1,head.frames ++ later.2)
      | _,_ => []
  | _,_,_ => []
termination_by schemas _ _ => sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec

def presentGroups (language : LanguageDef) (free schemaFree : FreeTypeContext)
    (category unitLabel : String) (schemaBound : List TypeExpr) (path : List Nat)
    (bound : List TypeExpr) (index : Nat) :
    List Pattern → List (List SourceOccurrence) → List (List Pattern × List Frame)
  | [],[] => [([],[])]
  | schema :: schemas,group :: groups =>
      (presentAt language free schemaFree category unitLabel schemaBound (path ++ [index]) schema
        (.grouped bound group)).flatMap fun head =>
          (presentGroups language free schemaFree category unitLabel schemaBound path bound (index + 1)
            schemas groups).map fun later => (head.target :: later.1,head.frames ++ later.2)
  | _,_ => []
termination_by schemas _ => sizeOf schemas
decreasing_by all_goals sizeOf_pattern_dec
end


/-- Primitive component evidence records the typed original and its actual
normal value. No firing or matching conclusion is part of this evidence. -/
structure ComponentValid (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (category unitLabel : String) (occurrence : SourceOccurrence) : Prop where
  originalGood : Admissible language free bound (.base category) occurrence.original
  normalized : occurrence.value = normalForm (some unitLabel) occurrence.original
  plain : occurrence.value ≠ .apply unitLabel [] ∧ ¬ IsBagNode occurrence.value

/-- A virtual group inherits component evidence; an original focus retains
its source type and the collection-free role required by this bag theory. -/
def Focus.Valid (language : LanguageDef) (free : FreeTypeContext) (category unitLabel : String) : Focus → Prop
  | .original bound expected source _ =>
      Admissible language free bound expected source ∧ collectionFree expected = true
  | .grouped bound components =>
      ∀ occurrence ∈ components,ComponentValid language free bound category unitLabel occurrence

private theorem normalForm_stable {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} (good : Admissible language free bound expected source)
    (collectionless : collectionFree expected = true) :
    normalForm (some unitLabel) (normalForm (some unitLabel) source) = normalForm (some unitLabel) source := by
  have comparisonGood := grammar_admissible (source := language)
    (target := {language with equations := []}) rfl good
  exact (normalForm_eq_of_equationEquiv laws.toBagTheory
    (equationEquiv_normalForm laws base comparisonGood collectionless)).symm

/-- The focused value is typed independently of the presentation producer. -/
theorem Focus.valid_value {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {focus : Focus}
    (good : focus.Valid language free bag.category unitLabel) :
    Admissible language free focus.bound (focus.expected bag.category) (focus.value unitLabel) := by
  cases focus with
  | original bound expected source context => exact good.1
  | grouped bound components =>
    apply collapsed_row_admissible laws base
    intro value member
    obtain ⟨occurrence,inside,rfl⟩ := List.mem_map.mp member
    have original := good occurrence inside
    rw [original.normalized]
    exact normalized_admissible laws base original.originalGood rfl

theorem Focus.valid_collectionFree {language : LanguageDef} {free : FreeTypeContext}
    {category unitLabel : String} {focus : Focus}
    (good : focus.Valid language free category unitLabel) :
    collectionFree (focus.expected category) = true := by
  cases focus with
  | original bound expected source context => exact good.2
  | grouped bound components => rfl

/-- Rebasing changes only real source context and address fields. -/
def rebaseHead (outer : OneHoleContext) : SourceHead → SourceHead
  | .unit => .unit
  | .physical occurrence => .physical (occurrence.underContext outer)

private theorem rebaseHead_original (outer : OneHoleContext) (head : SourceHead) (unitLabel : String) :
    (rebaseHead outer head).original unitLabel = head.original unitLabel := by cases head <;> rfl

private theorem sourceHead?_underContext (outer : OneHoleContext) (occurrences : List SourceOccurrence) :
    sourceHead? (occurrences.map (SourceOccurrence.underContext outer)) =
      (sourceHead? occurrences).map (rebaseHead outer) := by
  cases occurrences with
  | nil => rfl
  | cons first rest => cases rest <;> rfl

private theorem rebased_head_readback {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} (good : Admissible language free bound expected source)
    (collectionless : collectionFree expected = true) (outer : OneHoleContext) {head : SourceHead}
    (found : sourceHead? ((normalizedOccurrences unitLabel source).map
      (SourceOccurrence.underContext outer)) = some head) :
    Admissible language free bound expected (head.original unitLabel) ∧
      normalForm (some unitLabel) (head.original unitLabel) = normalForm (some unitLabel) source ∧
      EquationEquiv base language source (head.original unitLabel) := by
  rw [sourceHead?_underContext] at found
  obtain ⟨original,selected,equal⟩ := Option.map_eq_some_iff.mp found
  subst head
  simpa only [rebaseHead_original] using sourceHead_readback laws base good collectionless selected

/-- A scalar head is an original typed source value or a declared virtual
unit. Its agreement uses actual source equations, independent of matching. -/
theorem Focus.scalar_readback {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {focus : Focus}
    (good : focus.Valid language free bag.category unitLabel) {head : SourceHead}
    (found : focus.scalar? unitLabel bag.category = some head) :
    Admissible language free focus.bound (focus.expected bag.category) (head.original unitLabel) ∧
      normalForm (some unitLabel) (head.original unitLabel) = normalForm (some unitLabel) (focus.value unitLabel) ∧
      EquationEquiv base language (focus.value unitLabel) (head.original unitLabel) := by
  cases focus with
  | original bound expected source outer =>
    by_cases role : expected = .base bag.category
    · simp only [Focus.scalar?,role,beq_self_eq_true,ite_true,Focus.components] at found
      exact rebased_head_readback laws base good.1 good.2 outer found
    · simp only [Focus.scalar?,beq_iff_eq,role,ite_false,Option.some.injEq] at found
      subst head
      exact ⟨good.1,rfl,.refl _⟩
  | grouped bound components =>
    cases components with
    | nil =>
      simp only [Focus.scalar?,sourceHead?,Option.some.injEq] at found
      subst head
      exact ⟨declared_unit_admissible laws base free bound,rfl,.refl _⟩
    | cons occurrence later =>
      cases later with
      | nil =>
        simp only [Focus.scalar?,sourceHead?,Option.some.injEq] at found
        subst head
        have component := good occurrence (by simp)
        refine ⟨component.originalGood,?_,?_⟩
        · change normalForm (some unitLabel) occurrence.original = normalForm (some unitLabel) occurrence.value
          rw [component.normalized,normalForm_stable laws base component.originalGood rfl]
        · change EquationEquiv base language occurrence.value occurrence.original
          rw [component.normalized]
          exact (source_equiv_normalForm laws base component.originalGood rfl).symm
      | cons next rest => cases found

/-- Every component passed to a recursive group is still an actual original
record with the same local type, normal value, and nonunit algebra leaf. -/
theorem Focus.components_valid {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {focus : Focus}
    (good : focus.Valid language free bag.category unitLabel)
    (role : focus.expected bag.category = .base bag.category)
    {occurrence : SourceOccurrence} (member : occurrence ∈ focus.components unitLabel) :
    ComponentValid language free focus.bound bag.category unitLabel occurrence := by
  cases focus with
  | original bound expected source outer =>
    change expected = .base bag.category at role
    subst expected
    obtain ⟨original,inside,rfl⟩ := List.mem_map.mp member
    have evidence := normalizedOccurrences_sound laws good.1 inside
    refine ⟨evidence.1,evidence.2.2.2.1,?_⟩
    change original.value ≠ .apply unitLabel [] ∧ ¬ IsBagNode original.value
    exact normalizedOccurrence_plain inside
  | grouped bound components => exact good occurrence member

#print axioms Focus.valid_value
#print axioms Focus.valid_collectionFree
#print axioms Focus.scalar_readback
#print axioms Focus.components_valid


/-- Equal normal values at a common typed role preserve an abstraction
parameter's actual representation. A base-sort bag cannot stand in an
arrow-typed slot. -/
theorem typed_normalForm_represents {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {expected : TypeExpr} {source target : Pattern}
    (sourceGood : Admissible language free bound expected source)
    (targetGood : Admissible language free bound expected target)
    (collectionless : collectionFree expected = true)
    (same : normalForm (some unitLabel) source = normalForm (some unitLabel) target) :
    Represents source target := by
  intro parameter represented
  cases parameter with
  | simple name type => trivial
  | abstractionNamed binder bodyName type =>
    obtain ⟨body,rfl⟩ := (matchesParameterRepresentation_abstractionNamed_iff binder bodyName type source).mp represented
    have nonbag : ¬ IsBagNode target := by
      rintro ⟨elements,rfl⟩
      have equation := (bag_typing laws.toBareBagPresentation
        (grammar_hasType (source := language) (target := {language with equations := []}) rfl targetGood.typed)
        collectionless).2.1
      have typed := sourceGood.typed
      cases typed
      cases equation
    have image : normalForm (some unitLabel) target = .lambda none (normalForm (some unitLabel) body) := by
      simpa only [normalForm] using same.symm
    obtain ⟨targetBody,shape,_⟩ := normalForm_lambda_inverse nonbag image
    exact (matchesParameterRepresentation_abstractionNamed_iff binder bodyName type target).mpr ⟨targetBody,shape⟩
  | multiAbstractionNamed binders bodyName type =>
    obtain ⟨arity,body,rfl⟩ := (matchesParameterRepresentation_multiAbstractionNamed_iff binders bodyName type source).mp represented
    have nonbag : ¬ IsBagNode target := by
      rintro ⟨elements,rfl⟩
      have equation := (bag_typing laws.toBareBagPresentation
        (grammar_hasType (source := language) (target := {language with equations := []}) rfl targetGood.typed)
        collectionless).2.1
      have typed := sourceGood.typed
      cases typed
      cases equation
    have image : normalForm (some unitLabel) target = .multiLambda arity [] (normalForm (some unitLabel) body) := by
      simpa only [normalForm] using same.symm
    obtain ⟨targetBody,shape,_⟩ := normalForm_multiLambda_inverse nonbag image
    exact (matchesParameterRepresentation_multiAbstractionNamed_iff binders bodyName type target).mpr ⟨arity,targetBody,shape⟩

/-- Erasing the retained physical records recovers exactly the focused
normal value, without changing their stored zippers. -/
theorem Focus.components_image {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {focus : Focus}
    (good : focus.Valid language free bag.category unitLabel)
    (role : focus.expected bag.category = .base bag.category) :
    normalForm (some unitLabel) (.collection .hashBag
      ((focus.components unitLabel).map SourceOccurrence.value) none) =
      normalForm (some unitLabel) (focus.value unitLabel) := by
  cases focus with
  | original bound expected source outer =>
    change expected = .base bag.category at role
    subst expected
    change normalForm (some unitLabel) (.collection .hashBag
      (((normalizedOccurrences unitLabel source).map (SourceOccurrence.underContext outer)).map SourceOccurrence.value) none) =
      normalForm (some unitLabel) source
    simp only [List.map_map,Function.comp_def,SourceOccurrence.underContext]
    rw [normalizedOccurrences_values]
    have comparisonGood := grammar_admissible (source := language)
      (target := {language with equations := []}) rfl good.1
    exact (normalForm_eq_of_equationEquiv laws.toBagTheory
      (normalized_view_equivalent (language := {language with equations := []}) laws base comparisonGood)).symm
  | grouped bound components =>
    have each : ∀ value ∈ components.map SourceOccurrence.value,
        Admissible language free bound (.base bag.category) value := by
      intro value member
      obtain ⟨occurrence,inside,rfl⟩ := List.mem_map.mp member
      have original := good occurrence inside
      rw [original.normalized]
      exact normalized_admissible laws base original.originalGood rfl
    have rowGood := (component_row_admissible laws each).1
    have comparisonGood := grammar_admissible (source := language)
      (target := {language with equations := []}) rfl rowGood
    exact normalForm_eq_of_equationEquiv laws.toBagTheory
      (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ (path_collapse (base := base) laws rfl comparisonGood))

/-- A group receives the same component evidence as its original focus;
its membership comes from the actual global allocation permutation. -/
theorem Focus.group_valid {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {focus : Focus}
    (good : focus.Valid language free bag.category unitLabel)
    (role : focus.expected bag.category = .base bag.category)
    {count : Nat} {groups : List (List SourceOccurrence)} {residual group : List SourceOccurrence}
    (allocation : (groups,residual) ∈ groupedOccurrences count (focus.components unitLabel))
    (inside : group ∈ groups) :
    (Focus.grouped focus.bound group).Valid language free bag.category unitLabel := by
  intro occurrence member
  exact Focus.components_valid laws good role
    (((mem_groupedOccurrences count).mp allocation).2.mem_iff.mp
      (List.mem_append_left _ (List.mem_flatten.mpr ⟨group,inside,member⟩)))

/-- Sorting the residual transports the physical account. It does not
change multiplicity or replace a record by an equal-valued occurrence. -/
theorem grouped_sorted_residual {count : Nat} {occurrences residual : List SourceOccurrence}
    {groups : List (List SourceOccurrence)}
    (allocation : (groups,residual) ∈ groupedOccurrences count occurrences) :
    (groups,sortOccurrences residual) ∈ groupedOccurrences count occurrences := by
  obtain ⟨lengths,account⟩ := (mem_groupedOccurrences count).mp allocation
  exact (mem_groupedOccurrences count).mpr ⟨lengths,
    ((sortOccurrences_perm residual).append_left groups.flatten).trans account⟩

/-- Every finite grouping of a valid focus is typed and has its exact
source normal value. The residual also keeps its collection-data type. -/
theorem Focus.grouping_readback {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free : FreeTypeContext} {focus : Focus}
    (good : focus.Valid language free bag.category unitLabel)
    (role : focus.expected bag.category = .base bag.category)
    {count : Nat} {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (allocation : (groups,residual) ∈ groupedOccurrences count (focus.components unitLabel)) :
    Admissible language free focus.bound (.base bag.category) (groupedView unitLabel groups residual) ∧
      normalForm (some unitLabel) (groupedView unitLabel groups residual) =
        normalForm (some unitLabel) (focus.value unitLabel) ∧
      Admissible language free focus.bound (.collection .hashBag (.base bag.category))
        (.collection .hashBag (residual.map SourceOccurrence.value) none) := by
  have account := (mem_groupedOccurrences count).mp allocation |>.2
  have all : ∀ occurrence ∈ groups.flatten ++ residual,
      ComponentValid language free focus.bound bag.category unitLabel occurrence := by
    intro occurrence member
    exact Focus.components_valid laws good role (account.mem_iff.mp member)
  have valueGood : ∀ occurrence ∈ groups.flatten ++ residual,
      Admissible language free focus.bound (.base bag.category) occurrence.value := by
    intro occurrence member
    have original := all occurrence member
    rw [original.normalized]
    exact normalized_admissible laws base original.originalGood rfl
  have termsGood : Admissible language free focus.bound (.base bag.category) (groupedView unitLabel groups residual) := by
    apply (component_row_admissible laws ?_).1
    intro term member
    rcases List.mem_append.mp member with grouped | retained
    · obtain ⟨group,inside,rfl⟩ := List.mem_map.mp grouped
      apply collapsed_row_admissible laws base
      intro value member
      obtain ⟨occurrence,inGroup,rfl⟩ := List.mem_map.mp member
      exact valueGood occurrence (List.mem_append_left _ (List.mem_flatten.mpr ⟨group,inside,inGroup⟩))
    · obtain ⟨occurrence,inside,rfl⟩ := List.mem_map.mp retained
      exact valueGood occurrence (List.mem_append_right _ inside)
  have contents : bagContents unitLabel
      (groups.map (fun group => collapse unitLabel (group.map SourceOccurrence.value)) ++ residual.map SourceOccurrence.value) =
      (groups.flatten ++ residual).map SourceOccurrence.value := by
    have mapped : (groups.map (List.map SourceOccurrence.value)).flatten = groups.flatten.map SourceOccurrence.value :=
      List.map_flatten.symm
    rw [List.map_append,← mapped]
    simpa only [List.map_map,Function.comp_def] using
      bagContents_grouped (groups := groups.map (List.map SourceOccurrence.value))
        (residual := residual.map SourceOccurrence.value) (by
          intro value member
          rw [mapped,← List.map_append] at member
          obtain ⟨occurrence,inside,rfl⟩ := List.mem_map.mp member
          exact (all occurrence inside).plain)
  have comparisonGood := grammar_admissible (source := language)
    (target := {language with equations := []}) rfl termsGood
  let terms := groups.map (fun group => collapse unitLabel (group.map SourceOccurrence.value)) ++ residual.map SourceOccurrence.value
  have spliced := path_splice (base := base) laws rfl terms [] comparisonGood
  have dropped := path_dropUnits (base := base) laws rfl (terms.flatMap splice) []
    (path_admissible laws spliced comparisonGood rfl)
  have flattened : Path base {language with equations := []} (groupedView unitLabel groups residual)
      (.collection .hashBag ((groups.flatten ++ residual).map SourceOccurrence.value) none) := by
    have combined := spliced.trans dropped
    change Path base {language with equations := []} (.collection .hashBag terms none)
      (.collection .hashBag (bagContents unitLabel terms) none) at combined
    simpa only [terms,groupedView,contents] using combined
  have image := normalForm_eq_of_equationEquiv laws.toBagTheory
    (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ flattened)
  have permuted : normalForm (some unitLabel)
      (.collection .hashBag ((groups.flatten ++ residual).map SourceOccurrence.value) none) =
      normalForm (some unitLabel) (.collection .hashBag ((focus.components unitLabel).map SourceOccurrence.value) none) := by
    rw [normalForm_bag,normalForm_bag]
    exact normalizeBag_perm _ ((account.map SourceOccurrence.value).map (normalForm (some unitLabel)))
  refine ⟨termsGood,image.trans (permuted.trans (Focus.components_image laws base good role)),?_⟩
  apply (component_row_admissible laws ?_).2
  intro value member
  obtain ⟨occurrence,inside,rfl⟩ := List.mem_map.mp member
  exact valueGood occurrence (List.mem_append_right _ inside)

#print axioms typed_normalForm_represents
#print axioms Focus.components_image
#print axioms Focus.group_valid
#print axioms grouped_sorted_residual
#print axioms Focus.grouping_readback


private theorem presentArguments_readback_of
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free schemaFree : FreeTypeContext} (schemaBound : List TypeExpr) (path : List Nat)
    (bound : List TypeExpr) (label : String) (outer : Option OneHoleContext) (originals : List Pattern)
    {schemas sources : List Pattern} {parameters : List TermParam} (index : Nat)
    (sourceTyped : ArgumentsHaveTypes language free bound sources parameters)
    (canonical : ∀ source ∈ sources,source.hasCanonicalBinderMetadata = true)
    (objects : ∀ source ∈ sources,isObjectPattern source = true)
    (parameterFree : ∀ parameter ∈ parameters,collectionFree (TermParam.typeExpr parameter) = true)
    (elementSound : ∀ schema ∈ schemas,∀ (localBound : List TypeExpr) (localPath : List Nat) (focus : Focus),
      focus.Valid language free bag.category unitLabel →
      ∀ spelling ∈ presentAt language free schemaFree bag.category unitLabel localBound localPath schema focus,
      Admissible language free focus.bound (focus.expected bag.category) spelling.target ∧
        normalForm (some unitLabel) spelling.target = normalForm (some unitLabel) (focus.value unitLabel))
    {result : List Pattern × List Frame}
    (member : result ∈ presentArguments language free schemaFree bag.category unitLabel
      schemaBound path bound label outer originals index schemas sources parameters) :
    ArgumentsHaveTypes language free bound result.1 parameters ∧
      (∀ target ∈ result.1,target.hasCanonicalBinderMetadata = true) ∧
      (∀ target ∈ result.1,isObjectPattern target = true) ∧
      result.1.map (normalForm (some unitLabel)) = sources.map (normalForm (some unitLabel)) := by
  induction schemas generalizing sources parameters index result with
  | nil =>
    cases sources with
    | cons first later => simp [presentArguments] at member
    | nil =>
      cases parameters with
      | cons first later => simp [presentArguments] at member
      | nil =>
        simp only [presentArguments,List.mem_singleton] at member
        subst result
        exact ⟨.nil,by simp,by simp,rfl⟩
  | cons schema schemas recurse =>
    cases sources with
    | nil => simp [presentArguments] at member
    | cons source sources =>
      cases parameters with
      | nil => simp [presentArguments] at member
      | cons parameter parameters =>
        cases sourceTyped with
        | cons representation expectedEquation headTyped tailTyped =>
          cases outer with
          | none => simp [presentArguments] at member
          | some context =>
            rw [presentArguments.eq_def] at member
            dsimp only at member
            rw [expectedEquation] at member
            obtain ⟨head,headMember,tailMember⟩ := List.mem_flatMap.mp member
            obtain ⟨later,laterMember,equal⟩ := List.mem_map.mp tailMember
            subst result
            have sourceGood : Admissible language free bound _ source :=
              ⟨headTyped,canonical source (by simp),objects source (by simp)⟩
            have headFree := collectionFree_parameterType (parameterFree parameter (by simp)) expectedEquation
            have headReadback := elementSound schema (by simp) schemaBound (path ++ [index])
              (.original bound _ source (context.comp (.apply label (originals.take index) .hole (originals.drop (index + 1)))))
              ⟨sourceGood,headFree⟩ head headMember
            have tailReadback := recurse (index := index + 1) tailTyped
              (fun source inside => canonical source (by simp [inside]))
              (fun source inside => objects source (by simp [inside]))
              (fun parameter inside => parameterFree parameter (by simp [inside]))
              (fun schema inside => elementSound schema (by simp [inside])) laterMember
            refine ⟨.cons (typed_normalForm_represents laws sourceGood headReadback.1 headFree headReadback.2.symm parameter representation)
              expectedEquation headReadback.1.typed tailReadback.1,?_,?_,?_⟩
            · intro target inside
              rcases List.mem_cons.mp inside with rfl | within
              · exact headReadback.1.canonical
              · exact tailReadback.2.1 target within
            · intro target inside
              rcases List.mem_cons.mp inside with rfl | within
              · exact headReadback.1.object
              · exact tailReadback.2.2.1 target within
            · simp only [List.map_cons]
              rw [headReadback.2,tailReadback.2.2.2]
              rfl

private theorem presentGroups_readback_of
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    {free schemaFree : FreeTypeContext} (schemaBound : List TypeExpr) (path : List Nat) (bound : List TypeExpr)
    {schemas : List Pattern} {groups : List (List SourceOccurrence)} (index : Nat)
    (groupsGood : ∀ group ∈ groups,(Focus.grouped bound group).Valid language free bag.category unitLabel)
    (elementSound : ∀ schema ∈ schemas,∀ (localBound : List TypeExpr) (localPath : List Nat) (focus : Focus),
      focus.Valid language free bag.category unitLabel →
      ∀ spelling ∈ presentAt language free schemaFree bag.category unitLabel localBound localPath schema focus,
      Admissible language free focus.bound (focus.expected bag.category) spelling.target ∧
        normalForm (some unitLabel) spelling.target = normalForm (some unitLabel) (focus.value unitLabel))
    {result : List Pattern × List Frame}
    (member : result ∈ presentGroups language free schemaFree bag.category unitLabel schemaBound path bound index schemas groups) :
    (∀ target ∈ result.1,Admissible language free bound (.base bag.category) target) ∧
      result.1.map (normalForm (some unitLabel)) =
        groups.map (fun group => normalForm (some unitLabel) (collapse unitLabel (group.map SourceOccurrence.value))) := by
  induction schemas generalizing groups index result with
  | nil =>
    cases groups with
    | cons first later => simp [presentGroups] at member
    | nil =>
      simp only [presentGroups,List.mem_singleton] at member
      subst result
      exact ⟨by simp,rfl⟩
  | cons schema schemas recurse =>
    cases groups with
    | nil => simp [presentGroups] at member
    | cons group groups =>
      simp only [presentGroups] at member
      obtain ⟨head,headMember,tailMember⟩ := List.mem_flatMap.mp member
      obtain ⟨later,laterMember,equal⟩ := List.mem_map.mp tailMember
      subst result
      have headReadback := elementSound schema (by simp) schemaBound (path ++ [index])
        (.grouped bound group) (groupsGood group (by simp)) head headMember
      have tailReadback := recurse (index := index + 1)
        (fun group inside => groupsGood group (by simp [inside]))
        (fun schema inside => elementSound schema (by simp [inside])) laterMember
      constructor
      · intro target inside
        rcases List.mem_cons.mp inside with rfl | within
        · exact headReadback.1
        · exact tailReadback.1 target within
      · simp only [List.map_cons]
        rw [headReadback.2,tailReadback.2]
        rfl


/-- Recursive presentation construction preserves the focused source type
and its exact existing normal value. This is a producer theorem; ordinary
matching, capture readback and operational coverage are separate boundaries. -/
theorem presentAt_readback {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : BasePremiseEvaluator) {free schemaFree : FreeTypeContext}
    (schemaBound : List TypeExpr) (path : List Nat) (schema : Pattern) {focus : Focus}
    (good : focus.Valid language free bag.category unitLabel) {spelling : Spelling}
    (member : spelling ∈ presentAt language free schemaFree bag.category unitLabel schemaBound path schema focus) :
    Admissible language free focus.bound (focus.expected bag.category) spelling.target ∧
      normalForm (some unitLabel) spelling.target = normalForm (some unitLabel) (focus.value unitLabel) := by
  induction schema using Pattern.inductionOn generalizing schemaBound path focus spelling with
  | hfvar identifier =>
    simp only [presentAt,List.mem_singleton] at member
    subst spelling
    exact ⟨normalized_admissible laws base (Focus.valid_value laws base good) (Focus.valid_collectionFree good),
      normalForm_stable laws base (Focus.valid_value laws base good) (Focus.valid_collectionFree good)⟩
  | hbvar index =>
    cases picked : focus.scalar? unitLabel bag.category with
    | none => simp [presentAt,picked] at member
    | some head =>
      cases shape : head.original unitLabel <;> try (solve | simp [presentAt,picked,shape] at member)
      case bvar actual =>
        by_cases equal : index = actual
        · simp [presentAt,picked,shape,equal] at member
          subst spelling
          have read := Focus.scalar_readback laws base good picked
          exact ⟨by simpa only [shape] using read.1,by simpa only [shape,normalForm] using read.2.1⟩
        · simp [presentAt,picked,shape,equal] at member
  | happly label schemas recurse =>
    cases picked : focus.scalar? unitLabel bag.category with
    | none => simp [presentAt,picked] at member
    | some head =>
      cases shape : head.original unitLabel <;> try (solve | simp [presentAt,picked,shape] at member)
      case apply actual sources =>
        by_cases labels : label = actual
        · subst label
          simp only [presentAt,picked,shape,beq_self_eq_true,ite_true] at member
          obtain ⟨⟨rule,index⟩,selected,within⟩ := List.mem_flatMap.mp member
          obtain ⟨children,childMember,equal⟩ := List.mem_map.mp within
          subst spelling
          obtain ⟨declared,labelEq,typeEq,notBare,sourceTyped,_⟩ := constructorChoices_sound selected
          have ruleMember := List.mem_of_getElem? declared
          have different : rule ≠ bag := by
            intro same
            apply notBare
            obtain ⟨identifier,bare⟩ := laws.bareShape
            exact ⟨identifier,.hashBag,.base bag.category,by simpa only [same] using bare⟩
          have read := Focus.scalar_readback laws base good picked
          have headGood := read.1
          have sourcesCanonical : ∀ source ∈ sources,source.hasCanonicalBinderMetadata = true :=
            hasCanonicalBinderMetadataList_iff.mp (by simpa only [shape,Pattern.hasCanonicalBinderMetadata] using headGood.canonical)
          have sourcesObject : ∀ source ∈ sources,isObjectPattern source = true :=
            isObjectPatternList_iff.mp (by simpa only [shape,isObjectPattern] using headGood.object)
          have childrenRead := presentArguments_readback_of laws schemaBound path focus.bound actual
            (headContext? head) sources 0 sourceTyped sourcesCanonical sourcesObject
            (fun parameter inside => laws.otherParameters rule ruleMember different parameter inside)
            (fun schema inside localBound localPath focus valid spelling published =>
              recurse schema inside localBound localPath valid published) childMember
          constructor
          · refine ⟨?_,?_,?_⟩
            · rw [typeEq]
              simpa only [labelEq] using HasType.constructor ruleMember notBare childrenRead.1
            · exact hasCanonicalBinderMetadataList_iff.mpr childrenRead.2.1
            · exact isObjectPatternList_iff.mpr childrenRead.2.2.1
          · change normalForm (some unitLabel) (.apply actual children.1) = _
            rw [normalForm_apply,childrenRead.2.2.2]
            simpa only [shape,normalForm_apply] using read.2.1
        · simp [presentAt,picked,shape,labels] at member
  | hlambda binder schemaBody recurse =>
    cases picked : focus.scalar? unitLabel bag.category with
    | none => simp [presentAt,picked] at member
    | some head =>
      cases role : focus.expected bag.category <;> try (solve | simp [presentAt,picked,role] at member)
      case arrow domain codomain =>
        cases shape : head.original unitLabel <;> try (solve | simp [presentAt,picked,role,shape] at member)
        case lambda sourceBinder sourceBody =>
          cases context : headContext? head with
          | none => simp [presentAt,picked,role,shape,context] at member
          | some outer =>
            simp only [presentAt,picked,role,shape,context] at member
            obtain ⟨body,bodyMember,equal⟩ := List.mem_map.mp member
            subst spelling
            have read := Focus.scalar_readback laws base good picked
            have typed := read.1.typed
            rw [shape,role] at typed
            cases typed with
            | lambda bodyTyped =>
              have canonical := read.1.canonical
              simp only [shape,Pattern.hasCanonicalBinderMetadata,Bool.and_eq_true] at canonical
              have object := read.1.object
              simp only [shape,isObjectPattern] at object
              have freeRole := Focus.valid_collectionFree good
              simp only [role,collectionFree,Bool.and_eq_true] at freeRole
              have bodyRead := recurse (domain :: schemaBound) (path ++ [0])
                (focus := .original (domain :: focus.bound) codomain sourceBody (outer.comp (.lambda sourceBinder .hole)))
                ⟨⟨bodyTyped,canonical.2,object⟩,freeRole.2⟩ bodyMember
              constructor
              · refine ⟨?_,?_,?_⟩
                · exact .lambda bodyRead.1.typed
                · simp only [Pattern.hasCanonicalBinderMetadata,Bool.and_eq_true]
                  exact ⟨canonical.1,bodyRead.1.canonical⟩
                · exact bodyRead.1.object
              · have inner := congrArg (Pattern.lambda sourceBinder) bodyRead.2
                have rebuilt : normalForm (some unitLabel) (.lambda sourceBinder body.target) =
                    normalForm (some unitLabel) (head.original unitLabel) := by
                  simpa only [normalForm,shape,Focus.value] using inner
                exact rebuilt.trans read.2.1
  | hmultiLambda arity binders schemaBody recurse =>
    cases picked : focus.scalar? unitLabel bag.category with
    | none => simp [presentAt,picked] at member
    | some head =>
      cases role : focus.expected bag.category <;> try (solve | simp [presentAt,picked,role] at member)
      case arrow domain codomain =>
        cases domain <;> try (solve | simp [presentAt,picked,role] at member)
        case multiBinder domain =>
          cases shape : head.original unitLabel <;> try (solve | simp [presentAt,picked,role,shape] at member)
          case multiLambda actual sourceBinders sourceBody =>
            cases context : headContext? head with
            | none => simp [presentAt,picked,role,shape,context] at member
            | some outer =>
              by_cases arities : arity = actual
              · subst actual
                simp only [presentAt,picked,role,shape,context,beq_self_eq_true,ite_true] at member
                obtain ⟨body,bodyMember,equal⟩ := List.mem_map.mp member
                subst spelling
                have read := Focus.scalar_readback laws base good picked
                have typed := read.1.typed
                rw [shape,role] at typed
                cases typed with
                | multiLambda bodyTyped =>
                  have canonical := read.1.canonical
                  simp only [shape,Pattern.hasCanonicalBinderMetadata,Bool.and_eq_true] at canonical
                  have object := read.1.object
                  simp only [shape,isObjectPattern] at object
                  have freeRole := Focus.valid_collectionFree good
                  simp only [role,collectionFree,Bool.and_eq_true] at freeRole
                  have bodyRead := recurse (List.replicate arity domain ++ schemaBound) (path ++ [0])
                    (focus := .original (List.replicate arity domain ++ focus.bound) codomain sourceBody
                      (outer.comp (.multiLambda arity sourceBinders .hole)))
                    ⟨⟨bodyTyped,canonical.2,object⟩,freeRole.2⟩ bodyMember
                  constructor
                  · refine ⟨?_,?_,?_⟩
                    · exact .multiLambda bodyRead.1.typed
                    · simp only [Pattern.hasCanonicalBinderMetadata,Bool.and_eq_true]
                      exact ⟨canonical.1,bodyRead.1.canonical⟩
                    · exact bodyRead.1.object
                  · have inner := congrArg (Pattern.multiLambda arity sourceBinders) bodyRead.2
                    have rebuilt : normalForm (some unitLabel) (.multiLambda arity sourceBinders body.target) =
                        normalForm (some unitLabel) (head.original unitLabel) := by
                      simpa only [normalForm,shape,Focus.value] using inner
                    exact rebuilt.trans read.2.1
              · simp [presentAt,picked,role,shape,context,arities] at member
  | hsubst body replacement bodyIH replacementIH => simp [presentAt] at member
  | hcollection kind schemas rest recurse =>
    cases kind with
    | vec => simp [presentAt] at member
    | hashSet => simp [presentAt] at member
    | hashBag =>
      by_cases role : focus.expected bag.category = .base bag.category
      · simp only [presentAt,beq_iff_eq,role,ite_true] at member
        obtain ⟨⟨groups,residual⟩,allocated,inside⟩ := List.mem_flatMap.mp member
        by_cases exhausted : rest.isNone && !(sortOccurrences residual).isEmpty
        · simp only [exhausted,ite_true,List.not_mem_nil] at inside
        · simp only [exhausted] at inside
          obtain ⟨children,childrenMember,equal⟩ := List.mem_map.mp inside
          subst spelling
          have sortedAllocation := grouped_sorted_residual allocated
          have viewRead := Focus.grouping_readback laws base good role sortedAllocation
          have childrenRead := presentGroups_readback_of schemaBound path focus.bound 0
            (fun group inside => Focus.group_valid laws good role sortedAllocation inside)
            (fun schema inside localBound localPath focus valid spelling published =>
              recurse schema inside localBound localPath valid published) childrenMember
          have account := (mem_groupedOccurrences schemas.length).mp sortedAllocation |>.2
          have residualGood : ∀ value ∈ (sortOccurrences residual).map SourceOccurrence.value,
              Admissible language free focus.bound (.base bag.category) value := by
            intro value member
            obtain ⟨occurrence,inside,rfl⟩ := List.mem_map.mp member
            have original := Focus.components_valid laws good role
              (account.mem_iff.mp (List.mem_append_right _ inside))
            rw [original.normalized]
            exact normalized_admissible laws base original.originalGood rfl
          constructor
          · rw [role]
            apply (component_row_admissible laws ?_).1
            intro target member
            rcases List.mem_append.mp member with child | residual
            · exact childrenRead.1 target child
            · exact residualGood target residual
          · have image : normalForm (some unitLabel) (.collection .hashBag
                (children.1 ++ (sortOccurrences residual).map SourceOccurrence.value) none) =
              normalForm (some unitLabel) (groupedView unitLabel groups (sortOccurrences residual)) := by
              change normalForm (some unitLabel) (.collection .hashBag
                (children.1 ++ (sortOccurrences residual).map SourceOccurrence.value) none) =
                  normalForm (some unitLabel) (.collection .hashBag
                    (groups.map (fun group => collapse unitLabel (group.map SourceOccurrence.value)) ++
                      (sortOccurrences residual).map SourceOccurrence.value) none)
              rw [normalForm_bag,normalForm_bag,List.map_append,List.map_append,childrenRead.2]
              simp only [List.map_map,Function.comp_def]
            exact image.trans viewRead.2.1
      · simp [presentAt,role] at member

#print axioms presentAt_readback


end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching ContextualStep DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Every finite presentation is related to its focused input by the
actual declared source equations. Retained authored rows and their source
alignment are explicit; normal-form equality alone is not source authority. -/
theorem presentAt_source_equivalent
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unitLabel) (Match.applyBindings bindings row.left) =
          normalForm (some unitLabel) (Match.applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free schemaFree : FreeTypeContext} {schemaBound : List TypeExpr} {path : List Nat}
    {schema : Pattern} {focus : Focus}
    (good : focus.Valid language free bag.category unitLabel) {spelling : Spelling}
    (member : spelling ∈ presentAt language free schemaFree bag.category unitLabel
      schemaBound path schema focus) :
    Admissible language free focus.bound (focus.expected bag.category) spelling.target ∧
      ReferenceStep.Equivalent relEnv language (focus.value unitLabel) spelling.target := by
  have readback := presentAt_readback laws (engineBasePremises relEnv) schemaBound path schema good member
  have sourceGood := Focus.valid_value laws (engineBasePremises relEnv) good
  exact ⟨readback.1, (reference_equivalent_iff_normalForm_eq laws rows aligned relEnv
    sourceGood readback.1 (Focus.valid_collectionFree good)).mpr readback.2.symm⟩

/-- A successful independent source match supplies the schema-side guard
for the producer's actual declaration scan. The two typing checks are
derived separately from their original source spines. -/
theorem constructorChoices_complete_of_source_match
    {language : LanguageDef} {free schemaFree : FreeTypeContext}
    {sourceBound schemaBound : List TypeExpr} {expected : TypeExpr} {label : String}
    {schemas sources matchedTargets : List Pattern} {declaration : GrammarRule} {index : Nat}
    (declared : language.terms[index]? = some declaration)
    (labelRead : declaration.label = label) (typeRead : expected = .base declaration.category)
    (ordinary : ¬ UsesBareCollection declaration)
    (sourceTyped : ArgumentsHaveTypes language free sourceBound sources declaration.params)
    (sourceObjects : isObjectPatternList sources = true)
    (schemaTyped : RestAwareTyping.ArgumentsHaveTypes language schemaFree schemaBound schemas declaration.params)
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth start : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final : ScopedRuleMatching.Assignment}
    (matched : GeneralScopedMatch.Arguments rule spec ambient site path depth initial start
      schemas matchedTargets final)
    (matchedObjects : isObjectPatternList matchedTargets = true) :
    (declaration, index) ∈ constructorChoices language free schemaFree sourceBound schemaBound
      expected label schemas sources := by
  have sourceChecked := checkArgumentsHaveTypes_complete_of_objects sourceTyped sourceObjects
  have schemaChecked := schemaArguments_checked_of_source_match schemaTyped matched matchedObjects
  have notBare : usesBareCollection? declaration = false := by
    apply Bool.eq_false_of_not_eq_true
    intro yes
    exact ordinary ((usesBareCollection?_eq_true_iff declaration).mp yes)
  unfold constructorChoices
  apply List.mem_filter.mpr
  refine ⟨List.mk_mem_zipIdx_iff_getElem?.mpr declared, ?_⟩
  change (declaration.label == label && expected == .base declaration.category &&
    !usesBareCollection? declaration &&
      checkArgumentsHaveTypes language free sourceBound sources declaration.params &&
      RestAwareTyping.checkSchemaArguments language schemaFree schemaBound schemas declaration.params) = true
  rw [labelRead, typeRead, notBare, sourceChecked, schemaChecked, beq_self_eq_true, beq_self_eq_true]
  rfl

#print axioms presentAt_source_equivalent
#print axioms constructorChoices_complete_of_source_match

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.ScopeBoundary

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching ContextualStep DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- The finite reference producer really reaches the complete numeric
presentation in the named-free example with both increasing binder spines. -/
theorem produced_normal_view :
    (presentAt sourceLanguage free schemaFree "Proc" "PZero" [] [] schema
      (.original [] proc source .hole)).map Spelling.target = [normalForm (some "PZero") source] := by
  cbv

/-- The generated whole spelling is typed, belongs to the actual authored
source class and is matched by the shared recovered-body comparison. The
earlier literal rejection is retained as a separating control. -/
theorem produced_view_has_source_and_match (relEnv : Engine.RelationEnv) :
    matchAt rule specification 0 .left [] 0 [] schema (normalForm (some "PZero") source) = [] ∧
      ∃ spelling,
        spelling ∈ presentAt sourceLanguage free schemaFree "Proc" "PZero" [] [] schema
          (.original [] proc source .hole) ∧
        Admissible sourceLanguage free [] proc spelling.target ∧
        ReferenceStep.Equivalent relEnv sourceLanguage source spelling.target ∧
        matchAtWith (normalBodyComparison "PZero") rule specification 0 .left [] 0 []
          schema spelling.target = [[("F", value)]] := by
  have targetMember : normalForm (some "PZero") source ∈
      (presentAt sourceLanguage free schemaFree "Proc" "PZero" [] [] schema
        (.original [] proc source .hole)).map Spelling.target := by
    rw [produced_normal_view]
    exact List.mem_singleton_self _
  obtain ⟨spelling, member, targetRead⟩ := List.mem_map.mp targetMember
  have good : Focus.Valid sourceLanguage free "Proc" "PZero" (.original [] proc source .hole) :=
    ⟨source_roles.2.2.2.1, rfl⟩
  have readback := presentAt_source_equivalent (language := sourceLanguage) source_roles.1
    (by intro row declared; cases declared) (by intro row declared; cases declared) relEnv good member
  refine ⟨scoped_matching_separator.2, spelling, member, readback.1, readback.2, ?_⟩
  rw [targetRead]
  exact (whole_normal_view_matching relEnv).2.2.2.1

#print axioms produced_normal_view
#print axioms produced_view_has_source_and_match

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.ScopeBoundary


namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- The real variable-spine check and ordered source typing earn every
sort field of partial-spine recovery. The caller's ambient suffix remains
independent, and the dependency list is neither truncated nor reordered. -/
theorem partial_spine_of_argument_types
    {language : LanguageDef} {free : FreeTypeContext}
    {dependencies locals ambient : List TypeExpr} {arguments : List Pattern} {indices : List Nat}
    (checked : variableSpine? locals.length arguments = some indices)
    (typed : List.Forall₂ (fun argument dependency =>
      HasType language free (locals ++ ambient) argument dependency) arguments dependencies) :
    RestAwareTyping.PartialSortedSpine dependencies locals indices := by
  have argumentsRead := CanonicalBags.variableSpine?_arguments checked
  have typedIndices : List.Forall₂ (fun index dependency =>
      HasType language free (locals ++ ambient) (.bvar index) dependency) indices dependencies := by
    rw [argumentsRead] at typed
    exact List.forall₂_map_left_iff.mp typed
  have count := typedIndices.length_eq
  have bounded := CanonicalBags.variableSpine?_lt checked
  refine ⟨count, bounded, ?_⟩
  intro index member
  have inIndices : indices.idxOf index < indices.length := List.idxOf_lt_length_of_mem member
  have inDependencies : indices.idxOf index < dependencies.length := by omega
  have atPosition := typedIndices.get inIndices inDependencies
  have indexTyped : HasType language free (locals ++ ambient) (.bvar index)
      dependencies[indices.idxOf index] := by
    simpa only [List.get_eq_getElem, List.getElem_idxOf] using atPosition
  have lookup : (locals ++ ambient)[index]? = some dependencies[indices.idxOf index] := by
    cases indexTyped with
    | bvar found => exact found
  rw [List.getElem?_append_left (bounded index member)] at lookup
  exact (List.getElem?_eq_getElem inDependencies).trans lookup.symm

/-- Successful checking of the actual occurrence arguments discharges the
same sorted inverse-spine premise used by the source capture theorems. -/
theorem partial_spine_of_checked_arguments
    {language : LanguageDef} {free : FreeTypeContext}
    {dependencies locals ambient : List TypeExpr} {arguments : List Pattern} {indices : List Nat}
    (spineChecked : variableSpine? locals.length arguments = some indices)
    (sortsChecked : RestAwareTyping.checkOccurrenceArguments language free locals ambient
      arguments dependencies = true) :
    RestAwareTyping.PartialSortedSpine dependencies locals indices :=
  partial_spine_of_argument_types spineChecked
    (List.Forall₂.imp (fun _ _ good => good.forget)
      (RestAwareTyping.checkOccurrenceArguments_sound sortsChecked))

/-- A stored declaration row supplies its own dependency context. The
partial-spine certificate is obtained from its actual checks and cannot
replace a missing or differently sorted metadata row. -/
theorem checked_row_partial_spine
    {language : LanguageDef} {free : FreeTypeContext} {locals ambient : List TypeExpr}
    {spec : RuleBindingSpec} {row : MetavariableOccurrence} {indices : List Nat}
    (checked : RestAwareTyping.checkStoredRowArguments language free locals ambient spec row = true)
    (spineChecked : variableSpine? locals.length row.arguments = some indices) :
    ∃ dependencies, dependencies? spec row.name = some dependencies ∧
      RestAwareTyping.PartialSortedSpine dependencies locals indices := by
  obtain ⟨dependencies, declared, typed⟩ := RestAwareTyping.checkStoredRowArguments_sound checked
  exact ⟨dependencies, declared, partial_spine_of_argument_types spineChecked
    (List.Forall₂.imp (fun _ _ good => good.forget) typed)⟩

#print axioms partial_spine_of_argument_types
#print axioms partial_spine_of_checked_arguments
#print axioms checked_row_partial_spine

open Mettapedia.OSLF.MeTTaIL.Match

/-- Recursive groups use the caller's original physical records. They are
not rebuilt by traversing a newly normalized representative. Every selected
source child and the exact terminal rest keep their independent ordinary
matching judgments and complete assignment flow. -/
theorem Focus.scoped_source_groups
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unitLabel) (applyBindings bindings row.left) =
          normalForm (some unitLabel) (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {focus : Focus} {elements schemas : List Pattern}
    (good : focus.Valid language free bag.category unitLabel)
    (role : focus.expected bag.category = .base bag.category)
    (representativeGood : Admissible language free focus.bound (.base bag.category)
      (.collection .hashBag elements none))
    (equivalent : ReferenceStep.Equivalent relEnv language (focus.value unitLabel)
      (.collection .hashBag elements none))
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth index : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final : ScopedRuleMatching.Assignment}
    {rest : Option String}
    (matched : GeneralScopedMatch.Bag rule spec ambient site path depth initial index
      schemas rest .hashBag elements final) :
    ∃ groups residual selected originalResidual middle,
      (groups, residual) ∈ groupedOccurrences schemas.length (focus.components unitLabel) ∧
      GeneralScopedMatch.Arguments rule spec ambient site path depth initial index schemas selected middle ∧
      GeneralScopedMatch.Bag rule spec ambient site path depth middle (index + schemas.length)
        [] rest .hashBag originalResidual final ∧
      groups.map (fun group => collapse unitLabel (group.map SourceOccurrence.value)) =
        selected.map (normalForm (some unitLabel)) ∧
      residual.map SourceOccurrence.value =
        bagContents unitLabel (originalResidual.map (normalForm (some unitLabel))) ∧
      List.Forall₂ (fun original group =>
        Admissible language free focus.bound (.base bag.category) original ∧
        (Focus.grouped focus.bound group).Valid language free bag.category unitLabel ∧
        ReferenceStep.Equivalent relEnv language original
          (Focus.value unitLabel (Focus.grouped focus.bound group))) selected groups ∧
      Admissible language free focus.bound (.collection .hashBag (.base bag.category))
        (.collection .hashBag originalResidual none) := by
  let base := ContextualStep.engineBasePremises relEnv
  obtain ⟨selected, originalResidual, middle, selectedLength, selectedAccount,
    selectedMatches, restRead⟩ := scoped_bag_selected_values matched
  have sourceGood := Focus.valid_value laws base good
  rw [role] at sourceGood
  have sourceImage := (reference_equivalent_iff_normalForm_eq laws rows aligned relEnv
    sourceGood representativeGood rfl).mp equivalent
  let valueGroups := selected.map (fun element => bagContents unitLabel [normalForm (some unitLabel) element])
  have groupContents : valueGroups.flatten =
      bagContents unitLabel (selected.map (normalForm (some unitLabel))) := by
    simpa only [valueGroups, List.flatMap] using bagContents_flatMap unitLabel selected
  have componentsPlain : ∀ value ∈ (focus.components unitLabel).map SourceOccurrence.value,
      value ≠ .apply unitLabel [] ∧ ¬ IsBagNode value := by
    intro value member
    obtain ⟨occurrence, inside, rfl⟩ := List.mem_map.mp member
    exact (Focus.components_valid laws good role inside).plain
  have fixed : ((focus.components unitLabel).map SourceOccurrence.value).map
      (normalForm (some unitLabel)) = (focus.components unitLabel).map SourceOccurrence.value := by
    have each : ∀ value ∈ (focus.components unitLabel).map SourceOccurrence.value,
        normalForm (some unitLabel) value = value := by
      intro value member
      obtain ⟨occurrence, inside, rfl⟩ := List.mem_map.mp member
      have original := Focus.components_valid laws good role inside
      rw [original.normalized]
      exact normalForm_stable laws base original.originalGood rfl
    simpa only [List.map_id] using (List.map_congr_left (g := id) each)
  have normalizedContents : PatternCode.sortPatterns ((focus.components unitLabel).map SourceOccurrence.value) =
      PatternCode.sortPatterns (bagContents unitLabel (elements.map (normalForm (some unitLabel)))) := by
    have same := (Focus.components_image laws base good role).trans sourceImage
    have contents := congrArg (fun term => bagContents unitLabel [term]) same
    simpa only [normalForm_bag_contents, fixed, bagContents_plain componentsPlain] using contents
  have sourceContents : (bagContents unitLabel (elements.map (normalForm (some unitLabel)))).Perm
      ((focus.components unitLabel).map SourceOccurrence.value) :=
    (sortPatterns_perm _).symm.trans
      (normalizedContents ▸ sortPatterns_perm _)
  have account := ((selectedAccount.map (normalForm (some unitLabel))).flatMap_right splice).filter
    (fun term => decide (term ≠ .apply unitLabel []))
  change (bagContents unitLabel ((selected ++ originalResidual).map (normalForm (some unitLabel)))).Perm
    (bagContents unitLabel (elements.map (normalForm (some unitLabel)))) at account
  rw [List.map_append, bagContents_append, ← groupContents] at account
  have account := account.trans sourceContents
  obtain ⟨groups, residual, allocated, groupValues, residualValues⟩ :=
    grouped_occurrences_of_values SourceOccurrence.value valueGroups
      (bagContents unitLabel (originalResidual.map (normalForm (some unitLabel)))) account
  have allocation : (groups, residual) ∈ groupedOccurrences schemas.length (focus.components unitLabel) := by
    have lengths : valueGroups.length = schemas.length := by
      simpa only [valueGroups, List.length_map] using selectedLength
    simpa only [lengths] using allocated
  have values : groups.map (fun group => collapse unitLabel (group.map SourceOccurrence.value)) =
      selected.map (normalForm (some unitLabel)) := by
    have collapsed := congrArg (List.map (collapse unitLabel)) groupValues
    simp only [valueGroups, List.map_map, Function.comp_def] at collapsed
    exact collapsed.trans (List.map_congr_left fun element _ =>
      collapse_contents (rootNormal_normalForm unitLabel element))
  have selectedGood : ∀ element ∈ selected,
      Admissible language free focus.bound (.base bag.category) element := by
    intro element member
    exact source_bag_element laws representativeGood
      (selectedAccount.mem_iff.mp (List.mem_append_left _ member))
  have residualGood : Admissible language free focus.bound (.collection .hashBag (.base bag.category))
      (.collection .hashBag originalResidual none) :=
    (component_row_admissible laws fun element member => source_bag_element laws representativeGood
      (selectedAccount.mem_iff.mp (List.mem_append_right _ member))).2
  have mappedPairs : List.Forall₂ (· = ·)
      (groups.map (fun group => collapse unitLabel (group.map SourceOccurrence.value)))
      (selected.map (normalForm (some unitLabel))) := by
    simpa only [List.forall₂_eq_eq_eq] using values
  have groupPairs : List.Forall₂ (fun group original =>
      collapse unitLabel (group.map SourceOccurrence.value) = normalForm (some unitLabel) original)
      groups selected := List.forall₂_map_right_iff.mp (List.forall₂_map_left_iff.mp mappedPairs)
  have typedPairs : List.Forall₂ (fun original group =>
      Admissible language free focus.bound (.base bag.category) original ∧
      collapse unitLabel (group.map SourceOccurrence.value) = normalForm (some unitLabel) original)
      selected groups := (List.forall₂_and_left selected groups).mpr ⟨selectedGood, groupPairs.flip⟩
  have sourcePairs : List.Forall₂ (fun original group =>
      Admissible language free focus.bound (.base bag.category) original ∧
      (Focus.grouped focus.bound group).Valid language free bag.category unitLabel ∧
      ReferenceStep.Equivalent relEnv language original
        (Focus.value unitLabel (Focus.grouped focus.bound group))) selected groups := by
    have withValid := (List.forall₂_and_left groups selected).mpr
      ⟨(fun group member => Focus.group_valid laws good role allocation member), typedPairs.flip⟩
    apply List.Forall₂.flip
    apply List.Forall₂.imp (h := withValid)
    intro group original pair
    refine ⟨pair.2.1, pair.1, ?_⟩
    change ReferenceStep.Equivalent relEnv language original
      (collapse unitLabel (group.map SourceOccurrence.value))
    rw [pair.2.2]
    exact (ReferenceStep.equivalent_iff_unconditional
      (fun row member => (rows row member).1) aligned).mp
      (source_equiv_normalForm laws base pair.2.1 rfl)
  exact ⟨groups, residual, selected, originalResidual, middle, allocation, selectedMatches,
    restRead, values, residualValues, sourcePairs, residualGood⟩

#print axioms Focus.scoped_source_groups

/-- A retained physical component is a leaf of the original algebra
traversal. Local typing and its normalized value alone do not express this
shape fact. The predicate adds no address or occurrence to the account. -/
def Focus.Physical : Focus → Prop
  | .original _ _ _ _ => True
  | .grouped _ components => ∀ occurrence ∈ components, ¬ IsBagNode occurrence.original

/-- Actual source traversal supplies the physical leaf property; recursive
grouping only transports the same records. -/
theorem Focus.components_physical {unitLabel : String} {focus : Focus}
    (physical : focus.Physical) {occurrence : SourceOccurrence}
    (member : occurrence ∈ focus.components unitLabel) : ¬ IsBagNode occurrence.original := by
  cases focus with
  | original bound expected source context =>
    obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
    have filtered := (sortOccurrences_perm (componentOccurrences unitLabel source)).mem_iff.mp inside
    exact (sourceOccurrences_leaf_value unitLabel source original (List.mem_filter.mp filtered).1).1
  | grouped bound components => exact physical occurrence member

/-- Conservation of the complete tagged allocation propagates physical
leaf evidence to every child, including empty virtual-unit groups. -/
theorem Focus.group_physical {unitLabel : String} {focus : Focus} (physical : focus.Physical)
    {count : Nat} {groups : List (List SourceOccurrence)} {residual group : List SourceOccurrence}
    (allocation : (groups, residual) ∈ groupedOccurrences count (focus.components unitLabel))
    (inside : group ∈ groups) : (Focus.grouped focus.bound group).Physical := by
  intro occurrence member
  exact Focus.components_physical physical
    (((mem_groupedOccurrences count).mp allocation).2.mem_iff.mp
      (List.mem_append_left _ (List.mem_flatten.mpr ⟨group, inside, member⟩)))

private theorem sourceHead_original_nonbag_of {unitLabel : String} {components : List SourceOccurrence}
    {head : SourceHead} (physical : ∀ occurrence ∈ components, ¬ IsBagNode occurrence.original)
    (found : sourceHead? components = some head) : ¬ IsBagNode (head.original unitLabel) := by
  cases components with
  | nil =>
    simp only [sourceHead?, Option.some.injEq] at found
    subst head
    simp [SourceHead.original, IsBagNode]
  | cons first later =>
    cases later with
    | nil =>
      simp only [sourceHead?, Option.some.injEq] at found
      subst head
      exact physical first (by simp)
    | cons second rest => cases found

/-- The scalar head selected from genuine source components is a genuine
nonbag leaf. At other roles the original typed boundary is preserved. -/
theorem Focus.scalar_nonbag {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {focus : Focus} (good : focus.Valid language free bag.category unitLabel)
    (physical : focus.Physical) {head : SourceHead}
    (found : focus.scalar? unitLabel bag.category = some head) : ¬ IsBagNode (head.original unitLabel) := by
  cases focus with
  | original bound expected source context =>
    by_cases role : expected = .base bag.category
    · simp only [Focus.scalar?, role, beq_self_eq_true, ite_true] at found
      exact sourceHead_original_nonbag_of (fun occurrence member =>
        Focus.components_physical (focus := .original bound expected source context) physical member) found
    · simp only [Focus.scalar?, beq_iff_eq, role, ite_false, Option.some.injEq] at found
      subst head
      change ¬ IsBagNode source
      rintro ⟨elements, equal⟩
      have typed : HasType {language with equations := []} free bound
          (.collection .hashBag elements none) expected := by
        rw [equal] at good
        exact good.1.typed.of_terms_subset (by intro row member; exact member)
      exact role (bag_typing laws.toBareBagPresentation typed good.2).2.1
  | grouped bound components =>
    exact sourceHead_original_nonbag_of physical found

/-- The shape fact is necessary: local component validity alone accepts a
manually fabricated singleton-bag record, which no real source traversal
would emit as a leaf. The finite constructor-free view correctly refuses
to read that record as a bound-variable leaf. -/
theorem Focus.local_validity_does_not_imply_physical
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (schemaFree : FreeTypeContext)
    (rule : RewriteRule) (spec : RuleBindingSpec) :
    let source := Pattern.collection .hashBag [.bvar 0] none
    let occurrence := SourceOccurrence.leaf unitLabel source
    let focus := Focus.grouped [.base bag.category] [occurrence]
    focus.Valid language FreeTypeContext.empty bag.category unitLabel ∧
      ¬ focus.Physical ∧
      Focus.value unitLabel focus = .bvar 0 ∧
      GeneralScopedMatch.Matches rule spec 1 .left [] 0 [] (.bvar 0) (.bvar 0) [] ∧
      presentAt language FreeTypeContext.empty schemaFree bag.category unitLabel [] [] (.bvar 0) focus = [] := by
  dsimp only
  have variableGood : Admissible language FreeTypeContext.empty [.base bag.category]
      (.base bag.category) (.bvar 0) := ⟨.bvar rfl, rfl, rfl⟩
  have originalGood := (component_row_admissible laws (components := [.bvar 0])
    (by intro value member; obtain rfl := List.mem_singleton.mp member; exact variableGood)).1
  have image : normalForm (some unitLabel) (.collection .hashBag [.bvar 0] none) = .bvar 0 := by
    simp [normalizeBag, bagContents, splice, collapse, PatternCode.sortPatterns, normalForm]
  refine ⟨?_, ?_, ?_, .bound, ?_⟩
  · intro occurrence member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨originalGood, rfl, by simp [SourceOccurrence.leaf, image, IsBagNode]⟩
  · intro physical
    exact physical (SourceOccurrence.leaf unitLabel (.collection .hashBag [.bvar 0] none))
      (by simp) ⟨[.bvar 0], rfl⟩
  · change collapse unitLabel [normalForm (some unitLabel) (.collection .hashBag [.bvar 0] none)] = .bvar 0
    exact image
  · rw [presentAt.eq_def]
    rfl

#print axioms Focus.components_physical
#print axioms Focus.group_physical
#print axioms Focus.scalar_nonbag
#print axioms Focus.local_validity_does_not_imply_physical

theorem Focus.components_fixed {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : ContextualStep.BasePremiseEvaluator) {free : FreeTypeContext} {focus : Focus}
    (good : focus.Valid language free bag.category unitLabel)
    (role : focus.expected bag.category = .base bag.category) :
    ((focus.components unitLabel).map SourceOccurrence.value).map (normalForm (some unitLabel)) =
      (focus.components unitLabel).map SourceOccurrence.value := by
  have each : ∀ value ∈ (focus.components unitLabel).map SourceOccurrence.value,
      normalForm (some unitLabel) value = value := by
    intro value member
    obtain ⟨occurrence, inside, rfl⟩ := List.mem_map.mp member
    have original := Focus.components_valid laws good role inside
    rw [original.normalized]
    exact normalForm_stable laws base original.originalGood rfl
  simpa only [List.map_id] using (List.map_congr_left (g := id) each)

/-- A scalar source class always has the retained scalar readback needed
for constructor and binder descent. A multi-component group cannot be
mistaken for a scalar, including when the group has repeated equal values. -/
theorem Focus.scalar_isSome_of_normal {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (base : ContextualStep.BasePremiseEvaluator) {free : FreeTypeContext} {focus : Focus}
    (good : focus.Valid language free bag.category unitLabel)
    (scalar : ¬ IsBagNode (normalForm (some unitLabel) (focus.value unitLabel))) :
    (focus.scalar? unitLabel bag.category).isSome = true := by
  cases focus with
  | original bound expected source context =>
    by_cases role : expected = .base bag.category
    · simp only [Focus.scalar?, role, beq_self_eq_true, ite_true, Focus.components]
      rw [sourceHead?_underContext]
      simpa only [Option.isSome_map, Focus.value] using sourceHead_isSome_of_scalar scalar
    · simp only [Focus.scalar?, beq_iff_eq, role, ite_false, Option.isSome_some]
  | grouped bound components =>
    cases components with
    | nil => rfl
    | cons first later =>
      cases later with
      | nil => rfl
      | cons second rest =>
        have fixed := Focus.components_fixed laws base good rfl
        dsimp only [Focus.components] at fixed
        have plain : ∀ value ∈ (first :: second :: rest).map SourceOccurrence.value,
            value ≠ .apply unitLabel [] ∧ ¬ IsBagNode value := by
          intro value member
          obtain ⟨occurrence, inside, rfl⟩ := List.mem_map.mp member
          exact (good occurrence inside).plain
        have many : 2 ≤ (bagContents unitLabel
            (((first :: second :: rest).map SourceOccurrence.value).map (normalForm (some unitLabel)))).length := by
          rw [fixed, bagContents_plain plain]
          simp only [List.length_map, List.length_cons]
          omega
        have bagShape := normalizeBag_isBagNode_of_length unitLabel
          (((first :: second :: rest).map SourceOccurrence.value).map (normalForm (some unitLabel))) many
        apply False.elim (scalar ?_)
        change IsBagNode (normalForm (some unitLabel)
          (.collection .hashBag ((first :: second :: rest).map SourceOccurrence.value) none))
        rw [normalForm_bag]
        exact bagShape

/-- A typed ordinary scalar representative is read back to an actual
original leaf or the declared virtual unit. This joins actual authored
equivalence and physical origin evidence before recursive matching. -/
theorem Focus.scalar_source_readback
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unitLabel) (applyBindings bindings row.left) =
          normalForm (some unitLabel) (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {focus : Focus} {representative : Pattern}
    (good : focus.Valid language free bag.category unitLabel) (physical : focus.Physical)
    (representativeGood : Admissible language free focus.bound (focus.expected bag.category) representative)
    (equivalent : ReferenceStep.Equivalent relEnv language (focus.value unitLabel) representative)
    (scalar : ¬ IsBagNode (normalForm (some unitLabel) representative)) :
    ∃ head,
      focus.scalar? unitLabel bag.category = some head ∧
      Admissible language free focus.bound (focus.expected bag.category) (head.original unitLabel) ∧
      ¬ IsBagNode (head.original unitLabel) ∧
      normalForm (some unitLabel) (head.original unitLabel) = normalForm (some unitLabel) representative ∧
      ReferenceStep.Equivalent relEnv language representative (head.original unitLabel) := by
  let base := ContextualStep.engineBasePremises relEnv
  have sourceGood := Focus.valid_value laws base good
  have same := (reference_equivalent_iff_normalForm_eq laws rows aligned relEnv
    sourceGood representativeGood (Focus.valid_collectionFree good)).mp equivalent
  have sourceScalar : ¬ IsBagNode (normalForm (some unitLabel) (focus.value unitLabel)) := by
    rw [same]
    exact scalar
  obtain ⟨head, found⟩ := Option.isSome_iff_exists.mp (Focus.scalar_isSome_of_normal laws base good sourceScalar)
  obtain ⟨headGood, image, headSource⟩ := Focus.scalar_readback laws base good found
  have sourceEquivalent := (ReferenceStep.equivalent_iff_unconditional
    (fun row member => (rows row member).1) aligned).mp headSource
  exact ⟨head, found, headGood, Focus.scalar_nonbag laws good physical found,
    image.trans same, .trans _ _ _ (.symm _ _ equivalent) sourceEquivalent⟩

#print axioms Focus.components_fixed
#print axioms Focus.scalar_isSome_of_normal
#print axioms Focus.scalar_source_readback

/-- Compose strict child induction hypotheses through the actual recursive
group producer and the shared compared argument matcher. This lemma is a
structural proof step, not a source profile or a firing certificate. -/
private theorem presentGroups_source_arguments_of
    {language : LanguageDef} (relEnv : Engine.RelationEnv)
    {free schemaFree : FreeTypeContext} {category unitLabel : String}
    {locals ambient : List TypeExpr} {path : List Nat}
    {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite}
    {schemas sources : List Pattern} {groups : List (List SourceOccurrence)}
    {index : Nat} {firstInitial secondInitial firstFinal : ScopedRuleMatching.Assignment}
    (schemaTyped : RestAwareTyping.ElementsHaveType language schemaFree locals schemas (.base category))
    (sourcePairs : List.Forall₂ (fun source group =>
      Admissible language free (locals ++ ambient) (.base category) source ∧
      (Focus.grouped (locals ++ ambient) group).Valid language free category unitLabel ∧
      (Focus.grouped (locals ++ ambient) group).Physical ∧
      ReferenceStep.Equivalent relEnv language source
        (Focus.value unitLabel (Focus.grouped (locals ++ ambient) group))) sources groups)
    (elementComplete : ∀ schema ∈ schemas, ∀ (source : Pattern) (group : List SourceOccurrence)
      (localPath : List Nat) (old current completed : ScopedRuleMatching.Assignment),
      (∃ offset, schemas[offset]? = some schema ∧ localPath = path ++ [index + offset]) →
      RestAwareTyping.HasType language schemaFree locals schema (.base category) →
      Admissible language free (locals ++ ambient) (.base category) source →
      (Focus.grouped (locals ++ ambient) group).Valid language free category unitLabel →
      (Focus.grouped (locals ++ ambient) group).Physical →
      ReferenceStep.Equivalent relEnv language source
        (Focus.value unitLabel (Focus.grouped (locals ++ ambient) group)) →
      GeneralScopedMatch.Matches rule spec ambient.length site localPath locals.length old schema source completed →
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) old =
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) current →
      List.Forall₂ (fun (first second : String × ContextualValue) =>
        first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
          first.2.ambient = second.2.ambient ∧
            ReferenceStep.Equivalent relEnv language first.2.body second.2.body) old current →
      ∃ spelling next,
        spelling ∈ presentAt language free schemaFree category unitLabel locals localPath schema
          (.grouped (locals ++ ambient) group) ∧
        next ∈ matchAtWith (normalBodyComparison unitLabel) rule spec ambient.length site localPath
          locals.length current schema spelling.target ∧
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) completed =
          CanonicalBags.mapAssignment (normalForm (some unitLabel)) next ∧
        List.Forall₂ (fun (first second : String × ContextualValue) =>
          first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
            first.2.ambient = second.2.ambient ∧
              ReferenceStep.Equivalent relEnv language first.2.body second.2.body) completed next)
    (matched : GeneralScopedMatch.Arguments rule spec ambient.length site path locals.length
      firstInitial index schemas sources firstFinal)
    (initialNormal : CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstInitial =
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondInitial)
    (initialSource : List.Forall₂ (fun (first second : String × ContextualValue) =>
      first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
        first.2.ambient = second.2.ambient ∧
          ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstInitial secondInitial) :
    ∃ children secondFinal,
      children ∈ presentGroups language free schemaFree category unitLabel locals path
        (locals ++ ambient) index schemas groups ∧
      secondFinal ∈ matchArgsAtWith (normalBodyComparison unitLabel) rule spec ambient.length site path
        locals.length secondInitial index schemas children.1 ∧
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstFinal =
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondFinal ∧
      List.Forall₂ (fun (first second : String × ContextualValue) =>
        first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
          first.2.ambient = second.2.ambient ∧
            ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstFinal secondFinal := by
  induction schemas generalizing sources groups index firstInitial secondInitial firstFinal with
  | nil =>
    cases matched
    cases sourcePairs
    refine ⟨([], []), secondInitial, ?_, ?_, initialNormal, initialSource⟩
    · rw [presentGroups.eq_def]
      exact .head _
    · simp only [matchArgsAtWith, List.mem_singleton]
  | cons schema schemas recurse =>
    cases schemaTyped with
    | cons headTyped tailTyped =>
      cases matched with
      | cons headMatch tailMatch =>
        cases sourcePairs with
        | cons headPair tailPairs =>
          obtain ⟨head, middle, headPresent, headMatched, middleNormal, middleSource⟩ :=
            elementComplete schema (by simp) _ _ (path ++ [index]) _ _ _
              ⟨0, rfl, by simp⟩ headTyped headPair.1 headPair.2.1 headPair.2.2.1 headPair.2.2.2 headMatch initialNormal initialSource
          obtain ⟨later, secondFinal, laterPresent, laterMatched, finalNormal, finalSource⟩ :=
            recurse tailTyped tailPairs (fun child inside source group localPath old current completed addressed =>
              elementComplete child (by simp [inside]) source group localPath old current completed (by
                obtain ⟨offset, childAt, pathAt⟩ := addressed
                refine ⟨offset + 1, by simpa only [List.getElem?_cons_succ] using childAt, ?_⟩
                simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using pathAt))
              tailMatch middleNormal middleSource
          refine ⟨(head.target :: later.1, head.frames ++ later.2), secondFinal, ?_, ?_,
            finalNormal, finalSource⟩
          · rw [presentGroups.eq_def]
            dsimp only
            exact List.mem_flatMap.mpr ⟨head, headPresent,
              List.mem_map.mpr ⟨later, laterPresent, rfl⟩⟩
          · rw [matchArgsAtWith.eq_def]
            dsimp only
            exact List.mem_flatMap.mpr ⟨middle, headMatched, laterMatched⟩

#print axioms presentGroups_source_arguments_of

/-- The finite producer covers a scoped capture from an independently
typed ordinary source match. The inverse spine is earned by the actual
ordered sort check, and comparison happens after recovering both bodies. -/
theorem presentAt_capture_covered
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unitLabel) (applyBindings bindings row.left) =
          normalForm (some unitLabel) (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free schemaFree : FreeTypeContext} {focus : Focus} {representative : Pattern}
    {locals ambient dependencies : List TypeExpr} {arguments : List Pattern} {indices : List Nat}
    {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite} {path : List Nat} {identifier : String}
    {firstInitial secondInitial firstFinal : ScopedRuleMatching.Assignment}
    (good : focus.Valid language free bag.category unitLabel)
    (context : focus.bound = locals ++ ambient)
    (representativeGood : Admissible language free (locals ++ ambient) (focus.expected bag.category) representative)
    (equivalent : ReferenceStep.Equivalent relEnv language (focus.value unitLabel) representative)
    (declared : dependencies? spec identifier = some dependencies)
    (atSite : arguments? rule spec identifier site path = some arguments)
    (spineChecked : variableSpine? locals.length arguments = some indices)
    (sortsChecked : RestAwareTyping.checkOccurrenceArguments language schemaFree locals ambient
      arguments dependencies = true)
    (matched : GeneralScopedMatch.Matches rule spec ambient.length site path locals.length
      firstInitial (.fvar identifier) representative firstFinal)
    (initialNormal : CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstInitial =
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondInitial)
    (initialSource : List.Forall₂ (fun (first second : String × ContextualValue) =>
      first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
        first.2.ambient = second.2.ambient ∧
          ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstInitial secondInitial) :
    ∃ spelling secondFinal,
      spelling ∈ presentAt language free schemaFree bag.category unitLabel locals path (.fvar identifier) focus ∧
      secondFinal ∈ matchAtWith (normalBodyComparison unitLabel) rule spec ambient.length site path
        locals.length secondInitial (.fvar identifier) spelling.target ∧
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstFinal =
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondFinal ∧
      List.Forall₂ (fun (first second : String × ContextualValue) =>
        first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
          first.2.ambient = second.2.ambient ∧
            ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstFinal secondFinal := by
  let base := ContextualStep.engineBasePremises relEnv
  have sourceGood := Focus.valid_value laws base good
  have collectionless := Focus.valid_collectionFree good
  have normalGood := normalized_admissible laws base sourceGood collectionless
  have normalization : ReferenceStep.Equivalent relEnv language (focus.value unitLabel)
      (normalForm (some unitLabel) (focus.value unitLabel)) :=
    (ReferenceStep.equivalent_iff_unconditional (fun row member => (rows row member).1) aligned).mp
      (source_equiv_normalForm laws base sourceGood collectionless)
  rw [context] at normalGood
  have equivalentNormal : ReferenceStep.Equivalent relEnv language representative
      (normalForm (some unitLabel) (focus.value unitLabel)) :=
    .trans _ _ _ (.symm _ _ equivalent) normalization
  cases matched with
  | capture captured =>
    obtain ⟨secondFinal, compared, finalNormal, finalSource⟩ := capture?_source_transport_assignments
      laws rows aligned relEnv declared atSite spineChecked
      (partial_spine_of_checked_arguments spineChecked sortsChecked)
      representativeGood normalGood (.inl collectionless) equivalentNormal initialNormal initialSource captured
    refine ⟨⟨normalForm (some unitLabel) (focus.value unitLabel),
      [⟨path, locals, focus, none, none⟩]⟩, secondFinal, ?_, ?_, finalNormal, finalSource⟩
    · rw [presentAt.eq_def]
      exact .head _
    · simp only [matchAtWith, compared, Option.toList_some, List.mem_singleton]

private theorem normalForm_bvar_inverse {unitLabel : String} {index : Nat} {source : Pattern}
    (nonbag : ¬ IsBagNode source) (image : normalForm (some unitLabel) source = .bvar index) :
    source = .bvar index := by
  cases source with
  | bvar actual => simpa only [normalForm] using image
  | collection kind elements rest =>
    cases kind <;> cases rest <;> simp_all [normalForm, IsBagNode]
  | _ => simp only [normalForm] at image; cases image

/-- Bound-variable descent is complete at a physical focus in the actual
source class. It cannot invent a leaf by erasing an unaccounted bag wrapper. -/
theorem presentAt_bound_covered
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unitLabel) (applyBindings bindings row.left) =
          normalForm (some unitLabel) (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free schemaFree : FreeTypeContext} {focus : Focus} {index : Nat}
    (locals : List TypeExpr) (path : List Nat)
    (good : focus.Valid language free bag.category unitLabel) (physical : focus.Physical)
    (representativeGood : Admissible language free focus.bound (focus.expected bag.category) (.bvar index))
    (equivalent : ReferenceStep.Equivalent relEnv language (focus.value unitLabel) (.bvar index)) :
    ∃ spelling,
      spelling ∈ presentAt language free schemaFree bag.category unitLabel locals path (.bvar index) focus ∧
      spelling.target = .bvar index := by
  obtain ⟨head, found, _, nonbag, image, _⟩ := Focus.scalar_source_readback laws rows aligned relEnv
    good physical representativeGood equivalent (by simp [normalForm, IsBagNode])
  have shape : head.original unitLabel = .bvar index :=
    normalForm_bvar_inverse nonbag image
  refine ⟨⟨.bvar index, [⟨path, locals, focus, none, none⟩]⟩, ?_, rfl⟩
  rw [presentAt.eq_def]
  dsimp only
  rw [found]
  dsimp only
  rw [shape]
  simp only [beq_self_eq_true, if_true, List.mem_singleton]

#print axioms presentAt_capture_covered
#print axioms presentAt_bound_covered

/-- The sorted physical residual preserves the outer collection-data
boundary of a rest capture. Its source agreement uses the actual authored
equation decision theorem on those two typed data endpoints. -/
theorem Focus.residual_source_readback
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unitLabel) (applyBindings bindings row.left) =
          normalForm (some unitLabel) (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {focus : Focus} {count : Nat}
    {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence} {originals : List Pattern}
    (good : focus.Valid language free bag.category unitLabel)
    (role : focus.expected bag.category = .base bag.category)
    (allocation : (groups, residual) ∈ groupedOccurrences count (focus.components unitLabel))
    (originalGood : Admissible language free focus.bound (.collection .hashBag (.base bag.category))
      (.collection .hashBag originals none))
    (values : residual.map SourceOccurrence.value = bagContents unitLabel (originals.map (normalForm (some unitLabel)))) :
    Admissible language free focus.bound (.collection .hashBag (.base bag.category))
        (.collection .hashBag ((sortOccurrences residual).map SourceOccurrence.value) none) ∧
      ReferenceStep.Equivalent relEnv language (.collection .hashBag originals none)
        (.collection .hashBag ((sortOccurrences residual).map SourceOccurrence.value) none) := by
  let base := ContextualStep.engineBasePremises relEnv
  have all : ∀ occurrence ∈ sortOccurrences residual,
      ComponentValid language free focus.bound bag.category unitLabel occurrence := by
    intro occurrence member
    exact Focus.components_valid laws good role
      (((mem_groupedOccurrences count).mp allocation).2.mem_iff.mp
        (List.mem_append_right _ ((sortOccurrences_perm residual).mem_iff.mp member)))
  have each : ∀ value ∈ (sortOccurrences residual).map SourceOccurrence.value,
      Admissible language free focus.bound (.base bag.category) value := by
    intro value member
    obtain ⟨occurrence, inside, rfl⟩ := List.mem_map.mp member
    have evidence := all occurrence inside
    rw [evidence.normalized]
    exact normalized_admissible laws base evidence.originalGood rfl
  have dataGood := (component_row_admissible laws each).2
  have fixed : ((sortOccurrences residual).map SourceOccurrence.value).map (normalForm (some unitLabel)) =
      (sortOccurrences residual).map SourceOccurrence.value := by
    have each : ∀ value ∈ (sortOccurrences residual).map SourceOccurrence.value,
        normalForm (some unitLabel) value = value := by
      intro value member
      obtain ⟨occurrence, inside, rfl⟩ := List.mem_map.mp member
      have evidence := all occurrence inside
      rw [evidence.normalized]
      exact normalForm_stable laws base evidence.originalGood rfl
    simpa only [List.map_id] using (List.map_congr_left (g := id) each)
  have plain : ∀ value ∈ (sortOccurrences residual).map SourceOccurrence.value,
      value ≠ .apply unitLabel [] ∧ ¬ IsBagNode value := by
    intro value member
    obtain ⟨occurrence, inside, rfl⟩ := List.mem_map.mp member
    exact (all occurrence inside).plain
  refine ⟨dataGood, (reference_equivalent_iff_normalForm_eq_data laws rows aligned relEnv
    originalGood dataGood).mpr ?_⟩
  rw [normalForm_bag, normalForm_bag, fixed]
  change collapse unitLabel (PatternCode.sortPatterns (bagContents unitLabel
      (originals.map (normalForm (some unitLabel))))) =
    collapse unitLabel (PatternCode.sortPatterns (bagContents unitLabel
      ((sortOccurrences residual).map SourceOccurrence.value)))
  rw [bagContents_plain plain, sortOccurrences_values, sortPatterns_idempotent, values]

/-- The existing compared bag matcher can choose an already matched front
row and then continue on precisely its residual. Every selected front index
is an actual list position, and assignment flow is unchanged. -/
private theorem matchBagAtWith_of_front_arguments
    {compare : String → Pattern → Pattern → Bool} {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient depth index : Nat} {site : RulePatternSite} {path : List Nat}
    {initial middle final : ScopedRuleMatching.Assignment} {schemas selected residual : List Pattern}
    {rest : Option String} {kind : CollType}
    (arguments : middle ∈ matchArgsAtWith compare rule spec ambient site path depth initial index schemas selected)
    (continued : final ∈ matchBagAtWith compare rule spec ambient site path depth middle
      (index + schemas.length) [] rest kind residual) :
    final ∈ matchBagAtWith compare rule spec ambient site path depth initial index schemas rest kind
      (selected ++ residual) := by
  induction schemas generalizing selected initial index with
  | nil =>
    cases selected with
    | nil =>
      simp only [matchArgsAtWith, List.mem_singleton] at arguments
      subst middle
      simpa only [List.length_nil, Nat.add_zero, List.nil_append] using continued
    | cons target targets => simp [matchArgsAtWith] at arguments
  | cons schema schemas recurse =>
    cases selected with
    | nil => simp [matchArgsAtWith] at arguments
    | cons target targets =>
      rw [matchArgsAtWith.eq_def] at arguments
      dsimp only at arguments
      obtain ⟨next, head, later⟩ := List.mem_flatMap.mp arguments
      have restMatched : final ∈ matchBagAtWith compare rule spec ambient site path depth next
          (index + 1) schemas rest kind (targets ++ residual) := by
        apply recurse later
        have shifted : index + 1 + schemas.length = index + (schema :: schemas).length := by
          simp only [List.length_cons]
          omega
        exact shifted.symm ▸ continued
      rw [matchBagAtWith.eq_def]
      dsimp only
      apply List.mem_flatMap.mpr
      refine ⟨(target, 0), ?_, ?_⟩
      · exact List.mk_mem_zipIdx_iff_getElem?.mpr rfl
      · exact List.mem_flatMap.mpr ⟨next, head, by simpa using restMatched⟩

#print axioms Focus.residual_source_readback
#print axioms matchBagAtWith_of_front_arguments

/-- The recursive bag case composes strict-child coverage with the real
scoped residual continuation. Physical allocation, collection-data rests,
and the full ordered assignment account are preserved together. -/
private theorem presentAt_bag_covered_of
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unitLabel) (applyBindings bindings row.left) =
          normalForm (some unitLabel) (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free schemaFree : FreeTypeContext} {focus : Focus} {locals ambient : List TypeExpr}
    {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite} {path : List Nat}
    {schemas elements : List Pattern} {rest : Option String}
    {firstInitial secondInitial firstFinal : ScopedRuleMatching.Assignment}
    (good : focus.Valid language free bag.category unitLabel) (physical : focus.Physical)
    (context : focus.bound = locals ++ ambient)
    (role : focus.expected bag.category = .base bag.category)
    (representativeGood : Admissible language free (locals ++ ambient) (.base bag.category)
      (.collection .hashBag elements none))
    (equivalent : ReferenceStep.Equivalent relEnv language (focus.value unitLabel)
      (.collection .hashBag elements none))
    (schemaTyped : RestAwareTyping.ElementsHaveType language schemaFree locals schemas (.base bag.category))
    (restSpines : ∀ identifier, rest = some identifier → ∃ dependencies arguments indices,
      dependencies? spec identifier = some dependencies ∧
      arguments? rule spec identifier site (path ++ [schemas.length]) = some arguments ∧
      variableSpine? locals.length arguments = some indices ∧
      RestAwareTyping.checkOccurrenceArguments language schemaFree locals ambient arguments dependencies = true)
    (elementComplete : ∀ schema ∈ schemas, ∀ (source : Pattern) (group : List SourceOccurrence)
      (localPath : List Nat) (old current completed : ScopedRuleMatching.Assignment),
      (∃ offset, schemas[offset]? = some schema ∧ localPath = path ++ [offset]) →
      RestAwareTyping.HasType language schemaFree locals schema (.base bag.category) →
      Admissible language free (locals ++ ambient) (.base bag.category) source →
      (Focus.grouped (locals ++ ambient) group).Valid language free bag.category unitLabel →
      (Focus.grouped (locals ++ ambient) group).Physical →
      ReferenceStep.Equivalent relEnv language source
        (Focus.value unitLabel (Focus.grouped (locals ++ ambient) group)) →
      GeneralScopedMatch.Matches rule spec ambient.length site localPath locals.length old schema source completed →
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) old =
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) current →
      List.Forall₂ (fun (first second : String × ContextualValue) =>
        first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
          first.2.ambient = second.2.ambient ∧
            ReferenceStep.Equivalent relEnv language first.2.body second.2.body) old current →
      ∃ spelling next,
        spelling ∈ presentAt language free schemaFree bag.category unitLabel locals localPath schema
          (.grouped (locals ++ ambient) group) ∧
        next ∈ matchAtWith (normalBodyComparison unitLabel) rule spec ambient.length site localPath
          locals.length current schema spelling.target ∧
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) completed =
          CanonicalBags.mapAssignment (normalForm (some unitLabel)) next ∧
        List.Forall₂ (fun (first second : String × ContextualValue) =>
          first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
            first.2.ambient = second.2.ambient ∧
              ReferenceStep.Equivalent relEnv language first.2.body second.2.body) completed next)
    (matched : GeneralScopedMatch.Bag rule spec ambient.length site path locals.length firstInitial 0
      schemas rest .hashBag elements firstFinal)
    (initialNormal : CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstInitial =
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondInitial)
    (initialSource : List.Forall₂ (fun (first second : String × ContextualValue) =>
      first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
        first.2.ambient = second.2.ambient ∧
          ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstInitial secondInitial) :
    ∃ spelling secondFinal,
      spelling ∈ presentAt language free schemaFree bag.category unitLabel locals path
        (.collection .hashBag schemas rest) focus ∧
      secondFinal ∈ matchAtWith (normalBodyComparison unitLabel) rule spec ambient.length site path
        locals.length secondInitial (.collection .hashBag schemas rest) spelling.target ∧
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstFinal =
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondFinal ∧
      List.Forall₂ (fun (first second : String × ContextualValue) =>
        first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
          first.2.ambient = second.2.ambient ∧
            ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstFinal secondFinal := by
  have representativeGoodAtFocus : Admissible language free focus.bound (.base bag.category)
      (.collection .hashBag elements none) := by simpa only [context] using representativeGood
  obtain ⟨groups, residual, selected, originalResidual, middle, allocation, selectedMatches,
      restRead, _, residualValues, sourcePairs, originalResidualGood⟩ := Focus.scoped_source_groups
    laws rows aligned relEnv good role representativeGoodAtFocus equivalent matched
  have paired : List.Forall₂ (fun source group =>
      Admissible language free (locals ++ ambient) (.base bag.category) source ∧
      (Focus.grouped (locals ++ ambient) group).Valid language free bag.category unitLabel ∧
      (Focus.grouped (locals ++ ambient) group).Physical ∧
      ReferenceStep.Equivalent relEnv language source
        (Focus.value unitLabel (Focus.grouped (locals ++ ambient) group))) selected groups := by
    have withPhysical := (List.forall₂_and_left groups selected).mpr
      ⟨(fun group inside => Focus.group_physical physical allocation inside), sourcePairs.flip⟩
    apply List.Forall₂.flip
    apply List.Forall₂.imp (h := withPhysical)
    intro group source pair
    change Admissible language free (locals ++ ambient) (.base bag.category) source ∧
      (Focus.grouped (locals ++ ambient) group).Valid language free bag.category unitLabel ∧
      (Focus.grouped (locals ++ ambient) group).Physical ∧
      ReferenceStep.Equivalent relEnv language source (Focus.value unitLabel (Focus.grouped (locals ++ ambient) group))
    simpa only [context] using And.intro pair.2.1
      (And.intro pair.2.2.1 (And.intro pair.1 pair.2.2.2))
  obtain ⟨children, secondMiddle, childrenPresent, childrenMatched, middleNormal, middleSource⟩ :=
    presentGroups_source_arguments_of relEnv schemaTyped paired
      (fun schema inside source group localPath old current completed addressed =>
        elementComplete schema inside source group localPath old current completed (by
          simpa only [Nat.zero_add] using addressed)) selectedMatches initialNormal initialSource
  have continuation : ∃ secondFinal,
      (rest.isNone && !(sortOccurrences residual).isEmpty) = false ∧
      secondFinal ∈ matchBagAtWith (normalBodyComparison unitLabel) rule spec ambient.length site path
        locals.length secondMiddle (0 + schemas.length) [] rest .hashBag
          ((sortOccurrences residual).map SourceOccurrence.value) ∧
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstFinal =
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondFinal ∧
      List.Forall₂ (fun (first second : String × ContextualValue) =>
        first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
          first.2.ambient = second.2.ambient ∧
            ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstFinal secondFinal := by
    cases restRead with
    | nil =>
      have emptyValues : residual.map SourceOccurrence.value = [] := by
        simpa only [List.map_nil, bagContents, List.flatMap_nil, List.filter_nil] using residualValues
      have empty : residual = [] := List.map_eq_nil_iff.mp emptyValues
      refine ⟨secondMiddle, ?_, ?_, middleNormal, middleSource⟩
      · simp [empty, sortOccurrences]
      · simp [empty, sortOccurrences, matchBagAtWith]
    | rest captured =>
      rename_i identifier
      obtain ⟨dependencies, arguments, indices, declared, atSite, spineChecked, sortsChecked⟩ :=
        restSpines identifier rfl
      obtain ⟨dataGood, dataEquivalent⟩ := Focus.residual_source_readback laws rows aligned relEnv
        good role allocation originalResidualGood residualValues
      rw [context] at dataGood originalResidualGood
      have ordinaryCapture : capture? rule spec ambient.length locals.length site
          (path ++ [schemas.length]) middle identifier (.collection .hashBag originalResidual none) =
          some firstFinal := by simpa only [Nat.zero_add, captureRest?] using captured
      obtain ⟨secondFinal, compared, finalNormal, finalSource⟩ := capture?_source_transport_assignments
        laws rows aligned relEnv declared atSite spineChecked
        (partial_spine_of_checked_arguments spineChecked sortsChecked)
        originalResidualGood dataGood (.inr rfl) dataEquivalent middleNormal middleSource ordinaryCapture
      refine ⟨secondFinal, rfl, ?_, finalNormal, finalSource⟩
      simp only [matchBagAtWith, Nat.zero_add, captureRestWith?, compared,
        Option.toList_some, List.mem_singleton]
  obtain ⟨secondFinal, guard, continued, finalNormal, finalSource⟩ := continuation
  refine ⟨⟨.collection .hashBag (children.1 ++ (sortOccurrences residual).map SourceOccurrence.value) none,
    ⟨path, locals, focus, none, some (groups, sortOccurrences residual)⟩ :: children.2⟩,
    secondFinal, ?_, ?_, finalNormal, finalSource⟩
  · rw [presentAt.eq_def]
    dsimp only
    rw [role, beq_self_eq_true]
    apply List.mem_flatMap.mpr
    refine ⟨(groups, residual), allocation, ?_⟩
    dsimp only
    rw [guard]
    rw [context]
    exact List.mem_map.mpr ⟨children, childrenPresent, rfl⟩
  · rw [matchAtWith.eq_def]
    dsimp only
    exact matchBagAtWith_of_front_arguments childrenMatched continued

#print axioms presentAt_bag_covered_of

/-- Binder coverage transports the actual typed source head, local sort
prefix and original zipper together. Only the strict body induction
hypothesis is used; no binder-free or dependency-count restriction is added. -/
private theorem presentAt_binder_covered_of
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unitLabel) (applyBindings bindings row.left) =
          normalForm (some unitLabel) (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free schemaFree : FreeTypeContext} {focus : Focus} {locals ambient : List TypeExpr}
    {domain codomain : TypeExpr} {schemaBody representativeBody : Pattern}
    {schemaBinder actualBinder : Option String}
    {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite} {path : List Nat}
    {firstInitial secondInitial firstFinal : ScopedRuleMatching.Assignment}
    (good : focus.Valid language free bag.category unitLabel) (physical : focus.Physical)
    (context : focus.bound = locals ++ ambient)
    (role : focus.expected bag.category = .arrow domain codomain)
    (representativeGood : Admissible language free (locals ++ ambient) (.arrow domain codomain)
      (.lambda actualBinder representativeBody))
    (equivalent : ReferenceStep.Equivalent relEnv language (focus.value unitLabel)
      (.lambda actualBinder representativeBody))
    (schemaTyped : RestAwareTyping.HasType language schemaFree (domain :: locals) schemaBody codomain)
    (bodyComplete : ∀ (child : Focus),
      child.Valid language free bag.category unitLabel → child.Physical →
      child.bound = (domain :: locals) ++ ambient → child.expected bag.category = codomain →
      Admissible language free ((domain :: locals) ++ ambient) codomain representativeBody →
      ReferenceStep.Equivalent relEnv language (child.value unitLabel) representativeBody →
      GeneralScopedMatch.Matches rule spec ambient.length site (path ++ [0])
        (domain :: locals).length firstInitial schemaBody representativeBody firstFinal →
      RestAwareTyping.HasType language schemaFree (domain :: locals) schemaBody codomain →
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstInitial =
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondInitial →
      List.Forall₂ (fun (first second : String × ContextualValue) =>
        first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
          first.2.ambient = second.2.ambient ∧
            ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstInitial secondInitial →
      ∃ spelling next,
        spelling ∈ presentAt language free schemaFree bag.category unitLabel (domain :: locals) (path ++ [0]) schemaBody child ∧
        next ∈ matchAtWith (normalBodyComparison unitLabel) rule spec ambient.length site (path ++ [0])
          (domain :: locals).length secondInitial schemaBody spelling.target ∧
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstFinal =
          CanonicalBags.mapAssignment (normalForm (some unitLabel)) next ∧
        List.Forall₂ (fun (first second : String × ContextualValue) =>
          first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
            first.2.ambient = second.2.ambient ∧
              ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstFinal next)
    (matched : GeneralScopedMatch.Matches rule spec ambient.length site path locals.length firstInitial
      (.lambda schemaBinder schemaBody) (.lambda actualBinder representativeBody) firstFinal)
    (initialNormal : CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstInitial =
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondInitial)
    (initialSource : List.Forall₂ (fun (first second : String × ContextualValue) =>
      first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
        first.2.ambient = second.2.ambient ∧
          ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstInitial secondInitial) :
    ∃ spelling secondFinal,
      spelling ∈ presentAt language free schemaFree bag.category unitLabel locals path
        (.lambda schemaBinder schemaBody) focus ∧
      secondFinal ∈ matchAtWith (normalBodyComparison unitLabel) rule spec ambient.length site path
        locals.length secondInitial (.lambda schemaBinder schemaBody) spelling.target ∧
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstFinal =
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondFinal ∧
      List.Forall₂ (fun (first second : String × ContextualValue) =>
        first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
          first.2.ambient = second.2.ambient ∧
            ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstFinal secondFinal := by
  have representativeGoodAtFocus : Admissible language free focus.bound (focus.expected bag.category)
      (.lambda actualBinder representativeBody) := by simpa only [context, role] using representativeGood
  obtain ⟨head, found, headGood, nonbag, image, _⟩ := Focus.scalar_source_readback laws rows aligned relEnv
    good physical representativeGoodAtFocus equivalent (by simp [normalForm, IsBagNode])
  obtain ⟨sourceBody, shape, bodyImage⟩ := normalForm_lambda_inverse nonbag image
  obtain ⟨outer, outerRead⟩ : ∃ outer, headContext? head = some outer := by
    cases head with
    | unit => simp [SourceHead.original] at shape
    | physical occurrence => exact ⟨occurrence.context, rfl⟩
  have sourceBodyGood : Admissible language free (domain :: focus.bound) codomain sourceBody := by
    have typed := headGood.typed
    rw [shape, role] at typed
    cases typed with
    | lambda typed =>
      refine ⟨typed, ?_, ?_⟩
      · have canonical := headGood.canonical
        rw [shape] at canonical
        exact (Bool.and_eq_true_iff.mp canonical).2
      · simpa only [shape, isObjectPattern] using headGood.object
  have representativeBodyGood : Admissible language free ((domain :: locals) ++ ambient)
      codomain representativeBody := by
    have typed := representativeGood.typed
    cases typed with
    | lambda typed =>
      refine ⟨typed, ?_, ?_⟩
      · exact (Bool.and_eq_true_iff.mp representativeGood.canonical).2
      · simpa only [isObjectPattern] using representativeGood.object
  have freeRole := Focus.valid_collectionFree good
  rw [role] at freeRole
  have codomainFree : collectionFree codomain = true := (Bool.and_eq_true_iff.mp freeRole).2
  have bodyEquivalent : ReferenceStep.Equivalent relEnv language sourceBody representativeBody := by
    have sourceGoodAtBody : Admissible language free ((domain :: locals) ++ ambient) codomain sourceBody := by
      simpa only [context, List.cons_append] using sourceBodyGood
    exact (reference_equivalent_iff_normalForm_eq laws rows aligned relEnv sourceGoodAtBody
      representativeBodyGood codomainFree).mpr bodyImage
  let child : Focus := .original (domain :: focus.bound) codomain sourceBody
    (outer.comp (.lambda actualBinder .hole))
  have childGood : child.Valid language free bag.category unitLabel := ⟨sourceBodyGood, codomainFree⟩
  have childContext : child.bound = (domain :: locals) ++ ambient := by
    change domain :: focus.bound = (domain :: locals) ++ ambient
    rw [context, List.cons_append]
  cases matched with
  | binder bodyMatched =>
    obtain ⟨body, secondFinal, bodyPresent, bodyChecked, finalNormal, finalSource⟩ :=
      bodyComplete child childGood trivial childContext rfl representativeBodyGood bodyEquivalent
        (by simpa only [List.length_cons] using bodyMatched) schemaTyped initialNormal initialSource
    refine ⟨⟨.lambda actualBinder body.target, ⟨path, locals, focus, none, none⟩ :: body.frames⟩,
      secondFinal, ?_, ?_, finalNormal, finalSource⟩
    · rw [presentAt.eq_def]
      dsimp only
      rw [found, role]
      dsimp only
      rw [shape, outerRead]
      dsimp only
      exact List.mem_map.mpr ⟨body, bodyPresent, rfl⟩
    · simpa only [matchAtWith, List.length_cons] using bodyChecked

#print axioms presentAt_binder_covered_of

/-- Multi-binder descent keeps the entire declared arity, local sort prefix,
original source context and capture account through the strict body step. -/
private theorem presentAt_binders_covered_of
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unitLabel) (applyBindings bindings row.left) =
          normalForm (some unitLabel) (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free schemaFree : FreeTypeContext} {focus : Focus} {locals ambient : List TypeExpr}
    {domain codomain : TypeExpr} {arity : Nat} {schemaBody representativeBody : Pattern}
    {schemaBinders actualBinders : List String}
    {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite} {path : List Nat}
    {firstInitial secondInitial firstFinal : ScopedRuleMatching.Assignment}
    (good : focus.Valid language free bag.category unitLabel) (physical : focus.Physical)
    (context : focus.bound = locals ++ ambient)
    (role : focus.expected bag.category = .arrow (.multiBinder domain) codomain)
    (representativeGood : Admissible language free (locals ++ ambient) (.arrow (.multiBinder domain) codomain)
      (.multiLambda arity actualBinders representativeBody))
    (equivalent : ReferenceStep.Equivalent relEnv language (focus.value unitLabel)
      (.multiLambda arity actualBinders representativeBody))
    (schemaTyped : RestAwareTyping.HasType language schemaFree (List.replicate arity domain ++ locals) schemaBody codomain)
    (bodyComplete : ∀ (child : Focus),
      child.Valid language free bag.category unitLabel → child.Physical →
      child.bound = (List.replicate arity domain ++ locals) ++ ambient → child.expected bag.category = codomain →
      Admissible language free ((List.replicate arity domain ++ locals) ++ ambient) codomain representativeBody →
      ReferenceStep.Equivalent relEnv language (child.value unitLabel) representativeBody →
      GeneralScopedMatch.Matches rule spec ambient.length site (path ++ [0])
        (List.replicate arity domain ++ locals).length firstInitial schemaBody representativeBody firstFinal →
      RestAwareTyping.HasType language schemaFree (List.replicate arity domain ++ locals) schemaBody codomain →
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstInitial =
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondInitial →
      List.Forall₂ (fun (first second : String × ContextualValue) =>
        first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
          first.2.ambient = second.2.ambient ∧
            ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstInitial secondInitial →
      ∃ spelling next,
        spelling ∈ presentAt language free schemaFree bag.category unitLabel (List.replicate arity domain ++ locals) (path ++ [0]) schemaBody child ∧
        next ∈ matchAtWith (normalBodyComparison unitLabel) rule spec ambient.length site (path ++ [0])
          (List.replicate arity domain ++ locals).length secondInitial schemaBody spelling.target ∧
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstFinal =
          CanonicalBags.mapAssignment (normalForm (some unitLabel)) next ∧
        List.Forall₂ (fun (first second : String × ContextualValue) =>
          first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
            first.2.ambient = second.2.ambient ∧
              ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstFinal next)
    (matched : GeneralScopedMatch.Matches rule spec ambient.length site path locals.length firstInitial
      (.multiLambda arity schemaBinders schemaBody) (.multiLambda arity actualBinders representativeBody) firstFinal)
    (initialNormal : CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstInitial =
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondInitial)
    (initialSource : List.Forall₂ (fun (first second : String × ContextualValue) =>
      first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
        first.2.ambient = second.2.ambient ∧
          ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstInitial secondInitial) :
    ∃ spelling secondFinal,
      spelling ∈ presentAt language free schemaFree bag.category unitLabel locals path
        (.multiLambda arity schemaBinders schemaBody) focus ∧
      secondFinal ∈ matchAtWith (normalBodyComparison unitLabel) rule spec ambient.length site path
        locals.length secondInitial (.multiLambda arity schemaBinders schemaBody) spelling.target ∧
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstFinal =
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondFinal ∧
      List.Forall₂ (fun (first second : String × ContextualValue) =>
        first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
          first.2.ambient = second.2.ambient ∧
            ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstFinal secondFinal := by
  have representativeGoodAtFocus : Admissible language free focus.bound (focus.expected bag.category)
      (.multiLambda arity actualBinders representativeBody) := by simpa only [context, role] using representativeGood
  obtain ⟨head, found, headGood, nonbag, image, _⟩ := Focus.scalar_source_readback laws rows aligned relEnv
    good physical representativeGoodAtFocus equivalent (by simp [normalForm, IsBagNode])
  obtain ⟨sourceBody, shape, bodyImage⟩ := normalForm_multiLambda_inverse nonbag image
  obtain ⟨outer, outerRead⟩ : ∃ outer, headContext? head = some outer := by
    cases head with
    | unit => simp [SourceHead.original] at shape
    | physical occurrence => exact ⟨occurrence.context, rfl⟩
  have sourceBodyGood : Admissible language free (List.replicate arity domain ++ focus.bound) codomain sourceBody := by
    have typed := headGood.typed
    rw [shape, role] at typed
    cases typed with
    | multiLambda typed =>
      refine ⟨typed, ?_, ?_⟩
      · have canonical := headGood.canonical
        rw [shape] at canonical
        exact (Bool.and_eq_true_iff.mp canonical).2
      · simpa only [shape, isObjectPattern] using headGood.object
  have representativeBodyGood : Admissible language free ((List.replicate arity domain ++ locals) ++ ambient)
      codomain representativeBody := by
    have typed := representativeGood.typed
    cases typed with
    | multiLambda typed =>
      refine ⟨by simpa only [List.append_assoc] using typed, ?_, ?_⟩
      · exact (Bool.and_eq_true_iff.mp representativeGood.canonical).2
      · simpa only [isObjectPattern] using representativeGood.object
  have freeRole := Focus.valid_collectionFree good
  rw [role] at freeRole
  have codomainFree : collectionFree codomain = true := (Bool.and_eq_true_iff.mp freeRole).2
  have bodyEquivalent : ReferenceStep.Equivalent relEnv language sourceBody representativeBody := by
    have sourceGoodAtBody : Admissible language free ((List.replicate arity domain ++ locals) ++ ambient) codomain sourceBody := by
      simpa only [context, List.append_assoc] using sourceBodyGood
    exact (reference_equivalent_iff_normalForm_eq laws rows aligned relEnv sourceGoodAtBody
      representativeBodyGood codomainFree).mpr bodyImage
  let child : Focus := .original (List.replicate arity domain ++ focus.bound) codomain sourceBody
    (outer.comp (.multiLambda arity actualBinders .hole))
  have childGood : child.Valid language free bag.category unitLabel := ⟨sourceBodyGood, codomainFree⟩
  have childContext : child.bound = (List.replicate arity domain ++ locals) ++ ambient := by
    change List.replicate arity domain ++ focus.bound = (List.replicate arity domain ++ locals) ++ ambient
    simp only [context, List.append_assoc]
  cases matched with
  | binders bodyMatched =>
    obtain ⟨body, secondFinal, bodyPresent, bodyChecked, finalNormal, finalSource⟩ :=
      bodyComplete child childGood trivial childContext rfl representativeBodyGood bodyEquivalent
        (by simpa only [List.length_append, List.length_replicate, Nat.add_comm] using bodyMatched) schemaTyped initialNormal initialSource
    refine ⟨⟨.multiLambda arity actualBinders body.target, ⟨path, locals, focus, none, none⟩ :: body.frames⟩,
      secondFinal, ?_, ?_, finalNormal, finalSource⟩
    · rw [presentAt.eq_def]
      dsimp only
      rw [found, role]
      dsimp only
      rw [shape, outerRead]
      simp only [beq_self_eq_true, if_true]
      exact List.mem_map.mpr ⟨body, bodyPresent, rfl⟩
    · simpa only [matchAtWith, beq_self_eq_true, if_true, List.length_append, List.length_replicate, Nat.add_comm] using bodyChecked

#print axioms presentAt_binders_covered_of

/-- Ordered constructor spines transport independent ordinary source
matches through strict child induction hypotheses. Each child retains the
original constructor zipper and its actual declared parameter role. -/
private theorem presentArguments_source_arguments_of
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unitLabel) (applyBindings bindings row.left) =
          normalForm (some unitLabel) (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free schemaFree : FreeTypeContext} {locals ambient : List TypeExpr} {path : List Nat}
    {label : String} {outer : Option DerivedContexts.OneHoleContext} (originals : List Pattern)
    {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite}
    {schemas sources representatives : List Pattern} {parameters : List TermParam}
    {index : Nat} {firstInitial secondInitial firstFinal : ScopedRuleMatching.Assignment}
    (sourceTyped : ArgumentsHaveTypes language free (locals ++ ambient) sources parameters)
    (representativeTyped : ArgumentsHaveTypes language free (locals ++ ambient) representatives parameters)
    (schemaTyped : RestAwareTyping.ArgumentsHaveTypes language schemaFree locals schemas parameters)
    (sourceMeta : ∀ source ∈ sources, source.hasCanonicalBinderMetadata = true ∧ isObjectPattern source = true)
    (representativeMeta : ∀ representative ∈ representatives,
      representative.hasCanonicalBinderMetadata = true ∧ isObjectPattern representative = true)
    (images : sources.map (normalForm (some unitLabel)) = representatives.map (normalForm (some unitLabel)))
    (parameterFree : ∀ parameter ∈ parameters, collectionFree (TermParam.typeExpr parameter) = true)
    (outerPresent : outer.isSome = true ∨ sources = [])
    (elementComplete : ∀ schema ∈ schemas, ∀ (source representative : Pattern) (expected : TypeExpr)
      (sourceContext : DerivedContexts.OneHoleContext) (localPath : List Nat)
      (old current completed : ScopedRuleMatching.Assignment),
      (∃ offset parameter, schemas[offset]? = some schema ∧ parameters[offset]? = some parameter ∧
        parameterType? parameter = some expected ∧ localPath = path ++ [index + offset]) →
      RestAwareTyping.HasType language schemaFree locals schema expected →
      Admissible language free (locals ++ ambient) expected source →
      Admissible language free (locals ++ ambient) expected representative →
      collectionFree expected = true →
      ReferenceStep.Equivalent relEnv language source representative →
      GeneralScopedMatch.Matches rule spec ambient.length site localPath locals.length old schema representative completed →
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) old =
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) current →
      List.Forall₂ (fun (first second : String × ContextualValue) =>
        first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
          first.2.ambient = second.2.ambient ∧
            ReferenceStep.Equivalent relEnv language first.2.body second.2.body) old current →
      ∃ spelling next,
        spelling ∈ presentAt language free schemaFree bag.category unitLabel locals localPath schema
          (.original (locals ++ ambient) expected source sourceContext) ∧
        next ∈ matchAtWith (normalBodyComparison unitLabel) rule spec ambient.length site localPath
          locals.length current schema spelling.target ∧
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) completed =
          CanonicalBags.mapAssignment (normalForm (some unitLabel)) next ∧
        List.Forall₂ (fun (first second : String × ContextualValue) =>
          first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
            first.2.ambient = second.2.ambient ∧
              ReferenceStep.Equivalent relEnv language first.2.body second.2.body) completed next)
    (matched : GeneralScopedMatch.Arguments rule spec ambient.length site path locals.length
      firstInitial index schemas representatives firstFinal)
    (initialNormal : CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstInitial =
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondInitial)
    (initialSource : List.Forall₂ (fun (first second : String × ContextualValue) =>
      first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
        first.2.ambient = second.2.ambient ∧
          ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstInitial secondInitial) :
    ∃ children secondFinal,
      children ∈ presentArguments language free schemaFree bag.category unitLabel locals path
        (locals ++ ambient) label outer originals index schemas sources parameters ∧
      secondFinal ∈ matchArgsAtWith (normalBodyComparison unitLabel) rule spec ambient.length site path
        locals.length secondInitial index schemas children.1 ∧
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstFinal =
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondFinal ∧
      List.Forall₂ (fun (first second : String × ContextualValue) =>
        first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
          first.2.ambient = second.2.ambient ∧
            ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstFinal secondFinal := by
  induction schemas generalizing sources representatives parameters index firstInitial secondInitial firstFinal with
  | nil =>
    cases matched
    cases schemaTyped
    cases sourceTyped
    refine ⟨([], []), secondInitial, ?_, ?_, initialNormal, initialSource⟩
    · rw [presentArguments.eq_def]
      exact .head _
    · simp only [matchArgsAtWith, List.mem_singleton]
  | cons schema schemas recurse =>
    cases representatives with
    | nil => cases matched
    | cons representative representatives =>
      cases sources with
      | nil => cases images
      | cons source sources =>
        cases parameters with
        | nil => cases sourceTyped
        | cons parameter parameters =>
          cases sourceTyped with
          | cons sourceRepresentation sourceExpected sourceHeadTyped sourceTailTyped =>
            rename_i expected
            cases representativeTyped with
            | cons representativeRepresentation representativeExpected representativeHeadTyped representativeTailTyped =>
              rename_i representativeType
              have representativeTypeSame : representativeType = expected :=
                Option.some.inj (representativeExpected.symm.trans sourceExpected)
              subst representativeType
              cases schemaTyped with
              | cons schemaRepresentation schemaExpected schemaHeadTyped schemaTailTyped =>
                rename_i schemaType
                have schemaTypeSame : schemaType = expected := Option.some.inj (schemaExpected.symm.trans sourceExpected)
                subst schemaType
                cases matched with
                | cons headMatch tailMatch =>
                  have outerSome : outer.isSome = true := outerPresent.resolve_right (by simp)
                  obtain ⟨outside, outsideRead⟩ := Option.isSome_iff_exists.mp outerSome
                  subst outer
                  have sourceGood : Admissible language free (locals ++ ambient) expected source :=
                    ⟨sourceHeadTyped, (sourceMeta source (by simp)).1, (sourceMeta source (by simp)).2⟩
                  have representativeGood : Admissible language free (locals ++ ambient) expected representative :=
                    ⟨representativeHeadTyped, (representativeMeta representative (by simp)).1,
                      (representativeMeta representative (by simp)).2⟩
                  have expectedFree := collectionFree_parameterType (parameterFree parameter (by simp)) sourceExpected
                  simp only [List.map_cons, List.cons.injEq] at images
                  have headEquivalent := (reference_equivalent_iff_normalForm_eq laws rows aligned relEnv
                    sourceGood representativeGood expectedFree).mpr images.1
                  obtain ⟨head, middle, headPresent, headMatched, middleNormal, middleSource⟩ :=
                    elementComplete schema (by simp) source representative expected
                      (outside.comp (.apply label (originals.take index) .hole (originals.drop (index + 1))))
                      (path ++ [index]) _ _ _ ⟨0, parameter, rfl, rfl, sourceExpected, by simp⟩
                      schemaHeadTyped sourceGood representativeGood expectedFree
                      headEquivalent headMatch initialNormal initialSource
                  obtain ⟨later, secondFinal, laterPresent, laterMatched, finalNormal, finalSource⟩ :=
                    recurse sourceTailTyped representativeTailTyped schemaTailTyped
                      (fun source inside => sourceMeta source (by simp [inside]))
                      (fun representative inside => representativeMeta representative (by simp [inside]))
                      images.2 (fun parameter inside => parameterFree parameter (by simp [inside])) (.inl rfl)
                      (fun child inside source representative expected sourceContext localPath old current completed addressed =>
                        elementComplete child (by simp [inside]) source representative expected sourceContext localPath
                          old current completed (by
                            obtain ⟨offset, parameter, schemaAt, parameterAt, typeAt, pathAt⟩ := addressed
                            refine ⟨offset + 1, parameter, ?_, ?_, typeAt, ?_⟩
                            · simpa only [List.getElem?_cons_succ] using schemaAt
                            · simpa only [List.getElem?_cons_succ] using parameterAt
                            · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using pathAt))
                      tailMatch middleNormal middleSource
                  refine ⟨(head.target :: later.1, head.frames ++ later.2), secondFinal, ?_, ?_, finalNormal, finalSource⟩
                  · rw [presentArguments.eq_def]
                    dsimp only
                    rw [sourceExpected]
                    exact List.mem_flatMap.mpr ⟨head, headPresent,
                      List.mem_map.mpr ⟨later, laterPresent, rfl⟩⟩
                  · rw [matchArgsAtWith.eq_def]
                    dsimp only
                    exact List.mem_flatMap.mpr ⟨middle, headMatched, laterMatched⟩

#print axioms presentArguments_source_arguments_of

private theorem schema_apply_inversion {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {label : String} {arguments : List Pattern} {expected : TypeExpr}
    (typed : RestAwareTyping.HasType language free bound (.apply label arguments) expected) :
    ∃ declaration, declaration ∈ language.terms ∧ label = declaration.label ∧
      ¬ UsesBareCollection declaration ∧ expected = .base declaration.category ∧
      RestAwareTyping.ArgumentsHaveTypes language free bound arguments declaration.params := by
  cases typed with
  | constructor member ordinary argumentsTyped => exact ⟨_, member, rfl, ordinary, rfl, argumentsTyped⟩

/-- Actual validated constructor identities join the source head, schema
and representative spines before recursive matching. The producer records
the original declaration index and preserves every child source zipper. -/
private theorem presentAt_constructor_covered_of
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unitLabel) (applyBindings bindings row.left) =
          normalForm (some unitLabel) (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (valid : language.validate = [])
    (relEnv : Engine.RelationEnv)
    {free schemaFree : FreeTypeContext} {focus : Focus} {locals ambient : List TypeExpr}
    {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite} {path : List Nat}
    {label : String} {schemas representatives : List Pattern}
    {firstInitial secondInitial firstFinal : ScopedRuleMatching.Assignment}
    (good : focus.Valid language free bag.category unitLabel) (physical : focus.Physical)
    (context : focus.bound = locals ++ ambient)
    (representativeGood : Admissible language free (locals ++ ambient) (focus.expected bag.category)
      (.apply label representatives))
    (equivalent : ReferenceStep.Equivalent relEnv language (focus.value unitLabel) (.apply label representatives))
    (schemaTyped : RestAwareTyping.HasType language schemaFree locals (.apply label schemas) (focus.expected bag.category))
    (elementComplete : ∀ schema ∈ schemas, ∀ (source representative : Pattern) (expected : TypeExpr)
      (sourceContext : DerivedContexts.OneHoleContext) (localPath : List Nat)
      (old current completed : ScopedRuleMatching.Assignment),
      (∃ declaration offset parameter,
        declaration ∈ language.terms ∧ declaration.label = label ∧
        focus.expected bag.category = .base declaration.category ∧
        schemas[offset]? = some schema ∧ declaration.params[offset]? = some parameter ∧
        parameterType? parameter = some expected ∧ localPath = path ++ [offset]) →
      RestAwareTyping.HasType language schemaFree locals schema expected →
      Admissible language free (locals ++ ambient) expected source →
      Admissible language free (locals ++ ambient) expected representative →
      collectionFree expected = true →
      ReferenceStep.Equivalent relEnv language source representative →
      GeneralScopedMatch.Matches rule spec ambient.length site localPath locals.length old schema representative completed →
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) old =
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) current →
      List.Forall₂ (fun (first second : String × ContextualValue) =>
        first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
          first.2.ambient = second.2.ambient ∧
            ReferenceStep.Equivalent relEnv language first.2.body second.2.body) old current →
      ∃ spelling next,
        spelling ∈ presentAt language free schemaFree bag.category unitLabel locals localPath schema
          (.original (locals ++ ambient) expected source sourceContext) ∧
        next ∈ matchAtWith (normalBodyComparison unitLabel) rule spec ambient.length site localPath
          locals.length current schema spelling.target ∧
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) completed =
          CanonicalBags.mapAssignment (normalForm (some unitLabel)) next ∧
        List.Forall₂ (fun (first second : String × ContextualValue) =>
          first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
            first.2.ambient = second.2.ambient ∧
              ReferenceStep.Equivalent relEnv language first.2.body second.2.body) completed next)
    (matched : GeneralScopedMatch.Matches rule spec ambient.length site path locals.length
      firstInitial (.apply label schemas) (.apply label representatives) firstFinal)
    (initialNormal : CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstInitial =
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondInitial)
    (initialSource : List.Forall₂ (fun (first second : String × ContextualValue) =>
      first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
        first.2.ambient = second.2.ambient ∧
          ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstInitial secondInitial) :
    ∃ spelling secondFinal,
      spelling ∈ presentAt language free schemaFree bag.category unitLabel locals path (.apply label schemas) focus ∧
      secondFinal ∈ matchAtWith (normalBodyComparison unitLabel) rule spec ambient.length site path
        locals.length secondInitial (.apply label schemas) spelling.target ∧
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstFinal =
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondFinal ∧
      List.Forall₂ (fun (first second : String × ContextualValue) =>
        first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
          first.2.ambient = second.2.ambient ∧
            ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstFinal secondFinal := by
  have representativeGoodAtFocus : Admissible language free focus.bound (focus.expected bag.category)
      (.apply label representatives) := by simpa only [context] using representativeGood
  obtain ⟨head, found, headGood, nonbag, image, _⟩ := Focus.scalar_source_readback laws rows aligned relEnv
    good physical representativeGoodAtFocus equivalent (by simp [normalForm_apply, IsBagNode])
  rw [normalForm_apply] at image
  obtain ⟨sources, shape, images⟩ := normalForm_apply_inverse nonbag image
  have originalTyped := headGood.typed
  rw [shape] at originalTyped
  obtain ⟨declaration, declared, originalLabel, ordinary, resultRole, sourceTyped⟩ :=
    hasType_apply_inversion originalTyped
  obtain ⟨schemaDeclaration, schemaDeclared, schemaLabel, _, _, schemasTyped⟩ := schema_apply_inversion schemaTyped
  obtain ⟨representativeDeclaration, representativeDeclared, representativeLabel, _, _, representativesTyped⟩ :=
    hasType_apply_inversion representativeGood.typed
  have schemaSame : schemaDeclaration = declaration := List.inj_on_of_nodup_map
    (LanguageDef.constructorLabels_nodup_of_validate_eq_nil language valid)
    schemaDeclared declared (schemaLabel.symm.trans originalLabel)
  have representativeSame : representativeDeclaration = declaration := List.inj_on_of_nodup_map
    (LanguageDef.constructorLabels_nodup_of_validate_eq_nil language valid)
    representativeDeclared declared (representativeLabel.symm.trans originalLabel)
  subst schemaDeclaration
  subst representativeDeclaration
  obtain ⟨declarationIndex, atIndex⟩ := List.mem_iff_getElem?.mp declared
  have sourceObjects : isObjectPatternList sources = true := by simpa only [shape, isObjectPattern] using headGood.object
  have sourceCanonical : Pattern.hasCanonicalBinderMetadataList sources = true := by
    simpa only [shape, Pattern.hasCanonicalBinderMetadata] using headGood.canonical
  have representativeObjects : isObjectPatternList representatives = true := by
    simpa only [isObjectPattern] using representativeGood.object
  have representativeCanonical : Pattern.hasCanonicalBinderMetadataList representatives = true := by
    simpa only [Pattern.hasCanonicalBinderMetadata] using representativeGood.canonical
  have different : declaration ≠ bag := by
    intro same
    apply ordinary
    obtain ⟨identifier, bare⟩ := laws.bareShape
    exact ⟨identifier, .hashBag, .base bag.category, by simpa only [same] using bare⟩
  have parameterFree : ∀ parameter ∈ declaration.params, collectionFree (TermParam.typeExpr parameter) = true :=
    fun parameter inside => laws.otherParameters declaration declared different parameter inside
  have outerPresent : (headContext? head).isSome = true ∨ sources = [] := by
    cases head with
    | unit =>
      simp only [SourceHead.original, Pattern.apply.injEq] at shape
      exact .inr shape.2.symm
    | physical occurrence => exact .inl rfl
  cases matched with
  | constructor arguments =>
    have choice := constructorChoices_complete_of_source_match atIndex originalLabel.symm resultRole ordinary
      sourceTyped sourceObjects schemasTyped arguments representativeObjects
    have sourceTypedAtCaller := sourceTyped
    rw [context] at sourceTypedAtCaller
    obtain ⟨children, secondFinal, childrenPresent, childrenMatched, finalNormal, finalSource⟩ :=
      presentArguments_source_arguments_of (label := label) laws rows aligned relEnv sources sourceTypedAtCaller
        representativesTyped schemasTyped
        (fun source member => ⟨hasCanonicalBinderMetadataList_iff.mp sourceCanonical source member,
          isObjectPatternList_iff.mp sourceObjects source member⟩)
        (fun representative member => ⟨hasCanonicalBinderMetadataList_iff.mp representativeCanonical representative member,
          isObjectPatternList_iff.mp representativeObjects representative member⟩)
        images parameterFree outerPresent
        (fun schema inside source representative expected sourceContext localPath old current completed addressed =>
          elementComplete schema inside source representative expected sourceContext localPath old current completed (by
            obtain ⟨offset, parameter, schemaAt, parameterAt, typeAt, pathAt⟩ := addressed
            exact ⟨declaration, offset, parameter, declared, originalLabel.symm, resultRole, schemaAt,
              parameterAt, typeAt, by simpa only [Nat.zero_add] using pathAt⟩))
        arguments initialNormal initialSource
    refine ⟨⟨.apply label children.1,
      ⟨path, locals, focus, some declarationIndex, none⟩ :: children.2⟩,
      secondFinal, ?_, ?_, finalNormal, finalSource⟩
    · rw [presentAt.eq_def]
      dsimp only
      rw [found]
      dsimp only
      rw [shape]
      dsimp only
      rw [beq_self_eq_true]
      apply List.mem_flatMap.mpr
      refine ⟨(declaration, declarationIndex), choice, ?_⟩
      dsimp only
      rw [context]
      exact List.mem_map.mpr ⟨children, childrenPresent, rfl⟩
    · simpa only [matchAtWith, beq_self_eq_true, if_true] using childrenMatched

#print axioms presentAt_constructor_covered_of

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView


set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.Retained

open Mettapedia.OSLF.MeTTaIL Syntax DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted

structure Parameters where
  language : LanguageDef
  free : FreeTypeContext
  schemaFree : FreeTypeContext
  category : String
  unitLabel : String

inductive Kind where
  | spelling
  | children

abbrev Value : Kind → Type
  | .spelling => Spelling
  | .children => List Pattern × List Frame

inductive Query : Kind → Type where
  | at (schemaBound : List TypeExpr) (path : List Nat) (schema : Pattern) (focus : Focus) : Query .spelling
  | arguments (schemaBound : List TypeExpr) (path : List Nat) (bound : List TypeExpr)
      (label : String) (outer : Option OneHoleContext) (originals : List Pattern) (index : Nat)
      (schemas sources : List Pattern) (parameters : List TermParam) : Query .children
  | groups (schemaBound : List TypeExpr) (path : List Nat) (bound : List TypeExpr) (index : Nat)
      (schemas : List Pattern) (groups : List (List SourceOccurrence)) : Query .children

inductive Continuation : Kind → Type where
  | done : Continuation .spelling
  | application (frame : Frame) (label : String) (next : Continuation .spelling) : Continuation .children
  | collection (frame : Frame) (residual : List SourceOccurrence)
      (next : Continuation .spelling) : Continuation .children
  | lambda (frame : Frame) (binder : Option String)
      (next : Continuation .spelling) : Continuation .spelling
  | multiLambda (frame : Frame) (arity : Nat) (binders : List String)
      (next : Continuation .spelling) : Continuation .spelling
  | tail (query : Query .children) (next : Continuation .children) : Continuation .spelling
  | prepend (head : Spelling) (next : Continuation .children) : Continuation .children

inductive Task where
  | request {kind : Kind} (query : Query kind) (next : Continuation kind)
  | returned {kind : Kind} (value : Value kind) (next : Continuation kind)
  | constructors (schemaBound : List TypeExpr) (path : List Nat) (focus : Focus)
      (label : String) (schemas sources : List Pattern) (outer : Option OneHoleContext)
      (ordinal : Nat) (remaining : List GrammarRule) (next : Continuation .spelling)
  | allocations (schemaBound : List TypeExpr) (path : List Nat) (focus : Focus)
      (schemas : List Pattern) (rest : Option String)
      (cursor : GroupedCursor.State) (published : Nat)
      (within : published ≤ cursor.answers.length) (next : Continuation .spelling)

structure State where
  agenda : List Task
  answers : List Spelling

private def frame (path : List Nat) (schemaBound : List TypeExpr) (focus : Focus) : Frame :=
  ⟨path,schemaBound,focus,none,none⟩

def constructorReady (parameters : Parameters) (schemaBound : List TypeExpr) (focus : Focus)
    (label : String) (schemas sources : List Pattern) (row : GrammarRule) : Bool :=
  row.label == label && focus.expected parameters.category == .base row.category && !usesBareCollection? row &&
    checkArgumentsHaveTypes parameters.language parameters.free focus.bound sources row.params &&
      RestAwareTyping.checkSchemaArguments parameters.language parameters.schemaFree schemaBound schemas row.params

def allocationTasks (schemaBound : List TypeExpr) (path : List Nat) (focus : Focus)
    (schemas : List Pattern) (rest : Option String) (next : Continuation .spelling)
    (allocation : List (List SourceOccurrence) × List SourceOccurrence) : List Task :=
  let residual := sortOccurrences allocation.2
  if rest.isNone && !residual.isEmpty then [] else
    let parent : Frame := ⟨path,schemaBound,focus,none,some (allocation.1,residual)⟩
    [Task.request (.groups schemaBound path focus.bound 0 schemas allocation.1)
      (.collection parent residual next)]

/-- Each transition retains unresolved child work. Collection allocation is
advanced through the actual incremental cursor, never its completed list. -/
def expand (parameters : Parameters) : Task → List Task × List Spelling
  | .request (.at schemaBound path schema focus) next =>
      let parent := frame path schemaBound focus
      match schema with
      | .fvar _ =>
          ([.returned (kind := .spelling) ⟨normalForm (some parameters.unitLabel) (focus.value parameters.unitLabel),[parent]⟩ next],[])
      | .collection .hashBag schemas rest =>
          if focus.expected parameters.category == .base parameters.category then
            ([.allocations schemaBound path focus schemas rest
              (GroupedCursor.start schemas.length (focus.components parameters.unitLabel)) 0 (Nat.zero_le _) next],[])
          else ([],[])
      | .collection _ _ _ => ([],[])
      | .bvar expected =>
          match focus.scalar? parameters.unitLabel parameters.category with
          | some head =>
              match head.original parameters.unitLabel with
              | .bvar actual =>
                  if expected == actual then ([.returned (kind := .spelling) ⟨.bvar actual,[parent]⟩ next],[]) else ([],[])
              | _ => ([],[])
          | none => ([],[])
      | .apply label schemas =>
          match focus.scalar? parameters.unitLabel parameters.category with
          | some head =>
              match head.original parameters.unitLabel with
              | .apply actual sources =>
                  if label == actual then
                    ([.constructors schemaBound path focus actual schemas sources
                      (headContext? head) 0 parameters.language.terms next],[])
                  else ([],[])
              | _ => ([],[])
          | none => ([],[])
      | .lambda _ body =>
          match focus.scalar? parameters.unitLabel parameters.category,focus.expected parameters.category with
          | some head,.arrow domain codomain =>
              match head.original parameters.unitLabel,headContext? head with
              | .lambda binder sourceBody,some outer =>
                  ([.request (.at (domain :: schemaBound) (path ++ [0]) body
                      (.original (domain :: focus.bound) codomain sourceBody
                        (outer.comp (.lambda binder .hole))))
                    (.lambda parent binder next)],[])
              | _,_ => ([],[])
          | _,_ => ([],[])
      | .multiLambda arity _ body =>
          match focus.scalar? parameters.unitLabel parameters.category,focus.expected parameters.category with
          | some head,.arrow (.multiBinder domain) codomain =>
              match head.original parameters.unitLabel,headContext? head with
              | .multiLambda actual binders sourceBody,some outer =>
                  if arity == actual then
                    ([.request (.at (List.replicate arity domain ++ schemaBound) (path ++ [0]) body
                        (.original (List.replicate arity domain ++ focus.bound) codomain sourceBody
                          (outer.comp (.multiLambda arity binders .hole))))
                      (.multiLambda parent arity binders next)],[])
                  else ([],[])
              | _,_ => ([],[])
          | _,_ => ([],[])
      | .subst _ _ => ([],[])
  | .request (.arguments schemaBound path bound label outer originals index schemas sources arguments) next =>
      match schemas,sources,arguments with
      | [],[],[] => ([.returned (kind := .children) ([],[]) next],[])
      | schema :: laterSchemas,source :: laterSources,parameter :: laterParameters =>
          match outer,parameterType? parameter with
          | some context,some expected =>
              ([.request (.at schemaBound (path ++ [index]) schema
                  (.original bound expected source
                    (context.comp (.apply label (originals.take index) .hole (originals.drop (index + 1))))))
                (.tail (.arguments schemaBound path bound label outer originals (index + 1)
                  laterSchemas laterSources laterParameters) next)],[])
          | _,_ => ([],[])
      | _,_,_ => ([],[])
  | .request (.groups schemaBound path bound index schemas groups) next =>
      match schemas,groups with
      | [],[] => ([.returned (kind := .children) ([],[]) next],[])
      | schema :: laterSchemas,group :: laterGroups =>
          ([.request (.at schemaBound (path ++ [index]) schema (.grouped bound group))
            (.tail (.groups schemaBound path bound (index + 1) laterSchemas laterGroups) next)],[])
      | _,_ => ([],[])
  | .returned value .done => ([],[value])
  | .returned value (.application parent label next) =>
      ([.returned (kind := .spelling) ⟨.apply label value.1,parent :: value.2⟩ next],[])
  | .returned value (.collection parent residual next) =>
      ([.returned (kind := .spelling) ⟨.collection .hashBag (value.1 ++ residual.map SourceOccurrence.value) none,
        parent :: value.2⟩ next],[])
  | .returned value (.lambda parent binder next) =>
      ([.returned (kind := .spelling) ⟨.lambda binder value.target,parent :: value.frames⟩ next],[])
  | .returned value (.multiLambda parent arity binders next) =>
      ([.returned (kind := .spelling) ⟨.multiLambda arity binders value.target,parent :: value.frames⟩ next],[])
  | .returned value (.tail later next) => ([.request later (.prepend value next)],[])
  | .returned value (.prepend head next) =>
      ([.returned (kind := .children) (head.target :: value.1,head.frames ++ value.2) next],[])
  | .constructors schemaBound path focus label schemas sources outer ordinal remaining next =>
      match remaining with
      | [] => ([],[])
      | row :: later =>
          let scan := Task.constructors schemaBound path focus label schemas sources outer
            (ordinal + 1) later next
          if constructorReady parameters schemaBound focus label schemas sources row then
            let parent : Frame := ⟨path,schemaBound,focus,some ordinal,none⟩
            ([.request (.arguments schemaBound path focus.bound label outer sources 0 schemas sources row.params)
              (.application parent label next),scan],[])
          else ([scan],[])
  | .allocations schemaBound path focus schemas rest cursor published _ next =>
      let advanced := GroupedCursor.tick cursor
      let fresh := advanced.answers.drop published
      let children := fresh.flatMap (allocationTasks schemaBound path focus schemas rest next)
      let pending := if GroupedCursor.complete advanced then [] else
        [Task.allocations schemaBound path focus schemas rest advanced advanced.answers.length (Nat.le_refl _) next]
      (children ++ pending,[])

def startAt (schemaBound : List TypeExpr) (path : List Nat) (schema : Pattern) (focus : Focus) : State :=
  ⟨[.request (.at schemaBound path schema focus) .done],[]⟩

def tick (parameters : Parameters) (state : State) : State :=
  match state.agenda with
  | [] => state
  | task :: pending =>
      let changed := expand parameters task
      ⟨changed.1 ++ pending,state.answers ++ changed.2⟩

def run (parameters : Parameters) : Nat → State → State
  | 0,state => state
  | steps + 1,state => run parameters steps (tick parameters state)

def complete (state : State) : Bool := state.agenda.isEmpty

def results (parameters : Parameters) : {kind : Kind} → Query kind → List (Value kind)
  | _,.at schemaBound path schema focus =>
      presentAt parameters.language parameters.free parameters.schemaFree parameters.category
        parameters.unitLabel schemaBound path schema focus
  | _,.arguments schemaBound path bound label outer originals index schemas sources arguments =>
      presentArguments parameters.language parameters.free parameters.schemaFree parameters.category
        parameters.unitLabel schemaBound path bound label outer originals index schemas sources arguments
  | _,.groups schemaBound path bound index schemas groups =>
      presentGroups parameters.language parameters.free parameters.schemaFree parameters.category
        parameters.unitLabel schemaBound path bound index schemas groups

/-- A continuation interprets a completed child without changing its ordered
presentation frames. It is independent of the task transition function. -/
def readContinuation (parameters : Parameters) : {kind : Kind} → Continuation kind → Value kind → List Spelling
  | _,.done,value => [value]
  | _,.application parent label next,value =>
      readContinuation parameters next ⟨.apply label value.1,parent :: value.2⟩
  | _,.collection parent residual next,value =>
      readContinuation parameters next ⟨.collection .hashBag (value.1 ++ residual.map SourceOccurrence.value) none,
        parent :: value.2⟩
  | _,.lambda parent binder next,value =>
      readContinuation parameters next ⟨.lambda binder value.target,parent :: value.frames⟩
  | _,.multiLambda parent arity binders next,value =>
      readContinuation parameters next ⟨.multiLambda arity binders value.target,parent :: value.frames⟩
  | _,.tail later next,head =>
      (results parameters later).flatMap fun value =>
        readContinuation parameters next (head.target :: value.1,head.frames ++ value.2)
  | _,.prepend head next,value =>
      readContinuation parameters next (head.target :: value.1,head.frames ++ value.2)

def allocationResults (parameters : Parameters) (schemaBound : List TypeExpr) (path : List Nat)
    (focus : Focus) (schemas : List Pattern) (rest : Option String) (next : Continuation .spelling)
    (groups : List (List SourceOccurrence)) (remaining : List SourceOccurrence) : List Spelling :=
  let residual := sortOccurrences remaining
  if rest.isNone && !residual.isEmpty then [] else
    let parent : Frame := ⟨path,schemaBound,focus,none,some (groups,residual)⟩
    (presentGroups parameters.language parameters.free parameters.schemaFree parameters.category
      parameters.unitLabel schemaBound path focus.bound 0 schemas groups).flatMap fun children =>
        readContinuation parameters next ⟨.collection .hashBag (children.1 ++ residual.map SourceOccurrence.value) none,
          parent :: children.2⟩

def cursorAvailable (cursor : GroupedCursor.State) (published : Nat)
    (groups : List (List SourceOccurrence)) (residual : List SourceOccurrence) : Prop :=
  (groups,residual) ∈ cursor.answers.drop published ∨
    ∃ work ∈ cursor.agenda, work.pending groups residual

def Task.meaning (parameters : Parameters) : Task → Spelling → Prop
  | .request query next,wanted =>
      ∃ value ∈ results parameters query, wanted ∈ readContinuation parameters next value
  | .returned value next,wanted => wanted ∈ readContinuation parameters next value
  | .constructors schemaBound path focus label schemas sources outer ordinal remaining next,wanted =>
      ∃ row index, (row,index) ∈ remaining.zipIdx ordinal ∧
        constructorReady parameters schemaBound focus label schemas sources row = true ∧
        ∃ children ∈ presentArguments parameters.language parameters.free parameters.schemaFree
          parameters.category parameters.unitLabel schemaBound path focus.bound label outer sources
          0 schemas sources row.params,
          wanted ∈ readContinuation parameters next
            ⟨.apply label children.1,⟨path,schemaBound,focus,some index,none⟩ :: children.2⟩
  | .allocations schemaBound path focus schemas rest cursor published _ next,wanted =>
      ∃ groups residual, cursorAvailable cursor published groups residual ∧
        wanted ∈ allocationResults parameters schemaBound path focus schemas rest next groups residual

theorem returned_account (parameters : Parameters) {kind : Kind}
    (next : Continuation kind) (value : Value kind) (wanted : Spelling) :
    Task.meaning parameters (.returned value next) wanted ↔
      wanted ∈ (expand parameters (.returned value next)).2 ∨
        ∃ child ∈ (expand parameters (.returned value next)).1, child.meaning parameters wanted := by
  cases next <;> simp [Task.meaning,readContinuation,expand,List.mem_flatMap]

theorem start_meaning_iff (parameters : Parameters) (schemaBound : List TypeExpr)
    (path : List Nat) (schema : Pattern) (focus : Focus) (wanted : Spelling) :
    (∃ task ∈ (startAt schemaBound path schema focus).agenda, task.meaning parameters wanted) ↔
      wanted ∈ presentAt parameters.language parameters.free parameters.schemaFree parameters.category
        parameters.unitLabel schemaBound path schema focus := by
  simp [startAt,Task.meaning,results,readContinuation]

#print axioms returned_account
#print axioms start_meaning_iff

theorem children_account (parameters : Parameters) (query : Query .children)
    (next : Continuation .children) (wanted : Spelling) :
    Task.meaning parameters (.request query next) wanted ↔
      wanted ∈ (expand parameters (.request query next)).2 ∨
        ∃ child ∈ (expand parameters (.request query next)).1, child.meaning parameters wanted := by
  cases query with
  | arguments schemaBound path bound label outer originals index schemas sources arguments =>
      cases schemas <;> cases sources <;> cases arguments
      all_goals try (solve | simp [Task.meaning,results,presentArguments,expand])
      rename_i schema laterSchemas source laterSources parameter laterParameters
      cases outer with
      | none => simp [Task.meaning,results,presentArguments,expand]
      | some context =>
          cases found : parameterType? parameter with
          | none => simp [Task.meaning,results,presentArguments,expand,found]
          | some expected =>
              simp [Task.meaning,results,presentArguments,expand,found,readContinuation,
                List.mem_flatMap,List.mem_map]
              aesop
  | groups schemaBound path bound index schemas groups =>
      cases schemas <;> cases groups
      all_goals try (solve | simp [Task.meaning,results,presentGroups,expand])
      simp [Task.meaning,results,presentGroups,expand,readContinuation,List.mem_flatMap,List.mem_map]
      aesop

#print axioms children_account

theorem constructors_account (parameters : Parameters) (schemaBound : List TypeExpr)
    (path : List Nat) (focus : Focus) (label : String) (schemas sources : List Pattern)
    (outer : Option OneHoleContext) (ordinal : Nat) (remaining : List GrammarRule)
    (next : Continuation .spelling) (wanted : Spelling) :
    Task.meaning parameters
      (.constructors schemaBound path focus label schemas sources outer ordinal remaining next) wanted ↔
      wanted ∈ (expand parameters
        (.constructors schemaBound path focus label schemas sources outer ordinal remaining next)).2 ∨
      ∃ child ∈ (expand parameters
        (.constructors schemaBound path focus label schemas sources outer ordinal remaining next)).1,
        child.meaning parameters wanted := by
  cases remaining with
  | nil => simp [Task.meaning,expand]
  | cons row later =>
      cases ready : constructorReady parameters schemaBound focus label schemas sources row with
      | false =>
          simp [Task.meaning,expand,ready,List.zipIdx_cons]
          aesop
      | true =>
          simp [Task.meaning,expand,ready,List.zipIdx_cons,results,readContinuation]
          aesop

#print axioms constructors_account

theorem cursor_available_start (count : Nat) (occurrences : List SourceOccurrence)
    (groups : List (List SourceOccurrence)) (residual : List SourceOccurrence) :
    cursorAvailable (GroupedCursor.start count occurrences) 0 groups residual ↔
      (groups,residual) ∈ groupedOccurrences count occurrences := by
  simpa [cursorAvailable,GroupedCursor.start] using
    (GroupedCursor.start_pending_iff count occurrences (groups := groups) (residual := residual))

theorem at_account (parameters : Parameters) (schemaBound : List TypeExpr) (path : List Nat)
    (schema : Pattern) (focus : Focus) (next : Continuation .spelling) (wanted : Spelling) :
    Task.meaning parameters (.request (.at schemaBound path schema focus) next) wanted ↔
      wanted ∈ (expand parameters (.request (.at schemaBound path schema focus) next)).2 ∨
        ∃ child ∈ (expand parameters (.request (.at schemaBound path schema focus) next)).1,
          child.meaning parameters wanted := by
  cases schema with
  | fvar name => simp [Task.meaning,results,presentAt,expand,frame]
  | subst body replacement => simp [Task.meaning,results,presentAt,expand]
  | collection kind schemas rest =>
      cases kind <;> try (solve | simp [Task.meaning,results,presentAt,expand])
      by_cases role : focus.expected parameters.category == .base parameters.category
      · simp [Task.meaning,results,presentAt,expand,role,allocationResults,cursor_available_start,
          List.mem_flatMap,List.mem_map]
        aesop
      · simp [Task.meaning,results,presentAt,expand,role]
  | bvar expected =>
      cases picked : focus.scalar? parameters.unitLabel parameters.category with
      | none => simp [Task.meaning,results,presentAt,expand,picked]
      | some head =>
          cases shape : head.original parameters.unitLabel <;>
            try (solve | simp [Task.meaning,results,presentAt,expand,picked,shape])
          rename_i actual
          by_cases equal : expected == actual <;>
            simp [Task.meaning,results,presentAt,expand,picked,shape,frame,equal]
  | apply label schemas =>
      cases picked : focus.scalar? parameters.unitLabel parameters.category with
      | none => simp [Task.meaning,results,presentAt,expand,picked]
      | some head =>
          cases shape : head.original parameters.unitLabel <;>
            try (solve | simp [Task.meaning,results,presentAt,expand,picked,shape])
          rename_i actual sources
          by_cases equal : label == actual
          · simp only [Task.meaning,results,presentAt,expand,picked,shape,equal,if_pos,
              List.not_mem_nil,false_or,List.mem_singleton,exists_eq_left,constructorChoices,
              constructorReady,List.mem_flatMap,List.mem_map,List.mem_filter,Prod.exists]
            constructor
            · rintro ⟨value,⟨row,index,⟨declared,ready⟩,children,frames,member,same⟩,accepted⟩
              cases same
              exact ⟨row,index,declared,ready,children,frames,member,accepted⟩
            · rintro ⟨row,index,declared,ready,children,frames,member,accepted⟩
              exact ⟨_,⟨row,index,⟨declared,ready⟩,children,frames,member,rfl⟩,accepted⟩
          · simp [Task.meaning,results,presentAt,expand,picked,shape,equal]
  | lambda binder body =>
      cases picked : focus.scalar? parameters.unitLabel parameters.category with
      | none => simp [Task.meaning,results,presentAt,expand,picked]
      | some head =>
          cases role : focus.expected parameters.category <;>
            try (solve | simp [Task.meaning,results,presentAt,expand,picked,role])
          cases shape : head.original parameters.unitLabel <;>
            try (solve | simp [Task.meaning,results,presentAt,expand,picked,role,shape])
          cases context : headContext? head <;>
            try (solve | simp [Task.meaning,results,presentAt,expand,picked,role,shape,context])
          simp [Task.meaning,results,presentAt,expand,picked,role,shape,context,
            readContinuation,frame,List.mem_map]
  | multiLambda arity binders body =>
      cases picked : focus.scalar? parameters.unitLabel parameters.category with
      | none => simp [Task.meaning,results,presentAt,expand,picked]
      | some head =>
          cases role : focus.expected parameters.category <;>
            try (solve | simp [Task.meaning,results,presentAt,expand,picked,role])
          rename_i domain codomain
          cases domain <;> try (solve | simp [Task.meaning,results,presentAt,expand,picked,role])
          cases shape : head.original parameters.unitLabel <;>
            try (solve | simp [Task.meaning,results,presentAt,expand,picked,role,shape])
          rename_i actual sourceBinders sourceBody
          cases context : headContext? head <;>
            try (solve | simp [Task.meaning,results,presentAt,expand,picked,role,shape,context])
          by_cases equal : arity == actual
          · simp [Task.meaning,results,presentAt,expand,picked,role,shape,context,equal,
              readContinuation,frame,List.mem_map]
          · simp [Task.meaning,results,presentAt,expand,picked,role,shape,context,equal]

#print axioms cursor_available_start
#print axioms at_account

private theorem group_pending_before_selection {slots index : Nat}
    {closed : List (List SourceOccurrence)} {selected remaining : List SourceOccurrence}
    {occurrence : SourceOccurrence} {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (found : remaining[index]? = some occurrence)
    (pending : GroupedCursor.groupPending slots closed (occurrence :: selected)
      (remaining.eraseIdx index) groups residual) :
    GroupedCursor.groupPending slots closed selected remaining groups residual := by
  obtain ⟨suffix,later,shape,lengths,account⟩ := pending
  have within := (List.getElem?_eq_some_iff.mp found).1
  have item := (List.getElem?_eq_some_iff.mp found).2
  have chosen := List.getElem_cons_eraseIdx_perm within
  rw [item] at chosen
  refine ⟨occurrence :: suffix,later,?_,lengths,?_⟩
  · simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using shape
  · simpa only [List.cons_append] using (account.cons occurrence).trans chosen

private theorem residual_pending_before_selection {index : Nat}
    {closed : List (List SourceOccurrence)} {selected remaining : List SourceOccurrence}
    {occurrence : SourceOccurrence} {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (found : remaining[index]? = some occurrence)
    (pending : GroupedCursor.residualPending closed (occurrence :: selected)
      (remaining.eraseIdx index) groups residual) :
    GroupedCursor.residualPending closed selected remaining groups residual := by
  obtain ⟨groupsEq,suffix,shape,account⟩ := pending
  have within := (List.getElem?_eq_some_iff.mp found).1
  have item := (List.getElem?_eq_some_iff.mp found).2
  have chosen := List.getElem_cons_eraseIdx_perm within
  rw [item] at chosen
  refine ⟨groupsEq,occurrence :: suffix,?_,(account.cons occurrence).trans chosen⟩
  simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using shape

theorem cursor_finished_pending {work : GroupedCursor.Work}
    {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (done : work.finished? = some (groups,residual)) : work.pending groups residual := by
  cases work with
  | groups slots closed selected remaining => simp [GroupedCursor.Work.finished?] at done
  | selectGroup slots closed selected remaining cursor => simp [GroupedCursor.Work.finished?] at done
  | selectResidual closed selected remaining cursor => simp [GroupedCursor.Work.finished?] at done
  | residual closed selected remaining =>
      cases remaining with
      | cons head tail => simp [GroupedCursor.Work.finished?] at done
      | nil =>
          simp only [GroupedCursor.Work.finished?,Option.some.injEq,Prod.mk.injEq] at done
          rcases done with ⟨rfl,rfl⟩
          exact ⟨rfl,[],by simp,by simp⟩

#print axioms cursor_finished_pending

theorem cursor_expand_pending {work branch : GroupedCursor.Work}
    {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (member : branch ∈ GroupedCursor.expand work) (pending : branch.pending groups residual) :
    work.pending groups residual := by
  cases work with
  | groups slots closed selected remaining =>
      cases slots with
      | zero => simp [GroupedCursor.expand] at member
      | succ slots =>
          simp only [GroupedCursor.expand,List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl
          · by_cases last : slots = 0
            · subst slots
              simp only [GroupedCursor.Work.pending,GroupedCursor.residualPending] at pending
              obtain ⟨groupsEq,suffix,residualEq,account⟩ := pending
              subst residual
              refine ⟨[],[],?_,rfl,?_⟩
              · simpa using groupsEq
              · simpa using account
            · simp only [if_neg last,GroupedCursor.Work.pending] at pending
              obtain ⟨suffix,later,shape,lengths,account⟩ := pending
              refine ⟨[],suffix :: later,?_,?_,?_⟩
              · simpa only [List.reverse_nil,List.nil_append,List.append_nil,List.append_assoc,List.singleton_append] using shape
              · simp only [List.length_cons]
                omega
              · simpa only [List.nil_append,List.flatten_cons,List.append_assoc] using account
          · obtain ⟨index,occurrence,_,found,selectedPending⟩ := pending
            exact group_pending_before_selection found selectedPending
  | selectGroup slots closed selected remaining cursor =>
      cases found : remaining[cursor]? with
      | none => simp [GroupedCursor.expand,found] at member
      | some occurrence =>
          simp only [GroupedCursor.expand,found,List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl
          · exact ⟨cursor,occurrence,le_rfl,found,pending⟩
          · obtain ⟨index,selectedOccurrence,later,selectedFound,selectedPending⟩ := pending
            exact ⟨index,selectedOccurrence,by omega,selectedFound,selectedPending⟩
  | residual closed selected remaining =>
      cases remaining with
      | nil => simp [GroupedCursor.expand] at member
      | cons head tail =>
          simp only [GroupedCursor.expand,List.mem_singleton] at member
          subst branch
          obtain ⟨index,occurrence,_,found,selectedPending⟩ := pending
          exact residual_pending_before_selection found selectedPending
  | selectResidual closed selected remaining cursor =>
      cases found : remaining[cursor]? with
      | none => simp [GroupedCursor.expand,found] at member
      | some occurrence =>
          simp only [GroupedCursor.expand,found,List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl
          · exact ⟨cursor,occurrence,le_rfl,found,pending⟩
          · obtain ⟨index,selectedOccurrence,later,selectedFound,selectedPending⟩ := pending
            exact ⟨index,selectedOccurrence,by omega,selectedFound,selectedPending⟩

theorem cursor_pending_iff (work : GroupedCursor.Work)
    (groups : List (List SourceOccurrence)) (residual : List SourceOccurrence) :
    work.pending groups residual ↔ work.finished? = some (groups,residual) ∨
      ∃ branch ∈ GroupedCursor.expand work,branch.pending groups residual := by
  constructor
  · exact GroupedCursor.expand_covers
  · rintro (done | ⟨branch,member,pending⟩)
    · exact cursor_finished_pending done
    · exact cursor_expand_pending member pending

#print axioms cursor_expand_pending
#print axioms cursor_pending_iff

theorem cursor_finished_pending_iff {work : GroupedCursor.Work}
    {allocation : List (List SourceOccurrence) × List SourceOccurrence}
    (done : work.finished? = some allocation)
    (groups : List (List SourceOccurrence)) (residual : List SourceOccurrence) :
    work.pending groups residual ↔ allocation = (groups,residual) := by
  cases work with
  | groups slots closed selected remaining => simp [GroupedCursor.Work.finished?] at done
  | selectGroup slots closed selected remaining cursor => simp [GroupedCursor.Work.finished?] at done
  | selectResidual closed selected remaining cursor => simp [GroupedCursor.Work.finished?] at done
  | residual closed selected remaining =>
      cases remaining with
      | cons head tail => simp [GroupedCursor.Work.finished?] at done
      | nil =>
          simp only [GroupedCursor.Work.finished?,Option.some.injEq] at done
          subst allocation
          simp only [GroupedCursor.Work.pending,GroupedCursor.residualPending]
          constructor
          · rintro ⟨rfl,suffix,rfl,account⟩
            have empty : suffix = [] := List.perm_nil.mp account
            subst suffix
            simp
          · intro same
            cases same
            exact ⟨rfl,[],by simp,by simp⟩

theorem cursor_available_tick (cursor : GroupedCursor.State) (published : Nat)
    (sane : published ≤ cursor.answers.length)
    (groups : List (List SourceOccurrence)) (residual : List SourceOccurrence) :
    cursorAvailable cursor published groups residual ↔
      cursorAvailable (GroupedCursor.tick cursor) published groups residual := by
  cases cursor with
  | mk agenda answers =>
      cases agenda with
      | nil => rfl
      | cons work waiting =>
          cases done : work.finished? with
          | none =>
              have refines : work.pending groups residual ↔
                  ∃ child ∈ GroupedCursor.expand work,child.pending groups residual := by
                simpa only [done,reduceCtorEq,false_or] using cursor_pending_iff work groups residual
              simp only [cursorAvailable,GroupedCursor.tick,done,List.mem_cons,List.mem_append,
                or_and_right,exists_or,exists_eq_left,refines]
          | some allocation =>
              have refines := cursor_finished_pending_iff done groups residual
              simp only [cursorAvailable,GroupedCursor.tick,done,List.drop_append_of_le_length sane,
                List.mem_append,List.mem_cons,or_and_right,exists_or,exists_eq_left,
                refines]
              tauto

#print axioms cursor_finished_pending_iff
#print axioms cursor_available_tick

theorem allocationTasks_account (parameters : Parameters) (schemaBound : List TypeExpr)
    (path : List Nat) (focus : Focus) (schemas : List Pattern) (rest : Option String)
    (next : Continuation .spelling) (allocation : List (List SourceOccurrence) × List SourceOccurrence)
    (wanted : Spelling) :
    (∃ child ∈ allocationTasks schemaBound path focus schemas rest next allocation,
      child.meaning parameters wanted) ↔
      wanted ∈ allocationResults parameters schemaBound path focus schemas rest next allocation.1 allocation.2 := by
  by_cases rejected : rest.isNone && !(sortOccurrences allocation.2).isEmpty
  · simp [allocationTasks,allocationResults,rejected]
  · simp [allocationTasks,allocationResults,rejected,Task.meaning,results,readContinuation,List.mem_flatMap]

theorem pending_allocation_task_account (parameters : Parameters) (schemaBound : List TypeExpr)
    (path : List Nat) (focus : Focus) (schemas : List Pattern) (rest : Option String)
    (next : Continuation .spelling) (cursor : GroupedCursor.State) (wanted : Spelling) :
    (∃ child ∈ (if GroupedCursor.complete cursor then [] else
      [Task.allocations schemaBound path focus schemas rest cursor cursor.answers.length (Nat.le_refl _) next]),
      child.meaning parameters wanted) ↔
      ∃ groups residual,(∃ work ∈ cursor.agenda,work.pending groups residual) ∧
        wanted ∈ allocationResults parameters schemaBound path focus schemas rest next groups residual := by
  cases cursor with
  | mk agenda answers =>
      cases agenda <;> simp [GroupedCursor.complete,Task.meaning,cursorAvailable]

theorem allocationTaskBatch_account (parameters : Parameters) (schemaBound : List TypeExpr)
    (path : List Nat) (focus : Focus) (schemas : List Pattern) (rest : Option String)
    (next : Continuation .spelling)
    (allocations : List (List (List SourceOccurrence) × List SourceOccurrence)) (wanted : Spelling) :
    (∃ child ∈ allocations.flatMap (allocationTasks schemaBound path focus schemas rest next),
      child.meaning parameters wanted) ↔
      ∃ allocation ∈ allocations,
        wanted ∈ allocationResults parameters schemaBound path focus schemas rest next allocation.1 allocation.2 := by
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨child,⟨allocation,member,childMember⟩,meaning⟩
    exact ⟨allocation,member,(allocationTasks_account parameters schemaBound path focus schemas rest next
      allocation wanted).mp ⟨child,childMember,meaning⟩⟩
  · rintro ⟨allocation,member,meaning⟩
    obtain ⟨child,childMember,accepted⟩ :=
      (allocationTasks_account parameters schemaBound path focus schemas rest next allocation wanted).mpr meaning
    exact ⟨child,⟨allocation,member,childMember⟩,accepted⟩

theorem allocations_account (parameters : Parameters) (schemaBound : List TypeExpr)
    (path : List Nat) (focus : Focus) (schemas : List Pattern) (rest : Option String)
    (cursor : GroupedCursor.State) (published : Nat) (sane : published ≤ cursor.answers.length)
    (next : Continuation .spelling) (wanted : Spelling) :
    Task.meaning parameters
      (.allocations schemaBound path focus schemas rest cursor published sane next) wanted ↔
      wanted ∈ (expand parameters
        (.allocations schemaBound path focus schemas rest cursor published sane next)).2 ∨
      ∃ child ∈ (expand parameters
        (.allocations schemaBound path focus schemas rest cursor published sane next)).1,
        child.meaning parameters wanted := by
  change (∃ groups residual,cursorAvailable cursor published groups residual ∧
    wanted ∈ allocationResults parameters schemaBound path focus schemas rest next groups residual) ↔ _
  simp_rw [cursor_available_tick cursor published sane]
  simp only [expand,List.not_mem_nil,false_or,List.mem_append,or_and_right,exists_or]
  rw [allocationTaskBatch_account,pending_allocation_task_account]
  simp only [cursorAvailable,or_and_right,exists_or,Prod.exists]

#print axioms allocationTasks_account
#print axioms pending_allocation_task_account
#print axioms allocationTaskBatch_account
#print axioms allocations_account

theorem expand_account (parameters : Parameters) (task : Task) (wanted : Spelling) :
    task.meaning parameters wanted ↔ wanted ∈ (expand parameters task).2 ∨
      ∃ child ∈ (expand parameters task).1,child.meaning parameters wanted := by
  cases task with
  | request query next =>
      cases query with
      | «at» schemaBound path schema focus => exact at_account parameters schemaBound path schema focus next wanted
      | arguments schemaBound path bound label outer originals index schemas sources arguments =>
          exact children_account parameters _ next wanted
      | groups schemaBound path bound index schemas groups => exact children_account parameters _ next wanted
  | returned value next => exact returned_account parameters next value wanted
  | constructors schemaBound path focus label schemas sources outer ordinal remaining next =>
      exact constructors_account parameters schemaBound path focus label schemas sources outer ordinal remaining next wanted
  | allocations schemaBound path focus schemas rest cursor published sane next =>
      exact allocations_account parameters schemaBound path focus schemas rest cursor published sane next wanted

def State.accepts (parameters : Parameters) (state : State) (wanted : Spelling) : Prop :=
  wanted ∈ state.answers ∨ ∃ task ∈ state.agenda,task.meaning parameters wanted

theorem tick_accepts (parameters : Parameters) (state : State) (wanted : Spelling) :
    (tick parameters state).accepts parameters wanted ↔ state.accepts parameters wanted := by
  cases state with
  | mk agenda answers =>
      cases agenda with
      | nil => rfl
      | cons task waiting =>
          have preserves := expand_account parameters task wanted
          simp only [State.accepts,tick,List.mem_append,List.mem_cons,or_and_right,exists_or,exists_eq_left]
          simp only [preserves,or_assoc]

theorem run_accepts (parameters : Parameters) (steps : Nat) (state : State) (wanted : Spelling) :
    (run parameters steps state).accepts parameters wanted ↔ state.accepts parameters wanted := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps ih => exact (ih (tick parameters state)).trans (tick_accepts parameters state wanted)

theorem run_add (parameters : Parameters) (first second : Nat) (state : State) :
    run parameters (first + second) state = run parameters second (run parameters first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add,run]
  | succ first ih => simpa only [Nat.succ_add,run] using ih (tick parameters state)

#print axioms expand_account
#print axioms tick_accepts
#print axioms run_accepts
#print axioms run_add

mutual
  def schemaWeight : Pattern → Nat
    | .apply _ schemas | .collection _ schemas _ => schemasWeight schemas + 3
    | .lambda _ body | .multiLambda _ _ body => schemaWeight body + 2
    | .subst body replacement => schemaWeight body + schemaWeight replacement + 1
    | .bvar _ | .fvar _ => 1
  termination_by schema => sizeOf schema
  decreasing_by all_goals sizeOf_pattern_dec

  def schemasWeight : List Pattern → Nat
    | [] => 1
    | head :: tail => schemaWeight head + schemasWeight tail + 3
  termination_by schemas => sizeOf schemas
  decreasing_by all_goals sizeOf_pattern_dec
end

def Query.weight : {kind : Kind} → Query kind → Nat
  | _,.at _ _ schema _ => schemaWeight schema
  | _,.arguments _ _ _ _ _ _ _ schemas _ _ => schemasWeight schemas
  | _,.groups _ _ _ _ schemas _ => schemasWeight schemas

def Continuation.weight : {kind : Kind} → Continuation kind → Nat
  | _,.done => 0
  | _,.application _ _ next | _,.collection _ _ next => next.weight + 1
  | _,.lambda _ _ next | _,.multiLambda _ _ _ next => next.weight + 1
  | _,.tail later next => later.weight + next.weight + 2
  | _,.prepend _ next => next.weight + 1

def Task.rank : Task → Nat × Nat
  | .request query next => (query.weight + next.weight,0)
  | .returned _ next => (next.weight,0)
  | .constructors _ _ _ _ schemas _ _ _ remaining next =>
      (schemasWeight schemas + next.weight + 2,remaining.length)
  | .allocations _ _ _ schemas _ cursor _ _ next =>
      (schemasWeight schemas + next.weight + 2,GroupedCursor.agendaCost cursor.agenda)

abbrev Earlier (first second : Task) : Prop :=
  Prod.Lex ((· < ·) : Nat → Nat → Prop) ((· < ·) : Nat → Nat → Prop) first.rank second.rank

private theorem earlier_of_weight_lt {first second : Task} (less : first.rank.1 < second.rank.1) :
    Earlier first second := Prod.Lex.left _ _ less

theorem returned_decreases (parameters : Parameters) {kind : Kind}
    (value : Value kind) (next : Continuation kind) {child : Task}
    (member : child ∈ (expand parameters (.returned value next)).1) :
    Earlier child (.returned value next) := by
  cases next <;> simp only [expand,List.mem_singleton,List.not_mem_nil] at member
  all_goals subst child
  all_goals apply earlier_of_weight_lt
  all_goals simp only [Task.rank,Continuation.weight,Query.weight]
  all_goals omega

#print axioms schemaWeight
#print axioms schemasWeight
#print axioms returned_decreases

macro "retained_weight" : tactic => `(tactic|
  (subst_vars
   apply earlier_of_weight_lt
   dsimp only [Task.rank,Query.weight,Continuation.weight]
   simp only [schemaWeight,schemasWeight]
   omega))

theorem request_decreases (parameters : Parameters) {kind : Kind}
    (query : Query kind) (next : Continuation kind) {child : Task}
    (member : child ∈ (expand parameters (.request query next)).1) :
    Earlier child (.request query next) := by
  cases query with
  | «at» schemaBound path schema focus =>
      cases schema with
      | fvar name => simp only [expand,List.mem_singleton] at member; retained_weight
      | subst body replacement => simp [expand] at member
      | collection kind schemas rest =>
          cases kind <;> try (solve | simp [expand] at member)
          simp only [expand] at member
          split at member <;> simp_all only [List.mem_singleton,List.not_mem_nil] ; retained_weight
      | bvar expected =>
          cases picked : focus.scalar? parameters.unitLabel parameters.category with
          | none => simp [expand,picked] at member
          | some head =>
              cases shape : head.original parameters.unitLabel <;>
                try (solve | simp [expand,picked,shape] at member)
              simp only [expand,picked,shape] at member
              split at member <;> simp_all only [List.mem_singleton,List.not_mem_nil] ; retained_weight
      | apply label schemas =>
          cases picked : focus.scalar? parameters.unitLabel parameters.category with
          | none => simp [expand,picked] at member
          | some head =>
              cases shape : head.original parameters.unitLabel <;>
                try (solve | simp [expand,picked,shape] at member)
              simp only [expand,picked,shape] at member
              split at member <;> simp_all only [List.mem_singleton,List.not_mem_nil] ; retained_weight
      | lambda binder body =>
          cases picked : focus.scalar? parameters.unitLabel parameters.category with
          | none => simp [expand,picked] at member
          | some head =>
              cases role : focus.expected parameters.category <;>
                try (solve | simp [expand,picked,role] at member)
              cases shape : head.original parameters.unitLabel <;>
                try (solve | simp [expand,picked,role,shape] at member)
              cases context : headContext? head <;>
                simp [expand,picked,role,shape,context] at member ; retained_weight
      | multiLambda arity binders body =>
          cases picked : focus.scalar? parameters.unitLabel parameters.category with
          | none => simp [expand,picked] at member
          | some head =>
              cases role : focus.expected parameters.category <;>
                try (solve | simp [expand,picked,role] at member)
              rename_i domain codomain
              cases domain <;> try (solve | simp [expand,picked,role] at member)
              cases shape : head.original parameters.unitLabel <;>
                try (solve | simp [expand,picked,role,shape] at member)
              cases context : headContext? head <;>
                try (solve | simp [expand,picked,role,shape,context] at member)
              simp only [expand,picked,role,shape,context] at member
              split at member <;> simp_all only [List.mem_singleton,List.not_mem_nil] ; retained_weight
  | arguments schemaBound path bound label outer originals index schemas sources arguments =>
      cases schemas <;> cases sources <;> cases arguments
      all_goals try (solve | simp [expand] at member <;> retained_weight)
      rename_i schema laterSchemas source laterSources parameter laterParameters
      cases outer with
      | none => simp [expand] at member
      | some context =>
          cases found : parameterType? parameter <;> simp [expand,found] at member ; retained_weight
  | groups schemaBound path bound index schemas groups =>
      cases schemas <;> cases groups <;> simp [expand] at member <;> retained_weight

#print axioms request_decreases

theorem constructors_decreases (parameters : Parameters) (schemaBound : List TypeExpr)
    (path : List Nat) (focus : Focus) (label : String) (schemas sources : List Pattern)
    (outer : Option OneHoleContext) (ordinal : Nat) (remaining : List GrammarRule)
    (next : Continuation .spelling) {child : Task}
    (member : child ∈ (expand parameters
      (.constructors schemaBound path focus label schemas sources outer ordinal remaining next)).1) :
    Earlier child (.constructors schemaBound path focus label schemas sources outer ordinal remaining next) := by
  cases remaining with
  | nil => simp [expand] at member
  | cons row later =>
      simp only [expand] at member
      split at member
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl
        · apply earlier_of_weight_lt
          dsimp only [Task.rank,Query.weight,Continuation.weight]
          omega
        · apply Prod.Lex.right
          simp only [List.length_cons]
          exact Nat.lt_succ_self _
      · simp only [List.mem_singleton] at member
        subst child
        apply Prod.Lex.right
        simp only [List.length_cons]
        exact Nat.lt_succ_self _

theorem allocations_decreases (parameters : Parameters) (schemaBound : List TypeExpr)
    (path : List Nat) (focus : Focus) (schemas : List Pattern) (rest : Option String)
    (cursor : GroupedCursor.State) (published : Nat) (within : published ≤ cursor.answers.length)
    (next : Continuation .spelling) {child : Task}
    (member : child ∈ (expand parameters
      (.allocations schemaBound path focus schemas rest cursor published within next)).1) :
    Earlier child (.allocations schemaBound path focus schemas rest cursor published within next) := by
  simp only [expand,List.mem_append] at member
  rcases member with fresh | pending
  · obtain ⟨allocation,_,member⟩ := List.mem_flatMap.mp fresh
    simp only [allocationTasks] at member
    split at member
    · simp at member
    · simp only [List.mem_singleton] at member
      subst child
      apply earlier_of_weight_lt
      dsimp only [Task.rank,Query.weight,Continuation.weight]
      omega
  · by_cases finished : GroupedCursor.complete (GroupedCursor.tick cursor)
    · simp only [if_pos finished,List.not_mem_nil] at pending
    · simp only [if_neg finished,List.mem_singleton] at pending
      subst child
      have incomplete : cursor.agenda ≠ [] := by
        intro empty
        have unchanged : GroupedCursor.tick cursor = cursor := by
          simp only [GroupedCursor.tick,empty]
        apply finished
        simp only [unchanged,GroupedCursor.complete,empty,List.isEmpty_nil]
      have decrease := GroupedCursor.tick_cost cursor incomplete
      apply Prod.Lex.right
      omega

theorem expand_decreases (parameters : Parameters) {task child : Task}
    (member : child ∈ (expand parameters task).1) : Earlier child task := by
  cases task with
  | request query next => exact request_decreases parameters query next member
  | returned value next => exact returned_decreases parameters value next member
  | constructors schemaBound path focus label schemas sources outer ordinal remaining next =>
      exact constructors_decreases parameters schemaBound path focus label schemas sources outer ordinal remaining next member
  | allocations schemaBound path focus schemas rest cursor published within next =>
      exact allocations_decreases parameters schemaBound path focus schemas rest cursor published within next member

#print axioms constructors_decreases
#print axioms allocations_decreases
#print axioms expand_decreases

def taskCost (parameters : Parameters) (task : Task) : Nat :=
  1 + (((expand parameters task).1).attach.map fun child => taskCost parameters child.val).sum
termination_by task.rank
decreasing_by exact expand_decreases parameters child.property

def agendaCost (parameters : Parameters) (agenda : List Task) : Nat :=
  (agenda.map (taskCost parameters)).sum

theorem taskCost_eq (parameters : Parameters) (task : Task) :
    taskCost parameters task = 1 + agendaCost parameters (expand parameters task).1 := by
  rw [taskCost.eq_def]
  have same := congrArg (fun tasks : List Task => (tasks.map (taskCost parameters)).sum)
    (List.attach_map_subtype_val (expand parameters task).1)
  apply congrArg (fun cost : Nat => 1 + cost)
  simpa only [agendaCost,List.map_map,Function.comp_def] using same

theorem agendaCost_append (parameters : Parameters) (first second : List Task) :
    agendaCost parameters (first ++ second) = agendaCost parameters first + agendaCost parameters second := by
  simp only [agendaCost,List.map_append,List.sum_append]

theorem tick_cost (parameters : Parameters) (state : State) (pending : state.agenda ≠ []) :
    agendaCost parameters (tick parameters state).agenda + 1 = agendaCost parameters state.agenda := by
  cases state with
  | mk agenda answers =>
      cases agenda with
      | nil => exact False.elim (pending rfl)
      | cons task waiting =>
          simp only [tick]
          change agendaCost parameters ((expand parameters task).1 ++ waiting) + 1 =
            taskCost parameters task + agendaCost parameters waiting
          rw [agendaCost_append,taskCost_eq]
          omega

/-- Finiteness is earned from the actual retained expansion tree, including
all continuation and allocation tasks. No completed-run premise is required. -/
theorem finiteDrain (parameters : Parameters) (state : State) :
    ∃ steps,(run parameters steps state).agenda = [] := by
  by_cases finished : state.agenda = []
  · exact ⟨0,finished⟩
  · obtain ⟨steps,drained⟩ := finiteDrain parameters (tick parameters state)
    exact ⟨steps + 1,drained⟩
termination_by agendaCost parameters state.agenda
decreasing_by have decrease := tick_cost parameters state finished; omega

theorem run_idle (parameters : Parameters) (steps : Nat) (state : State) (finished : state.agenda = []) :
    run parameters steps state = state := by
  induction steps with
  | zero => rfl
  | succ steps ih => simpa only [run,tick,finished] using ih

theorem start_accepts_iff (parameters : Parameters) (schemaBound : List TypeExpr) (path : List Nat)
    (schema : Pattern) (focus : Focus) (wanted : Spelling) :
    (startAt schemaBound path schema focus).accepts parameters wanted ↔
      wanted ∈ presentAt parameters.language parameters.free parameters.schemaFree parameters.category
        parameters.unitLabel schemaBound path schema focus := by
  simpa only [State.accepts,startAt,List.not_mem_nil,false_or] using
    start_meaning_iff parameters schemaBound path schema focus wanted

/-- Every interrupted state completes, and its exact independent denotation
is retained in the actual answer list. -/
theorem completes_with_exact_answers (parameters : Parameters) (state : State) :
    ∃ steps,(run parameters steps state).agenda = [] ∧
      ∀ wanted,wanted ∈ (run parameters steps state).answers ↔ state.accepts parameters wanted := by
  obtain ⟨steps,drained⟩ := finiteDrain parameters state
  refine ⟨steps,drained,?_⟩
  intro wanted
  simpa only [State.accepts,drained,List.not_mem_nil,false_and,exists_false,or_false] using
    run_accepts parameters steps state wanted

/-- The retained producer covers precisely the separately specified finite
source presentations, while initialization retains only one unfinished task. -/
theorem start_completes_with_reference_answers (parameters : Parameters)
    (schemaBound : List TypeExpr) (path : List Nat) (schema : Pattern) (focus : Focus) :
    ∃ steps,(run parameters steps (startAt schemaBound path schema focus)).agenda = [] ∧
      ∀ wanted,wanted ∈ (run parameters steps (startAt schemaBound path schema focus)).answers ↔
        wanted ∈ presentAt parameters.language parameters.free parameters.schemaFree parameters.category
          parameters.unitLabel schemaBound path schema focus := by
  obtain ⟨steps,drained,exactAnswers⟩ := completes_with_exact_answers parameters
    (startAt schemaBound path schema focus)
  exact ⟨steps,drained,fun wanted => (exactAnswers wanted).trans
    (start_accepts_iff parameters schemaBound path schema focus wanted)⟩

#print axioms taskCost
#print axioms taskCost_eq
#print axioms tick_cost
#print axioms finiteDrain
#print axioms run_idle
#print axioms start_accepts_iff
#print axioms completes_with_exact_answers
#print axioms start_completes_with_reference_answers

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView.Retained

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching Match
open Mettapedia.GSLT.LanguageDef.WellSorted

open Mettapedia.OSLF.MeTTaIL.DerivedContexts GeneralTypedSites OccurrenceZipperAddress RestOccurrenceAddress

private theorem context_row_get {α : Type*} (before after : List α) (focus : α) :
    (before ++ focus :: after)[before.length]? = some focus := by
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

private theorem context_row_take {α : Type*} (before after : List α) (focus : α) :
    (before ++ focus :: after).take before.length = before := List.take_left

private theorem context_row_drop {α : Type*} (before after : List α) (focus : α) :
    (before ++ focus :: after).drop (before.length + 1) = after := by
  rw [List.drop_add_one_eq_tail_drop, List.drop_left]
  rfl

/-- The actual ordinary occurrence reader recovers a filled schema zipper
at its actual child address. Explicit substitutions and every binder form
are included, independently of operational descent permissions. -/
private theorem term_occurrence_at_context (context : OneHoleContext) (identifier : String) :
    termZipperAt? (context.fill (.fvar identifier)) (contextAddress context) = some (identifier, context) := by
  induction context with
  | hole => simp only [OneHoleContext.fill, contextAddress, termZipperAt?]
  | apply label before inner after recurse =>
    dsimp only [OneHoleContext.fill, contextAddress]
    rw [termZipperAt?.eq_def]
    dsimp only
    rw [context_row_get]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, recurse, context_row_take, context_row_drop]
  | lambda binder inner recurse =>
    dsimp only [OneHoleContext.fill, contextAddress]
    rw [termZipperAt?.eq_def]
    simp only [Option.bind_eq_bind, recurse, Option.bind_some, Option.pure_def]
  | multiLambda arity binders inner recurse =>
    dsimp only [OneHoleContext.fill, contextAddress]
    rw [termZipperAt?.eq_def]
    simp only [Option.bind_eq_bind, recurse, Option.bind_some, Option.pure_def]
  | substBody inner replacement recurse =>
    dsimp only [OneHoleContext.fill, contextAddress]
    rw [termZipperAt?.eq_def]
    simp only [Option.bind_eq_bind, recurse, Option.bind_some, Option.pure_def]
  | substReplacement body inner recurse =>
    dsimp only [OneHoleContext.fill, contextAddress]
    rw [termZipperAt?.eq_def]
    simp only [Option.bind_eq_bind, recurse, Option.bind_some, Option.pure_def]
  | collection kind before inner after rest recurse =>
    have within : before.length < (before ++ inner.fill (.fvar identifier) :: after).length := by
      simp only [List.length_append, List.length_cons]
      omega
    dsimp only [OneHoleContext.fill, contextAddress]
    rw [termZipperAt?.eq_def]
    dsimp only
    rw [if_pos within, context_row_get]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, recurse, context_row_take, context_row_drop]

/-- The real rest reader retains the enclosing collection zipper and exact
terminal rest address through arbitrary outer schema contexts. -/
private theorem rest_occurrence_at_context (context : OneHoleContext) (identifier : String)
    (kind : CollType) (elements : List Pattern) :
    restSiteAt? (context.fill (.collection kind elements (some identifier)))
      (contextAddress context ++ [elements.length]) =
        some { name := identifier, kind, elements, context } := by
  induction context with
  | hole => simp [OneHoleContext.fill, contextAddress, restSiteAt?]
  | apply label before inner after recurse =>
    dsimp only [OneHoleContext.fill, contextAddress, List.cons_append]
    rw [restSiteAt?.eq_def]
    dsimp only
    rw [context_row_get]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, recurse, context_row_take, context_row_drop, RestSite.push, OneHoleContext.comp]
  | lambda binder inner recurse =>
    dsimp only [OneHoleContext.fill, contextAddress, List.cons_append]
    rw [restSiteAt?.eq_def]
    simp only [Option.bind_eq_bind, recurse, Option.bind_some, Option.pure_def, RestSite.push, OneHoleContext.comp]
  | multiLambda arity binders inner recurse =>
    dsimp only [OneHoleContext.fill, contextAddress, List.cons_append]
    rw [restSiteAt?.eq_def]
    simp only [Option.bind_eq_bind, recurse, Option.bind_some, Option.pure_def, RestSite.push, OneHoleContext.comp]
  | substBody inner replacement recurse =>
    dsimp only [OneHoleContext.fill, contextAddress, List.cons_append]
    rw [restSiteAt?.eq_def]
    simp only [Option.bind_eq_bind, recurse, Option.bind_some, Option.pure_def, RestSite.push, OneHoleContext.comp]
  | substReplacement body inner recurse =>
    dsimp only [OneHoleContext.fill, contextAddress, List.cons_append]
    rw [restSiteAt?.eq_def]
    simp only [Option.bind_eq_bind, recurse, Option.bind_some, Option.pure_def, RestSite.push, OneHoleContext.comp]
  | collection outerKind before inner after tail recurse =>
    have within : before.length < (before ++ inner.fill (.collection kind elements (some identifier)) :: after).length := by
      simp only [List.length_append, List.length_cons]
      omega
    dsimp only [OneHoleContext.fill, contextAddress, List.cons_append]
    rw [restSiteAt?.eq_def]
    dsimp only
    rw [if_pos within, context_row_get]
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, recurse, context_row_take, context_row_drop, RestSite.push, OneHoleContext.comp]

#print axioms term_occurrence_at_context
#print axioms rest_occurrence_at_context

/-- A genuine typed schema zipper earns the existing typed occurrence
classifier at precisely its own full sort prefix and executable address. -/
private theorem typed_term_occurrence_at_context
    {language : LanguageDef} {free : FreeTypeContext} {context : OneHoleContext}
    {identifier : String} {rootType expected : TypeExpr}
    {schemaBound locals binderPrefix : List TypeExpr}
    (selected : TypedAt language free (.fvar identifier) context schemaBound rootType locals expected)
    (contextPrefix : locals = binderPrefix ++ schemaBound) :
    RestAwareTyping.TypedOccurrenceAt language free schemaBound (context.fill (.fvar identifier)) rootType
      binderPrefix (contextAddress context) identifier := by
  have decoded := term_occurrence_at_context context identifier
  have count : binderPrefix.length = binderCount context := by
    have length := selected.focusBound_length
    rw [contextPrefix, List.length_append] at length
    omega
  refine .term context locals expected decoded selected selected.fvar_lookup
    contextPrefix count ?_
  simpa only [Nat.zero_add, count] using termZipperAt?_depth decoded 0

/-- A real typed enclosing collection and its original zipper earn the
same existing classifier for a rest slot. The actual rest declaration,
ambient boundary and full binder prefix are retained. -/
private theorem typed_rest_occurrence_at_context
    {language : LanguageDef} {free : FreeTypeContext} {context : OneHoleContext}
    {identifier : String} {kind : CollType} {elements : List Pattern}
    {rootType expected : TypeExpr} {schemaBound locals binderPrefix : List TypeExpr}
    (selected : TypedAt language free (.collection kind elements (some identifier)) context schemaBound rootType locals expected)
    (typed : RestAwareTyping.HasType language free locals (.collection kind elements (some identifier)) expected)
    (contextPrefix : locals = binderPrefix ++ schemaBound) :
    RestAwareTyping.TypedOccurrenceAt language free schemaBound
      (context.fill (.collection kind elements (some identifier))) rootType binderPrefix
        (contextAddress context ++ [elements.length]) identifier := by
  have decoded := rest_occurrence_at_context context identifier kind elements
  have count : binderPrefix.length = binderCount context := by
    have length := selected.focusBound_length
    rw [contextPrefix, List.length_append] at length
    omega
  obtain ⟨elementType, lookup⟩ := typed.restDeclared
  refine .rest { name := identifier, kind, elements, context } locals expected elementType
    decoded rfl typed selected lookup contextPrefix count ?_
  simpa only [Nat.zero_add, count] using restSiteAt?_depth decoded 0

/-- Successful ordinary capture supplies the exact dependency lookup,
occurrence arguments and checked inverse spine used by execution. It does
not infer their sorts from a depth or from a target endpoint. -/
private theorem capture_partial_spine_contract
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth : Nat}
    {site : RulePatternSite} {path : List Nat} {identifier : String} {target : Pattern}
    {initial final : ScopedRuleMatching.Assignment}
    (captured : capture? rule spec ambient depth site path initial identifier target = some final) :
    ∃ dependencies arguments indices,
      dependencies? spec identifier = some dependencies ∧
      arguments? rule spec identifier site path = some arguments ∧
      variableSpine? depth arguments = some indices := by
  simp only [capture?, Option.bind_eq_bind, Option.bind_eq_some_iff] at captured
  obtain ⟨dependencies, declared, arguments, atSite, value, recovered, _⟩ := captured
  unfold recoverValue? at recovered
  split at recovered <;> [cases recovered; skip]
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at recovered
  obtain ⟨indices, spineChecked, _⟩ := recovered
  exact ⟨dependencies, arguments, indices, declared, atSite, spineChecked⟩

#print axioms typed_term_occurrence_at_context
#print axioms typed_rest_occurrence_at_context
#print axioms capture_partial_spine_contract


private theorem context_row_reconstruct {α : Type*} {items : List α} {index : Nat} {item : α}
    (selected : items[index]? = some item) :
    items.take index ++ item :: items.drop (index + 1) = items := by
  obtain ⟨within, actual⟩ := List.getElem?_eq_some_iff.mp selected
  have account := List.take_append_drop index items
  rw [List.drop_eq_getElem_cons within, actual] at account
  exact account

/-- An actual constructor argument index and its actual parameter index
earn the exact existing typed zipper. No result-sort inference from an
unrelated declaration or equal prefix length is used. -/
private theorem argument_slot_typedAt
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {declaration : GrammarRule} {arguments : List Pattern} {index : Nat}
    {argument : Pattern} {parameter : TermParam} {expected : TypeExpr}
    (declared : declaration ∈ language.terms) (ordinary : ¬ UsesBareCollection declaration)
    (typed : ArgumentsHaveTypes language free bound arguments declaration.params)
    (selected : arguments[index]? = some argument)
    (selectedParameter : declaration.params[index]? = some parameter)
    (parameterType : parameterType? parameter = some expected) :
    TypedAt language free argument
      (.apply declaration.label (arguments.take index) .hole (arguments.drop (index + 1)))
      bound (.base declaration.category) bound expected := by
  have rebuilt : ArgumentsHaveTypes language free bound
      (arguments.take index ++ argument :: arguments.drop (index + 1)) declaration.params := by
    rw [context_row_reconstruct selected]
    exact typed
  obtain ⟨beforeParameters, actualParameter, afterParameters, actualType,
      parametersEq, lengthEq, _, _, actualParameterType, argumentTyped, _⟩ := rebuilt.append_cons_split
  have within := (List.getElem?_eq_some_iff.mp selected).1
  have prefixLength : beforeParameters.length = index := by
    simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt within)] using lengthEq
  have actualAtIndex : declaration.params[index]? = some actualParameter := by
    rw [parametersEq, ← prefixLength]
    exact context_row_get beforeParameters afterParameters actualParameter
  have parameterSame : actualParameter = parameter := Option.some.inj (actualAtIndex.symm.trans selectedParameter)
  subst actualParameter
  have typeSame : actualType = expected := Option.some.inj (actualParameterType.symm.trans parameterType)
  subst actualType
  exact .application declared ordinary rebuilt parametersEq lengthEq actualParameterType (.here argumentTyped)

/-- A real homogeneous bag member keeps its original bag context, role
and caller sort list when selected for recursive schema descent. -/
private theorem bag_slot_typedAt
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {schemas : List Pattern}
    {schema : Pattern} {index : Nat} {rest : Option String}
    (typed : RestAwareTyping.ElementsHaveType language free bound schemas (.base bag.category))
    (selected : schemas[index]? = some schema) :
    TypedAt language free schema
      (.collection .hashBag (schemas.take index) .hole (schemas.drop (index + 1)) rest)
      bound (.base bag.category) bound (.base bag.category) := by
  obtain ⟨parameter, bare⟩ := laws.bareShape
  have rebuilt : ElementsHaveType language free bound
      (schemas.take index ++ schema :: schemas.drop (index + 1)) (.base bag.category) := by
    rw [context_row_reconstruct selected]
    exact typed.forget
  exact .collectionConstructor laws.bagAuthored bare rebuilt
    (.here (elementsHaveType_iff.mp typed.forget schema (List.mem_of_getElem? selected)))

#print axioms argument_slot_typedAt
#print axioms bag_slot_typedAt


/-- The actual stored row supplies the checked sorts at its actual typed
source occurrence. Empty-dependency inference is read from arguments?. -/
private theorem arguments?_checked_at_typed_occurrence
    {language : LanguageDef} {schemaFree : FreeTypeContext}
    {schemaBound ambient : List TypeExpr} {wholeSchema : Pattern} {rootType : TypeExpr}
    {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite}
    (siteSchema : sitePattern? rule site = some wholeSchema)
    (rowChecks : ∀ binderPrefix (row : MetavariableOccurrence),
      row ∈ spec.occurrences → row.site = site →
      RestAwareTyping.TypedOccurrenceAt language schemaFree schemaBound wholeSchema rootType
        binderPrefix row.path row.name →
      RestAwareTyping.checkStoredRowArguments language schemaFree
        (binderPrefix ++ schemaBound) ambient spec row = true)
    {binderPrefix : List TypeExpr} {path : List Nat} {identifier : String}
    {dependencies : List TypeExpr} {arguments : List Pattern}
    (typed : RestAwareTyping.TypedOccurrenceAt language schemaFree schemaBound wholeSchema rootType
      binderPrefix path identifier)
    (declared : dependencies? spec identifier = some dependencies)
    (atSite : arguments? rule spec identifier site path = some arguments) :
    RestAwareTyping.checkOccurrenceArguments language schemaFree
      (binderPrefix ++ schemaBound) ambient arguments dependencies = true := by
  have observed : occurrenceDeclared rule
      { name := identifier, site, path, arguments := [] } = true := by
    simp only [occurrenceDeclared, siteSchema, Option.bind_some,
      typed.executable, beq_self_eq_true]
  cases selectedRows : spec.occurrences.filter
      (fun row => row.name == identifier && row.site == site && row.path == path) with
  | nil =>
    cases dependencies with
    | nil =>
      have empty : arguments = [] := by
        simpa [arguments?, declared, observed, selectedRows] using atSite.symm
      subst arguments
      rfl
    | cons dependency dependencies =>
      simp [arguments?, declared, observed, selectedRows] at atSite
  | cons row later =>
    have inside : row ∈ spec.occurrences.filter
        (fun row => row.name == identifier && row.site == site && row.path == path) := by
      rw [selectedRows]
      exact .head _
    have rowIdentity : (row.name = identifier ∧ row.site = site) ∧ row.path = path := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using (List.mem_filter.mp inside).2
    cases later with
    | nil =>
      have rowRead :
          (if occurrenceDeclared rule row && row.arguments.length == dependencies.length
           then some row.arguments else none) = some arguments := by
        simpa [arguments?, declared, observed, selectedRows] using atSite
      split at rowRead
      next permitted =>
        have argumentsEq : row.arguments = arguments := Option.some.inj rowRead
        have checked := rowChecks binderPrefix row (List.mem_filter.mp inside).1 rowIdentity.1.2
          (by simpa only [rowIdentity.1.1, rowIdentity.2] using typed)
        unfold RestAwareTyping.checkStoredRowArguments at checked
        rw [rowIdentity.1.1, declared] at checked
        simpa only [argumentsEq] using checked
      next refused => cases rowRead
    | cons next later =>
      simp [arguments?, declared, observed, selectedRows] at atSite

/-- A successful ordinary rest match exposes its real dependency lookup,
argument row and inverse spine at the final source slot. -/
private theorem bag_rest_spine_contract
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient depth index : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final : ScopedRuleMatching.Assignment}
    {schemas targets : List Pattern} {rest : Option String} {kind : CollType} {identifier : String}
    (matched : GeneralScopedMatch.Bag rule spec ambient site path depth initial index schemas rest kind targets final)
    (restEq : rest = some identifier) :
    ∃ dependencies arguments indices,
      dependencies? spec identifier = some dependencies ∧
      arguments? rule spec identifier site (path ++ [index + schemas.length]) = some arguments ∧
      variableSpine? depth arguments = some indices := by
  induction schemas generalizing initial index targets with
  | nil =>
    cases matched with
    | nil => cases restEq
    | rest captured =>
      cases restEq
      simpa only [List.length_nil, Nat.add_zero] using capture_partial_spine_contract captured
  | cons schema schemas inductionHypothesis =>
    cases matched with
    | cons selected within head tail =>
      obtain ⟨dependencies, arguments, indices, declared, atSite, spineChecked⟩ :=
        inductionHypothesis tail
      refine ⟨dependencies, arguments, indices, declared, ?_, spineChecked⟩
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using atSite

#print axioms arguments?_checked_at_typed_occurrence
#print axioms bag_rest_spine_contract

/-- Validation identifies the original declaration before a selected child
is transported through the actual parameter type and source zipper. -/
private theorem schema_argument_slot_typedAt
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    (valid : language.validate = [])
    {label : String} {schemas : List Pattern} {type : TypeExpr}
    (typed : RestAwareTyping.HasType language free bound (.apply label schemas) type)
    {declaration : GrammarRule} {index : Nat} {schema : Pattern}
    {parameter : TermParam} {expected : TypeExpr}
    (declared : declaration ∈ language.terms) (labelEq : declaration.label = label)
    (atIndex : schemas[index]? = some schema)
    (atParameter : declaration.params[index]? = some parameter)
    (parameterType : parameterType? parameter = some expected) :
    TypedAt language free schema
      (.apply label (schemas.take index) .hole (schemas.drop (index + 1)))
      bound type bound expected := by
  obtain ⟨actualDeclaration, actualDeclared, actualLabel, ordinary, resultRole, argumentsTyped⟩ :=
    schema_apply_inversion typed
  have same : actualDeclaration = declaration := List.inj_on_of_nodup_map
    (LanguageDef.constructorLabels_nodup_of_validate_eq_nil language valid)
    actualDeclared declared (actualLabel.symm.trans labelEq.symm)
  subst actualDeclaration
  simpa only [labelEq, resultRole] using
    argument_slot_typedAt declared ordinary argumentsTyped.forget atIndex atParameter parameterType

#print axioms schema_argument_slot_typedAt

/-- The actual schema derivation identifies its homogeneous carrier and
retains the strong element typing instead of reconstructing it from the
forgotten ordinary judgment. -/
private theorem schema_bag_typing
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    {free : FreeTypeContext} {bound : List TypeExpr} {kind : CollType}
    {elements : List Pattern} {rest : Option String} {expected : TypeExpr}
    (typed : RestAwareTyping.HasType language free bound (.collection kind elements rest) expected)
    (collectionless : collectionFree expected = true) :
    kind = .hashBag ∧ expected = .base bag.category ∧
      RestAwareTyping.ElementsHaveType language free bound elements (.base bag.category) := by
  cases typed with
  | collection elementsTyped restTyped => simp [collectionFree] at collectionless
  | collectionConstructor membership shape elementsTyped restTyped =>
    obtain ⟨rfl, kindEq, elementEq⟩ := laws.toBagTheory.eq_bag_of_collectionParameter membership
      ((GrammarRule.bareParams_cons_iff _ _ _).mp shape).2
    exact ⟨kindEq, rfl, by simpa only [elementEq] using elementsTyped⟩

#print axioms schema_bag_typing

set_option maxRecDepth 4096 in
/-- Every independently typed ordinary scoped match in an admissible source
presentation is reached by the recursive finite producer. Actual source
zippers determine row addresses and complete binder-sort prefixes. -/
theorem presentAt_source_match_covered
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unitLabel) (applyBindings bindings row.left) =
          normalForm (some unitLabel) (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (valid : language.validate = [])
    (relEnv : Engine.RelationEnv)
    {free schemaFree : FreeTypeContext} {schemaBound ambient : List TypeExpr}
    {wholeSchema : Pattern} {rootType : TypeExpr}
    {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite}
    (siteSchema : sitePattern? rule site = some wholeSchema)
    (rowChecks : ∀ binderPrefix (row : MetavariableOccurrence),
      row ∈ spec.occurrences → row.site = site →
      RestAwareTyping.TypedOccurrenceAt language schemaFree schemaBound wholeSchema rootType
        binderPrefix row.path row.name →
      RestAwareTyping.checkStoredRowArguments language schemaFree
        (binderPrefix ++ schemaBound) ambient spec row = true)
    (schema : Pattern)
    {schemaContext : OneHoleContext} {locals : List TypeExpr} {expected : TypeExpr}
    {path : List Nat} {focus : Focus} {representative : Pattern}
    {firstInitial secondInitial firstFinal : ScopedRuleMatching.Assignment}
    (schemaAt : schemaContext.fill schema = wholeSchema)
    (address : path = contextAddress schemaContext)
    (selected : TypedAt language schemaFree schema schemaContext schemaBound rootType locals expected)
    (schemaTyped : RestAwareTyping.HasType language schemaFree locals schema expected)
    (good : focus.Valid language free bag.category unitLabel) (physical : focus.Physical)
    (context : focus.bound = locals ++ ambient) (role : focus.expected bag.category = expected)
    (representativeGood : Admissible language free (locals ++ ambient) expected representative)
    (equivalent : ReferenceStep.Equivalent relEnv language (focus.value unitLabel) representative)
    (matched : GeneralScopedMatch.Matches rule spec ambient.length site path locals.length
      firstInitial schema representative firstFinal)
    (initialNormal : CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstInitial =
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondInitial)
    (initialSource : List.Forall₂ (fun (first second : String × ContextualValue) =>
      first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
        first.2.ambient = second.2.ambient ∧
          ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstInitial secondInitial) :
    ∃ spelling secondFinal,
      spelling ∈ presentAt language free schemaFree bag.category unitLabel locals path schema focus ∧
      secondFinal ∈ matchAtWith (normalBodyComparison unitLabel) rule spec ambient.length site path
        locals.length secondInitial schema spelling.target ∧
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstFinal =
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondFinal ∧
      List.Forall₂ (fun (first second : String × ContextualValue) =>
        first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
          first.2.ambient = second.2.ambient ∧
            ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstFinal secondFinal := by
  cases schema with
  | fvar identifier =>
    cases matched with
    | capture captured =>
      obtain ⟨dependencies, arguments, indices, declared, atSite, spineChecked⟩ :=
        capture_partial_spine_contract captured
      obtain ⟨binderPrefix, contextPrefix⟩ := selected.ambient_suffix
      have typedOccurrence := typed_term_occurrence_at_context selected contextPrefix
      rw [schemaAt, ← address] at typedOccurrence
      have sortsChecked := arguments?_checked_at_typed_occurrence siteSchema rowChecks
        typedOccurrence declared atSite
      rw [← contextPrefix] at sortsChecked
      exact presentAt_capture_covered laws rows aligned relEnv good context
        (by simpa only [role] using representativeGood) equivalent declared atSite spineChecked
        sortsChecked (.capture captured) initialNormal initialSource
  | bvar index =>
    cases matched with
    | bound =>
      obtain ⟨spelling, produced, targetEq⟩ := presentAt_bound_covered laws rows aligned relEnv locals path
        good physical (by simpa only [context, role] using representativeGood) equivalent
      refine ⟨spelling, secondInitial, produced, ?_, initialNormal, initialSource⟩
      rw [targetEq]
      simp only [matchAtWith, beq_self_eq_true, if_true, List.mem_singleton]
  | apply label schemas =>
    cases matched with
    | constructor childrenMatched =>
      refine presentAt_constructor_covered_of laws rows aligned valid relEnv good physical context
        (by simpa only [role] using representativeGood) equivalent
        (by simpa only [role] using schemaTyped) ?_ (.constructor childrenMatched) initialNormal initialSource
      intro child inside source representative childType sourceContext localPath old current completed
        addressed childTyped sourceGood childGood childFree childEquivalent childMatched oldNormal oldSource
      obtain ⟨declaration, offset, parameter, declared, labelEq, resultRole,
        atIndex, atParameter, parameterType, pathEq⟩ := addressed
      let inner : OneHoleContext := .apply label (schemas.take offset) .hole (schemas.drop (offset + 1))
      have rebuilt : inner.fill child = .apply label schemas := by
        simp only [inner, OneHoleContext.fill]
        rw [context_row_reconstruct atIndex]
      have slot := schema_argument_slot_typedAt valid schemaTyped declared labelEq
        atIndex atParameter parameterType
      have outer : TypedAt language schemaFree (inner.fill child) schemaContext schemaBound rootType locals expected := by
        rw [rebuilt]
        exact selected
      have childSelected : TypedAt language schemaFree child (schemaContext.comp inner)
          schemaBound rootType locals childType := outer.comp slot
      have childAt : (schemaContext.comp inner).fill child = wholeSchema := by
        rw [OneHoleContext.fill_comp, rebuilt, schemaAt]
      have childAddress : localPath = contextAddress (schemaContext.comp inner) := by
        have within := (List.getElem?_eq_some_iff.mp atIndex).1
        simpa only [contextAddress_comp, inner, contextAddress, List.length_take,
          Nat.min_eq_left (Nat.le_of_lt within), ← address] using pathEq
      have smaller := List.sizeOf_lt_of_mem inside
      exact presentAt_source_match_covered laws rows aligned valid relEnv siteSchema rowChecks child
        childAt childAddress childSelected childTyped ⟨sourceGood, childFree⟩ trivial rfl rfl
        childGood childEquivalent childMatched oldNormal oldSource
  | lambda binder body =>
    cases schemaTyped with
    | @lambda _ _ _ domain codomain bodyTyped =>
      cases matched with
      | binder bodyMatched =>
        refine presentAt_binder_covered_of laws rows aligned relEnv good physical context role
          representativeGood equivalent bodyTyped ?_ (.binder bodyMatched) initialNormal initialSource
        intro child childValid childPhysical childContext childRole bodyGood childEquivalent
          childMatched childTyped oldNormal oldSource
        let inner : OneHoleContext := .lambda binder .hole
        have slot : TypedAt language schemaFree body inner locals (.arrow domain codomain)
            (domain :: locals) codomain := .lambda (.here bodyTyped.forget)
        have childSelected : TypedAt language schemaFree body (schemaContext.comp inner)
            schemaBound rootType (domain :: locals) codomain := selected.comp slot
        have childAt : (schemaContext.comp inner).fill body = wholeSchema := by
          simpa only [inner, OneHoleContext.fill_comp, OneHoleContext.fill] using schemaAt
        have childAddress : path ++ [0] = contextAddress (schemaContext.comp inner) := by
          simp only [contextAddress_comp, inner, contextAddress, ← address]
        exact presentAt_source_match_covered laws rows aligned valid relEnv siteSchema rowChecks body
          childAt childAddress childSelected childTyped childValid childPhysical childContext childRole
          bodyGood childEquivalent childMatched oldNormal oldSource
  | multiLambda arity binders body =>
    cases schemaTyped with
    | @multiLambda _ _ _ _ domain codomain bodyTyped =>
      cases matched with
      | binders bodyMatched =>
        refine presentAt_binders_covered_of laws rows aligned relEnv good physical context role
          representativeGood equivalent bodyTyped ?_ (.binders bodyMatched) initialNormal initialSource
        intro child childValid childPhysical childContext childRole bodyGood childEquivalent
          childMatched childTyped oldNormal oldSource
        let inner : OneHoleContext := .multiLambda arity binders .hole
        have slot : TypedAt language schemaFree body inner locals (.arrow (.multiBinder domain) codomain)
            (List.replicate arity domain ++ locals) codomain := .multiLambda (.here bodyTyped.forget)
        have childSelected : TypedAt language schemaFree body (schemaContext.comp inner)
            schemaBound rootType (List.replicate arity domain ++ locals) codomain := selected.comp slot
        have childAt : (schemaContext.comp inner).fill body = wholeSchema := by
          simpa only [inner, OneHoleContext.fill_comp, OneHoleContext.fill] using schemaAt
        have childAddress : path ++ [0] = contextAddress (schemaContext.comp inner) := by
          simp only [contextAddress_comp, inner, contextAddress, ← address]
        exact presentAt_source_match_covered laws rows aligned valid relEnv siteSchema rowChecks body
          childAt childAddress childSelected childTyped childValid childPhysical childContext childRole
          bodyGood childEquivalent childMatched oldNormal oldSource
  | subst body replacement =>
    cases matched with
    | substitution bodyMatched replacementMatched =>
      have object := representativeGood.object
      simp only [isObjectPattern] at object
      cases object
  | collection kind schemas rest =>
    have freeRole : collectionFree expected = true := by
      simpa only [role] using Focus.valid_collectionFree good
    obtain ⟨kindEq, typeEq, schemasTyped⟩ := schema_bag_typing laws schemaTyped freeRole
    cases kindEq
    cases typeEq
    cases matched with
    | bag notVector bagMatched =>
      refine presentAt_bag_covered_of laws rows aligned relEnv good physical context role
        representativeGood equivalent schemasTyped ?_ ?_ bagMatched initialNormal initialSource
      · intro identifier restEq
        obtain ⟨dependencies, arguments, indices, declared, atSite, spineChecked⟩ :=
          bag_rest_spine_contract bagMatched restEq
        have atSource : arguments? rule spec identifier site (path ++ [schemas.length]) = some arguments := by
          simpa only [Nat.zero_add] using atSite
        obtain ⟨binderPrefix, contextPrefix⟩ := selected.ambient_suffix
        have selectedRest := selected
        rw [restEq] at selectedRest
        have typedRest := schemaTyped
        rw [restEq] at typedRest
        have typedOccurrence := typed_rest_occurrence_at_context selectedRest typedRest contextPrefix
        have rootAt : schemaContext.fill (.collection .hashBag schemas (some identifier)) = wholeSchema := by
          simpa only [restEq] using schemaAt
        rw [rootAt, ← address] at typedOccurrence
        have sortsChecked := arguments?_checked_at_typed_occurrence siteSchema rowChecks
          typedOccurrence declared atSource
        rw [← contextPrefix] at sortsChecked
        exact ⟨dependencies, arguments, indices, declared, atSource, spineChecked, sortsChecked⟩
      · intro child inside source group localPath old current completed addressed childTyped
          sourceGood groupGood groupPhysical childEquivalent childMatched oldNormal oldSource
        obtain ⟨offset, atIndex, pathEq⟩ := addressed
        let inner : OneHoleContext :=
          .collection .hashBag (schemas.take offset) .hole (schemas.drop (offset + 1)) rest
        have rebuilt : inner.fill child = .collection .hashBag schemas rest := by
          simp only [inner, OneHoleContext.fill]
          rw [context_row_reconstruct atIndex]
        have slot := bag_slot_typedAt laws (rest := rest) schemasTyped atIndex
        have outer : TypedAt language schemaFree (inner.fill child) schemaContext schemaBound rootType
            locals (.base bag.category) := by
          rw [rebuilt]
          exact selected
        have childSelected : TypedAt language schemaFree child (schemaContext.comp inner)
            schemaBound rootType locals (.base bag.category) := outer.comp slot
        have childAt : (schemaContext.comp inner).fill child = wholeSchema := by
          rw [OneHoleContext.fill_comp, rebuilt, schemaAt]
        have childAddress : localPath = contextAddress (schemaContext.comp inner) := by
          have within := (List.getElem?_eq_some_iff.mp atIndex).1
          simpa only [contextAddress_comp, inner, contextAddress, List.length_take,
            Nat.min_eq_left (Nat.le_of_lt within), ← address] using pathEq
        have smaller := List.sizeOf_lt_of_mem inside
        exact presentAt_source_match_covered laws rows aligned valid relEnv siteSchema rowChecks child
          childAt childAddress childSelected childTyped groupGood groupPhysical rfl rfl
          sourceGood (.symm _ _ childEquivalent) childMatched oldNormal oldSource
termination_by sizeOf schema
decreasing_by all_goals sizeOf_pattern_dec

#print axioms presentAt_source_match_covered

/-- At the actual left endpoint, the root schema context is empty and the
free schema types are the rule's own declarations. The capture account is
earned from an initially empty ordinary source match. -/
theorem presentAt_rule_left_source_match_covered
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unitLabel) (applyBindings bindings row.left) =
          normalForm (some unitLabel) (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (valid : language.validate = [])
    (relEnv : Engine.RelationEnv) {rule : RewriteRule} {spec : RuleBindingSpec}
    {free : FreeTypeContext} {ambient : List TypeExpr} {rootType : TypeExpr}
    (schemaTyped : RestAwareTyping.HasType language (FreeTypeContext.ofList rule.typeContext)
      [] rule.left rootType)
    (rowChecks : ∀ binderPrefix (row : MetavariableOccurrence),
      row ∈ spec.occurrences → row.site = .left →
      RestAwareTyping.TypedOccurrenceAt language (FreeTypeContext.ofList rule.typeContext)
        [] rule.left rootType binderPrefix row.path row.name →
      RestAwareTyping.checkStoredRowArguments language (FreeTypeContext.ofList rule.typeContext)
        binderPrefix ambient spec row = true)
    {source representative : Pattern} {sourceFinal : ScopedRuleMatching.Assignment}
    (sourceGood : Admissible language free ambient rootType source)
    (collectionless : collectionFree rootType = true)
    (representativeGood : Admissible language free ambient rootType representative)
    (equivalent : ReferenceStep.Equivalent relEnv language source representative)
    (matched : GeneralScopedMatch.Matches rule spec ambient.length .left [] 0
      [] rule.left representative sourceFinal) :
    ∃ spelling final,
      spelling ∈ presentAt language free (FreeTypeContext.ofList rule.typeContext)
        bag.category unitLabel [] [] rule.left (.original ambient rootType source .hole) ∧
      final ∈ matchAtWith (normalBodyComparison unitLabel) rule spec ambient.length .left [] 0
        [] rule.left spelling.target ∧
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) sourceFinal =
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) final ∧
      List.Forall₂ (fun (first second : String × ContextualValue) =>
        first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
          first.2.ambient = second.2.ambient ∧
            ReferenceStep.Equivalent relEnv language first.2.body second.2.body) sourceFinal final := by
  exact presentAt_source_match_covered laws rows aligned valid relEnv rfl
    (by
      intro binderPrefix row member atLeft typed
      simpa only [List.append_nil] using rowChecks binderPrefix row member atLeft typed)
    rule.left rfl rfl (.here schemaTyped.forget) schemaTyped ⟨sourceGood, collectionless⟩
    trivial rfl rfl representativeGood equivalent matched rfl .nil

#print axioms presentAt_rule_left_source_match_covered


set_option maxRecDepth 4096 in
/-- The real retained producer eventually publishes a source-covering
spelling from every interrupted prefix, with its original ordered capture
account. Completion follows from its own finite expansion tree. -/
theorem retained_completes_with_source_match
    {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (rows : ∀ row ∈ language.equations,
      row.premises = [] ∧ RowPattern row.left ∧ RowPattern row.right ∧
        ∀ bindings, normalForm (some unitLabel) (applyBindings bindings row.left) =
          normalForm (some unitLabel) (applyBindings bindings row.right))
    (aligned : ReferenceStep.EquationsAligned language) (valid : language.validate = [])
    (relEnv : Engine.RelationEnv)
    {free schemaFree : FreeTypeContext} {schemaBound ambient : List TypeExpr}
    {wholeSchema : Pattern} {rootType : TypeExpr}
    {rule : RewriteRule} {spec : RuleBindingSpec} {site : RulePatternSite}
    (siteSchema : sitePattern? rule site = some wholeSchema)
    (rowChecks : ∀ binderPrefix (row : MetavariableOccurrence),
      row ∈ spec.occurrences → row.site = site →
      RestAwareTyping.TypedOccurrenceAt language schemaFree schemaBound wholeSchema rootType
        binderPrefix row.path row.name →
      RestAwareTyping.checkStoredRowArguments language schemaFree
        (binderPrefix ++ schemaBound) ambient spec row = true)
    (schema : Pattern)
    {schemaContext : OneHoleContext} {locals : List TypeExpr} {expected : TypeExpr}
    {path : List Nat} {focus : Focus} {representative : Pattern}
    {firstInitial secondInitial firstFinal : ScopedRuleMatching.Assignment}
    (schemaAt : schemaContext.fill schema = wholeSchema)
    (address : path = contextAddress schemaContext)
    (selected : TypedAt language schemaFree schema schemaContext schemaBound rootType locals expected)
    (schemaTyped : RestAwareTyping.HasType language schemaFree locals schema expected)
    (good : focus.Valid language free bag.category unitLabel) (physical : focus.Physical)
    (context : focus.bound = locals ++ ambient) (role : focus.expected bag.category = expected)
    (representativeGood : Admissible language free (locals ++ ambient) expected representative)
    (equivalent : ReferenceStep.Equivalent relEnv language (focus.value unitLabel) representative)
    (matched : GeneralScopedMatch.Matches rule spec ambient.length site path locals.length
      firstInitial schema representative firstFinal)
    (initialNormal : CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstInitial =
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondInitial)
    (initialSource : List.Forall₂ (fun (first second : String × ContextualValue) =>
      first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
        first.2.ambient = second.2.ambient ∧
          ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstInitial secondInitial) :
    let parameters : Retained.Parameters :=
      {language, free, schemaFree, category := bag.category, unitLabel}
    ∀ interrupted, ∃ more spelling secondFinal,
      (Retained.run parameters more
        (Retained.run parameters interrupted (Retained.startAt locals path schema focus))).agenda = [] ∧
      spelling ∈ (Retained.run parameters more
        (Retained.run parameters interrupted (Retained.startAt locals path schema focus))).answers ∧
      spelling ∈ presentAt language free schemaFree bag.category unitLabel locals path schema focus ∧
      secondFinal ∈ matchAtWith (normalBodyComparison unitLabel) rule spec ambient.length site path
        locals.length secondInitial schema spelling.target ∧
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstFinal =
        CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondFinal ∧
      List.Forall₂ (fun (first second : String × ContextualValue) =>
        first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
          first.2.ambient = second.2.ambient ∧
            ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstFinal secondFinal := by
  let parameters : Retained.Parameters :=
    {language, free, schemaFree, category := bag.category, unitLabel}
  change ∀ interrupted, ∃ more spelling secondFinal,
    (Retained.run parameters more
      (Retained.run parameters interrupted (Retained.startAt locals path schema focus))).agenda = [] ∧
    spelling ∈ (Retained.run parameters more
      (Retained.run parameters interrupted (Retained.startAt locals path schema focus))).answers ∧
    spelling ∈ presentAt language free schemaFree bag.category unitLabel locals path schema focus ∧
    secondFinal ∈ matchAtWith (normalBodyComparison unitLabel) rule spec ambient.length site path
      locals.length secondInitial schema spelling.target ∧
    CanonicalBags.mapAssignment (normalForm (some unitLabel)) firstFinal =
      CanonicalBags.mapAssignment (normalForm (some unitLabel)) secondFinal ∧
    List.Forall₂ (fun (first second : String × ContextualValue) =>
      first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
        first.2.ambient = second.2.ambient ∧
          ReferenceStep.Equivalent relEnv language first.2.body second.2.body) firstFinal secondFinal
  obtain ⟨spelling, secondFinal, produced, compared, finalNormal, finalSource⟩ :=
    presentAt_source_match_covered laws rows aligned valid relEnv siteSchema rowChecks schema
      schemaAt address selected schemaTyped good physical context role representativeGood equivalent matched
      initialNormal initialSource
  have accepted : (Retained.startAt locals path schema focus).accepts parameters spelling :=
    (Retained.start_accepts_iff parameters locals path schema focus spelling).mpr produced
  intro interrupted
  have stillAccepted :
      (Retained.run parameters interrupted (Retained.startAt locals path schema focus)).accepts parameters spelling :=
    (Retained.run_accepts parameters interrupted (Retained.startAt locals path schema focus) spelling).mpr accepted
  obtain ⟨more, drained, exactAnswers⟩ := Retained.completes_with_exact_answers parameters
    (Retained.run parameters interrupted (Retained.startAt locals path schema focus))
  exact ⟨more, spelling, secondFinal, drained, (exactAnswers spelling).mpr stillAccepted,
    produced, compared, finalNormal, finalSource⟩

#print axioms retained_completes_with_source_match

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.DataRestControls

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted
open AlgebraFocus.RecursiveView

private def collapsedSubject : Pattern := normalForm (some "Z") subject

/-- The existing declared repeated-rest rule is covered even after both
child collection presentations collapse to units. Every interrupted retained
run finishes with a matching spelling and the original source capture account. -/
theorem collapsed_repeated_rest_retained_coverage (relEnv : Engine.RelationEnv) :
    let parameters : Retained.Parameters :=
      {language, free := FreeTypeContext.empty, schemaFree, category := "P", unitLabel := "Z"}
    ∀ interrupted, ∃ more spelling final,
      (Retained.run parameters more
        (Retained.run parameters interrupted
          (Retained.startAt [] [] schema (.original [] proc collapsedSubject .hole)))).agenda = [] ∧
      spelling ∈ (Retained.run parameters more
        (Retained.run parameters interrupted
          (Retained.startAt [] [] schema (.original [] proc collapsedSubject .hole)))).answers ∧
      spelling ∈ presentAt language FreeTypeContext.empty schemaFree "P" "Z" [] [] schema
        (.original [] proc collapsedSubject .hole) ∧
      final ∈ matchAtWith compare rule specification 0 .left [] 0 [] schema spelling.target ∧
      CanonicalBags.mapAssignment (normalForm (some "Z")) captured =
        CanonicalBags.mapAssignment (normalForm (some "Z")) final ∧
      List.Forall₂ (fun (first second : String × ContextualValue) =>
        first.1 = second.1 ∧ first.2.dependencies = second.2.dependencies ∧
          first.2.ambient = second.2.ambient ∧
            ReferenceStep.Equivalent relEnv language first.2.body second.2.body) captured final := by
  have subjectGood : Admissible language FreeTypeContext.empty [] proc subject :=
    ⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩
  let base := ContextualStep.engineBasePremises relEnv
  have normalizedGood : Admissible language FreeTypeContext.empty [] proc collapsedSubject :=
    normalized_admissible laws base subjectGood rfl
  have presentationGood : Admissible language FreeTypeContext.empty [] proc presentation :=
    ⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩
  obtain ⟨_, _, sourceMatched, oldEquivalent, _⟩ := repeated_rest_source_control relEnv
  have normalizedSound : ReferenceStep.Equivalent relEnv language subject collapsedSubject :=
    (ReferenceStep.equivalent_iff_unconditional
      (by intro row member; cases member) (by intro row member; cases member)).mp
      (source_equiv_normalForm laws base subjectGood rfl)
  have equivalent : ReferenceStep.Equivalent relEnv language collapsedSubject presentation :=
    .trans _ _ _ (.symm _ _ normalizedSound) oldEquivalent
  have rowChecks : ∀ binderPrefix (row : MetavariableOccurrence),
      row ∈ specification.occurrences → row.site = .left →
      RestAwareTyping.TypedOccurrenceAt language schemaFree [] schema proc binderPrefix row.path row.name →
      RestAwareTyping.checkStoredRowArguments language schemaFree binderPrefix [] specification row = true := by
    intro binderPrefix row member atLeft typed
    have choices : row = {name := "R", site := .left, path := [0, 0], arguments := []} ∨
        row = {name := "R", site := .left, path := [1, 0], arguments := []} := by
      simpa only [specification, List.mem_cons, List.not_mem_nil, or_false] using member
    rcases choices with rfl | rfl <;> rfl
  exact retained_completes_with_source_match laws (by intro row member; cases member)
    (by intro row member; cases member) (by cbv) relEnv
    (free := FreeTypeContext.empty) (schemaFree := schemaFree)
    (schemaBound := []) (ambient := []) (wholeSchema := schema) (rootType := proc)
    (rule := rule) (spec := specification) (site := .left)
    (schemaContext := .hole) (locals := []) (expected := proc) (path := [])
    (focus := .original [] proc collapsedSubject .hole) (representative := presentation)
    (firstInitial := []) (secondInitial := []) (firstFinal := captured) rfl
    (by
      intro binderPrefix row member atLeft typed
      simpa only [List.append_nil] using rowChecks binderPrefix row member atLeft typed)
    schema rfl rfl (.here rest_has_data_role.2.2.forget) rest_has_data_role.2.2
    ⟨normalizedGood, rfl⟩ trivial rfl rfl presentationGood equivalent sourceMatched rfl .nil

#print axioms collapsed_repeated_rest_retained_coverage

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.DataRestControls

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.LexicalReadout

open Mettapedia.OSLF.MeTTaIL Syntax CollectionLaws ContextualStep DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

/-- Every extracted native law comes from the profile's actual declaration.
Repeated declarations can suppress extraction, but cannot invent another law. -/
theorem declared_law_authority {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BagTheory language bag (some unitLabel))
    {law : CollectionLaws.Laws} (member : law ∈ CollectionLaws.declared language) :
    law = ⟨.hashBag, some unitLabel⟩ := by
  simp only [CollectionLaws.declared, List.mem_filterMap] at member
  obtain ⟨kind, _, selected⟩ := member
  split at selected
  next declaration filtered =>
    have inFilter : declaration ∈ language.terms.filter
        (fun rule => CollectionLaws.bareKind rule == some kind) := by
      rw [filtered]
      simp
    have authored := (List.mem_filter.mp inFilter).1
    have bare : CollectionLaws.bareKind declaration = some kind :=
      beq_iff_eq.mp (List.mem_filter.mp inFilter).2
    obtain ⟨parameterName, element, shape⟩ :
        ∃ parameterName element, declaration.bareParams = [.simple parameterName (.collection kind element)] := by
      unfold CollectionLaws.bareKind at bare
      split at bare
      next parameterName actual element shape =>
        cases Option.some.inj bare
        exact ⟨parameterName, element, shape⟩
      next => cases bare
    have ordinaryShape := (GrammarRule.bareParams_cons_iff _ _ _).mp shape |>.2
    obtain ⟨same, kindEq, _⟩ := laws.eq_bag_of_collectionParameter authored ordinaryShape
    subst declaration
    subst kind
    rw [laws.bagAlgebra] at selected
    change some (⟨.hashBag, some unitLabel⟩ : CollectionLaws.Laws) = some law at selected
    exact (Option.some.inj selected).symm
  next => cases selected

/-- The executable kind lookup retains the actual selected unit. -/
theorem selected_law_authority {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BagTheory language bag (some unitLabel))
    {kind : CollType} {law : CollectionLaws.Laws}
    (found : lawFor (CollectionLaws.declared language) kind = some law) :
    kind = .hashBag ∧ law = ⟨.hashBag, some unitLabel⟩ := by
  have same := declared_law_authority laws (List.mem_of_find?_eq_some found)
  exact ⟨(lawFor_kind found).symm.trans (congrArg CollectionLaws.Laws.kind same), same⟩

private theorem splice_other {unitLabel : String} {pattern : Pattern}
    (notBag : ¬ IsBagNode pattern) (notUnit : pattern ≠ .apply unitLabel []) :
    CollectionLaws.splice ⟨.hashBag, some unitLabel⟩ pattern = [pattern] := by
  cases pattern with
  | collection kind elements rest =>
      cases kind <;> cases rest <;> first
        | rfl
        | exact (notBag ⟨elements,rfl⟩).elim
  | apply label arguments =>
      cases arguments with
      | nil =>
          have different : label ≠ unitLabel := by
            intro same
            subst label
            exact notUnit rfl
          simp [CollectionLaws.splice, Ne.symm different]
      | cons => rfl
  | _ => rfl

private theorem splice_path {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory language bag (some unitLabel))
    {base : BasePremiseEvaluator} {free : FreeTypeContext} {bound : List TypeExpr}
    {expected : TypeExpr} (collectionless : collectionFree expected = true) :
    ∀ (todo done : List Pattern),
      Admissible language free bound expected (.collection .hashBag (done ++ todo) none) →
      Path base language (.collection .hashBag (done ++ todo) none)
        (.collection .hashBag
          (done ++ todo.flatMap (CollectionLaws.splice ⟨.hashBag, some unitLabel⟩)) none)
  | [], _, _ => by simpa using Relation.ReflTransGen.refl
  | item :: todo, done, good => by
      by_cases nested : IsBagNode item
      · obtain ⟨inner, rfl⟩ := nested
        have first := path_of_derived (base := base)
          (DerivedInstance.flatten laws.bagAlgebraRule rfl
            (sortedAt_of_admissible laws good collectionless))
        have next := path_admissible laws first good collectionless
        have later := splice_path (base := base) laws collectionless todo (done ++ inner) next
        simpa [CollectionLaws.splice, List.append_assoc] using first.trans later
      · by_cases isUnit : item = .apply unitLabel []
        · subst item
          have first := path_of_derived (base := base)
            (DerivedInstance.unitElim laws.bagAlgebraRule rfl
              (sortedAt_of_admissible laws good collectionless))
          have next := path_admissible laws first good collectionless
          have later := splice_path (base := base) laws collectionless todo done next
          simpa [CollectionLaws.splice] using first.trans later
        · have regrouped : done ++ item :: todo = (done ++ [item]) ++ todo := by simp
          have later := splice_path (base := base) laws collectionless todo (done ++ [item]) (regrouped ▸ good)
          simpa [splice_other nested isUnit, List.append_assoc] using later

/-- The actual native flatten/unit traversal follows forward source laws
on the profile's admissible collection-free fibre. Unused caller types are
not restricted by a global free-name or bound-context approximation. -/
theorem normalize_path {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory language bag (some unitLabel)) (base : BasePremiseEvaluator)
    (pattern : Pattern) : ∀ {free : FreeTypeContext} {bound : List TypeExpr} {expected : TypeExpr},
    Admissible language free bound expected pattern → collectionFree expected = true →
      Path base language pattern (CollectionLaws.normalize (CollectionLaws.declared language) pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro free bound expected _ _
      simpa [CollectionLaws.normalize] using Relation.ReflTransGen.refl
  | hfvar identifier =>
      intro free bound expected _ _
      simpa [CollectionLaws.normalize] using Relation.ReflTransGen.refl
  | happly label arguments recurse =>
      intro free bound expected good collectionless
      rw [CollectionLaws.normalize]
      obtain ⟨declaration, authored, _, notBare, _, argumentsTyped⟩ := hasType_apply_inversion good.typed
      have different : declaration ≠ bag := by
        rintro rfl
        obtain ⟨parameterName, shape⟩ := laws.bareShape
        exact notBare ⟨parameterName, .hashBag, .base _, shape⟩
      have paths : ∀ argument ∈ arguments,
          Path base language argument (CollectionLaws.normalize (CollectionLaws.declared language) argument) := by
        intro argument member
        obtain ⟨before, after, rfl⟩ := List.append_of_mem member
        obtain ⟨beforeParameters, parameter, afterParameters, parameterExpected, parametersEq, _, _, _, parameterType,
          argumentTyped, _⟩ := ArgumentsHaveTypes.append_cons_split argumentsTyped
        have expectedFree := collectionFree_parameterType
          (laws.otherParameters declaration authored different parameter (by rw [parametersEq]; simp)) parameterType
        have canonical := good.canonical
        have object := good.object
        simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_iff] at canonical
        simp only [isObjectPattern, isObjectPatternList_iff] at object
        exact recurse argument member ⟨argumentTyped, canonical argument member, object argument member⟩ expectedFree
      simpa using path_map (base := base) (language := language) (.apply label)
        (fun before after => .apply label before .hole after) (fun _ _ _ => rfl)
        (CollectionLaws.normalize (CollectionLaws.declared language)) [] arguments paths
  | hlambda display body recurse =>
      intro free bound expected good collectionless
      have typed := good.typed
      cases typed with
      | @lambda _ _ _ domain codomain bodyTyped =>
          simp only [collectionFree, Bool.and_eq_true] at collectionless
          have canonical := good.canonical
          have object := good.object
          simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
          simp only [isObjectPattern] at object
          have inner := recurse ⟨bodyTyped, canonical.2, object⟩ collectionless.2
          simpa [CollectionLaws.normalize, OneHoleContext.fill] using path_fill (.lambda display .hole) inner
  | hmultiLambda arity display body recurse =>
      intro free bound expected good collectionless
      have typed := good.typed
      cases typed with
      | @multiLambda _ _ _ _ domain codomain bodyTyped =>
          simp only [collectionFree, Bool.and_eq_true] at collectionless
          have canonical := good.canonical
          have object := good.object
          simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
          simp only [isObjectPattern] at object
          have inner := recurse ⟨bodyTyped, canonical.2, object⟩ collectionless.2
          simpa [CollectionLaws.normalize, OneHoleContext.fill] using path_fill (.multiLambda arity display .hole) inner
  | hsubst body replacement _ _ =>
      intro free bound expected good _
      have object := good.object
      simp [isObjectPattern] at object
  | hcollection kind elements rest recurse =>
      intro free bound expected good collectionless
      obtain ⟨rfl, rfl, elementsTyped⟩ := bag_typing laws.toBareBagPresentation good.typed collectionless
      have object := good.object
      simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_iff_eq_none] at object
      obtain ⟨rfl, objectElements⟩ := object
      have canonical := good.canonical
      simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_iff] at canonical
      have paths : ∀ element ∈ elements,
          Path base language element (CollectionLaws.normalize (CollectionLaws.declared language) element) := by
        intro element member
        exact recurse element member
          ⟨elementsHaveType_iff.mp elementsTyped element member, canonical element member,
            isObjectPatternList_iff.mp objectElements element member⟩ rfl
      have inside := path_map (base := base) (language := language)
        (fun items => .collection .hashBag items none)
        (fun before after => .collection .hashBag before .hole after none)
        (fun _ _ _ => rfl) (CollectionLaws.normalize (CollectionLaws.declared language)) [] elements paths
      simp only [List.nil_append] at inside
      have afterInside := path_admissible laws inside good rfl
      rw [CanonicalBags.normalize_collection]
      cases found : lawFor (CollectionLaws.declared language) .hashBag with
      | none => simpa only [found] using inside
      | some law =>
          have same := (selected_law_authority laws.toBagTheory found).2
          subst law
          have afterSplice := splice_path (base := base) laws rfl
            (elements.map (CollectionLaws.normalize (CollectionLaws.declared language))) [] afterInside
          exact inside.trans (by simpa only [List.nil_append] using afterSplice)

/-- Every collection node on the typed fibre carries its actual declaration
and collection-data type evidence for the source's intrinsic kind laws. -/
theorem source_collections {language : LanguageDef} {bag : GrammarRule} {unit : Option String}
    (laws : BareBagTheory language bag unit) (pattern : Pattern) :
    ∀ {free : FreeTypeContext} {bound : List TypeExpr} {expected : TypeExpr},
      Admissible language free bound expected pattern → collectionFree expected = true →
        ReferenceStep.SourceCollections language pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _ _ _ _ _; exact .bvar index
  | hfvar identifier => intro _ _ _ _ _; exact .fvar identifier
  | happly label arguments recurse =>
      intro free bound expected good collectionless
      obtain ⟨declaration, authored, _, notBare, _, argumentsTyped⟩ := hasType_apply_inversion good.typed
      have different : declaration ≠ bag := by
        rintro rfl
        obtain ⟨parameterName, shape⟩ := laws.bareShape
        exact notBare ⟨parameterName, .hashBag, .base _, shape⟩
      apply ReferenceStep.SourceCollections.apply
      intro argument member
      obtain ⟨before, after, rfl⟩ := List.append_of_mem member
      obtain ⟨beforeParameters, parameter, afterParameters, parameterExpected, parametersEq, _, _, _, parameterType,
        argumentTyped, _⟩ := ArgumentsHaveTypes.append_cons_split argumentsTyped
      have expectedFree := collectionFree_parameterType
        (laws.otherParameters declaration authored different parameter (by rw [parametersEq]; simp)) parameterType
      have canonical := good.canonical
      have object := good.object
      simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_iff] at canonical
      simp only [isObjectPattern, isObjectPatternList_iff] at object
      exact recurse argument member ⟨argumentTyped, canonical argument member, object argument member⟩ expectedFree
  | hlambda display body recurse =>
      intro free bound expected good collectionless
      have typed := good.typed
      cases typed with
      | @lambda _ _ _ domain codomain bodyTyped =>
          simp only [collectionFree, Bool.and_eq_true] at collectionless
          have canonical := good.canonical
          have object := good.object
          simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
          simp only [isObjectPattern] at object
          exact .lambda (recurse ⟨bodyTyped, canonical.2, object⟩ collectionless.2)
  | hmultiLambda arity display body recurse =>
      intro free bound expected good collectionless
      have typed := good.typed
      cases typed with
      | @multiLambda _ _ _ _ domain codomain bodyTyped =>
          simp only [collectionFree, Bool.and_eq_true] at collectionless
          have canonical := good.canonical
          have object := good.object
          simp only [Pattern.hasCanonicalBinderMetadata, Bool.and_eq_true] at canonical
          simp only [isObjectPattern] at object
          exact .multiLambda (recurse ⟨bodyTyped, canonical.2, object⟩ collectionless.2)
  | hsubst body replacement _ _ =>
      intro free bound expected good _
      have object := good.object
      simp [isObjectPattern] at object
  | hcollection kind elements rest recurse =>
      intro free bound expected good collectionless
      obtain ⟨rfl, rfl, elementsTyped⟩ := bag_typing laws.toBareBagPresentation good.typed collectionless
      have object := good.object
      simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_iff_eq_none] at object
      obtain ⟨rfl, objectElements⟩ := object
      have canonical := good.canonical
      simp only [Pattern.hasCanonicalBinderMetadata, hasCanonicalBinderMetadataList_iff] at canonical
      obtain ⟨_, declaration, declared, _, typed⟩ :=
        (sortedAt_of_admissible laws good rfl).collection_type_origin
      exact .collection (.inr ⟨declaration, List.mem_of_getElem? declared, typed⟩)
        (fun element member => recurse element member
          ⟨elementsHaveType_iff.mp elementsTyped element member, canonical element member,
            isObjectPatternList_iff.mp objectElements element member⟩ rfl)

private theorem canon_admissible {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {expected : TypeExpr} {pattern : Pattern}
    (good : Admissible language free bound expected pattern) :
    Admissible language free bound expected (CanonicalBags.canon pattern) := by
  have sorted : OpenPatternWellSorted language free bound expected pattern :=
    ⟨good.typed, good.canonical, good.object, good.typed.isWellScopedAt⟩
  have result := CanonicalBags.openPatternWellSorted_canon sorted
  exact ⟨result.1, result.2.1, result.2.2.1⟩

/-- The native lexical normal form is typed and source-equivalent on the
actual algebra fibre. Its numeric readout agrees with the existing section;
the two representatives need not be literally equal. -/
theorem lawNormal_readout {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory language bag (some unitLabel))
    (relEnv : Engine.RelationEnv) {free : FreeTypeContext} {bound : List TypeExpr}
    {expected : TypeExpr} {pattern : Pattern}
    (good : Admissible language free bound expected pattern) (collectionless : collectionFree expected = true) :
    Admissible language free bound expected
      (CanonicalBags.lawNormal (CollectionLaws.declared language) pattern) ∧
      ReferenceStep.Equivalent relEnv language pattern
        (CanonicalBags.lawNormal (CollectionLaws.declared language) pattern) ∧
      normalForm (some unitLabel) (CanonicalBags.lawNormal (CollectionLaws.declared language) pattern) =
        normalForm (some unitLabel) pattern := by
  let normalized := CollectionLaws.normalize (CollectionLaws.declared language) pattern
  have path := normalize_path laws (engineBasePremises relEnv) pattern good collectionless
  have normalizedGood : Admissible language free bound expected normalized := path_admissible laws path good collectionless
  have sourceNormalized : ReferenceStep.Equivalent relEnv language pattern normalized :=
    (ReferenceStep.equivalent_iff_unconditional
      (by intro row member; rw [laws.equationsEmpty] at member; cases member)
      (by intro row member; rw [laws.equationsEmpty] at member; cases member)).mp
        (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ path)
  have sourceCanonical : ReferenceStep.Equivalent relEnv language normalized (CanonicalBags.canon normalized) :=
    ReferenceStep.equivalent_of_same (source_collections laws normalized normalizedGood collectionless)
      (CanonicalBags.canon_idempotent normalized).symm
  have equivalent : ReferenceStep.Equivalent relEnv language pattern
      (CanonicalBags.lawNormal (CollectionLaws.declared language) pattern) :=
    .trans _ _ _ sourceNormalized sourceCanonical
  refine ⟨canon_admissible normalizedGood, equivalent, ?_⟩
  exact ((equationEquiv_iff_normalForm_eq laws (engineBasePremises relEnv) good
      (canon_admissible normalizedGood) collectionless).mp
    ((ReferenceStep.equivalent_iff_unconditional
      (by intro row member; rw [laws.equationsEmpty] at member; cases member)
      (by intro row member; rw [laws.equationsEmpty] at member; cases member)).mpr equivalent)).symm

#print axioms declared_law_authority
#print axioms selected_law_authority
#print axioms normalize_path
#print axioms source_collections
#print axioms lawNormal_readout

end Mettapedia.GSLT.LanguageDef.BagNormalForm.LexicalReadout

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.LexicalReadout

open Mettapedia.OSLF.MeTTaIL Syntax CollectionLaws ContextualStep DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

/-- Actual retained equation rows remain in the source. The native output
is a typed representative with the original numeric readout, not a second
authority for the source relation. -/
theorem source_readout {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (unconditional : ReferenceStep.UnconditionalEquations language)
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {expected : TypeExpr} {pattern : Pattern}
    (good : Admissible language free bound expected pattern) (collectionless : collectionFree expected = true) :
    Admissible language free bound expected
      (CanonicalBags.lawNormal (CollectionLaws.declared language) pattern) ∧
      ReferenceStep.Equivalent relEnv language pattern
        (CanonicalBags.lawNormal (CollectionLaws.declared language) pattern) ∧
      normalForm (some unitLabel) (CanonicalBags.lawNormal (CollectionLaws.declared language) pattern) =
        normalForm (some unitLabel) pattern := by
  have comparisonGood : Admissible {language with equations := []} free bound expected pattern :=
    ⟨good.typed.of_terms_subset (by intro declaration member; exact member), good.canonical, good.object⟩
  obtain ⟨comparisonTarget, _, readout⟩ :=
    BagNormalForm.LexicalReadout.lawNormal_readout laws relEnv comparisonGood collectionless
  have targetGood : Admissible language free bound expected
      (CanonicalBags.lawNormal (CollectionLaws.declared language) pattern) :=
    ⟨comparisonTarget.typed.of_terms_subset (by intro declaration member; exact member),
      comparisonTarget.canonical, comparisonTarget.object⟩
  have first := source_equiv_normalForm laws (engineBasePremises relEnv) good collectionless
  have second := source_equiv_normalForm laws (engineBasePremises relEnv) targetGood collectionless
  have equation : EquationEquiv (engineBasePremises relEnv) language pattern
      (CanonicalBags.lawNormal (CollectionLaws.declared language) pattern) :=
    .trans _ _ _ first (readout ▸ second.symm)
  exact ⟨targetGood, (ReferenceStep.equivalent_iff_unconditional unconditional aligned).mp equation, readout⟩

/-- A homogeneous data endpoint retains its outer collection. Opaque typed
data variables remain variables; they never acquire the scalar carrier role. -/
theorem data_source_readout {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (unconditional : ReferenceStep.UnconditionalEquations language)
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern}
    (good : Admissible language free bound (.collection .hashBag (.base bag.category)) pattern) :
    Admissible language free bound (.collection .hashBag (.base bag.category))
      (CanonicalBags.lawNormal (CollectionLaws.declared language) pattern) ∧
      ReferenceStep.Equivalent relEnv language pattern
        (CanonicalBags.lawNormal (CollectionLaws.declared language) pattern) ∧
      normalForm (some unitLabel) (CanonicalBags.lawNormal (CollectionLaws.declared language) pattern) =
        normalForm (some unitLabel) pattern := by
  have typed := good.typed
  cases typed with
  | bvar lookup =>
      simp only [CanonicalBags.lawNormal, CollectionLaws.normalize, CanonicalBags.canon]
      exact ⟨good, .refl _, trivial⟩
  | fvar lookup =>
      simp only [CanonicalBags.lawNormal, CollectionLaws.normalize, CanonicalBags.canon]
      exact ⟨good, .refl _, trivial⟩
  | @collection _ _ elements rest _ elementsTyped =>
      have closed : rest = none := by
        have object := good.object
        simp only [isObjectPattern, Bool.and_eq_true, Option.isNone_iff_eq_none] at object
        exact object.1
      subst rest
      obtain ⟨parameterName, shape⟩ := laws.bareShape
      have scalarGood : Admissible language free bound (.base bag.category)
          (.collection .hashBag elements none) :=
        ⟨HasType.collectionConstructor laws.bagAuthored shape elementsTyped, good.canonical, good.object⟩
      obtain ⟨targetGood, equivalent, readout⟩ := source_readout laws unconditional aligned relEnv scalarGood rfl
      obtain ⟨targetElements, targetShape⟩ : ∃ targetElements,
          CanonicalBags.lawNormal (CollectionLaws.declared language) (.collection .hashBag elements none) =
            .collection .hashBag targetElements none := by
        unfold CanonicalBags.lawNormal
        rw [CanonicalBags.normalize_collection]
        cases found : lawFor (CollectionLaws.declared language) .hashBag <;>
          simp only [CanonicalBags.canon_collection]
        all_goals exact ⟨_, rfl⟩
      rw [targetShape] at targetGood
      have comparisonTyped := targetGood.typed.of_terms_subset
        (target := {language with equations := []}) (by intro declaration member; exact member)
      obtain ⟨_, _, outputElements⟩ := bag_typing laws.toBareBagPresentation comparisonTyped rfl
      have dataTyped : HasType language free bound (.collection .hashBag targetElements none)
          (.collection .hashBag (.base bag.category)) :=
        .collection (outputElements.of_terms_subset (by intro declaration member; exact member))
      exact ⟨targetShape.symm ▸ ⟨dataTyped, targetGood.canonical, targetGood.object⟩, equivalent, readout⟩
  | subst _ _ =>
      have object := good.object
      simp [isObjectPattern] at object

#print axioms source_readout
#print axioms data_source_readout

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.LexicalReadout

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.LexicalReadout

open Mettapedia.OSLF.MeTTaIL Syntax CollectionLaws ContextualStep DerivedContexts PatternLexOrder
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

/-- Sort complete physical records by the native value order. -/
def sortTagged (occurrences : List SourceOccurrence) : List SourceOccurrence :=
  occurrences.mergeSort fun first second => lexLe (ser first.value) (ser second.value)

theorem sortTagged_perm (occurrences : List SourceOccurrence) :
    (sortTagged occurrences).Perm occurrences := List.mergeSort_perm _ _

/-- Value readout of the tagged sorter is the actual native value sorter. -/
theorem sortTagged_values (occurrences : List SourceOccurrence) :
    (sortTagged occurrences).map SourceOccurrence.value = sortLex (occurrences.map SourceOccurrence.value) := by
  have ordered : (sortTagged occurrences).Pairwise
      (fun first second => PatternLe first.value second.value) := by
    exact List.pairwise_mergeSort
      (le := fun first second : SourceOccurrence => lexLe (ser first.value) (ser second.value))
      (fun first second third earlier later => lexLe_trans _ _ _ earlier later)
      (fun first second => by simpa only [Bool.or_eq_true] using lexLe_total (ser first.value) (ser second.value)) occurrences
  exact List.Perm.eq_of_pairwise' (List.pairwise_map.mpr ordered)
    (sortLex_pairwise _) (((sortTagged_perm occurrences).map SourceOccurrence.value).trans (sortLex_perm _).symm)

/-- The same original syntax, address and zipper accompany the native value. -/
def nativeRecord (language : LanguageDef) (occurrence : SourceOccurrence) : SourceOccurrence :=
  {occurrence with value := CanonicalBags.lawNormal (CollectionLaws.declared language) occurrence.original}

/-- This readout starts from the actual source traversal and omits only the
already separate physical unit account. No new occurrence is constructed. -/
def occurrences (language : LanguageDef) (unitLabel : String) (source : Pattern) : List SourceOccurrence :=
  sortTagged ((componentOccurrences unitLabel source).map (nativeRecord language))

/-- Sorting retains each complete record, including distinct equal-token
addresses and its original typed replacement zipper. -/
theorem occurrences_account (language : LanguageDef) (unitLabel : String) (source : Pattern) :
    (occurrences language unitLabel source).Perm
      ((componentOccurrences unitLabel source).map (nativeRecord language)) :=
  sortTagged_perm _

theorem occurrences_source_account (language : LanguageDef) (unitLabel : String) (source : Pattern) :
    (((occurrences language unitLabel source).map fun occurrence =>
          (occurrence.original, occurrence.address, occurrence.context)) ++
        (unitOccurrences unitLabel source).map fun occurrence =>
          (occurrence.original, occurrence.address, occurrence.context)).Perm
      ((sourceOccurrences unitLabel source).map fun occurrence =>
        (occurrence.original, occurrence.address, occurrence.context)) := by
  have sorted := (occurrences_account language unitLabel source).map
    (fun occurrence => (occurrence.original, occurrence.address, occurrence.context))
  simp only [List.map_map, nativeRecord, Function.comp_def] at sorted
  have previous := (occurrence_account unitLabel source).map
    (fun occurrence => (occurrence.original, occurrence.address, occurrence.context))
  rw [List.map_append] at previous
  exact (sorted.append_right _).trans
    (((sortOccurrences_perm (componentOccurrences unitLabel source)).map
      (fun occurrence => (occurrence.original, occurrence.address, occurrence.context))).append_right _ |>.symm.trans previous)

/-- Numeric readout transports the complete native records to the original
numeric records by a real permutation, retaining every original tag. -/
theorem occurrences_numeric_account {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (unconditional : ReferenceStep.UnconditionalEquations language)
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source) :
    ((occurrences language unitLabel source).map fun occurrence =>
      {occurrence with value := normalForm (some unitLabel) occurrence.value}).Perm
      (normalizedOccurrences unitLabel source) := by
  have sorted := (occurrences_account language unitLabel source).map
    (fun occurrence => {occurrence with value := normalForm (some unitLabel) occurrence.value})
  have records :
      ((componentOccurrences unitLabel source).map (nativeRecord language)).map
          (fun occurrence => {occurrence with value := normalForm (some unitLabel) occurrence.value}) =
        componentOccurrences unitLabel source := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (componentOccurrences unitLabel source)]
    apply List.map_congr_left
    intro occurrence member
    have sourceMember : occurrence ∈ sourceOccurrences unitLabel source := List.mem_of_mem_filter member
    obtain ⟨originalGood, _, value, _, _⟩ := sourceOccurrences_sound laws source good occurrence sourceMember
    have readout := WithAuthoredEquations.LexicalReadout.source_readout
      laws unconditional aligned relEnv originalGood rfl |>.2.2
    cases occurrence
    simp only [nativeRecord, Function.comp_apply] at *
    simp only [readout, value, id_eq]
  rw [records] at sorted
  exact sorted.trans (sortOccurrences_perm _).symm

/-- Each sorted native record retains its original typed source zipper and
has a typed source-equivalent native value at that same caller role. -/
theorem occurrences_source_readout {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (unconditional : ReferenceStep.UnconditionalEquations language)
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {occurrence : SourceOccurrence} (member : occurrence ∈ occurrences language unitLabel source) :
    Admissible language free bound (.base bag.category) occurrence.original ∧
      Admissible language free bound (.base bag.category) occurrence.value ∧
      ReferenceStep.Equivalent relEnv language occurrence.original occurrence.value ∧
      occurrence.context.fill occurrence.original = source ∧
      GeneralTypedSites.contextAddress occurrence.context = occurrence.address ∧
      ∀ replacement, HasType language free bound replacement (.base bag.category) →
        HasType language free bound (occurrence.context.fill replacement) (.base bag.category) := by
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp
    ((occurrences_account language unitLabel source).mem_iff.mp member)
  have sourceMember := List.mem_of_mem_filter originalMember
  obtain ⟨originalGood, fill, _, address, replacement⟩ :=
    sourceOccurrences_sound laws source good original sourceMember
  obtain ⟨nativeGood, equivalent, _⟩ := WithAuthoredEquations.LexicalReadout.source_readout
    laws unconditional aligned relEnv originalGood rfl
  exact ⟨originalGood, nativeGood, equivalent, fill, address, replacement⟩

/-- Lexical sorting preserves distinct physical addresses independently of
whether some values coincide. -/
theorem occurrences_distinct (language : LanguageDef) (unitLabel : String) (source : Pattern) :
    ((occurrences language unitLabel source).map SourceOccurrence.address).Nodup := by
  have current := (occurrences_account language unitLabel source).map SourceOccurrence.address
  simp only [List.map_map, nativeRecord, Function.comp_def] at current
  have previous := sortOccurrences_addresses (componentOccurrences unitLabel source)
  have same : ((occurrences language unitLabel source).map SourceOccurrence.address).Perm
      ((normalizedOccurrences unitLabel source).map SourceOccurrence.address) :=
    current.trans previous.symm
  exact same.nodup_iff.mpr (normalizedOccurrences_distinct unitLabel source)

#print axioms sortTagged_perm
#print axioms occurrences_source_readout
#print axioms occurrences_distinct
#print axioms sortTagged_values
#print axioms occurrences_account
#print axioms occurrences_source_account
#print axioms occurrences_numeric_account

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.LexicalReadout

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.LexicalReadout.Controls

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

private def proc : TypeExpr := .base "P"
private def dataType : TypeExpr := .collection .hashBag proc
private def bag (items : List Pattern) : Pattern := .collection .hashBag items none
private def carrier : GrammarRule where
  label := "Par"
  category := "P"
  params := [.simple "items" dataType]
  syntaxPattern := []
  algebra? := some {flatten := true, unit := some "Z"}
private def language : LanguageDef where
  name := "LexicalReadout"
  types := [TypeDecl.plain "P"]
  terms := [
    {label := "Z", category := "P", params := [], syntaxPattern := []},
    {label := "W", category := "P", params := [], syntaxPattern := []}, carrier]
  equations := []
  rewrites := []
private def free : FreeTypeContext := fun identifier => if identifier == "" then some proc else none
private def source : Pattern := bag [.bvar 2, bag [.apply "Z" [], .fvar ""]]
private def lexical : Pattern := bag [.bvar 2, .fvar ""]
private def numeric : Pattern := bag [.fvar "", .bvar 2]
private theorem laws : BareBagTheory language carrier (some "Z") :=
  (bagTheory_of_check (by decide +kernel)).asBare rfl

/-- The real native declaration removes the unit and flattens nesting, but
uses a different order from the numeric source section. Both outputs retain
their actual typed source meaning. -/
theorem different_order_and_declared_unit (relEnv : Engine.RelationEnv) :
    CollectionLaws.declared language = [⟨.hashBag, some "Z"⟩] ∧
      CanonicalBags.lawNormal (CollectionLaws.declared language) source = lexical ∧
      normalForm (some "Z") source = numeric ∧ lexical ≠ numeric ∧
      Admissible language free [proc,proc,proc] proc lexical ∧
      ReferenceStep.Equivalent relEnv language source lexical ∧
      normalForm (some "Z") lexical = normalForm (some "Z") source := by
  have good : Admissible language free [proc,proc,proc] proc source :=
    ⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩
  have actual : CanonicalBags.lawNormal (CollectionLaws.declared language) source = lexical := by cbv
  obtain ⟨typed, equivalent, readout⟩ :=
    BagNormalForm.LexicalReadout.lawNormal_readout laws relEnv good rfl
  rw [actual] at typed equivalent readout
  exact ⟨by decide +kernel, actual, by cbv, by decide +kernel, typed, equivalent, readout⟩

/-- Empty collection-data readback remains a container even though its
numeric comparison representative is the scalar unit. -/
theorem unit_data_readback (relEnv : Engine.RelationEnv) :
    CanonicalBags.lawNormal (CollectionLaws.declared language) (bag [.apply "Z" []]) = bag [] ∧
      Admissible language FreeTypeContext.empty [] dataType (bag []) ∧
      ReferenceStep.Equivalent relEnv language (bag [.apply "Z" []]) (bag []) ∧
      normalForm (some "Z") (bag []) = .apply "Z" [] := by
  have good : Admissible language FreeTypeContext.empty [] dataType (bag [.apply "Z" []]) :=
    ⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩
  have actual : CanonicalBags.lawNormal (CollectionLaws.declared language) (bag [.apply "Z" []]) = bag [] := by cbv
  obtain ⟨typed, equivalent, _⟩ := data_source_readout (language := language) laws
    (by intro row member; cases member) (by intro row member; cases member) relEnv good
  rw [actual] at typed equivalent
  exact ⟨actual, typed, equivalent, by cbv⟩

/-- Singleton collapse is an authored source law beyond the native
flatten/unit normalizer. Equality of native representatives is not claimed
to decide the whole authored theory. -/
theorem singleton_presentation_separator (relEnv : Engine.RelationEnv) :
    ReferenceStep.Equivalent relEnv language (bag [.fvar ""]) (.fvar "") ∧
      CanonicalBags.lawNormal (CollectionLaws.declared language) (bag [.fvar ""]) ≠
        CanonicalBags.lawNormal (CollectionLaws.declared language) (.fvar "") := by
  have good : Admissible language free [] proc (bag [.fvar ""]) :=
    ⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩
  have sourceLaw : DerivedInstance language (bag [.fvar ""]) (.fvar "") :=
    .singleton laws.bagAlgebraRule rfl (sortedAt_of_admissible laws good rfl)
  exact ⟨.rel _ _ (.inContext .hole (.inr sourceLaw)), by cbv; intro impossible; cases impossible⟩

/-- A different nullary constructor remains a real component; only Z was
selected as the declared unit. -/
theorem wrong_unit_retained (relEnv : Engine.RelationEnv) :
    CanonicalBags.lawNormal (CollectionLaws.declared language) (bag [.apply "W" [], .fvar ""]) =
        bag [.fvar "", .apply "W" []] ∧
      ¬ ReferenceStep.Equivalent relEnv language (bag [.apply "W" [], .fvar ""]) (.fvar "") := by
  refine ⟨by cbv, ?_⟩
  intro equivalent
  have firstGood : Admissible language free [] proc (bag [.apply "W" [], .fvar ""]) :=
    ⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩
  have secondGood : Admissible language free [] proc (.fvar "") :=
    ⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩
  have same := (reference_equivalent_iff_normalForm_eq (language := language) laws (by intro row member; cases member)
    (by intro row member; cases member) relEnv firstGood secondGood rfl).mp equivalent
  have different : normalForm (some "Z") (bag [.apply "W" [], .fvar ""]) ≠
      normalForm (some "Z") (.fvar "") := by
    cbv
    intro impossible
    cases impossible
  exact different same

/-- Even this genuine bare algebra cannot license kind-global flattening
at an arbitrary nested collection-data role. The current source theorem
keeps its actual scalar/homogeneous-data roles explicit. -/
theorem nested_data_role_separator :
    Admissible language free [] (.collection .hashBag dataType) (bag [bag [.fvar ""]]) ∧
      CanonicalBags.lawNormal (CollectionLaws.declared language) (bag [bag [.fvar ""]]) = bag [.fvar ""] ∧
      ¬ HasType language free [] (bag [.fvar ""]) (.collection .hashBag dataType) := by
  refine ⟨⟨checkHasType_sound (by decide +kernel), by decide +kernel, by decide +kernel⟩,
    by cbv, ?_⟩
  intro typed
  have checked := checkHasType_complete_of_object typed (by decide +kernel)
  have rejected : checkHasType language free [] (bag [.fvar ""]) (.collection .hashBag dataType) = false := by decide +kernel
  rw [rejected] at checked
  cases checked

/-- Equal token values retain both physical addresses, while the actual
unit has its separate original address. -/
theorem duplicate_addresses_and_unit_account :
    ((AlgebraFocus.LexicalReadout.occurrences language "Z" (bag [.bvar 2, .bvar 2, .apply "Z" []])).map
      AlgebraFocus.SourceOccurrence.address) = [[0], [1]] ∧
      ((AlgebraFocus.unitOccurrences "Z" (bag [.bvar 2, .bvar 2, .apply "Z" []])).map
        AlgebraFocus.SourceOccurrence.address) = [[2]] := by cbv

#print axioms different_order_and_declared_unit
#print axioms unit_data_readback
#print axioms singleton_presentation_separator
#print axioms wrong_unit_retained
#print axioms nested_data_role_separator
#print axioms duplicate_addresses_and_unit_account

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.LexicalReadout.Controls

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.LexicalReadout

open Mettapedia.OSLF.MeTTaIL Syntax CollectionLaws ContextualStep DerivedContexts PatternLexOrder
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

/-- Every numeric reference allocation has an actual native-value tagged
allocation with the same groups, residual and original physical records. -/
theorem native_group_allocation (language : LanguageDef) {unitLabel : String} {source : Pattern}
    {count : Nat} {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (allocation : (groups,residual) ∈ groupedOccurrences count (normalizedOccurrences unitLabel source)) :
    (groups.map (List.map (nativeRecord language)), residual.map (nativeRecord language)) ∈
      groupedOccurrences count (occurrences language unitLabel source) := by
  obtain ⟨lengths,account⟩ := (mem_groupedOccurrences count).mp allocation
  apply (mem_groupedOccurrences count).mpr
  refine ⟨by simpa only [List.length_map] using lengths, ?_⟩
  have mapped := account.map (nativeRecord language)
  simp only [List.map_append, List.map_flatten] at mapped
  have before := (sortOccurrences_perm (componentOccurrences unitLabel source)).map (nativeRecord language)
  exact mapped.trans (before.trans (occurrences_account language unitLabel source).symm)

/-- Conversely, numeric readout of an actual native tagged allocation is
an actual numeric reference allocation, with no reuse of an equal token. -/
theorem numeric_group_allocation {language : LanguageDef} {bag : GrammarRule} {unitLabel : String}
    (laws : BareBagTheory {language with equations := []} bag (some unitLabel))
    (unconditional : ReferenceStep.UnconditionalEquations language)
    (aligned : ReferenceStep.EquationsAligned language) (relEnv : Engine.RelationEnv)
    {free : FreeTypeContext} {bound : List TypeExpr} {source : Pattern}
    (good : Admissible language free bound (.base bag.category) source)
    {count : Nat} {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (allocation : (groups,residual) ∈ groupedOccurrences count (occurrences language unitLabel source)) :
    (groups.map (List.map (fun occurrence =>
        {occurrence with value := normalForm (some unitLabel) occurrence.value})),
      residual.map (fun occurrence => {occurrence with value := normalForm (some unitLabel) occurrence.value})) ∈
      groupedOccurrences count (normalizedOccurrences unitLabel source) := by
  obtain ⟨lengths,account⟩ := (mem_groupedOccurrences count).mp allocation
  apply (mem_groupedOccurrences count).mpr
  refine ⟨by simpa only [List.length_map] using lengths, ?_⟩
  have mapped := account.map (fun occurrence =>
    {occurrence with value := normalForm (some unitLabel) occurrence.value})
  simp only [List.map_append, List.map_flatten] at mapped
  exact mapped.trans (occurrences_numeric_account laws unconditional aligned relEnv good)

/-- Every actual native grouping, including empty groups, exhausts the
original source records together with its separate physical unit account. -/
theorem native_group_source_account (language : LanguageDef) {unitLabel : String} {source : Pattern}
    {count : Nat} {groups : List (List SourceOccurrence)} {residual : List SourceOccurrence}
    (allocation : (groups,residual) ∈ groupedOccurrences count (occurrences language unitLabel source)) :
    (((groups.flatten ++ residual).map fun occurrence =>
          (occurrence.original, occurrence.address, occurrence.context)) ++
        (unitOccurrences unitLabel source).map fun occurrence =>
          (occurrence.original, occurrence.address, occurrence.context)).Perm
      ((sourceOccurrences unitLabel source).map fun occurrence =>
        (occurrence.original, occurrence.address, occurrence.context)) := by
  have selected := ((mem_groupedOccurrences count).mp allocation).2.map
    (fun occurrence => (occurrence.original, occurrence.address, occurrence.context))
  exact (selected.append_right _).trans (occurrences_source_account language unitLabel source)

#print axioms native_group_allocation
#print axioms numeric_group_allocation
#print axioms native_group_source_account

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.LexicalReadout

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.RoleAwareSourceControls

open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionLaws CanonicalBags.RoleAware
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

private def proc : TypeExpr := .base "P"
private def dataType : TypeExpr := .collection .hashBag proc
private def nestedType : TypeExpr := .collection .hashBag dataType
private def bag (elements : List Pattern) : Pattern := .collection .hashBag elements none
private def a : Pattern := .apply "A" []
private def b : Pattern := .apply "B" []
private def z : Pattern := .apply "Z" []
private def zero : GrammarRule where
  label := "Z"
  category := "P"
  params := []
  syntaxPattern := []
private def atomA : GrammarRule := {zero with label := "A"}
private def atomB : GrammarRule := {zero with label := "B"}
private def carrier : GrammarRule where
  label := "Par"
  category := "P"
  params := [.simple "items" dataType]
  syntaxPattern := []
  algebra? := some {flatten := true, unit := some "Z"}
private def wrapper : GrammarRule where
  label := "Box"
  category := "P"
  params := [.simple "data" nestedType, .simple "algebra" proc]
  syntaxPattern := []
  collectionRepresentation := .wrapped
private def language : LanguageDef where
  name := "RoleAwareSource"
  types := [TypeDecl.plain "P"]
  terms := [zero, atomA, atomB, carrier, wrapper]
  equations := []
  rewrites := []
private def dataInput : Pattern := bag [bag [a], bag [z,a]]
private def source : Pattern := .apply "Box" [dataInput, bag [bag [a,b], z]]
private def result : Pattern := .apply "Box" [dataInput, bag [a,b]]
private def subSource : Pattern := .subst (bag [bag [.bvar 0, .bvar 1], z]) a
private def subResult : Pattern := .subst (bag [.bvar 0, .bvar 1]) a

private theorem declared : CollectionLaws.declared language = [⟨.hashBag, some "Z"⟩] := by cbv
private theorem homogeneous : checkBareHomogeneous (CollectionLaws.declared language) language = true := by decide +kernel

private theorem carrier_algebra : AlgebraRule language carrier .hashBag ⟨true, some "Z"⟩ := by
  refine ⟨by decide +kernel, rfl, ⟨"items", rfl⟩, ?_⟩
  intro identifier selected
  cases Option.some.inj selected
  exact ⟨zero, by decide +kernel, rfl, rfl, rfl⟩

private theorem authorized : SourceAlgebras (CollectionLaws.declared language) language := by
  intro rule member kind parameter law shape found
  have choices : rule = zero ∨ rule = atomA ∨ rule = atomB ∨ rule = carrier ∨ rule = wrapper := by
    simpa only [language, List.mem_cons, List.not_mem_nil, or_false] using member
  have ordinaryShape := (GrammarRule.bareParams_cons_iff _ _ _).mp shape |>.2
  rcases choices with rfl | rfl | rfl | rfl | rfl
  · simp [zero] at ordinaryShape
  · simp [atomA, zero] at ordinaryShape
  · simp [atomB, zero] at ordinaryShape
  · cases kind <;> simp [carrier, dataType, proc] at ordinaryShape
    rw [declared] at found
    simp only [lawFor, List.find?_cons] at found
    cases found
    exact carrier_algebra
  · simp [wrapper] at ordinaryShape

private theorem literal_source (label : String) : ReferenceStep.SourceCollections language (.apply label []) :=
  .apply (by intro item member; cases member)

private theorem par_source {bound : List TypeExpr} {elements : List Pattern}
    (typed : HasType language FreeTypeContext.empty bound (bag elements) dataType)
    (children : ∀ item ∈ elements, ReferenceStep.SourceCollections language item) :
    ReferenceStep.SourceCollections language (bag elements) :=
  .collection (.inr ⟨carrier, by decide +kernel, .simple "items" dataType,
    by decide +kernel, proc, .here, FreeTypeContext.empty, bound, typed⟩) children

private theorem data_source {elements : List Pattern} {element : TypeExpr}
    (occurs : CollectionTypeOccurs .hashBag element nestedType)
    (typed : HasType language FreeTypeContext.empty [] (bag elements) (.collection .hashBag element))
    (children : ∀ item ∈ elements, ReferenceStep.SourceCollections language item) :
    ReferenceStep.SourceCollections language (bag elements) :=
  .collection (.inr ⟨wrapper, by decide +kernel, .simple "data" nestedType,
    by decide +kernel, element, occurs, FreeTypeContext.empty, [], typed⟩) children

private theorem data_eligible : ReferenceStep.SourceCollections language dataInput := by
  apply data_source (element := dataType) .here (checkHasType_sound (by decide +kernel))
  intro item member
  have choices : item = bag [a] ∨ item = bag [z,a] := by
    simpa only [dataInput, List.mem_cons, List.not_mem_nil, or_false] using member
  rcases choices with rfl | rfl
  · apply data_source (element := proc) (.element .here) (checkHasType_sound (by decide +kernel))
    intro item member
    obtain rfl := List.mem_singleton.mp member
    exact literal_source "A"
  · apply data_source (element := proc) (.element .here) (checkHasType_sound (by decide +kernel))
    intro item member
    rcases List.mem_cons.mp member with rfl | member
    · exact literal_source "Z"
    · obtain rfl := List.mem_singleton.mp member
      exact literal_source "A"

private theorem source_eligible : ReferenceStep.SourceCollections language source := by
  apply ReferenceStep.SourceCollections.apply
  intro item member
  have choices : item = dataInput ∨ item = bag [bag [a,b], z] := by
    simpa only [source, List.mem_cons, List.not_mem_nil, or_false] using member
  rcases choices with rfl | rfl
  · exact data_eligible
  · apply par_source (bound := []) (checkHasType_sound (by decide +kernel))
    intro item member
    rcases List.mem_cons.mp member with rfl | member
    · apply par_source (bound := []) (checkHasType_sound (by decide +kernel))
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact literal_source "A"
      · obtain rfl := List.mem_singleton.mp member
        exact literal_source "B"
    · obtain rfl := List.mem_singleton.mp member
      exact literal_source "Z"

/-- The genuine mixed signature keeps its nested data containers and their
unit-valued data, while the separate base-result algebra slot normalizes. -/
theorem mixed_data_and_algebra (relEnv : Engine.RelationEnv) :
    language.validate = [] ∧
      checkBareHomogeneous (CollectionLaws.declared language) language = true ∧
      HasType language FreeTypeContext.empty [] source proc ∧
      reduceAt (CollectionLaws.declared language) [] language FreeTypeContext.empty [] source proc = result ∧
      source ≠ result ∧
      HasType language FreeTypeContext.empty [] result proc ∧
      ReferenceStep.Equivalent relEnv language source result := by
  have typed : HasType language FreeTypeContext.empty [] source proc := checkHasType_sound (by decide +kernel)
  have actual : reduceAt (CollectionLaws.declared language) [] language FreeTypeContext.empty [] source proc = result := by cbv
  have targetTyped := reduceAt_hasType homogeneous [] source typed
  have equivalent := reduceAt_source_equivalent (relEnv := relEnv) homogeneous authorized [] source typed source_eligible
  rw [actual] at targetTyped equivalent
  exact ⟨by cbv, homogeneous, typed, actual, by decide +kernel, targetTyped, equivalent⟩

private theorem substitution_eligible : ReferenceStep.SourceCollections language subSource := by
  apply ReferenceStep.SourceCollections.subst
  · apply par_source (bound := [proc,proc]) (checkHasType_sound (by decide +kernel))
    intro item member
    rcases List.mem_cons.mp member with rfl | member
    · apply par_source (bound := [proc,proc]) (checkHasType_sound (by decide +kernel))
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact .bvar 0
      · obtain rfl := List.mem_singleton.mp member
        exact .bvar 1
    · obtain rfl := List.mem_singleton.mp member
      exact literal_source "Z"
  · exact literal_source "A"

/-- Pending substitution is handled in its actual domain extension, with
normalization under that scope and the original outer bound context retained. -/
theorem pending_substitution_scope (relEnv : Engine.RelationEnv) :
    HasType language FreeTypeContext.empty [proc] subSource proc ∧
      isObjectPattern subSource = false ∧
      reduceAt (CollectionLaws.declared language) [proc] language FreeTypeContext.empty [proc] subSource proc = subResult ∧
      HasType language FreeTypeContext.empty [proc] subResult proc ∧
      ReferenceStep.Equivalent relEnv language subSource subResult := by
  have typed : HasType language FreeTypeContext.empty [proc] subSource proc :=
    HasType.subst (domain := proc) (checkHasType_sound (by decide +kernel)) (checkHasType_sound (by decide +kernel))
  have actual : reduceAt (CollectionLaws.declared language) [proc] language FreeTypeContext.empty [proc] subSource proc = subResult := by cbv
  have targetTyped := reduceAt_hasType homogeneous [proc] subSource typed
  have equivalent := reduceAt_source_equivalent (relEnv := relEnv) homogeneous authorized [proc] subSource typed substitution_eligible
  rw [actual] at targetTyped equivalent
  exact ⟨typed, rfl, actual, targetTyped, equivalent⟩

#print axioms authorized
#print axioms mixed_data_and_algebra
#print axioms pending_substitution_scope

end Mettapedia.GSLT.LanguageDef.BagNormalForm.RoleAwareSourceControls

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.RoleAwareSourceControls

open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionLaws CanonicalBags.RoleAware
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

private def wrongUnit : GrammarRule := {zero with label := "Wrong", category := "Q"}
private def unlicensedCarrier : GrammarRule :=
  {carrier with algebra? := some {flatten := true, unit := some "Wrong"}}
private def unlicensedLanguage : LanguageDef :=
  {language with
    types := [TypeDecl.plain "P", TypeDecl.plain "Q"]
    terms := [atomA, atomB, wrongUnit, unlicensedCarrier]}
private def unlicensedSource : Pattern := bag [bag [a,b]]
private def unlicensedTarget : Pattern := bag [a,b]

private theorem unlicensed_no_algebra {rule : GrammarRule} {kind : CollType} {algebra : CollectionAlgebra} :
    ¬ AlgebraRule unlicensedLanguage rule kind algebra := by
  intro declaration
  have choices : rule = atomA ∨ rule = atomB ∨ rule = wrongUnit ∨ rule = unlicensedCarrier := by
    simpa only [unlicensedLanguage, List.mem_cons, List.not_mem_nil, or_false] using declaration.authored
  obtain ⟨parameter, shape⟩ := declaration.selfSorted
  rcases choices with rfl | rfl | rfl | rfl
  · simp [atomA, zero] at shape
  · simp [atomB, zero] at shape
  · simp [wrongUnit, zero] at shape
  · have declared := declaration.declared
    change some (⟨true, some "Wrong"⟩ : CollectionAlgebra) = some algebra at declared
    cases Option.some.inj declared
    obtain ⟨unitRule, member, labelled, sorted, _⟩ := declaration.unitAuthored "Wrong" rfl
    have choices : unitRule = atomA ∨ unitRule = atomB ∨ unitRule = wrongUnit ∨ unitRule = unlicensedCarrier := by
      simpa only [unlicensedLanguage, List.mem_cons, List.not_mem_nil, or_false] using member
    rcases choices with rfl | rfl | rfl | rfl
    · simp [atomA, zero] at labelled
    · simp [atomB, zero] at labelled
    · simp [wrongUnit, zero, unlicensedCarrier, carrier] at sorted
    · simp [unlicensedCarrier, carrier] at labelled

private theorem unlicensed_generator_intrinsic (relEnv : Engine.RelationEnv) {first second : Pattern}
    (generator : ReferenceStep.Generator relEnv unlicensedLanguage first second) :
    CanonicalBags.BagStep first second := by
  rcases generator with authored | derived
  · cases authored with
    | forward member _ _ _ => cases member
    | reverse member _ _ _ => cases member
    | declared member _ _ => cases member
    | premised member _ _ _ => cases member
  · cases derived with
    | bagPerm _ _ permutation => exact .permute rfl permutation
    | setPerm _ _ permutation => exact .permute rfl permutation
    | setDedup _ _ => exact .members fun value => by simp
    | flatten declaration _ _ => exact (unlicensed_no_algebra declaration).elim
    | singleton declaration _ _ => exact (unlicensed_no_algebra declaration).elim
    | unitElim declaration _ _ => exact (unlicensed_no_algebra declaration).elim
    | emptyUnit declaration _ _ => exact (unlicensed_no_algebra declaration).elim

private theorem unlicensed_equivalent_intrinsic (relEnv : Engine.RelationEnv) {first second : Pattern}
    (related : ReferenceStep.Equivalent relEnv unlicensedLanguage first second) :
    CanonicalBags.Same first second := by
  induction related with
  | rel _ _ step =>
      cases step with
      | inContext context generator => exact ((unlicensed_generator_intrinsic relEnv generator).fill context).canon_eq
  | refl => rfl
  | symm _ _ _ recurse => exact recurse.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- Structural validity and typing preservation do not authorize an algebra
whose selected unit has the wrong source category. The actual computed
flattening is refused by the original reference equation relation. -/
theorem wrong_unit_source_authority (relEnv : Engine.RelationEnv) :
    unlicensedLanguage.validate = [] ∧
      checkBareHomogeneous (CollectionLaws.declared unlicensedLanguage) unlicensedLanguage = true ∧
      HasType unlicensedLanguage FreeTypeContext.empty [] unlicensedSource proc ∧
      reduceAt (CollectionLaws.declared unlicensedLanguage) [] unlicensedLanguage
        FreeTypeContext.empty [] unlicensedSource proc = unlicensedTarget ∧
      HasType unlicensedLanguage FreeTypeContext.empty [] unlicensedTarget proc ∧
      ¬ SourceAlgebras (CollectionLaws.declared unlicensedLanguage) unlicensedLanguage ∧
      ¬ ReferenceStep.Equivalent relEnv unlicensedLanguage unlicensedSource unlicensedTarget := by
  refine ⟨by cbv, by decide +kernel, checkHasType_sound (by decide +kernel), by cbv,
    checkHasType_sound (by decide +kernel), ?_, ?_⟩
  · intro authorized
    have declaration := authorized unlicensedCarrier (by decide +kernel) .hashBag "items"
      (⟨.hashBag,some "Wrong"⟩ : CollectionLaws.Laws) rfl (by decide +kernel)
    exact unlicensed_no_algebra declaration
  · intro related
    have same := unlicensed_equivalent_intrinsic relEnv related
    have different : ¬ CanonicalBags.Same unlicensedSource unlicensedTarget := by
      unfold CanonicalBags.Same
      cbv
      intro impossible
      cases impossible
    exact different same

#print axioms wrong_unit_source_authority

end Mettapedia.GSLT.LanguageDef.BagNormalForm.RoleAwareSourceControls

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.RoleAwareSourceControls

open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionLaws CanonicalBags.RoleAware
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

/-- Typed data readback and source equality have separate jobs. Role-aware
traversal, even followed by intrinsic canonical sorting, keeps two distinct
data presentations which the actual declared unit law equates. -/
theorem data_unit_comparison_separation (relEnv : Engine.RelationEnv) :
    HasType language FreeTypeContext.empty [] (bag [z]) dataType ∧
      HasType language FreeTypeContext.empty [] (bag []) dataType ∧
      ReferenceStep.Equivalent relEnv language (bag [z]) (bag []) ∧
      reduceAt (CollectionLaws.declared language) [] language FreeTypeContext.empty [] (bag [z]) dataType = bag [z] ∧
      reduceAt (CollectionLaws.declared language) [] language FreeTypeContext.empty [] (bag []) dataType = bag [] ∧
      CanonicalBags.canon
        (reduceAt (CollectionLaws.declared language) [] language FreeTypeContext.empty [] (bag [z]) dataType) ≠
      CanonicalBags.canon
        (reduceAt (CollectionLaws.declared language) [] language FreeTypeContext.empty [] (bag []) dataType) := by
  have sourceLaw : DerivedInstance language (bag [z]) (bag []) :=
    .unitElim (pre := []) (post := []) carrier_algebra rfl
      ⟨FreeTypeContext.empty, [], checkHasType_sound (by decide +kernel)⟩
  refine ⟨checkHasType_sound (by decide +kernel), checkHasType_sound (by decide +kernel),
    .rel _ _ (.inContext .hole (.inr sourceLaw)), by cbv, by cbv, ?_⟩
  cbv
  intro impossible
  cases impossible

#print axioms data_unit_comparison_separation

end Mettapedia.GSLT.LanguageDef.BagNormalForm.RoleAwareSourceControls

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RoleAwareReadout

open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionLaws CanonicalBags.RoleAware DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Keep the submitted physical source record and normalize its value at
its actual caller role. This does not invent a new source zipper from the
normalized output or decide how an enclosing algebra splices the record. -/
def sourceRecord (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (occurrence : SourceOccurrence) : SourceOccurrence :=
  {occurrence with value := reduceAt laws domains language free bound occurrence.original expected}

theorem sourceRecord_account (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (occurrence : SourceOccurrence) :
    (sourceRecord laws domains language free bound expected occurrence).original = occurrence.original ∧
      (sourceRecord laws domains language free bound expected occurrence).address = occurrence.address ∧
      (sourceRecord laws domains language free bound expected occurrence).context = occurrence.context :=
  ⟨rfl, rfl, rfl⟩

theorem sourceRecords_address_account (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (occurrences : List SourceOccurrence) :
    (occurrences.map (sourceRecord laws domains language free bound expected)).map SourceOccurrence.address =
      occurrences.map SourceOccurrence.address := by
  simp only [List.map_map, Function.comp_def, sourceRecord]

/-- Replacement retains the exact typed occurrence, including the original
parameter choices and the full context extended by every enclosing binder. -/
theorem sourceRecord_typedAt {laws : List Laws} {language : LanguageDef} {free : FreeTypeContext}
    (checked : checkBareHomogeneous laws language = true) (domains : List TypeExpr)
    {rootBound bound : List TypeExpr} {rootType expected : TypeExpr} {occurrence : SourceOccurrence}
    (selected : TypedAt language free occurrence.original occurrence.context rootBound rootType bound expected) :
    TypedAt language free (sourceRecord laws domains language free bound expected occurrence).value
      occurrence.context rootBound rootType bound expected := by
  apply selected.replaceAt
  · intro context parameter represented
    exact BagNormalForm.represents_fill context
      (fun parameter represented => reduceAt_parameter_representation laws domains language free bound expected represented)
      parameter represented
  · exact reduceAt_hasType checked domains occurrence.original selected.focus_typed

/-- The actual source equation relation follows the original source frame.
It is independent of the occurrence's previous cached normal value. -/
theorem sourceRecord_source {laws : List Laws} {language : LanguageDef} {free : FreeTypeContext}
    {relEnv : Engine.RelationEnv}
    (checked : checkBareHomogeneous laws language = true) (authorized : SourceAlgebras laws language)
    (domains : List TypeExpr) {rootBound bound : List TypeExpr} {rootType expected : TypeExpr}
    {occurrence : SourceOccurrence}
    (selected : TypedAt language free occurrence.original occurrence.context rootBound rootType bound expected)
    (eligible : ReferenceStep.SourceCollections language occurrence.original) :
    ReferenceStep.Equivalent relEnv language (occurrence.context.fill occurrence.original)
      (occurrence.context.fill (sourceRecord laws domains language free bound expected occurrence).value) :=
  ReferenceStep.equivalent_fill occurrence.context
    (reduceAt_source_equivalent checked authorized domains occurrence.original selected.focus_typed eligible)

theorem sourceRecord_sourceCollections {laws : List Laws} {language : LanguageDef} {free : FreeTypeContext}
    (checked : checkBareHomogeneous laws language = true) (domains : List TypeExpr)
    (domainRoles : ∀ domain ∈ domains, SourceTypeOccurrences language domain)
    {rootBound bound : List TypeExpr} {rootType expected : TypeExpr} {occurrence : SourceOccurrence}
    (selected : TypedAt language free occurrence.original occurrence.context rootBound rootType bound expected)
    (eligible : ReferenceStep.SourceCollections language occurrence.original)
    (role : SourceTypeOccurrences language expected) :
    ReferenceStep.SourceCollections language
      (sourceRecord laws domains language free bound expected occurrence).value :=
  reduceAt_sourceCollections checked domains domainRoles occurrence.original selected.focus_typed eligible role

#print axioms sourceRecord_typedAt
#print axioms sourceRecord_source
#print axioms sourceRecord_sourceCollections
#print axioms sourceRecords_address_account

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RoleAwareReadout

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.RoleAwareSourceControls

open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionLaws CanonicalBags.RoleAware DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.BindingSyntax.CollectionEquationFamily
open WithAuthoredEquations.AlgebraFocus RoleAwareReadout

/-- The finite checker reconstructs the source authority from the actual
nonempty algebra row and its correctly sorted nullary unit. -/
theorem automatic_source_algebra_authority :
    checkSourceAlgebras (CollectionLaws.declared language) language = true ∧
      ∃ receipt, checkedSourceAlgebras? (CollectionLaws.declared language) language = some receipt := by
  refine ⟨by decide +kernel, ?_⟩
  exact (checkedSourceAlgebras?_exact _ _).mpr
    (checkSourceAlgebras_sound (by decide +kernel))

theorem automatic_wrong_unit_rejected :
    checkSourceAlgebras (CollectionLaws.declared unlicensedLanguage) unlicensedLanguage = false ∧
      checkedSourceAlgebras? (CollectionLaws.declared unlicensedLanguage) unlicensedLanguage = none := by
  have rejected : checkSourceAlgebras (CollectionLaws.declared unlicensedLanguage) unlicensedLanguage = false := by decide +kernel
  exact ⟨rejected, by simp only [checkedSourceAlgebras?, rejected, Bool.false_eq_true, dite_false]⟩

/-- The mixed nested-data output retains its actual declared collection type
occurrences, including unit-valued data, without reusing an existential sort. -/
theorem mixed_output_source_collections : ReferenceStep.SourceCollections language result := by
  have typed : HasType language FreeTypeContext.empty [] source proc := checkHasType_sound (by decide +kernel)
  have output := reduceAt_sourceCollections homogeneous [] (by intro domain member; cases member)
    source typed source_eligible (SourceTypeOccurrences.base language "P")
  have actual : reduceAt (CollectionLaws.declared language) [] language FreeTypeContext.empty [] source proc = result := by cbv
  exact actual ▸ output

theorem substitution_output_source_collections : ReferenceStep.SourceCollections language subResult := by
  have typed : HasType language FreeTypeContext.empty [proc] subSource proc :=
    HasType.subst (domain := proc) (checkHasType_sound (by decide +kernel)) (checkHasType_sound (by decide +kernel))
  have output := reduceAt_sourceCollections homogeneous [proc]
    (by intro domain member; cases List.mem_singleton.mp member; exact SourceTypeOccurrences.base language "P")
    subSource typed substitution_eligible (SourceTypeOccurrences.base language "P")
  have actual : reduceAt (CollectionLaws.declared language) [proc] language FreeTypeContext.empty [proc] subSource proc = subResult := by cbv
  exact actual ▸ output

private def algebraSlot : SourceOccurrence :=
  ⟨bag [bag [a,b],z], [1], .apply "Box" [dataInput] .hole [], bag [bag [a,b],z]⟩

private theorem algebraSlot_typed :
    TypedAt language FreeTypeContext.empty algebraSlot.original algebraSlot.context [] proc [] proc := by
  apply TypedAt.application (rule := wrapper) (beforeParams := [.simple "data" nestedType])
    (afterParams := []) (parameter := .simple "algebra" proc)
  · decide +kernel
  · intro bare
    have checked := (usesBareCollection?_eq_true_iff wrapper).mpr bare
    simp [usesBareCollection?, wrapper] at checked
  · exact checkArgumentsHaveTypes_sound_of
      (fun _ _ _ accepted => checkHasType_sound accepted) (by decide +kernel)
  · rfl
  · rfl
  · rfl
  · exact .here (checkHasType_sound (by decide +kernel))

/-- Normalizing the real algebra slot retains the same globally typed zipper,
its original address, and the surrounding nested-data argument. -/
theorem typed_original_algebra_slot (relEnv : Engine.RelationEnv) :
    (sourceRecord (CollectionLaws.declared language) [] language FreeTypeContext.empty [] proc algebraSlot).address = [1] ∧
      (sourceRecord (CollectionLaws.declared language) [] language FreeTypeContext.empty [] proc algebraSlot).context = algebraSlot.context ∧
      TypedAt language FreeTypeContext.empty
        (sourceRecord (CollectionLaws.declared language) [] language FreeTypeContext.empty [] proc algebraSlot).value
        algebraSlot.context [] proc [] proc ∧
      ReferenceStep.Equivalent relEnv language source result := by
  refine ⟨rfl, rfl, sourceRecord_typedAt homogeneous [] algebraSlot_typed, ?_⟩
  have sourceSlot : ReferenceStep.SourceCollections language algebraSlot.original := by
    have whole := source_eligible
    cases whole with
    | apply children =>
        exact children (bag [bag [a,b],z]) (List.mem_cons_of_mem _ List.mem_cons_self)
  have equivalent := sourceRecord_source (relEnv := relEnv) homogeneous
    (checkSourceAlgebras_sound automatic_source_algebra_authority.1) [] algebraSlot_typed sourceSlot
  have actual : sourceRecord (CollectionLaws.declared language) [] language FreeTypeContext.empty [] proc algebraSlot =
      {algebraSlot with value := bag [a,b]} := by cbv
  change ReferenceStep.Equivalent relEnv language (algebraSlot.context.fill algebraSlot.original)
    (algebraSlot.context.fill (sourceRecord (CollectionLaws.declared language) [] language
      FreeTypeContext.empty [] proc algebraSlot).value) at equivalent
  rw [actual] at equivalent
  exact equivalent

/-- Unit deletion changes output positions. Reusing the output index as the
source token address points at Z, whereas the two surviving equal tokens
came from the distinct original addresses 1 and 2. -/
theorem output_index_is_not_source_origin :
    reduceAt (CollectionLaws.declared language) [] language FreeTypeContext.empty [] (bag [z,a,a]) proc = bag [a,a] ∧
      reduceAt (CollectionLaws.declared language) [] language FreeTypeContext.empty [] (bag [z,a,a]) dataType = bag [z,a,a] ∧
      (sourceOccurrences "Z" (bag [z,a,a])).map SourceOccurrence.address = [[0],[1],[2]] ∧
      (sourceOccurrences "Z" (bag [z,a,a])).map SourceOccurrence.original = [z,a,a] ∧
      ((sourceOccurrences "Z" (bag [z,a,a]))[0]?).map SourceOccurrence.original ≠ some a := by
  refine ⟨by cbv, by cbv, by cbv, by cbv, ?_⟩
  decide +kernel

#print axioms automatic_source_algebra_authority
#print axioms automatic_wrong_unit_rejected
#print axioms mixed_output_source_collections
#print axioms substitution_output_source_collections
#print axioms typed_original_algebra_slot
#print axioms output_index_is_not_source_origin

end Mettapedia.GSLT.LanguageDef.BagNormalForm.RoleAwareSourceControls

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RoleAwareReadout

open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionLaws CanonicalBags.RoleAware DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- A real visit retains the existing physical source record and its caller
role. A missing role marks an unchecked argument held opaque. -/
structure TypedOrigin where
  source : SourceOccurrence
  bound : List TypeExpr
  expected : Option TypeExpr
  declaration : Option (Nat × GrammarRule) := none
  deriving Repr, DecidableEq

def TypedOrigin.underContext (context : OneHoleContext) (origin : TypedOrigin) : TypedOrigin :=
  {origin with source := origin.source.underContext context}

/-- A removed node retains both its original occurrence and the algebra
request which classified it. Source authority is checked independently. -/
structure AlgebraAdministration where
  origin : TypedOrigin
  declaration : Nat × GrammarRule
  law : Laws
  deriving Repr, DecidableEq

def AlgebraAdministration.underContext (context : OneHoleContext)
    (event : AlgebraAdministration) : AlgebraAdministration :=
  {event with origin := event.origin.underContext context}

/-- The source visits keep their order. Surviving output roots, discarded
unit nodes and flattened carrier nodes retain those original records.
An unchecked subtree is held opaque and is not labelled complete. -/
structure TaggedReduction where
  target : Pattern
  root : TypedOrigin
  children : List TypedOrigin
  below : List TypedOrigin
  visited : List TypedOrigin
  unitRemovals : List AlgebraAdministration
  carrierRemovals : List AlgebraAdministration
  complete : Bool
  deriving Repr, DecidableEq

def TaggedReduction.survivors (trace : TaggedReduction) : List TypedOrigin := trace.root :: trace.below

def TaggedReduction.underContext (context : OneHoleContext) (trace : TaggedReduction) : TaggedReduction :=
  {trace with
    root := trace.root.underContext context
    children := trace.children.map (TypedOrigin.underContext context)
    below := trace.below.map (TypedOrigin.underContext context)
    visited := trace.visited.map (TypedOrigin.underContext context)
    unitRemovals := trace.unitRemovals.map (AlgebraAdministration.underContext context)
    carrierRemovals := trace.carrierRemovals.map (AlgebraAdministration.underContext context)}

private def originAt (bound : List TypeExpr) (expected : Option TypeExpr)
    (declaration : Option (Nat × GrammarRule)) (source target : Pattern) : TypedOrigin :=
  ⟨⟨source, [], .hole, target⟩, bound, expected, declaration⟩

private def opaqueTrace (bound : List TypeExpr) (expected : Option TypeExpr)
    (source : Pattern) (complete : Bool := false) : TaggedReduction :=
  let root := originAt bound expected none source source
  ⟨source, root, [], [], [root], [], [], complete⟩

private def liftedChildren (frame : Nat → OneHoleContext) : Nat → List TaggedReduction → List TaggedReduction
  | _, [] => []
  | index, child :: children => child.underContext (frame index) :: liftedChildren frame (index + 1) children

private theorem liftedChildren_targets (frame : Nat → OneHoleContext) (index : Nat)
    (children : List TaggedReduction) :
    (liftedChildren frame index children).map TaggedReduction.target = children.map TaggedReduction.target := by
  induction children generalizing index with
  | nil => rfl
  | cons child children recurse =>
      simp only [liftedChildren, List.map_cons, TaggedReduction.underContext, recurse]

private def assembleTrace (bound : List TypeExpr) (expected : TypeExpr)
    (declaration : Option (Nat × GrammarRule)) (source target : Pattern)
    (children : List TaggedReduction) : TaggedReduction :=
  let root := originAt bound (some expected) declaration source target
  ⟨target, root, children.map TaggedReduction.root, children.flatMap TaggedReduction.survivors,
    root :: children.flatMap TaggedReduction.visited,
    children.flatMap TaggedReduction.unitRemovals, children.flatMap TaggedReduction.carrierRemovals,
    children.all TaggedReduction.complete⟩

private structure TaggedFrontier where
  values : List Pattern
  children : List TypedOrigin
  below : List TypedOrigin
  units : List AlgebraAdministration
  carriers : List AlgebraAdministration

private def spliceTagged (declaration : Nat × GrammarRule) (law : Laws)
    (child : TaggedReduction) : TaggedFrontier :=
  match child.target with
  | .collection actual elements none =>
      if actual = law.kind then
        ⟨elements, child.children, child.below, child.unitRemovals,
          child.carrierRemovals ++ [⟨child.root, declaration, law⟩]⟩
      else ⟨[child.target], [child.root], child.survivors, child.unitRemovals, child.carrierRemovals⟩
  | .apply label [] =>
      if law.unit = some label then
        ⟨[], [], child.below, child.unitRemovals ++ [⟨child.root, declaration, law⟩], child.carrierRemovals⟩
      else ⟨[child.target], [child.root], child.survivors, child.unitRemovals, child.carrierRemovals⟩
  | _ => ⟨[child.target], [child.root], child.survivors, child.unitRemovals, child.carrierRemovals⟩

private theorem spliceTagged_values (declaration : Nat × GrammarRule) (law : Laws)
    (child : TaggedReduction) : (spliceTagged declaration law child).values = CollectionLaws.splice law child.target := by
  cases shape : child.target with
  | collection actual elements rest =>
      cases rest with
      | none => simp only [spliceTagged, shape, CollectionLaws.splice]; split <;> rfl
      | some tail => simp only [spliceTagged, shape, CollectionLaws.splice]
  | apply label arguments =>
      cases arguments with
      | nil => simp only [spliceTagged, shape, CollectionLaws.splice]; split <;> rfl
      | cons head tail => simp only [spliceTagged, shape, CollectionLaws.splice]
  | _ => simp only [spliceTagged, shape, CollectionLaws.splice]

private def finishTagged (laws : List Laws) (declaration : Nat × GrammarRule)
    (kind : CollType) (children : List TaggedReduction) : TaggedFrontier :=
  match lawFor laws kind with
  | none => ⟨children.map TaggedReduction.target, children.map TaggedReduction.root,
      children.flatMap TaggedReduction.survivors,
      children.flatMap TaggedReduction.unitRemovals, children.flatMap TaggedReduction.carrierRemovals⟩
  | some law =>
      let fronts := children.map (spliceTagged declaration law)
      ⟨fronts.flatMap TaggedFrontier.values, fronts.flatMap TaggedFrontier.children,
        fronts.flatMap TaggedFrontier.below, fronts.flatMap TaggedFrontier.units,
        fronts.flatMap TaggedFrontier.carriers⟩

private theorem finishTagged_values (laws : List Laws) (declaration : Nat × GrammarRule)
    (kind : CollType) (children : List TaggedReduction) :
    (finishTagged laws declaration kind children).values =
      finishAlgebra laws kind (children.map TaggedReduction.target) := by
  unfold finishTagged finishAlgebra
  cases found : lawFor laws kind with
  | none => rfl
  | some law =>
      simp only [List.flatMap_map]
      apply List.flatMap_congr
      intro child member
      exact spliceTagged_values declaration law child

private def algebraTrace (laws : List Laws) (bound : List TypeExpr) (expected : TypeExpr)
    (declaration : Nat × GrammarRule) (source : Pattern) (kind : CollType) (rest : Option String)
    (children : List TaggedReduction) : TaggedReduction :=
  let front := finishTagged laws declaration kind children
  let target := Pattern.collection kind front.values rest
  let root := originAt bound (some expected) (some declaration) source target
  ⟨target, root, front.children, front.below, root :: children.flatMap TaggedReduction.visited,
    front.units, front.carriers, children.all TaggedReduction.complete⟩

mutual
  /-- Companion traversal of the actual role-aware reducer. Every origin is
  created at a source visit, then moved as a record; equality of output values
  is never used to reconstruct an original address. -/
  def reduceAtTagged (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef)
      (free : FreeTypeContext) (bound : List TypeExpr) (source : Pattern) (expected : TypeExpr) : TaggedReduction :=
    match source with
    | .bvar _ | .fvar _ => opaqueTrace bound (some expected) source true
    | .apply label arguments =>
        match applicationRule? domains language free bound expected label arguments with
        | none => opaqueTrace bound (some expected) source
        | some rule =>
            let children := liftedChildren (fun index => .apply label (arguments.take index) .hole
              (arguments.drop (index + 1))) 0
              (reduceArgumentsTagged laws domains language free bound arguments rule.params)
            assembleTrace bound expected (some (language.terms.idxOf rule, rule)) source
              (.apply label (children.map TaggedReduction.target)) children
    | .lambda display body =>
        match expected with
        | .arrow domain codomain =>
            let child := (reduceAtTagged laws domains language free (domain :: bound) body codomain).underContext
              (.lambda display .hole)
            assembleTrace bound expected none source (.lambda display child.target) [child]
        | _ => opaqueTrace bound (some expected) source
    | .multiLambda arity displays body =>
        match expected with
        | .arrow (.multiBinder domain) codomain =>
            let child := (reduceAtTagged laws domains language free (List.replicate arity domain ++ bound) body codomain).underContext
              (.multiLambda arity displays .hole)
            assembleTrace bound expected none source (.multiLambda arity displays child.target) [child]
        | _ => opaqueTrace bound (some expected) source
    | .subst body replacement =>
        match substitutionDomain? domains language free bound expected body replacement with
        | none => opaqueTrace bound (some expected) source
        | some domain =>
            let first := (reduceAtTagged laws domains language free (domain :: bound) body expected).underContext
              (.substBody .hole replacement)
            let second := (reduceAtTagged laws domains language free bound replacement domain).underContext
              (.substReplacement body .hole)
            assembleTrace bound expected none source (.subst first.target second.target) [first,second]
    | .collection kind elements rest =>
        match expected with
        | .collection actual element =>
            if actual = kind then
              let children := liftedChildren (fun index => .collection kind (elements.take index) .hole
                (elements.drop (index + 1)) rest) 0
                (reduceElementsTagged laws domains language free bound elements element)
              assembleTrace bound expected none source (.collection kind (children.map TaggedReduction.target) rest) children
            else opaqueTrace bound (some expected) source
        | _ =>
            match collectionRule? domains language free bound expected kind elements rest with
            | none => opaqueTrace bound (some expected) source
            | some rule =>
                match bareCollectionElementType? rule kind expected with
                | none => opaqueTrace bound (some expected) source
                | some element =>
                    let children := liftedChildren (fun index => .collection kind (elements.take index) .hole
                      (elements.drop (index + 1)) rest) 0
                      (reduceElementsTagged laws domains language free bound elements element)
                    algebraTrace laws bound expected (language.terms.idxOf rule, rule) source kind rest children
  termination_by sizeOf source

  def reduceArgumentsTagged (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef)
      (free : FreeTypeContext) (bound : List TypeExpr) : List Pattern → List TermParam → List TaggedReduction
    | [], _ => []
    | argument :: arguments, parameter :: parameters =>
        (match parameterType? parameter with
        | some expected => reduceAtTagged laws domains language free bound argument expected
        | none => opaqueTrace bound none argument) ::
          reduceArgumentsTagged laws domains language free bound arguments parameters
    | arguments, [] => arguments.map (fun argument => opaqueTrace bound none argument)
  termination_by arguments _ => sizeOf arguments

  def reduceElementsTagged (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef)
      (free : FreeTypeContext) (bound : List TypeExpr) : List Pattern → TypeExpr → List TaggedReduction
    | [], _ => []
    | element :: elements, expected => reduceAtTagged laws domains language free bound element expected ::
        reduceElementsTagged laws domains language free bound elements expected
  termination_by elements _ => sizeOf elements
end

private theorem reduceArgumentsTagged_targets_of
    (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (arguments : List Pattern) (parameters : List TermParam)
    (each : ∀ argument ∈ arguments, ∀ expected,
      (reduceAtTagged laws domains language free bound argument expected).target =
        reduceAt laws domains language free bound argument expected) :
    (reduceArgumentsTagged laws domains language free bound arguments parameters).map TaggedReduction.target =
      reduceArguments laws domains language free bound arguments parameters := by
  induction arguments generalizing parameters with
  | nil => simp only [reduceArgumentsTagged, reduceArguments, List.map_nil]
  | cons argument arguments recurse =>
      cases parameters with
      | nil => simp only [reduceArgumentsTagged, List.map_map, opaqueTrace, Function.comp_def, reduceArguments, List.map_id']
      | cons parameter parameters =>
          simp only [reduceArgumentsTagged, reduceArguments]
          cases type : parameterType? parameter with
          | none =>
              simp only [opaqueTrace, List.map_cons]
              exact congrArg (List.cons argument)
                (recurse parameters (fun value member expected => each value (.tail _ member) expected))
          | some expected =>
              simp only [List.map_cons, each argument (.head _) expected]
              exact congrArg (List.cons (reduceAt laws domains language free bound argument expected))
                (recurse parameters (fun value member expected => each value (.tail _ member) expected))

private theorem reduceElementsTagged_targets_of
    (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (elements : List Pattern) (expected : TypeExpr)
    (each : ∀ element ∈ elements,
      (reduceAtTagged laws domains language free bound element expected).target =
        reduceAt laws domains language free bound element expected) :
    (reduceElementsTagged laws domains language free bound elements expected).map TaggedReduction.target =
      reduceElements laws domains language free bound elements expected := by
  induction elements with
  | nil => simp only [reduceElementsTagged, reduceElements, List.map_nil]
  | cons element elements recurse =>
      simp only [reduceElementsTagged, reduceElements, List.map_cons, each element (.head _)]
      exact congrArg (List.cons (reduceAt laws domains language free bound element expected))
        (recurse (fun value member => each value (.tail _ member)))

/-- Erasing the companion origin account computes the actual existing
role-aware reduction. It does not define the reducer by its own reference. -/
theorem reduceAtTagged_target (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef)
    (free : FreeTypeContext) (source : Pattern) :
    ∀ bound expected, (reduceAtTagged laws domains language free bound source expected).target =
      reduceAt laws domains language free bound source expected := by
  induction source using Pattern.inductionOn with
  | hbvar index => intro bound expected; simp only [reduceAtTagged, reduceAt, opaqueTrace]
  | hfvar identifier => intro bound expected; simp only [reduceAtTagged, reduceAt, opaqueTrace]
  | happly label arguments recurse =>
      intro bound expected
      simp only [reduceAtTagged, reduceAt]
      cases selected : applicationRule? domains language free bound expected label arguments with
      | none => rfl
      | some rule =>
          simp only [assembleTrace, liftedChildren_targets]
          exact congrArg (Pattern.apply label)
            (reduceArgumentsTagged_targets_of laws domains language free bound arguments rule.params
              (fun argument member expected => recurse argument member bound expected))
  | hlambda display body recurse =>
      intro bound expected
      cases expected <;> simp [reduceAtTagged, reduceAt, opaqueTrace, assembleTrace, TaggedReduction.underContext, recurse]
  | hmultiLambda arity displays body recurse =>
      intro bound expected
      cases expected with
      | arrow domain codomain =>
          cases domain <;> simp [reduceAtTagged, reduceAt, opaqueTrace, assembleTrace, TaggedReduction.underContext, recurse]
      | _ => simp [reduceAtTagged, reduceAt, opaqueTrace]
  | hsubst body replacement bodyIH replacementIH =>
      intro bound expected
      simp only [reduceAtTagged, reduceAt]
      cases selected : substitutionDomain? domains language free bound expected body replacement with
      | none => rfl
      | some domain =>
          exact congrArg₂ Pattern.subst (bodyIH (domain :: bound) expected) (replacementIH bound domain)
  | hcollection kind elements rest recurse =>
      intro bound expected
      cases expected with
      | collection actual element =>
          by_cases same : actual = kind
          · simp only [reduceAtTagged, reduceAt, same, ↓reduceIte, assembleTrace, liftedChildren_targets]
            exact congrArg (fun values => Pattern.collection kind values rest)
              (reduceElementsTagged_targets_of laws domains language free bound elements element
                (fun value member => recurse value member bound element))
          · simp only [reduceAtTagged, reduceAt, same, ↓reduceIte, opaqueTrace]
      | base category =>
          simp only [reduceAtTagged, reduceAt]
          cases selected : collectionRule? domains language free bound (.base category) kind elements rest with
          | none => rfl
          | some rule =>
              dsimp only
              cases elementRead : bareCollectionElementType? rule kind (.base category) with
              | none => rfl
              | some element =>
                  simp only [algebraTrace, finishTagged_values, liftedChildren_targets]
                  exact congrArg (fun values => Pattern.collection kind (finishAlgebra laws kind values) rest)
                    (reduceElementsTagged_targets_of laws domains language free bound elements element
                      (fun value member => recurse value member bound element))
      | arrow domain codomain =>
          simp only [reduceAtTagged, reduceAt]
          cases selected : collectionRule? domains language free bound (.arrow domain codomain) kind elements rest with
          | none => rfl
          | some rule =>
              dsimp only
              cases elementRead : bareCollectionElementType? rule kind (.arrow domain codomain) with
              | none => rfl
              | some element =>
                  simp only [algebraTrace, finishTagged_values, liftedChildren_targets]
                  exact congrArg (fun values => Pattern.collection kind (finishAlgebra laws kind values) rest)
                    (reduceElementsTagged_targets_of laws domains language free bound elements element
                      (fun value member => recurse value member bound element))
      | multiBinder body =>
          simp only [reduceAtTagged, reduceAt]
          cases selected : collectionRule? domains language free bound (.multiBinder body) kind elements rest with
          | none => rfl
          | some rule =>
              dsimp only
              cases elementRead : bareCollectionElementType? rule kind (.multiBinder body) with
              | none => rfl
              | some element =>
                  simp only [algebraTrace, finishTagged_values, liftedChildren_targets]
                  exact congrArg (fun values => Pattern.collection kind (finishAlgebra laws kind values) rest)
                    (reduceElementsTagged_targets_of laws domains language free bound elements element
                      (fun value member => recurse value member bound element))

#print axioms reduceAtTagged_target

/-- The original source visit sequence is partitioned without changing any
record or multiplicity. Units and carrier administrations are not surviving
tokens and are not new logical derivations. -/
def TaggedReduction.SourceAccount (trace : TaggedReduction) : Prop :=
  trace.visited.Perm (trace.survivors ++ trace.unitRemovals.map AlgebraAdministration.origin ++
    trace.carrierRemovals.map AlgebraAdministration.origin)

private theorem opaqueTrace_account (bound : List TypeExpr) (expected : Option TypeExpr)
    (source : Pattern) (complete : Bool) : (opaqueTrace bound expected source complete).SourceAccount := by
  exact List.Perm.refl _

private theorem taggedAccount_underContext (context : OneHoleContext) {trace : TaggedReduction}
    (account : trace.SourceAccount) : (trace.underContext context).SourceAccount := by
  have mapped := account.map (TypedOrigin.underContext context)
  simpa only [TaggedReduction.SourceAccount, TaggedReduction.underContext,
    TaggedReduction.survivors, List.map_append, List.map_cons, List.map_map,
    Function.comp_def, AlgebraAdministration.underContext] using mapped

private theorem flatMap_partition_account {α : Type} (items : List α)
    (visited kept units carriers : α → List TypedOrigin)
    (each : ∀ item ∈ items, (visited item).Perm (kept item ++ units item ++ carriers item)) :
    (items.flatMap visited).Perm
      (items.flatMap kept ++ items.flatMap units ++ items.flatMap carriers) := by
  induction items with
  | nil => exact .refl _
  | cons item items recurse =>
      have first := each item (.head _)
      have rest := recurse (fun other member => each other (.tail _ member))
      apply List.perm_iff_count.mpr
      intro origin
      have firstCount := List.perm_iff_count.mp first origin
      have restCount := List.perm_iff_count.mp rest origin
      simp only [List.count_append, List.flatMap_cons] at firstCount restCount ⊢
      omega

private theorem assembleTrace_account (bound : List TypeExpr) (expected : TypeExpr)
    (declaration : Option (Nat × GrammarRule)) (source target : Pattern)
    (children : List TaggedReduction) (each : ∀ child ∈ children, child.SourceAccount) :
    (assembleTrace bound expected declaration source target children).SourceAccount := by
  have combined := flatMap_partition_account children TaggedReduction.visited TaggedReduction.survivors
    (fun child => child.unitRemovals.map AlgebraAdministration.origin)
    (fun child => child.carrierRemovals.map AlgebraAdministration.origin) each
  have rooted := combined.cons (originAt bound (some expected) declaration source target)
  simpa only [TaggedReduction.SourceAccount, TaggedReduction.survivors, assembleTrace,
    List.map_flatMap, List.cons_append] using rooted

private theorem spliceTagged_account (declaration : Nat × GrammarRule) (law : Laws)
    {child : TaggedReduction} (account : child.SourceAccount) :
    child.visited.Perm ((spliceTagged declaration law child).below ++
      (spliceTagged declaration law child).units.map AlgebraAdministration.origin ++
      (spliceTagged declaration law child).carriers.map AlgebraAdministration.origin) := by
  cases shape : child.target with
  | collection actual elements rest =>
      cases rest with
      | none =>
          simp only [spliceTagged, shape]
          split
          · apply List.perm_iff_count.mpr
            intro origin
            have count := List.perm_iff_count.mp account origin
            simp only [TaggedReduction.survivors, List.count_cons, List.count_append,
              List.map_append, List.map_cons, List.map_nil, List.count_nil] at count ⊢
            omega
          · exact account
      | some => simpa only [spliceTagged, shape, TaggedReduction.SourceAccount] using account
  | apply label arguments =>
      cases arguments with
      | nil =>
          simp only [spliceTagged, shape]
          split
          · apply List.perm_iff_count.mpr
            intro origin
            have count := List.perm_iff_count.mp account origin
            simp only [TaggedReduction.survivors, List.count_cons, List.count_append,
              List.map_append, List.map_cons, List.map_nil, List.count_nil] at count ⊢
            omega
          · exact account
      | cons => simpa only [spliceTagged, shape, TaggedReduction.SourceAccount] using account
  | _ => simpa only [spliceTagged, shape, TaggedReduction.SourceAccount] using account

private theorem finishTagged_account (laws : List Laws) (declaration : Nat × GrammarRule)
    (kind : CollType) (children : List TaggedReduction)
    (each : ∀ child ∈ children, child.SourceAccount) :
    (children.flatMap TaggedReduction.visited).Perm
      ((finishTagged laws declaration kind children).below ++
        (finishTagged laws declaration kind children).units.map AlgebraAdministration.origin ++
        (finishTagged laws declaration kind children).carriers.map AlgebraAdministration.origin) := by
  unfold finishTagged
  cases found : lawFor laws kind with
  | none =>
      simpa only [List.map_flatMap] using flatMap_partition_account children
        TaggedReduction.visited TaggedReduction.survivors
        (fun child => child.unitRemovals.map AlgebraAdministration.origin)
        (fun child => child.carrierRemovals.map AlgebraAdministration.origin) each
  | some law =>
      simpa only [List.flatMap_map, List.map_flatMap, Function.comp_def] using
        flatMap_partition_account children TaggedReduction.visited
          (fun child => (spliceTagged declaration law child).below)
          (fun child => (spliceTagged declaration law child).units.map AlgebraAdministration.origin)
          (fun child => (spliceTagged declaration law child).carriers.map AlgebraAdministration.origin)
          (fun child member => spliceTagged_account declaration law (each child member))

private theorem algebraTrace_account (laws : List Laws) (bound : List TypeExpr) (expected : TypeExpr)
    (declaration : Nat × GrammarRule) (source : Pattern) (kind : CollType) (rest : Option String)
    (children : List TaggedReduction) (each : ∀ child ∈ children, child.SourceAccount) :
    (algebraTrace laws bound expected declaration source kind rest children).SourceAccount := by
  have combined := finishTagged_account laws declaration kind children each
  have rooted := combined.cons (originAt bound (some expected) (some declaration) source
    (.collection kind (finishTagged laws declaration kind children).values rest))
  simpa only [TaggedReduction.SourceAccount, TaggedReduction.survivors, algebraTrace,
    List.cons_append] using rooted

private theorem liftedChildren_account (frame : Nat → OneHoleContext) (index : Nat)
    (children : List TaggedReduction) (each : ∀ child ∈ children, child.SourceAccount) :
    ∀ child ∈ liftedChildren frame index children, child.SourceAccount := by
  induction children generalizing index with
  | nil => simp only [liftedChildren, List.not_mem_nil, false_implies, implies_true]
  | cons child children recurse =>
      intro current member
      rcases List.mem_cons.mp member with rfl | member
      · exact taggedAccount_underContext (frame index) (each child (.head _))
      · exact recurse (index + 1) (fun other member => each other (.tail _ member)) current member

private theorem reduceArgumentsTagged_account_of
    (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (arguments : List Pattern) (parameters : List TermParam)
    (each : ∀ argument ∈ arguments, ∀ expected,
      (reduceAtTagged laws domains language free bound argument expected).SourceAccount) :
    ∀ child ∈ reduceArgumentsTagged laws domains language free bound arguments parameters, child.SourceAccount := by
  induction arguments generalizing parameters with
  | nil => simp only [reduceArgumentsTagged, List.not_mem_nil, false_implies, implies_true]
  | cons argument arguments recurse =>
      cases parameters with
      | nil =>
          simp only [reduceArgumentsTagged]
          intro child member
          obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
          exact opaqueTrace_account bound none value false
      | cons parameter parameters =>
          simp only [reduceArgumentsTagged]
          intro child member
          rcases List.mem_cons.mp member with rfl | member
          · cases type : parameterType? parameter with
            | none => exact opaqueTrace_account bound none argument false
            | some expected => exact each argument (.head _) expected
          · exact recurse parameters (fun value member expected => each value (.tail _ member) expected) child member

private theorem reduceElementsTagged_account_of
    (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (elements : List Pattern) (expected : TypeExpr)
    (each : ∀ element ∈ elements, (reduceAtTagged laws domains language free bound element expected).SourceAccount) :
    ∀ child ∈ reduceElementsTagged laws domains language free bound elements expected, child.SourceAccount := by
  induction elements with
  | nil => simp only [reduceElementsTagged, List.not_mem_nil, false_implies, implies_true]
  | cons element elements recurse =>
      intro child member
      simp only [reduceElementsTagged] at member
      rcases List.mem_cons.mp member with rfl | member
      · exact each element (.head _)
      · exact recurse (fun value member => each value (.tail _ member)) child member

/-- Every actual source visit is retained once in its original record: as a
surviving output node, an explicit unit removal or a flattened carrier node.
This conserves equal-token multiplicity and does not assign new identities. -/
theorem reduceAtTagged_source_account (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef)
    (free : FreeTypeContext) (source : Pattern) :
    ∀ bound expected, (reduceAtTagged laws domains language free bound source expected).SourceAccount := by
  induction source using Pattern.inductionOn with
  | hbvar index => intro bound expected; simpa only [reduceAtTagged] using opaqueTrace_account bound (some expected) (.bvar index) true
  | hfvar identifier => intro bound expected; simpa only [reduceAtTagged] using opaqueTrace_account bound (some expected) (.fvar identifier) true
  | happly label arguments recurse =>
      intro bound expected
      simp only [reduceAtTagged]
      cases selected : applicationRule? domains language free bound expected label arguments with
      | none => exact opaqueTrace_account bound (some expected) (.apply label arguments) false
      | some rule =>
          apply assembleTrace_account
          apply liftedChildren_account
          exact reduceArgumentsTagged_account_of laws domains language free bound arguments rule.params
            (fun argument member expected => recurse argument member bound expected)
  | hlambda display body recurse =>
      intro bound expected
      cases expected with
      | arrow domain codomain =>
          simp only [reduceAtTagged]
          apply assembleTrace_account
          intro child member
          cases List.mem_singleton.mp member
          exact taggedAccount_underContext _ (recurse (domain :: bound) codomain)
      | _ => simp only [reduceAtTagged]; exact opaqueTrace_account _ _ _ _
  | hmultiLambda arity displays body recurse =>
      intro bound expected
      cases expected with
      | arrow domain codomain =>
          cases domain with
          | multiBinder inner =>
              simp only [reduceAtTagged]
              apply assembleTrace_account
              intro child member
              cases List.mem_singleton.mp member
              exact taggedAccount_underContext _ (recurse (List.replicate arity inner ++ bound) codomain)
          | _ => simp only [reduceAtTagged]; exact opaqueTrace_account _ _ _ _
      | _ => simp only [reduceAtTagged]; exact opaqueTrace_account _ _ _ _
  | hsubst body replacement bodyIH replacementIH =>
      intro bound expected
      simp only [reduceAtTagged]
      cases selected : substitutionDomain? domains language free bound expected body replacement with
      | none => exact opaqueTrace_account _ _ _ _
      | some domain =>
          apply assembleTrace_account
          intro child member
          rcases List.mem_cons.mp member with rfl | member
          · exact taggedAccount_underContext _ (bodyIH (domain :: bound) expected)
          · cases List.mem_singleton.mp member
            exact taggedAccount_underContext _ (replacementIH bound domain)
  | hcollection kind elements rest recurse =>
      intro bound expected
      cases expected with
      | collection actual element =>
          simp only [reduceAtTagged]
          split
          · apply assembleTrace_account
            apply liftedChildren_account
            exact reduceElementsTagged_account_of laws domains language free bound elements element
              (fun value member => recurse value member bound element)
          · exact opaqueTrace_account _ _ _ _
      | base category =>
          simp only [reduceAtTagged]
          cases selected : collectionRule? domains language free bound (.base category) kind elements rest with
          | none => exact opaqueTrace_account _ _ _ _
          | some rule =>
              dsimp only
              cases shape : bareCollectionElementType? rule kind (.base category) with
              | none => exact opaqueTrace_account _ _ _ _
              | some element =>
                  apply algebraTrace_account
                  apply liftedChildren_account
                  exact reduceElementsTagged_account_of laws domains language free bound elements element
                    (fun value member => recurse value member bound element)
      | arrow domain codomain =>
          simp only [reduceAtTagged]
          cases selected : collectionRule? domains language free bound (.arrow domain codomain) kind elements rest with
          | none => exact opaqueTrace_account _ _ _ _
          | some rule =>
              dsimp only
              cases shape : bareCollectionElementType? rule kind (.arrow domain codomain) with
              | none => exact opaqueTrace_account _ _ _ _
              | some element =>
                  apply algebraTrace_account
                  apply liftedChildren_account
                  exact reduceElementsTagged_account_of laws domains language free bound elements element
                    (fun value member => recurse value member bound element)
      | multiBinder body =>
          simp only [reduceAtTagged]
          cases selected : collectionRule? domains language free bound (.multiBinder body) kind elements rest with
          | none => exact opaqueTrace_account _ _ _ _
          | some rule =>
              dsimp only
              cases shape : bareCollectionElementType? rule kind (.multiBinder body) with
              | none => exact opaqueTrace_account _ _ _ _
              | some element =>
                  apply algebraTrace_account
                  apply liftedChildren_account
                  exact reduceElementsTagged_account_of laws domains language free bound elements element
                    (fun value member => recurse value member bound element)

#print axioms reduceAtTagged_source_account

/-- The retained zipper and address point to this very source presentation.
No equality between normalized values is used to select the source point. -/
def TypedOrigin.Rooted (source : Pattern) (origin : TypedOrigin) : Prop :=
  origin.source.context.fill origin.source.original = source ∧
    origin.source.address = GeneralTypedSites.contextAddress origin.source.context

private theorem originAt_rooted (bound : List TypeExpr) (expected : Option TypeExpr)
    (declaration : Option (Nat × GrammarRule)) (source target : Pattern) :
    TypedOrigin.Rooted source (originAt bound expected declaration source target) := ⟨rfl,rfl⟩

private theorem rooted_underContext (context : OneHoleContext) {source : Pattern} {origin : TypedOrigin}
    (rooted : TypedOrigin.Rooted source origin) :
    TypedOrigin.Rooted (context.fill source) (origin.underContext context) := by
  refine ⟨?_, ?_⟩
  · simpa only [TypedOrigin.underContext, SourceOccurrence.underContext, OneHoleContext.fill_comp] using
      congrArg context.fill rooted.1
  · have address : GeneralTypedSites.contextAddress (context.comp origin.source.context) =
        GeneralTypedSites.contextAddress context ++ GeneralTypedSites.contextAddress origin.source.context := by
      induction context <;> simp_all only [OneHoleContext.comp, GeneralTypedSites.contextAddress,
        List.nil_append, List.cons_append]
    simpa only [TypedOrigin.underContext, SourceOccurrence.underContext, address] using
      congrArg (GeneralTypedSites.contextAddress context ++ ·) rooted.2

private theorem opaqueTrace_rooted (bound : List TypeExpr) (expected : Option TypeExpr)
    (source : Pattern) (complete : Bool) :
    ∀ origin ∈ (opaqueTrace bound expected source complete).visited, TypedOrigin.Rooted source origin := by
  intro origin member
  cases List.mem_singleton.mp member
  exact originAt_rooted bound expected none source source

private theorem liftedTrace_rooted (context : OneHoleContext) {source : Pattern} {trace : TaggedReduction}
    (each : ∀ origin ∈ trace.visited, TypedOrigin.Rooted source origin) :
    ∀ origin ∈ (trace.underContext context).visited, TypedOrigin.Rooted (context.fill source) origin := by
  intro origin member
  obtain ⟨old,present,rfl⟩ := List.mem_map.mp member
  exact rooted_underContext context (each old present)

private theorem raw_source_reconstruct {α : Type} {items : List α} {index : Nat} {item : α}
    (selected : items[index]? = some item) :
    items.take index ++ item :: items.drop (index + 1) = items := by
  obtain ⟨within, actual⟩ := List.getElem?_eq_some_iff.mp selected
  have account := List.take_append_drop index items
  rw [List.drop_eq_getElem_cons within, actual] at account
  exact account

private theorem liftedChildren_rooted {sources : List Pattern} {traces : List TaggedReduction}
    (aligned : List.Forall₂ (fun source trace =>
      ∀ origin ∈ trace.visited, TypedOrigin.Rooted source origin) sources traces)
    (frame : Nat → OneHoleContext) (start : Nat) (whole : Pattern)
    (fills : ∀ index source, sources[index]? = some source → (frame (start + index)).fill source = whole) :
    ∀ origin ∈ (liftedChildren frame start traces).flatMap TaggedReduction.visited,
      TypedOrigin.Rooted whole origin := by
  induction aligned generalizing start with
  | nil => simp only [liftedChildren, List.flatMap_nil, List.not_mem_nil, false_implies, implies_true]
  | @cons source trace sources traces head tail recurse =>
      intro origin member
      simp only [liftedChildren, List.flatMap_cons, List.mem_append] at member
      rcases member with earlier | later
      · have atHead := fills 0 source (by rfl)
        simp only [Nat.add_zero] at atHead
        exact atHead ▸ liftedTrace_rooted (frame start) head origin earlier
      · apply recurse (start + 1) ?_ origin later
        intro index source selected
        have found := fills (index + 1) source (by simpa only [List.getElem?_cons_succ] using selected)
        simpa only [Nat.add_assoc, Nat.add_comm 1] using found

private theorem reduceArgumentsTagged_rooted_of
    (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (arguments : List Pattern) (parameters : List TermParam)
    (each : ∀ argument ∈ arguments, ∀ expected,
      ∀ origin ∈ (reduceAtTagged laws domains language free bound argument expected).visited,
        TypedOrigin.Rooted argument origin) :
    List.Forall₂ (fun (source : Pattern) (trace : TaggedReduction) => ∀ origin ∈ trace.visited, TypedOrigin.Rooted source origin)
      arguments (reduceArgumentsTagged laws domains language free bound arguments parameters) := by
  induction arguments generalizing parameters with
  | nil => simpa only [reduceArgumentsTagged] using (List.Forall₂.nil : List.Forall₂
      (fun (source : Pattern) (trace : TaggedReduction) => ∀ origin ∈ trace.visited, TypedOrigin.Rooted source origin) [] [])
  | cons argument arguments recurse =>
      cases parameters with
      | nil =>
          simp only [reduceArgumentsTagged]
          apply List.forall₂_map_right_iff.mpr
          apply List.forall₂_same.mpr
          intro source member
          exact opaqueTrace_rooted bound none source false
      | cons parameter parameters =>
          simp only [reduceArgumentsTagged]
          refine List.Forall₂.cons ?_ (recurse parameters (fun value member expected => each value (.tail _ member) expected))
          cases actual : parameterType? parameter with
          | none => exact opaqueTrace_rooted bound none argument false
          | some expected => exact each argument (.head _) expected

private theorem reduceElementsTagged_rooted_of
    (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (elements : List Pattern) (expected : TypeExpr)
    (each : ∀ element ∈ elements,
      ∀ origin ∈ (reduceAtTagged laws domains language free bound element expected).visited,
        TypedOrigin.Rooted element origin) :
    List.Forall₂ (fun (source : Pattern) (trace : TaggedReduction) => ∀ origin ∈ trace.visited, TypedOrigin.Rooted source origin)
      elements (reduceElementsTagged laws domains language free bound elements expected) := by
  induction elements with
  | nil => simpa only [reduceElementsTagged] using (List.Forall₂.nil : List.Forall₂
      (fun (source : Pattern) (trace : TaggedReduction) => ∀ origin ∈ trace.visited, TypedOrigin.Rooted source origin) [] [])
  | cons element elements recurse =>
      simpa only [reduceElementsTagged] using List.Forall₂.cons (each element (.head _))
        (recurse (fun value member => each value (.tail _ member)))

private theorem assembleTrace_rooted (bound : List TypeExpr) (expected : TypeExpr)
    (declaration : Option (Nat × GrammarRule)) (source target : Pattern)
    (children : List TaggedReduction)
    (each : ∀ origin ∈ children.flatMap TaggedReduction.visited, TypedOrigin.Rooted source origin) :
    ∀ origin ∈ (assembleTrace bound expected declaration source target children).visited,
      TypedOrigin.Rooted source origin := by
  intro origin member
  rcases List.mem_cons.mp member with rfl | member
  · exact originAt_rooted bound (some expected) declaration source target
  · exact each origin member

private theorem algebraTrace_rooted (laws : List Laws) (bound : List TypeExpr) (expected : TypeExpr)
    (declaration : Nat × GrammarRule) (source : Pattern) (kind : CollType) (rest : Option String)
    (children : List TaggedReduction)
    (each : ∀ origin ∈ children.flatMap TaggedReduction.visited, TypedOrigin.Rooted source origin) :
    ∀ origin ∈ (algebraTrace laws bound expected declaration source kind rest children).visited,
      TypedOrigin.Rooted source origin := by
  intro origin member
  rcases List.mem_cons.mp member with rfl | member
  · exact originAt_rooted bound (some expected) (some declaration) source _
  · exact each origin member

/-- Every record in the full visit account has its actual original zipper
and address, including the records later classified as administration. -/
theorem reduceAtTagged_original_points (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef)
    (free : FreeTypeContext) (source : Pattern) :
    ∀ bound expected, ∀ origin ∈ (reduceAtTagged laws domains language free bound source expected).visited,
      TypedOrigin.Rooted source origin := by
  induction source using Pattern.inductionOn with
  | hbvar index => intro bound expected; simpa only [reduceAtTagged] using opaqueTrace_rooted bound (some expected) (.bvar index) true
  | hfvar identifier => intro bound expected; simpa only [reduceAtTagged] using opaqueTrace_rooted bound (some expected) (.fvar identifier) true
  | happly label arguments recurse =>
      intro bound expected
      simp only [reduceAtTagged]
      cases selected : applicationRule? domains language free bound expected label arguments with
      | none => exact opaqueTrace_rooted bound (some expected) (.apply label arguments) false
      | some rule =>
          apply assembleTrace_rooted
          apply liftedChildren_rooted
            (reduceArgumentsTagged_rooted_of laws domains language free bound arguments rule.params
              (fun argument member expected => recurse argument member bound expected))
          intro index source selected
          simpa only [Nat.zero_add, OneHoleContext.fill] using
            congrArg (Pattern.apply label) (raw_source_reconstruct selected)
  | hlambda display body recurse =>
      intro bound expected
      cases expected with
      | arrow domain codomain =>
          simp only [reduceAtTagged]
          apply assembleTrace_rooted
          simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, OneHoleContext.fill] using
            liftedTrace_rooted (.lambda display .hole) (recurse (domain :: bound) codomain)
      | _ => simp only [reduceAtTagged]; exact opaqueTrace_rooted _ _ _ _
  | hmultiLambda arity displays body recurse =>
      intro bound expected
      cases expected with
      | arrow domain codomain =>
          cases domain with
          | multiBinder inner =>
              simp only [reduceAtTagged]
              apply assembleTrace_rooted
              simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, OneHoleContext.fill] using
                liftedTrace_rooted (.multiLambda arity displays .hole) (recurse (List.replicate arity inner ++ bound) codomain)
          | _ => simp only [reduceAtTagged]; exact opaqueTrace_rooted _ _ _ _
      | _ => simp only [reduceAtTagged]; exact opaqueTrace_rooted _ _ _ _
  | hsubst body replacement bodyIH replacementIH =>
      intro bound expected
      simp only [reduceAtTagged]
      cases selected : substitutionDomain? domains language free bound expected body replacement with
      | none => exact opaqueTrace_rooted _ _ _ _
      | some domain =>
          apply assembleTrace_rooted
          intro origin member
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at member
          rcases member with first | second
          · exact liftedTrace_rooted (.substBody .hole replacement) (bodyIH (domain :: bound) expected) origin first
          · exact liftedTrace_rooted (.substReplacement body .hole) (replacementIH bound domain) origin second
  | hcollection kind elements rest recurse =>
      intro bound expected
      have collectionChildren : ∀ element, ∀ origin ∈
          (liftedChildren (fun index => .collection kind (elements.take index) .hole
            (elements.drop (index + 1)) rest) 0
            (reduceElementsTagged laws domains language free bound elements element)).flatMap TaggedReduction.visited,
          TypedOrigin.Rooted (.collection kind elements rest) origin := by
        intro element
        apply liftedChildren_rooted
          (reduceElementsTagged_rooted_of laws domains language free bound elements element
            (fun value member => recurse value member bound element))
        intro index source selected
        simpa only [Nat.zero_add, OneHoleContext.fill] using
          congrArg (fun values => Pattern.collection kind values rest) (raw_source_reconstruct selected)
      cases expected with
      | collection actual element =>
          simp only [reduceAtTagged]
          split
          · exact assembleTrace_rooted _ _ _ _ _ _ (collectionChildren element)
          · exact opaqueTrace_rooted _ _ _ _
      | base category =>
          simp only [reduceAtTagged]
          cases selected : collectionRule? domains language free bound (.base category) kind elements rest with
          | none => exact opaqueTrace_rooted _ _ _ _
          | some rule =>
              dsimp only
              cases shape : bareCollectionElementType? rule kind (.base category) with
              | none => exact opaqueTrace_rooted _ _ _ _
              | some element => exact algebraTrace_rooted _ _ _ _ _ _ _ _ (collectionChildren element)
      | arrow domain codomain =>
          simp only [reduceAtTagged]
          cases selected : collectionRule? domains language free bound (.arrow domain codomain) kind elements rest with
          | none => exact opaqueTrace_rooted _ _ _ _
          | some rule =>
              dsimp only
              cases shape : bareCollectionElementType? rule kind (.arrow domain codomain) with
              | none => exact opaqueTrace_rooted _ _ _ _
              | some element => exact algebraTrace_rooted _ _ _ _ _ _ _ _ (collectionChildren element)
      | multiBinder body =>
          simp only [reduceAtTagged]
          cases selected : collectionRule? domains language free bound (.multiBinder body) kind elements rest with
          | none => exact opaqueTrace_rooted _ _ _ _
          | some rule =>
              dsimp only
              cases shape : bareCollectionElementType? rule kind (.multiBinder body) with
              | none => exact opaqueTrace_rooted _ _ _ _
              | some element => exact algebraTrace_rooted _ _ _ _ _ _ _ _ (collectionChildren element)

#print axioms reduceAtTagged_original_points

private theorem trace_underContext_distinct (context : OneHoleContext) {trace : TaggedReduction}
    (distinct : (trace.visited.map (fun origin => origin.source.address)).Nodup) :
    ((trace.underContext context).visited.map (fun origin => origin.source.address)).Nodup := by
  have sourceDistinct : ((trace.visited.map TypedOrigin.source).map SourceOccurrence.address).Nodup := by
    simpa only [List.map_map, Function.comp_def] using distinct
  have rebased := underContext_distinct context sourceDistinct
  simpa only [TaggedReduction.underContext, TypedOrigin.underContext, List.map_map,
    Function.comp_def] using rebased

private theorem liftedChildren_address_range (frame : Nat → OneHoleContext) (start : Nat)
    (children : List TaggedReduction)
    (frames : ∀ index, index < children.length →
      GeneralTypedSites.contextAddress (frame (start + index)) = [start + index]) :
    ∀ origin ∈ (liftedChildren frame start children).flatMap TaggedReduction.visited,
      ∃ index suffix, start ≤ index ∧ index < start + children.length ∧ origin.source.address = index :: suffix := by
  induction children generalizing start with
  | nil => simp only [liftedChildren, List.flatMap_nil, List.not_mem_nil, false_implies, implies_true]
  | cons child children recurse =>
      intro origin member
      simp only [liftedChildren, List.flatMap_cons, List.mem_append] at member
      rcases member with earlier | later
      · obtain ⟨old, present, rfl⟩ := List.mem_map.mp earlier
        have headAddressRule := frames 0 (by simp only [List.length_cons]; omega)
        simp only [Nat.add_zero] at headAddressRule
        refine ⟨start, old.source.address, Nat.le_refl _, by simp only [List.length_cons]; omega, ?_⟩
        simp only [TypedOrigin.underContext, SourceOccurrence.underContext, headAddressRule, List.singleton_append]
      · obtain ⟨index,suffix,lower,upper,address⟩ := recurse (start + 1) (by
          intro index within
          have next := frames (index + 1) (by simp only [List.length_cons]; omega)
          simpa only [Nat.add_assoc, Nat.add_comm 1] using next) origin later
        exact ⟨index,suffix,by omega,by simp only [List.length_cons]; omega,address⟩

private theorem liftedChildren_distinct (frame : Nat → OneHoleContext) (start : Nat)
    (children : List TaggedReduction)
    (frames : ∀ index, index < children.length →
      GeneralTypedSites.contextAddress (frame (start + index)) = [start + index])
    (each : ∀ child ∈ children, (child.visited.map (fun origin => origin.source.address)).Nodup) :
    (((liftedChildren frame start children).flatMap TaggedReduction.visited).map
      (fun origin => origin.source.address)).Nodup := by
  induction children generalizing start with
  | nil => exact List.Pairwise.nil
  | cons child children recurse =>
      have nextFrames : ∀ index, index < children.length →
          GeneralTypedSites.contextAddress (frame (start + 1 + index)) = [start + 1 + index] := by
        intro index within
        have next := frames (index + 1) (by simp only [List.length_cons]; omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1] using next
      have headAddressRule := frames 0 (by simp only [List.length_cons]; omega)
      simp only [Nat.add_zero] at headAddressRule
      simp only [liftedChildren, List.flatMap_cons, List.map_append]
      refine List.nodup_append.mpr ⟨trace_underContext_distinct _ (each child (.head _)),
        recurse (start + 1) nextFrames (fun other member => each other (.tail _ member)), ?_⟩
      intro first firstMember second secondMember same
      obtain ⟨firstOrigin, firstPresent, firstRead⟩ := List.mem_map.mp firstMember
      obtain ⟨old, oldPresent, firstOriginEq⟩ := List.mem_map.mp firstPresent
      obtain ⟨secondOrigin, secondPresent, secondRead⟩ := List.mem_map.mp secondMember
      obtain ⟨index,suffix,lower,_,address⟩ := liftedChildren_address_range frame (start + 1) children nextFrames
        secondOrigin secondPresent
      have firstAddress : first = start :: old.source.address := by
        rw [← firstRead, ← firstOriginEq]
        simp only [TypedOrigin.underContext, SourceOccurrence.underContext, headAddressRule, List.singleton_append]
      have secondAddress : second = index :: suffix := secondRead.symm.trans address
      rw [firstAddress,secondAddress] at same
      have indices := (List.cons.inj same).1
      omega

private theorem rootedTrace_distinct (bound : List TypeExpr) (expected : TypeExpr)
    (declaration : Option (Nat × GrammarRule)) (source target : Pattern) (children : List TaggedReduction)
    (distinct : ((children.flatMap TaggedReduction.visited).map (fun origin => origin.source.address)).Nodup)
    (nonempty : ∀ origin ∈ children.flatMap TaggedReduction.visited, origin.source.address ≠ []) :
    ((assembleTrace bound expected declaration source target children).visited.map
      (fun origin => origin.source.address)).Nodup := by
  simp only [assembleTrace, List.map_cons, originAt, List.nodup_cons]
  refine ⟨?_,distinct⟩
  intro present
  obtain ⟨origin,member,empty⟩ := List.mem_map.mp present
  exact nonempty origin member empty

private theorem algebraRootedTrace_distinct (laws : List Laws) (bound : List TypeExpr) (expected : TypeExpr)
    (declaration : Nat × GrammarRule) (source : Pattern) (kind : CollType) (rest : Option String)
    (children : List TaggedReduction)
    (distinct : ((children.flatMap TaggedReduction.visited).map (fun origin => origin.source.address)).Nodup)
    (nonempty : ∀ origin ∈ children.flatMap TaggedReduction.visited, origin.source.address ≠ []) :
    ((algebraTrace laws bound expected declaration source kind rest children).visited.map
      (fun origin => origin.source.address)).Nodup := by
  simp only [algebraTrace, List.map_cons, originAt, List.nodup_cons]
  refine ⟨?_,distinct⟩
  intro present
  obtain ⟨origin,member,empty⟩ := List.mem_map.mp present
  exact nonempty origin member empty

private theorem reduceArgumentsTagged_length (laws : List Laws) (domains : List TypeExpr)
    (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr)
    (arguments : List Pattern) (parameters : List TermParam) :
    (reduceArgumentsTagged laws domains language free bound arguments parameters).length = arguments.length := by
  induction arguments generalizing parameters with
  | nil => simp only [reduceArgumentsTagged, List.length_nil]
  | cons argument arguments recurse =>
      cases parameters with
      | nil => simp only [reduceArgumentsTagged, List.length_map]
      | cons parameter parameters => simp only [reduceArgumentsTagged, List.length_cons, recurse]

private theorem reduceElementsTagged_length (laws : List Laws) (domains : List TypeExpr)
    (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr)
    (elements : List Pattern) (expected : TypeExpr) :
    (reduceElementsTagged laws domains language free bound elements expected).length = elements.length := by
  induction elements with
  | nil => simp only [reduceElementsTagged, List.length_nil]
  | cons element elements recurse => simp only [reduceElementsTagged, List.length_cons, recurse]

private theorem reduceArgumentsTagged_distinct_of
    (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (arguments : List Pattern) (parameters : List TermParam)
    (each : ∀ argument ∈ arguments, ∀ expected,
      ((reduceAtTagged laws domains language free bound argument expected).visited.map (fun origin => origin.source.address)).Nodup) :
    ∀ child ∈ reduceArgumentsTagged laws domains language free bound arguments parameters,
      (child.visited.map (fun origin => origin.source.address)).Nodup := by
  induction arguments generalizing parameters with
  | nil => simp only [reduceArgumentsTagged, List.not_mem_nil, false_implies, implies_true]
  | cons argument arguments recurse =>
      cases parameters with
      | nil =>
          simp only [reduceArgumentsTagged]
          intro child member
          obtain ⟨source,_,rfl⟩ := List.mem_map.mp member
          exact List.nodup_singleton _
      | cons parameter parameters =>
          simp only [reduceArgumentsTagged]
          intro child member
          rcases List.mem_cons.mp member with rfl | member
          · cases type : parameterType? parameter with
            | none => exact List.nodup_singleton _
            | some expected => exact each argument (.head _) expected
          · exact recurse parameters (fun value member expected => each value (.tail _ member) expected) child member

private theorem reduceElementsTagged_distinct_of
    (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (elements : List Pattern) (expected : TypeExpr)
    (each : ∀ element ∈ elements,
      ((reduceAtTagged laws domains language free bound element expected).visited.map (fun origin => origin.source.address)).Nodup) :
    ∀ child ∈ reduceElementsTagged laws domains language free bound elements expected,
      (child.visited.map (fun origin => origin.source.address)).Nodup := by
  induction elements with
  | nil => simp only [reduceElementsTagged, List.not_mem_nil, false_implies, implies_true]
  | cons element elements recurse =>
      intro child member
      simp only [reduceElementsTagged] at member
      rcases List.mem_cons.mp member with rfl | member
      · exact each element (.head _)
      · exact recurse (fun value member => each value (.tail _ member)) child member

private theorem childVisits_nonempty (frame : Nat → OneHoleContext) (start : Nat) (children : List TaggedReduction)
    (frames : ∀ index, index < children.length →
      GeneralTypedSites.contextAddress (frame (start + index)) = [start + index]) :
    ∀ origin ∈ (liftedChildren frame start children).flatMap TaggedReduction.visited, origin.source.address ≠ [] := by
  intro origin member empty
  obtain ⟨index,suffix,_,_,address⟩ := liftedChildren_address_range frame start children frames origin member
  rw [address] at empty
  cases empty

/-- Equal normalized values never reuse one source visit: original child
addresses remain pairwise distinct throughout the complete account. -/
theorem reduceAtTagged_original_addresses_distinct (laws : List Laws) (domains : List TypeExpr)
    (language : LanguageDef) (free : FreeTypeContext) (source : Pattern) :
    ∀ bound expected,
      ((reduceAtTagged laws domains language free bound source expected).visited.map
        (fun origin => origin.source.address)).Nodup := by
  induction source using Pattern.inductionOn with
  | hbvar index => intro bound expected; simp only [reduceAtTagged, opaqueTrace, List.map_cons, List.map_nil]; exact List.nodup_singleton _
  | hfvar identifier => intro bound expected; simp only [reduceAtTagged, opaqueTrace, List.map_cons, List.map_nil]; exact List.nodup_singleton _
  | happly label arguments recurse =>
      intro bound expected
      simp only [reduceAtTagged]
      cases selected : applicationRule? domains language free bound expected label arguments with
      | none => exact List.nodup_singleton _
      | some rule =>
          have frames : ∀ index, index < (reduceArgumentsTagged laws domains language free bound arguments rule.params).length →
              GeneralTypedSites.contextAddress
                (.apply label (arguments.take (0 + index)) .hole (arguments.drop (0 + index + 1))) = [0 + index] := by
            intro index within
            rw [reduceArgumentsTagged_length] at within
            simp only [GeneralTypedSites.contextAddress, List.length_take, Nat.zero_add,
              Nat.min_eq_left (Nat.le_of_lt within)]
          apply rootedTrace_distinct
          · exact liftedChildren_distinct _ _ _ frames
              (reduceArgumentsTagged_distinct_of laws domains language free bound arguments rule.params
                (fun value member expected => recurse value member bound expected))
          · exact childVisits_nonempty _ _ _ frames
  | hlambda display body recurse =>
      intro bound expected
      cases expected with
      | arrow domain codomain =>
          simp only [reduceAtTagged]
          apply rootedTrace_distinct
          · simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using
              trace_underContext_distinct (.lambda display .hole) (recurse (domain :: bound) codomain)
          · intro origin member empty
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at member
            obtain ⟨old,_,rfl⟩ := List.mem_map.mp member
            cases empty
      | _ => simp only [reduceAtTagged]; exact List.nodup_singleton _
  | hmultiLambda arity displays body recurse =>
      intro bound expected
      cases expected with
      | arrow domain codomain =>
          cases domain with
          | multiBinder inner =>
              simp only [reduceAtTagged]
              apply rootedTrace_distinct
              · simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using
                  trace_underContext_distinct (.multiLambda arity displays .hole) (recurse (List.replicate arity inner ++ bound) codomain)
              · intro origin member empty
                simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at member
                obtain ⟨old,_,rfl⟩ := List.mem_map.mp member
                cases empty
          | _ => simp only [reduceAtTagged]; exact List.nodup_singleton _
      | _ => simp only [reduceAtTagged]; exact List.nodup_singleton _
  | hsubst body replacement bodyIH replacementIH =>
      intro bound expected
      simp only [reduceAtTagged]
      cases selected : substitutionDomain? domains language free bound expected body replacement with
      | none => exact List.nodup_singleton _
      | some domain =>
          have frames : ∀ index, index < ([reduceAtTagged laws domains language free (domain :: bound) body expected,
              reduceAtTagged laws domains language free bound replacement domain] : List TaggedReduction).length →
              GeneralTypedSites.contextAddress
                ((fun index => if index = 0 then .substBody .hole replacement else .substReplacement body .hole) (0 + index)) = [0 + index] := by
            intro index within
            have indexCases : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at within; omega
            rcases indexCases with rfl | rfl <;> rfl
          have each : ∀ trace ∈ [reduceAtTagged laws domains language free (domain :: bound) body expected,
              reduceAtTagged laws domains language free bound replacement domain],
              (trace.visited.map (fun origin => origin.source.address)).Nodup := by
            intro trace member
            rcases List.mem_cons.mp member with rfl | member
            · exact bodyIH (domain :: bound) expected
            · cases List.mem_singleton.mp member
              exact replacementIH bound domain
          apply rootedTrace_distinct
          · simpa [liftedChildren] using
              liftedChildren_distinct
                (fun index => if index = 0 then .substBody .hole replacement else .substReplacement body .hole) 0 _ frames each
          · simpa [liftedChildren] using
              childVisits_nonempty
                (fun index => if index = 0 then .substBody .hole replacement else .substReplacement body .hole) 0
                [reduceAtTagged laws domains language free (domain :: bound) body expected,
                  reduceAtTagged laws domains language free bound replacement domain] frames
  | hcollection kind elements rest recurse =>
      intro bound expected
      have childrenDistinct : ∀ element,
          (((liftedChildren (fun index => .collection kind (elements.take index) .hole
            (elements.drop (index + 1)) rest) 0
            (reduceElementsTagged laws domains language free bound elements element)).flatMap TaggedReduction.visited).map
              (fun origin => origin.source.address)).Nodup ∧
          (∀ origin ∈ (liftedChildren (fun index => .collection kind (elements.take index) .hole
            (elements.drop (index + 1)) rest) 0
            (reduceElementsTagged laws domains language free bound elements element)).flatMap TaggedReduction.visited,
              origin.source.address ≠ []) := by
        intro element
        have frames : ∀ index, index < (reduceElementsTagged laws domains language free bound elements element).length →
            GeneralTypedSites.contextAddress
              (.collection kind (elements.take (0 + index)) .hole (elements.drop (0 + index + 1)) rest) = [0 + index] := by
          intro index within
          rw [reduceElementsTagged_length] at within
          simp only [GeneralTypedSites.contextAddress, List.length_take, Nat.zero_add,
            Nat.min_eq_left (Nat.le_of_lt within)]
        exact ⟨liftedChildren_distinct _ _ _ frames
          (reduceElementsTagged_distinct_of laws domains language free bound elements element
            (fun value member => recurse value member bound element)), childVisits_nonempty _ _ _ frames⟩
      cases expected with
      | collection actual element =>
          simp only [reduceAtTagged]
          split
          · exact rootedTrace_distinct _ _ _ _ _ _ (childrenDistinct element).1 (childrenDistinct element).2
          · exact List.nodup_singleton _
      | base category =>
          simp only [reduceAtTagged]
          cases selected : collectionRule? domains language free bound (.base category) kind elements rest with
          | none => exact List.nodup_singleton _
          | some rule =>
              dsimp only
              cases shape : bareCollectionElementType? rule kind (.base category) with
              | none => exact List.nodup_singleton _
              | some element => exact algebraRootedTrace_distinct _ _ _ _ _ _ _ _ (childrenDistinct element).1 (childrenDistinct element).2
      | arrow domain codomain =>
          simp only [reduceAtTagged]
          cases selected : collectionRule? domains language free bound (.arrow domain codomain) kind elements rest with
          | none => exact List.nodup_singleton _
          | some rule =>
              dsimp only
              cases shape : bareCollectionElementType? rule kind (.arrow domain codomain) with
              | none => exact List.nodup_singleton _
              | some element => exact algebraRootedTrace_distinct _ _ _ _ _ _ _ _ (childrenDistinct element).1 (childrenDistinct element).2
      | multiBinder body =>
          simp only [reduceAtTagged]
          cases selected : collectionRule? domains language free bound (.multiBinder body) kind elements rest with
          | none => exact List.nodup_singleton _
          | some rule =>
              dsimp only
              cases shape : bareCollectionElementType? rule kind (.multiBinder body) with
              | none => exact List.nodup_singleton _
              | some element => exact algebraRootedTrace_distinct _ _ _ _ _ _ _ _ (childrenDistinct element).1 (childrenDistinct element).2

#print axioms reduceAtTagged_original_addresses_distinct

def TaggedReduction.partition (trace : TaggedReduction) : List TypedOrigin :=
  trace.survivors ++ trace.unitRemovals.map AlgebraAdministration.origin ++
    trace.carrierRemovals.map AlgebraAdministration.origin

/-- The full partition contains exactly the original visits, with distinct
original addresses and genuine source zippers. This is a source-account
statement, not a completeness theorem for every normalized output position. -/
theorem reduceAtTagged_original_partition (laws : List Laws) (domains : List TypeExpr)
    (language : LanguageDef) (free : FreeTypeContext) (source : Pattern)
    (bound : List TypeExpr) (expected : TypeExpr) :
    let trace := reduceAtTagged laws domains language free bound source expected
    trace.visited.Perm trace.partition ∧
      (trace.partition.map (fun origin => origin.source.address)).Nodup ∧
      (∀ origin ∈ trace.partition, TypedOrigin.Rooted source origin) := by
  dsimp only
  have account := reduceAtTagged_source_account laws domains language free source bound expected
  have distinct := reduceAtTagged_original_addresses_distinct laws domains language free source bound expected
  refine ⟨account, ?_, ?_⟩
  · exact (account.map (fun origin => origin.source.address)).nodup_iff.mp distinct
  · intro origin member
    exact reduceAtTagged_original_points laws domains language free source bound expected origin
      (account.mem_iff.mpr member)

#print axioms reduceAtTagged_original_partition

open GeneralPremise.SchemaTyping

private theorem liftedChildren_complete (frame : Nat → OneHoleContext) (index : Nat)
    (children : List TaggedReduction) :
    (liftedChildren frame index children).all TaggedReduction.complete = children.all TaggedReduction.complete := by
  induction children generalizing index with
  | nil => rfl
  | cons child children recurse =>
      simp only [liftedChildren, List.all_cons, TaggedReduction.underContext, recurse]

private theorem reduceArgumentsTagged_complete_of_objects
    (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) {arguments : List Pattern} {parameters : List TermParam}
    (each : ∀ argument ∈ arguments, ∀ expected,
      HasType language free bound argument expected → isObjectPattern argument = true →
        (reduceAtTagged laws domains language free bound argument expected).complete = true)
    (typed : ArgumentsHaveTypes language free bound arguments parameters)
    (objects : isObjectPatternList arguments = true) :
    (reduceArgumentsTagged laws domains language free bound arguments parameters).all TaggedReduction.complete = true := by
  induction arguments generalizing parameters with
  | nil => cases typed; simp only [reduceArgumentsTagged, List.all_nil]
  | cons argument arguments recurse =>
      cases typed with
      | cons representation parameterType head tail =>
          simp only [isObjectPatternList, Bool.and_eq_true] at objects
          simp only [reduceArgumentsTagged, parameterType, List.all_cons, Bool.and_eq_true]
          exact ⟨each argument (.head _) _ head objects.1,
            recurse (fun value member expected typed object => each value (.tail _ member) expected typed object) tail objects.2⟩

private theorem reduceElementsTagged_complete_of_objects
    (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) {elements : List Pattern} {expected : TypeExpr}
    (each : ∀ element ∈ elements, HasType language free bound element expected → isObjectPattern element = true →
      (reduceAtTagged laws domains language free bound element expected).complete = true)
    (typed : ElementsHaveType language free bound elements expected)
    (objects : isObjectPatternList elements = true) :
    (reduceElementsTagged laws domains language free bound elements expected).all TaggedReduction.complete = true := by
  induction elements with
  | nil => simp only [reduceElementsTagged, List.all_nil]
  | cons element elements recurse =>
      cases typed with
      | cons head tail =>
          simp only [isObjectPatternList, Bool.and_eq_true] at objects
          simp only [reduceElementsTagged, List.all_cons, Bool.and_eq_true]
          exact ⟨each element (.head _) head objects.1,
            recurse (fun value member typed object => each value (.tail _ member) typed object) tail objects.2⟩

/-- Every actually typed object uses checked recursive branches, so its
source traversal has no opaque skipped subtree. No arbitrary typing-domain
choice is identified with the selected domain of a pending substitution. -/
theorem reduceAtTagged_complete_of_object (laws : List Laws) (domains : List TypeExpr)
    (language : LanguageDef) (free : FreeTypeContext) (source : Pattern) :
    ∀ {bound : List TypeExpr} {expected : TypeExpr}, HasType language free bound source expected →
      isObjectPattern source = true →
      (reduceAtTagged laws domains language free bound source expected).complete = true := by
  induction source using Pattern.inductionOn with
  | hbvar index => intro bound expected typed object; simp only [reduceAtTagged, opaqueTrace]
  | hfvar identifier => intro bound expected typed object; simp only [reduceAtTagged, opaqueTrace]
  | happly label arguments recurse =>
      intro bound expected typed object
      have accepted := checkSchemaType_complete_of_object (domains := domains) typed object
      have existsRule : (applicationRule? domains language free bound expected label arguments).isSome = true :=
        (applicationRule_isSome domains language free bound expected label arguments).trans accepted
      simp only [isObjectPattern] at object
      simp only [reduceAtTagged]
      cases selected : applicationRule? domains language free bound expected label arguments with
      | none => simp only [selected, Option.isSome_none, Bool.false_eq_true] at existsRule
      | some rule =>
          obtain ⟨_,_,_,_,argumentsTyped⟩ := applicationRule_readout selected
          simp only [assembleTrace, liftedChildren_complete]
          exact reduceArgumentsTagged_complete_of_objects laws domains language free bound
            (fun argument member expected typed object => recurse argument member typed object) argumentsTyped object
  | hlambda display body recurse =>
      intro bound expected typed object
      cases typed with
      | lambda bodyTyped =>
          simp only [isObjectPattern] at object
          simp only [reduceAtTagged, assembleTrace, List.all_cons, List.all_nil,
            Bool.and_true, TaggedReduction.underContext]
          exact recurse bodyTyped object
  | hmultiLambda arity displays body recurse =>
      intro bound expected typed object
      cases typed with
      | multiLambda bodyTyped =>
          simp only [isObjectPattern] at object
          simp only [reduceAtTagged, assembleTrace, List.all_cons, List.all_nil,
            Bool.and_true, TaggedReduction.underContext]
          exact recurse bodyTyped object
  | hsubst body replacement bodyIH replacementIH =>
      intro bound expected typed object
      simp only [isObjectPattern, Bool.false_eq_true] at object
  | hcollection kind elements rest recurse =>
      intro bound expected typed object
      have accepted := checkSchemaType_complete_of_object (domains := domains) typed object
      simp only [isObjectPattern, Bool.and_eq_true] at object
      rcases CanonicalBags.hasType_collection_inv typed with ⟨element,rfl,items⟩ |
        ⟨sourceRule,parameter,sourceElement,sourceDeclared,sourceParameters,rfl,sourceItems⟩
      · simp only [reduceAtTagged, ↓reduceIte, assembleTrace, liftedChildren_complete]
        exact reduceElementsTagged_complete_of_objects laws domains language free bound
          (fun element member typed object => recurse element member typed object) items object.2
      · have existsRule : (collectionRule? domains language free bound (.base sourceRule.category) kind elements rest).isSome = true :=
          (collectionRule_base_isSome domains language free bound sourceRule.category kind elements rest).trans accepted
        simp only [reduceAtTagged]
        cases selected : collectionRule? domains language free bound (.base sourceRule.category) kind elements rest with
        | none => simp only [selected, Option.isSome_none, Bool.false_eq_true] at existsRule
        | some rule =>
            obtain ⟨element,member,shape,items⟩ := collectionRule_readout selected
            simp only [shape, algebraTrace, liftedChildren_complete]
            exact reduceElementsTagged_complete_of_objects laws domains language free bound
              (fun element member typed object => recurse element member typed object) items object.2

#print axioms reduceAtTagged_complete_of_object

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RoleAwareReadout

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.RoleAwareSourceControls

open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionLaws CanonicalBags.RoleAware DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted
open WithAuthoredEquations.AlgebraFocus RoleAwareReadout

private def tracedData : Pattern := bag [bag [z,a,a]]
private def tracedSource : Pattern := .apply "Box" [tracedData, bag [bag [a,a],z]]
private def tracedTarget : Pattern := .apply "Box" [tracedData, bag [a,a]]
private def actualTrace : TaggedReduction :=
  reduceAtTagged (CollectionLaws.declared language) [] language FreeTypeContext.empty [] tracedSource proc

/-- The actual mixed traversal keeps the data Z and both distinct copies of
A. Only the scalar carrier and its separate unit are administration. -/
theorem mixed_trace_physical_account :
    HasType language FreeTypeContext.empty [] tracedSource proc ∧
      actualTrace.complete = true ∧ actualTrace.target = tracedTarget ∧
      actualTrace.unitRemovals.map (fun event => event.origin.source.address) = [[1,1]] ∧
      actualTrace.carrierRemovals.map (fun event => event.origin.source.address) = [[1,0]] ∧
      actualTrace.survivors.map (fun origin => origin.source.address) =
        [[],[0],[0,0],[0,0,0],[0,0,1],[0,0,2],[1],[1,0,0],[1,0,1]] ∧
      (actualTrace.visited.map (fun origin => origin.source.address)).Nodup ∧
      actualTrace.SourceAccount ∧
      (∀ origin ∈ actualTrace.visited, TypedOrigin.Rooted tracedSource origin) := by
  refine ⟨checkHasType_sound (by decide +kernel), by cbv, by cbv, by cbv, by cbv, by cbv,
    by decide +kernel, reduceAtTagged_source_account _ _ _ _ _ _ _,
    reduceAtTagged_original_points _ _ _ _ _ _ _⟩

private def originalUnitRecord : TypedOrigin :=
  ⟨⟨z,[1,1],.apply "Box" [tracedData] (.collection .hashBag [bag [a,a]] .hole [] none) [],z⟩,
    [],some proc,some (0,zero)⟩

/-- The removal retains the actual unit constructor and the actual Par row
which licenses it. Supplying a surviving A address for that record is false. -/
theorem wrong_trace_origin_rejected :
    actualTrace.unitRemovals = [⟨originalUnitRecord,(3,carrier),⟨.hashBag,some "Z"⟩⟩] ∧
      TypedOrigin.Rooted tracedSource originalUnitRecord ∧
      ¬ TypedOrigin.Rooted tracedSource
        {originalUnitRecord with source := {originalUnitRecord.source with address := [1,0,0]}} := by
  refine ⟨by cbv, ⟨rfl,rfl⟩, ?_⟩
  intro wrong
  have addresses := wrong.2
  change [1,0,0] = [1,1] at addresses
  cases addresses

private def actualSubstitutionTrace : TaggedReduction :=
  reduceAtTagged (CollectionLaws.declared language) [proc] language FreeTypeContext.empty [proc] subSource proc

/-- Both bound-variable visits retain the exact domain extension under the
pending substitution. Their source zippers still rebuild the original schema. -/
theorem substitution_trace_scope_account :
    actualSubstitutionTrace.complete = true ∧
      actualSubstitutionTrace.target = subResult ∧
      actualSubstitutionTrace.unitRemovals.map (fun event => event.origin.source.address) = [[0,1]] ∧
      actualSubstitutionTrace.carrierRemovals.map (fun event => event.origin.source.address) = [[0,0]] ∧
      (actualSubstitutionTrace.visited.filter (fun origin =>
        origin.source.original == .bvar 0 || origin.source.original == .bvar 1)).map
        (fun origin => (origin.bound,origin.expected,origin.source.address)) =
        [([proc,proc],some proc,[0,0,0]),([proc,proc],some proc,[0,0,1])] ∧
      actualSubstitutionTrace.SourceAccount ∧
      (∀ origin ∈ actualSubstitutionTrace.visited, TypedOrigin.Rooted subSource origin) := by
  exact ⟨by cbv, by cbv, by cbv, by cbv, by cbv,
    reduceAtTagged_source_account _ _ _ _ _ _ _, reduceAtTagged_original_points _ _ _ _ _ _ _⟩

#print axioms mixed_trace_physical_account
#print axioms wrong_trace_origin_rejected
#print axioms substitution_trace_scope_account

end Mettapedia.GSLT.LanguageDef.BagNormalForm.RoleAwareSourceControls

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.RoleAwareSourceControls

open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionLaws CanonicalBags.RoleAware DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted
open WithAuthoredEquations.AlgebraFocus RoleAwareReadout

private def secondSort : TypeExpr := .base "Q"
private def firstDomain : TypeExpr := .arrow proc proc
private def selectedDomain : TypeExpr := .arrow secondSort secondSort
private def domainChoiceLanguage : LanguageDef :=
  {language with types := [TypeDecl.plain "P", TypeDecl.plain "Q"]}
private def identityReplacement : Pattern := .lambda none (.bvar 0)
private def domainChoiceSource : Pattern := .subst a identityReplacement
private def domainChoiceTrace : TaggedReduction :=
  reduceAtTagged (CollectionLaws.declared domainChoiceLanguage) [selectedDomain,firstDomain]
    domainChoiceLanguage FreeTypeContext.empty [] domainChoiceSource proc

/-- A valid raw signature does not make the existential substitution domain
unique. The traversal records the actual finite checker's chosen domain;
an arbitrary different typing derivation does not identify that context. -/
theorem pending_domain_choice_boundary :
    domainChoiceLanguage.validate = [] ∧
      TypedAt domainChoiceLanguage FreeTypeContext.empty a (.substBody .hole identityReplacement)
        [] proc [firstDomain] proc ∧
      TypedAt domainChoiceLanguage FreeTypeContext.empty a (.substBody .hole identityReplacement)
        [] proc [selectedDomain] proc ∧
      substitutionDomain? [selectedDomain,firstDomain] domainChoiceLanguage FreeTypeContext.empty []
        proc a identityReplacement = some selectedDomain ∧
      domainChoiceTrace.visited.map (fun origin => (origin.source.address,origin.bound,origin.expected)) =
        [([],[],some proc),([0],[selectedDomain],some proc),([1],[],some selectedDomain),
          ([1,0],[secondSort],some secondSort)] ∧
      [firstDomain] ≠ [selectedDomain] ∧ isObjectPattern domainChoiceSource = false := by
  refine ⟨by cbv, ?_, ?_, by cbv, by cbv, by decide +kernel, rfl⟩
  · exact .substBody (checkHasType_sound (by decide +kernel))
      (.here (checkHasType_sound (by decide +kernel)))
  · exact .substBody (checkHasType_sound (by decide +kernel))
      (.here (checkHasType_sound (by decide +kernel)))

#print axioms pending_domain_choice_boundary

end Mettapedia.GSLT.LanguageDef.BagNormalForm.RoleAwareSourceControls


namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RoleAwareReadout.TypedPaths

open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionLaws CanonicalBags.RoleAware DerivedContexts ReferenceStep
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics

/-- The formation factors of the existing ordinary collection carrier.
Formed already records its object syntax and same-context typing. -/
def objectFormation (bound : List TypeExpr) (term : Pattern) : Prop :=
  term.hasCanonicalBinderMetadata = true ∧ ScopeSafeAt bound.length term

theorem formed_iff_open {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {expected : TypeExpr} {term : Pattern} :
    ReferenceStep.Formed language free bound expected (objectFormation bound) term ↔
      OpenPatternWellSorted language free bound expected term := by
  constructor
  · intro formed
    exact ⟨formed.typed,formed.formed.1,formed.object,formed.formed.2⟩
  · rintro ⟨typed,canonical,object,scope⟩
    exact ⟨object,typed,canonical,scope⟩

private def pathFormation (source : Pattern) (bound : List TypeExpr) (term : Pattern) : Prop :=
  objectFormation bound term ∧ Represents source term

private theorem represents_refl (source : Pattern) : Represents source source := fun _ represented => represented

private theorem represents_trans {first middle last : Pattern}
    (before : Represents first middle) (after : Represents middle last) : Represents first last :=
  fun parameter represented => after parameter (before parameter represented)

private theorem pathFormed_of_open {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {expected : TypeExpr} {origin source : Pattern}
    (good : OpenPatternWellSorted language free bound expected source)
    (represented : Represents origin source) :
    ReferenceStep.Formed language free bound expected (pathFormation origin bound) source :=
  ⟨good.2.2.1,good.1,⟨good.2.1,good.2.2.2⟩,represented⟩

/-- One actual derived-law instance, with both endpoints typed in this very
caller context, is a typed disciplined step. No raw-equivalence endpoint
lifting is used. Its representation evidence is retained for enclosing slots. -/
private theorem derived_root_step {language : LanguageDef} {relEnv : Engine.RelationEnv}
    (discipline : EquationDiscipline) {free : FreeTypeContext} {bound : List TypeExpr} {expected : TypeExpr}
    {origin source target : Pattern} (generator : DerivedInstance language source target)
    (good : OpenPatternWellSorted language free bound expected source)
    (targetTyped : HasType language free bound target expected) (represented : Represents origin source) :
    ReferenceStep.TypedStep relEnv language discipline free bound expected (pathFormation origin bound) source target := by
  refine ⟨pathFormed_of_open good represented, ?_, .inContext .hole (.inr generator)⟩
  refine ⟨derived_isObjectPattern generator good.2.2.1,targetTyped,?_,?_⟩
  · exact ⟨derived_hasCanonicalBinderMetadata generator good.2.1,targetTyped.isWellScopedAt⟩
  · exact represents_trans represented (derived_represents generator)

/-- Typed occurrence congruence for this actual constructed path. The
source-dependent representation invariant discharges authored binder slots;
the public result later forgets that auxiliary invariant. -/
private theorem lift_path {language : LanguageDef} {relEnv : Engine.RelationEnv}
    {discipline : EquationDiscipline} {free : FreeTypeContext}
    {bound focusBound : List TypeExpr} {expected focusType : TypeExpr}
    {origin source target : Pattern} {context : OneHoleContext}
    (selected : TypedAt language free source context bound expected focusBound focusType)
    (good : OpenPatternWellSorted language free bound expected (context.fill source))
    (represented : Represents origin (context.fill source))
    (path : ReferenceStep.TypedEquivalent relEnv language discipline free focusBound focusType
      (pathFormation source focusBound) source target) :
    ReferenceStep.TypedEquivalent relEnv language discipline free bound expected
      (pathFormation origin bound) (context.fill source) (context.fill target) := by
  apply ReferenceStep.TypedEquivalent.fill context ?_ path
  intro term formed
  have compatible : RepresentationCompatible source term := fun frame parameter representation =>
    represents_fill frame formed.formed.2 parameter representation
  have typed := selected.replace compatible formed.typed
  refine ⟨isObjectPattern_fill_replace context good.2.2.1 (fun _ => formed.object),typed,?_,?_⟩
  · exact ⟨hasCanonicalBinderMetadata_fill_replace context good.2.1 (fun _ => formed.formed.1.1),
      typed.isWellScopedAt⟩
  · exact represents_trans represented (represents_fill context formed.formed.2)

/-- Actual flattening at a homogeneous algebra's base-result occurrence.
The target spine is derived from the checked source spine and nested member;
its same-context typing is not an additional endpoint assumption. -/
theorem flatten_step {laws : List Laws} {language : LanguageDef} {relEnv : Engine.RelationEnv}
    (checked : checkBareHomogeneous laws language = true) (discipline : EquationDiscipline)
    {free : FreeTypeContext} {bound : List TypeExpr} {rule : GrammarRule}
    {kind : CollType} {parameter : String} {law : Laws}
    (shape : rule.bareParams = [.simple parameter (.collection kind (.base rule.category))])
    (found : lawFor laws kind = some law)
    (declaration : AlgebraRule language rule kind ⟨true,law.unit⟩)
    (before middle after : List Pattern)
    (typed : ElementsHaveType language free bound (before ++ .collection kind middle none :: after) (.base rule.category))
    (canonical : (.collection kind (before ++ .collection kind middle none :: after) none : Pattern).hasCanonicalBinderMetadata = true)
    (object : isObjectPattern (.collection kind (before ++ .collection kind middle none :: after) none) = true) :
    ReferenceStep.TypedStep relEnv language discipline free bound (.base rule.category) (objectFormation bound)
      (.collection kind (before ++ .collection kind middle none :: after) none)
      (.collection kind (before ++ middle ++ after) none) := by
  have sourceTyped : HasType language free bound
      (.collection kind (before ++ .collection kind middle none :: after) none) (.base rule.category) :=
    .collectionConstructor declaration.authored shape typed
  have selectedTyped : HasType language free bound (.collection kind middle none) (.base rule.category) :=
    CanonicalBags.elementsHaveType_iff.mp typed _ (by simp)
  have middleTyped : ElementsHaveType language free bound middle (.base rule.category) := by
    apply CanonicalBags.elementsHaveType_iff.mpr
    intro item member
    apply splice_base_typed checked found selectedTyped item
    simpa only [CollectionLaws.splice, lawFor_kind found, ↓reduceIte] using member
  have targetItems : ElementsHaveType language free bound (before ++ middle ++ after) (.base rule.category) := by
    apply CanonicalBags.elementsHaveType_iff.mpr
    intro item member
    simp only [List.mem_append] at member
    rcases member with (earlier | inner) | later
    · exact CanonicalBags.elementsHaveType_iff.mp typed item (by simp [earlier])
    · exact CanonicalBags.elementsHaveType_iff.mp middleTyped item inner
    · exact CanonicalBags.elementsHaveType_iff.mp typed item (by simp [later])
  have targetTyped : HasType language free bound (.collection kind (before ++ middle ++ after) none)
      (.base rule.category) := .collectionConstructor declaration.authored shape targetItems
  have generator : DerivedInstance language
      (.collection kind (before ++ .collection kind middle none :: after) none)
      (.collection kind (before ++ middle ++ after) none) :=
    .flatten declaration rfl ⟨free,bound,sourceTyped⟩
  exact ⟨⟨object,sourceTyped,canonical,sourceTyped.isWellScopedAt⟩,
    ⟨derived_isObjectPattern generator object,targetTyped,
      derived_hasCanonicalBinderMetadata generator canonical,targetTyped.isWellScopedAt⟩,
    .inContext .hole (.inr generator)⟩

/-- The declared unit is removed at its actual typed base-result collection,
while the same free/bound context and formation factors are retained. -/
theorem unit_step {language : LanguageDef} {relEnv : Engine.RelationEnv}
    (discipline : EquationDiscipline) {free : FreeTypeContext} {bound : List TypeExpr} {rule : GrammarRule}
    {kind : CollType} {parameter unitLabel : String} {algebra : CollectionAlgebra}
    (shape : rule.bareParams = [.simple parameter (.collection kind (.base rule.category))])
    (declaration : AlgebraRule language rule kind algebra) (unit : algebra.unit = some unitLabel)
    (before after : List Pattern)
    (typed : ElementsHaveType language free bound (before ++ .apply unitLabel [] :: after) (.base rule.category))
    (canonical : (.collection kind (before ++ .apply unitLabel [] :: after) none : Pattern).hasCanonicalBinderMetadata = true)
    (object : isObjectPattern (.collection kind (before ++ .apply unitLabel [] :: after) none) = true) :
    ReferenceStep.TypedStep relEnv language discipline free bound (.base rule.category) (objectFormation bound)
      (.collection kind (before ++ .apply unitLabel [] :: after) none) (.collection kind (before ++ after) none) := by
  have sourceTyped : HasType language free bound (.collection kind (before ++ .apply unitLabel [] :: after) none)
      (.base rule.category) := .collectionConstructor declaration.authored shape typed
  have targetItems : ElementsHaveType language free bound (before ++ after) (.base rule.category) := by
    apply CanonicalBags.elementsHaveType_iff.mpr
    intro item member
    rcases List.mem_append.mp member with earlier | later
    · exact CanonicalBags.elementsHaveType_iff.mp typed item (by simp [earlier])
    · exact CanonicalBags.elementsHaveType_iff.mp typed item (by simp [later])
  have targetTyped : HasType language free bound (.collection kind (before ++ after) none) (.base rule.category) :=
    .collectionConstructor declaration.authored shape targetItems
  have generator : DerivedInstance language
      (.collection kind (before ++ .apply unitLabel [] :: after) none) (.collection kind (before ++ after) none) :=
    .unitElim declaration unit ⟨free,bound,sourceTyped⟩
  exact ⟨⟨object,sourceTyped,canonical,sourceTyped.isWellScopedAt⟩,
    ⟨derived_isObjectPattern generator object,targetTyped,
      derived_hasCanonicalBinderMetadata generator canonical,targetTyped.isWellScopedAt⟩,
    .inContext .hole (.inr generator)⟩

#print axioms flatten_step
#print axioms unit_step

/-- Intrinsic permutation is realized from the actual declared collection
site at this source, including wrapped and nested data occurrences. Both
endpoints retain the same caller type and local bound context. -/
theorem permutation_step {language : LanguageDef} {relEnv : Engine.RelationEnv}
    (discipline : EquationDiscipline) {free : FreeTypeContext} {bound : List TypeExpr} {expected : TypeExpr}
    {kind : CollType} {elements other : List Pattern}
    (unordered : CanonicalBags.Unordered kind = true) (permutation : elements.Perm other)
    (site : ReferenceStep.CollectionLawSite language kind elements)
    (good : OpenPatternWellSorted language free bound expected (.collection kind elements none)) :
    ReferenceStep.TypedStep relEnv language discipline free bound expected (objectFormation bound)
      (.collection kind elements none) (.collection kind other none) := by
  have generator : DerivedInstance language (.collection kind elements none) (.collection kind other none) := by
    rcases site with vector | ⟨rule,declared,typed⟩
    · subst kind
      cases unordered
    · cases kind with
      | vec => cases unordered
      | hashBag => exact .bagPerm declared typed permutation
      | hashSet => exact .setPerm declared typed permutation
  have targetTyped := (CanonicalBags.BagStep.permute (rest := none) unordered permutation).hasType good.1
  exact ⟨(formed_iff_open).mpr good,
    ⟨derived_isObjectPattern generator good.2.2.1,targetTyped,
      derived_hasCanonicalBinderMetadata generator good.2.1,targetTyped.isWellScopedAt⟩,
    .inContext .hole (.inr generator)⟩

/-- The actual selected lexical sorter is a typed permutation step. This
states sorting only; set contraction is a separate derived-law path. -/
theorem lexical_permutation_step {language : LanguageDef} {relEnv : Engine.RelationEnv}
    (discipline : EquationDiscipline) {free : FreeTypeContext} {bound : List TypeExpr} {expected : TypeExpr}
    {kind : CollType} {elements : List Pattern}
    (unordered : CanonicalBags.Unordered kind = true)
    (site : ReferenceStep.CollectionLawSite language kind elements)
    (good : OpenPatternWellSorted language free bound expected (.collection kind elements none)) :
    ReferenceStep.TypedStep relEnv language discipline free bound expected (objectFormation bound)
      (.collection kind elements none) (.collection kind (PatternLexOrder.sortLex elements) none) :=
  permutation_step discipline unordered (PatternLexOrder.sortLex_perm elements).symm site good

#print axioms permutation_step
#print axioms lexical_permutation_step

private theorem strengthen_step {language : LanguageDef} {relEnv : Engine.RelationEnv}
    {discipline : EquationDiscipline} {free : FreeTypeContext} {bound : List TypeExpr} {expected : TypeExpr}
    {origin source target : Pattern}
    (step : ReferenceStep.TypedStep relEnv language discipline free bound expected (objectFormation bound) source target)
    (sourceRepresents : Represents origin source) (targetRepresents : Represents origin target) :
    ReferenceStep.TypedStep relEnv language discipline free bound expected (pathFormation origin bound) source target :=
  ⟨⟨step.1.object,step.1.typed,step.1.formed,sourceRepresents⟩,
    ⟨step.2.1.object,step.2.1.typed,step.2.1.formed,targetRepresents⟩,step.2.2⟩

private theorem base_collection_elements {laws : List Laws} {language : LanguageDef}
    (checked : checkBareHomogeneous laws language = true)
    {free : FreeTypeContext} {bound : List TypeExpr} {kind : CollType} {law : Laws}
    (found : lawFor laws kind = some law) {elements : List Pattern} {category : String}
    (typed : HasType language free bound (.collection kind elements none) (.base category)) :
    ElementsHaveType language free bound elements (.base category) := by
  apply CanonicalBags.elementsHaveType_iff.mpr
  intro item member
  apply splice_base_typed checked found typed item
  simpa only [CollectionLaws.splice, lawFor_kind found, ↓reduceIte] using member

private theorem splice_typed_path
    {laws : List Laws} {language : LanguageDef} {relEnv : Engine.RelationEnv}
    (checked : checkBareHomogeneous laws language = true) (discipline : EquationDiscipline)
    {free : FreeTypeContext} {bound : List TypeExpr} {rule : GrammarRule} {kind : CollType}
    {parameter : String} {law : Laws}
    (shape : rule.bareParams = [.simple parameter (.collection kind (.base rule.category))])
    (found : lawFor laws kind = some law) (declaration : AlgebraRule language rule kind ⟨true,law.unit⟩)
    (origin : Pattern) : ∀ (todo done : List Pattern),
      OpenPatternWellSorted language free bound (.base rule.category) (.collection kind (done ++ todo) none) →
      Represents origin (.collection kind (done ++ todo) none) →
      ReferenceStep.TypedEquivalent relEnv language discipline free bound (.base rule.category)
        (pathFormation origin bound) (.collection kind (done ++ todo) none)
        (.collection kind (done ++ todo.flatMap (CollectionLaws.splice law)) none)
  | [], done, good, represented => by
      simp only [List.flatMap_nil,List.append_nil]
      exact .refl _
  | item :: todo, done, good, represented => by
      have typed := base_collection_elements checked found good.1
      have keep (fixed : CollectionLaws.splice law item = [item]) :
          ReferenceStep.TypedEquivalent relEnv language discipline free bound (.base rule.category)
            (pathFormation origin bound) (.collection kind (done ++ item :: todo) none)
            (.collection kind (done ++ (item :: todo).flatMap (CollectionLaws.splice law)) none) := by
        have regrouped : done ++ item :: todo = (done ++ [item]) ++ todo := by simp
        have later := splice_typed_path (relEnv := relEnv) checked discipline shape found declaration origin todo (done ++ [item])
          (regrouped ▸ good) (regrouped ▸ represented)
        simpa only [List.flatMap_cons,fixed,List.append_assoc,List.singleton_append] using later
      have sameKind := lawFor_kind found
      cases item with
      | collection actual middle rest =>
          cases rest with
          | none =>
              by_cases same : actual = law.kind
              · have actualEq : actual = kind := same.trans sameKind
                have step := flatten_step (relEnv := relEnv) checked discipline shape found declaration done middle todo
                  (by simpa only [actualEq] using typed) (by simpa only [actualEq] using good.2.1)
                  (by simpa only [actualEq] using good.2.2.1)
                have startRepresents : Represents origin (.collection kind (done ++ .collection kind middle none :: todo) none) := by
                  simpa only [actualEq] using represented
                have nextRepresents : Represents origin (.collection kind (done ++ middle ++ todo) none) :=
                  represents_trans startRepresents (represents_collection kind _ none _)
                have first := strengthen_step step startRepresents nextRepresents
                have nextGood := (formed_iff_open).mp step.2.1
                have later := splice_typed_path (relEnv := relEnv) checked discipline shape found declaration origin todo (done ++ middle)
                  (by simpa only [List.append_assoc] using nextGood)
                  (by simpa only [List.append_assoc] using nextRepresents)
                have combined := Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ first) later
                simpa only [ReferenceStep.TypedEquivalent, List.flatMap_cons, CollectionLaws.splice,
                  sameKind, actualEq, ↓reduceIte,List.append_assoc] using combined
              · exact keep (by simp only [CollectionLaws.splice,same,if_false])
          | some other => exact keep rfl
      | apply label arguments =>
          cases arguments with
          | nil =>
              by_cases unit : law.unit = some label
              · have step := unit_step (relEnv := relEnv) discipline shape declaration unit done todo
                  typed good.2.1 good.2.2.1
                have nextRepresents : Represents origin (.collection kind (done ++ todo) none) :=
                  represents_trans represented (represents_collection kind _ none _)
                have first := strengthen_step step represented nextRepresents
                have nextGood := (formed_iff_open).mp step.2.1
                have later := splice_typed_path (relEnv := relEnv) checked discipline shape found declaration origin todo done nextGood nextRepresents
                have combined := Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ first) later
                simpa only [ReferenceStep.TypedEquivalent,List.flatMap_cons,CollectionLaws.splice,
                  unit,↓reduceIte,List.nil_append] using combined
              · exact keep (by simp only [CollectionLaws.splice,unit,if_false])
          | cons first rest => exact keep rfl
      | bvar index => exact keep rfl
      | fvar identifier => exact keep rfl
      | lambda display body => exact keep rfl
      | multiLambda arity displays body => exact keep rfl
      | subst body replacement => exact keep rfl

/-- Every actual splicing operation has a path through object terms of the
same original caller fibre. Each nontrivial link is the declared flattening
or unit step above; retained authored rows are not removed or used as an oracle. -/
private theorem finishAlgebra_typed_path
    {laws : List Laws} {language : LanguageDef} {relEnv : Engine.RelationEnv}
    (checked : checkBareHomogeneous laws language = true) (authorized : SourceAlgebras laws language)
    (discipline : EquationDiscipline) {free : FreeTypeContext} {bound : List TypeExpr}
    {rule : GrammarRule} (declared : rule ∈ language.terms) {kind : CollType} {parameter : String}
    (shape : rule.bareParams = [.simple parameter (.collection kind (.base rule.category))])
    {origin : Pattern} {elements : List Pattern}
    (good : OpenPatternWellSorted language free bound (.base rule.category) (.collection kind elements none))
    (represented : Represents origin (.collection kind elements none)) :
    ReferenceStep.TypedEquivalent relEnv language discipline free bound (.base rule.category)
      (pathFormation origin bound) (.collection kind elements none)
      (.collection kind (finishAlgebra laws kind elements) none) := by
  unfold finishAlgebra
  cases found : lawFor laws kind with
  | none => exact .refl _
  | some law =>
      have declaration := authorized rule declared kind parameter law shape found
      simpa only [List.nil_append] using
        splice_typed_path (relEnv := relEnv) checked discipline shape found declaration origin elements [] good represented

#print axioms finishAlgebra_typed_path

private theorem open_list_member {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {items : List Pattern} {item : Pattern} {expected : TypeExpr}
    (typed : HasType language free bound item expected)
    (canonical : Pattern.hasCanonicalBinderMetadataList items = true)
    (objects : isObjectPatternList items = true) (member : item ∈ items) :
    OpenPatternWellSorted language free bound expected item :=
  ⟨typed,(hasCanonicalBinderMetadataList_iff).mp canonical item member,
    (isObjectPatternList_iff).mp objects item member,typed.isWellScopedAt⟩

private theorem arguments_typed_path
    {laws : List Laws} {domains : List TypeExpr} {language : LanguageDef} {relEnv : Engine.RelationEnv}
    {discipline : EquationDiscipline} {free : FreeTypeContext} {bound : List TypeExpr}
    {rule : GrammarRule} (declared : rule ∈ language.terms) (ordinary : ¬ UsesBareCollection rule)
    (origin : Pattern) : ∀ (todo : List Pattern) (todoRows : List TermParam)
      (before : List Pattern) (beforeRows : List TermParam),
      ArgumentsHaveTypes language free bound before beforeRows →
      ArgumentsHaveTypes language free bound todo todoRows →
      rule.params = beforeRows ++ todoRows →
      OpenPatternWellSorted language free bound (.base rule.category) (.apply rule.label (before ++ todo)) →
      Represents origin (.apply rule.label (before ++ todo)) →
      (∀ argument ∈ todo, ∀ expected, OpenPatternWellSorted language free bound expected argument →
        ReferenceStep.TypedEquivalent relEnv language discipline free bound expected (pathFormation argument bound)
          argument (reduceAt laws domains language free bound argument expected)) →
      ReferenceStep.TypedEquivalent relEnv language discipline free bound (.base rule.category)
        (pathFormation origin bound) (.apply rule.label (before ++ todo))
        (.apply rule.label (before ++ reduceArguments laws domains language free bound todo todoRows))
  | [], todoRows, before, beforeRows, beforeTyped, todoTyped, shape, good, represented, each => by
      cases todoTyped
      simp only [reduceArguments]
      exact .refl _
  | argument :: todo, todoRows, before, beforeRows, beforeTyped, todoTyped, shape, good, represented, each => by
      cases todoTyped with
      | @cons _ _ _ parameterRow afterRows expected representation parameterType headTyped tailTyped =>
          have fullTyped : ArgumentsHaveTypes language free bound (before ++ argument :: todo) rule.params := by
            rw [shape]
            exact argumentsHaveTypes_join representation parameterType headTyped tailTyped beforeTyped
          have selected : TypedAt language free argument (.apply rule.label before .hole todo)
              bound (.base rule.category) bound expected :=
            .application declared ordinary fullTyped shape beforeTyped.length_eq.symm parameterType (.here headTyped)
          have argumentGood := open_list_member headTyped
            (show Pattern.hasCanonicalBinderMetadataList (before ++ argument :: todo) = true from good.2.1)
            (show isObjectPatternList (before ++ argument :: todo) = true from good.2.2.1)
            (by simp)
          have argumentPath := each argument (.head _) expected argumentGood
          have first := lift_path selected good represented argumentPath
          have argumentEnd := argumentPath.formed_right (pathFormed_of_open argumentGood (represents_refl argument))
          have nextRepresentation := argumentEnd.formed.2 parameterRow representation
          have nextBeforeTyped : ArgumentsHaveTypes language free bound
              (before ++ [reduceAt laws domains language free bound argument expected]) (beforeRows ++ [parameterRow]) :=
            argumentsHaveTypes_join nextRepresentation parameterType argumentEnd.typed (.nil) beforeTyped
          have nextShape : rule.params = (beforeRows ++ [parameterRow]) ++ afterRows := by
            simpa only [List.append_assoc,List.singleton_append] using shape
          have fullEnd := first.formed_right (pathFormed_of_open good represented)
          have nextGood : OpenPatternWellSorted language free bound (.base rule.category)
              (.apply rule.label ((before ++ [reduceAt laws domains language free bound argument expected]) ++ todo)) := by
            simpa only [OneHoleContext.fill,List.append_assoc,List.singleton_append] using
              (show OpenPatternWellSorted language free bound (.base rule.category)
                ((.apply rule.label before .hole todo : OneHoleContext).fill
                  (reduceAt laws domains language free bound argument expected)) from
                ⟨fullEnd.typed,fullEnd.formed.1.1,fullEnd.object,fullEnd.formed.1.2⟩)
          have nextRepresents : Represents origin
              (.apply rule.label ((before ++ [reduceAt laws domains language free bound argument expected]) ++ todo)) := by
            simpa only [OneHoleContext.fill,List.append_assoc,List.singleton_append] using fullEnd.formed.2
          have later := arguments_typed_path (relEnv := relEnv) declared ordinary origin todo afterRows
            (before ++ [reduceAt laws domains language free bound argument expected]) (beforeRows ++ [parameterRow])
            nextBeforeTyped tailTyped nextShape nextGood nextRepresents
            (fun value member expected good => each value (.tail _ member) expected good)
          simp only [List.append_assoc,List.singleton_append] at later
          have combined := Relation.EqvGen.trans _ _ _ first later
          simpa only [ReferenceStep.TypedEquivalent,OneHoleContext.fill,reduceArguments,parameterType,
            List.append_assoc,List.singleton_append] using combined

private theorem elements_concat {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {element : TypeExpr} {before after : List Pattern}
    (first : ElementsHaveType language free bound before element)
    (second : ElementsHaveType language free bound after element) :
    ElementsHaveType language free bound (before ++ after) element := by
  apply CanonicalBags.elementsHaveType_iff.mpr
  intro item member
  rcases List.mem_append.mp member with earlier | later
  · exact CanonicalBags.elementsHaveType_iff.mp first item earlier
  · exact CanonicalBags.elementsHaveType_iff.mp second item later

private theorem elements_typed_path
    {laws : List Laws} {domains : List TypeExpr} {language : LanguageDef} {relEnv : Engine.RelationEnv}
    {discipline : EquationDiscipline} {free : FreeTypeContext} {bound : List TypeExpr}
    {kind : CollType} {element parentType : TypeExpr}
    (role : parentType = .collection kind element ∨
      ∃ rule parameter, rule ∈ language.terms ∧
        rule.bareParams = [.simple parameter (.collection kind element)] ∧ parentType = .base rule.category)
    (origin : Pattern) : ∀ (todo before : List Pattern),
      ElementsHaveType language free bound before element → ElementsHaveType language free bound todo element →
      OpenPatternWellSorted language free bound parentType (.collection kind (before ++ todo) none) →
      Represents origin (.collection kind (before ++ todo) none) →
      (∀ item ∈ todo, OpenPatternWellSorted language free bound element item →
        ReferenceStep.TypedEquivalent relEnv language discipline free bound element (pathFormation item bound)
          item (reduceAt laws domains language free bound item element)) →
      ReferenceStep.TypedEquivalent relEnv language discipline free bound parentType
        (pathFormation origin bound) (.collection kind (before ++ todo) none)
        (.collection kind (before ++ reduceElements laws domains language free bound todo element) none)
  | [], before, beforeTyped, todoTyped, good, represented, each => by
      simp only [reduceElements]
      exact .refl _
  | item :: todo, before, beforeTyped, todoTyped, good, represented, each => by
      cases todoTyped with
      | cons headTyped tailTyped =>
          have fullTyped := elements_concat beforeTyped (ElementsHaveType.cons headTyped tailTyped)
          have selected : TypedAt language free item (.collection kind before .hole todo none)
              bound parentType bound element := by
            rcases role with rfl | ⟨rule,parameter,declared,shape,rfl⟩
            · exact .collection fullTyped (.here headTyped)
            · exact .collectionConstructor declared shape fullTyped (.here headTyped)
          have itemGood := open_list_member headTyped
            (show Pattern.hasCanonicalBinderMetadataList (before ++ item :: todo) = true from good.2.1)
            (show isObjectPatternList (before ++ item :: todo) = true from good.2.2.1) (by simp)
          have itemPath := each item (.head _) itemGood
          have first := lift_path selected good represented itemPath
          have itemEnd := itemPath.formed_right (pathFormed_of_open itemGood (represents_refl item))
          have nextBeforeTyped := elements_concat beforeTyped (ElementsHaveType.cons itemEnd.typed (.nil _ _))
          have fullEnd := first.formed_right (pathFormed_of_open good represented)
          have nextGood : OpenPatternWellSorted language free bound parentType
              (.collection kind ((before ++ [reduceAt laws domains language free bound item element]) ++ todo) none) := by
            simpa only [OneHoleContext.fill,List.append_assoc,List.singleton_append] using
              (show OpenPatternWellSorted language free bound parentType
                ((.collection kind before .hole todo none : OneHoleContext).fill
                  (reduceAt laws domains language free bound item element)) from
                ⟨fullEnd.typed,fullEnd.formed.1.1,fullEnd.object,fullEnd.formed.1.2⟩)
          have nextRepresents : Represents origin
              (.collection kind ((before ++ [reduceAt laws domains language free bound item element]) ++ todo) none) := by
            simpa only [OneHoleContext.fill,List.append_assoc,List.singleton_append] using fullEnd.formed.2
          have later := elements_typed_path (relEnv := relEnv) role origin todo
            (before ++ [reduceAt laws domains language free bound item element]) nextBeforeTyped tailTyped
            nextGood nextRepresents (fun value member good => each value (.tail _ member) good)
          simp only [List.append_assoc,List.singleton_append] at later
          have combined := Relation.EqvGen.trans _ _ _ first later
          simpa only [ReferenceStep.TypedEquivalent,OneHoleContext.fill,reduceElements,List.append_assoc,
            List.singleton_append] using combined

#print axioms arguments_typed_path
#print axioms elements_typed_path

private theorem reduceAt_typed_path
    {laws : List Laws} {language : LanguageDef} {relEnv : Engine.RelationEnv}
    (checked : checkBareHomogeneous laws language = true) (authorized : SourceAlgebras laws language)
    (discipline : EquationDiscipline) (domains : List TypeExpr) (free : FreeTypeContext) (source : Pattern) :
    ∀ {bound : List TypeExpr} {expected : TypeExpr}, OpenPatternWellSorted language free bound expected source →
      ReferenceStep.TypedEquivalent relEnv language discipline free bound expected (pathFormation source bound)
        source (reduceAt laws domains language free bound source expected) := by
  induction source using Pattern.inductionOn with
  | hbvar index => intro bound expected good; simp only [reduceAt]; exact .refl _
  | hfvar identifier => intro bound expected good; simp only [reduceAt]; exact .refl _
  | happly label arguments recurse =>
      intro bound expected good
      simp only [reduceAt]
      cases selected : applicationRule? domains language free bound expected label arguments with
      | none => exact .refl _
      | some rule =>
          obtain ⟨member,head,expectedEq,ordinary,argumentsTyped⟩ := applicationRule_readout selected
          rw [← head,expectedEq] at good ⊢
          simpa only [List.nil_append] using
            arguments_typed_path (relEnv := relEnv) (laws := laws) (domains := domains) member ordinary
              (.apply rule.label arguments) arguments rule.params [] [] .nil argumentsTyped rfl good
              (represents_refl _) (fun argument member expected good => recurse argument member good)
  | hlambda display body recurse =>
      intro bound expected good
      cases good.1 with
      | lambda bodyTyped =>
          have canonical := good.2.1
          simp only [Pattern.hasCanonicalBinderMetadata,Bool.and_eq_true] at canonical
          have bodyGood : OpenPatternWellSorted language free _ _ body :=
            ⟨bodyTyped,canonical.2,good.2.2.1,bodyTyped.isWellScopedAt⟩
          have path := lift_path (relEnv := relEnv) (TypedAt.lambda (.here bodyTyped)) good
            (represents_refl _) (recurse bodyGood)
          simpa only [reduceAt,OneHoleContext.fill] using path
  | hmultiLambda arity displays body recurse =>
      intro bound expected good
      cases good.1 with
      | multiLambda bodyTyped =>
          have canonical := good.2.1
          simp only [Pattern.hasCanonicalBinderMetadata,Bool.and_eq_true] at canonical
          have bodyGood : OpenPatternWellSorted language free _ _ body :=
            ⟨bodyTyped,canonical.2,good.2.2.1,bodyTyped.isWellScopedAt⟩
          have path := lift_path (relEnv := relEnv) (TypedAt.multiLambda (.here bodyTyped)) good
            (represents_refl _) (recurse bodyGood)
          simpa only [reduceAt,OneHoleContext.fill] using path
  | hsubst body replacement bodyIH replacementIH =>
      intro bound expected good
      have impossible := good.2.2.1
      simp only [isObjectPattern,Bool.false_eq_true] at impossible
  | hcollection kind elements rest recurse =>
      intro bound expected good
      have closed : rest = none := by
        have object := good.2.2.1
        simp only [isObjectPattern,Bool.and_eq_true] at object
        cases rest with
        | none => rfl
        | some identifier => cases object.1
      subst rest
      rcases CanonicalBags.hasType_collection_inv good.1 with ⟨element,rfl,items⟩ |
        ⟨sourceRule,sourceParameter,sourceElement,sourceDeclared,sourceShape,rfl,sourceItems⟩
      · simp only [reduceAt,↓reduceIte]
        simpa only [List.nil_append] using
          elements_typed_path (relEnv := relEnv) (laws := laws) (domains := domains) (.inl rfl)
            (.collection kind elements none) elements [] (.nil _ _) items good (represents_refl _)
            (fun item member good => recurse item member good)
      · simp only [reduceAt]
        cases selected : collectionRule? domains language free bound (.base sourceRule.category) kind elements none with
        | none => exact .refl _
        | some rule =>
            obtain ⟨element,member,elementRead,items⟩ := collectionRule_readout selected
            simp only [elementRead]
            obtain ⟨expectedEq,parameter,shape⟩ := (bareCollectionElementType?_eq_some_iff _ _ _ _).mp elementRead
            rw [expectedEq] at good ⊢
            have first : ReferenceStep.TypedEquivalent relEnv language discipline free bound (.base rule.category)
                (pathFormation (.collection kind elements none) bound) (.collection kind elements none)
                (.collection kind (reduceElements laws domains language free bound elements element) none) := by
              simpa only [List.nil_append] using
                elements_typed_path (relEnv := relEnv) (laws := laws) (domains := domains)
                  (.inr ⟨rule,parameter,member,shape,rfl⟩) (.collection kind elements none)
                  elements [] (.nil _ _) items good (represents_refl _)
                  (fun item member good => recurse item member good)
            cases found : lawFor laws kind with
            | none => simpa only [finishAlgebra,found] using first
            | some law =>
                have homogeneous := homogeneous_bare_of_checked checked found member shape
                rw [homogeneous] at items shape first ⊢
                have firstEnd := first.formed_right (pathFormed_of_open good (represents_refl _))
                have normalizedGood : OpenPatternWellSorted language free bound (.base rule.category)
                    (.collection kind (reduceElements laws domains language free bound elements (.base rule.category)) none) :=
                  ⟨firstEnd.typed,firstEnd.formed.1.1,firstEnd.object,firstEnd.formed.1.2⟩
                have later := finishAlgebra_typed_path (relEnv := relEnv) checked authorized discipline member shape
                  normalizedGood firstEnd.formed.2
                exact .trans _ _ _ first later

/-- Actual role-directed normalization is a path through the ordinary
collection carrier, at one free/bound/expected fibre throughout. Every
nontrivial link is constructed above from the actual declared source law.
No raw-equivalence endpoint lifting or reflective formation is assumed. -/
theorem reduceAt_typed_equivalent
    {laws : List Laws} {language : LanguageDef} {relEnv : Engine.RelationEnv}
    (checked : checkBareHomogeneous laws language = true) (authorized : SourceAlgebras laws language)
    (discipline : EquationDiscipline) (domains : List TypeExpr) (free : FreeTypeContext)
    (source : Pattern) {bound : List TypeExpr} {expected : TypeExpr}
    (good : OpenPatternWellSorted language free bound expected source) :
    ReferenceStep.TypedEquivalent relEnv language discipline free bound expected (objectFormation bound)
      source (reduceAt laws domains language free bound source expected) :=
  (reduceAt_typed_path (relEnv := relEnv) checked authorized discipline domains free source good).weaken
    (fun _ formed => formed.1)

/-- The checked tagged traversal has the same actual typed normalization
path. This preserves its original source account without inferring a typed
output-position map or a captured-body rebasing certificate. -/
theorem reduceAtTagged_typed_equivalent
    {laws : List Laws} {language : LanguageDef} {relEnv : Engine.RelationEnv}
    (checked : checkBareHomogeneous laws language = true) (authorized : SourceAlgebras laws language)
    (discipline : EquationDiscipline) (domains : List TypeExpr) (free : FreeTypeContext)
    (source : Pattern) {bound : List TypeExpr} {expected : TypeExpr}
    (good : OpenPatternWellSorted language free bound expected source) :
    ReferenceStep.TypedEquivalent relEnv language discipline free bound expected (objectFormation bound)
      source (reduceAtTagged laws domains language free bound source expected).target := by
  rw [reduceAtTagged_target]
  exact reduceAt_typed_equivalent checked authorized discipline domains free source good

#print axioms reduceAt_typed_equivalent
#print axioms reduceAtTagged_typed_equivalent

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RoleAwareReadout.TypedPaths


namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.RoleAwareSourceControls

open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionLaws CanonicalBags.RoleAware DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted
open WithAuthoredEquations.AlgebraFocus RoleAwareReadout TypedPaths

private theorem traced_open :
    OpenPatternWellSorted language FreeTypeContext.empty [] proc tracedSource := by
  have typed := mixed_trace_physical_account.1
  exact ⟨typed, by decide +kernel, by decide +kernel, typed.isWellScopedAt⟩

/-- The exact mixed trace has a path in the ordinary typed equation carrier.
The separate data Z and duplicate source visits retain their physical account. -/
theorem mixed_trace_typed_normalization (relEnv : Engine.RelationEnv)
    (discipline : ReferenceStep.EquationDiscipline) :
    ReferenceStep.TypedEquivalent relEnv language discipline FreeTypeContext.empty [] proc
        (objectFormation []) tracedSource actualTrace.target ∧
      actualTrace.target = tracedTarget ∧ actualTrace.SourceAccount ∧
      (actualTrace.partition.map (fun origin => origin.source.address)).Nodup := by
  have path := reduceAtTagged_typed_equivalent (relEnv := relEnv) homogeneous authorized
    discipline [] FreeTypeContext.empty tracedSource traced_open
  exact ⟨path, mixed_trace_physical_account.2.2.1,
    reduceAtTagged_source_account _ _ _ _ _ _ _,
    (reduceAtTagged_original_partition _ _ _ _ _ _ _).2.1⟩

private def binderInput : Pattern :=
  .lambda none (.multiLambda 2 [] (bag [bag [.bvar 3,.bvar 0,.bvar 1,.bvar 0],z]))
private def binderOutput : Pattern :=
  .lambda none (.multiLambda 2 [] (bag [.bvar 3,.bvar 0,.bvar 1,.bvar 0]))
private def binderType : TypeExpr := .arrow proc (.arrow (.multiBinder proc) proc)

/-- Lambda and multi-binder scopes retain the ambient variable and both local
binders. The repeated local variable is not collapsed or relabelled. -/
theorem binder_scopes_typed_normalization (relEnv : Engine.RelationEnv)
    (discipline : ReferenceStep.EquationDiscipline) :
    OpenPatternWellSorted language FreeTypeContext.empty [proc] binderType binderInput ∧
      reduceAt (CollectionLaws.declared language) [] language FreeTypeContext.empty [proc]
        binderInput binderType = binderOutput ∧
      ReferenceStep.TypedEquivalent relEnv language discipline FreeTypeContext.empty [proc] binderType
        (objectFormation [proc]) binderInput binderOutput := by
  have typed : HasType language FreeTypeContext.empty [proc] binderInput binderType :=
    checkHasType_sound (by decide +kernel)
  have good : OpenPatternWellSorted language FreeTypeContext.empty [proc] binderType binderInput :=
    ⟨typed,by decide +kernel,by decide +kernel,typed.isWellScopedAt⟩
  have actual : reduceAt (CollectionLaws.declared language) [] language FreeTypeContext.empty [proc]
      binderInput binderType = binderOutput := by cbv
  refine ⟨good,actual,?_⟩
  simpa only [actual] using
    reduceAt_typed_equivalent (relEnv := relEnv) homogeneous authorized discipline []
      FreeTypeContext.empty binderInput good

/-- Actual declared nested-parameter evidence licenses the selected lexical
permutation at a data role. It keeps the unit-valued data and both copies of A. -/
theorem nested_data_lexical_typed_step (relEnv : Engine.RelationEnv)
    (discipline : ReferenceStep.EquationDiscipline) :
    PatternLexOrder.sortLex [b,z,a,a] = [a,a,b,z] ∧
      ReferenceStep.TypedStep relEnv language discipline FreeTypeContext.empty [] dataType
        (objectFormation []) (bag [b,z,a,a]) (bag [a,a,b,z]) := by
  have typed : HasType language FreeTypeContext.empty [] (bag [b,z,a,a]) dataType :=
    checkHasType_sound (by decide +kernel)
  have good : OpenPatternWellSorted language FreeTypeContext.empty [] dataType (bag [b,z,a,a]) :=
    ⟨typed,by decide +kernel,by decide +kernel,typed.isWellScopedAt⟩
  have site : ReferenceStep.CollectionLawSite language .hashBag [b,z,a,a] :=
    .inr ⟨wrapper,by decide +kernel,.simple "data" nestedType,by decide +kernel,
      proc,.element .here,FreeTypeContext.empty,[],typed⟩
  have actual : PatternLexOrder.sortLex [b,z,a,a] = [a,a,b,z] := by decide +kernel
  refine ⟨actual,?_⟩
  simpa only [actual, bag] using lexical_permutation_step (relEnv := relEnv) discipline rfl site good

/-- Same-context typing rules out replacing the result by an arrow-valued
object, even though that object has valid scope and binder metadata. -/
theorem wrong_sort_typed_path_rejected (relEnv : Engine.RelationEnv)
    (discipline : ReferenceStep.EquationDiscipline) :
    ¬ ReferenceStep.TypedEquivalent relEnv language discipline FreeTypeContext.empty [] proc
      (objectFormation []) tracedSource (.lambda none (.bvar 0)) := by
  intro path
  have target := path.formed_right (formed_iff_open.mpr traced_open)
  cases target.typed

/-- An escaping variable is not a well-typed endpoint of this closed fibre. -/
theorem escaping_typed_path_rejected (relEnv : Engine.RelationEnv)
    (discipline : ReferenceStep.EquationDiscipline) :
    ¬ ReferenceStep.TypedEquivalent relEnv language discipline FreeTypeContext.empty [] proc
      (objectFormation []) tracedSource (.bvar 0) := by
  intro path
  have target := path.formed_right (formed_iff_open.mpr traced_open)
  cases target.typed with
  | bvar selected => cases selected

/-- Correct endpoint types do not supply a missing unit declaration. -/
theorem wrong_unit_typed_path_rejected (relEnv : Engine.RelationEnv)
    (discipline : ReferenceStep.EquationDiscipline) :
    ¬ ReferenceStep.TypedEquivalent relEnv unlicensedLanguage discipline FreeTypeContext.empty [] proc
      (objectFormation []) unlicensedSource unlicensedTarget := by
  obtain ⟨_,_,_,_,_,_,refused⟩ := wrong_unit_source_authority relEnv
  intro path
  exact refused path.toDisciplined.toEquivalent

/-- Pending substitution has its existing raw source path. It is schema
syntax, so its nontrivial normalization is outside the object typed carrier. -/
theorem pending_substitution_typed_object_boundary (relEnv : Engine.RelationEnv)
    (discipline : ReferenceStep.EquationDiscipline) :
    ReferenceStep.Equivalent relEnv language subSource subResult ∧
      ¬ ReferenceStep.TypedEquivalent relEnv language discipline FreeTypeContext.empty [proc] proc
        (objectFormation [proc]) subSource subResult := by
  refine ⟨(pending_substitution_scope relEnv).2.2.2.2,?_⟩
  intro path
  rcases path.ends with same | both
  · exact (by decide +kernel : subSource ≠ subResult) same
  · have impossible := both.1.object
    change false = true at impossible
    cases impossible

#print axioms mixed_trace_typed_normalization
#print axioms binder_scopes_typed_normalization
#print axioms nested_data_lexical_typed_step
#print axioms wrong_sort_typed_path_rejected
#print axioms escaping_typed_path_rejected
#print axioms wrong_unit_typed_path_rejected
#print axioms pending_substitution_typed_object_boundary

end Mettapedia.GSLT.LanguageDef.BagNormalForm.RoleAwareSourceControls


namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RoleAwareReadout

open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionLaws CanonicalBags.RoleAware DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem originAt_typed_readout
    {laws : List Laws} {domains : List TypeExpr} {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {source target : Pattern} {expected : TypeExpr}
    (declaration : Option (Nat × GrammarRule))
    (typed : HasType language free bound source expected)
    (readout : target = reduceAt laws domains language free bound source expected) :
    ∃ role, (originAt bound (some expected) declaration source target).expected = some role ∧
      TypedAt language free (originAt bound (some expected) declaration source target).source.original
        (originAt bound (some expected) declaration source target).source.context
        bound expected (originAt bound (some expected) declaration source target).bound role ∧
      (originAt bound (some expected) declaration source target).source.value =
        reduceAt laws domains language free (originAt bound (some expected) declaration source target).bound
          (originAt bound (some expected) declaration source target).source.original role :=
  ⟨expected,rfl,.here typed,readout⟩

private theorem original_underContext_typedAt
    {language : LanguageDef} {free : FreeTypeContext}
    {rootBound localBound : List TypeExpr} {rootType localType expected : TypeExpr}
    {source : Pattern} {origin : TypedOrigin} {frame : OneHoleContext}
    (rooted : origin.source.context.fill origin.source.original = source)
    (outer : TypedAt language free source frame rootBound rootType localBound localType)
    (inner : TypedAt language free origin.source.original origin.source.context
      localBound localType origin.bound expected) :
    TypedAt language free (origin.underContext frame).source.original
      (origin.underContext frame).source.context rootBound rootType
      (origin.underContext frame).bound expected := by
  have outerRead : TypedAt language free (origin.source.context.fill origin.source.original)
      frame rootBound rootType localBound localType := by
    rw [rooted]
    exact outer
  exact outerRead.comp inner

private theorem liftedChildren_nil_readout (frame : Nat → OneHoleContext) (start : Nat) :
    liftedChildren frame start [] = [] := rfl

private theorem liftedChildren_cons_readout (frame : Nat → OneHoleContext) (start : Nat)
    (child : TaggedReduction) (children : List TaggedReduction) :
    liftedChildren frame start (child :: children) =
      child.underContext (frame start) :: liftedChildren frame (start + 1) children := rfl

private theorem liftedChildren_visited_at
    (frame : Nat → OneHoleContext) (start : Nat) (children : List TaggedReduction)
    {origin : TypedOrigin}
    (member : origin ∈ (liftedChildren frame start children).flatMap TaggedReduction.visited) :
    ∃ (index : Nat) (child : TaggedReduction) (inner : TypedOrigin), children[index]? = some child ∧ inner ∈ child.visited ∧
      origin = inner.underContext (frame (start + index)) := by
  induction children generalizing start with
  | nil => simp only [liftedChildren_nil_readout,List.flatMap_nil,List.not_mem_nil] at member
  | cons child children recurse =>
      simp only [liftedChildren_cons_readout,List.flatMap_cons,List.mem_append] at member
      rcases member with head | tail
      · simp only [TaggedReduction.underContext,List.mem_map] at head
        obtain ⟨inner,innerMember,rfl⟩ := head
        exact ⟨0,child,inner,rfl,innerMember,by simp only [Nat.add_zero]⟩
      · obtain ⟨index,selected,inner,atIndex,innerMember,actual⟩ := recurse (start + 1) tail
        refine ⟨index + 1,selected,inner,?_,innerMember,?_⟩
        · simpa only [List.getElem?_cons_succ] using atIndex
        · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using actual

private theorem reduceArgumentsTagged_at
    (laws : List Laws) (domains : List TypeExpr) {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {arguments : List Pattern} {parameterRows : List TermParam}
    (typed : ArgumentsHaveTypes language free bound arguments parameterRows) :
    ∀ (index : Nat) (trace : TaggedReduction), (reduceArgumentsTagged laws domains language free bound arguments parameterRows)[index]? = some trace →
      ∃ argument parameter expected,
        arguments[index]? = some argument ∧ parameterRows[index]? = some parameter ∧
        parameterType? parameter = some expected ∧
        trace = reduceAtTagged laws domains language free bound argument expected ∧
        HasType language free bound argument expected := by
  induction arguments generalizing parameterRows with
  | nil =>
      cases typed
      intro index trace selected
      simp only [reduceArgumentsTagged,List.getElem?_nil] at selected
      cases selected
  | cons argument arguments recurse =>
      cases typed with
      | @cons _ _ _ parameter parameterRows expected representation parameterType headTyped tailTyped =>
          intro index trace selected
          cases index with
          | zero =>
              have actual : reduceAtTagged laws domains language free bound argument expected = trace := by
                simpa only [reduceArgumentsTagged,parameterType,List.getElem?_cons_zero,Option.some.injEq] using selected
              subst trace
              exact ⟨argument,parameter,expected,rfl,rfl,parameterType,rfl,headTyped⟩
          | succ index =>
              have later : (reduceArgumentsTagged laws domains language free bound arguments parameterRows)[index]? = some trace := by
                simpa only [reduceArgumentsTagged,parameterType,List.getElem?_cons_succ] using selected
              obtain ⟨item,row,role,atArgument,atParameter,rowType,traceRead,itemTyped⟩ := recurse tailTyped index trace later
              exact ⟨item,row,role,by simpa only [List.getElem?_cons_succ] using atArgument,
                by simpa only [List.getElem?_cons_succ] using atParameter,rowType,traceRead,itemTyped⟩

private theorem reduceElementsTagged_at
    (laws : List Laws) (domains : List TypeExpr) {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {elements : List Pattern} {expected : TypeExpr}
    (typed : ElementsHaveType language free bound elements expected) :
    ∀ (index : Nat) (trace : TaggedReduction), (reduceElementsTagged laws domains language free bound elements expected)[index]? = some trace →
      ∃ element, elements[index]? = some element ∧
        trace = reduceAtTagged laws domains language free bound element expected ∧
        HasType language free bound element expected := by
  induction elements with
  | nil =>
      intro index trace selected
      simp only [reduceElementsTagged,List.getElem?_nil] at selected
      cases selected
  | cons element elements recurse =>
      cases typed with
      | cons headTyped tailTyped =>
          intro index trace selected
          cases index with
          | zero =>
              have actual : reduceAtTagged laws domains language free bound element expected = trace := by
                simpa only [reduceElementsTagged,List.getElem?_cons_zero,Option.some.injEq] using selected
              subst trace
              exact ⟨element,rfl,rfl,headTyped⟩
          | succ index =>
              have later : (reduceElementsTagged laws domains language free bound elements expected)[index]? = some trace := by
                simpa only [reduceElementsTagged,List.getElem?_cons_succ] using selected
              obtain ⟨item,atElement,traceRead,itemTyped⟩ := recurse tailTyped index trace later
              exact ⟨item,by simpa only [List.getElem?_cons_succ] using atElement,traceRead,itemTyped⟩

private theorem opaqueTrace_visits (bound : List TypeExpr) (expected : Option TypeExpr)
    (source : Pattern) (complete : Bool) :
    (opaqueTrace bound expected source complete).visited = [(opaqueTrace bound expected source complete).root] := rfl

private theorem assembleTrace_visits (bound : List TypeExpr) (expected : TypeExpr)
    (declaration : Option (Nat × GrammarRule)) (source target : Pattern) (children : List TaggedReduction) :
    (assembleTrace bound expected declaration source target children).visited =
      (assembleTrace bound expected declaration source target children).root :: children.flatMap TaggedReduction.visited := rfl

private theorem algebraTrace_visits (laws : List Laws) (bound : List TypeExpr) (expected : TypeExpr)
    (declaration : Nat × GrammarRule) (source : Pattern) (kind : CollType) (rest : Option String)
    (children : List TaggedReduction) :
    (algebraTrace laws bound expected declaration source kind rest children).visited =
      (algebraTrace laws bound expected declaration source kind rest children).root :: children.flatMap TaggedReduction.visited := rfl

private theorem tagged_root_at (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (source : Pattern) (expected : TypeExpr) :
    ∃ declaration, (reduceAtTagged laws domains language free bound source expected).root =
      originAt bound (some expected) declaration source
        (reduceAtTagged laws domains language free bound source expected).target := by
  cases source with
  | bvar index => exact ⟨none,by simp only [reduceAtTagged]; rfl⟩
  | fvar identifier => exact ⟨none,by simp only [reduceAtTagged]; rfl⟩
  | apply label arguments =>
      cases selected : applicationRule? domains language free bound expected label arguments with
      | none => exact ⟨none,by simp only [reduceAtTagged,selected]; rfl⟩
      | some rule => exact ⟨some (language.terms.idxOf rule,rule),by simp only [reduceAtTagged,selected]; rfl⟩
  | lambda display body => cases expected <;> exact ⟨none,by simp only [reduceAtTagged]; rfl⟩
  | multiLambda arity displays body =>
      cases expected with
      | arrow domain codomain => cases domain <;> exact ⟨none,by simp only [reduceAtTagged]; rfl⟩
      | base category => exact ⟨none,by simp only [reduceAtTagged]; rfl⟩
      | collection kind element => exact ⟨none,by simp only [reduceAtTagged]; rfl⟩
      | multiBinder body => exact ⟨none,by simp only [reduceAtTagged]; rfl⟩
  | subst body replacement =>
      cases selected : substitutionDomain? domains language free bound expected body replacement with
      | none => exact ⟨none,by simp only [reduceAtTagged,selected]; rfl⟩
      | some domain => exact ⟨none,by simp only [reduceAtTagged,selected]; rfl⟩
  | collection kind elements rest =>
      cases expected with
      | collection actual element =>
          by_cases same : actual = kind
          · exact ⟨none,by simp only [reduceAtTagged,same,↓reduceIte]; rfl⟩
          · exact ⟨none,by simp only [reduceAtTagged,same,↓reduceIte]; rfl⟩
      | base category =>
          cases selected : collectionRule? domains language free bound (.base category) kind elements rest with
          | none => exact ⟨none,by simp only [reduceAtTagged,selected]; rfl⟩
          | some rule =>
              cases element : bareCollectionElementType? rule kind (.base category) with
              | none => exact ⟨none,by simp only [reduceAtTagged,selected,element]; rfl⟩
              | some elementType => exact ⟨some (language.terms.idxOf rule,rule),by simp only [reduceAtTagged,selected,element]; rfl⟩
      | arrow domain codomain =>
          cases selected : collectionRule? domains language free bound (.arrow domain codomain) kind elements rest with
          | none => exact ⟨none,by simp only [reduceAtTagged,selected]; rfl⟩
          | some rule =>
              cases element : bareCollectionElementType? rule kind (.arrow domain codomain) with
              | none => exact ⟨none,by simp only [reduceAtTagged,selected,element]; rfl⟩
              | some elementType => exact ⟨some (language.terms.idxOf rule,rule),by simp only [reduceAtTagged,selected,element]; rfl⟩
      | multiBinder domain =>
          cases selected : collectionRule? domains language free bound (.multiBinder domain) kind elements rest with
          | none => exact ⟨none,by simp only [reduceAtTagged,selected]; rfl⟩
          | some rule =>
              cases element : bareCollectionElementType? rule kind (.multiBinder domain) with
              | none => exact ⟨none,by simp only [reduceAtTagged,selected,element]; rfl⟩
              | some elementType => exact ⟨some (language.terms.idxOf rule,rule),by simp only [reduceAtTagged,selected,element]; rfl⟩

private theorem tagged_root_typed_readout
    (laws : List Laws) (domains : List TypeExpr) {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {source : Pattern} {expected : TypeExpr}
    (typed : HasType language free bound source expected) :
    let origin := (reduceAtTagged laws domains language free bound source expected).root
    ∃ role, origin.expected = some role ∧
      TypedAt language free origin.source.original origin.source.context bound expected origin.bound role ∧
      origin.source.value = reduceAt laws domains language free origin.bound origin.source.original role ∧
      origin.declaration = (reduceAtTagged laws domains language free origin.bound origin.source.original role).root.declaration := by
  dsimp only
  obtain ⟨declaration,rootRead⟩ := tagged_root_at laws domains language free bound source expected
  rw [rootRead]
  refine ⟨expected,rfl,.here typed,reduceAtTagged_target laws domains language free source bound expected,?_⟩
  exact (congrArg TypedOrigin.declaration rootRead).symm

private theorem element_slot_typedAt
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {kind : CollType} {element parentType : TypeExpr}
    (role : parentType = .collection kind element ∨
      ∃ rule parameter, rule ∈ language.terms ∧
        rule.bareParams = [.simple parameter (.collection kind element)] ∧ parentType = .base rule.category)
    {elements : List Pattern} {item : Pattern} {index : Nat}
    (typed : ElementsHaveType language free bound elements element) (selected : elements[index]? = some item) :
    TypedAt language free item
      (.collection kind (elements.take index) .hole (elements.drop (index + 1)) none)
      bound parentType bound element := by
  have allTyped : ElementsHaveType language free bound
      (elements.take index ++ item :: elements.drop (index + 1)) element := by
    rw [raw_source_reconstruct selected]
    exact typed
  have itemTyped := CanonicalBags.elementsHaveType_iff.mp typed item (List.mem_of_getElem? selected)
  rcases role with rfl | ⟨rule,parameter,declared,shape,rfl⟩
  · exact .collection allTyped (.here itemTyped)
  · exact .collectionConstructor declared shape allTyped (.here itemTyped)

/-- Every actual source visit retains its globally typed original zipper,
its exact selected caller role and the recorded local reducer result. No
algebra authority or equality of arbitrary typing derivations is assumed. -/
theorem reduceAtTagged_visits_typedAt
    (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef) (free : FreeTypeContext)
    (source : Pattern) :
    ∀ {bound : List TypeExpr} {expected : TypeExpr}, HasType language free bound source expected →
      isObjectPattern source = true →
      ∀ origin ∈ (reduceAtTagged laws domains language free bound source expected).visited,
        ∃ role, origin.expected = some role ∧
          TypedAt language free origin.source.original origin.source.context bound expected origin.bound role ∧
          origin.source.value = reduceAt laws domains language free origin.bound origin.source.original role ∧
          origin.declaration = (reduceAtTagged laws domains language free origin.bound origin.source.original role).root.declaration := by
  induction source using Pattern.inductionOn with
  | hbvar index =>
      intro bound expected typed object origin member
      simp only [reduceAtTagged,opaqueTrace_visits,List.mem_singleton] at member
      subst origin
      simpa only [reduceAtTagged,↓reduceIte] using tagged_root_typed_readout laws domains typed
  | hfvar identifier =>
      intro bound expected typed object origin member
      simp only [reduceAtTagged,opaqueTrace_visits,List.mem_singleton] at member
      subst origin
      simpa only [reduceAtTagged,↓reduceIte] using tagged_root_typed_readout laws domains typed
  | happly label arguments recurse =>
      intro bound expected typed object origin member
      cases selected : applicationRule? domains language free bound expected label arguments with
      | none =>
          simp only [reduceAtTagged,selected,opaqueTrace_visits,List.mem_singleton] at member
          subst origin
          simpa only [reduceAtTagged,selected] using tagged_root_typed_readout laws domains typed
      | some rule =>
          obtain ⟨declared,head,expectedEq,ordinary,argumentsTyped⟩ := applicationRule_readout selected
          simp only [reduceAtTagged,selected,assembleTrace_visits,List.mem_cons] at member
          rcases member with root | childMember
          · subst origin
            simpa only [reduceAtTagged,selected] using tagged_root_typed_readout laws domains typed
          · obtain ⟨index,child,inner,atChild,innerMember,rfl⟩ := liftedChildren_visited_at _ 0 _ childMember
            obtain ⟨argument,parameter,argumentType,atArgument,atParameter,parameterType,childRead,argumentTyped⟩ :=
              reduceArgumentsTagged_at laws domains argumentsTyped index child atChild
            subst child
            have argumentObject := (isObjectPatternList_iff).mp object argument (List.mem_of_getElem? atArgument)
            obtain ⟨role,expectedRead,innerTyped,valueRead,headerRead⟩ :=
              recurse argument (List.mem_of_getElem? atArgument) argumentTyped argumentObject inner innerMember
            have outer : TypedAt language free argument
                (.apply label (arguments.take index) .hole (arguments.drop (index + 1))) bound expected bound argumentType := by
              simpa only [head,expectedEq] using
                (RecursiveView.argument_slot_typedAt declared ordinary argumentsTyped atArgument atParameter parameterType)
            have rooted := reduceAtTagged_original_points laws domains language free argument bound argumentType inner innerMember
            exact ⟨role,expectedRead,by simpa only [Nat.zero_add] using original_underContext_typedAt rooted.1 outer innerTyped,valueRead,headerRead⟩
  | hlambda display body recurse =>
      intro bound expected typed object origin member
      cases typed with
      | lambda bodyTyped =>
          simp only [reduceAtTagged,assembleTrace_visits,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.mem_cons] at member
          rcases member with root | childMember
          · subst origin
            simpa only [reduceAtTagged,↓reduceIte] using tagged_root_typed_readout laws domains (HasType.lambda (binder := display) bodyTyped)
          · simp only [TaggedReduction.underContext,List.mem_map] at childMember
            obtain ⟨inner,innerMember,rfl⟩ := childMember
            obtain ⟨role,expectedRead,innerTyped,valueRead,headerRead⟩ := recurse bodyTyped object inner innerMember
            have rooted := reduceAtTagged_original_points laws domains language free body _ _ inner innerMember
            exact ⟨role,expectedRead,original_underContext_typedAt rooted.1 (TypedAt.lambda (.here bodyTyped)) innerTyped,valueRead,headerRead⟩
  | hmultiLambda arity displays body recurse =>
      intro bound expected typed object origin member
      cases typed with
      | multiLambda bodyTyped =>
          simp only [reduceAtTagged,assembleTrace_visits,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.mem_cons] at member
          rcases member with root | childMember
          · subst origin
            simpa only [reduceAtTagged,↓reduceIte] using tagged_root_typed_readout laws domains (HasType.multiLambda (arity := arity) (binders := displays) bodyTyped)
          · simp only [TaggedReduction.underContext,List.mem_map] at childMember
            obtain ⟨inner,innerMember,rfl⟩ := childMember
            obtain ⟨role,expectedRead,innerTyped,valueRead,headerRead⟩ := recurse bodyTyped object inner innerMember
            have rooted := reduceAtTagged_original_points laws domains language free body _ _ inner innerMember
            exact ⟨role,expectedRead,original_underContext_typedAt rooted.1 (TypedAt.multiLambda (.here bodyTyped)) innerTyped,valueRead,headerRead⟩
  | hsubst body replacement bodyIH replacementIH =>
      intro bound expected typed object origin member
      simp only [isObjectPattern,Bool.false_eq_true] at object
  | hcollection kind elements rest recurse =>
      intro bound expected typed object origin member
      have closed : rest = none := by
        have shape := object
        simp only [isObjectPattern,Bool.and_eq_true] at shape
        cases rest with
        | none => rfl
        | some identifier => cases shape.1
      subst rest
      have objects : isObjectPatternList elements = true := (Bool.and_eq_true_iff.mp object).2
      rcases CanonicalBags.hasType_collection_inv typed with ⟨element,rfl,items⟩ |
        ⟨sourceRule,sourceParameter,sourceElement,sourceDeclared,sourceShape,rfl,sourceItems⟩
      · simp only [reduceAtTagged,↓reduceIte,assembleTrace_visits,List.mem_cons] at member
        rcases member with root | childMember
        · subst origin
          simpa only [reduceAtTagged,↓reduceIte] using tagged_root_typed_readout laws domains typed
        · obtain ⟨index,child,inner,atChild,innerMember,rfl⟩ := liftedChildren_visited_at _ 0 _ childMember
          obtain ⟨item,atItem,childRead,itemTyped⟩ := reduceElementsTagged_at laws domains items index child atChild
          subst child
          have itemObject := (isObjectPatternList_iff).mp objects item (List.mem_of_getElem? atItem)
          obtain ⟨role,expectedRead,innerTyped,valueRead,headerRead⟩ := recurse item (List.mem_of_getElem? atItem) itemTyped itemObject inner innerMember
          have outer := element_slot_typedAt (kind := kind) (.inl rfl) items atItem
          have rooted := reduceAtTagged_original_points laws domains language free item bound element inner innerMember
          exact ⟨role,expectedRead,by simpa only [Nat.zero_add] using original_underContext_typedAt rooted.1 outer innerTyped,valueRead,headerRead⟩
      · cases selected : collectionRule? domains language free bound (.base sourceRule.category) kind elements none with
        | none =>
            simp only [reduceAtTagged,selected,opaqueTrace_visits,List.mem_singleton] at member
            subst origin
            simpa only [reduceAtTagged,selected] using tagged_root_typed_readout laws domains typed
        | some rule =>
            obtain ⟨element,declared,elementRead,items⟩ := collectionRule_readout selected
            obtain ⟨expectedEq,parameter,shape⟩ := (bareCollectionElementType?_eq_some_iff _ _ _ _).mp elementRead
            simp only [reduceAtTagged,selected,elementRead,algebraTrace_visits,List.mem_cons] at member
            rcases member with root | childMember
            · subst origin
              simpa only [reduceAtTagged,selected,elementRead] using tagged_root_typed_readout laws domains typed
            · obtain ⟨index,child,inner,atChild,innerMember,rfl⟩ := liftedChildren_visited_at _ 0 _ childMember
              obtain ⟨item,atItem,childRead,itemTyped⟩ := reduceElementsTagged_at laws domains items index child atChild
              subst child
              have itemObject := (isObjectPatternList_iff).mp objects item (List.mem_of_getElem? atItem)
              obtain ⟨role,expectedRead,innerTyped,valueRead,headerRead⟩ := recurse item (List.mem_of_getElem? atItem) itemTyped itemObject inner innerMember
              have outer := element_slot_typedAt (.inr ⟨rule,parameter,declared,shape,expectedEq⟩) items atItem
              have rooted := reduceAtTagged_original_points laws domains language free item bound element inner innerMember
              exact ⟨role,expectedRead,by simpa only [Nat.zero_add] using original_underContext_typedAt rooted.1 outer innerTyped,valueRead,headerRead⟩

private theorem tagged_root_declaration
    (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (source : Pattern) (expected : TypeExpr) {index : Nat} {rule : GrammarRule}
    (recorded : (reduceAtTagged laws domains language free bound source expected).root.declaration = some (index,rule)) :
    language.terms[index]? = some rule := by
  cases source with
  | bvar identifier =>
      simp only [reduceAtTagged] at recorded
      change none = some (index,rule) at recorded
      cases recorded
  | fvar identifier =>
      simp only [reduceAtTagged] at recorded
      change none = some (index,rule) at recorded
      cases recorded
  | apply label arguments =>
      cases selected : applicationRule? domains language free bound expected label arguments with
      | none =>
          simp only [reduceAtTagged,selected] at recorded
          change none = some (index,rule) at recorded
          cases recorded
      | some chosen =>
          obtain ⟨declared,_,_,_,_⟩ := applicationRule_readout selected
          simp only [reduceAtTagged,selected] at recorded
          change some (language.terms.idxOf chosen,chosen) = some (index,rule) at recorded
          have indexEq := congrArg Prod.fst (Option.some.inj recorded)
          have ruleEq := congrArg Prod.snd (Option.some.inj recorded)
          change language.terms.idxOf chosen = index at indexEq
          change chosen = rule at ruleEq
          rw [← indexEq,← ruleEq]
          exact List.getElem?_idxOf declared
  | lambda display body =>
      cases expected <;> simp only [reduceAtTagged] at recorded <;>
        change none = some (index,rule) at recorded <;> cases recorded
  | multiLambda arity displays body =>
      cases expected with
      | arrow domain codomain =>
          cases domain <;> simp only [reduceAtTagged] at recorded <;>
            change none = some (index,rule) at recorded <;> cases recorded
      | base category =>
          simp only [reduceAtTagged] at recorded
          change none = some (index,rule) at recorded
          cases recorded
      | collection kind element =>
          simp only [reduceAtTagged] at recorded
          change none = some (index,rule) at recorded
          cases recorded
      | multiBinder domain =>
          simp only [reduceAtTagged] at recorded
          change none = some (index,rule) at recorded
          cases recorded
  | subst body replacement =>
      cases selected : substitutionDomain? domains language free bound expected body replacement <;>
        simp only [reduceAtTagged,selected] at recorded <;>
        change none = some (index,rule) at recorded <;> cases recorded
  | collection kind elements rest =>
      cases expected with
      | collection actual element =>
          by_cases same : actual = kind <;> simp only [reduceAtTagged,same,↓reduceIte] at recorded <;>
            change none = some (index,rule) at recorded <;> cases recorded
      | base category =>
          cases selected : collectionRule? domains language free bound (.base category) kind elements rest with
          | none =>
              simp only [reduceAtTagged,selected] at recorded
              change none = some (index,rule) at recorded
              cases recorded
          | some chosen =>
              obtain ⟨element,declared,elementRead,_⟩ := collectionRule_readout selected
              simp only [reduceAtTagged,selected,elementRead] at recorded
              change some (language.terms.idxOf chosen,chosen) = some (index,rule) at recorded
              have indexEq := congrArg Prod.fst (Option.some.inj recorded)
              have ruleEq := congrArg Prod.snd (Option.some.inj recorded)
              change language.terms.idxOf chosen = index at indexEq
              change chosen = rule at ruleEq
              rw [← indexEq,← ruleEq]
              exact List.getElem?_idxOf declared
      | arrow domain codomain =>
          cases selected : collectionRule? domains language free bound (.arrow domain codomain) kind elements rest with
          | none =>
              simp only [reduceAtTagged,selected] at recorded
              change none = some (index,rule) at recorded
              cases recorded
          | some chosen =>
              obtain ⟨element,declared,elementRead,_⟩ := collectionRule_readout selected
              simp only [reduceAtTagged,selected,elementRead] at recorded
              change some (language.terms.idxOf chosen,chosen) = some (index,rule) at recorded
              have indexEq := congrArg Prod.fst (Option.some.inj recorded)
              have ruleEq := congrArg Prod.snd (Option.some.inj recorded)
              change language.terms.idxOf chosen = index at indexEq
              change chosen = rule at ruleEq
              rw [← indexEq,← ruleEq]
              exact List.getElem?_idxOf declared
      | multiBinder domain =>
          cases selected : collectionRule? domains language free bound (.multiBinder domain) kind elements rest with
          | none =>
              simp only [reduceAtTagged,selected] at recorded
              change none = some (index,rule) at recorded
              cases recorded
          | some chosen =>
              obtain ⟨element,declared,elementRead,_⟩ := collectionRule_readout selected
              simp only [reduceAtTagged,selected,elementRead] at recorded
              change some (language.terms.idxOf chosen,chosen) = some (index,rule) at recorded
              have indexEq := congrArg Prod.fst (Option.some.inj recorded)
              have ruleEq := congrArg Prod.snd (Option.some.inj recorded)
              change language.terms.idxOf chosen = index at indexEq
              change chosen = rule at ruleEq
              rw [← indexEq,← ruleEq]
              exact List.getElem?_idxOf declared

/-- A retained local declaration is the actual row at its recorded original
signature position. Rootedness and equal output values cannot supply this
header fact for a forged source record. -/
theorem reduceAtTagged_visits_declared
    (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef) (free : FreeTypeContext)
    (source : Pattern) {bound : List TypeExpr} {expected : TypeExpr}
    (typed : HasType language free bound source expected) (object : isObjectPattern source = true)
    {origin : TypedOrigin} (member : origin ∈ (reduceAtTagged laws domains language free bound source expected).visited)
    {index : Nat} {rule : GrammarRule} (recorded : origin.declaration = some (index,rule)) :
    language.terms[index]? = some rule := by
  obtain ⟨role,_,_,_,headerRead⟩ := reduceAtTagged_visits_typedAt laws domains language free source typed object origin member
  apply tagged_root_declaration laws domains language free origin.bound origin.source.original role
  rw [← headerRead]
  exact recorded

private theorem canonical_of_context_fill (context : OneHoleContext) {focus : Pattern}
    (canonical : (context.fill focus).hasCanonicalBinderMetadata = true) :
    focus.hasCanonicalBinderMetadata = true := by
  induction context with
  | hole => exact canonical
  | apply label before inner after recurse =>
      have children : Pattern.hasCanonicalBinderMetadataList (before ++ inner.fill focus :: after) = true := canonical
      exact recurse ((hasCanonicalBinderMetadataList_iff).mp children _ (by simp))
  | lambda display inner recurse => exact recurse (Bool.and_eq_true_iff.mp canonical).2
  | multiLambda arity displays inner recurse => exact recurse (Bool.and_eq_true_iff.mp canonical).2
  | substBody inner replacement recurse => exact recurse (Bool.and_eq_true_iff.mp canonical).1
  | substReplacement body inner recurse => exact recurse (Bool.and_eq_true_iff.mp canonical).2
  | collection kind before inner after rest recurse =>
      have children : Pattern.hasCanonicalBinderMetadataList (before ++ inner.fill focus :: after) = true := canonical
      exact recurse ((hasCanonicalBinderMetadataList_iff).mp children _ (by simp))

private theorem original_visit_open
    {laws : List Laws} {domains : List TypeExpr} {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {expected role : TypeExpr} {source : Pattern} {origin : TypedOrigin}
    (good : OpenPatternWellSorted language free bound expected source)
    (member : origin ∈ (reduceAtTagged laws domains language free bound source expected).visited)
    (selected : TypedAt language free origin.source.original origin.source.context bound expected origin.bound role) :
    OpenPatternWellSorted language free origin.bound role origin.source.original := by
  have rooted := reduceAtTagged_original_points laws domains language free source bound expected origin member
  have canonical : origin.source.original.hasCanonicalBinderMetadata = true :=
    canonical_of_context_fill origin.source.context (by rw [rooted.1]; exact good.2.1)
  have object : isObjectPattern origin.source.original = true :=
    object_of_fill origin.source.context origin.source.original (by rw [rooted.1]; exact good.2.2.1)
  exact ⟨selected.focus_typed,canonical,object,selected.focus_typed.isWellScopedAt⟩

/-- The original visit and its recorded value have an actual typed source-law
path at the earned local role. This does not identify an output address with
an original address or choose a different declaration for an equal value. -/
theorem reduceAtTagged_visit_typed_equivalent
    {laws : List Laws} {language : LanguageDef} {relEnv : Engine.RelationEnv}
    (checked : checkBareHomogeneous laws language = true) (authorized : SourceAlgebras laws language)
    (discipline : ReferenceStep.EquationDiscipline) (domains : List TypeExpr) (free : FreeTypeContext)
    (source : Pattern) {bound : List TypeExpr} {expected : TypeExpr}
    (good : OpenPatternWellSorted language free bound expected source)
    {origin : TypedOrigin} (member : origin ∈ (reduceAtTagged laws domains language free bound source expected).visited) :
    ∃ role, origin.expected = some role ∧
      TypedAt language free origin.source.original origin.source.context bound expected origin.bound role ∧
      ReferenceStep.TypedEquivalent relEnv language discipline free origin.bound role (TypedPaths.objectFormation origin.bound)
        origin.source.original origin.source.value ∧
      origin.declaration = (reduceAtTagged laws domains language free origin.bound origin.source.original role).root.declaration := by
  obtain ⟨role,expectedRead,selected,valueRead,headerRead⟩ :=
    reduceAtTagged_visits_typedAt laws domains language free source good.1 good.2.2.1 origin member
  have focused := original_visit_open good member selected
  have path := TypedPaths.reduceAt_typed_equivalent (relEnv := relEnv) checked authorized discipline domains free origin.source.original focused
  rw [← valueRead] at path
  exact ⟨role,expectedRead,selected,path,headerRead⟩

/-- The actual source zipper earns a full sort prefix. Any successful inverse
capture of its recorded normalized value retains that role and the exact
contextual headers at arbitrary dependency and binder arity. This reads
success; it does not assert recovery succeeds across every equation. -/
theorem reduceAtTagged_visit_capture_readout
    {laws : List Laws} {language : LanguageDef} {relEnv : Engine.RelationEnv}
    (checked : checkBareHomogeneous laws language = true) (authorized : SourceAlgebras laws language)
    (discipline : ReferenceStep.EquationDiscipline) (domains : List TypeExpr) (free : FreeTypeContext)
    (source : Pattern) {bound : List TypeExpr} {expected : TypeExpr}
    (good : OpenPatternWellSorted language free bound expected source)
    {origin : TypedOrigin} (member : origin ∈ (reduceAtTagged laws domains language free bound source expected).visited) :
    ∃ role locals, origin.expected = some role ∧ origin.bound = locals ++ bound ∧
      Admissible language free (locals ++ bound) role origin.source.value ∧
      ∀ (dependencies : List TypeExpr) (arguments : List Pattern) (indices : List Nat) (value : RuleBinding.ContextualValue),
        RuleBinding.variableSpine? locals.length arguments = some indices →
        RestAwareTyping.PartialSortedSpine dependencies locals indices →
        RuleBinding.recoverValue? dependencies bound.length locals.length arguments origin.source.value = some value →
          value.dependencies = dependencies ∧ value.ambient = bound.length ∧
          Admissible language free (dependencies ++ bound) role value.body := by
  obtain ⟨role,expectedRead,selected,path,headerRead⟩ :=
    reduceAtTagged_visit_typed_equivalent (relEnv := relEnv) checked authorized discipline domains free source good member
  obtain ⟨locals,boundRead⟩ := selected.ambient_suffix
  have focused := original_visit_open good member selected
  have formed := path.formed_right (TypedPaths.formed_iff_open.mpr focused)
  have valueGood : Admissible language free origin.bound role origin.source.value :=
    ⟨formed.typed,formed.formed.1,formed.object⟩
  rw [boundRead] at valueGood
  refine ⟨role,locals,expectedRead,boundRead,valueGood,?_⟩
  intro dependencies arguments indices value spineCheck spine recovered
  exact RecursiveView.recoverValue?_admissible_from_success spineCheck spine valueGood recovered

#print axioms reduceAtTagged_visit_typed_equivalent
#print axioms reduceAtTagged_visit_capture_readout

#print axioms tagged_root_declaration
#print axioms reduceAtTagged_visits_declared

#print axioms tagged_root_at
#print axioms tagged_root_typed_readout
#print axioms element_slot_typedAt
#print axioms reduceAtTagged_visits_typedAt

#print axioms originAt_typed_readout
#print axioms original_underContext_typedAt
#print axioms liftedChildren_visited_at
#print axioms reduceArgumentsTagged_at
#print axioms reduceElementsTagged_at

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RoleAwareReadout


namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.RoleAwareSourceControls

open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionLaws CanonicalBags.RoleAware DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted
open WithAuthoredEquations.AlgebraFocus RoleAwareReadout TypedPaths

/-- Every mixed-trace visit has its actual typed original zipper, local
normalization path and original declaration index. Equal tokens stay separate
members of the already conserved physical visit list. -/
theorem mixed_visits_typed_readback (relEnv : Engine.RelationEnv)
    (discipline : ReferenceStep.EquationDiscipline) :
    ∀ origin ∈ actualTrace.visited, ∃ role, origin.expected = some role ∧
      TypedAt language FreeTypeContext.empty origin.source.original origin.source.context [] proc origin.bound role ∧
      ReferenceStep.TypedEquivalent relEnv language discipline FreeTypeContext.empty origin.bound role
        (objectFormation origin.bound) origin.source.original origin.source.value ∧
      ∀ index declaration, origin.declaration = some (index,declaration) → language.terms[index]? = some declaration := by
  intro origin member
  obtain ⟨role,expectedRead,selected,path,_⟩ :=
    reduceAtTagged_visit_typed_equivalent (relEnv := relEnv) homogeneous authorized discipline []
      FreeTypeContext.empty tracedSource traced_open member
  refine ⟨role,expectedRead,selected,path,?_⟩
  intro index declaration recorded
  exact reduceAtTagged_visits_declared _ _ _ _ _ traced_open.1 traced_open.2.2.1 member recorded

private def nestedDataVisit : TypedOrigin :=
  ⟨⟨tracedData,[0],.apply "Box" [] .hole [bag [bag [a,a],z]],tracedData⟩,[],some nestedType,none⟩

/-- The actual inverse captures a nested data container at its data type.
The inner Z remains data; the recovered body is not silently given P. -/
theorem nested_data_capture_typed_readback (relEnv : Engine.RelationEnv)
    (discipline : ReferenceStep.EquationDiscipline) :
    nestedDataVisit ∈ actualTrace.visited ∧ nestedDataVisit.source.address = [0] ∧
      RuleBinding.recoverValue? [] 0 0 [] nestedDataVisit.source.value = some ⟨[],0,tracedData⟩ ∧
      Admissible language FreeTypeContext.empty [] nestedType tracedData := by
  have member : nestedDataVisit ∈ actualTrace.visited := by decide +kernel
  have recovered : RuleBinding.recoverValue? [] 0 0 [] nestedDataVisit.source.value = some ⟨[],0,tracedData⟩ := by decide +kernel
  obtain ⟨role,locals,expectedRead,boundRead,valueGood,readout⟩ :=
    reduceAtTagged_visit_capture_readout (relEnv := relEnv) homogeneous authorized discipline []
      FreeTypeContext.empty tracedSource traced_open member
  change some nestedType = some role at expectedRead
  cases Option.some.inj expectedRead
  change [] = locals ++ [] at boundRead
  simp only [List.append_nil] at boundRead
  subst locals
  have spine : RestAwareTyping.PartialSortedSpine [] [] [] := by
    constructor <;> simp
  have body := readout [] [] [] ⟨[],0,tracedData⟩ (by decide +kernel) spine recovered
  exact ⟨member,rfl,recovered,body.2.2⟩

private def forgedTraceRoot : TypedOrigin := {actualTrace.root with declaration := some (3,wrapper)}

/-- A genuine original zipper does not validate a forged declaration header.
The actual traversal cannot publish this otherwise unchanged root record. -/
theorem wrong_declared_origin_rejected :
    TypedOrigin.Rooted tracedSource forgedTraceRoot ∧ forgedTraceRoot ∉ actualTrace.visited := by
  have rootMember : actualTrace.root ∈ actualTrace.visited := by decide +kernel
  have rooted := reduceAtTagged_original_points (CollectionLaws.declared language) [] language
    FreeTypeContext.empty tracedSource [] proc actualTrace.root rootMember
  refine ⟨rooted,?_⟩
  intro member
  have declared := reduceAtTagged_visits_declared (CollectionLaws.declared language) [] language
    FreeTypeContext.empty tracedSource traced_open.1 traced_open.2.2.1 member
    (show forgedTraceRoot.declaration = some (3,wrapper) from rfl)
  have refused : language.terms[3]? ≠ some wrapper := by decide +kernel
  exact refused declared

#print axioms mixed_visits_typed_readback
#print axioms nested_data_capture_typed_readback
#print axioms wrong_declared_origin_rejected

end Mettapedia.GSLT.LanguageDef.BagNormalForm.RoleAwareSourceControls

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RoleAwareReadout.OutputSites

open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionLaws CanonicalBags.RoleAware DerivedContexts GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- An existing immutable source visit paired with a structural output site.
The two addresses remain distinct data. Typing is established separately. -/
structure OutputOrigin where
  origin : TypedOrigin
  site : SiteData
  deriving Repr,DecidableEq

mutual
  /-- Read one exact subtree prefix. Records are consumed in their supplied
  order; equality validates the next record instead of searching by value.
  This is finite readout of an account, not runtime initialization. -/
  def readAt (language : LanguageDef) (bound : List TypeExpr) (expected : TypeExpr)
      (target : Pattern) (origins : List TypedOrigin) : Option (List OutputOrigin × List TypedOrigin) :=
    match origins with
    | [] => none
    | origin :: remaining =>
      if origin.bound == bound && origin.expected == some expected && origin.source.value == target then
        let root : OutputOrigin := ⟨origin,SiteData.here bound expected target⟩
        match target with
        | .bvar _ | .fvar _ => some ([root],remaining)
        | .apply label arguments =>
            match origin.declaration with
            | none => none
            | some (declaration,rule) =>
                if language.terms[declaration]? == some rule && rule.label == label &&
                    expected == .base rule.category && !usesBareCollection? rule then do
                  let (children,last) ← readArguments language bound declaration label arguments 0 arguments rule.params remaining
                  pure (root :: children,last)
                else none
        | .lambda display body =>
            match expected with
            | .arrow domain codomain => do
                let (children,last) ← readAt language (domain :: bound) codomain body remaining
                pure (root :: children.map (fun entry =>
                  {entry with site := entry.site.wrapLambda display domain}),last)
            | _ => none
        | .multiLambda arity displays body =>
            match expected with
            | .arrow (.multiBinder domain) codomain => do
                let (children,last) ← readAt language (List.replicate arity domain ++ bound) codomain body remaining
                pure (root :: children.map (fun entry =>
                  {entry with site := entry.site.wrapMultiLambda arity displays domain}),last)
            | _ => none
        | .subst _ _ => none
        | .collection kind elements rest =>
            if rest.isNone then
              match expected with
              | .collection actual element =>
                  if actual == kind then do
                    let (children,last) ← readElements language bound element (.directCollection kind) kind elements 0 elements remaining
                    pure (root :: children,last)
                  else none
              | _ =>
                  match origin.declaration with
                  | none => none
                  | some (declaration,rule) =>
                      if language.terms[declaration]? == some rule then
                        match bareCollectionElementType? rule kind expected with
                        | none => none
                        | some element => do
                            let (children,last) ← readElements language bound element (.authoredCollection declaration) kind elements 0 elements remaining
                            pure (root :: children,last)
                      else none
            else none
      else none
  termination_by sizeOf target

  def readArguments (language : LanguageDef) (bound : List TypeExpr) (declaration : Nat)
      (label : String) (allArguments : List Pattern) (start : Nat) :
      List Pattern → List TermParam → List TypedOrigin → Option (List OutputOrigin × List TypedOrigin)
    | [],[],origins => some ([],origins)
    | argument :: arguments,parameter :: parameterRows,origins =>
        if matchesParameterRepresentation? parameter argument then do
          let expected ← parameterType? parameter
          let (first,afterFirst) ← readAt language bound expected argument origins
          let (later,last) ← readArguments language bound declaration label allArguments (start + 1) arguments parameterRows afterFirst
          pure (first.map (fun entry =>
            {entry with site := entry.site.wrapApplication declaration label allArguments start}) ++ later,last)
        else none
    | _,_,_ => none
  termination_by arguments _ _ => sizeOf arguments

  def readElements (language : LanguageDef) (bound : List TypeExpr) (element : TypeExpr)
      (frame : TypingFrame) (kind : CollType) (allElements : List Pattern) (start : Nat) :
      List Pattern → List TypedOrigin → Option (List OutputOrigin × List TypedOrigin)
    | [],origins => some ([],origins)
    | item :: elements,origins => do
        let (first,afterFirst) ← readAt language bound element item origins
        let (later,last) ← readElements language bound element frame kind allElements (start + 1) elements afterFirst
        pure (first.map (fun entry =>
          {entry with site := entry.site.wrapCollection frame kind allElements start}) ++ later,last)
  termination_by elements _ => sizeOf elements
end

/-- Complete readout refuses trailing records. It does not manufacture or
reuse original visits to fill a missing normalized output occurrence. -/
def readOutput (language : LanguageDef) (bound : List TypeExpr) (expected : TypeExpr)
    (trace : TaggedReduction) : Option (List OutputOrigin) := do
  let (entries,remaining) ← readAt language bound expected trace.target trace.survivors
  if remaining.isEmpty then some entries else none

private theorem wrapped_origins (wrap : SiteData → SiteData) (entries : List OutputOrigin) :
    (entries.map (fun entry => {entry with site := wrap entry.site})).map OutputOrigin.origin =
      entries.map OutputOrigin.origin := by
  simp only [List.map_map]
  rfl

private theorem readArguments_account_of (language : LanguageDef) (bound : List TypeExpr)
    (declaration : Nat) (label : String) (allArguments : List Pattern) (arguments : List Pattern) :
    ∀ (parameterRows : List TermParam) (start : Nat) (origins : List TypedOrigin)
      (entries : List OutputOrigin) (suffix : List TypedOrigin),
      (∀ argument ∈ arguments, ∀ expected origins entries suffix,
        readAt language bound expected argument origins = some (entries,suffix) →
          entries.map OutputOrigin.origin ++ suffix = origins) →
      readArguments language bound declaration label allArguments start arguments parameterRows origins = some (entries,suffix) →
      entries.map OutputOrigin.origin ++ suffix = origins := by
  induction arguments with
  | nil =>
      intro parameterRows start origins entries suffix each accepted
      cases parameterRows with
      | nil =>
          simp only [readArguments,Option.some.injEq] at accepted
          have entriesEq := congrArg Prod.fst accepted
          have suffixEq := congrArg Prod.snd accepted
          change [] = entries at entriesEq
          change origins = suffix at suffixEq
          rw [← entriesEq,← suffixEq]
          rfl
      | cons parameter parameterRows => simp only [readArguments] at accepted; cases accepted
  | cons argument arguments recurse =>
      intro parameterRows start origins entries suffix each accepted
      cases parameterRows with
      | nil => simp only [readArguments] at accepted; cases accepted
      | cons parameter parameterRows =>
          cases representationRead : matchesParameterRepresentation? parameter argument with
          | false => simp only [readArguments,representationRead] at accepted; cases accepted
          | true =>
            simp only [readArguments,representationRead,↓reduceIte] at accepted
            cases parameterRead : parameterType? parameter with
            | none => simp only [parameterRead,Option.bind_eq_bind,Option.bind_none] at accepted; cases accepted
            | some expected =>
                simp only [parameterRead,Option.bind_eq_bind,Option.bind_some,
                  Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at accepted
                obtain ⟨⟨first,afterFirst⟩,firstRead,⟨⟨later,last⟩,laterRead,finished⟩⟩ := accepted
                have firstAccount := each argument (.head _) expected origins first afterFirst firstRead
                have laterAccount := recurse parameterRows (start + 1) afterFirst later last
                  (fun item member => each item (.tail _ member)) laterRead
                have entriesEq := congrArg Prod.fst finished
                have suffixEq := congrArg Prod.snd finished
                change first.map (fun entry => {entry with site := entry.site.wrapApplication declaration label allArguments start}) ++ later = entries at entriesEq
                change last = suffix at suffixEq
                rw [← entriesEq,← suffixEq,List.map_append,wrapped_origins,List.append_assoc,laterAccount,firstAccount]

private theorem readElements_account_of (language : LanguageDef) (bound : List TypeExpr)
    (element : TypeExpr) (frame : TypingFrame) (kind : CollType) (allElements : List Pattern) (elements : List Pattern) :
    ∀ (start : Nat) (origins : List TypedOrigin) (entries : List OutputOrigin) (suffix : List TypedOrigin),
      (∀ item ∈ elements, ∀ origins entries suffix,
        readAt language bound element item origins = some (entries,suffix) →
          entries.map OutputOrigin.origin ++ suffix = origins) →
      readElements language bound element frame kind allElements start elements origins = some (entries,suffix) →
      entries.map OutputOrigin.origin ++ suffix = origins := by
  induction elements with
  | nil =>
      intro start origins entries suffix each accepted
      simp only [readElements,Option.some.injEq] at accepted
      have entriesEq := congrArg Prod.fst accepted
      have suffixEq := congrArg Prod.snd accepted
      change [] = entries at entriesEq
      change origins = suffix at suffixEq
      rw [← entriesEq,← suffixEq]
      rfl
  | cons item elements recurse =>
      intro start origins entries suffix each accepted
      simp only [readElements,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at accepted
      obtain ⟨⟨first,afterFirst⟩,firstRead,⟨⟨later,last⟩,laterRead,finished⟩⟩ := accepted
      have firstAccount := each item (.head _) origins first afterFirst firstRead
      have laterAccount := recurse (start + 1) afterFirst later last
        (fun value member => each value (.tail _ member)) laterRead
      have entriesEq := congrArg Prod.fst finished
      have suffixEq := congrArg Prod.snd finished
      change first.map (fun entry => {entry with site := entry.site.wrapCollection frame kind allElements start}) ++ later = entries at entriesEq
      change last = suffix at suffixEq
      rw [← entriesEq,← suffixEq,List.map_append,wrapped_origins,List.append_assoc,laterAccount,firstAccount]

private theorem after_root_account {root : OutputOrigin} {head : TypedOrigin}
    {children entries : List OutputOrigin} {remaining suffix last : List TypedOrigin}
    (headRead : root.origin = head) (returned : (root :: children,last) = (entries,suffix))
    (bodyAccount : children.map OutputOrigin.origin ++ last = remaining) :
    entries.map OutputOrigin.origin ++ suffix = head :: remaining := by
  have entriesEq := congrArg Prod.fst returned
  have suffixEq := congrArg Prod.snd returned
  change root :: children = entries at entriesEq
  change last = suffix at suffixEq
  rw [← entriesEq,← suffixEq,List.map_cons,List.cons_append,headRead,bodyAccount]

/-- Every successful subtree read consumes exactly its original prefix.
Neither missing entries nor equal values allow a source visit to be reused. -/
theorem readAt_account (language : LanguageDef) (target : Pattern) :
    ∀ (bound : List TypeExpr) (expected : TypeExpr) (origins : List TypedOrigin)
      (entries : List OutputOrigin) (suffix : List TypedOrigin),
      readAt language bound expected target origins = some (entries,suffix) →
        entries.map OutputOrigin.origin ++ suffix = origins := by
  induction target using Pattern.inductionOn with
  | hbvar index =>
      intro bound expected origins entries suffix accepted
      cases origins with
      | nil => simp only [readAt] at accepted; cases accepted
      | cons origin remaining =>
          simp only [readAt] at accepted
          split at accepted
          · exact after_root_account rfl (Option.some.inj accepted) rfl
          · cases accepted
  | hfvar identifier =>
      intro bound expected origins entries suffix accepted
      cases origins with
      | nil => simp only [readAt] at accepted; cases accepted
      | cons origin remaining =>
          simp only [readAt] at accepted
          split at accepted
          · exact after_root_account rfl (Option.some.inj accepted) rfl
          · cases accepted
  | happly label arguments recurse =>
      intro bound expected origins entries suffix accepted
      cases origins with
      | nil => simp only [readAt] at accepted; cases accepted
      | cons origin remaining =>
          simp only [readAt] at accepted
          split at accepted
          · cases declarationRead : origin.declaration with
            | none => simp only [declarationRead] at accepted; cases accepted
            | some pair =>
                obtain ⟨declaration,rule⟩ := pair
                simp only [declarationRead] at accepted
                split at accepted
                · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at accepted
                  obtain ⟨⟨children,last⟩,childRead,finished⟩ := accepted
                  have account := readArguments_account_of language bound declaration label arguments arguments
                    rule.params 0 remaining children last (fun child member expected => recurse child member bound expected) childRead
                  exact after_root_account rfl finished account
                · cases accepted
          · cases accepted
  | hlambda display body recurse =>
      intro bound expected origins entries suffix accepted
      cases origins with
      | nil => simp only [readAt] at accepted; cases accepted
      | cons origin remaining =>
          simp only [readAt] at accepted
          split at accepted
          · cases expected with
            | base category => cases accepted
            | collection kind element => cases accepted
            | multiBinder domain => cases accepted
            | arrow domain codomain =>
                simp only [Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at accepted
                obtain ⟨⟨children,last⟩,childRead,finished⟩ := accepted
                have account := recurse (domain :: bound) codomain remaining children last childRead
                exact after_root_account rfl finished (by rw [wrapped_origins]; exact account)
          · cases accepted
  | hmultiLambda arity displays body recurse =>
      intro bound expected origins entries suffix accepted
      cases origins with
      | nil => simp only [readAt] at accepted; cases accepted
      | cons origin remaining =>
          simp only [readAt] at accepted
          split at accepted
          · cases expected with
            | base category => cases accepted
            | collection kind element => cases accepted
            | multiBinder domain => cases accepted
            | arrow domain codomain =>
                cases domain with
                | base category => cases accepted
                | arrow first second => cases accepted
                | collection kind element => cases accepted
                | multiBinder inner =>
                    simp only [Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at accepted
                    obtain ⟨⟨children,last⟩,childRead,finished⟩ := accepted
                    have account := recurse (List.replicate arity inner ++ bound) codomain remaining children last childRead
                    exact after_root_account rfl finished (by rw [wrapped_origins]; exact account)
          · cases accepted
  | hsubst body replacement bodyIH replacementIH =>
      intro bound expected origins entries suffix accepted
      cases origins with
      | nil => simp only [readAt] at accepted; cases accepted
      | cons origin remaining =>
          simp only [readAt] at accepted
          split at accepted <;> cases accepted
  | hcollection kind elements rest recurse =>
      intro bound expected origins entries suffix accepted
      cases origins with
      | nil => simp only [readAt] at accepted; cases accepted
      | cons origin remaining =>
          simp only [readAt] at accepted
          split at accepted
          · split at accepted
            · cases expected with
              | collection actual element =>
                  cases same : (actual == kind) with
                  | true =>
                    simp only [same,↓reduceIte,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at accepted
                    obtain ⟨⟨children,last⟩,childRead,finished⟩ := accepted
                    have account := readElements_account_of language bound element (.directCollection kind) kind elements elements
                      0 remaining children last (fun child member => recurse child member bound element) childRead
                    exact after_root_account rfl finished account
                  | false => simp only [same] at accepted; cases accepted
              | base category =>
                  cases declarationRead : origin.declaration with
                  | none => simp only [declarationRead] at accepted; cases accepted
                  | some pair =>
                      obtain ⟨declaration,rule⟩ := pair
                      simp only [declarationRead] at accepted
                      split at accepted
                      · cases elementRead : bareCollectionElementType? rule kind (.base category) with
                        | none => simp only [elementRead] at accepted; cases accepted
                        | some element =>
                            simp only [elementRead,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at accepted
                            obtain ⟨⟨children,last⟩,childRead,finished⟩ := accepted
                            have account := readElements_account_of language bound element (.authoredCollection declaration) kind elements elements
                              0 remaining children last (fun child member => recurse child member bound element) childRead
                            exact after_root_account rfl finished account
                      · cases accepted
              | arrow domain codomain =>
                  cases declarationRead : origin.declaration with
                  | none => simp only [declarationRead] at accepted; cases accepted
                  | some pair =>
                      obtain ⟨declaration,rule⟩ := pair
                      simp only [declarationRead] at accepted
                      split at accepted
                      · cases elementRead : bareCollectionElementType? rule kind (.arrow domain codomain) with
                        | none => simp only [elementRead] at accepted; cases accepted
                        | some element =>
                            simp only [elementRead,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at accepted
                            obtain ⟨⟨children,last⟩,childRead,finished⟩ := accepted
                            have account := readElements_account_of language bound element (.authoredCollection declaration) kind elements elements
                              0 remaining children last (fun child member => recurse child member bound element) childRead
                            exact after_root_account rfl finished account
                      · cases accepted
              | multiBinder domain =>
                  cases declarationRead : origin.declaration with
                  | none => simp only [declarationRead] at accepted; cases accepted
                  | some pair =>
                      obtain ⟨declaration,rule⟩ := pair
                      simp only [declarationRead] at accepted
                      split at accepted
                      · cases elementRead : bareCollectionElementType? rule kind (.multiBinder domain) with
                        | none => simp only [elementRead] at accepted; cases accepted
                        | some element =>
                            simp only [elementRead,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at accepted
                            obtain ⟨⟨children,last⟩,childRead,finished⟩ := accepted
                            have account := readElements_account_of language bound element (.authoredCollection declaration) kind elements elements
                              0 remaining children last (fun child member => recurse child member bound element) childRead
                            exact after_root_account rfl finished account
                      · cases accepted
            · cases accepted
          · cases accepted

/-- A complete readout accounts for the entire supplied survivor stream,
with no hidden suffix and no origin reconstructed from equal output values. -/
theorem readOutput_account (language : LanguageDef) (bound : List TypeExpr) (expected : TypeExpr)
    (trace : TaggedReduction) (entries : List OutputOrigin)
    (accepted : readOutput language bound expected trace = some entries) :
    entries.map OutputOrigin.origin = trace.survivors := by
  simp only [readOutput,Option.bind_eq_bind,Option.bind_eq_some_iff] at accepted
  obtain ⟨⟨actual,suffix⟩,read,finished⟩ := accepted
  have account := readAt_account language trace.target bound expected trace.survivors actual suffix read
  cases suffix with
  | nil =>
      simp only [List.isEmpty_nil,↓reduceIte,Option.some.injEq] at finished
      subst entries
      simpa only [List.append_nil] using account
  | cons head tail => simp only [List.isEmpty_cons] at finished; cases finished

#print axioms readAt_account
#print axioms readOutput_account

#print axioms readArguments_account_of
#print axioms readElements_account_of


/-- Local value typing is indexed by the role and complete bound context
stored at the actual original visit. It supplies no output zipper. -/
def LocallyTyped (language : LanguageDef) (free : FreeTypeContext)
    (origins : List TypedOrigin) : Prop :=
  ∀ origin ∈ origins, ∀ expected, origin.expected = some expected →
    HasType language free origin.bound origin.source.value expected

private theorem locallyTyped_suffix {language : LanguageDef} {free : FreeTypeContext}
    {first suffix origins : List TypedOrigin}
    (account : first ++ suffix = origins) (typed : LocallyTyped language free origins) :
    LocallyTyped language free suffix := by
  intro origin member expected role
  exact typed origin (account ▸ List.mem_append_right first member) expected role

private theorem readAt_header (language : LanguageDef) (bound : List TypeExpr) (expected : TypeExpr)
    (target : Pattern) {origins : List TypedOrigin} {entries : List OutputOrigin} {suffix : List TypedOrigin}
    (accepted : readAt language bound expected target origins = some (entries,suffix)) :
    ∃ origin remaining, origins = origin :: remaining ∧
      origin.bound = bound ∧ origin.expected = some expected ∧ origin.source.value = target := by
  cases origins with
  | nil => simp only [readAt] at accepted; cases accepted
  | cons origin remaining =>
      simp only [readAt] at accepted
      split at accepted
      · rename_i header
        have parsed : origin.bound = bound ∧ origin.expected = some expected ∧ origin.source.value = target := by
          simpa only [Bool.and_eq_true,beq_iff_eq,and_assoc] using header
        exact ⟨origin,remaining,rfl,parsed⟩
      · cases accepted

/-- A successfully read subtree uses precisely the next record's local
context and role. No uniqueness of typing derivations is assumed. -/
theorem readAt_target_typed (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (target : Pattern)
    {origins : List TypedOrigin} {entries : List OutputOrigin} {suffix : List TypedOrigin}
    (typed : LocallyTyped language free origins)
    (accepted : readAt language bound expected target origins = some (entries,suffix)) :
    HasType language free bound target expected := by
  obtain ⟨origin,remaining,rfl,boundRead,roleRead,valueRead⟩ := readAt_header language bound expected target accepted
  have localTyping := typed origin (.head _) expected roleRead
  rw [boundRead,valueRead] at localTyping
  exact localTyping

private theorem readArguments_target_typed
    (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr)
    (declaration : Nat) (label : String) (allArguments : List Pattern) (arguments : List Pattern) :
    ∀ (parameterRows : List TermParam) (start : Nat) (origins : List TypedOrigin)
      (entries : List OutputOrigin) (suffix : List TypedOrigin),
      LocallyTyped language free origins →
      readArguments language bound declaration label allArguments start arguments parameterRows origins = some (entries,suffix) →
      ArgumentsHaveTypes language free bound arguments parameterRows := by
  induction arguments with
  | nil =>
      intro parameterRows start origins entries suffix typed accepted
      cases parameterRows with
      | nil => exact .nil
      | cons parameter parameterRows => simp only [readArguments] at accepted; cases accepted
  | cons argument arguments recurse =>
      intro parameterRows start origins entries suffix typed accepted
      cases parameterRows with
      | nil => simp only [readArguments] at accepted; cases accepted
      | cons parameter parameterRows =>
          cases representationRead : matchesParameterRepresentation? parameter argument with
          | false => simp only [readArguments,representationRead] at accepted; cases accepted
          | true =>
              simp only [readArguments,representationRead,↓reduceIte] at accepted
              cases parameterRead : parameterType? parameter with
              | none => simp only [parameterRead,Option.bind_eq_bind,Option.bind_none] at accepted; cases accepted
              | some expected =>
                  simp only [parameterRead,Option.bind_eq_bind,Option.bind_some,
                    Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at accepted
                  obtain ⟨⟨first,afterFirst⟩,firstRead,⟨⟨later,last⟩,laterRead,finished⟩⟩ := accepted
                  have firstAccount := readAt_account language argument bound expected origins first afterFirst firstRead
                  exact .cons ((matchesParameterRepresentation?_eq_true_iff parameter argument).mp representationRead)
                    parameterRead (readAt_target_typed language free bound expected argument typed firstRead)
                    (recurse parameterRows (start + 1) afterFirst later last
                      (locallyTyped_suffix firstAccount typed) laterRead)

private theorem readElements_target_typed
    (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr)
    (element : TypeExpr) (frame : TypingFrame) (kind : CollType) (allElements : List Pattern) (elements : List Pattern) :
    ∀ (start : Nat) (origins : List TypedOrigin) (entries : List OutputOrigin) (suffix : List TypedOrigin),
      LocallyTyped language free origins →
      readElements language bound element frame kind allElements start elements origins = some (entries,suffix) →
      ElementsHaveType language free bound elements element := by
  induction elements with
  | nil => intro start origins entries suffix typed accepted; exact .nil bound element
  | cons item elements recurse =>
      intro start origins entries suffix typed accepted
      simp only [readElements,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at accepted
      obtain ⟨⟨first,afterFirst⟩,firstRead,⟨⟨later,last⟩,laterRead,finished⟩⟩ := accepted
      have firstAccount := readAt_account language item bound element origins first afterFirst firstRead
      exact .cons (readAt_target_typed language free bound element item typed firstRead)
        (recurse (start + 1) afterFirst later last (locallyTyped_suffix firstAccount typed) laterRead)

/-- The actual normalization trace supplies local typing for every survivor
from its independently typed original visit and the checked role reducer. -/
theorem reduceAtTagged_survivors_locallyTyped
    {laws : List Laws} {language : LanguageDef}
    (checked : checkBareHomogeneous laws language = true)
    (domains : List TypeExpr) (free : FreeTypeContext) (source : Pattern)
    {bound : List TypeExpr} {expected : TypeExpr}
    (sourceTyped : HasType language free bound source expected)
    (object : isObjectPattern source = true) :
    LocallyTyped language free
      (reduceAtTagged laws domains language free bound source expected).survivors := by
  intro origin member role roleRead
  have account := reduceAtTagged_source_account laws domains language free source bound expected
  have visited : origin ∈ (reduceAtTagged laws domains language free bound source expected).visited :=
    account.mem_iff.mpr (List.mem_append_left _ (List.mem_append_left _ member))
  obtain ⟨actual,actualRead,originalTyped,valueRead,_⟩ :=
    reduceAtTagged_visits_typedAt laws domains language free source sourceTyped object origin visited
  have actualEq : actual = role := Option.some.inj (actualRead.symm.trans roleRead)
  subst actual
  have normalized := reduceAt_hasType checked domains origin.source.original originalTyped.focus_typed
  rw [← valueRead] at normalized
  exact normalized

/-- The finite completed readout carries the complete original survivor
account, and the removed units/carriers remain separate administrations. -/
theorem readOutput_original_account
    (laws : List Laws) (domains : List TypeExpr) (language : LanguageDef)
    (free : FreeTypeContext) (source : Pattern) (bound : List TypeExpr) (expected : TypeExpr)
    (entries : List OutputOrigin)
    (accepted : readOutput language bound expected
      (reduceAtTagged laws domains language free bound source expected) = some entries) :
    let trace := reduceAtTagged laws domains language free bound source expected
    trace.visited.Perm
      (entries.map OutputOrigin.origin ++ trace.unitRemovals.map AlgebraAdministration.origin ++
        trace.carrierRemovals.map AlgebraAdministration.origin) ∧
    ((entries.map OutputOrigin.origin ++ trace.unitRemovals.map AlgebraAdministration.origin ++
      trace.carrierRemovals.map AlgebraAdministration.origin).map
        (fun origin => origin.source.address)).Nodup ∧
    (∀ entry ∈ entries, TypedOrigin.Rooted source entry.origin) := by
  dsimp only
  have readAccount := readOutput_account language bound expected _ entries accepted
  obtain ⟨partition,distinct,rooted⟩ := reduceAtTagged_original_partition laws domains language free source bound expected
  refine ⟨?_,?_,?_⟩
  · simpa only [TaggedReduction.partition,← readAccount] using partition
  · simpa only [TaggedReduction.partition,← readAccount] using distinct
  · intro entry member
    apply rooted entry.origin
    apply List.mem_append_left
    apply List.mem_append_left
    rw [← readAccount]
    exact List.mem_map.mpr ⟨entry,member,rfl⟩

#print axioms readAt_header
#print axioms readAt_target_typed
#print axioms readArguments_target_typed
#print axioms readElements_target_typed
#print axioms reduceAtTagged_survivors_locallyTyped
#print axioms readOutput_original_account


open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

/-- Local readback metadata relates the output focus to its unchanged
original visit. It does not identify the two structural addresses. -/
def HeaderMatches (entry : OutputOrigin) : Prop :=
  entry.site.focus = entry.origin.source.value ∧
  entry.site.focusBound = entry.origin.bound ∧
  entry.origin.expected = some entry.site.focusType

/-- Output support uses the existing independently licensed typed-site
judgment, including its declaration positions and complete binder context. -/
def Supported (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr)
    (expected : TypeExpr) (target : Pattern) (entry : OutputOrigin) : Prop :=
  Licensed language free OperationalPermissions.all bound expected target entry.site ∧ HeaderMatches entry

private theorem suffix_head {α : Type} {all : List α} {start : Nat} {head : α} {tail : List α}
    (remaining : all.drop start = head :: tail) : all[start]? = some head := by
  have atZero := congrArg (fun items => items[0]?) remaining
  simpa only [List.getElem?_drop,Nat.add_zero,List.getElem?_cons_zero] using atZero

private theorem suffix_tail {α : Type} {all : List α} {start : Nat} {head : α} {tail : List α}
    (remaining : all.drop start = head :: tail) : all.drop (start + 1) = tail := by
  have afterHead := congrArg (List.drop 1) remaining
  simpa only [List.drop_drop,List.drop_succ_cons,List.drop_zero] using afterHead

private theorem readArguments_supported_of
    (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr)
    (declaration : Nat) (label : String) (allArguments : List Pattern) (allParameters : List TermParam)
    (parentType : TypeExpr) (parent : Pattern)
    (objects : isObjectPatternList allArguments = true)
    (outer : ∀ index argument parameter expected inner,
      allArguments[index]? = some argument → allParameters[index]? = some parameter →
      parameterType? parameter = some expected →
      Licensed language free OperationalPermissions.all bound expected argument inner →
      Licensed language free OperationalPermissions.all bound parentType parent
        (inner.wrapApplication declaration label allArguments index))
    (arguments : List Pattern) :
    ∀ (parameterRows : List TermParam) (start : Nat) (origins : List TypedOrigin)
      (entries : List OutputOrigin) (suffix : List TypedOrigin),
      allArguments.drop start = arguments → allParameters.drop start = parameterRows →
      (∀ argument ∈ arguments, ∀ expected origins entries suffix,
        isObjectPattern argument = true → LocallyTyped language free origins →
        readAt language bound expected argument origins = some (entries,suffix) →
        ∀ entry ∈ entries, Supported language free bound expected argument entry) →
      LocallyTyped language free origins →
      readArguments language bound declaration label allArguments start arguments parameterRows origins = some (entries,suffix) →
      ∀ entry ∈ entries, Supported language free bound parentType parent entry := by
  induction arguments with
  | nil =>
      intro parameterRows start origins entries suffix argumentSuffix parameterSuffix each typed accepted entry member
      cases parameterRows with
      | nil =>
          simp only [readArguments,Option.some.injEq] at accepted
          have empty := congrArg Prod.fst accepted
          change [] = entries at empty
          rw [← empty] at member
          cases member
      | cons parameter parameterRows => simp only [readArguments] at accepted; cases accepted
  | cons argument arguments recurse =>
      intro parameterRows start origins entries suffix argumentSuffix parameterSuffix each typed accepted entry member
      cases parameterRows with
      | nil => simp only [readArguments] at accepted; cases accepted
      | cons parameter parameterRows =>
          cases representationRead : matchesParameterRepresentation? parameter argument with
          | false => simp only [readArguments,representationRead] at accepted; cases accepted
          | true =>
              simp only [readArguments,representationRead,↓reduceIte] at accepted
              cases parameterRead : parameterType? parameter with
              | none => simp only [parameterRead,Option.bind_eq_bind,Option.bind_none] at accepted; cases accepted
              | some expected =>
                  simp only [parameterRead,Option.bind_eq_bind,Option.bind_some,
                    Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at accepted
                  obtain ⟨⟨first,afterFirst⟩,firstRead,⟨⟨later,last⟩,laterRead,finished⟩⟩ := accepted
                  have entriesEq := congrArg Prod.fst finished
                  change first.map (fun entry => {entry with site := entry.site.wrapApplication declaration label allArguments start}) ++ later = entries at entriesEq
                  rw [← entriesEq] at member
                  rcases List.mem_append.mp member with inFirst | inLater
                  · obtain ⟨child,childMember,rfl⟩ := List.mem_map.mp inFirst
                    have atArgument := suffix_head argumentSuffix
                    have atParameter := suffix_head parameterSuffix
                    have childObject : isObjectPattern argument = true := by
                      have all := objects
                      simp only [CanonicalBags.isObjectPatternList_eq_all,List.all_eq_true] at all
                      exact all argument (List.mem_of_getElem? atArgument)
                    obtain ⟨licensed,metadata⟩ := each argument (.head _) expected origins first afterFirst childObject typed firstRead child childMember
                    exact ⟨outer start argument parameter expected child.site atArgument atParameter parameterRead licensed,metadata⟩
                  · have firstAccount := readAt_account language argument bound expected origins first afterFirst firstRead
                    exact recurse parameterRows (start + 1) afterFirst later last
                      (suffix_tail argumentSuffix) (suffix_tail parameterSuffix)
                      (fun item itemMember => each item (.tail _ itemMember))
                      (locallyTyped_suffix firstAccount typed) laterRead entry inLater

private theorem readElements_supported_of
    (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr)
    (element : TypeExpr) (frame : TypingFrame) (kind : CollType) (allElements : List Pattern)
    (parentType : TypeExpr) (parent : Pattern)
    (objects : isObjectPatternList allElements = true)
    (outer : ∀ index item inner, allElements[index]? = some item →
      Licensed language free OperationalPermissions.all bound element item inner →
      Licensed language free OperationalPermissions.all bound parentType parent
        (inner.wrapCollection frame kind allElements index))
    (elements : List Pattern) :
    ∀ (start : Nat) (origins : List TypedOrigin) (entries : List OutputOrigin) (suffix : List TypedOrigin),
      allElements.drop start = elements →
      (∀ item ∈ elements, ∀ origins entries suffix,
        isObjectPattern item = true → LocallyTyped language free origins →
        readAt language bound element item origins = some (entries,suffix) →
        ∀ entry ∈ entries, Supported language free bound element item entry) →
      LocallyTyped language free origins →
      readElements language bound element frame kind allElements start elements origins = some (entries,suffix) →
      ∀ entry ∈ entries, Supported language free bound parentType parent entry := by
  induction elements with
  | nil =>
      intro start origins entries suffix elementSuffix each typed accepted entry member
      simp only [readElements,Option.some.injEq] at accepted
      have empty := congrArg Prod.fst accepted
      change [] = entries at empty
      rw [← empty] at member
      cases member
  | cons item elements recurse =>
      intro start origins entries suffix elementSuffix each typed accepted entry member
      simp only [readElements,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at accepted
      obtain ⟨⟨first,afterFirst⟩,firstRead,⟨⟨later,last⟩,laterRead,finished⟩⟩ := accepted
      have entriesEq := congrArg Prod.fst finished
      change first.map (fun entry => {entry with site := entry.site.wrapCollection frame kind allElements start}) ++ later = entries at entriesEq
      rw [← entriesEq] at member
      rcases List.mem_append.mp member with inFirst | inLater
      · obtain ⟨child,childMember,rfl⟩ := List.mem_map.mp inFirst
        have atItem := suffix_head elementSuffix
        have childObject : isObjectPattern item = true := by
          have all := objects
          simp only [CanonicalBags.isObjectPatternList_eq_all,List.all_eq_true] at all
          exact all item (List.mem_of_getElem? atItem)
        obtain ⟨licensed,metadata⟩ := each item (.head _) origins first afterFirst childObject typed firstRead child childMember
        exact ⟨outer start item child.site atItem licensed,metadata⟩
      · have firstAccount := readAt_account language item bound element origins first afterFirst firstRead
        exact recurse (start + 1) afterFirst later last (suffix_tail elementSuffix)
          (fun value valueMember => each value (.tail _ valueMember))
          (locallyTyped_suffix firstAccount typed) laterRead entry inLater

private theorem after_root_supported
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}
    {expected : TypeExpr} {target : Pattern} {root : OutputOrigin}
    {children entries : List OutputOrigin} {last suffix : List TypedOrigin}
    (returned : (root :: children,last) = (entries,suffix))
    (rootSupported : Supported language free bound expected target root)
    (childrenSupported : ∀ entry ∈ children, Supported language free bound expected target entry) :
    ∀ entry ∈ entries, Supported language free bound expected target entry := by
  have entriesEq := congrArg Prod.fst returned
  intro entry member
  change root :: children = entries at entriesEq
  rw [← entriesEq] at member
  rcases List.mem_cons.mp member with rfl | inChildren
  · exact rootSupported
  · exact childrenSupported entry inChildren

#print axioms readArguments_supported_of
#print axioms readElements_supported_of
#print axioms after_root_supported


private theorem readAt_head_supported
    (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr) (expected : TypeExpr)
    (target : Pattern) (origin : TypedOrigin) (remaining : List TypedOrigin)
    {entries : List OutputOrigin} {suffix : List TypedOrigin}
    (object : isObjectPattern target = true)
    (typed : LocallyTyped language free (origin :: remaining))
    (accepted : readAt language bound expected target (origin :: remaining) = some (entries,suffix)) :
    Supported language free bound expected target ⟨origin,SiteData.here bound expected target⟩ := by
  obtain ⟨head,tail,heads,boundRead,roleRead,valueRead⟩ := readAt_header language bound expected target accepted
  have headEq := (List.cons.inj heads).1
  subst head
  exact ⟨.here rfl object (readAt_target_typed language free bound expected target typed accepted),
    valueRead.symm,boundRead.symm,roleRead⟩

/-- The finite reader constructs existing licensed output sites from exact
recorded roles. Its declaration checks and representation checks are used
in the proof; no arbitrary typing derivation is identified with a stored row. -/
theorem readAt_supported (language : LanguageDef) (free : FreeTypeContext) (target : Pattern) :
    ∀ (bound : List TypeExpr) (expected : TypeExpr) (origins : List TypedOrigin)
      (entries : List OutputOrigin) (suffix : List TypedOrigin),
      isObjectPattern target = true → LocallyTyped language free origins →
      readAt language bound expected target origins = some (entries,suffix) →
      ∀ entry ∈ entries, Supported language free bound expected target entry := by
  induction target using Pattern.inductionOn with
  | hbvar index =>
      intro bound expected origins entries suffix object typed accepted
      cases origins with
      | nil => simp only [readAt] at accepted; cases accepted
      | cons origin remaining =>
          have rootSupported := readAt_head_supported language free bound expected (.bvar index) origin remaining object typed accepted
          simp only [readAt] at accepted
          split at accepted
          · simp only [Option.some.injEq] at accepted
            exact after_root_supported accepted rootSupported (by intro entry member; cases member)
          · cases accepted
  | hfvar identifier =>
      intro bound expected origins entries suffix object typed accepted
      cases origins with
      | nil => simp only [readAt] at accepted; cases accepted
      | cons origin remaining =>
          have rootSupported := readAt_head_supported language free bound expected (.fvar identifier) origin remaining object typed accepted
          simp only [readAt] at accepted
          split at accepted
          · simp only [Option.some.injEq] at accepted
            exact after_root_supported accepted rootSupported (by intro entry member; cases member)
          · cases accepted
  | happly label arguments recurse =>
      intro bound expected origins entries suffix object typed accepted
      cases origins with
      | nil => simp only [readAt] at accepted; cases accepted
      | cons origin remaining =>
          have rootSupported := readAt_head_supported language free bound expected (.apply label arguments) origin remaining object typed accepted
          have remainingTyped := locallyTyped_suffix (first := [origin]) rfl typed
          simp only [isObjectPattern] at object
          simp only [readAt] at accepted
          split at accepted
          · cases declarationRead : origin.declaration with
            | none => simp only [declarationRead] at accepted; cases accepted
            | some pair =>
                obtain ⟨declaration,rule⟩ := pair
                simp only [declarationRead] at accepted
                split at accepted
                · rename_i rowChecked
                  simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at rowChecked
                  obtain ⟨⟨⟨declared,labelEq⟩,expectedEq⟩,notBare⟩ := rowChecked
                  have ordinary : ¬ UsesBareCollection rule := by
                    intro bare
                    have yes := (usesBareCollection?_eq_true_iff rule).mpr bare
                    rw [notBare] at yes
                    cases yes
                  subst label
                  subst expected
                  simp only [Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at accepted
                  obtain ⟨⟨children,last⟩,childRead,finished⟩ := accepted
                  have argumentsTyped := readArguments_target_typed language free bound declaration rule.label
                    arguments arguments rule.params 0 remaining children last remainingTyped childRead
                  have childrenSupported := readArguments_supported_of language free bound declaration rule.label
                    arguments rule.params (.base rule.category) (.apply rule.label arguments) object
                    (fun index argument parameter parameterType inner selected selectedParameter parameterRead licensed =>
                      .application (List.mk_mem_zipIdx_iff_getElem?.mpr declared) ordinary argumentsTyped object
                        selected selectedParameter parameterRead (.inl rfl) licensed)
                    arguments rule.params 0 remaining children last rfl rfl
                    (fun argument member expected origins entries suffix object typed read =>
                      recurse argument member bound expected origins entries suffix object typed read)
                    remainingTyped childRead
                  exact after_root_supported finished rootSupported childrenSupported
                · cases accepted
          · cases accepted
  | hlambda display body recurse =>
      intro bound expected origins entries suffix object typed accepted
      cases origins with
      | nil => simp only [readAt] at accepted; cases accepted
      | cons origin remaining =>
          have rootSupported := readAt_head_supported language free bound expected (.lambda display body) origin remaining object typed accepted
          have remainingTyped := locallyTyped_suffix (first := [origin]) rfl typed
          simp only [isObjectPattern] at object
          simp only [readAt] at accepted
          split at accepted
          · cases expected with
            | arrow domain codomain =>
                simp only [Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at accepted
                obtain ⟨⟨children,last⟩,childRead,finished⟩ := accepted
                apply after_root_supported finished rootSupported
                intro entry member
                obtain ⟨child,childMember,rfl⟩ := List.mem_map.mp member
                obtain ⟨licensed,metadata⟩ := recurse (domain :: bound) codomain remaining children last object remainingTyped childRead child childMember
                exact ⟨.lambda rfl licensed,metadata⟩
            | base category => cases accepted
            | collection kind element => cases accepted
            | multiBinder domain => cases accepted
          · cases accepted
  | hmultiLambda arity displays body recurse =>
      intro bound expected origins entries suffix object typed accepted
      cases origins with
      | nil => simp only [readAt] at accepted; cases accepted
      | cons origin remaining =>
          have rootSupported := readAt_head_supported language free bound expected (.multiLambda arity displays body) origin remaining object typed accepted
          have remainingTyped := locallyTyped_suffix (first := [origin]) rfl typed
          simp only [isObjectPattern] at object
          simp only [readAt] at accepted
          split at accepted
          · cases expected with
            | arrow domain codomain =>
                cases domain with
                | multiBinder domain =>
                    simp only [Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at accepted
                    obtain ⟨⟨children,last⟩,childRead,finished⟩ := accepted
                    apply after_root_supported finished rootSupported
                    intro entry member
                    obtain ⟨child,childMember,rfl⟩ := List.mem_map.mp member
                    obtain ⟨licensed,metadata⟩ := recurse (List.replicate arity domain ++ bound) codomain remaining children last object remainingTyped childRead child childMember
                    exact ⟨.multiLambda rfl licensed,metadata⟩
                | base category => cases accepted
                | collection kind element => cases accepted
                | arrow first second => cases accepted
            | base category => cases accepted
            | collection kind element => cases accepted
            | multiBinder domain => cases accepted
          · cases accepted
  | hsubst body replacement bodyIH replacementIH =>
      intro bound expected origins entries suffix object typed accepted
      simp only [isObjectPattern,Bool.false_eq_true] at object
  | hcollection kind elements rest recurse =>
      intro bound expected origins entries suffix object typed accepted
      have shape := object
      simp only [isObjectPattern,Bool.and_eq_true] at shape
      have noTail := Option.isNone_iff_eq_none.mp shape.1
      subst rest
      cases origins with
      | nil => simp only [readAt] at accepted; cases accepted
      | cons origin remaining =>
          have rootSupported := readAt_head_supported language free bound expected (.collection kind elements none) origin remaining object typed accepted
          have remainingTyped := locallyTyped_suffix (first := [origin]) rfl typed
          simp only [readAt] at accepted
          split at accepted
          · simp only [Option.isNone_none,↓reduceIte] at accepted
            cases expected with
            | collection actual element =>
                cases same : (actual == kind) with
                | false => simp only [same] at accepted; cases accepted
                | true =>
                    have sameKind : actual = kind := (beq_iff_eq.mp same)
                    subst actual
                    simp only [same,↓reduceIte,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at accepted
                    obtain ⟨⟨children,last⟩,childRead,finished⟩ := accepted
                    have elementsTyped := readElements_target_typed language free bound element (.directCollection kind)
                      kind elements elements 0 remaining children last remainingTyped childRead
                    have childrenSupported := readElements_supported_of language free bound element (.directCollection kind)
                      kind elements (.collection kind element) (.collection kind elements none) shape.2
                      (fun index item inner selected licensed => .directCollection
                        (by cases kind <;> simp [OperationalPermissions.all]) elementsTyped shape.2 selected licensed)
                      elements 0 remaining children last rfl
                      (fun item member origins entries suffix object typed read =>
                        recurse item member bound element origins entries suffix object typed read)
                      remainingTyped childRead
                    exact after_root_supported finished rootSupported childrenSupported
            | base category =>
                cases declarationRead : origin.declaration with
                | none => simp only [declarationRead] at accepted; cases accepted
                | some pair =>
                    obtain ⟨declaration,rule⟩ := pair
                    simp only [declarationRead] at accepted
                    split at accepted
                    · rename_i rowChecked
                      have declared : language.terms[declaration]? = some rule := beq_iff_eq.mp rowChecked
                      cases elementRead : bareCollectionElementType? rule kind (.base category) with
                      | none => simp only [elementRead] at accepted; cases accepted
                      | some element =>
                          obtain ⟨expectedEq,parameter,parametersEq⟩ :=
                            (bareCollectionElementType?_eq_some_iff rule kind (.base category) element).mp elementRead
                          have categoryEq : category = rule.category := TypeExpr.base.inj expectedEq
                          subst category
                          simp only [elementRead,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at accepted
                          obtain ⟨⟨children,last⟩,childRead,finished⟩ := accepted
                          have elementsTyped := readElements_target_typed language free bound element (.authoredCollection declaration)
                            kind elements elements 0 remaining children last remainingTyped childRead
                          have childrenSupported := readElements_supported_of language free bound element (.authoredCollection declaration)
                            kind elements (.base rule.category) (.collection kind elements none) shape.2
                            (fun index item inner selected licensed => .authoredCollection
                              (List.mk_mem_zipIdx_iff_getElem?.mpr declared) parametersEq
                              (by cases kind <;> simp [OperationalPermissions.all]) elementsTyped shape.2 selected licensed)
                            elements 0 remaining children last rfl
                            (fun item member origins entries suffix object typed read =>
                              recurse item member bound element origins entries suffix object typed read)
                            remainingTyped childRead
                          exact after_root_supported finished rootSupported childrenSupported
                    · cases accepted
            | arrow domain codomain =>
                cases declarationRead : origin.declaration with
                | none => simp only [declarationRead] at accepted; cases accepted
                | some pair =>
                    obtain ⟨declaration,rule⟩ := pair
                    simp only [declarationRead] at accepted
                    split at accepted
                    · have impossible : bareCollectionElementType? rule kind (.arrow domain codomain) = none := by
                        cases actual : bareCollectionElementType? rule kind (.arrow domain codomain) with
                        | none => rfl
                        | some element =>
                            have wrong := (bareCollectionElementType?_eq_some_iff rule kind (.arrow domain codomain) element).mp actual
                            cases wrong.1
                      simp only [impossible] at accepted
                      cases accepted
                    · cases accepted
            | multiBinder domain =>
                cases declarationRead : origin.declaration with
                | none => simp only [declarationRead] at accepted; cases accepted
                | some pair =>
                    obtain ⟨declaration,rule⟩ := pair
                    simp only [declarationRead] at accepted
                    split at accepted
                    · have impossible : bareCollectionElementType? rule kind (.multiBinder domain) = none := by
                        cases actual : bareCollectionElementType? rule kind (.multiBinder domain) with
                        | none => rfl
                        | some element =>
                            have wrong := (bareCollectionElementType?_eq_some_iff rule kind (.multiBinder domain) element).mp actual
                            cases wrong.1
                      simp only [impossible] at accepted
                      cases accepted
                    · cases accepted
          · cases accepted

#print axioms readAt_head_supported
#print axioms readAt_supported


/-- Successful complete readout yields actual licensed output occurrences,
not just endpoint typings. Structural permission remains independently
selectable by a caller after this all-context readout. -/
theorem readOutput_supported (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (trace : TaggedReduction)
    (entries : List OutputOrigin) (object : isObjectPattern trace.target = true)
    (typed : LocallyTyped language free trace.survivors)
    (accepted : readOutput language bound expected trace = some entries) :
    ∀ entry ∈ entries, Supported language free bound expected trace.target entry := by
  simp only [readOutput,Option.bind_eq_bind,Option.bind_eq_some_iff] at accepted
  obtain ⟨⟨actual,suffix⟩,read,finished⟩ := accepted
  cases suffix with
  | nil =>
      simp only [List.isEmpty_nil,↓reduceIte,Option.some.injEq] at finished
      subst entries
      exact readAt_supported language free trace.target bound expected trace.survivors actual [] object typed read
  | cons head tail => simp only [List.isEmpty_cons] at finished; cases finished

/-- The source-normalization path earns object formation and the original
visits earn local value typing. The reader then transports every returned
survivor to its actual normalized output zipper and exact typed frames. -/
theorem reduceAtTagged_readOutput_supported
    {laws : List Laws} {language : LanguageDef} {relEnv : Engine.RelationEnv}
    (checked : checkBareHomogeneous laws language = true) (authorized : SourceAlgebras laws language)
    (discipline : ReferenceStep.EquationDiscipline) (domains : List TypeExpr) (free : FreeTypeContext)
    (source : Pattern) {bound : List TypeExpr} {expected : TypeExpr}
    (good : OpenPatternWellSorted language free bound expected source)
    (entries : List OutputOrigin)
    (accepted : readOutput language bound expected
      (reduceAtTagged laws domains language free bound source expected) = some entries) :
    ∀ entry ∈ entries, Supported language free bound expected
      (reduceAtTagged laws domains language free bound source expected).target entry := by
  have path := TypedPaths.reduceAtTagged_typed_equivalent (relEnv := relEnv)
    checked authorized discipline domains free source good
  have formed := path.formed_right (TypedPaths.formed_iff_open.mpr good)
  exact readOutput_supported language free bound expected _ entries formed.object
    (reduceAtTagged_survivors_locallyTyped checked domains free source good.1 good.2.2.1) accepted

/-- Capturing a successfully read output focus keeps its recorded role and
full sorted binder prefix. This reads an actual inverse success and does
not claim that all authored equations preserve inverse-recovery success. -/
theorem reduceAtTagged_readOutput_capture
    {laws : List Laws} {language : LanguageDef} {relEnv : Engine.RelationEnv}
    (checked : checkBareHomogeneous laws language = true) (authorized : SourceAlgebras laws language)
    (discipline : ReferenceStep.EquationDiscipline) (domains : List TypeExpr) (free : FreeTypeContext)
    (source : Pattern) {bound : List TypeExpr} {expected : TypeExpr}
    (good : OpenPatternWellSorted language free bound expected source)
    (entries : List OutputOrigin)
    (accepted : readOutput language bound expected
      (reduceAtTagged laws domains language free bound source expected) = some entries)
    {entry : OutputOrigin} (member : entry ∈ entries) :
    ∃ locals, entry.site.focusBound = locals ++ bound ∧
      Admissible language free entry.site.focusBound entry.site.focusType entry.site.focus ∧
      ∀ (dependencies : List TypeExpr) (arguments : List Pattern) (indices : List Nat) (value : RuleBinding.ContextualValue),
        RuleBinding.variableSpine? locals.length arguments = some indices →
        RestAwareTyping.PartialSortedSpine dependencies locals indices →
        RuleBinding.recoverValue? dependencies bound.length locals.length arguments entry.site.focus = some value →
          value.dependencies = dependencies ∧ value.ambient = bound.length ∧
          Admissible language free (dependencies ++ bound) entry.site.focusType value.body := by
  obtain ⟨licensed,metadata⟩ := reduceAtTagged_readOutput_supported (relEnv := relEnv)
    checked authorized discipline domains free source good entries accepted entry member
  have readAccount := readOutput_account language bound expected _ entries accepted
  have survivor : entry.origin ∈ (reduceAtTagged laws domains language free bound source expected).survivors := by
    rw [← readAccount]
    exact List.mem_map.mpr ⟨entry,member,rfl⟩
  have account := reduceAtTagged_source_account laws domains language free source bound expected
  have visited : entry.origin ∈ (reduceAtTagged laws domains language free bound source expected).visited :=
    account.mem_iff.mpr (List.mem_append_left _ (List.mem_append_left _ survivor))
  obtain ⟨role,locals,roleRead,boundRead,valueGood,inverse⟩ :=
    reduceAtTagged_visit_capture_readout (relEnv := relEnv) checked authorized discipline domains free source good visited
  have sameRole : role = entry.site.focusType := Option.some.inj (roleRead.symm.trans metadata.2.2)
  subst role
  refine ⟨locals,?_,?_,?_⟩
  · exact metadata.2.1.trans boundRead
  · rw [metadata.1,metadata.2.1,boundRead]
    exact valueGood
  · intro dependencies arguments indices value spineCheck spine recovered
    exact inverse dependencies arguments indices value spineCheck spine (by simpa only [metadata.1] using recovered)

#print axioms readOutput_supported
#print axioms reduceAtTagged_readOutput_supported
#print axioms reduceAtTagged_readOutput_capture

end Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus.RoleAwareReadout.OutputSites

namespace Mettapedia.GSLT.LanguageDef.BagNormalForm.RoleAwareSourceControls

open Mettapedia.OSLF.MeTTaIL
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionLaws CanonicalBags.RoleAware DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted EquationSemantics GeneralTypedOccurrence
open WithAuthoredEquations.AlgebraFocus RoleAwareReadout OutputSites

private def mixedOutputEntries : List OutputOrigin :=
  (readOutput language [] proc actualTrace).getD []

/-- Exact original records are paired with their new output positions.
The nested data Z remains present, while the scalar unit and flattened
carrier remain separate original administrations. -/
theorem mixed_output_sites_and_account (relEnv : Engine.RelationEnv)
    (discipline : ReferenceStep.EquationDiscipline) :
    readOutput language [] proc actualTrace = some mixedOutputEntries ∧
      mixedOutputEntries.map (fun entry => entry.origin.source.address) =
        [[],[0],[0,0],[0,0,0],[0,0,1],[0,0,2],[1],[1,0,0],[1,0,1]] ∧
      mixedOutputEntries.map (fun entry => entry.site.address) =
        [[],[0],[0,0],[0,0,0],[0,0,1],[0,0,2],[1],[1,0],[1,1]] ∧
      (actualTrace).unitRemovals.map (fun event => event.origin.source.address) = [[1,1]] ∧
      (actualTrace).carrierRemovals.map (fun event => event.origin.source.address) = [[1,0]] ∧
      mixedOutputEntries[3]?.map (fun entry => entry.site.focus) = some z ∧
      ∀ entry ∈ mixedOutputEntries,
        Licensed language FreeTypeContext.empty GeneralTypedSites.OperationalPermissions.all [] proc (actualTrace).target entry.site ∧
        TypedAt language FreeTypeContext.empty entry.site.focus entry.site.context [] proc entry.site.focusBound entry.site.focusType ∧
        entry.site.context.fill entry.site.focus = (actualTrace).target ∧
        entry.site.address = GeneralTypedSites.contextAddress entry.site.context ∧ HeaderMatches entry := by
  have accepted : readOutput language [] proc actualTrace = some mixedOutputEntries := by decide +kernel
  refine ⟨accepted,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,?_⟩
  intro entry member
  obtain ⟨licensed,metadata⟩ := reduceAtTagged_readOutput_supported (relEnv := relEnv)
    homogeneous authorized discipline [] FreeTypeContext.empty tracedSource traced_open mixedOutputEntries accepted entry member
  exact ⟨licensed,licensed.typedAt,licensed.source_eq,licensed.address_eq,metadata⟩

/-- The second output A has a new structural index. Substituting that
output address into its original source record is a false source origin. -/
theorem output_address_is_not_original_address :
    ∃ entry ∈ mixedOutputEntries, entry.site.address = [1,1] ∧
      entry.origin.source.address = [1,0,1] ∧ entry.site.focus = a ∧
      ¬ TypedOrigin.Rooted tracedSource
        {entry.origin with source := {entry.origin.source with address := entry.site.address}} := by
  let entry := mixedOutputEntries[8]'(by decide +kernel)
  have member : entry ∈ mixedOutputEntries := by decide +kernel
  refine ⟨entry,member,by decide +kernel,by decide +kernel,by decide +kernel,?_⟩
  intro rooted
  have wrong := rooted.2
  change entry.site.address = GeneralTypedSites.contextAddress entry.origin.source.context at wrong
  have refused : entry.site.address ≠ GeneralTypedSites.contextAddress entry.origin.source.context := by decide +kernel
  exact refused wrong

private def scopedOutputSource : Pattern :=
  .lambda none (.multiLambda 2 [] (bag [bag [.bvar 0,.bvar 3],z]))
private def scopedOutputType : TypeExpr := .arrow proc (.arrow (.multiBinder proc) proc)
private def scopedOutputTrace : TaggedReduction :=
  reduceAtTagged (CollectionLaws.declared language) [] language FreeTypeContext.empty
    [proc] scopedOutputSource scopedOutputType
private def scopedOutputEntries : List OutputOrigin :=
  (readOutput language [proc] scopedOutputType scopedOutputTrace).getD []
private theorem scopedOutputGood :
    OpenPatternWellSorted language FreeTypeContext.empty [proc] scopedOutputType scopedOutputSource := by
  have typed : HasType language FreeTypeContext.empty [proc] scopedOutputSource scopedOutputType :=
    checkHasType_sound (by decide +kernel)
  exact ⟨typed,by decide +kernel,by decide +kernel,typed.isWellScopedAt⟩

/-- Actual output capture crosses one lambda, a two-variable binder and
an ambient variable. The nonempty increasing dependency spine is preserved. -/
theorem scoped_output_capture_readback (relEnv : Engine.RelationEnv)
    (discipline : ReferenceStep.EquationDiscipline) :
    readOutput language [proc] scopedOutputType scopedOutputTrace = some scopedOutputEntries ∧
      ∃ entry ∈ scopedOutputEntries,
        entry.site.focus = .bvar 0 ∧ entry.site.focusBound = [proc,proc,proc,proc] ∧
        RuleBinding.recoverValue? [proc,proc] 1 3 [.bvar 0,.bvar 2] entry.site.focus =
          some ⟨[proc,proc],1,.bvar 0⟩ ∧
        Admissible language FreeTypeContext.empty ([proc,proc] ++ [proc]) proc (.bvar 0) := by
  have accepted : readOutput language [proc] scopedOutputType scopedOutputTrace = some scopedOutputEntries := by decide +kernel
  let entry := scopedOutputEntries[3]'(by decide +kernel)
  have member : entry ∈ scopedOutputEntries := by decide +kernel
  have focusRead : entry.site.focus = .bvar 0 := by decide +kernel
  have boundRead : entry.site.focusBound = [proc,proc,proc,proc] := by decide +kernel
  have typeRead : entry.site.focusType = proc := by decide +kernel
  have recovered : RuleBinding.recoverValue? [proc,proc] 1 3 [.bvar 0,.bvar 2] entry.site.focus =
      some ⟨[proc,proc],1,.bvar 0⟩ := by decide +kernel
  obtain ⟨locals,prefixRead,_,readout⟩ := reduceAtTagged_readOutput_capture (relEnv := relEnv)
    homogeneous authorized discipline [] FreeTypeContext.empty scopedOutputSource scopedOutputGood scopedOutputEntries accepted member
  rw [boundRead] at prefixRead
  have prefixes : locals ++ [proc] = [proc,proc,proc] ++ [proc] := prefixRead.symm
  have localsEq := List.append_cancel_right prefixes
  subst locals
  have spine : RestAwareTyping.PartialSortedSpine [proc,proc] [proc,proc,proc] [0,2] := by
    constructor <;> decide +kernel
  have body := readout [proc,proc] [.bvar 0,.bvar 2] [0,2] ⟨[proc,proc],1,.bvar 0⟩
    (by decide +kernel) spine recovered
  rw [typeRead] at body
  exact ⟨accepted,entry,member,focusRead,boundRead,recovered,body.2.2⟩

private def rootUnitTrace : TaggedReduction :=
  reduceAtTagged (CollectionLaws.declared language) [] language FreeTypeContext.empty [] z proc
private def rootUnitEntries : List OutputOrigin :=
  (readOutput language [] proc rootUnitTrace).getD []
private def unsupportedUnitPresentation : TaggedReduction :=
  let originalRoot := rootUnitTrace.root
  let presentedRoot : TypedOrigin := {originalRoot with source := {originalRoot.source with value := bag []}}
  {rootUnitTrace with
    target := bag []
    root := presentedRoot}

/-- The declared unit has a genuine empty-carrier equation, while the
actual reducer keeps a unit at its own root. The unit constructor record
cannot be reused as the empty carrier's declaration authority. -/
theorem unit_root_presentation_requires_output_declaration (relEnv : Engine.RelationEnv) :
    rootUnitTrace.target = z ∧ readOutput language [] proc rootUnitTrace = some rootUnitEntries ∧
      rootUnitEntries.map (fun entry => entry.origin.declaration) = [some (0,zero)] ∧
      ReferenceStep.Equivalent relEnv language z (bag []) ∧
      readOutput language [] proc unsupportedUnitPresentation = none ∧
      zero ≠ carrier := by
  have emptyTyped : HasType language FreeTypeContext.empty [] (bag []) proc := checkHasType_sound (by decide +kernel)
  have declaredEmpty : DerivedInstance language (bag []) z :=
    .emptyUnit carrier_algebra rfl ⟨FreeTypeContext.empty,[],emptyTyped⟩
  have equation : ReferenceStep.Equivalent relEnv language (bag []) z :=
    .rel _ _ (.inContext .hole (.inr declaredEmpty))
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,.symm _ _ equation,
    by decide +kernel,by decide +kernel⟩

#print axioms mixed_output_sites_and_account
#print axioms output_address_is_not_original_address
#print axioms scoped_output_capture_readback
#print axioms unit_root_presentation_requires_output_declaration

end Mettapedia.GSLT.LanguageDef.BagNormalForm.RoleAwareSourceControls
