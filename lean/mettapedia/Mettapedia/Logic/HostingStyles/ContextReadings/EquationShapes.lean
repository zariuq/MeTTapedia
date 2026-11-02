import Mettapedia.Logic.HostingStyles.PrimeCandidate.ProbeData
import Mettapedia.Logic.HostingStyles.ContextReadings.Readings
import Mettapedia.GSLT.LanguageDef.BagNormalFormTyping
import Mettapedia.OSLF.MeTTaIL.PlainRuleValidation

/-!
# The equations of a presented language give the shape of its contexts

The contexts of a presented language are linear patterns: each hole occurs
once.  Whether the generated theory nevertheless *discards* or *copies*
(`ContextTheory.Discards`, `ContextTheory.Copies`) is decided by its static
equivalence, and so by its authored equations.

* **An erasing equation** `e(x, y) = x` (`ErasingEquation`), for a declared
  constructor `e` of two plain arguments of its own sort, gives a context that
  discards: the constructor applied to two holes
  (`ErasingEquation.discards`).
* **A copying equation** `d(x) = p(x, x)` (`CopyingEquation`), for declared
  constructors `d` of one and `p` of two plain arguments of one sort, gives a
  context that copies: `d` applied to a hole acts as `p` applied to two holes
  filled twice (`CopyingEquation.copies`).
* **Conversely**, a language each of whose generators of the static
  equivalence keeps a positive weight that contexts add (`KeptWeight`) has a
  linear size (`KeptWeight.linearSize`), and then it neither discards nor
  copies at an inhabited interface (`KeptWeight.not_discards`,
  `KeptWeight.not_copies`).  The weight that counts every node of a pattern
  other than the quotations and the droppings is kept by a language whose one
  equation is that of quotation and dropping (`QuoteDropOnly.keptWeight`) and
  by a language with no equation at all (`keptWeight_of_equationFree`).

So a language with an erasing or a copying equation at an inhabited sort keeps
no such weight (`ErasingEquation.isEmpty_keptWeight`,
`CopyingEquation.isEmpty_keptWeight`).

The constructors of a presented language are contexts
(`unaryContext`, `binaryContext`): a declared constructor of plain arguments
applied to its holes sorts every filling, in the presentation and in every
presentation it maps into.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.ContextReadings

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles

/-! ## Declared constructors as contexts -/

/-- **The image of a declared constructor applied to terms of its parameters
is a term**, in every presentation the presentation maps into. -/
theorem apply_wellSorted {presentation target : ValidatedLanguageDef}
    (morphism : StructuralMorphism presentation target) {rule : GrammarRule}
    (declared : rule ∈ presentation.language.terms) (plain : ¬ UsesBareCollection rule)
    {bound : List TypeExpr} {arguments : List Pattern}
    (typed : ArgumentsHaveTypes target.language FreeTypeContext.empty bound arguments
      (rule.params.map (mapTermParam morphism.symbols)))
    (canonical : ∀ argument ∈ arguments, argument.hasCanonicalBinderMetadata = true)
    (object : ∀ argument ∈ arguments, isObjectPattern argument = true) :
    OpenPatternWellSorted target.language FreeTypeContext.empty bound
      (.base (morphism.symbols.sort rule.category))
      (.apply (morphism.symbols.constructor rule.label) arguments) := by
  have applied : HasType target.language FreeTypeContext.empty bound
      (.apply (mapGrammarRule morphism.symbols rule).label arguments)
      (.base (mapGrammarRule morphism.symbols rule).category) :=
    .constructor (morphism.mapsTerms rule declared)
      (fun bare => plain ((usesBareCollection_mapGrammarRule_iff _ _).mp bare)) typed
  refine ⟨applied, ?_, ?_, ?_⟩
  · simp only [Pattern.hasCanonicalBinderMetadata]
    exact BagNormalForm.hasCanonicalBinderMetadataList_iff.mpr canonical
  · simp only [isObjectPattern]
    exact BagNormalForm.isObjectPatternList_iff.mpr object
  · exact applied.isWellScopedAt

/-- **A declared constructor of one plain argument, as a context of one
hole.** -/
def unaryContext (presentation : ValidatedLanguageDef) {rule : GrammarRule}
    {name argument result : String} (declared : rule ∈ presentation.language.terms)
    (category : rule.category = result) (params : rule.params = [.simple name (.base argument)])
    (stage : List TypeExpr) :
    Contexts.Context presentation
      (fun _ : Unit => (⟨.base argument, stage⟩ : Contexts.Interface)) ⟨.base result, stage⟩ where
  shape := .apply rule.label [.hole ()]
  linear := ⟨by simp [MultiHoleContext.holes, MultiHoleContext.holesList],
    fun _ => by simp [MultiHoleContext.holes, MultiHoleContext.holesList]⟩
  sorted := fun {target} morphism filling => by
    subst category
    have plain : ¬ UsesBareCollection rule := by
      rintro ⟨_, _, _, bare⟩
      have full := ((GrammarRule.bareParams_cons_iff _ _ _).mp bare).2
      rw [params] at full
      simp at full
    have typed : ArgumentsHaveTypes target.language FreeTypeContext.empty
        (stage.map (mapTypeExpr morphism.symbols)) [(filling ()).1]
        (rule.params.map (mapTermParam morphism.symbols)) := by
      rw [params]
      exact .cons trivial rfl (filling ()).2.1 .nil
    exact apply_wellSorted morphism declared plain typed
      (fun argument (member : argument ∈ [(filling ()).1]) => by
        obtain rfl := List.mem_singleton.mp member
        exact (filling ()).2.2.1)
      (fun argument (member : argument ∈ [(filling ()).1]) => by
        obtain rfl := List.mem_singleton.mp member
        exact (filling ()).2.2.2.1)

/-- **A declared constructor of two plain arguments, as a context of two
holes.** -/
def binaryContext (presentation : ValidatedLanguageDef) {rule : GrammarRule}
    {firstName secondName result : String} (sorts : Bool → String)
    (declared : rule ∈ presentation.language.terms) (category : rule.category = result)
    (params : rule.params =
      [.simple firstName (.base (sorts false)), .simple secondName (.base (sorts true))])
    (stage : List TypeExpr) :
    Contexts.Context presentation
      (fun index : Bool => (⟨.base (sorts index), stage⟩ : Contexts.Interface))
      ⟨.base result, stage⟩ where
  shape := .apply rule.label [.hole false, .hole true]
  linear := ⟨by simp [MultiHoleContext.holes, MultiHoleContext.holesList],
    fun index => by cases index <;> simp [MultiHoleContext.holes, MultiHoleContext.holesList]⟩
  sorted := fun {target} morphism filling => by
    subst category
    have plain : ¬ UsesBareCollection rule := by
      rintro ⟨_, _, _, bare⟩
      have full := ((GrammarRule.bareParams_cons_iff _ _ _).mp bare).2
      rw [params] at full
      simp at full
    have typed : ArgumentsHaveTypes target.language FreeTypeContext.empty
        (stage.map (mapTypeExpr morphism.symbols)) [(filling false).1, (filling true).1]
        (rule.params.map (mapTermParam morphism.symbols)) := by
      rw [params]
      exact .cons trivial rfl (filling false).2.1 (.cons trivial rfl (filling true).2.1 .nil)
    exact apply_wellSorted morphism declared plain typed
      (fun argument (member : argument ∈ [(filling false).1, (filling true).1]) => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact (filling false).2.2.1
        · exact (filling true).2.2.1)
      (fun argument (member : argument ∈ [(filling false).1, (filling true).1]) => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact (filling false).2.2.2.1
        · exact (filling true).2.2.2.1)

/-- Filling the context of a constructor of one argument applies it. -/
theorem fill_unaryContext {presentation : ValidatedLanguageDef} {rule : GrammarRule}
    {name argument result : String} (declared : rule ∈ presentation.language.terms)
    (category : rule.category = result) (params : rule.params = [.simple name (.base argument)])
    (stage : List TypeExpr)
    (filling : (index : Unit) → Contexts.Term presentation.language ⟨.base argument, stage⟩) :
    ((unaryContext presentation declared category params stage).fill filling).1 =
      .apply rule.label [(filling ()).1] :=
  rfl

/-- Filling the context of a constructor of two arguments applies it. -/
theorem fill_binaryContext {presentation : ValidatedLanguageDef} {rule : GrammarRule}
    {firstName secondName result : String} (sorts : Bool → String)
    (declared : rule ∈ presentation.language.terms) (category : rule.category = result)
    (params : rule.params =
      [.simple firstName (.base (sorts false)), .simple secondName (.base (sorts true))])
    (stage : List TypeExpr)
    (filling : (index : Bool) → Contexts.Term presentation.language ⟨.base (sorts index), stage⟩) :
    ((binaryContext presentation sorts declared category params stage).fill filling).1 =
      .apply rule.label [(filling false).1, (filling true).1] :=
  rfl

/-! ## An erasing equation gives a context that discards -/

/-- **An erasing equation** of a language at a sort: `e(x, y) = x`, authored
without premise, for a declared constructor `e` of the sort with two plain
arguments of the sort. -/
structure ErasingEquation (lang : LanguageDef) (sort : String) (rule : GrammarRule)
    (equation : Equation) : Prop where
  declared : rule ∈ lang.terms
  category : rule.category = sort
  params : ∃ first second : String,
    rule.params = [.simple first (.base sort), .simple second (.base sort)]
  authored : equation ∈ lang.equations
  premiseFree : equation.premises = []
  sides : ∃ kept erased : String, kept ≠ erased ∧
    equation.left = .apply rule.label [.fvar kept, .fvar erased] ∧ equation.right = .fvar kept

/-- One instance of an erasing equation. -/
theorem ErasingEquation.generator {lang : LanguageDef} {sort : String} {rule : GrammarRule}
    {equation : Equation} (erasing : ErasingEquation lang sort rule equation)
    (base : BasePremiseEvaluator) (first second : Pattern) :
    EquationGenerator base lang (.apply rule.label [first, second]) first := by
  obtain ⟨kept, erased, distinct, left, right⟩ := erasing.sides
  have differ : (kept == erased) = false := beq_eq_false_iff_ne.mpr distinct
  have differ' : (erased == kept) = false := beq_eq_false_iff_ne.mpr (Ne.symm distinct)
  refine .inl ⟨0, .forward (equation := equation)
    (initialBindings := [(erased, second), (kept, first)])
    (finalBindings := [(erased, second), (kept, first)]) erasing.authored
    (by simp [readsRaw, left, right, Mettapedia.OSLF.MeTTaIL.Match.binderFree, Mettapedia.OSLF.MeTTaIL.Match.binderFreeList]) ?_ ?_ ?_⟩
  · rw [left]
    simp [matchPattern, matchArgs, mergeBindings, differ]
  · rw [erasing.premiseFree]
    exact .nil _
  · rw [right]
    simp [applyBindings, differ']

/-- **An erasing equation gives a context that discards**: the constructor
applied to two holes returns what fills the first. -/
theorem ErasingEquation.discards {presentation : ValidatedLanguageDef} {sort : String}
    {rule : GrammarRule} {equation : Equation}
    (erasing : ErasingEquation presentation.language sort rule equation)
    (base : BasePremiseEvaluator) (stage : List TypeExpr) :
    (contextTheory base presentation).Discards ⟨.base sort, stage⟩ := by
  obtain ⟨first, second, params⟩ := erasing.params
  refine ⟨binaryContext presentation (fun _ => sort) erasing.declared erasing.category params stage,
    fun filling => ?_⟩
  exact Relation.EqvGen.rel _ _
    (EquationContextStep.inContext .hole
      (erasing.generator base (filling false).1 (filling true).1))

/-! ## A copying equation gives a context that copies -/

/-- **A copying equation** of a language at a sort: `d(x) = p(x, x)`, authored
without premise, for declared constructors of the sort, `d` with one and `p`
with two plain arguments of the sort. -/
structure CopyingEquation (lang : LanguageDef) (sort : String) (copy pair : GrammarRule)
    (equation : Equation) : Prop where
  copyDeclared : copy ∈ lang.terms
  pairDeclared : pair ∈ lang.terms
  copyCategory : copy.category = sort
  pairCategory : pair.category = sort
  copyParams : ∃ name : String, copy.params = [.simple name (.base sort)]
  pairParams : ∃ first second : String,
    pair.params = [.simple first (.base sort), .simple second (.base sort)]
  authored : equation ∈ lang.equations
  premiseFree : equation.premises = []
  sides : ∃ copied : String, equation.left = .apply copy.label [.fvar copied] ∧
    equation.right = .apply pair.label [.fvar copied, .fvar copied]

/-- One instance of a copying equation. -/
theorem CopyingEquation.generator {lang : LanguageDef} {sort : String} {copy pair : GrammarRule}
    {equation : Equation} (copying : CopyingEquation lang sort copy pair equation)
    (base : BasePremiseEvaluator) (pattern : Pattern) :
    EquationGenerator base lang (.apply copy.label [pattern]) (.apply pair.label [pattern, pattern]) := by
  obtain ⟨copied, left, right⟩ := copying.sides
  refine .inl ⟨0, .forward (equation := equation) (initialBindings := [(copied, pattern)])
    (finalBindings := [(copied, pattern)]) copying.authored
    (by simp [readsRaw, left, right, Mettapedia.OSLF.MeTTaIL.Match.binderFree, Mettapedia.OSLF.MeTTaIL.Match.binderFreeList]) ?_ ?_ ?_⟩
  · rw [left]
    simp [matchPattern, matchArgs, mergeBindings]
  · rw [copying.premiseFree]
    exact .nil _
  · rw [right]
    simp [applyBindings]

/-- **A copying equation gives a context that copies**: `d` applied to a hole
acts as `p` applied to two holes filled twice. -/
theorem CopyingEquation.copies {presentation : ValidatedLanguageDef} {sort : String}
    {copy pair : GrammarRule} {equation : Equation}
    (copying : CopyingEquation presentation.language sort copy pair equation)
    (base : BasePremiseEvaluator) (stage : List TypeExpr) :
    (contextTheory base presentation).Copies ⟨.base sort, stage⟩ := by
  obtain ⟨name, copyParams⟩ := copying.copyParams
  obtain ⟨first, second, pairParams⟩ := copying.pairParams
  refine ⟨binaryContext presentation (fun _ => sort) copying.pairDeclared copying.pairCategory
      pairParams stage,
    unaryContext presentation copying.copyDeclared copying.copyCategory copyParams stage,
    fun term => ?_⟩
  exact Relation.EqvGen.rel _ _
    (EquationContextStep.inContext .hole (copying.generator base term.1))

/-! ## Conversely: a weight that every generator keeps -/

/-- **A weight that the static equivalence of a language keeps**: a positive
number on patterns that a pattern with holes adds over what fills its holes,
each as often as its hole occurs, and that every generator of the static
equivalence keeps. -/
structure KeptWeight (base : BasePremiseEvaluator) (lang : LanguageDef) where
  /-- The weight of a pattern. -/
  weight : Pattern → Nat
  /-- The weight of a pattern with holes, its holes not counted. -/
  contextWeight : {ι : Type} → MultiHoleContext ι → Nat
  positive : ∀ pattern : Pattern, 0 < weight pattern
  additive : ∀ {ι : Type} (filling : ι → Pattern) (context : MultiHoleContext ι),
    weight (context.fill filling) =
      contextWeight context + (context.holes.map fun index => weight (filling index)).sum
  generator : ∀ {source target : Pattern}, EquationGenerator base lang source target →
    weight source = weight target

namespace KeptWeight

variable {base : BasePremiseEvaluator} {lang : LanguageDef}

/-- A context of one hole adds the weight of what fills it. -/
theorem fill_oneHole (kept : KeptWeight base lang) (context : OneHoleContext) (pattern : Pattern) :
    kept.weight (context.fill pattern) =
      kept.contextWeight (MultiHoleContext.ofOneHole context) + kept.weight pattern := by
  have filled := kept.additive (fun _ : Unit => pattern) (MultiHoleContext.ofOneHole context)
  rw [MultiHoleContext.fill_ofOneHole, MultiHoleContext.holes_ofOneHole] at filled
  simpa using filled

/-- **Equivalent patterns have the same weight.** -/
theorem equiv (kept : KeptWeight base lang) {left right : Pattern}
    (equivalent : EquationEquiv base lang left right) : kept.weight left = kept.weight right := by
  induction equivalent with
  | rel _ _ step =>
      cases step with
      | inContext context generator =>
          rw [kept.fill_oneHole, kept.fill_oneHole, kept.generator generator]
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **The contexts of a presentation whose static equivalence keeps a weight
have a linear size.** -/
def linearSize {presentation : ValidatedLanguageDef}
    (kept : KeptWeight base presentation.language) :
    (contextTheory base presentation).LinearSize where
  size := fun term => kept.weight term.1
  positive := fun term => kept.positive term.1
  respects := fun related => kept.equiv (equationEquiv_of_termSetoid related)
  additive := fun {arity} _ _ _ context => by
    classical
    refine ⟨kept.contextWeight context.shape, fun filling => ?_⟩
    show kept.weight (context.shape.fill fun index => (filling index).1) = _
    rw [kept.additive, ← List.sum_toFinset _ context.linear.1]
    congr 2
    exact Finset.eq_univ_iff_forall.mpr fun index => List.mem_toFinset.mpr (context.linear.2 index)

/-- **Such a presentation discards at no inhabited interface.** -/
theorem not_discards {presentation : ValidatedLanguageDef}
    (kept : KeptWeight base presentation.language) {interface : Contexts.Interface}
    (term : Contexts.Term presentation.language interface) :
    ¬ (contextTheory base presentation).Discards interface :=
  kept.linearSize.not_discards term

/-- **Nor does it copy.** -/
theorem not_copies {presentation : ValidatedLanguageDef}
    (kept : KeptWeight base presentation.language) {interface : Contexts.Interface}
    (term : Contexts.Term presentation.language interface) :
    ¬ (contextTheory base presentation).Copies interface :=
  kept.linearSize.not_copies term

end KeptWeight

/-- **Positive**: a language whose one equation is that of quotation and
dropping keeps the weight that does not count those two. -/
def _root_.Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles.QuoteDropOnly.keptWeight
    {lang : LanguageDef} (only : QuoteDropOnly lang) (base : BasePremiseEvaluator) :
    KeptWeight base lang where
  weight := weight
  contextWeight := contextWeight
  positive := weight_pos
  additive := weight_fill
  generator := fun generator => by
    rcases only.generator generator with rfl | rfl
    · exact weight_quoted_dropped _
    · exact (weight_quoted_dropped _).symm

/-- **Positive**: a language with no equation, no bag, no set and no
collection algebra keeps that weight too: its static equivalence has no
generator. -/
def keptWeight_of_equationFree {lang : LanguageDef} (free : lang.isEquationFree = true)
    (base : BasePremiseEvaluator) : KeptWeight base lang where
  weight := weight
  contextWeight := contextWeight
  positive := weight_pos
  additive := weight_fill
  generator := fun generator => by
    rcases generator with authored | derived
    · exact (no_equationInstance_of_equations_eq_nil (equations_eq_nil_of_isEquationFree free)
        _ _ authored).elim
    · exact (no_derivedInstance_of_isEquationFree free _ _ derived).elim

/-- **Negative**: a language with an erasing equation at an inhabited sort
keeps no weight. -/
theorem ErasingEquation.isEmpty_keptWeight {presentation : ValidatedLanguageDef} {sort : String}
    {rule : GrammarRule} {equation : Equation}
    (erasing : ErasingEquation presentation.language sort rule equation)
    (base : BasePremiseEvaluator) {stage : List TypeExpr}
    (term : Contexts.Term presentation.language ⟨.base sort, stage⟩) :
    IsEmpty (KeptWeight base presentation.language) :=
  ⟨fun kept => kept.not_discards term (erasing.discards base stage)⟩

/-- **Negative**: nor does a language with a copying equation at an inhabited
sort. -/
theorem CopyingEquation.isEmpty_keptWeight {presentation : ValidatedLanguageDef} {sort : String}
    {copy pair : GrammarRule} {equation : Equation}
    (copying : CopyingEquation presentation.language sort copy pair equation)
    (base : BasePremiseEvaluator) {stage : List TypeExpr}
    (term : Contexts.Term presentation.language ⟨.base sort, stage⟩) :
    IsEmpty (KeptWeight base presentation.language) :=
  ⟨fun kept => kept.not_copies term (copying.copies base stage)⟩

/-! ## Two small languages -/

/-- A datum with no part. -/
def pointRule : GrammarRule :=
  { label := "point", category := "Datum", params := [], syntaxPattern := [] }

/-- The constructor that an erasing equation is about. -/
def firstRule : GrammarRule :=
  { label := "first", category := "Datum"
    params := [.simple "kept" (.base "Datum"), .simple "erased" (.base "Datum")]
    syntaxPattern := [] }

/-- `first(kept, erased) = kept`. -/
def firstEquation : Equation :=
  { name := "first-of-two"
    typeContext := [("kept", .base "Datum"), ("erased", .base "Datum")]
    premises := []
    left := .apply "first" [.fvar "kept", .fvar "erased"]
    right := .fvar "kept" }

/-- **A language with an erasing equation**: one sort, a point, and a
constructor of two arguments equal to its first. -/
def erasingLanguage : LanguageDef :=
  { name := "erasing"
    types := [TypeDecl.plain "Datum"]
    terms := [pointRule, firstRule]
    equations := [firstEquation]
    rewrites := [] }

/-- The language with an erasing equation passes the declaration gate. -/
theorem erasingLanguage_validate : erasingLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorEquationsAndRewrites
  case htypes => decide +kernel
  case hconstructors => decide +kernel
  case hequations => decide +kernel
  case hrewrites => decide +kernel
  case hcategory => decide +kernel
  case hparams => decide +kernel
  case hsyntax => decide +kernel
  case hequationValid =>
    intro equation member
    exact LanguageDef.validateEquation_eq_nil_of_plainEquationOk
      (List.all_eq_true.mp
        (by decide +kernel :
          erasingLanguage.equations.all (LanguageDef.plainEquationOk erasingLanguage) = true)
        equation member)
  case hrewriteValid =>
    intro rewrite member
    exact (List.not_mem_nil member).elim

/-- The language with an erasing equation, as a presentation. -/
def erasingPresentation : ValidatedLanguageDef := ⟨erasingLanguage, erasingLanguage_validate⟩

/-- **Positive**, for `ErasingEquation`. -/
theorem erasingLanguage_erasingEquation :
    ErasingEquation erasingLanguage "Datum" firstRule firstEquation where
  declared := by decide
  category := rfl
  params := ⟨"kept", "erased", rfl⟩
  authored := List.mem_singleton.mpr rfl
  premiseFree := rfl
  sides := ⟨"kept", "erased", by decide, rfl, rfl⟩

/-- The point, a closed term. -/
def erasingPoint : Contexts.Term erasingLanguage ⟨.base "Datum", []⟩ :=
  ⟨.apply "point" [], checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- **The language with an erasing equation discards**, for every evaluator of
premises and beneath any binders. -/
theorem erasingPresentation_discards (base : BasePremiseEvaluator) (stage : List TypeExpr) :
    (contextTheory base erasingPresentation).Discards ⟨.base "Datum", stage⟩ :=
  erasingLanguage_erasingEquation.discards (presentation := erasingPresentation) base stage

/-- So it has no linear size. -/
theorem erasingPresentation_not_linearSize (base : BasePremiseEvaluator) :
    IsEmpty (contextTheory base erasingPresentation).LinearSize :=
  ⟨fun sized => sized.not_discards erasingPoint (erasingPresentation_discards base [])⟩

/-- The constructor that a copying equation copies with. -/
def twiceRule : GrammarRule :=
  { label := "twice", category := "Datum", params := [.simple "copied" (.base "Datum")]
    syntaxPattern := [] }

/-- The constructor that a copying equation copies into. -/
def pairRule : GrammarRule :=
  { label := "pair", category := "Datum"
    params := [.simple "left" (.base "Datum"), .simple "right" (.base "Datum")]
    syntaxPattern := [] }

/-- `twice(copied) = pair(copied, copied)`. -/
def twiceEquation : Equation :=
  { name := "twice-is-pair"
    typeContext := [("copied", .base "Datum")]
    premises := []
    left := .apply "twice" [.fvar "copied"]
    right := .apply "pair" [.fvar "copied", .fvar "copied"] }

/-- **A language with a copying equation**: one sort, a point, a pairing and a
constructor of one argument equal to the pair of its argument with itself. -/
def copyingLanguage : LanguageDef :=
  { name := "copying"
    types := [TypeDecl.plain "Datum"]
    terms := [pointRule, twiceRule, pairRule]
    equations := [twiceEquation]
    rewrites := [] }

/-- The language with a copying equation passes the declaration gate. -/
theorem copyingLanguage_validate : copyingLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorEquationsAndRewrites
  case htypes => decide +kernel
  case hconstructors => decide +kernel
  case hequations => decide +kernel
  case hrewrites => decide +kernel
  case hcategory => decide +kernel
  case hparams => decide +kernel
  case hsyntax => decide +kernel
  case hequationValid =>
    intro equation member
    exact LanguageDef.validateEquation_eq_nil_of_plainEquationOk
      (List.all_eq_true.mp
        (by decide +kernel :
          copyingLanguage.equations.all (LanguageDef.plainEquationOk copyingLanguage) = true)
        equation member)
  case hrewriteValid =>
    intro rewrite member
    exact (List.not_mem_nil member).elim

/-- The language with a copying equation, as a presentation. -/
def copyingPresentation : ValidatedLanguageDef := ⟨copyingLanguage, copyingLanguage_validate⟩

/-- **Positive**, for `CopyingEquation`. -/
theorem copyingLanguage_copyingEquation :
    CopyingEquation copyingLanguage "Datum" twiceRule pairRule twiceEquation where
  copyDeclared := by decide
  pairDeclared := by decide
  copyCategory := rfl
  pairCategory := rfl
  copyParams := ⟨"copied", rfl⟩
  pairParams := ⟨"left", "right", rfl⟩
  authored := List.mem_singleton.mpr rfl
  premiseFree := rfl
  sides := ⟨"copied", rfl, rfl⟩

/-- The point of the language with a copying equation. -/
def copyingPoint : Contexts.Term copyingLanguage ⟨.base "Datum", []⟩ :=
  ⟨.apply "point" [], checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- **The language with a copying equation copies.** -/
theorem copyingPresentation_copies (base : BasePremiseEvaluator) (stage : List TypeExpr) :
    (contextTheory base copyingPresentation).Copies ⟨.base "Datum", stage⟩ :=
  copyingLanguage_copyingEquation.copies (presentation := copyingPresentation) base stage

/-- So it has no linear size. -/
theorem copyingPresentation_not_linearSize (base : BasePremiseEvaluator) :
    IsEmpty (contextTheory base copyingPresentation).LinearSize :=
  ⟨fun sized => sized.not_copies copyingPoint (copyingPresentation_copies base [])⟩

/-- **Negative**, for `ErasingEquation`: the one equation of the language
with a copying equation erases nothing. -/
theorem copyingLanguage_no_erasingEquation (sort : String) (rule : GrammarRule)
    (equation : Equation) : ¬ ErasingEquation copyingLanguage sort rule equation := by
  intro erasing
  obtain ⟨kept, erased, -, left, -⟩ := erasing.sides
  obtain rfl : equation = twiceEquation := List.mem_singleton.mp erasing.authored
  simp [twiceEquation] at left

/-- **Negative**, for `CopyingEquation`: the one equation of the language
with an erasing equation copies nothing. -/
theorem erasingLanguage_no_copyingEquation (sort : String) (copy pair : GrammarRule)
    (equation : Equation) : ¬ CopyingEquation erasingLanguage sort copy pair equation := by
  intro copying
  obtain ⟨copied, left, -⟩ := copying.sides
  obtain rfl : equation = firstEquation := List.mem_singleton.mp copying.authored
  simp [firstEquation] at left

/-- **Negative**, for `ErasingEquation`: the one equation of the candidate
presentation, that of quotation and dropping, erases nothing. -/
theorem language_no_erasingEquation (sort : String) (rule : GrammarRule) (equation : Equation) :
    ¬ ErasingEquation Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.language sort rule
      equation := by
  intro erasing
  obtain ⟨kept, erased, -, left, -⟩ := erasing.sides
  have member := erasing.authored
  rw [language_quoteDropOnly.equations] at member
  obtain rfl := List.mem_singleton.mp member
  simp [Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.quoteDropEquation] at left

/-- **Negative**, for `CopyingEquation`: nor does it copy anything. -/
theorem language_no_copyingEquation (sort : String) (copy pair : GrammarRule)
    (equation : Equation) :
    ¬ CopyingEquation Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.language sort copy
      pair equation := by
  intro copying
  obtain ⟨copied, left, -⟩ := copying.sides
  have member := copying.authored
  rw [language_quoteDropOnly.equations] at member
  obtain rfl := List.mem_singleton.mp member
  simp [Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef.quoteDropEquation] at left

#print axioms apply_wellSorted
#print axioms unaryContext
#print axioms binaryContext
#print axioms ErasingEquation.generator
#print axioms ErasingEquation.discards
#print axioms CopyingEquation.generator
#print axioms CopyingEquation.copies
#print axioms KeptWeight.equiv
#print axioms KeptWeight.linearSize
#print axioms KeptWeight.not_discards
#print axioms KeptWeight.not_copies
#print axioms QuoteDropOnly.keptWeight
#print axioms keptWeight_of_equationFree
#print axioms ErasingEquation.isEmpty_keptWeight
#print axioms CopyingEquation.isEmpty_keptWeight
#print axioms erasingLanguage_validate
#print axioms erasingLanguage_erasingEquation
#print axioms erasingPresentation_discards
#print axioms erasingPresentation_not_linearSize
#print axioms copyingLanguage_validate
#print axioms copyingLanguage_copyingEquation
#print axioms copyingPresentation_copies
#print axioms copyingPresentation_not_linearSize
#print axioms copyingLanguage_no_erasingEquation
#print axioms erasingLanguage_no_copyingEquation
#print axioms language_no_erasingEquation
#print axioms language_no_copyingEquation

end Mettapedia.Logic.HostingStyles.ContextReadings
