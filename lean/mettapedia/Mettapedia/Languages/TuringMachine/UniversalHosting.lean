import Mettapedia.Languages.TuringMachine.Universal
import Mettapedia.Languages.TuringMachine.Hosted
import Mettapedia.GSLT.Contexts.TermsAlone

/-!
# The universal Turing-machine theory hosts every machine, in the category of theories

`Universal` shows that the map from a machine into the universal theory
preserves bisimilarity and reflects it, for theories given by their terms
alone.  Here the target is the universal theory presented through its
contexts (`contextTheory base universal`), with all its contexts, and the
statement is in the vocabulary of maps of theories.

## What is proved

* `intoUniversalTheory machine` is a map of theories, from the machine on its
  configurations (`(configurationGSLT machine).termsAlone`) to the universal
  theory.  It is **hosting** (`intoUniversalTheory_hosting`): it reflects the
  static equivalence of the universal theory, which is the commutation of the
  members of a bag; it preserves steps; and every step of the image is the
  image of a step, up to that equivalence.
* **A machine is a label of the universal theory.**  `tableLabel machine` is
  the context "a bag of the rows of the machine and one hole".  Placing a
  configuration in it gives the bag of the machine
  (`apply_tableLabel`), and the transitions of a configuration that this
  context labels are the steps of the machine
  (`transition_tableLabel_iff`).  Two machines are two labels on the same
  terms.

## What is not proved, and why

The source above has no context but the hole.  The presentation of a machine
by its language definition has more: `Run` with a hole for the state, and so
on.  The map into the universal theory is not stated on that source.

* The existing construction of maps between presented theories starts from a
  map of declarations that carries rewrites to rewrites.  There is none from
  a machine with a table entry into the universal theory
  (`no_structuralMorphism_into_universal`): a rule of a machine is headed by
  `Run`, and the four rules of the universal theory are headed by the bag.
* A context of a presented theory is certified to be sorted in every
  presentation reached by such a map from its own presentation
  (`Contexts.Context.sorted`).  A context of a machine therefore carries no
  certificate for the presentations reached from the universal theory, and
  its image `bag of the context and the rows` cannot be shown to be a context
  of the universal theory.  The missing lemma is that the sorting of a context
  depends on the constructors alone: transfer of `Context.sorted` along a map
  of declarations that need not carry rewrites.
* Wrapping at the interface of configurations alone is not a map at all.  The
  language of a machine has terms at every type expression, bags of
  configurations among them, and the table bag does not commute with the
  one-element bag (`singletonBag_not_equivariant`).  The map has to wrap every
  `Run` inside a term, through bags and binders, and its typing has to be
  proved in every presentation that the universal theory maps into.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Contexts
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.BagNormalForm
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.Framework.TypeSynthesis

/-! ## Bags of rows and a configuration, as terms of the universal theory -/

/-- The interface of the closed terms of the sort of bags. -/
def soups : Interface := ⟨.base "Soup", []⟩

theorem ConstructorTerm.canonical {pattern : Pattern} (isTerm : ConstructorTerm pattern) :
    pattern.hasCanonicalBinderMetadata = true := by
  induction isTerm with
  | apply label arguments _ recurse =>
      simp only [Pattern.hasCanonicalBinderMetadata]
      exact hasCanonicalBinderMetadataList_iff.mpr recurse

theorem ConstructorTerm.object {pattern : Pattern} (isTerm : ConstructorTerm pattern) :
    isObjectPattern pattern = true := by
  induction isTerm with
  | apply label arguments _ recurse =>
      simp only [isObjectPattern]
      exact isObjectPatternList_iff.mpr recurse

/-- A bag of terms of the sort of bags is a term of that sort, in the
universal theory and in every presentation it maps into. -/
theorem soup_sorted {extension : ValidatedLanguageDef}
    (morphism : StructuralMorphism universal extension) (members : List Pattern)
    (sorted : ∀ member ∈ members,
      OpenPatternWellSorted extension.language FreeTypeContext.empty
        (soups.map morphism.symbols).stage (soups.map morphism.symbols).type member) :
    OpenPatternWellSorted extension.language FreeTypeContext.empty
      (soups.map morphism.symbols).stage (soups.map morphism.symbols).type (soup members) := by
  have typed : HasType extension.language FreeTypeContext.empty
      (soups.map morphism.symbols).stage (soup members) (soups.map morphism.symbols).type :=
    HasType.collectionConstructor
      (rule := mapGrammarRule morphism.symbols mixConstructor) (parameterName := "members")
      (morphism.mapsTerms _ mixConstructor_mem) rfl
      (elementsHaveType_iff.mpr fun member membership => (sorted member membership).1)
  refine ⟨typed, ?_, ?_, ?_⟩
  · simp only [soup, Pattern.hasCanonicalBinderMetadata]
    exact hasCanonicalBinderMetadataList_iff.mpr fun member membership =>
      (sorted member membership).2.1
  · simp only [soup, isObjectPattern, Option.isNone_none, Bool.true_and]
    exact isObjectPatternList_iff.mpr fun member membership => (sorted member membership).2.2.1
  · simpa [ScopeSafeAt] using typed.isWellScopedAt

/-- A constructor term of the sort of bags is a term of the universal
theory. -/
theorem constructorTerm_sorted {pattern : Pattern} (isTerm : ConstructorTerm pattern)
    (typed : HasType universalTheory FreeTypeContext.empty [] pattern (.base "Soup")) :
    OpenPatternWellSorted universalTheory FreeTypeContext.empty soups.stage soups.type pattern :=
  ⟨typed, isTerm.canonical, isTerm.object, typed.isWellScopedAt⟩

/-- A row, as a term of the universal theory. -/
theorem rowTerm_sorted (entry : Transition) :
    OpenPatternWellSorted universalTheory FreeTypeContext.empty soups.stage soups.type
      (rowTerm entry) :=
  constructorTerm_sorted (constructorTerm_rowTerm entry) (universal_hasType_rowTerm entry)

/-- The bag of the rows of a machine and a configuration is a term of the
universal theory. -/
theorem TableWith.sorted {machine : Machine} {configuration : Configuration}
    {members : List Pattern} (holds : TableWith machine configuration.term members) :
    OpenPatternWellSorted universalTheory FreeTypeContext.empty soups.stage soups.type
      (soup members) := by
  have typed : HasType universalTheory FreeTypeContext.empty [] (soup members) (.base "Soup") :=
    universal_hasType_soup fun member inMembers => by
      rcases List.mem_cons.mp (holds.mem_iff.mp inMembers) with rfl | inTable
      · exact universal_hasType_term configuration
      · obtain ⟨entry, -, rfl⟩ := List.mem_map.mp inTable
        exact universal_hasType_rowTerm entry
  refine ⟨typed, ?_, ?_, ?_⟩
  · simp only [soup, Pattern.hasCanonicalBinderMetadata]
    exact hasCanonicalBinderMetadataList_iff.mpr fun member inMembers =>
      (holds.constructorTerm member inMembers).canonical
  · simp only [soup, isObjectPattern, Option.isNone_none, Bool.true_and]
    exact isObjectPatternList_iff.mpr fun member inMembers =>
      (holds.constructorTerm member inMembers).object
  · exact typed.isWellScopedAt

/-- A bag of the rows of a machine and a configuration, as a term. -/
def bagTerm {machine : Machine} {configuration : Configuration} {members : List Pattern}
    (holds : TableWith machine configuration.term members) : Term universalTheory soups :=
  ⟨soup members, holds.sorted⟩

/-- **The image of a configuration**: the bag of the configuration and the
rows of the machine. -/
def tableTerm (machine : Machine) (configuration : Configuration) : Term universalTheory soups :=
  bagTerm (machine := machine) (configuration := configuration) (List.Perm.refl _)

@[simp] theorem tableTerm_val (machine : Machine) (configuration : Configuration) :
    (tableTerm machine configuration).1 = withTable machine configuration.term := rfl

/-- Two bags of the same rows and the same configuration are equal in the
universal theory: one instance of the commutation of the members. -/
theorem bag_equiv {machine : Machine} {configuration : Configuration}
    {members others : List Pattern} (holds : TableWith machine configuration.term members)
    (othersHold : TableWith machine configuration.term others)
    {first second : Term universalTheory soups} (firstShape : first.1 = soup members)
    (secondShape : second.1 = soup others) :
    (termSetoid base universalTheory soups).r first second := by
  refine Relation.EqvGen.rel _ _ ?_
  show EquationContextStep base universalTheory first.1 second.1
  rw [firstShape, secondShape]
  exact EquationContextStep.inContext .hole (Or.inr (DerivedInstance.bagPerm
    (rule := mixConstructor) ⟨mixConstructor_mem, "members", .base "Soup", rfl⟩ holds.sortedAt
    (holds.trans othersHold.symm)))

/-- The static equivalence of the terms of an interface is contained in that
of the patterns. -/
theorem equationEquiv_of_termSetoid {language : LanguageDef} {interface : Interface}
    {first second : Term language interface}
    (equivalent : (termSetoid base language interface).r first second) :
    EquationEquiv base language first.1 second.1 := by
  induction equivalent with
  | rel _ _ step => exact Relation.EqvGen.rel _ _ step
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ recurse => exact Relation.EqvGen.symm _ _ recurse
  | trans _ _ _ _ _ firstStep secondStep => exact Relation.EqvGen.trans _ _ _ firstStep secondStep

/-! ## The three laws on terms -/

/-- **No two configurations have the same image**, up to the static
equivalence of the universal theory. -/
theorem tableTerm_reflects (machine : Machine) (first second : Configuration)
    (equivalent : (termSetoid base universalTheory soups).r (tableTerm machine first)
      (tableTerm machine second)) : first = second := by
  have raw : EquationEquiv base universalTheory (withTable machine first.term)
      (withTable machine second.term) := equationEquiv_of_termSetoid equivalent
  exact hosts_unique (machine := machine) (term := withTable machine second.term)
    ((hosts_withTable machine first.term).of_equiv (Relation.EqvGen.symm _ _ raw))
    (hosts_withTable machine second.term)

/-- **A step of the machine is a step of the image.** -/
theorem tableTerm_preserves (machine : Machine) {first next : Configuration}
    (step : Step base (turingMachine machine) first.term next.term) :
    TermStep base universalTheory (tableTerm machine first) (tableTerm machine next) := by
  obtain ⟨after, engineStep, afterHolds⟩ :=
    tableWith_forward (machine := machine) (members := first.term :: description machine)
      (List.Perm.refl _) step
  exact ⟨tableTerm machine first, bagTerm afterHolds,
    (termSetoid base universalTheory soups).iseqv.refl _, engineStep,
    bag_equiv afterHolds (List.Perm.refl _) rfl rfl⟩

/-- **A step of the image is the image of a step of the machine**, up to the
static equivalence. -/
theorem tableTerm_reflectsSteps (machine : Machine) (first : Configuration)
    {next : Term universalTheory soups}
    (step : TermStep base universalTheory (tableTerm machine first) next) :
    ∃ after : Configuration, Step base (turingMachine machine) first.term after.term ∧
      (termSetoid base universalTheory soups).r next (tableTerm machine after) := by
  obtain ⟨redex, contractum, toRedex, engineStep, toNext⟩ := step
  have rawRedex : EquationEquiv base universalTheory
      (soup (first.term :: description machine)) redex.1 := equationEquiv_of_termSetoid toRedex
  obtain ⟨others, redexShape, othersHold⟩ :=
    tableWith_of_equiv_redex (machine := machine) (configuration := first)
      (members := first.term :: description machine) (List.Perm.refl _) rawRedex engineStep
  rw [redexShape] at engineStep
  obtain ⟨nextPattern, afterMembers, machineStep, contractumShape, afterHold⟩ :=
    tableWith_backward othersHold engineStep
  obtain ⟨entry, member, applies, rfl⟩ := step_term_iff.mp machineStep
  refine ⟨first.after entry, machineStep, ?_⟩
  exact (termSetoid base universalTheory soups).iseqv.trans
    ((termSetoid base universalTheory soups).iseqv.symm toNext)
    (bag_equiv afterHold (List.Perm.refl _) contractumShape rfl)

/-! ## The map of theories -/

/-- The configurations of a machine are compared by identity, so every map on
them respects their static equivalence. -/
theorem tableTerm_resp (table machine : Machine) {first second : Configuration}
    (same : (configurationGSLT machine).equations.r first second) :
    (termSetoid base universalTheory soups).r (tableTerm table first)
      (tableTerm table second) := by
  have equal : first = second := same
  rw [equal]

/-- The configurations of one machine in the bag of the rows of another. -/
def withTableOf (table machine : Machine) :
    ContextMap (configurationGSLT machine).termsAlone (contextTheory base universal) :=
  ContextMap.ofTerms (source := configurationGSLT machine) (target := contextTheory base universal)
    soups (tableTerm table) (tableTerm_resp table machine)

/-- **The map from a machine into the universal theory**, as a map of
theories presented through their contexts. -/
def intoUniversalTheory (machine : Machine) :
    ContextMap (configurationGSLT machine).termsAlone (contextTheory base universal) :=
  withTableOf machine machine

/-- **The universal theory hosts every machine**: the map reflects the static
equivalence, and it preserves and reflects the transitions that contexts
label. -/
theorem intoUniversalTheory_hosting (machine : Machine) : (intoUniversalTheory machine).Hosting :=
  (ContextMap.ofTerms_hosting_iff (source := configurationGSLT machine)
    (target := contextTheory base universal) soups (tableTerm machine)
    (tableTerm_resp machine machine)).mpr
    ⟨fun first second equivalent => tableTerm_reflects machine first second equivalent,
      fun _ _ step => tableTerm_preserves machine step,
      fun first _ step => tableTerm_reflectsSteps machine first step⟩

/-- What every probe of the machine sees is what the same probe, carried
along the map, sees of the images. -/
theorem intoUniversalTheory_bisimilar_iff (machine : Machine) (first second : Configuration) :
    ((intoUniversalTheory machine).push (configurationGSLT machine).termsAlone.fullProbe).Bisimilar
        (index := PUnit.unit) (tableTerm machine first) (tableTerm machine second) ↔
      (configurationGSLT machine).Bisimilar first second :=
  Iff.trans
    (ContextMap.Hosting.bisimilar_push_iff (intoUniversalTheory machine)
      (intoUniversalTheory_hosting machine) (configurationGSLT machine).termsAlone.fullProbe
      (index := PUnit.unit) (left := first) (right := second))
    (configurationGSLT machine).termsAlone_bisimilar_iff

/-! ## Negative: the wrong table, and what the host adds -/

/-- **The wrong table does not host.**  In the bag with no row a
configuration has no step, so the map does not preserve the steps of a
machine that has one. -/
theorem emptyTable_not_hosting {machine : Machine} {first next : Configuration}
    (step : Step base (turingMachine machine) first.term next.term) :
    ¬ (withTableOf ⟨[]⟩ machine).Hosting := by
  intro hosting
  have preserved : TermStep base universalTheory (tableTerm ⟨[]⟩ first) (tableTerm ⟨[]⟩ next) :=
    ((ContextMap.ofTerms_hosting_iff (source := configurationGSLT machine)
      (target := contextTheory base universal) soups (tableTerm ⟨[]⟩)
      (tableTerm_resp ⟨[]⟩ machine)).mp hosting).2.1 first next step
  obtain ⟨after, impossible, -⟩ := tableTerm_reflectsSteps ⟨[]⟩ first preserved
  obtain ⟨entry, member, -⟩ := step_term_iff.mp impossible
  cases member

/-- The two-state busy beaver is not hosted by the bag with no row. -/
theorem busyBeaver2_not_hosted_by_emptyTable : ¬ (withTableOf ⟨[]⟩ busyBeaver2).Hosting :=
  emptyTable_not_hosting (first := Configuration.blank)
    (next := Configuration.blank.after ⟨0, 0, 1, .right, 1⟩)
    (step_term_term_iff.mpr ⟨⟨0, 0, 1, .right, 1⟩, by decide, by decide, rfl⟩)

/-- A configuration, as a term of the sort of bags. -/
def runTerm (configuration : Configuration) : Term universalTheory soups :=
  ⟨configuration.term, constructorTerm_sorted (constructorTerm_term configuration)
    (universal_hasType_term configuration)⟩

/-- **The map is not exhausting**: a configuration outside every bag is a
term of the universal theory and the image of no configuration. -/
theorem intoUniversalTheory_not_exhausting (machine : Machine) :
    ¬ (intoUniversalTheory machine).Exhausting := by
  intro exhausting
  obtain ⟨preimage, equivalent⟩ := ContextMap.Exhausting.term_surjective _ exhausting
    (origin := PUnit.unit) (runTerm Configuration.blank)
  have raw : EquationEquiv base universalTheory Configuration.blank.term
      (withTable machine preimage.term) := equationEquiv_of_termSetoid equivalent
  have same := normalForm_eq_of_equationEquiv universalTheory_bagTheory
    (Relation.EqvGen.symm _ _ raw)
  rw [(constructorTerm_term Configuration.blank).normalForm_eq] at same
  have shape := (constructorTerm_term Configuration.blank).eq_of_normalForm_eq _ same
  simp [withTable, soup, Configuration.term, run] at shape

/-! ## A machine is a label of the universal theory -/

/-- The bag with one hole and the rows of a machine. -/
def tableShape (machine : Machine) : MultiHoleContext Unit :=
  .collection .hashBag (.hole () :: (description machine).map MultiHoleContext.ofPattern) none

theorem holes_tableShape (machine : Machine) :
    MultiHoleContext.holes (tableShape machine) = [()] := by
  have rows : ∀ patterns : List Pattern,
      (patterns.map (MultiHoleContext.ofPattern (ι := Unit))).flatMap MultiHoleContext.holes =
        [] := by
    intro patterns
    induction patterns with
    | nil => rfl
    | cons pattern patterns recurse =>
        simp only [List.map_cons, List.flatMap_cons, MultiHoleContext.holes_ofPattern, recurse,
          List.append_nil]
  simp only [tableShape, MultiHoleContext.holes, MultiHoleContext.holesList_eq_flatMap,
    List.flatMap_cons, rows, List.append_nil]

theorem fill_tableShape (machine : Machine) (symbols : LanguageDefSymbolMap)
    (filling : Unit → Pattern) :
    (mapContextSymbols symbols (tableShape machine)).fill filling =
      soup (filling () :: (description machine).map (mapPattern symbols)) := by
  simp only [tableShape, mapContextSymbols, mapContextSymbolsList_eq_map, List.map_cons,
    List.map_map, MultiHoleContext.fill, MultiHoleContext.fillList_eq_map, soup]
  congr 2
  apply List.map_congr_left
  intro pattern _
  simp only [Function.comp, mapContextSymbols_ofPattern, MultiHoleContext.fill_ofPattern]

/-- **The table of a machine, as a context of the universal theory.** -/
def tableLabel (machine : Machine) : (contextTheory base universal).Label soups soups where
  shape := tableShape machine
  linear := by
    rw [MultiHoleContext.Linear, holes_tableShape]
    exact ⟨by simp, fun _ => by simp⟩
  sorted := fun morphism filling => by
    rw [fill_tableShape]
    apply soup_sorted morphism
    intro member membership
    rcases List.mem_cons.mp membership with rfl | inRows
    · exact (filling ()).2
    · obtain ⟨row, inDescription, rfl⟩ := List.mem_map.mp inRows
      obtain ⟨entry, -, rfl⟩ := List.mem_map.mp inDescription
      exact openPatternWellSorted_map morphism (rowTerm_sorted entry)

/-- **Placing a configuration in the table of a machine gives the bag of the
machine.** -/
theorem apply_tableLabel (machine : Machine) (configuration : Configuration) :
    (contextTheory base universal).apply (tableLabel machine) (runTerm configuration) =
      tableTerm machine configuration := by
  apply Subtype.ext
  show (tableShape machine).fill (fun _ => configuration.term) = withTable machine configuration.term
  have filled := fill_tableShape machine LanguageDefSymbolMap.id fun _ => configuration.term
  rw [mapContextSymbols_id] at filled
  rw [filled]
  simp [withTable]

/-- **The transitions of a configuration that the table of a machine labels
are the steps of the machine.** -/
theorem transition_tableLabel_iff (machine : Machine) (configuration : Configuration)
    (next : Term universalTheory soups) :
    (contextTheory base universal).Transition (runTerm configuration) (tableLabel machine) next ↔
      ∃ after : Configuration,
        Step base (turingMachine machine) configuration.term after.term ∧
          (termSetoid base universalTheory soups).r next (tableTerm machine after) := by
  show TermStep base universalTheory
    ((contextTheory base universal).apply (tableLabel machine) (runTerm configuration)) next ↔ _
  rw [apply_tableLabel]
  constructor
  · exact tableTerm_reflectsSteps machine configuration
  · rintro ⟨after, step, equivalent⟩
    exact termStep_resp_right base universalTheory (tableTerm_preserves machine step)
      ((termSetoid base universalTheory soups).iseqv.symm equivalent)

/-! ## The obstruction to the structural route -/

/-- **No map of declarations that carries rewrites to rewrites goes from a
machine with a table entry into the universal theory.**  A rule of a machine
is headed by `Run`; the rules of the universal theory are headed by the
bag. -/
theorem no_structuralMorphism_into_universal (machine : Machine)
    (nonempty : machine.transitions ≠ []) :
    IsEmpty (StructuralMorphism (naive machine) universal) := by
  refine ⟨fun morphism => ?_⟩
  obtain ⟨entry, rest, table⟩ := List.exists_cons_of_ne_nil nonempty
  have ruleMember : interiorRule 0 entry ∈ (turingMachine machine).rewrites := by
    show interiorRule 0 entry ∈ rewrites machine
    unfold rewrites
    rw [table]
    simp
  obtain ⟨control, tape, left⟩ := rewrites_headed_by_run machine _ ruleMember
  have image := morphism.mapsRewrites _ ruleMember
  have imageLeft : (mapRewriteRule morphism.symbols (interiorRule 0 entry)).left =
      .apply (morphism.symbols.constructor "Run")
        (mapPatternList morphism.symbols [control, tape]) := by
    show mapPattern morphism.symbols (interiorRule 0 entry).left = _
    rw [left]
    rfl
  have inRules : mapRewriteRule morphism.symbols (interiorRule 0 entry) ∈
      [interiorRightRule, interiorLeftRule, edgeRightRule, edgeLeftRule] := image
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inRules
  rcases inRules with same | same | same | same <;>
    · rw [same] at imageLeft
      simp [interiorRightRule, interiorLeftRule, edgeRightRule, edgeLeftRule] at imageLeft

/-! ## The obstruction to wrapping at one interface only -/

/-- **The table bag does not commute with the one-element bag.**  A bag of one
configuration is a term of the machine and of the universal theory, at the
type of bags of configurations.  A map that wraps a configuration into its
table bag at the interface of configurations, and leaves the patterns of the
other interfaces as they are, would have to identify the two sides here.
They are not equal in the universal theory: its one static law reorders the
members of a bag and does not open a bag inside a bag.  So the map from a
machine with all its contexts has to be defined through every type former,
bags and binders included, and not at the interface of configurations
alone. -/
theorem singletonBag_not_equivariant (machine : Machine) (configuration : Configuration) :
    ¬ EquationEquiv base universalTheory (.collection .hashBag [configuration.term] none)
      (.collection .hashBag [withTable machine configuration.term] none) := by
  intro equivalent
  have same := normalForm_eq_of_equationEquiv universalTheory_bagTheory equivalent
  rw [normalForm_bag, normalForm_bag] at same
  simp only [normalizeBag, Pattern.collection.injEq, true_and, and_true, List.map_cons,
    List.map_nil] at same
  have perm : [normalForm none configuration.term].Perm
      [normalForm none (withTable machine configuration.term)] :=
    (sortPatterns_perm _).symm.trans (same ▸ sortPatterns_perm _)
  have equal := List.perm_singleton.mp perm
  have heads : normalForm none (withTable machine configuration.term) =
      normalForm none configuration.term := (List.cons.inj equal).1.symm
  rw [(constructorTerm_term configuration).normalForm_eq] at heads
  have shape := (constructorTerm_term configuration).eq_of_normalForm_eq _ heads
  simp [withTable, soup, Configuration.term, run] at shape

#print axioms intoUniversalTheory
#print axioms singletonBag_not_equivariant
#print axioms intoUniversalTheory_hosting
#print axioms intoUniversalTheory_bisimilar_iff
#print axioms emptyTable_not_hosting
#print axioms busyBeaver2_not_hosted_by_emptyTable
#print axioms intoUniversalTheory_not_exhausting
#print axioms apply_tableLabel
#print axioms transition_tableLabel_iff
#print axioms no_structuralMorphism_into_universal

end Mettapedia.Languages.TuringMachine
