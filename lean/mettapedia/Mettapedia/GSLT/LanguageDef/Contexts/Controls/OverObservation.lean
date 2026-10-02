import Mettapedia.GSLT.Contexts.ImageObservation
import Mettapedia.GSLT.LanguageDef.Contexts.Structural
import Mettapedia.GSLT.LanguageDef.Contexts.TypedLabels
import Mettapedia.GSLT.LanguageDef.Interaction.Controls.ContactMorphisms

/-!
# A target that observes too much

The law-free contact theory has two constants, `A` and `B`, that no rule of
the theory mentions.  Exchanging them is a symmetry, so no context of the
theory tells them apart: they are bisimilar over all its context-labelled
transitions.

Add one constructor, `Test`, and one rule, `Test(A) ⟶ Nil`.  The rule looks
at what it is handed.  The inclusion of the contact theory into the extended
theory is a morphism: what every probe of the contact theory sees is
preserved, because the bisimilarity of the extended theory is computed over
the images of the contact theory's contexts, and none of them is `Test`.
Computed over all the contexts of the extended theory, the images of `A` and
`B` are separated at once, by the context `Test`.

So the inclusion preserves bisimulation when the target is observed through
the source's contexts, and does not when the target is observed through all
of its own.  The separating context goes from the image of an interface to
the image of an interface, so the inclusion is a map for which the contexts
of the target between images of interfaces see more than the images of the
source's contexts: the equality of the two that an exhausting map enjoys
fails for it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Contexts.Controls

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Contexts
open Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-! ## The contact theory at every interface -/

/-- The validated law-free contact presentation. -/
abbrev bareValidated : ValidatedLanguageDef := barePresentation.presentation

/-- The interface of closed processes. -/
abbrev proc : Interface := closedInterface (presentation := bareValidated)
  barePresentation.interactingLangSort

theorem bare_equationFree : bareValidated.language.isEquationFree = true := by decide

/-- A reduct of a term of an interface is a term of the interface. -/
theorem bare_reduct_sorted {stage : List TypeExpr} {type : TypeExpr} {first second : Pattern}
    (sorted : OpenPatternWellSorted (contactWith []) FreeTypeContext.empty stage type
      (join (input first) (output second))) :
    OpenPatternWellSorted (contactWith []) FreeTypeContext.empty stage type
      (join first second) := by
  obtain ⟨typed, canonical, object, wellScoped⟩ := sorted
  refine ⟨hasType_reduct typed, ?_, ?_, ?_⟩
  · simpa [join, input, output, Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList] using canonical
  · simpa [join, input, output, isObjectPattern, isObjectPatternList] using object
  · simpa [ScopeSafeAt, join, input, output, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt] using wellScoped

/-- The reductions of the contact theory at an interface. -/
theorem bare_termStep_iff {interface : Interface}
    {term next : Term bareValidated.language interface} :
    TermStep base bareValidated.language term next ↔
      ∃ first second, term.1 = join (input first) (output second) ∧
        next.1 = join first second := by
  rw [termStep_iff_step base _ bare_equationFree]
  exact step_iff_of_rewrites (language := contactWith []) rfl

/-- The two constants as terms of the interface of closed processes. -/
def constantA : Term bareValidated.language proc := ofClosed closedA

/-- The second constant. -/
def constantB : Term bareValidated.language proc := ofClosed closedB

/-- **No context of the contact theory separates the two constants.**  Terms
that agree after renaming `B` to `A` are bisimilar over all context-labelled
transitions. -/
theorem bisimilar_of_collapse_eq {interface : Interface}
    {left right : Term bareValidated.language interface}
    (same : mapPattern collapseSymbols left.1 = mapPattern collapseSymbols right.1) :
    (contextTheory base bareValidated).fullProbe.Bisimilar (index := interface) left right := by
  have transfer : ∀ {origin result : Interface}
      {first second : Term bareValidated.language origin},
      mapPattern collapseSymbols first.1 = mapPattern collapseSymbols second.1 →
      ∀ (label : (contextTheory base bareValidated).Label origin result)
        {next : Term bareValidated.language result},
        (contextTheory base bareValidated).Transition first label next →
          ∃ next' : Term bareValidated.language result,
            (contextTheory base bareValidated).Transition second label next' ∧
              mapPattern collapseSymbols next.1 = mapPattern collapseSymbols next'.1 := by
    intro origin result first second agree label next transition
    obtain ⟨context, plugs⟩ := exists_oneHole_of_label base label
    obtain ⟨x, y, shape, nextShape⟩ := (bare_termStep_iff).mp transition
    have image : mapPattern collapseSymbols
        ((contextTheory base bareValidated).apply label second).1 =
        join (input (mapPattern collapseSymbols x)) (output (mapPattern collapseSymbols y)) := by
      rw [plugs second, ← CIGSLT.mapOneHoleContext_fill, ← agree,
        CIGSLT.mapOneHoleContext_fill, ← plugs first, shape, collapse_join]
    obtain ⟨x', y', shape', imageX, imageY⟩ := collapse_join_inv image
    have sorted := ((contextTheory base bareValidated).apply label second).2
    rw [shape'] at sorted
    refine ⟨⟨join x' y', bare_reduct_sorted sorted⟩, ?_, ?_⟩
    · exact (bare_termStep_iff).mpr ⟨x', y', shape', rfl⟩
    · rw [nextShape, collapse_contact, collapse_contact, imageX, imageY]
  refine ⟨fun index first second =>
    mapPattern collapseSymbols first.1 = mapPattern collapseSymbols second.1, ⟨?_, ?_⟩, same⟩
  · intro origin first second agree result label next transition
    exact transfer agree label transition
  · intro origin first second agree result label next' transition
    obtain ⟨next, step, nextAgree⟩ := transfer agree.symm label transition
    exact ⟨next, step, nextAgree.symm⟩

theorem constants_bisimilar :
    (contextTheory base bareValidated).fullProbe.Bisimilar (index := proc) constantA constantB :=
  bisimilar_of_collapse_eq (by decide +kernel)

/-! ## The theory with a rule that looks at its argument -/

/-- The declaration of the observing constructor. -/
def testDeclaration : GrammarRule :=
  { label := "Test", category := "Proc",
    params := [.simple "body" (.base "Proc")], syntaxPattern := [.nonTerminal "body"] }

/-- `Test(A) ⟶ Nil`. -/
def testRule : RewriteRule where
  name := "Test"
  typeContext := []
  premises := []
  left := .apply "Test" [termA]
  right := termNil

/-- The contact theory with the observing constructor and its rule. -/
def probingLanguage : LanguageDef :=
  { name := "Probing"
    types := ["Proc"]
    terms := terms ++ [testDeclaration]
    equations := []
    rewrites := [syncRule, testRule] }

theorem testRule_validates : LanguageDef.validateRewrite probingLanguage testRule = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [testRule, probingLanguage, terms, testDeclaration, termA, termNil]

theorem probingSync_validates : LanguageDef.validateRewrite probingLanguage syncRule = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [syncRule, join, probingLanguage, terms, testDeclaration]

theorem probing_validate_eq_nil : probingLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  · rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
  · intro rewrite membership
    have cases : rewrite = syncRule ∨ rewrite = testRule := by
      have listed : rewrite ∈ [syncRule, testRule] := membership
      simpa using listed
    rcases cases with rfl | rfl
    · exact probingSync_validates
    · exact testRule_validates

/-- The validated extended presentation. -/
def probingValidated : ValidatedLanguageDef := ⟨probingLanguage, probing_validate_eq_nil⟩

theorem probing_equationFree : probingValidated.language.isEquationFree = true := by decide

/-- The rules of the extended theory carry no premise and bind nothing. -/
theorem probing_plainRules : PlainRules probingLanguage := by
  intro rule membership
  have cases : rule = syncRule ∨ rule = testRule := by
    have listed : rule ∈ [syncRule, testRule] := membership
    simpa using listed
  rcases cases with rfl | rfl <;> exact ⟨rfl, by decide +kernel⟩

/-- **The reductions of the extended theory**: the contact rule, and the
observing rule on `A` alone. -/
theorem probing_step_iff {source target : Pattern} :
    Step base probingLanguage source target ↔
      (∃ first second, source = join (input first) (output second) ∧
        target = join first second) ∨
      (source = .apply "Test" [termA] ∧ target = termNil) := by
  constructor
  · intro step
    obtain ⟨rule, membership, bindings, rfl, rfl⟩ :=
      sides_of_step probing_plainRules (by
        intro rule membership
        have cases : rule = syncRule ∨ rule = testRule := by
          have listed : rule ∈ [syncRule, testRule] := membership
          simpa using listed
        rcases cases with rfl | rfl <;> decide) step
    have cases : rule = syncRule ∨ rule = testRule := by
      have listed : rule ∈ [syncRule, testRule] := membership
      simpa using listed
    rcases cases with rfl | rfl
    · exact .inl ⟨applyBindings bindings (.fvar "x"), applyBindings bindings (.fvar "y"),
        by simp [syncRule, join, input, output, applyBindings],
        by simp [syncRule, join, applyBindings]⟩
    · exact .inr ⟨by simp [testRule, termA, applyBindings],
        by simp [testRule, termNil, applyBindings]⟩
  · rintro (⟨first, second, rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · obtain ⟨bindings, matched, applied⟩ := sync_matches first second
      exact (step_iff_exists_match probing_plainRules).mpr
        ⟨syncRule, List.Mem.head _, bindings, matched, applied⟩
    · exact (step_iff_exists_match probing_plainRules).mpr
        ⟨testRule, List.Mem.tail _ (List.Mem.head _), by decide +kernel⟩

/-- The inclusion of the contact theory into the extended theory. -/
def toProbing : StructuralMorphism bareValidated probingValidated where
  symbols := LanguageDefSymbolMap.id
  mapsTypes := by
    intro declaration membership
    rw [mapTypeDecl_id]
    exact membership
  mapsTerms := by
    intro rule membership
    rw [mapGrammarRule_id]
    exact List.mem_append_left _ membership
  mapsEquations := by
    intro equation membership
    cases membership
  mapsRewrites := by
    intro rewrite membership
    rw [mapRewriteRule_id]
    obtain rfl : rewrite = syncRule := List.mem_singleton.mp membership
    exact List.Mem.head _

/-- A term of the contact theory is not headed by the observing
constructor. -/
theorem bare_term_ne_test {interface : Interface} (term : Term bareValidated.language interface)
    (arguments : List Pattern) : term.1 ≠ .apply "Test" arguments := by
  intro shape
  have typed := term.2.1
  rw [shape] at typed
  obtain ⟨rule, ruleMember, ruleLabel, -⟩ := typed.apply_inv
  change rule ∈ terms at ruleMember
  simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at ruleMember
  rcases ruleMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact absurd ruleLabel (by decide)

/-- The inclusion preserves each authored contact reduction. -/
theorem toProbing_preservesSteps : PreservesSteps base toProbing :=
  preservesSteps_of_equationFree base toProbing bare_equationFree probing_equationFree (by
    intro pattern next step
    change Step base probingLanguage (mapPattern LanguageDefSymbolMap.id pattern)
      (mapPattern LanguageDefSymbolMap.id next)
    rw [mapPattern_id, mapPattern_id]
    exact probing_step_iff.mpr
      (.inl ((step_iff_of_rewrites (language := contactWith []) rfl).mp step)))

/-- Every reduction of an image term is lifted to the contact theory.  Source
terms cannot be headed by the new observing constructor. -/
theorem toProbing_reflectsSteps : ReflectsSteps base toProbing :=
  reflectsSteps_of_equationFree base toProbing bare_equationFree probing_equationFree (by
    intro interface term next step
    change Step base probingLanguage (mapPattern LanguageDefSymbolMap.id term.1) next at step
    rw [mapPattern_id] at step
    rcases probing_step_iff.mp step with ⟨first, second, shape, rfl⟩ | ⟨shape, -⟩
    · have sorted := term.2
      rw [shape] at sorted
      refine ⟨⟨join first second, bare_reduct_sorted sorted⟩, ?_, ?_⟩
      · exact (step_iff_of_rewrites (language := contactWith []) rfl).mpr
          ⟨first, second, shape, rfl⟩
      · change _ = mapPattern LanguageDefSymbolMap.id (join first second)
        rw [mapPattern_id]
    · exact absurd shape (bare_term_ne_test term _))

/-- The inclusion is a morphism: its transitions transport forward and lift
backward along image contexts. -/
def toProbingMorphism :
    ContextMorphism (contextTheory base bareValidated) (contextTheory base probingValidated) :=
  structuralContextMorphism base toProbing
    (preservesEquations_of_equationFree base toProbing bare_equationFree)
    toProbing_preservesSteps toProbing_reflectsSteps

/-! ## The observing context -/

/-- The interface of closed processes of the extended theory, as the image of
the one of the contact theory. -/
abbrev probingProc : Interface := proc.map toProbing.symbols

/-- The context `Test([-])` is a label of the extended theory. -/
def testLabel : (contextTheory base probingValidated).Label probingProc probingProc :=
  labelOfOccurrence (presentation := probingValidated) (source := probingProc)
    (target := probingProc) (.apply "Test" [] .hole []) (label := "A") (arguments := [])
    (TypedAt.application (rule := testDeclaration) (beforeParams := []) (afterParams := [])
      (parameter := .simple "body" (.base "Proc"))
      (List.mem_append_right _ (List.Mem.head _))
      (by rintro ⟨name, kind, element, shape⟩; cases shape)
      (.cons trivial rfl
        (HasType.constructor (rule := terms[0])
          (List.mem_append_left _ (List.getElem_mem (by decide)))
          (by rintro ⟨name, kind, element, shape⟩; cases shape) .nil) .nil)
      rfl rfl rfl
      (.here (HasType.constructor (rule := terms[0])
        (List.mem_append_left _ (List.getElem_mem (by decide)))
        (by rintro ⟨name, kind, element, shape⟩; cases shape) .nil)))
    (by decide +kernel) (by decide +kernel)

/-- Placing a term in the observing context applies `Test` to it. -/
theorem apply_testLabel (term : Term probingValidated.language probingProc) :
    ((contextTheory base probingValidated).apply testLabel term).1 = .apply "Test" [term.1] :=
  apply_labelOfOccurrence base _ _ _ _ term

/-- **Over the contexts of the extended theory between images of interfaces
the two images are separated**, by the context `Test`. -/
theorem images_not_bisimilar_targetProbe :
    ¬ toProbingMorphism.targetProbe.Bisimilar (index := proc)
      (Term.map toProbing constantA) (Term.map toProbing constantB) := by
  rintro ⟨relation, ⟨forward, -⟩, related⟩
  have fires : (contextTheory base probingValidated).Transition
      (Term.map toProbing constantA) testLabel
      (Term.map toProbing (ofClosed (ClosedTerm.ofCheck termNil (by decide +kernel)))) := by
    apply (termStep_iff_step base _ probing_equationFree _ _).mpr
    rw [apply_testLabel]
    exact probing_step_iff.mpr (.inr ⟨by decide +kernel, by decide +kernel⟩)
  obtain ⟨next, step, -⟩ := forward related (target := proc) testLabel fires
  have raw := (termStep_iff_step base _ probing_equationFree _ _).mp step
  change Step base probingLanguage
    ((contextTheory base probingValidated).apply testLabel (Term.map toProbing constantB)).1
    next.1 at raw
  rw [apply_testLabel] at raw
  rcases probing_step_iff.mp raw with ⟨first, second, shape, -⟩ | ⟨shape, -⟩
  · simp [join] at shape
  · revert shape
    decide +kernel

/-- **Over all the contexts of the extended theory the two images are
separated.** -/
theorem images_not_bisimilar :
    ¬ (contextTheory base probingValidated).fullProbe.Bisimilar (index := probingProc)
      (Term.map toProbing constantA) (Term.map toProbing constantB) :=
  fun bisimilar => images_not_bisimilar_targetProbe
    (toProbingMorphism.toContextMap.bisimilar_targetProbe_of_fullProbe (origin := proc)
      bisimilar)

/-- **A target that observes too much.**  The two constants are bisimilar over
all contexts of the contact theory.  Their images are bisimilar when the
extended theory is observed through the images of those contexts, and are
not when it is observed through all of its own. -/
theorem over_observation :
    (contextTheory base bareValidated).fullProbe.Bisimilar (index := proc) constantA constantB ∧
    (toProbingMorphism.push (contextTheory base bareValidated).fullProbe).Bisimilar
      (index := proc) (Term.map toProbing constantA) (Term.map toProbing constantB) ∧
    ¬ (contextTheory base probingValidated).fullProbe.Bisimilar (index := probingProc)
      (Term.map toProbing constantA) (Term.map toProbing constantB) :=
  ⟨constants_bisimilar, toProbingMorphism.preserves_full constants_bisimilar,
    images_not_bisimilar⟩

/-- **The contexts of the target see more than the images of the source's
contexts.**  For the inclusion the two bisimilarities on images differ, so
the conclusion of `ContextMap.Exhausting.bisimilar_targetProbe_iff` fails for
a map that is not exhausting. -/
theorem targetProbe_sees_more :
    (toProbingMorphism.push (contextTheory base bareValidated).fullProbe).Bisimilar
      (index := proc) (Term.map toProbing constantA) (Term.map toProbing constantB) ∧
    ¬ toProbingMorphism.targetProbe.Bisimilar (index := proc)
      (Term.map toProbing constantA) (Term.map toProbing constantB) :=
  ⟨toProbingMorphism.preserves_full constants_bisimilar, images_not_bisimilar_targetProbe⟩

end Mettapedia.GSLT.LanguageDef.Contexts.Controls
