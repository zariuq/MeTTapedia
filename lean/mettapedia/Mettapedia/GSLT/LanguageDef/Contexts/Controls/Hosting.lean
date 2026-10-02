import Mettapedia.GSLT.LanguageDef.Contexts.Controls.OverObservation

/-!
# Hosting and exhausting, separated

Three maps of the law-free contact theory.

* The identity is hosting and exhausting.
* The renaming of the constant `B` to the constant `A` is a morphism: it
  preserves what every probe sees.  It is not hosting, because it identifies
  two terms; and it is not a constant map, so identifying terms is what
  hosting excludes, of which the constant map is the extreme case.  It is not
  exhausting either: the term `B` is the image of nothing.
* The inclusion into the theory with the observing constructor is hosting,
  because it is injective on terms and its image transitions lift back to the
  source.  It is not exhausting: the target has a
  term, `Test(A)`, that is the image of nothing.

An iGSLT morphism is a map of declarations that preserves reduction
bisimilarity.  When its map of declarations also preserves the static
equivalence, preserves reductions and reflects the reductions of images, it
is a morphism of the context theories.  The first two of these hold of
themselves as soon as the map fixes the name of the built-in relation and the
units that collection algebras declare, so the reflection of reductions is
the one condition left.  The renaming of `B` to `A`, which is not injective,
is an instance.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.GSLT.LanguageDef.Contexts.Controls

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Contexts
open Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-! ## From iGSLT morphisms -/

/-- **An iGSLT morphism whose map of declarations preserves the static
equivalence, preserves reductions and reflects the reductions of images is a
morphism of the context theories.**  The three conditions are not part of an
iGSLT morphism, which asks only that reduction bisimilarity be preserved.
This form asks nothing of the names the map fixes; when it fixes the built-in
relation and the declared units, `ofReflectingIGSLTMorphism` needs the third
condition alone. -/
def ofIGSLTMorphism {source target : IGSLT} (morphism : source ⟶ target)
    (equations : PreservesEquations defaultBasePremises morphism.structural.structural)
    (steps : PreservesSteps defaultBasePremises morphism.structural.structural)
    (reflects : ReflectsSteps defaultBasePremises morphism.structural.structural) :
    ContextMorphism (contextTheory defaultBasePremises source.presentation.presentation)
      (contextTheory defaultBasePremises target.presentation.presentation) :=
  structuralContextMorphism defaultBasePremises morphism.structural.structural equations steps
    reflects

/-- **An iGSLT morphism that reflects the reductions of images is a morphism
of the context theories.**  That it preserves the static equivalence and
reductions is proved; the two conditions on names are that the built-in
relation and the units declared by collection algebras keep theirs. -/
def ofReflectingIGSLTMorphism {source target : IGSLT} (morphism : source ⟶ target)
    (relationFixesEq : morphism.structural.structural.symbols.relation "eq" = "eq")
    (units : EquationSimulation.FixesDeclaredUnits morphism.structural.structural.symbols
      source.presentation.presentation.language)
    (reflects : ReflectsSteps defaultBasePremises morphism.structural.structural) :
    ContextMorphism (contextTheory defaultBasePremises source.presentation.presentation)
      (contextTheory defaultBasePremises target.presentation.presentation) :=
  structuralContextMorphism_of_reflects morphism.structural.structural relationFixesEq units
    reflects

/-! ## The renaming -/

/-- The contact theory declares no collection algebra, so the renaming has no
declared unit to fix. -/
theorem collapse_fixesUnits :
    EquationSimulation.FixesDeclaredUnits collapseStructural.symbols bareValidated.language :=
  EquationSimulation.fixesDeclaredUnits_of_no_algebra _ (by decide)

/-- The renaming preserves the static equivalence: an instance of the general
statement at a map that is not injective. -/
theorem collapse_preservesEquations : PreservesEquations base collapseStructural :=
  preservesEquations_default collapseStructural rfl collapse_fixesUnits

/-- The renaming preserves reduction at every interface, by the same general
statement. -/
theorem collapse_preservesSteps : PreservesSteps base collapseStructural :=
  preservesSteps_default collapseStructural rfl collapse_fixesUnits

/-- Every reduction of the renaming of a term is the renaming of a
reduction. -/
theorem collapse_reflectsSteps : ReflectsSteps base collapseStructural :=
  reflectsSteps_of_equationFree base collapseStructural bare_equationFree bare_equationFree
    (by
      intro interface term next step
      obtain ⟨first', second', image, rfl⟩ :=
        (step_iff_of_rewrites (language := contactWith []) rfl).mp step
      obtain ⟨first, second, shape, rfl, rfl⟩ :=
        collapse_join_inv (pattern := term.1) image
      have sorted := term.2
      rw [shape] at sorted
      refine ⟨⟨join first second, bare_reduct_sorted sorted⟩, ?_, ?_⟩
      · exact (step_iff_of_rewrites (language := contactWith []) rfl).mpr
          ⟨first, second, shape, rfl⟩
      · exact (collapse_contact first second).symm)

/-- **The iGSLT morphism that renames `B` to `A` is a morphism of
theories.** -/
def collapseMorphism :
    ContextMorphism (contextTheory base bareValidated) (contextTheory base bareValidated) :=
  ofReflectingIGSLTMorphism collapse rfl collapse_fixesUnits collapse_reflectsSteps

/-- In the contact theory, terms of an interface are equivalent only when
they are equal. -/
theorem bare_equivalent_iff {interface : Interface}
    (left right : Term bareValidated.language interface) :
    (termSetoid base bareValidated.language interface).r left right ↔ left = right :=
  termSetoid_iff_eq base _ bare_equationFree left right

/-- **The renaming is not hosting**: it identifies the two constants. -/
theorem collapse_not_hosting : ¬ collapseMorphism.toContextMap.Hosting := by
  refine ContextMap.not_hosting_of_identifies (first := constantA) (second := constantB) _ ?_ ?_
  · intro equivalent
    have same := (bare_equivalent_iff constantA constantB).mp equivalent
    have patterns : termA = termB := congrArg Subtype.val same
    revert patterns
    decide
  · have same : Term.map collapseStructural constantA = Term.map collapseStructural constantB :=
      Subtype.ext (by decide +kernel)
    change (termSetoid base bareValidated.language _).r (Term.map collapseStructural constantA)
      (Term.map collapseStructural constantB)
    rw [same]
    exact Relation.EqvGen.refl _

/-- A renamed term does not mention `B`. -/
theorem collapse_ne_termB (pattern : Pattern) : mapPattern collapseSymbols pattern ≠ termB := by
  intro image
  obtain ⟨label, arguments, -, labelImage, -⟩ :=
    (mapPattern_eq_apply_iff _ _ _ _).mp image
  unfold collapseSymbols at labelImage
  by_cases isB : label = "B"
  · simp [isB] at labelImage
  · simp [isB] at labelImage

/-- **The renaming is not exhausting**: the constant `B` is the image of
nothing. -/
theorem collapse_not_exhausting : ¬ collapseMorphism.toContextMap.Exhausting := by
  intro exhausting
  obtain ⟨preimage, equivalent⟩ := ContextMap.Exhausting.term_surjective _ exhausting
    (origin := proc) (show Term bareValidated.language (proc.map collapseSymbols) from constantB)
  have same := (bare_equivalent_iff _ _).mp equivalent
  have patterns : termB = mapPattern collapseSymbols preimage.1 := congrArg Subtype.val same
  exact collapse_ne_termB preimage.1 patterns.symm

/-! ## The inclusion -/

/-- The inclusion is faithful on contexts because it is injective on terms. -/
theorem toProbing_faithful : toProbingMorphism.toContextMap.Faithful := by
  apply (ContextMap.faithful_iff_reflectsEquations _).mpr
  intro origin first second equivalent
  have same := (termSetoid_iff_eq base _ probing_equationFree _ _).mp equivalent
  have patterns : first.1 = second.1 := by
    have raw : mapPattern LanguageDefSymbolMap.id first.1 =
        mapPattern LanguageDefSymbolMap.id second.1 := congrArg Subtype.val same
    simpa using raw
  have equal : first = second := Subtype.ext patterns
  rw [equal]
  exact Relation.EqvGen.refl _

/-- The inclusion is hosting: faithfulness and the two operational laws
are established independently. -/
theorem toProbing_hosting : toProbingMorphism.toContextMap.Hosting :=
  ⟨toProbing_faithful, toProbingMorphism.transitions,
    structuralContextMap_reflectsTransitions base toProbing
      (preservesEquations_of_equationFree base toProbing bare_equationFree)
      toProbing_reflectsSteps⟩

/-- The term `Test(A)` of the extended theory. -/
def testOfA : Term probingValidated.language probingProc :=
  (contextTheory base probingValidated).apply testLabel (Term.map toProbing constantA)

/-- **The inclusion is not exhausting**: `Test(A)` is the image of nothing. -/
theorem toProbing_not_exhausting : ¬ toProbingMorphism.toContextMap.Exhausting := by
  intro exhausting
  obtain ⟨preimage, equivalent⟩ := ContextMap.Exhausting.term_surjective _ exhausting
    (origin := proc) testOfA
  have same := (termSetoid_iff_eq base _ probing_equationFree _ _).mp equivalent
  have patterns : testOfA.1 = mapPattern LanguageDefSymbolMap.id preimage.1 :=
    congrArg Subtype.val same
  rw [mapPattern_id, testOfA, apply_testLabel] at patterns
  exact bare_term_ne_test preimage _ patterns.symm

/-- **Hosting and exhausting are independent of being a morphism.**  The
identity has both; the renaming is a morphism with neither; the inclusion is
a hosting morphism that is not exhausting. -/
theorem hosting_exhausting_separated :
    ((ContextMap.id (contextTheory base bareValidated)).Hosting ∧
      (ContextMap.id (contextTheory base bareValidated)).Exhausting) ∧
    (¬ collapseMorphism.toContextMap.Hosting ∧ ¬ collapseMorphism.toContextMap.Exhausting) ∧
    (toProbingMorphism.toContextMap.Hosting ∧ ¬ toProbingMorphism.toContextMap.Exhausting) :=
  ⟨⟨ContextMap.hosting_id _, ContextMap.exhausting_id _⟩,
    ⟨collapse_not_hosting, collapse_not_exhausting⟩,
    ⟨toProbing_hosting, toProbing_not_exhausting⟩⟩

end Mettapedia.GSLT.LanguageDef.Contexts.Controls
