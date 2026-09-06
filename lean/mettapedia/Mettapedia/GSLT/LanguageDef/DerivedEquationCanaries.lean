import Mettapedia.GSLT.LanguageDef.EquationSemantics

/-!
# Canaries for presentation-derived equations

Two minimal presentations discriminate the derived laws.

* `bagLanguage` declares one bare bag constructor over its own sort.  Its
  generated equation theory permutes bag elements, so two bags that differ
  only in element order are equivalent while their multiplicities are
  retained.
* `vecLanguage` declares the same constructor over a vector.  It is equation
  free, so its generated theory is syntactic equality, and reordering a vector
  is not an equation.

The rho presentation is the live instance: it declares a bag, it declares the
parallel algebra, and it is therefore not equation free.
-/

namespace Mettapedia.GSLT.LanguageDef.DerivedEquationCanaries

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.EquationSemantics

/-- The two ordinary constructors and the one bare bag carrier used below. -/
def atomARule : GrammarRule :=
  { label := "A", category := "T", params := [], syntaxPattern := [] }

def atomBRule : GrammarRule :=
  { label := "B", category := "T", params := [], syntaxPattern := [] }

def bagRule : GrammarRule :=
  { label := "Bag", category := "T",
    params := [.simple "xs" (.collection .hashBag (.base "T"))],
    syntaxPattern := [] }

/-- One sort, one nullary atom, one bare bag constructor over the sort. -/
def bagLanguage : LanguageDef :=
  { name := "BagCanary"
    types := [TypeDecl.plain "T"]
    terms := [atomARule, atomBRule, bagRule]
    equations := []
    rewrites := [] }

/-- The same presentation with an ordered vector in place of the bag. -/
def vecLanguage : LanguageDef :=
  { name := "VecCanary"
    types := [TypeDecl.plain "T"]
    terms :=
      [ { label := "A", category := "T", params := [], syntaxPattern := [] },
        { label := "B", category := "T", params := [], syntaxPattern := [] },
        { label := "Seq", category := "T",
          params := [.simple "xs" (.collection .vec (.base "T"))],
          syntaxPattern := [] } ]
    equations := []
    rewrites := [] }

def atomA : Pattern := .apply "A" []
def atomB : Pattern := .apply "B" []

theorem bagLanguage_usesBags : bagLanguage.usesCollection .hashBag = true := by
  decide

theorem bagLanguage_carrier :
    CollectionCarrierRule bagLanguage bagRule .hashBag where
  authored := by simp [bagLanguage]
  selfSorted := ⟨"xs", .base "T", rfl⟩

theorem bagLanguage_example_sorted :
    SortedAt bagLanguage
      (.collection .hashBag [atomA, atomB] none) "T" := by
  refine ⟨WellSorted.FreeTypeContext.empty, [], ?_⟩
  apply WellSorted.HasType.collectionConstructor
      (rule := bagRule) (parameterName := "xs")
      (elementType := .base "T")
  · simp [bagLanguage]
  · rfl
  · apply WellSorted.ElementsHaveType.cons
    · exact WellSorted.HasType.constructor
        (rule := atomARule) (by simp [bagLanguage])
        (by simp [WellSorted.UsesBareCollection, atomARule])
        WellSorted.ArgumentsHaveTypes.nil
    · apply WellSorted.ElementsHaveType.cons
      · exact WellSorted.HasType.constructor
          (rule := atomBRule) (by simp [bagLanguage])
          (by simp [WellSorted.UsesBareCollection, atomBRule])
          WellSorted.ArgumentsHaveTypes.nil
      · exact WellSorted.ElementsHaveType.nil [] (.base "T")

theorem bagLanguage_not_equationFree : bagLanguage.isEquationFree = false := by
  decide

theorem vecLanguage_equationFree : vecLanguage.isEquationFree = true := by
  decide

/-- Positive: reordering a bag is an equation of the bag presentation. -/
theorem bag_reorder_equivalent (base : BasePremiseEvaluator) :
    EquationEquiv base bagLanguage
      (.collection .hashBag [atomA, atomB] none)
      (.collection .hashBag [atomB, atomA] none) :=
  equationEquiv_bag_perm bagLanguage_carrier bagLanguage_example_sorted
    (List.Perm.swap atomB atomA [])

/-- Negative: an open bag tail is a schema pattern, not a carrier value, and
therefore cannot trigger a derived equation. -/
theorem bag_open_tail_has_no_derived_step (target : Pattern) :
    ¬ DerivedInstance bagLanguage
      (.collection .hashBag [atomA] (some "rest")) target :=
  no_derivedInstance_of_open_collection_source _ _ _ _ _

/-- Negative: reordering a vector is not an equation of the vector
presentation.  That presentation is equation free, so its generated theory is
syntactic equality, and the two vectors differ. -/
theorem vec_reorder_not_equivalent (base : BasePremiseEvaluator) :
    ¬ EquationEquiv base vecLanguage
      (.collection .vec [atomA, atomB] none)
      (.collection .vec [atomB, atomA] none) := by
  intro equivalent
  have equal :=
    (equationEquiv_iff_eq_of_no_generators vecLanguage_equationFree _ _).mp
      equivalent
  simp [atomA, atomB] at equal

/-- The vector presentation's saturated step is its authored step. -/
theorem vecLanguage_saturated_iff_step (base : BasePremiseEvaluator)
    (source target : Pattern) :
    StepModuloEquations base vecLanguage source target ↔
      Step base vecLanguage source target :=
  stepModuloEquations_iff_step_of_no_generators vecLanguage_equationFree
    source target

/-! ## The live rho presentation -/

theorem rhoCalc_usesBags : rhoCalc.usesCollection .hashBag = true := by
  decide

theorem rhoCalc_no_sets : rhoCalc.usesCollection .hashSet = false := by
  decide

theorem rhoCalc_declaresAlgebra : rhoCalc.hasAlgebraDeclarations = true := by
  decide

theorem rhoCalc_not_equationFree : rhoCalc.isEquationFree = false := by
  decide

end Mettapedia.GSLT.LanguageDef.DerivedEquationCanaries
