import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation
import Mettapedia.OSLF.StructuralModal.SeparatingConjunction
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# The platform's equation theory, and the cut on it

The platform presentation declares a parallel carrier: a bag of processes.  That
one declaration is its whole equation theory, and it is a *declaration* rather
than a list of authored equations — the bag laws are derived from it.

What that buys is item 3 on this presentation.  The cut reads as a separating
conjunction over decompositions modulo the equations, its symmetry comes from
the presentation's own derived permutation law rather than from a hypothesis,
and the structural connective's reading modulo those equations is that
separating conjunction on the nose.

The condition the derived law carries is not dropped here.  A bag is permuted
freely only where the presentation sorts it, so the statements below carry that
sorting judgement exactly as the derived law does.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformEquations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.OSLF.StructuralModal
open Mettapedia.OSLF.StructuralModal.SeparatingConjunction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation

variable (arities : List Nat)

/-! ## The declaration is a carrier -/

/-- **The platform declares a bag carrier.**  Both obligations are discharged by
the presentation as written: the rule is authored, and its single parameter is a
collection of the right kind. -/
theorem parDeclaration_isCarrier :
    CollectionCarrierRule (rhoPlatform arities) parDeclaration .hashBag where
  authored := by simp [rhoPlatform]
  selfSorted := ⟨"parts", .base "Proc", rfl⟩

/-- So the presentation is visibly one that uses bags. -/
theorem platform_usesCollection :
    (rhoPlatform arities).usesCollection .hashBag = true :=
  usesCollection_eq_true_of_collectionCarrierRule (parDeclaration_isCarrier arities)

/-- **And it declares a collection algebra**: the parallel bag flattens, and its
unit is the terminated process.  Every obligation is met by the presentation as
written, so associativity, the singleton law and the unit law below are derived
from one declaration rather than authored one at a time. -/
theorem parDeclaration_isAlgebra :
    AlgebraRule (rhoPlatform arities) parDeclaration .hashBag
      { flatten := true, unit := some stopDeclaration.label } where
  authored := by simp [rhoPlatform]
  declared := rfl
  selfSorted := ⟨"parts", rfl⟩
  unitAuthored := by
    intro unit unitEq
    obtain rfl := Option.some.inj unitEq
    exact ⟨stopDeclaration, by simp [rhoPlatform], rfl, rfl, rfl⟩

/-! ## The laws the declaration derives

Three laws, none authored: associativity as flattening, the singleton law, and
the unit.  Each carries the sorting judgement the derived layer is conditioned
on, and each is instantiated in `Sorted` below. -/

/-- **Associativity**, as the flattening of a nested composition. -/
theorem platform_flatten (base : BasePremiseEvaluator)
    {pre inner post : List Pattern}
    (sorted : SortedAt (rhoPlatform arities)
      (.collection .hashBag (pre ++ (.collection .hashBag inner none) :: post) none)
      parDeclaration.category) :
    EquationEquiv base (rhoPlatform arities)
      (.collection .hashBag (pre ++ (.collection .hashBag inner none) :: post) none)
      (.collection .hashBag (pre ++ inner ++ post) none) :=
  derivedInstance_equivalent
    (DerivedInstance.flatten (parDeclaration_isAlgebra arities) rfl sorted)

/-- **The singleton law.**  A composition of one part is that part — which is
what makes a cut able to reach an element at all. -/
theorem platform_singleton (base : BasePremiseEvaluator) {element : Pattern}
    (sorted : SortedAt (rhoPlatform arities)
      (.collection .hashBag [element] none) parDeclaration.category) :
    EquationEquiv base (rhoPlatform arities)
      (.collection .hashBag [element] none) element :=
  derivedInstance_equivalent
    (DerivedInstance.singleton (parDeclaration_isAlgebra arities) rfl sorted)

/-- **The unit law.**  The empty composition is the terminated process. -/
theorem platform_emptyUnit (base : BasePremiseEvaluator)
    (sorted : SortedAt (rhoPlatform arities)
      (.collection .hashBag [] none) parDeclaration.category) :
    EquationEquiv base (rhoPlatform arities)
      (.collection .hashBag [] none) (.apply stopDeclaration.label []) :=
  derivedInstance_equivalent
    (DerivedInstance.emptyUnit (parDeclaration_isAlgebra arities) rfl sorted)

/-- **And the unit absorbs.**  A terminated process beside others may be
dropped. -/
theorem platform_unitElim (base : BasePremiseEvaluator) {pre post : List Pattern}
    (sorted : SortedAt (rhoPlatform arities)
      (.collection .hashBag (pre ++ (.apply stopDeclaration.label []) :: post) none)
      parDeclaration.category) :
    EquationEquiv base (rhoPlatform arities)
      (.collection .hashBag (pre ++ (.apply stopDeclaration.label []) :: post) none)
      (.collection .hashBag (pre ++ post) none) :=
  derivedInstance_equivalent
    (DerivedInstance.unitElim (parDeclaration_isAlgebra arities) rfl sorted)

/-! ## The derived permutation law -/

/-- The collections the platform sorts at the carrier's category. -/
def sortedParts (elements : List Pattern) : Prop :=
  SortedAt (rhoPlatform arities)
    (.collection .hashBag elements none) parDeclaration.category

/-- **Permutation invariance is derived, not assumed.**  It needs no hypothesis
beyond the carrier declaration the presentation already makes. -/
theorem platform_permInvariantOn (base : BasePremiseEvaluator) :
    PermInvariantOn (EquationEquiv base (rhoPlatform arities)) .hashBag
      (sortedParts arities) :=
  permInvariantOn_of_bagCarrier (parDeclaration_isCarrier arities)

/-! ## Item 3 on this presentation

The cut reads as a separating conjunction over decompositions modulo the
platform's own equations, and it is symmetric on every decomposition the
platform sorts. -/

/-- **The cut of the platform is a separating conjunction.**  Symmetry on every
decomposition the presentation sorts, from the presentation's own derived law. -/
theorem platform_cut_comm (base : BasePremiseEvaluator)
    {left right : Pattern → Prop} {term : Pattern}
    (split : SepConj (EquationEquiv base (rhoPlatform arities)) .hashBag
      left right term)
    (sorted : ∀ leftParts rightParts : List Pattern,
      left (.collection .hashBag leftParts none) →
      right (.collection .hashBag rightParts none) →
      sortedParts arities (leftParts ++ rightParts)) :
    SepConj (EquationEquiv base (rhoPlatform arities)) .hashBag
      right left term :=
  sepConj_comm_of_bagCarrier (parDeclaration_isCarrier arities) split sorted

/-- **And the structural connective's reading modulo those equations is that
separating conjunction**, on the nose.  The connective is the platform's cut and
the separating reading is what the equation layer makes of it; neither is
posited beside the other. -/
theorem platform_satisfiesModuloOver_cut (base : BasePremiseEvaluator)
    (span : Mettapedia.OSLF.Framework.DerivedModalities.ReductionSpan Pattern)
    (leftFormula rightFormula : Formula) (term : Pattern) :
    EquationInvariance.satisfiesModuloOver
        (EquationEquiv base (rhoPlatform arities)) span
        (.cut .hashBag leftFormula rightFormula) term ↔
      SepConj (EquationEquiv base (rhoPlatform arities)) .hashBag
        (EquationInvariance.satisfiesModuloOver
          (EquationEquiv base (rhoPlatform arities)) span leftFormula)
        (EquationInvariance.satisfiesModuloOver
          (EquationEquiv base (rhoPlatform arities)) span rightFormula) term :=
  satisfiesModuloOver_cut _ span .hashBag leftFormula rightFormula term

/-- The empty bag is the cut's unit former on this presentation, and it is a
connective of the structural language rather than a predicate beside it. -/
theorem platform_emptyColl_reading (base : BasePremiseEvaluator)
    (span : Mettapedia.OSLF.Framework.DerivedModalities.ReductionSpan Pattern)
    (term : Pattern) :
    EquationInvariance.satisfiesModuloOver
        (EquationEquiv base (rhoPlatform arities)) span
        (.emptyColl .hashBag) term ↔
      EquationEquiv base (rhoPlatform arities) term
        (.collection .hashBag [] none) :=
  Iff.rfl

/-! ## The sorting judgement, discharged

Everything above carries the condition the derived law is conditioned on.  A
condition carried at every use and met at none is the shape of gap this
development has repaired before, so here is a concrete family that meets it, and
the instances that follow from it. -/

namespace Sorted

open Mettapedia.GSLT.LanguageDef.WellSorted

/-- The presentation these instances are about. -/
abbrev platform : LanguageDef := rhoPlatform [2]

/-- The terminated process. -/
def stop : Pattern := .apply stopDeclaration.label []

/-- A name: the terminated process, quoted. -/
def quotedStop : Pattern := .apply quoteDeclaration.label [stop]

/-- An output on that name. -/
def output : Pattern := .apply outLabel [quotedStop, stop]

/-- A concrete parallel composition of two processes. -/
def parts : List Pattern := [stop, output]

/-- The same composition, written the other way round. -/
def swapped : List Pattern := [output, stop]

/-- **The family is sorted**, by the presentation's own declarations: the bare
bag takes the parallel carrier's category because each of its elements is a
process the presentation declares. -/
theorem parts_sorted : sortedParts [2] parts :=
  ⟨FreeTypeContext.empty, [],
    (checkHasType_eq_true_iff (by decide)).mp (by decide +kernel)⟩

/-- And so is its reordering. -/
theorem swapped_sorted : sortedParts [2] swapped :=
  ⟨FreeTypeContext.empty, [],
    (checkHasType_eq_true_iff (by decide)).mp (by decide +kernel)⟩

/-- The two orders are a permutation of each other. -/
theorem parts_perm : List.Perm parts swapped :=
  List.Perm.swap output stop []

/-- **The derived law, instantiated.**  Two presentations of one parallel
composition are equated by the platform's own equations — no hypothesis left
standing. -/
theorem parts_equated (base : BasePremiseEvaluator) :
    EquationEquiv base platform
      (.collection .hashBag parts none) (.collection .hashBag swapped none) :=
  platform_permInvariantOn [2] base parts_sorted parts_perm

/-! ### The algebra laws, instantiated

The laws above carry the sorting judgement.  Here they are met. -/

/-- The singleton composition of the terminated process is sorted. -/
theorem stop_sorted : sortedParts [2] [stop] :=
  ⟨FreeTypeContext.empty, [],
    (checkHasType_eq_true_iff (by decide)).mp (by decide +kernel)⟩

/-- So is the singleton composition of the output. -/
theorem output_sorted : sortedParts [2] [output] :=
  ⟨FreeTypeContext.empty, [],
    (checkHasType_eq_true_iff (by decide)).mp (by decide +kernel)⟩

/-- And so is the empty composition. -/
theorem empty_sorted : sortedParts [2] [] :=
  ⟨FreeTypeContext.empty, [],
    (checkHasType_eq_true_iff (by decide)).mp (by decide +kernel)⟩

/-- **The singleton law, met.** -/
theorem singleton_law (base : BasePremiseEvaluator) :
    EquationEquiv base platform (.collection .hashBag [output] none) output :=
  platform_singleton [2] base output_sorted

/-- **The unit law, met**: the empty composition is the terminated process. -/
theorem empty_is_stop (base : BasePremiseEvaluator) :
    EquationEquiv base platform (.collection .hashBag [] none)
      (.apply stopDeclaration.label []) :=
  platform_emptyUnit [2] base empty_sorted

/-- **The unit absorbs, met**: a terminated process beside an output drops
away. -/
theorem stop_absorbs (base : BasePremiseEvaluator) :
    EquationEquiv base platform (.collection .hashBag parts none)
      (.collection .hashBag [output] none) :=
  platform_unitElim [2] base (pre := []) (post := [output]) parts_sorted

/-- **And the two compose**: the parallel composition of a terminated process
and an output *is* that output.  Nothing here is authored; every step is a law
the single algebra declaration derives. -/
theorem parts_equiv_output (base : BasePremiseEvaluator) :
    EquationEquiv base platform (.collection .hashBag parts none) output :=
  Relation.EqvGen.trans _ _ _ (stop_absorbs base) (singleton_law base)

/-! ### The cut's symmetry, instantiated -/

/-- "Is the singleton composition of the terminated process." -/
def isStopPart (term : Pattern) : Prop := term = .collection .hashBag [stop] none

/-- "Is the singleton composition of the output." -/
def isOutputPart (term : Pattern) : Prop := term = .collection .hashBag [output] none

/-- The composition splits into those two parts, positionally and so also
separatingly. -/
theorem splits (base : BasePremiseEvaluator) :
    SepConj (EquationEquiv base platform) .hashBag isStopPart isOutputPart
      (.collection .hashBag parts none) :=
  ⟨[stop], [output], Relation.EqvGen.refl _, rfl, rfl⟩

/-- **The cut is symmetric here, with nothing assumed.**  The sorting condition
the derived law carries is discharged by `parts_sorted`, so this is an instance
of the separating conjunction on the platform rather than a statement about one. -/
theorem splits_comm (base : BasePremiseEvaluator) :
    SepConj (EquationEquiv base platform) .hashBag isOutputPart isStopPart
      (.collection .hashBag parts none) := by
  refine platform_cut_comm [2] base (splits base) ?_
  intro leftParts rightParts leftHolds rightHolds
  simp only [isStopPart, Pattern.collection.injEq] at leftHolds
  simp only [isOutputPart, Pattern.collection.injEq] at rightHolds
  obtain ⟨-, leftList, -⟩ := leftHolds
  obtain ⟨-, rightList, -⟩ := rightHolds
  subst leftList; subst rightList
  exact parts_sorted

end Sorted

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformEquations
