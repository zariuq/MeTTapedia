import Mettapedia.TypeTheory.MaterialSets.Hypersets.DependentProduct
import Mettapedia.GSLT.Topos.ConstructivePresheafDependentFunctions
import Mettapedia.TypeTheory.DisplayedPresheafSlicePi
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Logic.Equiv.Basic

/-!
# Material functions and contextual dependent products

Material function graphs classify dependent functions between member carriers
in one context. A contextual dependent product additionally supplies compatible
values at every argument reached along every contextual restriction. The
explicit dependent-section construction is compared with the existing right
Kan extension by their actual adjunctions, including evaluation.

For a discrete context, evaluation is an equivalence with ordinary dependent
functions; composed with the material function-graph equivalence this gives a
qualified positive comparison. The growing-domain control is nonconstant:
there is an actual current material function, but a newly available argument
has an empty result fibre, so the contextual right-Kan product is empty.
No universal equality of material pointwise products and contextual products
is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.PresheafProducts

open CategoryTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
open Mettapedia.TypeTheory.CategoryIndexedFamilyCwf
open Mettapedia.TypeTheory.CategoryIndexedFamilyGeneralPi

universe u w

variable {C : Type u} [Category.{u} C]

/-- The explicit compatible-section product acts on natural maps of its
dependent codomain; it is not defined to be the right-Kan product. -/
def sectionProductFunctor (domain : C ⥤ Type u) :
    (domain.Elements ⥤ Type u) ⥤ (C ⥤ Type u) where
  obj codomain := dependentFunctions domain codomain
  map transformation := mapFamily transformation
  map_id _codomain := mapFamily_identity
  map_comp first second := mapFamily_compose first second

/-- The explicit future-section carrier satisfies the dependent-product
adjunction with actual restriction along the element projection. -/
def sectionProductAdjunction (domain : C ⥤ Type u) :
    (Functor.whiskeringLeft _ _ (Type u)).obj (CategoryOfElements.π domain) ⊣
      sectionProductFunctor domain :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun parameter codomain => dependentHomEquiv domain codomain parameter
      homEquiv_naturality_left_symm := by
        intro first second codomain earlier later
        ext point parameter
        rfl
      homEquiv_naturality_right := by
        intro parameter first second earlier later
        exact curry_natural_right earlier later }

/-- Both constructions are right adjoint to the same actual restriction
functor, so the explicit section product is naturally the existing Kan
product. This compares independent constructions, not aliases. -/
noncomputable def sectionProductRightKanIso (domain : C ⥤ Type u) :
    sectionProductFunctor domain ≅ (CategoryOfElements.π domain).ran :=
  Adjunction.rightAdjointUniq (sectionProductAdjunction domain)
    ((CategoryOfElements.π domain).ranAdjunction (Type u))

set_option backward.isDefEq.respectTransparency false in
/-- The comparison preserves the evaluation transformation. -/
theorem sectionProductRightKanIso_evaluation (domain : C ⥤ Type u)
    (codomain : domain.Elements ⥤ Type u) :
    Functor.whiskerLeft (CategoryOfElements.π domain)
        ((sectionProductRightKanIso domain).hom.app codomain) ≫
      ((CategoryOfElements.π domain).ranAdjunction (Type u)).counit.app codomain =
        evaluate domain codomain := by
  have counitEq : (sectionProductAdjunction domain).counit.app codomain =
      evaluate domain codomain := by
    ext point parameter
    rfl
  exact (Adjunction.rightAdjointUniq_hom_app_counit
    (sectionProductAdjunction domain)
    ((CategoryOfElements.π domain).ranAdjunction (Type u)) codomain).trans counitEq

/-- At a contextual point, the existing indexed product consists of
compatible dependent sections over all restrictions out of that point. -/
noncomputable def sectionRightKanEquiv (domain : C ⥤ Type u)
    (codomain : domain.Elements ⥤ Type u) (point : C) :
    DependentSection domain codomain point ≃
      (generalPiFamily (context := Cat.of C) domain codomain).obj point :=
  (((sectionProductRightKanIso domain).app codomain).app point).toEquiv

/-- Evaluation at the identity restriction observes only current
arguments. The omitted future data need not be recoverable. -/
def currentFunction (domain : C ⥤ Type u)
    (codomain : domain.Elements ⥤ Type u) (point : C)
    (sectionValue : DependentSection domain codomain point) :
    ∀ argument : domain.obj point, codomain.obj ⟨point, argument⟩ :=
  sectionValue.app point (𝟙 point)

/-- Observe only current arguments of an element of the actual Kan
product. Its compatible future values are left out of this observation. -/
noncomputable def currentRightKanFunction (domain : C ⥤ Type u)
    (codomain : domain.Elements ⥤ Type u) (point : C)
    (function : (generalPiFamily (context := Cat.of C) domain codomain).obj point) :
    ∀ argument : domain.obj point, codomain.obj ⟨point, argument⟩ :=
  currentFunction domain codomain point ((sectionRightKanEquiv domain codomain point).symm function)

private theorem familyMap_heq (domain : C ⥤ Type u)
    (codomain : domain.Elements ⥤ Type u)
    {source target otherTarget : domain.Elements}
    (sameTarget : target = otherTarget)
    (first : source ⟶ target) (second : source ⟶ otherTarget)
    (sameArrow : HEq first.val second.val) (value : codomain.obj source) :
    HEq (codomain.map first value) (codomain.map second value) := by
  cases sameTarget
  have same : first = second := Subtype.ext (eq_of_heq sameArrow)
  cases same
  rfl

private theorem dependentApplication_heq {Index : Type u} {Fibre : Index → Type u}
    (function : ∀ index, Fibre index) {first second : Index} (same : first = second) :
    HEq (function first) (function second) := by
  cases same
  rfl

section DiscreteComparison

variable {World : Type u}
variable (domain : Discrete World ⥤ Type u)
variable (codomain : domain.Elements ⥤ Type u) (point : Discrete World)

set_option backward.isDefEq.respectTransparency false in
/-- In a discrete context there are no additional argument worlds to
serve, so an ordinary dependent function extends to a contextual section. -/
def discreteSection
    (function : ∀ argument : domain.obj point, codomain.obj ⟨point, argument⟩) :
    DependentSection domain codomain point where
  app target restriction argument := by
    have same : point = target := Discrete.ext (Discrete.eq_of_hom restriction)
    cases same
    exact function argument
  naturality {target last} step restriction argument := by
    have firstSame : point = target := Discrete.ext (Discrete.eq_of_hom restriction)
    cases firstSame
    have lastSame : point = last := Discrete.ext (Discrete.eq_of_hom step)
    cases lastSame
    have stepId : step = 𝟙 point := Subsingleton.elim _ _
    have restrictionId : restriction = 𝟙 point := Subsingleton.elim _ _
    cases stepId
    cases restrictionId
    change codomain.map (argumentMap domain (𝟙 point) argument) (function argument) =
      function (domain.map (𝟙 point) argument)
    apply eq_of_heq
    have mapped := familyMap_heq domain codomain
      (congrArg (domain.elementsMk point) (domain.map_id_apply point argument))
      (argumentMap domain (𝟙 point) argument)
      (𝟙 (domain.elementsMk point argument)) (HEq.rfl) (function argument)
    exact (mapped.trans (heq_of_eq (codomain.map_id_apply _ _))).trans
      (dependentApplication_heq function (domain.map_id_apply point argument)).symm

/-- The positive comparison has inverse laws for actual values, including
all contextual arguments, rather than only preservation of inhabitation. -/
def discreteSectionEquiv :
    DependentSection domain codomain point ≃
      (∀ argument : domain.obj point, codomain.obj ⟨point, argument⟩) where
  toFun := currentFunction domain codomain point
  invFun := discreteSection domain codomain point
  left_inv sectionValue := by
    apply DependentSection.ext
    intro target restriction argument
    have same : point = target := Discrete.ext (Discrete.eq_of_hom restriction)
    cases same
    have restrictionId : restriction = 𝟙 point := Subsingleton.elim _ _
    cases restrictionId
    rfl
  right_inv function := by
    funext argument
    rfl

/-- Ordinary dependent functions are exactly the existing Kan product in
the explicitly discrete case. -/
noncomputable def discreteRightKanEquiv :
    (generalPiFamily (context := Cat.of (Discrete World)) domain codomain).obj point ≃
      (∀ argument : domain.obj point, codomain.obj ⟨point, argument⟩) :=
  (sectionRightKanEquiv domain codomain point).symm.trans
    (discreteSectionEquiv domain codomain point)

end DiscreteComparison

/-- Reindexing ordinary sections across an equivalence uses only its
explicit inverse and equality transport. -/
private def piBaseEquiv {Index Target : Type*} (indices : Index ≃ Target)
    (Fibre : Target → Sort*) :
    (∀ index, Fibre (indices index)) ≃ (∀ target, Fibre target) where
  toFun function target :=
    cast (congrArg Fibre (indices.apply_symm_apply target)) (function (indices.symm target))
  invFun function index := function (indices index)
  left_inv function := by
    funext index
    exact eq_of_heq ((cast_heq _ _).trans
      (congr_arg_heq function (indices.symm_apply_apply index)))
  right_inv function := by
    funext target
    exact eq_of_heq ((cast_heq _ _).trans
      (congr_arg_heq function (indices.apply_symm_apply target)))

private def materialSectionCongr {Index Target : Type*}
    {Fibre : Index → Sort*} {TargetFibre : Target → Sort*}
    (indices : Index ≃ Target)
    (fibres : ∀ index, Fibre index ≃ TargetFibre (indices index)) :
    (∀ index, Fibre index) ≃ (∀ target, TargetFibre target) :=
  (Equiv.piCongrRight fibres).trans (piBaseEquiv indices TargetFibre)

/-- When the current carriers are identified with material members and
the context is discrete, contextual Pi is equivalent to members of the
material function-graph product. The presentation parameter is explicit. -/
noncomputable def discreteMaterialProductEquiv
    {World : Type (w + 1)}
    (domain : Discrete World ⥤ Type (w + 1))
    (codomain : domain.Elements ⥤ Type (w + 1)) (point : Discrete World)
    (presentation : HSet.Presentation.{w}) (X : HSet.{w})
    (B : El (· ∈ ·) X → HSet.{w})
    (arguments : domain.obj point ≃ El (· ∈ ·) X)
    (results : ∀ argument : domain.obj point,
      codomain.obj ⟨point, argument⟩ ≃ El (· ∈ ·) (B (arguments argument))) :
    (generalPiFamily (context := Cat.of (Discrete World)) domain codomain).obj point ≃
      El (· ∈ ·) (HSet.dependentProduct presentation X B) :=
  (discreteRightKanEquiv domain codomain point).trans
    ((materialSectionCongr arguments results).trans (HSet.piSetEquiv presentation X B).symm)

/-! ## A growing material domain and a missing future result -/

namespace Controls

/-- Both objects and arrow carriers are in the ambient member universe. -/
abbrev World := ULift.{1} (Fin 2)

def zero : World := ⟨0⟩
def one : World := ⟨1⟩
def step : zero ⟶ one := homOfLE (show zero ≤ one from by decide)

def argumentSets (world : World) : HSet.{0} :=
  if world.down = 0 then {∅} else {∅, {∅}}

theorem argumentSets_stable {source target : World} (arrow : source ⟶ target)
    {member : HSet.{0}} (belongs : member ∈ argumentSets source) :
    member ∈ argumentSets target := by
  have stages := leOfHom arrow
  change source.down.val ≤ target.down.val at stages
  by_cases sourceZero : source.down = 0
  · by_cases targetZero : target.down = 0
    · simpa [argumentSets, sourceZero, targetZero] using belongs
    · have memberEmpty : member = ∅ := HSet.mem_singleton.mp
        (by simpa [argumentSets, sourceZero] using belongs)
      simpa [argumentSets, targetZero] using HSet.mem_insert_iff.mpr (Or.inl memberEmpty)
  · have targetNonzero : target.down ≠ 0 := by
      intro targetZero
      apply sourceZero
      apply Fin.ext
      rw [targetZero] at stages
      change source.down.val ≤ 0 at stages
      exact Nat.eq_zero_of_le_zero stages
    simpa [argumentSets, sourceZero, targetNonzero] using belongs

/-- The actual material member domain grows from one member to two. -/
def arguments : World ⥤ Type 1 where
  obj world := El (· ∈ ·) (argumentSets world)
  map arrow := TypeCat.ofHom fun member =>
    ⟨member.1, argumentSets_stable arrow member.2⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro member
    exact El.ext HSet.propositional rfl
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro member
    exact El.ext HSet.propositional rfl

/-- Result fibres are inhabited exactly at the retained empty member.
Separation expresses this condition without deciding equality of hypersets. -/
def resultSets (point : arguments.Elements) : HSet.{0} :=
  HSet.sep (fun _ => point.2.1 = ∅) {∅}

theorem resultSets_arrow {source target : arguments.Elements} (arrow : source ⟶ target) :
    resultSets source = resultSets target := by
  have sameMember : source.2.1 = target.2.1 := congrArg PSigma.fst arrow.property
  unfold resultSets
  rw [sameMember]

/-- The results form a genuine dependent family: the contextual member
inclusion preserves the relevant member value. -/
def results : arguments.Elements ⥤ Type 1 where
  obj point := El (· ∈ ·) (resultSets point)
  map arrow := TypeCat.ofHom fun member =>
    ⟨member.1, resultSets_arrow arrow ▸ member.2⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro member
    exact El.ext HSet.propositional rfl
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro member
    exact El.ext HSet.propositional rfl

def currentArgument : arguments.obj zero := ⟨∅, HSet.mem_singleton_self ∅⟩

def futureArgument : arguments.obj one :=
  ⟨{∅}, HSet.mem_insert_iff.mpr (Or.inr (HSet.mem_singleton_self {∅}))⟩

/-- A nonvacuous ordinary function exists on all current material members. -/
def pointwiseFunction : ∀ argument : arguments.obj zero, results.obj ⟨zero, argument⟩ :=
  fun argument => ⟨∅, HSet.mem_sep.mpr
    ⟨HSet.mem_singleton_self ∅, HSet.mem_singleton.mp argument.2⟩⟩

theorem current_domain_inhabited : Nonempty (arguments.obj zero) := ⟨currentArgument⟩

theorem current_pointwise_function_exists :
    Nonempty (∀ argument : arguments.obj zero, results.obj ⟨zero, argument⟩) :=
  ⟨pointwiseFunction⟩

theorem future_result_empty : ¬ Nonempty (results.obj ⟨one, futureArgument⟩) := by
  rintro ⟨result⟩
  have impossible : ({∅} : HSet.{0}) = ∅ := (HSet.mem_sep.mp result.2).2
  exact HSet.empty_ne_singleton_empty impossible.symm

theorem no_contextual_section : ¬ Nonempty (DependentSection arguments results zero) := by
  rintro ⟨sectionValue⟩
  exact future_result_empty ⟨sectionValue.app one step futureArgument⟩

/-- The failure holds for the existing right-Kan product, not only the
explicit section representation used to expose the missing future value. -/
theorem no_contextual_rightKan_product :
    ¬ Nonempty (generalPiFamily (context := Cat.of World) arguments results |>.obj zero) := by
  rintro ⟨function⟩
  exact no_contextual_section ⟨(sectionRightKanEquiv arguments results zero).symm function⟩

/-- The actual current-function observation cannot be inverted on this
nonconstant family, even though the current ordinary function is total. -/
theorem current_observation_not_surjective :
    ¬ Function.Surjective (currentRightKanFunction arguments results zero) := by
  intro surjective
  obtain ⟨function, _⟩ := surjective pointwiseFunction
  exact no_contextual_rightKan_product ⟨function⟩

/-- The existing material construction really contains a current
function graph, while its contextual product has no element. -/
theorem material_graph_without_contextual_product (presentation : HSet.Presentation.{0}) :
    Nonempty (El (· ∈ ·)
      (HSet.dependentProduct presentation (argumentSets zero)
        (fun argument => resultSets ⟨zero, argument⟩))) ∧
      ¬ Nonempty (generalPiFamily (context := Cat.of World) arguments results |>.obj zero) := by
  constructor
  · exact ⟨(HSet.piSetEquiv presentation (argumentSets zero)
      (fun argument => resultSets ⟨zero, argument⟩)).symm pointwiseFunction⟩
  · exact no_contextual_rightKan_product

end Controls

#print axioms sectionProductAdjunction
#print axioms sectionProductRightKanIso
#print axioms sectionProductRightKanIso_evaluation
#print axioms discreteSectionEquiv
#print axioms discreteMaterialProductEquiv
#print axioms Controls.arguments
#print axioms Controls.results
#print axioms Controls.no_contextual_section
#print axioms Controls.no_contextual_rightKan_product
#print axioms Controls.current_observation_not_surjective
#print axioms Controls.material_graph_without_contextual_product

end Mettapedia.TypeTheory.MaterialSets.Hypersets.PresheafProducts
