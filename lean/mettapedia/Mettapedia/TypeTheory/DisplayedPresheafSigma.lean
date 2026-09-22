import Mettapedia.TypeTheory.DisplayedPresheafCwfIndexedComparison
import Mettapedia.TypeTheory.CategoryIndexedFamilyTypeFormers
import Mettapedia.TypeTheory.ContextualTypeOperations

/-!
# Dependent sums in the proof-relevant presheaf CwF

The existing category-indexed dependent sum is applied to a displayed
family over a presheaf context. The codomain is moved from the total
presheaf's element category to the equivalent indexed-comprehension
category, retaining its contextual arrows and evidence. This construction
does not add an authored Prime former or judgmental conversion.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafSigma

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafCwf
open Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge
open Mettapedia.TypeTheory.CategoryIndexedFamilyCwf
open Mettapedia.TypeTheory.CategoryIndexedFamilyTypeFormers
open Mettapedia.TypeTheory.ContextualProductComparison
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u

variable {Context : Type u} [Category.{u} Context]

private theorem sections_heq_of_pointwise
    {Index : Type u} [Category.{u} Index]
    {firstFamily secondFamily : Index ⥤ Type u}
    (sameFamily : firstFamily = secondFamily)
    (first : firstFamily.sections) (second : secondFamily.sections)
    (sameValue : ∀ point : Index, HEq (first.val point) (second.val point)) :
    HEq first second := by
  cases sameFamily
  apply heq_of_eq
  apply (Functor.sections_ext_iff).2
  intro point
  exact eq_of_heq (sameValue point)

/-- A dependent sum over one presheaf context retains both the first
evidence and the second evidence depending on it. -/
def sigmaDisplayed
    {base : Face.{u, u, u} Context}
    (domain : DisplayedFamily.{u, u, u, u} base)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)) :
    DisplayedFamily.{u, u, u, u} base :=
  sigmaFamily (context := Cat.of base.Elements) domain
    (displayedToTotalElements domain ⋙ codomain)

/-- The indexed-family substitution lift and the total-presheaf lift agree
under regrouping of dependent evidence, including contextual arrows. -/
theorem indexedLift_totalSquare
    {source target : Face.{u, u, u} Context}
    (substitution : source ⟶ target)
    (domain : DisplayedFamily.{u, u, u, u} target) :
    liftIndexedSubstitution (source := Cat.of source.Elements)
        (target := Cat.of target.Elements) substitution.mapElements domain ⋙
        displayedToTotalElements domain =
      displayedToTotalElements (reindexDisplayed substitution domain) ⋙
        (totalReindexMap substitution domain).mapElements := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro first second arrow
  apply heq_of_eq
  apply CategoryOfElements.ext (totalSpace domain)
  change
    ((displayedToTotalElements domain).map
      ((liftIndexedSubstitution (source := Cat.of source.Elements)
        (target := Cat.of target.Elements) substitution.mapElements domain).map arrow)).val =
    ((totalReindexMap substitution domain).mapElements.map
      ((displayedToTotalElements (reindexDisplayed substitution domain)).map arrow)).val
  erw [displayedToTotalElements_underlying]
  erw [displayedToTotalElements_underlying]
  rfl

/-- Pairing a dependent section with the identity base map gives the same
proof-bearing contextual functor in the indexed and total presentations. -/
theorem sectionLift_indexedSquare
    {base : Face.{u, u, u} Context}
    (domain : DisplayedFamily.{u, u, u, u} base)
    (first : domain.sections) :
    (show base.Elements ⥤ domain.Elements from
      selfExtend categoryIndexedCwf (context := Cat.of base.Elements)
        (type := domain) first) ⋙ displayedToTotalElements domain =
      (sectionLift domain first).mapElements := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro source target arrow
  apply heq_of_eq
  apply CategoryOfElements.ext (totalSpace domain)
  change
    ((displayedToTotalElements domain).map
      ((show base.Elements ⥤ domain.Elements from
        selfExtend categoryIndexedCwf (context := Cat.of base.Elements)
          (type := domain) first).map arrow)).val =
    ((sectionLift domain first).mapElements.map arrow).val
  erw [displayedToTotalElements_underlying]
  rfl

/-- The abstract self-extension substitution of the presheaf CwF is the
already-established natural section lift. -/
theorem selfExtend_eq_sectionLift
    {base : Face.{u, u, u} Context}
    (domain : DisplayedFamily.{u, u, u, u} base)
    (first : domain.sections) :
    selfExtend (Mettapedia.TypeTheory.DisplayedPresheafCwf.presheafCwf Context)
        (context := base) (type := domain) first =
      sectionLift domain first := by
  rfl

/-- Introduce a dependent-sum term from a section of the first family and
a section of the second family pulled back along that first section. -/
def sigmaDisplayedPair
    {base : Face.{u, u, u} Context}
    (domain : DisplayedFamily.{u, u, u, u} base)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain))
    (first : domain.sections)
    (second : (reindexDisplayed (sectionLift domain first) codomain).sections) :
    (sigmaDisplayed domain codomain).sections := by
  have secondFamilyEq :
      reindexFamily (source := Cat.of base.Elements)
          (target := Cat.of domain.Elements)
          (displayedToTotalElements domain ⋙ codomain)
          (show base.Elements ⥤ domain.Elements from
            selfExtend categoryIndexedCwf (context := Cat.of base.Elements)
              (type := domain) first) =
        reindexDisplayed (sectionLift domain first) codomain := by
    change
      ((show base.Elements ⥤ domain.Elements from
          selfExtend categoryIndexedCwf (context := Cat.of base.Elements)
            (type := domain) first) ⋙ displayedToTotalElements domain) ⋙ codomain =
        (sectionLift domain first).mapElements ⋙ codomain
    exact congrArg (fun functor => functor ⋙ codomain)
      (sectionLift_indexedSquare domain first)
  have secondIndexed :
      (reindexFamily (source := Cat.of base.Elements)
        (target := Cat.of domain.Elements)
        (displayedToTotalElements domain ⋙ codomain)
        (show base.Elements ⥤ domain.Elements from
          selfExtend categoryIndexedCwf (context := Cat.of base.Elements)
            (type := domain) first)).sections :=
    secondFamilyEq.symm ▸ second
  exact sigmaPair (context := Cat.of base.Elements) (domain := domain)
    (codomain := displayedToTotalElements domain ⋙ codomain)
    first secondIndexed

/-- At each contextual point, pairing retains both supplied values;
the heterogeneous equality accounts only for regrouping the indexed and
total presentations of the second fibre. -/
theorem sigmaDisplayedPair_value_heq
    {base : Face.{u, u, u} Context}
    (domain : DisplayedFamily.{u, u, u, u} base)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain))
    (first : domain.sections)
    (second : (reindexDisplayed (sectionLift domain first) codomain).sections)
    (point : base.Elements) :
    HEq ((sigmaDisplayedPair domain codomain first second).val point)
      (⟨first.val point, second.val point⟩ :
        (sigmaDisplayed domain codomain).obj point) := by
  apply heq_of_eq
  unfold sigmaDisplayedPair
  simp only [sigmaPair]
  refine Sigma.ext (by rfl) ?_
  exact sectionCast_value_heq _ second point

/-- First projection of a displayed dependent-sum term. -/
def sigmaDisplayedFst
    {base : Face.{u, u, u} Context}
    {domain : DisplayedFamily.{u, u, u, u} base}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)}
    (value : (sigmaDisplayed domain codomain).sections) : domain.sections :=
  sigmaFst (context := Cat.of base.Elements) (domain := domain)
    (codomain := displayedToTotalElements domain ⋙ codomain) value

/-- First-projection beta for an actual dependent pair, without truncating
the first witness. -/
theorem sigmaDisplayedFst_pair
    {base : Face.{u, u, u} Context}
    (domain : DisplayedFamily.{u, u, u, u} base)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain))
    (first : domain.sections)
    (second : (reindexDisplayed (sectionLift domain first) codomain).sections) :
    sigmaDisplayedFst (sigmaDisplayedPair domain codomain first second) = first := by
  apply (Functor.sections_ext_iff).2
  intro point
  rfl

/-- Second projection is still indexed by the first projection, so the
dependency is not erased when a pair is consumed. -/
def sigmaDisplayedSnd
    {base : Face.{u, u, u} Context}
    {domain : DisplayedFamily.{u, u, u, u} base}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)}
    (value : (sigmaDisplayed domain codomain).sections) :
    (reindexDisplayed
      (sectionLift domain (sigmaDisplayedFst value)) codomain).sections := by
  let first := sigmaDisplayedFst value
  have secondFamilyEq :
      reindexFamily (source := Cat.of base.Elements)
          (target := Cat.of domain.Elements)
          (displayedToTotalElements domain ⋙ codomain)
          (show base.Elements ⥤ domain.Elements from
            selfExtend categoryIndexedCwf (context := Cat.of base.Elements)
              (type := domain) first) =
        reindexDisplayed (sectionLift domain first) codomain := by
    change
      ((show base.Elements ⥤ domain.Elements from
          selfExtend categoryIndexedCwf (context := Cat.of base.Elements)
            (type := domain) first) ⋙ displayedToTotalElements domain) ⋙ codomain =
        (sectionLift domain first).mapElements ⋙ codomain
    exact congrArg (fun functor => functor ⋙ codomain)
      (sectionLift_indexedSquare domain first)
  have indexedSecond :
      (reindexFamily (source := Cat.of base.Elements)
          (target := Cat.of domain.Elements)
          (displayedToTotalElements domain ⋙ codomain)
          (show base.Elements ⥤ domain.Elements from
            selfExtend categoryIndexedCwf (context := Cat.of base.Elements)
              (type := domain) first)).sections :=
    sigmaSnd (context := Cat.of base.Elements) (domain := domain)
      (codomain := displayedToTotalElements domain ⋙ codomain) value
  exact secondFamilyEq ▸ indexedSecond

/-- The second projection reads the retained second component at each
contextual point; only the family-presentation cast is heterogeneous. -/
theorem sigmaDisplayedSnd_value_heq
    {base : Face.{u, u, u} Context}
    {domain : DisplayedFamily.{u, u, u, u} base}
    {codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)}
    (value : (sigmaDisplayed domain codomain).sections)
    (point : base.Elements) :
    HEq ((sigmaDisplayedSnd value).val point) ((value.val point).2) := by
  unfold sigmaDisplayedSnd
  simp only [sigmaSnd]
  exact sectionCast_value_heq _ _ point

/-- Second-projection beta retains the dependent witness at every context
point. The statement is heterogeneous because its type depends on the
first projection of the pair. -/
theorem sigmaDisplayedSnd_pair_pointwise
    {base : Face.{u, u, u} Context}
    (domain : DisplayedFamily.{u, u, u, u} base)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain))
    (first : domain.sections)
    (second : (reindexDisplayed (sectionLift domain first) codomain).sections) :
    ∀ point : base.Elements,
      HEq ((sigmaDisplayedSnd
          (sigmaDisplayedPair domain codomain first second)).val point)
        (second.val point) := by
  intro point
  unfold sigmaDisplayedSnd sigmaDisplayedPair
  simp only [sigmaSnd, sigmaPair]
  refine (sectionCast_value_heq _ _ point).trans ?_
  exact sectionCast_value_heq _ second point

/-- Global heterogeneous second-projection beta follows from the
pointwise retained-evidence law and the first-projection beta index. -/
theorem sigmaDisplayedSnd_pair_heq
    {base : Face.{u, u, u} Context}
    (domain : DisplayedFamily.{u, u, u, u} base)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain))
    (first : domain.sections)
    (second : (reindexDisplayed (sectionLift domain first) codomain).sections) :
    HEq (sigmaDisplayedSnd (sigmaDisplayedPair domain codomain first second))
      second := by
  have familyEq :
      reindexDisplayed
          (sectionLift domain
            (sigmaDisplayedFst (sigmaDisplayedPair domain codomain first second)))
          codomain =
        reindexDisplayed (sectionLift domain first) codomain := by
    rw [sigmaDisplayedFst_pair]
  exact sections_heq_of_pointwise familyEq _ _
    (sigmaDisplayedSnd_pair_pointwise domain codomain first second)

/-- Semantic dependent pairs satisfy eta: projecting and immediately
re-pairing an existing proof-relevant section changes no witness. -/
theorem sigmaDisplayed_eta
    {base : Face.{u, u, u} Context}
    (domain : DisplayedFamily.{u, u, u, u} base)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain))
    (value : (sigmaDisplayed domain codomain).sections) :
    sigmaDisplayedPair domain codomain
      (sigmaDisplayedFst value) (sigmaDisplayedSnd value) = value := by
  apply (Functor.sections_ext_iff).2
  intro point
  have paired := sigmaDisplayedPair_value_heq domain codomain
    (sigmaDisplayedFst value) (sigmaDisplayedSnd value) point
  have reconstructed :
      HEq (⟨(sigmaDisplayedFst value).val point,
        (sigmaDisplayedSnd value).val point⟩ :
          (sigmaDisplayed domain codomain).obj point)
        (value.val point) := by
    apply heq_of_eq
    refine Sigma.ext (by rfl) ?_
    exact sigmaDisplayedSnd_value_heq value point
  exact eq_of_heq (paired.trans reconstructed)

/-- Sections of a semantic dependent sum are exactly pairs of a first
section and a second section indexed by that first section. This is an
equivalence of proof-relevant sections, not a quotient or mere existence. -/
def sigmaDisplayedSectionsEquiv
    {base : Face.{u, u, u} Context}
    (domain : DisplayedFamily.{u, u, u, u} base)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)) :
    (Σ first : domain.sections,
      (reindexDisplayed (sectionLift domain first) codomain).sections) ≃
      (sigmaDisplayed domain codomain).sections where
  toFun pair := sigmaDisplayedPair domain codomain pair.1 pair.2
  invFun value := ⟨sigmaDisplayedFst value, sigmaDisplayedSnd value⟩
  left_inv := by
    rintro ⟨first, second⟩
    apply Sigma.ext (sigmaDisplayedFst_pair domain codomain first second)
    exact sigmaDisplayedSnd_pair_heq domain codomain first second
  right_inv := sigmaDisplayed_eta domain codomain

/-- The indexed and total-presheaf presentations of a reindexed dependent
codomain agree as functors, including their action on contextual arrows. -/
theorem sigmaDisplayed_codomainBaseChange
    {source target : Face.{u, u, u} Context}
    (substitution : source ⟶ target)
    (domain : DisplayedFamily.{u, u, u, u} target)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)) :
    liftIndexedSubstitution (source := Cat.of source.Elements)
        (target := Cat.of target.Elements) substitution.mapElements domain ⋙
          (displayedToTotalElements domain ⋙ codomain) =
      displayedToTotalElements (reindexDisplayed substitution domain) ⋙
        ((totalReindexMap substitution domain).mapElements ⋙ codomain) := by
  change
    (liftIndexedSubstitution (source := Cat.of source.Elements)
        (target := Cat.of target.Elements) substitution.mapElements domain ⋙
        displayedToTotalElements domain) ⋙ codomain =
      (displayedToTotalElements (reindexDisplayed substitution domain) ⋙
        (totalReindexMap substitution domain).mapElements) ⋙ codomain
  exact congrArg (fun functor => functor ⋙ codomain)
    (indexedLift_totalSquare substitution domain)

/-- Formation of the displayed dependent sum commutes with arbitrary
natural substitution of presheaf contexts. -/
theorem sigmaDisplayed_reindex
    {source target : Face.{u, u, u} Context}
    (substitution : source ⟶ target)
    (domain : DisplayedFamily.{u, u, u, u} target)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain)) :
    reindexDisplayed substitution (sigmaDisplayed domain codomain) =
      sigmaDisplayed (reindexDisplayed substitution domain)
        (reindexDisplayed (totalReindexMap substitution domain) codomain) := by
  change reindexFamily (source := Cat.of source.Elements)
      (target := Cat.of target.Elements)
      (sigmaFamily (context := Cat.of target.Elements) domain
        (displayedToTotalElements domain ⋙ codomain))
      substitution.mapElements = _
  erw [sigmaFamily_reindex (source := Cat.of source.Elements)
    (target := Cat.of target.Elements) domain
    (displayedToTotalElements domain ⋙ codomain) substitution.mapElements]

  change sigmaFamily (context := Cat.of source.Elements)
      (reindexDisplayed substitution domain)
      (liftIndexedSubstitution (source := Cat.of source.Elements)
        (target := Cat.of target.Elements) substitution.mapElements domain ⋙
          (displayedToTotalElements domain ⋙ codomain)) =
    sigmaFamily (context := Cat.of source.Elements)
      (reindexDisplayed substitution domain)
      (displayedToTotalElements (reindexDisplayed substitution domain) ⋙
        ((totalReindexMap substitution domain).mapElements ⋙ codomain))
  exact congrArg
    (sigmaFamily (context := Cat.of source.Elements)
      (reindexDisplayed substitution domain))
    (sigmaDisplayed_codomainBaseChange substitution domain codomain)

/-- Reindexing a dependent pair preserves its first witness pointwise.
This value-level law needs no choice of a transport for the formation equality. -/
theorem sigmaDisplayedFst_reindex_value
    {source target : Face.{u, u, u} Context}
    (substitution : source ⟶ target)
    (domain : DisplayedFamily.{u, u, u, u} target)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain))
    (value : (sigmaDisplayed domain codomain).sections)
    (point : source.Elements) :
    ((reindexDisplayedSection substitution
        (sigmaDisplayed domain codomain) value).val point).1 =
      (reindexDisplayedSection substitution domain
        (sigmaDisplayedFst value)).val point := by
  rfl

/-- Reindexing an introduced dependent pair retains both witnesses,
including the second witness's dependent family transport. -/
theorem sigmaDisplayedPair_reindex_heq
    {source target : Face.{u, u, u} Context}
    (substitution : source ⟶ target)
    (domain : DisplayedFamily.{u, u, u, u} target)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain))
    (first : domain.sections)
    (second : (reindexDisplayed (sectionLift domain first) codomain).sections) :
    HEq (reindexDisplayedSection substitution (sigmaDisplayed domain codomain)
      (sigmaDisplayedPair domain codomain first second))
      (sigmaDisplayedPair (reindexDisplayed substitution domain)
        (reindexDisplayed (totalReindexMap substitution domain) codomain)
        (reindexDisplayedSection substitution domain first)
        (reindexDependentSection substitution domain codomain first second)) := by
  have familyEq := sigmaDisplayed_reindex substitution domain codomain
  apply sections_heq_of_pointwise familyEq _ _
  intro point
  have leftPair := sigmaDisplayedPair_value_heq domain codomain first second
    (substitution.mapElements.obj point)
  have rightPair := sigmaDisplayedPair_value_heq
    (reindexDisplayed substitution domain)
    (reindexDisplayed (totalReindexMap substitution domain) codomain)
    (reindexDisplayedSection substitution domain first)
    (reindexDependentSection substitution domain codomain first second) point
  have secondValue := reindexDependentSection_value_heq
    substitution domain codomain first second point
  change HEq
    ((sigmaDisplayedPair domain codomain first second).val
      (substitution.mapElements.obj point))
    ((sigmaDisplayedPair (reindexDisplayed substitution domain)
      (reindexDisplayed (totalReindexMap substitution domain) codomain)
      (reindexDisplayedSection substitution domain first)
      (reindexDependentSection substitution domain codomain first second)).val point)
  have middle : HEq
      (⟨first.val (substitution.mapElements.obj point),
        second.val (substitution.mapElements.obj point)⟩ :
        (sigmaDisplayed domain codomain).obj
          (substitution.mapElements.obj point))
      (⟨(reindexDisplayedSection substitution domain first).val point,
        (reindexDependentSection substitution domain codomain first second).val point⟩ :
        (sigmaDisplayed (reindexDisplayed substitution domain)
          (reindexDisplayed (totalReindexMap substitution domain) codomain)).obj point) := by
    cases secondValue
    rfl
  exact leftPair.trans (middle.trans rightPair.symm)

/-- Pair introduction is substitution-stable for any proposed second
witness accompanied by an equality to the canonical transported one. -/
theorem sigmaDisplayedPair_reindex
    {source target : Face.{u, u, u} Context}
    (substitution : source ⟶ target)
    (domain : DisplayedFamily.{u, u, u, u} target)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain))
    (first : domain.sections)
    (second : (reindexDisplayed (sectionLift domain first) codomain).sections)
    (reindexedSecond :
      (reindexDisplayed
        (sectionLift (reindexDisplayed substitution domain)
          (reindexDisplayedSection substitution domain first))
        (reindexDisplayed (totalReindexMap substitution domain) codomain)).sections)
    (sameSecond : HEq (reindexDisplayedSection substitution _ second)
      reindexedSecond) :
    HEq (reindexDisplayedSection substitution (sigmaDisplayed domain codomain)
      (sigmaDisplayedPair domain codomain first second))
      (sigmaDisplayedPair (reindexDisplayed substitution domain)
        (reindexDisplayed (totalReindexMap substitution domain) codomain)
        (reindexDisplayedSection substitution domain first) reindexedSecond) := by
  cases sameSecond
  exact sigmaDisplayedPair_reindex_heq substitution domain codomain first second

/-- The first projection of a reindexed dependent sum commutes with
substitution after the proved formation equality transports its type. -/
theorem sigmaDisplayedFst_reindex
    {source target : Face.{u, u, u} Context}
    (substitution : source ⟶ target)
    (domain : DisplayedFamily.{u, u, u, u} target)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain))
    (value : (sigmaDisplayed domain codomain).sections) :
    sigmaDisplayedFst
      ((sigmaDisplayed_reindex substitution domain codomain) ▸
        reindexDisplayedSection substitution (sigmaDisplayed domain codomain) value) =
      reindexDisplayedSection substitution domain (sigmaDisplayedFst value) := by
  apply (Functor.sections_ext_iff).2
  intro point
  have castValue := sectionCast_value_heq
    (sigmaDisplayed_reindex substitution domain codomain)
    (reindexDisplayedSection substitution (sigmaDisplayed domain codomain) value)
    point
  exact congrArg Sigma.fst (eq_of_heq castValue)

/-- The dependent second projection also survives context substitution.
The heterogeneous equality records its changed first-projection index. -/
theorem sigmaDisplayedSnd_reindex
    {source target : Face.{u, u, u} Context}
    (substitution : source ⟶ target)
    (domain : DisplayedFamily.{u, u, u, u} target)
    (codomain : DisplayedFamily.{u, u, u, u} (totalSpace domain))
    (value : (sigmaDisplayed domain codomain).sections) :
    HEq (sigmaDisplayedSnd
      ((sigmaDisplayed_reindex substitution domain codomain) ▸
        reindexDisplayedSection substitution (sigmaDisplayed domain codomain) value))
      (reindexDisplayedSection substitution _ (sigmaDisplayedSnd value)) := by
  let casted :
      (sigmaDisplayed (reindexDisplayed substitution domain)
        (reindexDisplayed (totalReindexMap substitution domain) codomain)).sections :=
    (sigmaDisplayed_reindex substitution domain codomain) ▸
      reindexDisplayedSection substitution (sigmaDisplayed domain codomain) value
  have firstEq : sigmaDisplayedFst casted =
      reindexDisplayedSection substitution domain (sigmaDisplayedFst value) := by
    exact sigmaDisplayedFst_reindex substitution domain codomain value
  have familyEq :
      reindexDisplayed
          (sectionLift (reindexDisplayed substitution domain)
            (sigmaDisplayedFst casted))
          (reindexDisplayed (totalReindexMap substitution domain) codomain) =
        reindexDisplayed substitution
          (reindexDisplayed (sectionLift domain (sigmaDisplayedFst value)) codomain) := by
    rw [firstEq]
    exact (dependentSectionBaseChangeFamily substitution domain codomain
      (sigmaDisplayedFst value)).symm
  apply sections_heq_of_pointwise familyEq _ _
  intro point
  have castValue := sectionCast_value_heq
    (sigmaDisplayed_reindex substitution domain codomain)
    (reindexDisplayedSection substitution (sigmaDisplayed domain codomain) value)
    point
  have secondCast := (Sigma.mk.inj (eq_of_heq castValue)).2
  have leftValue := sigmaDisplayedSnd_value_heq casted point
  have rightValue := sigmaDisplayedSnd_value_heq value
    (substitution.mapElements.obj point)
  exact leftValue.trans (secondCast.trans rightValue.symm)

/-- The fixed-syntax proof-relevant presheaf CwF carries dependent sums
with both beta laws. Formation is separately proved substitution-stable by
`sigmaDisplayed_reindex`. -/
def presheafDependentSums (Context : Type u) [Category.{u} Context] :
    Mettapedia.TypeTheory.ContextualSumComparison.DependentSumBeta
      (presheafCwf Context) where
  sigma := sigmaDisplayed
  pair first second := sigmaDisplayedPair _ _ first second
  fst value := sigmaDisplayedFst value
  snd value := sigmaDisplayedSnd value
  fst_pair first second := sigmaDisplayedFst_pair _ _ first second
  snd_pair first second := sigmaDisplayedSnd_pair_heq _ _ first second

/-- The same genuine semantic Σ structure inhabits the project's raw
operation interface; its formation-substitution law is a separate theorem. -/
def presheafSigmaOperations (Context : Type u) [Category.{u} Context] :
    SigmaOperations (presheafCwf Context) :=
  SigmaOperations.ofQualified (presheafDependentSums Context)

/-- Strict Σ-formation substitution for the fixed-syntax presheaf CwF. -/
theorem presheafSigmaFormationSubstitution
    (Context : Type u) [Category.{u} Context] :
    StrictSigmaFormationSubstitution (presheafSigmaOperations Context) := by
  intro source target substitution domain codomain
  exact sigmaDisplayed_reindex substitution domain codomain

/-- The proof-relevant presheaf dependent sum satisfies the shared strict
formation, pair-introduction, and both projection substitution laws. -/
theorem presheafDependentSums_strictSubstitution
    (Context : Type u) [Category.{u} Context] :
    StrictSigmaSubstitution (presheafSigmaOperations Context) := by
  refine ⟨?_, ?_, ?_⟩
  · exact presheafSigmaFormationSubstitution Context
  · intro source target substitution domain codomain first second
      reindexedSecond sameSecond
    exact sigmaDisplayedPair_reindex substitution domain codomain first second
      reindexedSecond sameSecond
  · intro source target substitution domain codomain value reindexedValue sameValue
    have familyEq := sigmaDisplayed_reindex substitution domain codomain
    let casted := familyEq ▸ reindexDisplayedSection substitution
      (sigmaDisplayed domain codomain) value
    have castValue : casted = reindexedValue :=
      eq_of_heq (rec_heq_of_heq familyEq sameValue)
    rw [← castValue]
    constructor
    · exact heq_of_eq
        (sigmaDisplayedFst_reindex substitution domain codomain value).symm
    · exact (sigmaDisplayedSnd_reindex substitution domain codomain value).symm

/-- The second Boolean-family component is supported only when the first
evidence agrees with the selected true section. -/
private def boolSelectedCodomain :
    DisplayedFamily.{0, 0, 0, 0} (totalSpace boolFamily) :=
  observationFibreFamily (sectionLift boolFamily boolTrueTerm)

/-- Positive control: the dependent sum contains a true-evidence receipt
with an actual witness of the second, dependent component. -/
def boolSigmaTrueWitness :
    (sigmaDisplayed boolFamily boolSelectedCodomain).obj
      ⟨boolContext, PUnit.unit⟩ :=
  ⟨true, ⟨PUnit.unit, rfl⟩⟩

/-- Negative control: the same dependent sum has no false-evidence branch.
The second component is genuinely indexed by the first. -/
theorem boolSigmaFalseRejected :
    ¬ ∃ receipt : (sigmaDisplayed boolFamily boolSelectedCodomain).obj
        ⟨boolContext, PUnit.unit⟩, receipt.1 = false := by
  rintro ⟨⟨first, ⟨candidate, exactEq⟩⟩, falseEq⟩
  cases candidate
  have evidenceEq : (true : Bool) = first :=
    eq_of_heq (Sigma.mk.inj exactEq).2
  cases falseEq
  exact Bool.noConfusion evidenceEq

#print axioms sigmaDisplayed
#print axioms indexedLift_totalSquare
#print axioms sectionLift_indexedSquare
#print axioms selfExtend_eq_sectionLift
#print axioms sigmaDisplayedPair
#print axioms sigmaDisplayedPair_value_heq
#print axioms sigmaDisplayedFst_pair
#print axioms sigmaDisplayedSnd
#print axioms sigmaDisplayedSnd_value_heq
#print axioms sigmaDisplayedSnd_pair_pointwise
#print axioms sigmaDisplayedSnd_pair_heq
#print axioms sigmaDisplayed_eta
#print axioms sigmaDisplayedSectionsEquiv
#print axioms sigmaDisplayed_codomainBaseChange
#print axioms sigmaDisplayed_reindex
#print axioms sigmaDisplayedFst_reindex_value
#print axioms sigmaDisplayedPair_reindex_heq
#print axioms sigmaDisplayedPair_reindex
#print axioms sigmaDisplayedFst_reindex
#print axioms sigmaDisplayedSnd_reindex
#print axioms presheafDependentSums
#print axioms presheafSigmaFormationSubstitution
#print axioms presheafDependentSums_strictSubstitution
#print axioms boolSigmaTrueWitness
#print axioms boolSigmaFalseRejected

end Mettapedia.TypeTheory.DisplayedPresheafSigma
