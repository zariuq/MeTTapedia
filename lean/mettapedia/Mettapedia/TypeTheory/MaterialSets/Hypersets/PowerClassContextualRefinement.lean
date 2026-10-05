import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafDescent

/-!
# Exact contextual section refinement

A finer observer identifies fewer source states. A material family with
authored contextual action descending through the coarser observer also
descends through the finer one. Both displayed families are independently
decoded from their complete observation fibres.

The constructed map on natural sections retains their actual source values.
Its image consists exactly of the finer sections whose pulled source terms
are compatible with the coarser observer. Successive refinements agree on
whole natural sections. No observation representative or intermediate state
is selected, and no approximate distance is used as dependent transport.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassContextualRefinement

open CategoryTheory AccessiblePointedGraph
open PowerClassFamilyDescent PowerClassPresheafDescent

universe u

variable {C : Type u} [Category.{u} C]
variable (source fineTarget coarseTarget : Cᵒᵖ ⥤ Type u)
variable (fine : NatTrans source fineTarget) (coarse : NatTrans source coarseTarget)

/-- Kernel inclusion is the exact premise for forgetting observation data.
It does not claim that a map on every unauthored target value is available. -/
def KernelRefinement : Prop :=
  ∀ X ⦃left right : source.obj X⦄,
    fine.app X left = fine.app X right → coarse.app X left = coarse.app X right

theorem kernelRefinement_refl : KernelRefinement source fineTarget fineTarget fine fine :=
  fun _ _ _ same => same

theorem kernelRefinement_of_square (coarsen : NatTrans fineTarget coarseTarget)
    (square : ∀ X value, coarse.app X value = coarsen.app X (fine.app X value)) :
    KernelRefinement source fineTarget coarseTarget fine coarse := by
  intro X left right same
  exact (square X left).trans ((congrArg (coarsen.app X) same).trans (square X right).symm)

variable (refines : KernelRefinement source fineTarget coarseTarget fine coarse)

/-- Complete a fine fibre to its full coarse fibre. All fine sources are
retained in the predicate construction; existential witnesses stay in Prop. -/
def coarsenClass (X : Cᵒᵖ) (observed : ObservationClass (fine.app X)) :
    ObservationClass (coarse.app X) :=
  ⟨{other | ∃ witness, witness ∈ observed.1 ∧ coarse.app X other = coarse.app X witness}, by
    obtain ⟨value, same⟩ := observed.2
    refine ⟨value, ?_⟩
    funext other
    apply propext
    constructor
    · rintro ⟨witness, belongs, related⟩
      have fineSame : fine.app X witness = fine.app X value := by
        rw [same] at belongs
        exact belongs
      exact related.trans (refines X fineSame)
    · intro related
      exact ⟨value, by rw [same]; rfl, related⟩⟩

theorem coarsenClass_beta (X : Cᵒᵖ) (value : source.obj X) :
    coarsenClass source fineTarget coarseTarget fine coarse refines X (classOf (fine.app X) value) =
      classOf (coarse.app X) value := by
  apply Subtype.ext
  funext other
  apply propext
  constructor
  · rintro ⟨witness, same, related⟩
    exact related.trans (refines X same)
  · intro related
    exact ⟨value, rfl, related⟩

/-- The completed observation fibres commute with every authored context. -/
def classCoarsening : NatTrans (classFace source fineTarget fine)
    (classFace source coarseTarget coarse) where
  app X := TypeCat.ofHom (coarsenClass source fineTarget coarseTarget fine coarse refines X)
  naturality X Y step := by
    apply ConcreteCategory.hom_ext
    intro observed
    obtain ⟨value, rfl⟩ := classOf_surjective (fine.app X) observed
    change coarsenClass source fineTarget coarseTarget fine coarse refines Y
        ((classFace source fineTarget fine).map step (classOf (fine.app X) value)) =
      (classFace source coarseTarget coarse).map step
        (coarsenClass source fineTarget coarseTarget fine coarse refines X
          (classOf (fine.app X) value))
    rw [classFace_map_class, coarsenClass_beta, coarsenClass_beta, classFace_map_class]

variable (graphs : source.Elements → AccessiblePointedGraph.{u})
variable (transport : MaterialTransport source coarseTarget coarse graphs)

/-- Construct the finer material transport from the same authored source
action, with its family and member compatibility derived by kernel inclusion. -/
def refineTransport : MaterialTransport source fineTarget fine graphs where
  invariant X := fun _ _ same => transport.invariant X (refines X same)
  map := transport.map
  map_id_value := transport.map_id_value
  map_comp_value := transport.map_comp_value
  compatible step := fun _ _ same first second sameValue =>
    transport.compatible step (refines _ same) first second sameValue

theorem compatible_refinement (term : RawSection source graphs)
    (compatible : ContextualCompatible source coarseTarget coarse graphs transport term) :
    ContextualCompatible source fineTarget fine graphs
      (refineTransport source fineTarget coarseTarget fine coarse refines graphs transport) term :=
  ⟨fun X _ _ same => compatible.1 X (refines X same), compatible.2⟩

include transport in
/-- The two independently constructed complete-fibre decoders agree along
the actual contextual coarsening, not merely on their positive support. -/
theorem family_coarsening (X : Cᵒᵖ) (observed : ObservationClass (fine.app X)) :
    decodedFamily (fun value => graphs ⟨X, value⟩) observed =
      decodedFamily (fun value => graphs ⟨X, value⟩)
        ((classCoarsening source fineTarget coarseTarget fine coarse refines).app X observed) := by
  obtain ⟨value, rfl⟩ := classOf_surjective (fine.app X) observed
  change decodedFamily (fun value => graphs ⟨X, value⟩) (classOf (fine.app X) value) =
    decodedFamily (fun value => graphs ⟨X, value⟩)
      (coarsenClass source fineTarget coarseTarget fine coarse refines X (classOf (fine.app X) value))
  rw [coarsenClass_beta]
  exact (family_beta (fine.app X) (fun value => graphs ⟨X, value⟩)
    ((refineTransport source fineTarget coarseTarget fine coarse refines graphs transport).invariant X)
    value).trans (family_beta (coarse.app X) (fun value => graphs ⟨X, value⟩)
      (transport.invariant X) value).symm

/-- Refine a genuine natural section by pulling its material values to the
authored source and decoding them through the finer complete fibres. -/
def refineSection
    (term : (observedDisplayed source coarseTarget coarse graphs transport).sections) :
    (observedDisplayed source fineTarget fine graphs
      (refineTransport source fineTarget coarseTarget fine coarse refines graphs transport)).sections :=
  descendContextualSection source fineTarget fine graphs
    (refineTransport source fineTarget coarseTarget fine coarse refines graphs transport)
    (pullContextualSection source coarseTarget coarse graphs transport term)
    (compatible_refinement source fineTarget coarseTarget fine coarse refines graphs transport _
      (pullContextualSection_compatible source coarseTarget coarse graphs transport term))

theorem pull_refineSection
    (term : (observedDisplayed source coarseTarget coarse graphs transport).sections) :
    pullContextualSection source fineTarget fine graphs
        (refineTransport source fineTarget coarseTarget fine coarse refines graphs transport)
        (refineSection source fineTarget coarseTarget fine coarse refines graphs transport term) =
      pullContextualSection source coarseTarget coarse graphs transport term :=
  pull_descendContextualSection source fineTarget fine graphs
    (refineTransport source fineTarget coarseTarget fine coarse refines graphs transport) _ _

theorem pullContextualSection_injective :
    Function.Injective (pullContextualSection source coarseTarget coarse graphs transport) := by
  intro first second same
  exact (contextualSectionEquiv source coarseTarget coarse graphs transport).injective (Subtype.ext same)

theorem refineSection_injective :
    Function.Injective (refineSection source fineTarget coarseTarget fine coarse refines graphs transport) := by
  intro first second same
  apply pullContextualSection_injective source coarseTarget coarse graphs transport
  exact (pull_refineSection source fineTarget coarseTarget fine coarse refines graphs transport first).symm.trans
    ((congrArg (pullContextualSection source fineTarget fine graphs
      (refineTransport source fineTarget coarseTarget fine coarse refines graphs transport)) same).trans
        (pull_refineSection source fineTarget coarseTarget fine coarse refines graphs transport second))

/-- Exact range criterion: a fine section admits coarse descent precisely
when its whole pulled term, including contextual action, is coarse-compatible. -/
def CoarseCompatibleSection
    (term : (observedDisplayed source fineTarget fine graphs
      (refineTransport source fineTarget coarseTarget fine coarse refines graphs transport)).sections) : Prop :=
  ContextualCompatible source coarseTarget coarse graphs transport
    (pullContextualSection source fineTarget fine graphs
      (refineTransport source fineTarget coarseTarget fine coarse refines graphs transport) term)

theorem coarseCompatible_refineSection
    (term : (observedDisplayed source coarseTarget coarse graphs transport).sections) :
    CoarseCompatibleSection source fineTarget coarseTarget fine coarse refines graphs transport
      (refineSection source fineTarget coarseTarget fine coarse refines graphs transport term) := by
  unfold CoarseCompatibleSection
  rw [pull_refineSection]
  exact pullContextualSection_compatible source coarseTarget coarse graphs transport term

/-- A natural fine section already satisfies the authored contextual law.
The additional coarsening obligation is exactly its selected-value kernel law. -/
theorem coarseCompatible_iff_termCompatible
    (term : (observedDisplayed source fineTarget fine graphs
      (refineTransport source fineTarget coarseTarget fine coarse refines graphs transport)).sections) :
    CoarseCompatibleSection source fineTarget coarseTarget fine coarse refines graphs transport term ↔
      ∀ X, TermCompatible (coarse.app X) (fun value => graphs ⟨X, value⟩)
        (fun value => pullContextualSection source fineTarget fine graphs
          (refineTransport source fineTarget coarseTarget fine coarse refines graphs transport) term ⟨X, value⟩) := by
  constructor
  · exact And.left
  · intro compatible
    exact ⟨compatible, (pullContextualSection_compatible source fineTarget fine graphs
      (refineTransport source fineTarget coarseTarget fine coarse refines graphs transport) term).2⟩

/-- The complete material value read by the refined natural section agrees
at every fine class with the coarse section at its completed coarse class. -/
theorem refineSection_value
    (term : (observedDisplayed source coarseTarget coarse graphs transport).sections)
    (X : Cᵒᵖ) (observed : ObservationClass (fine.app X)) :
    (contextualMemberEquiv source fineTarget fine graphs ⟨X, observed⟩
      ((refineSection source fineTarget coarseTarget fine coarse refines graphs transport term).val
        ⟨X, observed⟩)).1 =
      (contextualMemberEquiv source coarseTarget coarse graphs
        ⟨X, (classCoarsening source fineTarget coarseTarget fine coarse refines).app X observed⟩
        (term.val ⟨X, (classCoarsening source fineTarget coarseTarget fine coarse refines).app X observed⟩)).1 := by
  obtain ⟨value, rfl⟩ := classOf_surjective (fine.app X) observed
  change _ = (contextualMemberEquiv source coarseTarget coarse graphs
    ⟨X, coarsenClass source fineTarget coarseTarget fine coarse refines X (classOf (fine.app X) value)⟩
    (term.val ⟨X, coarsenClass source fineTarget coarseTarget fine coarse refines X
      (classOf (fine.app X) value)⟩)).1
  rw [coarsenClass_beta]
  have sourceValues := congrArg (fun raw => (raw ⟨X, value⟩).1)
    (pull_refineSection source fineTarget coarseTarget fine coarse refines graphs transport term)
  exact (pullContextualSection_value source fineTarget fine graphs
    (refineTransport source fineTarget coarseTarget fine coarse refines graphs transport)
    (refineSection source fineTarget coarseTarget fine coarse refines graphs transport term) ⟨X, value⟩).symm.trans
    (sourceValues.trans (pullContextualSection_value source coarseTarget coarse graphs transport term ⟨X, value⟩))

/-- A bijection of actual natural sections, with the selected-value condition
on the finer side. It does not assert that every fine section can be coarsened. -/
def sectionRefinementEquiv :
    (observedDisplayed source coarseTarget coarse graphs transport).sections ≃
      {term : (observedDisplayed source fineTarget fine graphs
        (refineTransport source fineTarget coarseTarget fine coarse refines graphs transport)).sections //
        CoarseCompatibleSection source fineTarget coarseTarget fine coarse refines graphs transport term} where
  toFun term := ⟨refineSection source fineTarget coarseTarget fine coarse refines graphs transport term,
    coarseCompatible_refineSection source fineTarget coarseTarget fine coarse refines graphs transport term⟩
  invFun term := descendContextualSection source coarseTarget coarse graphs transport
    (pullContextualSection source fineTarget fine graphs
      (refineTransport source fineTarget coarseTarget fine coarse refines graphs transport) term.1) term.2
  left_inv term := by
    change descendContextualSection source coarseTarget coarse graphs transport
      (pullContextualSection source fineTarget fine graphs
        (refineTransport source fineTarget coarseTarget fine coarse refines graphs transport)
        (refineSection source fineTarget coarseTarget fine coarse refines graphs transport term)) _ = term
    simp only [pull_refineSection]
    exact descend_pullContextualSection source coarseTarget coarse graphs transport term
  right_inv term := by
    apply Subtype.ext
    apply pullContextualSection_injective source fineTarget fine graphs
      (refineTransport source fineTarget coarseTarget fine coarse refines graphs transport)
    exact (pull_refineSection source fineTarget coarseTarget fine coarse refines graphs transport _).trans
      (pull_descendContextualSection source coarseTarget coarse graphs transport _ term.2)

theorem coarseCompatible_iff_in_range
    (term : (observedDisplayed source fineTarget fine graphs
      (refineTransport source fineTarget coarseTarget fine coarse refines graphs transport)).sections) :
    CoarseCompatibleSection source fineTarget coarseTarget fine coarse refines graphs transport term ↔
      ∃ coarseTerm, refineSection source fineTarget coarseTarget fine coarse refines graphs transport coarseTerm = term := by
  constructor
  · intro compatible
    let equivalence := sectionRefinementEquiv source fineTarget coarseTarget fine coarse refines graphs transport
    exact ⟨equivalence.symm ⟨term, compatible⟩,
      congrArg Subtype.val (equivalence.apply_symm_apply ⟨term, compatible⟩)⟩
  · rintro ⟨coarseTerm, rfl⟩
    exact coarseCompatible_refineSection source fineTarget coarseTarget fine coarse refines graphs transport coarseTerm

section Composition

variable (middleTarget : Cᵒᵖ ⥤ Type u) (middle : NatTrans source middleTarget)
variable (earlier : KernelRefinement source fineTarget middleTarget fine middle)
variable (later : KernelRefinement source middleTarget coarseTarget middle coarse)

include earlier later in
theorem kernelRefinement_comp :
    KernelRefinement source fineTarget coarseTarget fine coarse :=
  fun X _ _ same => later X (earlier X same)

/-- Complete fibres coarsen in stages exactly as they do in one step. -/
theorem coarsenClass_comp (X : Cᵒᵖ) (observed : ObservationClass (fine.app X)) :
    coarsenClass source middleTarget coarseTarget middle coarse later X
        (coarsenClass source fineTarget middleTarget fine middle earlier X observed) =
      coarsenClass source fineTarget coarseTarget fine coarse
        (kernelRefinement_comp source fineTarget coarseTarget fine coarse middleTarget middle earlier later)
        X observed := by
  obtain ⟨value, rfl⟩ := classOf_surjective (fine.app X) observed
  rw [coarsenClass_beta, coarsenClass_beta, coarsenClass_beta]

/-- The complete material source action is the same in staged and direct
refinement. Only the proved observation compatibility changes. -/
theorem refineTransport_comp :
    refineTransport source fineTarget middleTarget fine middle earlier graphs
        (refineTransport source middleTarget coarseTarget middle coarse later graphs transport) =
      refineTransport source fineTarget coarseTarget fine coarse
        (kernelRefinement_comp source fineTarget coarseTarget fine coarse middleTarget middle earlier later)
        graphs transport := rfl

/-- Equality of whole natural sections follows from their actual source
decoders and the proved inverse laws, not only equality of present supports. -/
theorem refineSection_comp
    (term : (observedDisplayed source coarseTarget coarse graphs transport).sections) :
    refineSection source fineTarget middleTarget fine middle earlier graphs
        (refineTransport source middleTarget coarseTarget middle coarse later graphs transport)
        (refineSection source middleTarget coarseTarget middle coarse later graphs transport term) =
      refineSection source fineTarget coarseTarget fine coarse
        (kernelRefinement_comp source fineTarget coarseTarget fine coarse middleTarget middle earlier later)
        graphs transport term := by
  apply pullContextualSection_injective source fineTarget fine graphs
    (refineTransport source fineTarget coarseTarget fine coarse
      (kernelRefinement_comp source fineTarget coarseTarget fine coarse middleTarget middle earlier later)
      graphs transport)
  exact (pull_refineSection source fineTarget middleTarget fine middle earlier graphs
    (refineTransport source middleTarget coarseTarget middle coarse later graphs transport) _).trans
    ((pull_refineSection source middleTarget coarseTarget middle coarse later graphs transport term).trans
      (pull_refineSection source fineTarget coarseTarget fine coarse
        (kernelRefinement_comp source fineTarget coarseTarget fine coarse middleTarget middle earlier later)
        graphs transport term).symm)

end Composition

theorem coarsenClass_identity (X : Cᵒᵖ) (observed : ObservationClass (coarse.app X)) :
    coarsenClass source coarseTarget coarseTarget coarse coarse
      (kernelRefinement_refl source coarseTarget coarse) X observed = observed := by
  obtain ⟨value, rfl⟩ := classOf_surjective (coarse.app X) observed
  exact coarsenClass_beta source coarseTarget coarseTarget coarse coarse
    (kernelRefinement_refl source coarseTarget coarse) X value

theorem refineSection_identity
    (term : (observedDisplayed source coarseTarget coarse graphs transport).sections) :
    refineSection source coarseTarget coarseTarget coarse coarse
      (kernelRefinement_refl source coarseTarget coarse) graphs transport term = term :=
  descend_pullContextualSection source coarseTarget coarse graphs transport term

end Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassContextualRefinement
