import Mettapedia.TypeTheory.MaterialSets.Hypersets.BoundedProductBeckChevalley
import Mettapedia.TypeTheory.MaterialSets.Hypersets.NaturalOrdinalModel

/-!
# Infinite, empty, cyclic and bound-sensitive material product controls

The infinite example uses the independently constructed material natural set,
with genuinely varying fibres `{∅,a}` bounded by that same set. Both an empty
constant section and the diagonal section have constructed material graphs,
and those graphs are distinguished at the material ordinal one. No host
natural-number decoder or decision of arbitrary hyperset equality is used.

Other controls retain self-membered values, exclude an empty fibre, and show
that omitting the common-bound proof can really lose all sections. The
pullback control distinguishes corresponding freshly labelled function
graphs despite their proved Beck--Chevalley equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.BoundedProductControls

universe u

open HSet BoundedDependentProducts

theorem product_empty_domain (B : Element (∅ : HSet.{u}) → HSet.{u}) (Y : HSet.{u}) :
    product ∅ B Y = {∅} := by
  have bounded : ∀ a : Element (∅ : HSet.{u}), B a ⊆ Y :=
    fun a => (notMem_empty a.1 a.2).elim
  apply ext
  intro G
  rw [mem_product_iff, mem_singleton]
  constructor
  · intro member
    apply eq_empty_iff.mpr
    intro z entry
    obtain ⟨a, _, _⟩ := (mem_pairSet_iff bounded).mp (member.1 entry)
    exact notMem_empty a.1 a.2
  · rintro rfl
    exact ⟨fun z entry => (notMem_empty z entry).elim,
      fun a => (notMem_empty a.1 a.2).elim⟩

theorem product_empty_of_empty_fibre {X Y : HSet.{u}} {B : Element X → HSet.{u}}
    (a : Element X) (empty : B a = ∅) : product X B Y = ∅ := by
  apply eq_empty_iff.mpr
  intro G member
  have evaluated := evaluate (Y := Y) (B := B) ⟨G, member⟩ a
  exact notMem_empty evaluated.1 (empty ▸ evaluated.2)

theorem product_singleton_empty :
    product ({∅} : HSet.{u}) (fun _ => ∅) ∅ = ∅ :=
  product_empty_of_empty_fibre ⟨∅, mem_singleton_self ∅⟩ rfl

theorem product_singleton_singleton (x y : HSet.{u}) :
    product {x} (fun _ => {y}) {y} = {{kpair x y}} := by
  have bounded : ∀ _ : Element ({x} : HSet.{u}), ({y} : HSet.{u}) ⊆ {y} := fun _ _ h => h
  apply ext
  intro G
  rw [mem_product_iff, mem_singleton]
  constructor
  · rintro ⟨bound, good⟩
    have only : ∀ z ∈ G, z = kpair x y := by
      intro z member
      obtain ⟨a, b, same⟩ := (mem_pairSet_iff bounded).mp (bound member)
      exact same.symm.trans (congrArg₂ kpair (mem_singleton.mp a.2) (mem_singleton.mp b.2))
    obtain ⟨b, entry, _⟩ := good ⟨x, mem_singleton_self x⟩
    have includes : kpair x y ∈ G := mem_singleton.mp b.2 ▸ entry.elim id
    exact ext fun z => ⟨fun member => mem_singleton.mpr (only z member),
      fun member => mem_singleton.mp member ▸ includes⟩
  · rintro rfl
    constructor
    · intro z member
      obtain rfl := mem_singleton.mp member
      exact mem_pairSet_iff bounded |>.mpr
        ⟨⟨x, mem_singleton_self x⟩, ⟨y, mem_singleton_self y⟩, rfl⟩
    · intro a
      refine ⟨⟨y, mem_singleton_self y⟩, ?_, ?_⟩
      · change Nonempty (kpair a.1 y ∈ {kpair x y})
        rw [mem_singleton.mp a.2]
        exact ⟨mem_singleton_self _⟩
      · rintro z ⟨member⟩ _
        obtain rfl := mem_singleton.mp member
        exact snd_kpair _ _

theorem product_quine_singleton :
    product {quineAtom.{u}} (fun _ => {quineAtom}) {quineAtom} =
      {{kpair quineAtom quineAtom}} := product_singleton_singleton _ _

def quineSection : Section ({quineAtom} : HSet.{u}) (fun _ => {quineAtom}) :=
  fun _ => ⟨quineAtom, mem_singleton_self _⟩

theorem quine_evaluation (a : Element ({quineAtom} : HSet.{u})) :
    (evaluate (BoundedDependentProducts.graphMember (fun _ _ h => h) quineSection) a).1 =
      quineAtom := congrArg PSigma.fst (evaluate_beta _ quineSection a)

theorem cartesian_empty_codomain (X : HSet.{u}) : cartesian X ∅ = ∅ := by
  apply eq_empty_iff.mpr
  intro z member
  obtain ⟨_, _, y, impossible, _⟩ := mem_cartesian_iff.mp member
  exact notMem_empty y impossible

/-- A real missing-bound failure: every fibre is inhabited, but separation
from the empty codomain cuts out every possible graph entry. -/
theorem wrong_bound_loses_inhabited_product :
    product ({∅} : HSet.{u}) (fun _ => {∅}) ∅ = ∅ := by
  apply eq_empty_iff.mpr
  intro G member
  obtain ⟨b, entry, _⟩ := (mem_product_iff.mp member).2 ⟨∅, mem_singleton_self ∅⟩
  have CartesianMember := (mem_sep.mp ((mem_product_iff.mp member).1 (entry.elim id))).1
  rw [cartesian_empty_codomain] at CartesianMember
  exact notMem_empty _ CartesianMember

theorem valid_bound_retains_inhabited_product :
    product ({∅} : HSet.{u}) (fun _ => {∅}) {∅} ≠ ∅ := by
  rw [product_singleton_singleton]
  intro empty
  exact notMem_empty _ (empty ▸ mem_singleton_self ({kpair ∅ ∅} : HSet.{u}))

/-- Totality on an empty domain is vacuous; the powerset bound, rather than
this predicate alone, enforces the empty graph. -/
theorem total_empty_domain_allows_extraneous_graph (B : Element (∅ : HSet.{u}) → HSet.{u}) :
    IsFunctionGraph kuratowski ∅ B ({∅} : HSet.{u}) ∧ {∅} ∉ product ∅ B {∅} := by
  constructor
  · intro a
    exact (notMem_empty a.1 a.2).elim
  · rw [product_empty_domain, mem_singleton]
    exact fun same => empty_ne_singleton_empty same.symm

namespace Infinite

def family (a : Element (NaturalOrdinalModel.naturals : HSet.{u})) : HSet.{u} := {∅, a.1}

theorem bounded : ∀ a : Element (NaturalOrdinalModel.naturals : HSet.{u}),
    family a ⊆ NaturalOrdinalModel.naturals := by
  intro a value member
  rcases mem_pair.mp member with rfl | rfl
  · exact NaturalOrdinalModel.zero_member_naturals
  · exact a.2

def argument (number : Nat) : Element (NaturalOrdinalModel.naturals : HSet.{u}) :=
  ⟨NaturalOrdinalModel.ordinal number, NaturalOrdinalModel.ordinal_member_naturals number⟩

/-- An actual infinite sequence of distinct members, not a finite sample. -/
theorem argument_injective : Function.Injective (argument : Nat →
    Element (NaturalOrdinalModel.naturals : HSet.{u})) :=
  fun _ _ same => NaturalOrdinalModel.ordinal_injective (congrArg PSigma.fst same)

theorem nonconstant_fibres : family.{u} (argument 0) ≠ family (argument 1) := by
  intro same
  have member : NaturalOrdinalModel.ordinal 1 ∈ family (argument 0) :=
    same.symm ▸ mem_pair.mpr (Or.inr rfl)
  change NaturalOrdinalModel.ordinal 1 ∈ ({∅, NaturalOrdinalModel.ordinal 0} : HSet.{u}) at member
  rcases mem_pair.mp member with equal | equal
  · exact NaturalOrdinalModel.Controls.zero_one_distinguished
      (NaturalOrdinalModel.ordinal_zero.trans equal.symm)
  · exact NaturalOrdinalModel.Controls.zero_one_distinguished equal.symm

def zeroSection : Section (NaturalOrdinalModel.naturals : HSet.{u}) family :=
  fun _ => ⟨∅, mem_pair.mpr (Or.inl rfl)⟩

def diagonalSection : Section (NaturalOrdinalModel.naturals : HSet.{u}) family :=
  fun a => ⟨a.1, mem_pair.mpr (Or.inr rfl)⟩

def naturalProduct : HSet.{u} := product NaturalOrdinalModel.naturals family NaturalOrdinalModel.naturals

def zeroGraph : Element (naturalProduct : HSet.{u}) :=
  BoundedDependentProducts.graphMember bounded zeroSection

def diagonalGraph : Element (naturalProduct : HSet.{u}) :=
  BoundedDependentProducts.graphMember bounded diagonalSection

theorem zero_evaluation (number : Nat) : (evaluate zeroGraph (argument number)).1 = ∅ :=
  congrArg PSigma.fst (evaluate_beta bounded zeroSection _)

theorem diagonal_evaluation (number : Nat) :
    (evaluate diagonalGraph (argument number)).1 = NaturalOrdinalModel.ordinal number :=
  congrArg PSigma.fst (evaluate_beta bounded diagonalSection _)

theorem zero_diagonal_graphs_distinguished : (zeroGraph : Element (naturalProduct : HSet.{u})).1 ≠
    diagonalGraph.1 := by
  intro same
  have sections := graph_injective bounded same
  have equal := congrArg (fun term => (term (argument 1)).1) sections
  exact NaturalOrdinalModel.Controls.zero_one_distinguished
    (NaturalOrdinalModel.ordinal_zero.trans equal)

/-- The family is defined by a proposition without deciding equality. Its
zero fibre is empty, although the ordinal-one fibre has a material member. -/
def missingZero (a : Element (NaturalOrdinalModel.naturals : HSet.{u})) : HSet.{u} :=
  HSet.sep (fun _ => a.1 ≠ ∅) (family a)

theorem missingZero_bounded : ∀ a : Element (NaturalOrdinalModel.naturals : HSet.{u}),
    missingZero a ⊆ NaturalOrdinalModel.naturals :=
  fun a _ member => bounded a (mem_sep.mp member).1

theorem missingZero_at_zero : missingZero (argument 0) = (∅ : HSet.{u}) := by
  apply eq_empty_iff.mpr
  intro value member
  exact (mem_sep.mp member).2 NaturalOrdinalModel.ordinal_zero

theorem missingZero_at_one_inhabited :
    NaturalOrdinalModel.ordinal 1 ∈ missingZero (argument 1) := by
  refine mem_sep.mpr ⟨mem_pair.mpr (Or.inr rfl), fun equal => ?_⟩
  exact NaturalOrdinalModel.Controls.zero_one_distinguished
    (NaturalOrdinalModel.ordinal_zero.trans equal.symm)

theorem missingZero_product_empty :
    product NaturalOrdinalModel.naturals missingZero NaturalOrdinalModel.naturals = (∅ : HSet.{u}) :=
  product_empty_of_empty_fibre (argument 0) missingZero_at_zero

end Infinite

namespace PullbackLabels

open BoundedProductBeckChevalley

def emptyPoint : Element ({∅} : HSet.{u}) := ⟨∅, mem_singleton_self ∅⟩

def cyclicPoint : Element ({quineAtom} : HSet.{u}) := ⟨quineAtom, mem_singleton_self _⟩

def leftMap : Element ({∅} : HSet.{u}) → Element ({∅} : HSet.{u}) := fun _ => emptyPoint

def rightMap : Element ({quineAtom} : HSet.{u}) → Element ({∅} : HSet.{u}) := fun _ => emptyPoint

def codomain : Element ({∅} : HSet.{u}) → HSet.{u} := fun _ => {∅}

theorem codomain_bounded : ∀ a : Element ({∅} : HSet.{u}), codomain a ⊆ ({∅} : HSet.{u}) :=
  fun _ _ member => member

def oldArgument : Element (oldFibre leftMap rightMap (cyclicPoint : Element ({quineAtom} : HSet.{u}))) :=
  fibreElement leftMap (rightMap cyclicPoint) emptyPoint rfl

def newArgument : Element (newFibre leftMap rightMap (cyclicPoint : Element ({quineAtom} : HSet.{u}))) :=
  fibreBackward leftMap rightMap cyclicPoint oldArgument

def oldSection : Section (oldFibre leftMap rightMap (cyclicPoint : Element ({quineAtom} : HSet.{u})))
    (oldCodomain leftMap rightMap codomain cyclicPoint) := fun _ => ⟨∅, mem_singleton_self ∅⟩

def oldGraph : Element (product (oldFibre leftMap rightMap cyclicPoint)
    (oldCodomain leftMap rightMap codomain cyclicPoint) ({∅} : HSet.{u})) :=
  BoundedDependentProducts.graphMember (fun _ _ member => member) oldSection

def newGraph : Element (product (newFibre leftMap rightMap cyclicPoint)
    (newCodomain leftMap rightMap codomain cyclicPoint) ({∅} : HSet.{u})) :=
  beckChevalley leftMap rightMap codomain codomain_bounded cyclicPoint oldGraph

theorem corresponding_value_preserved : (evaluate newGraph newArgument).1 = (∅ : HSet.{u}) :=
  (congrArg PSigma.fst (beckChevalley_evaluate leftMap rightMap codomain codomain_bounded
    cyclicPoint oldGraph newArgument)).trans (congrArg PSigma.fst (evaluate_beta _ oldSection _))

/-- The actual Beck--Chevalley comparison does not equate different freshly
labelled graphs: a cyclic base label is present in the new argument pair. -/
theorem fresh_graphs_distinguished : (newGraph : Element (product
    (newFibre leftMap rightMap cyclicPoint) (newCodomain leftMap rightMap codomain cyclicPoint)
    ({∅} : HSet.{u}))).1 ≠ oldGraph.1 := by
  intro same
  have entry := evaluate_entry newGraph newArgument
  have oldEntry := same ▸ entry
  obtain ⟨a, equals⟩ := (mem_graph_iff (fun _ _ member => member) oldSection).mp oldEntry
  have firstValue := (kpair_inj.mp equals).1
  have oldEmpty : a.1 = (∅ : HSet.{u}) := mem_singleton.mp (inclusion a).2
  have newEmpty : kpair (quineAtom : HSet.{u}) ∅ = ∅ := firstValue.symm.trans oldEmpty
  exact notMem_empty {quineAtom} (newEmpty ▸ mem_kpair.mpr (Or.inl rfl))

end PullbackLabels

end Mettapedia.TypeTheory.MaterialSets.Hypersets.BoundedProductControls
