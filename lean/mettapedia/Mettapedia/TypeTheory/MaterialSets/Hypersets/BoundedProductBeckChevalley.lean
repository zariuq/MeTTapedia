import Mettapedia.TypeTheory.MaterialSets.Hypersets.BoundedProductSubstitution

/-!
# Constructed material pullbacks and dependent-product Beck--Chevalley

Fibres of an arbitrary map of material member types are separated from its
domain. A pullback is then an actual dependent-pair set, bounded by the
original domain. Its projection fibre has a constructed coordinate
equivalence with the original fibre. The induced product comparison has
inverse and evaluation laws for arbitrary bounded dependent codomains.

The new graph arguments are pullback pairs; their encodings need not equal
the old graph arguments. The comparison transports actual dependent terms
through the fibre equivalence while preserving each codomain material value.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.BoundedProductBeckChevalley

universe u

open HSet BoundedDependentProducts BoundedProductSubstitution

/-- The material fibre of an authored map, constructed by separation. -/
def fibre {X Z : HSet.{u}} (σ : Element X → Element Z) (z : Element Z) : HSet.{u} :=
  HSet.sep (fun x => ∃ hx : x ∈ X, σ ⟨x, hx⟩ = z) X

theorem fibre_subset {X Z : HSet.{u}} (σ : Element X → Element Z) (z : Element Z) :
    fibre σ z ⊆ X := fun _ member => (mem_sep.mp member).1

def inclusion {X Z : HSet.{u}} {σ : Element X → Element Z} {z : Element Z}
    (a : Element (fibre σ z)) : Element X := ⟨a.1, (mem_sep.mp a.2).1⟩

theorem inclusion_spec {X Z : HSet.{u}} {σ : Element X → Element Z} {z : Element Z}
    (a : Element (fibre σ z)) : σ (inclusion a) = z := by
  obtain ⟨_, hx, same⟩ := mem_sep.mp a.2
  exact same

def fibreElement {X Z : HSet.{u}} (σ : Element X → Element Z) (z : Element Z)
    (a : Element X) (same : σ a = z) : Element (fibre σ z) :=
  ⟨a.1, mem_sep.mpr ⟨a.2, a.2, same⟩⟩

theorem inclusion_fibreElement {X Z : HSet.{u}} (σ : Element X → Element Z)
    (z : Element Z) (a : Element X) (same : σ a = z) :
    inclusion (fibreElement σ z a same) = a := El.ext propositional rfl

theorem fibreElement_inclusion {X Z : HSet.{u}} {σ : Element X → Element Z}
    {z : Element Z} (a : Element (fibre σ z)) :
    fibreElement σ z (inclusion a) (inclusion_spec a) = a := El.ext propositional rfl

variable {X Z W : HSet.{u}} (σ : Element X → Element Z) (τ : Element W → Element Z)

/-- The actual material pullback, with no replacement or presentation input. -/
def pullback : HSet.{u} := pairSet W (fun w => fibre σ (τ w)) X

def first (pair : Element (pullback σ τ)) : Element W :=
  pairFirst (fun w => fibre_subset σ (τ w)) pair

def second (pair : Element (pullback σ τ)) : Element X :=
  inclusion (pairSecond (fun w => fibre_subset σ (τ w)) pair)

theorem square (pair : Element (pullback σ τ)) : σ (second σ τ pair) = τ (first σ τ pair) :=
  inclusion_spec (pairSecond (fun w => fibre_subset σ (τ w)) pair)

def pullbackPair (w : Element W) (a : Element X) (same : σ a = τ w) :
    Element (pullback σ τ) :=
  BoundedDependentProducts.pairMember (fun w => fibre_subset σ (τ w)) w
    (fibreElement σ (τ w) a same)

theorem first_pair (w : Element W) (a : Element X) (same : σ a = τ w) :
    first σ τ (pullbackPair σ τ w a same) = w :=
  pairFirst_pairMember _ _ _

theorem second_pair (w : Element W) (a : Element X) (same : σ a = τ w) :
    second σ τ (pullbackPair σ τ w a same) = a := El.ext propositional (snd_kpair _ _)

theorem pair_coordinates (pair : Element (pullback σ τ)) :
    pullbackPair σ τ (first σ τ pair) (second σ τ pair) (square σ τ pair) = pair := by
  apply El.ext propositional
  exact congrArg PSigma.fst (pairMember_pairFirst_pairSecond
    (fun w => fibre_subset σ (τ w)) pair)

/-- Every pair of compatible coordinates has exactly one pullback member. -/
theorem pullback_universal (w : Element W) (a : Element X) (same : σ a = τ w) :
    ∃! pair : Element (pullback σ τ), first σ τ pair = w ∧ second σ τ pair = a := by
  refine ⟨pullbackPair σ τ w a same, ⟨first_pair σ τ w a same, second_pair σ τ w a same⟩,
    fun pair coordinates => ?_⟩
  apply El.ext propositional
  have reconstruction := congrArg PSigma.fst (pair_coordinates σ τ pair)
  change kpair (first σ τ pair).1 (second σ τ pair).1 = pair.1 at reconstruction
  rw [coordinates.1, coordinates.2] at reconstruction
  exact reconstruction.symm

def oldFibre (w : Element W) : HSet.{u} := fibre σ (τ w)

def newFibre (w : Element W) : HSet.{u} := fibre (first σ τ) w

/-- Read the original coordinate of a member of the new projection fibre. -/
def fibreForward (w : Element W) (pair : Element (newFibre σ τ w)) :
    Element (oldFibre σ τ w) :=
  fibreElement σ (τ w) (second σ τ (inclusion pair))
    ((square σ τ (inclusion pair)).trans (congrArg τ (inclusion_spec pair)))

/-- Reconstruct the new fibre member from the original coordinate and the
retained base point. There is no chosen inverse or representative. -/
def fibreBackward (w : Element W) (a : Element (oldFibre σ τ w)) :
    Element (newFibre σ τ w) :=
  fibreElement (first σ τ) w (pullbackPair σ τ w (inclusion a) (inclusion_spec a))
    (first_pair σ τ w (inclusion a) (inclusion_spec a))

theorem fibreBackward_forward (w : Element W) (pair : Element (newFibre σ τ w)) :
    fibreBackward σ τ w (fibreForward σ τ w pair) = pair := by
  apply El.ext propositional
  have reconstruction := congrArg PSigma.fst (pair_coordinates σ τ (inclusion pair))
  change kpair (first σ τ (inclusion pair)).1 (second σ τ (inclusion pair)).1 = pair.1
    at reconstruction
  rw [inclusion_spec pair] at reconstruction
  exact reconstruction

theorem fibreForward_backward (w : Element W) (a : Element (oldFibre σ τ w)) :
    fibreForward σ τ w (fibreBackward σ τ w a) = a :=
  El.ext propositional (snd_kpair _ _)

def fibreEquiv (w : Element W) : Element (newFibre σ τ w) ≃ Element (oldFibre σ τ w) where
  toFun := fibreForward σ τ w
  invFun := fibreBackward σ τ w
  left_inv := fibreBackward_forward σ τ w
  right_inv := fibreForward_backward σ τ w

theorem fibreEquiv_coordinate (w : Element W) (pair : Element (newFibre σ τ w)) :
    inclusion (fibreEquiv σ τ w pair) = second σ τ (inclusion pair) :=
  El.ext propositional rfl

variable {Y : HSet.{u}} (B : Element X → HSet.{u}) (bounded : ∀ a, B a ⊆ Y)

def oldCodomain (w : Element W) (a : Element (oldFibre σ τ w)) : HSet.{u} := B (inclusion a)

def newCodomain (w : Element W) (pair : Element (newFibre σ τ w)) : HSet.{u} :=
  B (second σ τ (inclusion pair))

/-- Beck--Chevalley for the constructed material pullback: all complete
dependent functions on the corresponding fibres, with a constructed inverse.
Fresh graph labels change from `x` to `(w,x)`; codomain values are preserved. -/
def beckChevalley (w : Element W) :
    Element (product (oldFibre σ τ w) (oldCodomain σ τ B w) Y) ≃
      Element (product (newFibre σ τ w) (newCodomain σ τ B w) Y) :=
  productReindexEquiv (fun a => bounded (inclusion a)) (fibreEquiv σ τ w)

theorem beckChevalley_evaluate (w : Element W)
    (g : Element (product (oldFibre σ τ w) (oldCodomain σ τ B w) Y))
    (pair : Element (newFibre σ τ w)) :
    evaluate (beckChevalley σ τ B bounded w g) pair =
      evaluate g (fibreEquiv σ τ w pair) :=
  productReindexEquiv_evaluate _ _ _ _

theorem beckChevalley_entry (w : Element W)
    (g : Element (product (oldFibre σ τ w) (oldCodomain σ τ B w) Y))
    (pair : Element (newFibre σ τ w))
    (value : Element (newCodomain σ τ B w pair)) :
    kpair pair.1 value.1 ∈ (beckChevalley σ τ B bounded w g).1 ↔
      kpair (fibreEquiv σ τ w pair).1 value.1 ∈ g.1 := by
  exact (product_entry_iff (beckChevalley σ τ B bounded w g) pair value).trans
    ((congrArg (fun term => term = value) (beckChevalley_evaluate σ τ B bounded w g pair)
      |>.to_iff).trans (product_entry_iff g (fibreEquiv σ τ w pair) value).symm)

/-- Encoding a dependent term and changing base gives the same complete
new graph as first changing its arguments and then encoding. -/
theorem beckChevalley_graphMember (w : Element W)
    (s : Section (oldFibre σ τ w) (oldCodomain σ τ B w)) :
    beckChevalley σ τ B bounded w
        (BoundedDependentProducts.graphMember (fun a => bounded (inclusion a)) s) =
      BoundedDependentProducts.graphMember
        (fun pair => bounded (second σ τ (inclusion pair)))
        (fun pair => s (fibreEquiv σ τ w pair)) := by
  exact (productReindexEquiv_reindex (fun a => bounded (inclusion a))
    (fibreEquiv σ τ w) (BoundedDependentProducts.graphMember
      (fun a => bounded (inclusion a)) s)).trans
    (reindex_graphMember (fun a => bounded (inclusion a)) (fibreEquiv σ τ w) s)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.BoundedProductBeckChevalley
