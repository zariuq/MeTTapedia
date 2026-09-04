import Mathlib.Logic.Relation

/-!
# Pointwise reflection of proof-relevant cells into a locally thin boundary

A locally thin bicategorical hom identifies all parallel two-cells.  At one
fixed pair of parallel one-cells, this is the quotient of the cell type by the
indiscrete equivalence relation.  This module isolates that pointwise
reflection and its exact observer criterion.

An observation factors through the thin reflection exactly when it is
constant on the original cell fibre.  Consequently, a pair of cells separated
by a declared observation is a precise obstruction to local thinness.  Merely
having proof-relevant terms or receipts elsewhere is not such an obstruction:
the discriminator must live in the cell fibre being reflected.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory
namespace LocallyThinCellReflection

universe uCell uOutput

/-! ## The pointwise thin reflection -/

/-- The indiscrete equivalence relation on one parallel-cell fibre. -/
def indiscreteSetoid (Cell : Type uCell) : Setoid Cell where
  r := fun _ _ => True
  iseqv := {
    refl := fun _ => trivial
    symm := fun _ => trivial
    trans := fun _ _ => trivial }

/-- Identify all cells between one fixed pair of parallel one-cells.  The
quotient preserves whether the cell fibre is inhabited while making it
subsingleton. -/
def ThinReflection (Cell : Type uCell) : Type uCell :=
  Quotient (indiscreteSetoid Cell)

/-- The unit from a retained cell to its locally thin reflection. -/
def reflect {Cell : Type uCell} (cell : Cell) : ThinReflection Cell :=
  Quotient.mk (indiscreteSetoid Cell) cell

instance thinReflectionSubsingleton (Cell : Type uCell) :
    Subsingleton (ThinReflection Cell) where
  allEq := by
    intro left right
    induction left using Quotient.inductionOn with
    | _ leftRepresentative =>
        induction right using Quotient.inductionOn with
        | _ rightRepresentative =>
            exact Quotient.sound trivial

/-- Every reflected cell has an original representative. -/
theorem reflect_surjective {Cell : Type uCell} :
    Function.Surjective (@reflect Cell) := by
  intro reflected
  induction reflected using Quotient.inductionOn with
  | _ representative => exact ⟨representative, rfl⟩

/-- Thin reflection preserves inhabitation exactly. -/
theorem thinReflection_nonempty_iff {Cell : Type uCell} :
    Nonempty (ThinReflection Cell) ↔ Nonempty Cell := by
  constructor
  · rintro ⟨reflected⟩
    obtain ⟨cell, _⟩ := reflect_surjective reflected
    exact ⟨cell⟩
  · rintro ⟨cell⟩
    exact ⟨reflect cell⟩

/-! ## Observer factorization -/

/-- An observation of retained cells descends to their locally thin
reflection. -/
def FactorsThrough
    {Cell : Type uCell} {Output : Type uOutput}
    (observe : Cell → Output) : Prop :=
  ∃ summarize : ThinReflection Cell → Output,
    ∀ cell, summarize (reflect cell) = observe cell

/-- The exact invariance condition required by local thinning. -/
def FibreInvariant
    {Cell : Type uCell} {Output : Type uOutput}
    (observe : Cell → Output) : Prop :=
  ∀ left right, observe left = observe right

/-- Construct the descended observation from its fibre invariance. -/
def descend
    {Cell : Type uCell} {Output : Type uOutput}
    (observe : Cell → Output) (invariant : FibreInvariant observe) :
    ThinReflection Cell → Output :=
  Quotient.lift observe (fun left right _ => invariant left right)

@[simp] theorem descend_reflect
    {Cell : Type uCell} {Output : Type uOutput}
    (observe : Cell → Output) (invariant : FibreInvariant observe)
    (cell : Cell) :
    descend observe invariant (reflect cell) = observe cell :=
  rfl

/-- An observation descends to the locally thin reflection exactly when it
cannot distinguish any two cells in the original parallel fibre. -/
theorem factorsThrough_iff_fibreInvariant
    {Cell : Type uCell} {Output : Type uOutput}
    (observe : Cell → Output) :
    FactorsThrough observe ↔ FibreInvariant observe := by
  constructor
  · rintro ⟨summarize, commutes⟩ left right
    rw [← commutes left, ← commutes right]
    exact congrArg summarize (Subsingleton.elim _ _)
  · intro invariant
    exact ⟨descend observe invariant, descend_reflect observe invariant⟩

/-- A descended observer is uniquely determined by its values on retained
cells, including when the original fibre is empty. -/
theorem descended_unique
    {Cell : Type uCell} {Output : Type uOutput}
    (observe : Cell → Output)
    (left right : ThinReflection Cell → Output)
    (leftCommutes : ∀ cell, left (reflect cell) = observe cell)
    (rightCommutes : ∀ cell, right (reflect cell) = observe cell) :
    left = right := by
  funext reflected
  obtain ⟨cell, equalReflected⟩ := reflect_surjective reflected
  subst equalReflected
  exact (leftCommutes cell).trans (rightCommutes cell).symm

/-! ## Exact loss and discriminator criteria -/

/-- Thin reflection is lossless on one cell fibre exactly when that fibre was
already subsingleton. -/
theorem reflect_injective_iff_subsingleton (Cell : Type uCell) :
    Function.Injective (@reflect Cell) ↔ Subsingleton Cell := by
  constructor
  · intro injective
    exact {
      allEq := by
        intro left right
        apply injective
        exact Subsingleton.elim _ _ }
  · intro thin left right _
    exact thin.elim left right

/-- Concrete evidence that a declared observation distinguishes parallel
cells. -/
structure Discriminator (Cell : Type uCell) (Output : Type uOutput) where
  left : Cell
  right : Cell
  observe : Cell → Output
  separates : observe left ≠ observe right

namespace Discriminator

variable {Cell : Type uCell} {Output : Type uOutput}

/-- A genuine discriminator prevents the observer from descending through
local thinning. -/
theorem not_factorsThrough (discriminator : Discriminator Cell Output) :
    ¬ FactorsThrough discriminator.observe := by
  rw [factorsThrough_iff_fibreInvariant]
  intro invariant
  exact discriminator.separates
    (invariant discriminator.left discriminator.right)

/-- A genuinely discriminated cell fibre is not already thin. -/
theorem not_subsingleton (discriminator : Discriminator Cell Output) :
    ¬ Subsingleton Cell := by
  intro thin
  exact discriminator.separates
    (congrArg discriminator.observe
      (thin.elim discriminator.left discriminator.right))

/-- Therefore the thin-reflection unit is not injective. -/
theorem reflect_not_injective (discriminator : Discriminator Cell Output) :
    ¬ Function.Injective (@reflect Cell) := by
  rw [reflect_injective_iff_subsingleton]
  exact discriminator.not_subsingleton

end Discriminator

/-! ## A positive and negative control -/

namespace Canaries

/-- A constant observation lawfully descends. -/
theorem constant_observer_factors
    {Cell : Type uCell} {Output : Type uOutput} (output : Output) :
    FactorsThrough (fun _ : Cell => output) := by
  rw [factorsThrough_iff_fibreInvariant]
  intro _ _
  rfl

/-- Boolean identity distinguishes the two cells of `Bool`, so it cannot
descend to their locally thin reflection. -/
def boolDiscriminator : Discriminator Bool Bool where
  left := false
  right := true
  observe := id
  separates := by decide

theorem bool_identity_does_not_factor :
    ¬ FactorsThrough (fun value : Bool => value) :=
  boolDiscriminator.not_factorsThrough

end Canaries

/-! ## Axiom audit -/

#print axioms reflect_surjective
#print axioms thinReflection_nonempty_iff
#print axioms factorsThrough_iff_fibreInvariant
#print axioms descended_unique
#print axioms reflect_injective_iff_subsingleton
#print axioms Discriminator.not_factorsThrough
#print axioms Discriminator.reflect_not_injective
#print axioms Canaries.constant_observer_factors
#print axioms Canaries.bool_identity_does_not_factor

end LocallyThinCellReflection
end Mettapedia.TypeTheory
