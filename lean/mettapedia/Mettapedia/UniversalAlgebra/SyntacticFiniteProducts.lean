import Mettapedia.UniversalAlgebra.SyntacticCategory

/-!
# Finite products in an equational syntactic category

Finite variable contexts form products by addition.  The empty context is
terminal, the two blocks of variables give projections, and concatenation of
term tuples gives pairing.  The equations below prove the universal property
directly.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

open CategoryTheory

universe u

variable {S : Signature.{u}}

namespace BoundedTermTuple

/-- Projection onto the first block of a concatenated finite context. -/
def firstProjection (left right : Nat) :
    BoundedTermTuple S (left + right) left where
  component position :=
    let embedded := Fin.castAdd right position
    ⟨.var embedded.val, embedded.isLt⟩

/-- Projection onto the second block of a concatenated finite context. -/
def secondProjection (left right : Nat) :
    BoundedTermTuple S (left + right) right where
  component position :=
    let embedded := Fin.natAdd left position
    ⟨.var embedded.val, embedded.isLt⟩

/-- Concatenate two tuples with the same input context. -/
def pair {input left right : Nat}
    (first : BoundedTermTuple S input left)
    (second : BoundedTermTuple S input right) :
    BoundedTermTuple S input (left + right) where
  component := Fin.addCases first.component second.component

/-- Pairing respects pointwise generated consequence. -/
theorem pair_equivalent (system : EquationSystem S)
    {input left right : Nat}
    {first first' : BoundedTermTuple S input left}
    {second second' : BoundedTermTuple S input right}
    (firstEquivalent : Equivalent system first first')
    (secondEquivalent : Equivalent system second second') :
    Equivalent system (pair first second) (pair first' second') := by
  intro position
  refine Fin.addCases ?_ ?_ position
  · intro firstPosition
    simpa only [pair, Fin.addCases_left] using firstEquivalent firstPosition
  · intro secondPosition
    simpa only [pair, Fin.addCases_right] using secondEquivalent secondPosition

/-- The first projection of a raw pair recovers its first tuple. -/
theorem pair_comp_firstProjection {input left right : Nat}
    (first : BoundedTermTuple S input left)
    (second : BoundedTermTuple S input right) :
    comp (pair first second) (firstProjection left right) = first := by
  ext position
  change substitution (pair first second) (Fin.castAdd right position).val =
    (first.component position).1
  rw [substitution_apply (pair first second) (Fin.castAdd right position)]
  simp only [pair, Fin.addCases_left]

/-- The second projection of a raw pair recovers its second tuple. -/
theorem pair_comp_secondProjection {input left right : Nat}
    (first : BoundedTermTuple S input left)
    (second : BoundedTermTuple S input right) :
    comp (pair first second) (secondProjection left right) = second := by
  ext position
  change substitution (pair first second) (Fin.natAdd left position).val =
    (second.component position).1
  rw [substitution_apply (pair first second) (Fin.natAdd left position)]
  simp only [pair, Fin.addCases_right]

/-- Pairing the two projected blocks recovers a raw tuple. -/
theorem pair_projections {input left right : Nat}
    (tuple : BoundedTermTuple S input (left + right)) :
    pair (comp tuple (firstProjection left right))
      (comp tuple (secondProjection left right)) = tuple := by
  ext position
  refine Fin.addCases ?_ ?_ position
  · intro firstPosition
    simp only [pair, Fin.addCases_left, comp, firstProjection,
      Term.subst_var]
    change substitution tuple (Fin.castAdd right firstPosition).val =
      (tuple.component (Fin.castAdd right firstPosition)).1
    exact substitution_apply tuple (Fin.castAdd right firstPosition)
  · intro secondPosition
    simp only [pair, Fin.addCases_right, comp, secondProjection,
      Term.subst_var]
    change substitution tuple (Fin.natAdd left secondPosition).val =
      (tuple.component (Fin.natAdd left secondPosition)).1
    exact substitution_apply tuple (Fin.natAdd left secondPosition)

end BoundedTermTuple

namespace SyntacticCategory

variable (system : EquationSystem S)

/-- The unique displayed arrow into the empty context. -/
def terminalArrow {input : Nat} :
    object system input ⟶ object system 0 :=
  mk system ⟨Fin.elim0⟩

/-- Every arrow into the empty context is the displayed terminal arrow. -/
theorem hom_ext_empty {input : Nat}
    (arrow : object system input ⟶ object system 0) :
    arrow = terminalArrow system := by
  induction arrow using Quotient.inductionOn with
  | _ tuple =>
      apply (mk_eq_iff system _ _).mpr
      intro position
      exact Fin.elim0 position

/-- Projection onto the first block of a context sum. -/
def firstProjection (left right : Nat) :
    object system (left + right) ⟶ object system left :=
  mk system (BoundedTermTuple.firstProjection left right)

/-- Projection onto the second block of a context sum. -/
def secondProjection (left right : Nat) :
    object system (left + right) ⟶ object system right :=
  mk system (BoundedTermTuple.secondProjection left right)

/-- Pair two syntactic arrows by concatenating their output tuples. -/
def pair {input left right : Nat} :
    (object system input ⟶ object system left) →
    (object system input ⟶ object system right) →
    (object system input ⟶ object system (left + right)) :=
  Quotient.lift₂
    (fun first second => mk system (BoundedTermTuple.pair first second))
    (by
      intro first first' second second' firstEquivalent secondEquivalent
      apply (mk_eq_iff system _ _).mpr
      exact BoundedTermTuple.pair_equivalent system firstEquivalent
        secondEquivalent)

/-- Pairing followed by the first projection is the first arrow. -/
theorem pair_firstProjection {input left right : Nat}
    (first : object system input ⟶ object system left)
    (second : object system input ⟶ object system right) :
    pair system first second ≫ firstProjection system left right = first := by
  induction first using Quotient.inductionOn with
  | _ first =>
    induction second using Quotient.inductionOn with
    | _ second =>
      apply (mk_eq_iff system _ _).mpr
      rw [BoundedTermTuple.pair_comp_firstProjection]
      exact (BoundedTermTuple.consequenceSetoid system _ _).refl first

/-- Pairing followed by the second projection is the second arrow. -/
theorem pair_secondProjection {input left right : Nat}
    (first : object system input ⟶ object system left)
    (second : object system input ⟶ object system right) :
    pair system first second ≫ secondProjection system left right = second := by
  induction first using Quotient.inductionOn with
  | _ first =>
    induction second using Quotient.inductionOn with
    | _ second =>
      apply (mk_eq_iff system _ _).mpr
      rw [BoundedTermTuple.pair_comp_secondProjection]
      exact (BoundedTermTuple.consequenceSetoid system _ _).refl second

/-- An arrow into a context sum is recovered from its two projections. -/
theorem pair_projections {input left right : Nat}
    (arrow : object system input ⟶ object system (left + right)) :
    pair system
        (arrow ≫ firstProjection system left right)
        (arrow ≫ secondProjection system left right) = arrow := by
  induction arrow using Quotient.inductionOn with
  | _ tuple =>
      apply (mk_eq_iff system _ _).mpr
      rw [BoundedTermTuple.pair_projections]
      exact (BoundedTermTuple.consequenceSetoid system _ _).refl tuple

/-- The two projection equations uniquely determine a paired arrow. -/
theorem pair_unique {input left right : Nat}
    {first : object system input ⟶ object system left}
    {second : object system input ⟶ object system right}
    {candidate : object system input ⟶ object system (left + right)}
    (firstEquation :
      candidate ≫ firstProjection system left right = first)
    (secondEquation :
      candidate ≫ secondProjection system left right = second) :
    candidate = pair system first second := by
  calc
    candidate = pair system
        (candidate ≫ firstProjection system left right)
        (candidate ≫ secondProjection system left right) :=
      (pair_projections system candidate).symm
    _ = pair system first second := by rw [firstEquation, secondEquation]

/-- Context addition, the displayed projections, and tuple pairing satisfy the
binary-product universal property. -/
theorem contextSum_isProduct {input left right : Nat}
    (first : object system input ⟶ object system left)
    (second : object system input ⟶ object system right) :
    pair system first second ≫ firstProjection system left right = first ∧
    pair system first second ≫ secondProjection system left right = second ∧
    ∀ candidate,
      candidate ≫ firstProjection system left right = first →
      candidate ≫ secondProjection system left right = second →
      candidate = pair system first second :=
  ⟨pair_firstProjection system first second,
    pair_secondProjection system first second,
    fun _candidate firstEquation secondEquation =>
      pair_unique system firstEquation secondEquation⟩

end SyntacticCategory

end Mettapedia.UniversalAlgebra
