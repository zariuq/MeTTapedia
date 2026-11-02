import Mettapedia.TypeTheory.MaterialSets.Hypersets.NaturalAlgebraRepresentation

/-!
# Generation, constructor faithfulness and empty-fibre controls

A collapsed natural algebra is generated but fails no-confusion. A
recursive-only algebra has an injective constructor but no generated values.
The material natural comparison preserves and reflects actual natural values.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.IndexedPolynomial.GeneratedControls
open Algebra MaterialSets.Hypersets
open MaterialSets.Hypersets.NaturalAlgebraRepresentation

def zeroTree : Fix polynomial () () := .roll false (fun impossible => nomatch impossible)
def oneTree : Fix polynomial () () := .roll true (fun _ => zeroTree)

theorem source_zero_ne_one : zeroTree ≠ oneTree := by
  intro same
  have tags := congrArg (fun tree => (Fix.out polynomial tree).1) same
  exact Bool.noConfusion tags

def collapsed : Algebra polynomial (fun _ _ => Unit) := unaryAlgebra () (fun _ => ())

theorem collapsed_generated (value : Unit) : Generated collapsed () () value := by
  cases value
  exact generated_closed collapsed () () false (fun impossible => nomatch impossible)
    (fun impossible => nomatch impossible)

theorem collapsed_not_constructor_injective : ¬ Function.Injective (collapsed.act () ()) := by
  intro injective
  have layers := injective (a₁ := ⟨false, fun impossible => nomatch impossible⟩)
    (a₂ := ⟨true, fun _ => ()⟩) rfl
  exact Bool.noConfusion (congrArg Sigma.fst layers)

theorem collapsed_fold_not_injective : ¬ Function.Injective (Fix.fold polynomial collapsed.act () ()) := by
  intro injective
  exact source_zero_ne_one (injective (a₁ := zeroTree) (a₂ := oneTree) rfl)

theorem collapsed_no_representation : ¬ Nonempty (Representation polynomial collapsed) := by
  rintro ⟨representation⟩
  have same : representation.toEquiv () () zeroTree = representation.toEquiv () () oneTree := Subsingleton.elim _ _
  exact source_zero_ne_one ((representation.toEquiv () ()).injective same)

def evenSuccessor (value : Nat) : Nat := 2 * (value / 2) + 2
def evenAlgebra := unaryAlgebra 0 evenSuccessor

theorem generated_even (value : Nat) (generated : Generated evenAlgebra () () value) :
    ∃ number, value = 2 * number := by
  apply generated (fun _ _ candidate => ∃ number, candidate = 2 * number)
  intro _ _ shape children _
  cases shape with
  | false => exact ⟨0, rfl⟩
  | true => exact ⟨children () / 2 + 1, by simp [evenAlgebra, unaryAlgebra, evenSuccessor, Nat.mul_add]⟩

theorem even_generated_injective :
    ∀ base index, Function.Injective ((generatedAlgebra evenAlgebra).act base index) := by
  apply unaryAlgebra_generated_injective
  · intro value _
    simp [evenSuccessor]
  · intro first second firstGenerated secondGenerated same
    obtain ⟨first, rfl⟩ := generated_even first firstGenerated
    obtain ⟨second, rfl⟩ := generated_even second secondGenerated
    simp only [evenSuccessor] at same
    rw [Nat.mul_div_right first (m := 2) (by decide), Nat.mul_div_right second (m := 2) (by decide)] at same
    exact Nat.add_right_cancel same

theorem even_not_ambient_injective : ¬ Function.Injective (evenAlgebra.act () ()) := by
  intro injective
  have layers := injective (a₁ := ⟨true, fun _ => 0⟩) (a₂ := ⟨true, fun _ => 1⟩) rfl
  have branches := eq_of_heq (Sigma.mk.inj layers).2
  exact Nat.zero_ne_one (congrFun branches ())

theorem odd_junk_not_generated : ¬ Generated evenAlgebra () () 1 := by
  intro generated
  obtain ⟨number, same⟩ := generated_even 1 generated
  have residues := congrArg (fun value => value % 2) same
  simp at residues

noncomputable def even_representation : Representation polynomial (generatedAlgebra evenAlgebra) :=
  generatedRepresentation evenAlgebra even_generated_injective

def loopPolynomial : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Unit
  Position _ := Unit
  next _ _ := ()

def loopAlgebra : Algebra loopPolynomial (fun _ _ => Unit) where
  act _ _ _ := ()

theorem loop_constructor_injective : ∀ base index, Function.Injective (loopAlgebra.act base index) := by
  intro base index ⟨shape, children⟩ ⟨other, branches⟩ _
  cases shape
  cases other
  apply congrArg (Sigma.mk ())
  funext position
  exact Subsingleton.elim _ _

theorem loop_no_generated (value : Unit) : ¬ Generated loopAlgebra () () value := by
  intro generated
  exact generated (fun _ _ _ => False) (fun _ _ _ _ hypotheses => hypotheses ())

theorem loop_generated_fibre_empty : ¬ Nonempty (GeneratedCarrier loopAlgebra () ()) := by
  rintro ⟨value⟩
  exact loop_no_generated value.val value.property

noncomputable def loop_guarded_representation : Representation loopPolynomial (generatedAlgebra loopAlgebra) :=
  generatedRepresentation loopAlgebra (generatedAlgebra_injective loopAlgebra loop_constructor_injective)

theorem loop_no_ambient_representation : ¬ Nonempty (Representation loopPolynomial loopAlgebra) := by
  rintro ⟨representation⟩
  let tree := (representation.toEquiv () ()).symm ()
  exact loop_no_generated (Fix.fold loopPolynomial loopAlgebra.act () () tree)
    (generated_fold loopAlgebra () () tree)

theorem material_zero_one_distinct : (naturalEquivalence.{0} 0).val ≠ (naturalEquivalence.{0} 1).val := by
  intro same
  have values : naturalEquivalence.{0} 0 = naturalEquivalence.{0} 1 := Subtype.ext same
  exact Nat.zero_ne_one (naturalEquivalence.injective values)

theorem material_natural_equality (first second : Nat) :
    (naturalEquivalence.{0} first).val = (naturalEquivalence.{0} second).val ↔ first = second := by
  constructor
  · intro same
    exact naturalEquivalence.injective (Subtype.ext same)
  · rintro rfl
    rfl

theorem material_two_is_actual_ordinal :
    (naturalEquivalence.{0} 2).val = NaturalOrdinalModel.ordinal 2 := naturalEquivalence_ordinal 2

theorem material_quine_refused : (naturalEquivalence.{0} 2).val ≠ HSet.quineAtom := comparison_refuses_quine 2

#print axioms collapsed_fold_not_injective
#print axioms collapsed_no_representation
#print axioms even_representation
#print axioms loop_generated_fibre_empty
#print axioms loop_guarded_representation
#print axioms material_natural_equality
end Mettapedia.TypeTheory.IndexedPolynomial.GeneratedControls
