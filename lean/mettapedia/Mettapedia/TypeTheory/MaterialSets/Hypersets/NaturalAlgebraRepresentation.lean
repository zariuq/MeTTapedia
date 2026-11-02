import Mettapedia.TypeTheory.IndexedPolynomialGeneratedRepresentation
import Mettapedia.TypeTheory.MaterialSets.Hypersets.NaturalOrdinalModel

/-!
# Initial-algebra comparison with material natural ordinals

Host naturals and the generated well-founded material sets are derived as
representations of the same polynomial, using their primitive constructors.
The generated material carrier is then identified with the existing natural
ordinal set. Constructor preservation determines the resulting comparison;
neither a chosen enumeration nor an ambient hyperset bijection is assumed.

These equivalences are semantic. They do not supply executable set decoding
or an external-kernel certificate for an elaborated Lean declaration.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.NaturalAlgebraRepresentation
open IndexedPolynomial IndexedPolynomial.Algebra
universe u

def polynomial : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Bool
  Position shape := match shape with | false => Empty | true => Unit
  next _ _ := ()

def unaryAlgebra {A : Type u} (zero : A) (successor : A → A) :
    Algebra polynomial (fun _ _ => A) where
  act _ _ layer := match layer with
    | ⟨false, _⟩ => zero
    | ⟨true, children⟩ => successor (children ())

theorem unaryAlgebra_injective {A : Type u} (zero : A) (successor : A → A)
    (separate : ∀ value, successor value ≠ zero) (injective : Function.Injective successor) :
    ∀ base index, Function.Injective ((unaryAlgebra zero successor).act base index) := by
  intro base index ⟨first, children⟩ ⟨second, other⟩ same
  cases first <;> cases second
  · apply congrArg (Sigma.mk false)
    funext impossible
    exact nomatch impossible
  · exact False.elim (separate (other ()) same.symm)
  · exact False.elim (separate (children ()) same)
  · apply congrArg (Sigma.mk true)
    funext position
    cases position
    exact injective same

def hostAlgebra := unaryAlgebra 0 Nat.succ

theorem host_generated : ∀ base index value, Generated hostAlgebra base index value := by
  intro base index value
  cases base
  cases index
  induction value with
  | zero =>
      exact generated_closed hostAlgebra () () false (fun impossible => nomatch impossible)
        (fun impossible => nomatch impossible)
  | succ value previous => exact generated_closed hostAlgebra () () true (fun _ => value) (fun _ => previous)

noncomputable def hostRepresentation : Representation polynomial hostAlgebra :=
  representationOfGeneration hostAlgebra
    (generatedAlgebra_injective hostAlgebra
      (unaryAlgebra_injective 0 Nat.succ Nat.succ_ne_zero (fun _ _ same => Nat.succ.inj same))) host_generated

theorem unaryAlgebra_generated_injective {A : Type u} (zero : A) (successor : A → A)
    (separate : ∀ value, Generated (unaryAlgebra zero successor) () () value → successor value ≠ zero)
    (injective : ∀ first second,
      Generated (unaryAlgebra zero successor) () () first →
      Generated (unaryAlgebra zero successor) () () second →
      successor first = successor second → first = second) :
    ∀ base index, Function.Injective ((generatedAlgebra (unaryAlgebra zero successor)).act base index) := by
  intro base index ⟨first, children⟩ ⟨second, other⟩ same
  cases base
  cases index
  cases first <;> cases second
  · apply congrArg (Sigma.mk false)
    funext impossible
    exact nomatch impossible
  · exact False.elim (separate (other ()).val (other ()).property (congrArg Subtype.val same).symm)
  · exact False.elim (separate (children ()).val (children ()).property (congrArg Subtype.val same))
  · apply congrArg (Sigma.mk true)
    funext position
    cases position
    apply Subtype.ext
    exact injective _ _ (children ()).property (other ()).property (congrArg Subtype.val same)

def setSuccessor (value : WellFoundedPart.{u}) : WellFoundedPart.{u} :=
  ⟨insert value.val value.val, value.property.insert value.property⟩

private theorem wf_membership_asymm {x : HSet.{u}} (wellFounded : x.WF) :
    ∀ y : HSet.{u}, y ∈ x → x ∉ y := by
  induction wellFounded with
  | intro x before previous =>
      intro y member reverse
      exact previous y member x reverse member

theorem setSuccessor_ne_empty (value : WellFoundedPart.{u}) : setSuccessor value ≠ WellFoundedPart.empty := by
  intro same
  have member : value.val ∈ (setSuccessor value).val := HSet.mem_insert_iff.mpr (Or.inl rfl)
  have sets : (setSuccessor value).val = (∅ : HSet.{u}) := congrArg Subtype.val same
  rw [sets] at member
  exact HSet.notMem_empty value.val member

theorem setSuccessor_injective : Function.Injective (setSuccessor : WellFoundedPart.{u} → WellFoundedPart.{u}) := by
  intro first second same
  have sets := congrArg Subtype.val same
  have firstMember : first.val ∈ (setSuccessor second).val :=
    sets ▸ HSet.mem_insert_iff.mpr (Or.inl rfl : first.val = first.val ∨ first.val ∈ first.val)
  have secondMember : second.val ∈ (setSuccessor first).val :=
    sets.symm ▸ HSet.mem_insert_iff.mpr (Or.inl rfl : second.val = second.val ∨ second.val ∈ second.val)
  rcases HSet.mem_insert_iff.mp firstMember with equal | member
  · exact Subtype.ext equal
  · rcases HSet.mem_insert_iff.mp secondMember with equal | reverse
    · exact Subtype.ext equal.symm
    · exact False.elim (wf_membership_asymm first.property second.val reverse member)

def setAlgebra : Algebra polynomial (fun _ _ => HSet.{u}) :=
  unaryAlgebra ∅ NaturalOrdinalModel.successor

theorem generated_wellFounded (base : Unit) (index : Unit) (value : HSet.{u})
    (generated : Generated setAlgebra base index value) : value.WF := by
  apply generated (fun _ _ candidate => candidate.WF)
  intro _ _ shape children hypotheses
  cases shape with
  | false => exact HSet.wf_empty
  | true => exact (hypotheses ()).insert (hypotheses ())

theorem quine_not_generated : ¬ Generated setAlgebra () () (HSet.quineAtom.{u}) :=
  fun generated => HSet.not_wf_quineAtom (generated_wellFounded () () HSet.quineAtom generated)

theorem setAlgebra_generated_injective :
    ∀ base index, Function.Injective ((generatedAlgebra setAlgebra.{u}).act base index) := by
  apply unaryAlgebra_generated_injective
  · intro value generated same
    exact setSuccessor_ne_empty ⟨value, generated_wellFounded () () value generated⟩ (Subtype.ext same)
  · intro first second firstGenerated secondGenerated same
    have compared := setSuccessor_injective
      (a₁ := ⟨first, generated_wellFounded () () first firstGenerated⟩)
      (a₂ := ⟨second, generated_wellFounded () () second secondGenerated⟩) (Subtype.ext same)
    exact congrArg Subtype.val compared

noncomputable def setRepresentation : Representation polynomial (generatedAlgebra setAlgebra.{u}) :=
  generatedRepresentation setAlgebra setAlgebra_generated_injective

theorem ordinal_generated (number : Nat) :
    Generated setAlgebra.{u} () () (NaturalOrdinalModel.ordinal number) := by
  induction number with
  | zero =>
      rw [NaturalOrdinalModel.ordinal_zero]
      exact generated_closed setAlgebra () () false (fun impossible => nomatch impossible)
        (fun impossible => nomatch impossible)
  | succ number previous =>
      rw [NaturalOrdinalModel.ordinal_successor]
      exact generated_closed setAlgebra () () true (fun _ => NaturalOrdinalModel.ordinal number) (fun _ => previous)

theorem generated_iff_natural (value : HSet.{u}) :
    Generated setAlgebra () () value ↔ value ∈ NaturalOrdinalModel.naturals := by
  constructor
  · intro generated
    apply generated (fun _ _ candidate => candidate ∈ NaturalOrdinalModel.naturals)
    intro base index shape children hypotheses
    cases shape with
    | false => exact NaturalOrdinalModel.zero_member_naturals
    | true => exact NaturalOrdinalModel.successor_member_naturals (hypotheses ())
  · intro member
    obtain ⟨number, same⟩ := (NaturalOrdinalModel.member_naturals value).mp member
    exact same ▸ ordinal_generated number

def generatedToNaturalMembers : GeneratedCarrier setAlgebra.{u} () () ≃
    {value : HSet.{u} // value ∈ NaturalOrdinalModel.naturals} where
  toFun value := ⟨value.val, (generated_iff_natural value.val).mp value.property⟩
  invFun value := ⟨value.val, (generated_iff_natural _).mpr value.property⟩
  left_inv value := by apply Subtype.ext; rfl
  right_inv value := by apply Subtype.ext; rfl

noncomputable def comparison : Iso hostAlgebra (generatedAlgebra setAlgebra.{u}) :=
  Representation.change hostRepresentation setRepresentation

noncomputable def naturalEquivalence : Nat ≃ {value : HSet.{u} // value ∈ NaturalOrdinalModel.naturals} :=
  (comparison.toEquiv () ()).trans generatedToNaturalMembers

theorem naturalEquivalence_zero : (naturalEquivalence.{u} 0).val = ∅ := by
  have law := comparison.{u}.commutes () ()
    (⟨false, fun impossible => nomatch impossible⟩ : polynomial.Extension (fun _ _ => Nat) () ())
  exact congrArg (fun value => value.val) law

theorem naturalEquivalence_successor (number : Nat) :
    (naturalEquivalence.{u} (number + 1)).val =
      NaturalOrdinalModel.successor (naturalEquivalence number).val := by
  have law := comparison.{u}.commutes () ()
    (⟨true, fun _ => number⟩ : polynomial.Extension (fun _ _ => Nat) () ())
  exact congrArg (fun value => value.val) law

theorem naturalEquivalence_ordinal (number : Nat) :
    (naturalEquivalence.{u} number).val = NaturalOrdinalModel.ordinal number := by
  induction number with
  | zero => exact naturalEquivalence_zero.trans NaturalOrdinalModel.ordinal_zero.symm
  | succ number previous =>
      rw [naturalEquivalence_successor, previous]
      exact (NaturalOrdinalModel.ordinal_successor number).symm

theorem comparison_retains_membership (number : Nat) :
    (naturalEquivalence.{u} number).val ∈ NaturalOrdinalModel.naturals :=
  (naturalEquivalence number).property

theorem comparison_refuses_quine (number : Nat) :
    (naturalEquivalence.{u} number).val ≠ HSet.quineAtom := by
  intro same
  exact NaturalOrdinalModel.Controls.quine_not_natural (same ▸ comparison_retains_membership number)

#print axioms setSuccessor_injective
#print axioms setRepresentation
#print axioms generated_iff_natural
#print axioms naturalEquivalence
#print axioms naturalEquivalence_successor
#print axioms comparison_refuses_quine
end Mettapedia.TypeTheory.MaterialSets.Hypersets.NaturalAlgebraRepresentation
