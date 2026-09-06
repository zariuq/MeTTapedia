import Mettapedia.TypeTheory.CwfSimpleDependentInstitution

/-!
# When simple types suffice: the descent criterion

The simple-families institution sits inside the dependent-families
institution by the constant-family route.  This module states the boundary
exactly.

* The global-inhabitation institution of a CwF is a logical readout: a point
  satisfies a type when the fibre is inhabited.  It identifies distinct types
  with inhabited fibres, so it is not a semantics of terms.
* A dependent family over an inhabited context descends to a simple type
  exactly when it is constant.  Simple types suffice for precisely the
  families that descend.
* On the constant-family image the route is exact: a simple theorem transports
  to the dependent side and back.
* The varying Boolean family is outside the image, and transport along a
  path in it is a genuinely dependent elimination: it refutes the path
  `false = true`.  Transport in the family of finite types is another, with
  the computation rule at reflexivity.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DependencyDescentCriterion

open Mettapedia.Logic
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.CwfInhabitationInstitution
open Mettapedia.TypeTheory.CwfSimpleDependentInstitution

/-! ## The global-inhabitation institution is a readout -/

/-- Point-satisfaction reads inhabitation only: the constant families at
`PUnit` and at `Bool` are distinct sentences satisfied by the same points. -/
theorem readout_identifies_inhabited_types :
    (∀ point : dependentInstitution.model.obj (Opposite.op boolContext),
      dependentInstitution.satisfies boolContext point (constantFamily PUnit) ↔
        dependentInstitution.satisfies boolContext point (constantFamily Bool)) ∧
      constantFamily (Γ := Bool) PUnit ≠ constantFamily Bool := by
  refine ⟨fun _ => ⟨fun _ => ⟨fun _ => true⟩, fun _ => ⟨fun _ => PUnit.unit⟩⟩, ?_⟩
  intro equal
  have typesEqual : (PUnit : Type) = Bool := congrFun equal true
  have equivalence : PUnit ≃ Bool := Equiv.cast typesEqual
  exact Bool.false_ne_true (equivalence.symm.injective (Subsingleton.elim _ _))

/-! ## The descent criterion -/

/-- A family over an inhabited context is a simple type exactly when it is
constant: simple types suffice for the families that descend. -/
theorem descends_iff_constant {Γ : Type} [Nonempty Γ] (family : familiesCwf.Ty Γ) :
    (∃ type : Type, family = constantFamily type) ↔
      ∀ left right, family left = family right := by
  constructor
  · rintro ⟨type, rfl⟩ left right
    rfl
  · intro constant
    obtain ⟨point⟩ := ‹Nonempty Γ›
    exact ⟨family point, funext fun other => constant other point⟩

/-! ## Exactness and transport on the image -/

/-- A simple theorem, the identity function type, transports to the
dependent side; exactness on the image is `entails_iff`. -/
theorem identity_transports :
    dependentInstitution.Entails boolContext ∅ (constantFamily (Bool → Bool)) := by
  have simple : simpleInstitution.Entails simpleBoolContext ∅ (Bool → Bool) :=
    fun _ _ => ⟨fun _ => id⟩
  have transported := (entails_iff simpleBoolContext ∅ (Bool → Bool)).1 simple
  rw [Set.image_empty] at transported
  exact transported

/-! ## Outside the image -/

/-- The varying family is no translated simple type. -/
theorem varying_outside_image :
    ¬ ∃ type : Type, mapSentence.app simpleBoolContext type = varyingBoolFamily := by
  rintro ⟨type, equal⟩
  exact varyingBoolFamily_not_constant ⟨type, equal.symm⟩

/-! ## Genuinely dependent transport -/

/-- Transport along a path in the varying family is dependent elimination: a
path `false = true` would carry the unit of the singleton fibre into the
empty fibre. -/
theorem no_path_false_true : ¬ ((false : Bool) = true) := by
  intro path
  have transported : varyingBoolFamily true :=
    path ▸ (PUnit.unit : varyingBoolFamily false)
  cases transported

/-- Transport in the family of finite types along a path of indices. -/
def finTransport {left right : Nat} (path : left = right) : Fin left → Fin right :=
  fun index => path ▸ index

/-- The computation rule of transport at reflexivity. -/
theorem finTransport_refl (index : Nat) : finTransport (rfl : index = index) = id :=
  rfl

/-- The family of finite types is not constant, so its transport is not
available at the simple level. -/
theorem finFamily_not_constant :
    ¬ ∃ type : Type, (fun index : Nat => Fin index) = constantFamily type := by
  rintro ⟨type, equal⟩
  have zero : Fin 0 = type := congrFun equal 0
  have one : Fin 1 = type := congrFun equal 1
  have equivalence : Fin 0 ≃ Fin 1 := Equiv.cast (zero.trans one.symm)
  exact Fin.elim0 (equivalence.symm 0)

#print axioms readout_identifies_inhabited_types
#print axioms descends_iff_constant
#print axioms identity_transports
#print axioms varying_outside_image
#print axioms no_path_false_true
#print axioms finFamily_not_constant

end Mettapedia.TypeTheory.DependencyDescentCriterion
