import Mettapedia.TypeTheory.DecidableIdentityRouteStructure

/-!
# Ordinary equality as a decidable identity-route structure

Literal equality supplies a canonical route layer: a route from `source` to
`target` is a lifted equality proof.  This layer has groupoid operations,
external propositional identity elimination, and decidable route support
whenever the object carrier has decidable equality.

The construction is useful as a comparison object.  It characterizes the
strict endpoint-equality face without identifying operational paths,
conversion histories, or revision traces with identity proofs.  The negative
control records that unequal endpoints have no route in this layer.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.EqualityIdentityRouteStructure

open Mettapedia.TypeTheory.ScopedIdentity
open Mettapedia.TypeTheory.IdentityRouteCapabilities
open Mettapedia.TypeTheory.IdentityEliminationCapabilities
open Mettapedia.TypeTheory.DecidableIdentityRouteStructure

universe u

/-- Literal endpoint equality, lifted from `Prop` into `Type`, as a route
layer. -/
def equalityLayer (Object : Type u) : Layer Object where
  Route source target := PLift (source = target)
  refl _ := ⟨rfl⟩
  Support source target := source = target
  forget route := route.down

/-- Equality paths carry the usual groupoid operations. -/
def equalityGroupoid (Object : Type u) : RouteGroupoid (equalityLayer Object) where
  comp first second := ⟨first.down.trans second.down⟩
  inv route := ⟨route.down.symm⟩
  refl_comp := by
    intro source target route
    change (⟨rfl.trans route.down⟩ : PLift (source = target)) = route
    exact Subsingleton.elim _ _
  comp_refl := by
    intro source target route
    change (⟨route.down.trans rfl⟩ : PLift (source = target)) = route
    exact Subsingleton.elim _ _
  assoc := by
    intro first second third last earlier middle later
    change
      (⟨(earlier.down.trans middle.down).trans later.down⟩ :
        PLift (first = last)) =
      ⟨earlier.down.trans (middle.down.trans later.down)⟩
    exact Subsingleton.elim _ _
  inv_comp := by
    intro source target route
    change (⟨route.down.symm.trans route.down⟩ : PLift (target = target)) =
      ⟨rfl⟩
    exact Subsingleton.elim _ _
  comp_inv := by
    intro source target route
    change (⟨route.down.trans route.down.symm⟩ : PLift (source = source)) =
      ⟨rfl⟩
    exact Subsingleton.elim _ _

/-- Propositional identity elimination for lifted ordinary equality. -/
def equalityElimination (Object : Type u) :
    ExternalPropositionalIdentityElimination (equalityLayer Object) where
  eliminate := by
    intro source motive atRefl target route
    cases route.down
    exact atRefl

/-- Decidable equality decides whether the corresponding equality-route
fibre is inhabited. -/
def equalityDecision (Object : Type u) [DecidableEq Object] :
    RouteInhabitationDecision (equalityLayer Object) := by
  intro source target
  by_cases same : source = target
  · exact .present ⟨same⟩
  · exact .absent (fun route => same route.down)

/-- The complete decidable identity-route structure carried by ordinary
equality. -/
def equalityStructure (Object : Type u) [DecidableEq Object] :
    Structure (equalityLayer Object) where
  groupoid := equalityGroupoid Object
  elimination := equalityElimination Object
  decision := equalityDecision Object

/-- Equality routes reflect their endpoints definitionally through their
stored equality proof. -/
theorem endpointReflection (Object : Type u) :
    EndpointReflection (equalityLayer Object) :=
  fun route => route.down

/-- Every equality-route fibre is a subsingleton. -/
theorem routeUIP (Object : Type u) : RouteUIP (equalityLayer Object) := by
  intro source target
  change Subsingleton (PLift (source = target))
  infer_instance

/-- Forgetting a lifted equality proof to proposition-valued support loses no
route identity. -/
theorem supportFaithful (Object : Type u) :
    SupportFaithful (equalityLayer Object) := by
  intro source target first second _sameSupport
  change PLift (source = target) at first second
  exact Subsingleton.elim first second

/-- Equality routes exist exactly when their endpoints are equal. -/
theorem route_nonempty_iff {Object : Type u} (source target : Object) :
    Nonempty ((equalityLayer Object).Route source target) ↔ source = target := by
  constructor
  · rintro ⟨route⟩
    exact route.down
  · intro same
    exact ⟨⟨same⟩⟩

/-- Negative control: distinct endpoints have no equality route. -/
theorem no_route_of_ne {Object : Type u} {source target : Object}
    (different : source ≠ target) :
    ¬ Nonempty ((equalityLayer Object).Route source target) := by
  rw [route_nonempty_iff]
  exact different

/-! ## Compatibility with the earlier Boolean canary -/

namespace Canary

open Mettapedia.TypeTheory.IdentityRouteCapabilities.Canary

/-- The earlier Boolean lifted-equality canary is exactly the generic
construction specialized to `Bool`. -/
theorem bool_layer_agrees : equalityLayer Bool = liftedEquality :=
  rfl

/-- Positive control: Boolean equality has the complete decidable identity
structure. -/
theorem bool_has_structure :
    Nonempty (Structure (equalityLayer Bool)) :=
  ⟨equalityStructure Bool⟩

/-- Negative control: the two Boolean endpoints remain distinct in the
strict equality layer. -/
theorem false_true_have_no_route :
    ¬ Nonempty ((equalityLayer Bool).Route false true) :=
  no_route_of_ne Bool.false_ne_true

/-- The ordinary-equality comparison object has both its positive identity
structure and its endpoint-separation canary. -/
theorem equality_identity_boundary :
    Nonempty (Structure (equalityLayer Bool)) ∧
      ¬ Nonempty ((equalityLayer Bool).Route false true) :=
  ⟨bool_has_structure, false_true_have_no_route⟩

end Canary

#print axioms equalityGroupoid
#print axioms equalityElimination
#print axioms equalityDecision
#print axioms equalityStructure
#print axioms route_nonempty_iff
#print axioms no_route_of_ne
#print axioms Canary.equality_identity_boundary

end Mettapedia.TypeTheory.EqualityIdentityRouteStructure
