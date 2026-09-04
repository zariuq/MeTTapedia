import Mettapedia.GSLT.Core.ContextualTypeReindexing
import Mettapedia.GSLT.Core.LooseRelationCompanions

/-!
# Reindexing dependent families along represented loose routes

A category with families reindexes types and terms along substitutions.  The
loose arrows of the route equipment are more general: they may be partial,
nondeterministic, or retain several pieces of evidence for the same visible
endpoint.  Such an arrow does not automatically determine a substitution.

This module identifies the exact bridge.  An exact `Representation` of a
loose arrow by the companion of a function supplies a substitution in the
set-families CwF, and hence reindexing of types, terms, and display maps.  The
action is independent of the chosen representation proof and respects
horizontal composition contravariantly.

The negative control has only one visible source and target, so an endpoint
function and its ordinary CwF reindexing certainly exist.  It nevertheless
retains two route witnesses.  Therefore it has no exact representation and
the endpoint action cannot stand in for the proof-relevant route.  This keeps
relational computation strictly more general than contextual substitution.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ContextualRouteReindexing

open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.Core.ContextualLadder
open CategoryTheory

universe u

/-- The substitution in the set-families CwF selected by an exact
representation of a loose route. -/
def substitution {Source Target : Type u}
    {relation : Loose Source Target}
    (representation : Representation relation) :
    familiesCwf.Sub Source Target :=
  representation.map

/-- Reindex a dependent type family along a represented loose route. -/
def reindexType {Source Target : Type u}
    {relation : Loose Source Target}
    (representation : Representation relation)
    (family : Target → Type u) : Source → Type u :=
  familiesCwf.tySub family (substitution representation)

/-- Reindex a section of a dependent family along a represented loose
route. -/
def reindexTerm {Source Target : Type u}
    {relation : Loose Source Target}
    (representation : Representation relation)
    {family : Target → Type u} (term : ∀ target, family target) :
    ∀ source, reindexType representation family source :=
  familiesCwf.tmSub term (substitution representation)

/-- A represented route also acts on the category of display maps over the
target context. -/
def reindexDisplay {Source Target : Type u}
    {relation : Loose Source Target}
    (representation : Representation relation) :
    TypeOver familiesCwf Target ⥤ TypeOver familiesCwf Source :=
  TypeOver.reindexFunctor (substitution representation)

@[simp] theorem substitution_apply {Source Target : Type u}
    {relation : Loose Source Target}
    (representation : Representation relation) (source : Source) :
    substitution representation source = representation.map source :=
  rfl

@[simp] theorem reindexType_apply {Source Target : Type u}
    {relation : Loose Source Target}
    (representation : Representation relation)
    (family : Target → Type u) (source : Source) :
    reindexType representation family source =
      family (representation.map source) :=
  rfl

@[simp] theorem reindexTerm_apply {Source Target : Type u}
    {relation : Loose Source Target}
    (representation : Representation relation)
    {family : Target → Type u} (term : ∀ target, family target)
    (source : Source) :
    reindexTerm representation term source =
      term (representation.map source) :=
  rfl

@[simp] theorem reindexDisplay_object {Source Target : Type u}
    {relation : Loose Source Target}
    (representation : Representation relation)
    (family : TypeOver familiesCwf Target) :
    ((reindexDisplay representation).obj family).val =
      reindexType representation family.val :=
  rfl

/-- Horizontal composition of represented routes becomes ordinary CwF
substitution composition. -/
@[simp] theorem substitution_horizontalComp
    {First Middle Last : Type u}
    {earlier : Loose First Middle} {later : Loose Middle Last}
    (earlierRepresentation : Representation earlier)
    (laterRepresentation : Representation later) :
    substitution
        (Representation.horizontalComp earlierRepresentation
          laterRepresentation) =
      familiesCwf.compS (substitution laterRepresentation)
        (substitution earlierRepresentation) :=
  rfl

/-- Type reindexing is contravariantly compatible with horizontal route
composition. -/
@[simp] theorem reindexType_horizontalComp
    {First Middle Last : Type u}
    {earlier : Loose First Middle} {later : Loose Middle Last}
    (earlierRepresentation : Representation earlier)
    (laterRepresentation : Representation later)
    (family : Last → Type u) :
    reindexType
        (Representation.horizontalComp earlierRepresentation
          laterRepresentation) family =
      reindexType earlierRepresentation
        (reindexType laterRepresentation family) :=
  rfl

/-- Term reindexing obeys the same contravariant composition law. -/
@[simp] theorem reindexTerm_horizontalComp
    {First Middle Last : Type u}
    {earlier : Loose First Middle} {later : Loose Middle Last}
    (earlierRepresentation : Representation earlier)
    (laterRepresentation : Representation later)
    {family : Last → Type u} (term : ∀ last, family last) :
    reindexTerm
        (Representation.horizontalComp earlierRepresentation
          laterRepresentation) term =
      reindexTerm earlierRepresentation
        (reindexTerm laterRepresentation term) :=
  rfl

/-- Equal endpoint maps induce heterogeneously equal dependent
precompositions. -/
theorem precomposeTerm_heq_of_map_eq
    {Source Target : Type u} {family : Target → Type u}
    (term : ∀ target, family target) {firstMap secondMap : Source → Target}
    (sameMap : firstMap = secondMap) :
    HEq (fun source => term (firstMap source))
      (fun source => term (secondMap source)) := by
  cases sameMap
  rfl

/-- Exact representability makes the induced type action independent of the
particular proof that admitted the route. -/
theorem reindexType_representation_independent
    {Source Target : Type u} {relation : Loose Source Target}
    (first second : Representation relation)
    (family : Target → Type u) :
    reindexType first family = reindexType second family := by
  unfold reindexType substitution
  rw [Representation.map_unique first second]

/-- The corresponding term actions agree as dependent terms. -/
theorem reindexTerm_representation_independent
    {Source Target : Type u} {relation : Loose Source Target}
    (first second : Representation relation)
    {family : Target → Type u} (term : ∀ target, family target) :
    HEq (reindexTerm first term) (reindexTerm second term) := by
  exact precomposeTerm_heq_of_map_eq term
    (Representation.map_unique first second)

/-! ## A proof-relevant non-collapse control -/

/-- One visible endpoint with two distinct route witnesses. -/
def duplicateWitnessRoute : Loose PUnit PUnit :=
  fun _ _ => Bool

/-- The visible endpoint map exists and is unique for the one-point
contexts. -/
def duplicateWitnessEndpoint : PUnit → PUnit :=
  fun _ => PUnit.unit

/-- Reindexing along the visible endpoint map is the identity action on
families over the one-point context. -/
theorem duplicateWitnessEndpoint_reindexType
    (family : PUnit → Type u) :
    familiesCwf.tySub family duplicateWitnessEndpoint = family := by
  funext point
  cases point
  rfl

/-- The route is total even though it retains duplicate evidence. -/
theorem duplicateWitnessRoute_total : Total duplicateWitnessRoute := by
  intro source
  exact ⟨⟨PUnit.unit, false⟩⟩

/-- Duplicate route witnesses violate proof-relevant determinism. -/
theorem duplicateWitnessRoute_not_deterministic :
    ¬ Deterministic duplicateWitnessRoute := by
  intro deterministic
  let fibreSubsingleton : Subsingleton
      (duplicateWitnessRoute PUnit.unit PUnit.unit) :=
    Representation.fibreSubsingleton deterministic PUnit.unit PUnit.unit
  have same : (false : Bool) = true :=
    fibreSubsingleton.allEq false true
  exact Bool.false_ne_true same

/-- Consequently the endpoint function does not license replacement of the
proof-relevant route by a CwF substitution. -/
theorem duplicateWitnessRoute_not_representable :
    ¬ Nonempty (Representation duplicateWitnessRoute) := by
  rintro ⟨representation⟩
  exact duplicateWitnessRoute_not_deterministic
    representation.deterministic

#print axioms substitution
#print axioms reindexType
#print axioms reindexTerm
#print axioms reindexDisplay
#print axioms substitution_horizontalComp
#print axioms reindexType_horizontalComp
#print axioms reindexTerm_horizontalComp
#print axioms precomposeTerm_heq_of_map_eq
#print axioms reindexType_representation_independent
#print axioms reindexTerm_representation_independent
#print axioms duplicateWitnessEndpoint_reindexType
#print axioms duplicateWitnessRoute_total
#print axioms duplicateWitnessRoute_not_deterministic
#print axioms duplicateWitnessRoute_not_representable

end Mettapedia.GSLT.Core.ContextualRouteReindexing
