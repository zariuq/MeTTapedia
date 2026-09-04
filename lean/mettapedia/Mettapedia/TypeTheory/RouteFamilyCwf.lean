import Mettapedia.GSLT.Core.ContextualLadderTerminal
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes

/-!
# The CwF of route-indexed families

An intensional `RouteType` carries a reflexive relation.  A dependent type
over it must say how values move along every route; an arbitrary family of
types over the carrier is not enough.  This module equips route types with
their resulting category-with-families structure:

* contexts are route types;
* substitutions are route-preserving maps;
* types are families with a chosen transport along every route;
* terms are transport-preserving sections; and
* comprehension is the dependent total route type.

The construction is a split displayed reflexive-graph semantics.  It does
not assume transitivity of routes and therefore does not silently replace the
declared route relation by its reflexive-transitive closure.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.RouteFamilyCwf

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes

universe u

/-! ## The strict category operations used by the CwF -/

/-- Identity route substitution, exposed independently of category notation
so the CwF laws reduce without typeclass elaboration. -/
def routeIdentity (context : RouteType.{u}) : RouteHom context context where
  toFun point := point
  map_route route := route

/-- Composition of route substitutions in execution order. -/
def routeCompose {first middle last : RouteType.{u}}
    (earlier : RouteHom first middle) (later : RouteHom middle last) :
    RouteHom first last where
  toFun point := later.toFun (earlier.toFun point)
  map_route route := later.map_route (earlier.map_route route)

/-! ## Route-indexed dependent types and terms -/

/-- A dependent family over a route type, with chosen transport along every
declared route.  Only the reflexivity law is required because `RouteType`
itself assumes no route composition. -/
structure RouteFamily (context : RouteType.{u}) : Type (u + 1) where
  fibre : context.carrier -> Type u
  transport : {source target : context.carrier} ->
    context.Route source target -> fibre source -> fibre target
  transport_refl : forall (point : context.carrier) (value : fibre point),
    transport (context.route_refl point) value = value

namespace RouteFamily

/-- Equality of route families is determined by their fibre and transport
operations; the reflexivity field is propositional. -/
theorem ext {context : RouteType.{u}} {left right : RouteFamily context}
    (sameFibre : left.fibre = right.fibre)
    (sameTransport :
      HEq (@RouteFamily.transport _ left) (@RouteFamily.transport _ right)) :
    left = right := by
  cases left
  cases right
  cases sameFibre
  cases sameTransport
  rfl

/-- Pull a route family back along a route-preserving map. -/
def reindex {source target : RouteType.{u}} (family : RouteFamily target)
    (substitution : RouteHom source target) : RouteFamily source where
  fibre point := family.fibre (substitution.toFun point)
  transport route := family.transport (substitution.map_route route)
  transport_refl point value := by
    have sameRoute :
        substitution.map_route (source.route_refl point) =
          target.route_refl (substitution.toFun point) :=
      Subsingleton.elim _ _
    rw [sameRoute]
    exact family.transport_refl _ value

@[simp]
theorem reindex_fibre {source target : RouteType.{u}}
    (family : RouteFamily target) (substitution : RouteHom source target)
    (point : source.carrier) :
    (family.reindex substitution).fibre point =
      family.fibre (substitution.toFun point) :=
  rfl

@[simp]
theorem reindex_transport {source target : RouteType.{u}}
    (family : RouteFamily target) (substitution : RouteHom source target)
    {first last : source.carrier} (route : source.Route first last)
    (value : family.fibre (substitution.toFun first)) :
    (family.reindex substitution).transport route value =
      family.transport (substitution.map_route route) value :=
  rfl

@[simp]
theorem reindex_identity {context : RouteType.{u}}
    (family : RouteFamily context) :
    family.reindex (routeIdentity context) = family :=
  rfl

@[simp]
theorem reindex_composite {first middle last : RouteType.{u}}
    (family : RouteFamily last) (earlier : RouteHom first middle)
    (later : RouteHom middle last) :
    family.reindex (routeCompose earlier later) =
      (family.reindex later).reindex earlier :=
  rfl

/-- A route-insensitive family has one fixed fibre and identity transport. -/
def constant (context : RouteType.{u}) (valueType : Type u) :
    RouteFamily context where
  fibre _ := valueType
  transport _ value := value
  transport_refl _ _ := rfl

@[simp]
theorem constant_reindex {source target : RouteType.{u}}
    (substitution : RouteHom source target) (valueType : Type u) :
    (constant target valueType).reindex substitution =
      constant source valueType :=
  rfl

end RouteFamily

/-- A term of a route family is a section that commutes with all route
transport. -/
structure RouteSection {context : RouteType.{u}}
    (family : RouteFamily context) : Type u where
  value : forall point : context.carrier, family.fibre point
  natural : forall {source target : context.carrier}
    (route : context.Route source target),
    family.transport route (value source) = value target

namespace RouteSection

/-- Route sections are equal when their values agree; naturality proofs are
propositional. -/
@[ext]
theorem ext {context : RouteType.{u}} {family : RouteFamily context}
    {left right : RouteSection family}
    (sameValue : left.value = right.value) : left = right := by
  cases left
  cases right
  cases sameValue
  rfl

/-- Reindex a section along a route-preserving substitution. -/
def reindex {source target : RouteType.{u}} {family : RouteFamily target}
    (term : RouteSection family) (substitution : RouteHom source target) :
    RouteSection (family.reindex substitution) where
  value point := term.value (substitution.toFun point)
  natural route := term.natural (substitution.map_route route)

@[simp]
theorem reindex_value {source target : RouteType.{u}}
    {family : RouteFamily target} (term : RouteSection family)
    (substitution : RouteHom source target) (point : source.carrier) :
    (term.reindex substitution).value point =
      term.value (substitution.toFun point) :=
  rfl

end RouteSection

/-! ## Comprehension -/

/-- Extend a route context by a route-indexed family.  A total-space route
consists of a base route whose chosen transport sends the source value to the
target value. -/
def extend (context : RouteType.{u}) (family : RouteFamily context) :
    RouteType.{u} where
  carrier := Sigma family.fibre
  Route source target :=
    Exists fun route : context.Route source.1 target.1 =>
      family.transport route source.2 = target.2
  route_refl point :=
    Exists.intro (context.route_refl point.1)
      (family.transport_refl point.1 point.2)

/-- The first projection from comprehension is route preserving. -/
def weaken {context : RouteType.{u}} (family : RouteFamily context) :
    RouteHom (extend context family) context where
  toFun point := point.1
  map_route route := by
    rcases route with ⟨baseRoute, _⟩
    exact baseRoute

/-- The final variable is a section of the reindexed family over its
comprehension context. -/
def lastVariable {context : RouteType.{u}} (family : RouteFamily context) :
    RouteSection (family.reindex (weaken family)) where
  value point := point.2
  natural route := by
    rcases route with ⟨_, transported⟩
    exact transported

/-- Pair a substitution with a term to obtain a substitution into
comprehension. -/
def pair {source target : RouteType.{u}}
    (substitution : RouteHom source target) (family : RouteFamily target)
    (term : RouteSection (family.reindex substitution)) :
    RouteHom source (extend target family) where
  toFun point := ⟨substitution.toFun point, term.value point⟩
  map_route route :=
    Exists.intro (substitution.map_route route) (term.natural route)

@[simp]
theorem weaken_pair {source target : RouteType.{u}}
    (substitution : RouteHom source target) (family : RouteFamily target)
    (term : RouteSection (family.reindex substitution)) :
    routeCompose (pair substitution family term) (weaken family) =
      substitution := by
  apply RouteHom.ext
  intro point
  rfl

/-! ## The route-family CwF -/

/-- Route types, route-preserving maps, transported families, and natural
sections form a genuine category with families. -/
def routeCwf : Cwf.{u + 1, u, u + 1, u} where
  Ctx := RouteType.{u}
  Sub := RouteHom
  idS := routeIdentity
  compS later earlier := routeCompose earlier later
  id_comp substitution := by
    apply RouteHom.ext
    intro point
    rfl
  comp_id substitution := by
    apply RouteHom.ext
    intro point
    rfl
  comp_assoc later middle earlier := by
    apply RouteHom.ext
    intro point
    rfl
  Ty := RouteFamily
  tySub family substitution := family.reindex substitution
  tySub_id family := RouteFamily.reindex_identity family
  tySub_comp family later earlier :=
    RouteFamily.reindex_composite family earlier later
  Tm _ family := RouteSection family
  tmSub term substitution := term.reindex substitution
  tmSub_id term := by
    apply RouteSection.ext
    rfl
  tmSub_comp term later earlier := by
    apply RouteSection.ext
    rfl
  ext := extend
  wk family := weaken family
  vz family := lastVariable family
  pair substitution family term := pair substitution family term
  wk_pair substitution family term := weaken_pair substitution family term
  vz_pair substitution family term := by
    apply RouteSection.ext
    rfl
  pair_eta family substitution := by
    apply RouteHom.ext
    intro point
    apply Sigma.ext rfl
    exact HEq.rfl

/-! ## Terminal context -/

/-- The one-point discrete route context. -/
def empty : RouteType.{u} where
  carrier := PUnit
  Route := Eq
  route_refl _ := rfl

/-- Every route context has its unique substitution into `empty`. -/
def toEmpty (context : RouteType.{u}) : RouteHom context empty where
  toFun _ := PUnit.unit
  map_route _ := rfl

/-- The route-family CwF with its chosen terminal context. -/
def routeCwfWithTerminal : CwfWithTerminal.{u + 1, u, u + 1, u} where
  toCwf := routeCwf.{u}
  empty := empty.{u}
  toEmpty := toEmpty
  toEmpty_unique := by
    intro context substitution
    apply RouteHom.ext
    intro point
    cases substitution.toFun point
    rfl

/-! ## Readout-pulled families -/

/-- Pull an extensional family over the quotient readout back to an
intensional route context.  Route transport is equality transport along
`Quot.sound`. -/
def pullbackReadoutFamily (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u) :
    RouteFamily context where
  fibre point := family (Quot.mk context.Route point)
  transport route value :=
    cast (congrArg family (Quot.sound route)) value
  transport_refl point value := by
    have sameEquality :
        Quot.sound (context.route_refl point) =
          (rfl : Quot.mk context.Route point = Quot.mk context.Route point) :=
      Subsingleton.elim _ _
    rw [sameEquality]
    rfl

@[simp]
theorem pullbackReadoutFamily_fibre (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u)
    (point : context.carrier) :
    (pullbackReadoutFamily context family).fibre point =
      family (Quot.mk context.Route point) :=
  rfl

/-! ## Positive and negative controls -/

namespace Canary

/-- A nonconstant family over a discrete Boolean route context. -/
def discreteBoolFamily : RouteFamily (discreteOn.obj ⟨Bool⟩) where
  fibre
    | false => PUnit
    | true => Bool
  transport route := by
    cases route
    exact id
  transport_refl point value := by
    cases point <;> rfl

/-- A section of the nonconstant discrete family. -/
def discreteBoolSection : RouteSection discreteBoolFamily where
  value
    | false => PUnit.unit
    | true => false
  natural route := by
    cases route
    rfl

/-- A genuine nonconstant transported family over the codiscrete Boolean
route context.  Directed transports exist in both directions, but they are
not required to be inverse because the base relation has no composition law. -/
def codiscreteVaryingFamily : RouteFamily codiscretePair where
  fibre
    | false => PUnit
    | true => Bool
  transport {source target} _ := by
    cases source <;> cases target
    · exact id
    · exact fun _ => false
    · exact fun _ => PUnit.unit
    · exact id
  transport_refl point value := by
    cases point <;> rfl

/-- The varying codiscrete family has a route-natural section. -/
def codiscreteVaryingSection : RouteSection codiscreteVaryingFamily where
  value
    | false => PUnit.unit
    | true => false
  natural {source target} _ := by
    cases source <;> cases target <;> rfl

/-- The varying family really has inequivalent endpoint fibres. -/
theorem discreteBoolFamily_fibres_not_equiv :
    ¬ Nonempty
      (discreteBoolFamily.fibre false ≃
        discreteBoolFamily.fibre true) := by
  rintro ⟨equivalence⟩
  have allEqual : forall value : Bool, value = equivalence PUnit.unit := by
    intro value
    rcases equivalence.surjective value with ⟨source, sourceImage⟩
    cases source
    exact sourceImage.symm
  exact Bool.false_ne_true
    ((allEqual false).trans (allEqual true).symm)

/-- The same endpoint fibres remain inequivalent in the genuine codiscrete
transported family. -/
theorem codiscreteVaryingFamily_fibres_not_equiv :
    ¬ Nonempty
      (codiscreteVaryingFamily.fibre false ≃
        codiscreteVaryingFamily.fibre true) :=
  discreteBoolFamily_fibres_not_equiv

/-- Reindexing the nonconstant family along Boolean negation swaps its
endpoint fibres and is not the original family. -/
def discreteNegation :
    RouteHom (discreteOn.obj ⟨Bool⟩) (discreteOn.obj ⟨Bool⟩) where
  toFun := Bool.not
  map_route route := congrArg Bool.not route

theorem discreteBoolFamily_reindex_negation_ne :
    discreteBoolFamily.reindex discreteNegation ≠ discreteBoolFamily := by
  intro sameFamily
  have sameFalseFibre := congrArg
    (fun family : RouteFamily (discreteOn.obj ⟨Bool⟩) => family.fibre false)
    sameFamily
  change Bool = PUnit at sameFalseFibre
  have equivalence : Bool ≃ PUnit := Equiv.cast sameFalseFibre
  exact discreteBoolFamily_fibres_not_equiv
    ⟨equivalence.symm⟩

/-- Constant route families are stable under the same nonidentity
substitution. -/
theorem constantBool_reindex_negation :
    (RouteFamily.constant (discreteOn.obj ⟨Bool⟩) Bool).reindex
        discreteNegation =
      RouteFamily.constant (discreteOn.obj ⟨Bool⟩) Bool :=
  RouteFamily.constant_reindex discreteNegation Bool

/-- The terminal context has the promised unique-map property. -/
theorem empty_maps_equal (context : RouteType.{u})
    (left right : routeCwf.{u}.Sub context empty) : left = right := by
  exact (routeCwfWithTerminal.{u}.emptyUniversal context).uniq left |>.trans
    ((routeCwfWithTerminal.{u}.emptyUniversal context).uniq right).symm

end Canary

#print axioms RouteFamily.reindex_identity
#print axioms RouteFamily.reindex_composite
#print axioms weaken_pair
#print axioms routeCwf
#print axioms routeCwfWithTerminal
#print axioms pullbackReadoutFamily
#print axioms Canary.discreteBoolFamily_fibres_not_equiv
#print axioms Canary.codiscreteVaryingFamily
#print axioms Canary.codiscreteVaryingSection
#print axioms Canary.codiscreteVaryingFamily_fibres_not_equiv
#print axioms Canary.discreteBoolFamily_reindex_negation_ne
#print axioms Canary.constantBool_reindex_negation
#print axioms Canary.empty_maps_equal

end Mettapedia.TypeTheory.RouteFamilyCwf
