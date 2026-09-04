import Mettapedia.TypeTheory.CwfDependentRightAdjoint
import Mettapedia.TypeTheory.RouteFamilyCwf

/-!
# The route quotient as a dependent right adjoint

The route quotient is not a lossless pushforward of every intensional
dependent type.  It nevertheless supports the standard modal orientation:

* `routeQuotient` acts on contexts and substitutions;
* an extensional family over the quotient context pulls back to a transported
  route family; and
* extensional sections are naturally equivalent to route-natural sections of
  that pulled-back family.

The reverse half of the term equivalence is genuine quotient descent.  A
route-natural section first induces a relation-invariant map into the
dependent total space; quotient lifting then recovers the extensional
section.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.RouteQuotientDependentRightAdjoint

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.CwfDependentRightAdjoint
open Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes
open Mettapedia.TypeTheory.RouteFamilyCwf

universe u

/-! ## The extensional family CwF -/

/-- Identity substitution of extensional contexts. -/
def extIdentity (context : ExtType.{u}) : ExtHom context context where
  toFun point := point

/-- Composition of extensional substitutions. -/
def extCompose {first middle last : ExtType.{u}}
    (earlier : ExtHom first middle) (later : ExtHom middle last) :
    ExtHom first last where
  toFun point := later.toFun (earlier.toFun point)

/-- Bare extensional contexts carry the ordinary set-family CwF. -/
def extCwf : Cwf.{u + 1, u, u + 1, u} where
  Ctx := ExtType.{u}
  Sub := ExtHom
  idS := extIdentity
  compS later earlier := extCompose earlier later
  id_comp substitution := by
    apply ExtHom.ext
    intro point
    rfl
  comp_id substitution := by
    apply ExtHom.ext
    intro point
    rfl
  comp_assoc later middle earlier := by
    apply ExtHom.ext
    intro point
    rfl
  Ty context := context.carrier -> Type u
  tySub family substitution point := family (substitution.toFun point)
  tySub_id _ := rfl
  tySub_comp _ _ _ := rfl
  Tm context family := forall point : context.carrier, family point
  tmSub term substitution point := term (substitution.toFun point)
  tmSub_id _ := rfl
  tmSub_comp _ _ _ := rfl
  ext context family := ⟨Sigma family⟩
  wk _ := ⟨fun point => point.1⟩
  vz _ point := point.2
  pair substitution _ term :=
    ⟨fun point => ⟨substitution.toFun point, term point⟩⟩
  wk_pair _ _ _ := rfl
  vz_pair _ _ _ := rfl
  pair_eta _ _ := rfl

/-- The one-point extensional context. -/
def extEmpty : ExtType.{u} :=
  ⟨PUnit⟩

/-- The unique extensional substitution into the one-point context. -/
def extToEmpty (context : ExtType.{u}) : ExtHom context extEmpty where
  toFun _ := PUnit.unit

/-- The extensional family CwF with its terminal context. -/
def extCwfWithTerminal : CwfWithTerminal.{u + 1, u, u + 1, u} where
  toCwf := extCwf.{u}
  empty := extEmpty.{u}
  toEmpty := extToEmpty
  toEmpty_unique := by
    intro context substitution
    apply ExtHom.ext
    intro point
    cases substitution.toFun point
    rfl

/-! ## Transposing sections across the quotient -/

/-- A dependent section commutes with equality transport in its base. -/
theorem dependentSection_transport {Index : Type u} {family : Index -> Type u}
    (term : forall index, family index) {source target : Index}
    (equality : source = target) :
    cast (congrArg family equality) (term source) = term target := by
  cases equality
  rfl

/-- Equality transport around a proof of reflexivity is the identity,
independently of the particular proof term. -/
theorem cast_congrArg_self {Index : Type u} (family : Index -> Type u)
    (index : Index) (equality : index = index) (value : family index) :
    cast (congrArg family equality) value = value := by
  have proofIrrelevance : equality = rfl := Subsingleton.elim _ _
  cases proofIrrelevance
  rfl

/-- Pull an extensional section back to a route-natural section. -/
def pullbackSection (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u)
    (term : forall quotient, family quotient) :
    RouteSection (pullbackReadoutFamily context family) where
  value point := term (Quot.mk context.Route point)
  natural {source target} route := by
    let equality : Quot.mk context.Route source =
        Quot.mk context.Route target := Quot.sound route
    change cast (congrArg family equality)
        (term (Quot.mk context.Route source)) =
      term (Quot.mk context.Route target)
    exact dependentSection_transport term equality

/-- The total-space map induced by a route-natural section. -/
def sectionTotal {context : RouteType.{u}}
    {family : (routeQuotient.obj context).carrier -> Type u}
    (term : RouteSection (pullbackReadoutFamily context family))
    (point : context.carrier) : Sigma family :=
  ⟨Quot.mk context.Route point, term.value point⟩

/-- Naturality is exactly the relation-invariance required to quotient the
total-space map. -/
theorem sectionTotal_respects {context : RouteType.{u}}
    {family : (routeQuotient.obj context).carrier -> Type u}
    (term : RouteSection (pullbackReadoutFamily context family))
    {source target : context.carrier} (route : context.Route source target) :
    sectionTotal term source = sectionTotal term target := by
  let baseEquality : Quot.mk context.Route source =
      Quot.mk context.Route target := Quot.sound route
  apply Sigma.ext baseEquality
  exact
    (cast_heq (congrArg family baseEquality) (term.value source)).symm.trans
      (heq_of_eq (term.natural route))

/-- Quotient the total-space map of a route-natural section. -/
def descendedTotal {context : RouteType.{u}}
    {family : (routeQuotient.obj context).carrier -> Type u}
    (term : RouteSection (pullbackReadoutFamily context family)) :
    (routeQuotient.obj context).carrier -> Sigma family :=
  Quot.lift (sectionTotal term)
    (fun _ _ route => sectionTotal_respects term route)

/-- The descended total-space map remains over the quotient point supplied
as its input. -/
theorem descendedTotal_fst {context : RouteType.{u}}
    {family : (routeQuotient.obj context).carrier -> Type u}
    (term : RouteSection (pullbackReadoutFamily context family))
    (quotient : (routeQuotient.obj context).carrier) :
    (descendedTotal term quotient).1 = quotient := by
  refine @Quot.ind context.carrier context.Route
    (fun point => (descendedTotal term point).1 = point) ?_ quotient
  intro point
  rfl

/-- Descend a route-natural section to a genuine extensional dependent
section on quotient classes. -/
def descendSection {context : RouteType.{u}}
    {family : (routeQuotient.obj context).carrier -> Type u}
    (term : RouteSection (pullbackReadoutFamily context family)) :
    forall quotient, family quotient :=
  fun quotient =>
    cast (congrArg family (descendedTotal_fst term quotient))
      (descendedTotal term quotient).2

@[simp]
theorem descendSection_mk {context : RouteType.{u}}
    {family : (routeQuotient.obj context).carrier -> Type u}
    (term : RouteSection (pullbackReadoutFamily context family))
    (point : context.carrier) :
    descendSection term (Quot.mk context.Route point) = term.value point := by
  change
    cast
      (congrArg family
        (descendedTotal_fst term (Quot.mk context.Route point)))
      (term.value point) = term.value point
  exact cast_congrArg_self family (Quot.mk context.Route point)
    (descendedTotal_fst term (Quot.mk context.Route point)) (term.value point)

/-- Extensional and route-natural sections of a pulled-back family are
equivalent. -/
def sectionEquiv (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u) :
    (extCwf.Tm (routeQuotient.obj context) family) ≃
      (routeCwf.Tm context (pullbackReadoutFamily context family)) where
  toFun := pullbackSection context family
  invFun := descendSection
  left_inv term := by
    funext quotient
    refine @Quot.ind context.carrier context.Route
      (fun point => descendSection (pullbackSection context family term) point =
        term point) ?_ quotient
    intro point
    exact descendSection_mk _ point
  right_inv term := by
    apply RouteSection.ext
    funext point
    exact descendSection_mk term point

/-! ## Naturality and the DRA instance -/

/-- Pullback of extensional quotient families commutes with route
substitution. -/
theorem pullbackReadoutFamily_natural {first last : RouteType.{u}}
    (family : (routeQuotient.obj last).carrier -> Type u)
    (substitution : RouteHom first last) :
    pullbackReadoutFamily first
        (extCwf.tySub family (routeQuotient.map substitution)) =
      routeCwf.tySub (pullbackReadoutFamily last family) substitution :=
  rfl

/-- The section transposition commutes with substitution. -/
theorem pullbackSection_natural {first last : RouteType.{u}}
    (family : (routeQuotient.obj last).carrier -> Type u)
    (term : extCwf.Tm (routeQuotient.obj last) family)
    (substitution : RouteHom first last) :
    HEq
      (pullbackSection first
        (extCwf.tySub family (routeQuotient.map substitution))
        (extCwf.tmSub term (routeQuotient.map substitution)))
      (routeCwf.tmSub
        (pullbackSection last family term) substitution) :=
  HEq.rfl

/-- The quotient context functor and pullback of extensional families form a
dependent right adjoint. -/
def routeQuotientDra :
    DependentRightAdjoint routeCwf extCwf where
  leftContext context := routeQuotient.obj context
  leftSub substitution := routeQuotient.map substitution
  leftSub_id context := by
    apply ExtHom.ext
    intro quotient
    refine @Quot.ind context.carrier context.Route
      (fun point =>
        (routeQuotient.map (routeIdentity context)).toFun point =
          (extIdentity (routeQuotient.obj context)).toFun point) ?_ quotient
    intro point
    rfl
  leftSub_comp later earlier := by
    apply ExtHom.ext
    intro quotient
    refine @Quot.ind _ _
      (fun point =>
        (routeQuotient.map (routeCompose earlier later)).toFun point =
          (extCompose (routeQuotient.map earlier)
            (routeQuotient.map later)).toFun point) ?_ quotient
    intro point
    rfl
  rightType context family := pullbackReadoutFamily context family
  rightType_natural := pullbackReadoutFamily_natural
  termEquiv := sectionEquiv
  termEquiv_natural := pullbackSection_natural

/-- The same construction bundled over the chosen terminal route and
extensional CwFs. -/
def routeQuotientDraWithTerminal :
    DependentRightAdjointWithTerminal routeCwfWithTerminal
      extCwfWithTerminal where
  toDra := routeQuotientDra

/-! ## Proper-image controls -/

/-- Every family in the right action has equivalent fibres at route-related
points. -/
def relatedFibreEquiv (context : RouteType.{u})
    (family : (routeQuotient.obj context).carrier -> Type u)
    {source target : context.carrier} (route : context.Route source target) :
    (pullbackReadoutFamily context family).fibre source ≃
      (pullbackReadoutFamily context family).fibre target :=
  Equiv.cast (congrArg family (Quot.sound route))

/-- An intensional route family belongs to the right action up to fibrewise
equivalence when some extensional quotient family has equivalent fibres at
every base point. -/
def InRightImageUpToFibreEquivalence (context : RouteType.{u})
    (target : RouteFamily context) : Prop :=
  Exists fun family : (routeQuotient.obj context).carrier -> Type u =>
    forall point : context.carrier,
      Nonempty
        ((pullbackReadoutFamily context family).fibre point ≃
          target.fibre point)

namespace Canary

/-- Pullback is not surjective on intensional types: the nonconstant family
over the codiscrete Boolean route context cannot be equivalent fibrewise to
any quotient-pulled family. -/
theorem codiscreteVaryingFamily_not_in_right_image :
    ¬ InRightImageUpToFibreEquivalence codiscretePair
      RouteFamilyCwf.Canary.codiscreteVaryingFamily := by
  rintro ⟨family, fibreEquiv⟩
  let sourceToTarget :
      RouteFamilyCwf.Canary.codiscreteVaryingFamily.fibre false ≃
        RouteFamilyCwf.Canary.codiscreteVaryingFamily.fibre true :=
    (Classical.choice (fibreEquiv false)).symm |>.trans
      ((relatedFibreEquiv codiscretePair family trivial).trans
        (Classical.choice (fibreEquiv true)))
  exact RouteFamilyCwf.Canary.codiscreteVaryingFamily_fibres_not_equiv
    ⟨sourceToTarget⟩

/-- Constant families are in the dependent right action. -/
theorem constantFamily_in_right_image (valueType : Type) :
    Exists fun family : (routeQuotient.obj codiscretePair).carrier -> Type =>
      pullbackReadoutFamily codiscretePair family =
        RouteFamily.constant codiscretePair valueType := by
  refine ⟨fun _ => valueType, ?_⟩
  rfl

/-- The DRA image is inhabited but proper. -/
theorem right_image_boundary :
    (Exists fun family : (routeQuotient.obj codiscretePair).carrier -> Type =>
      pullbackReadoutFamily codiscretePair family =
        RouteFamily.constant codiscretePair Bool) /\
    ¬ InRightImageUpToFibreEquivalence codiscretePair
      RouteFamilyCwf.Canary.codiscreteVaryingFamily :=
  ⟨constantFamily_in_right_image Bool,
    codiscreteVaryingFamily_not_in_right_image⟩

end Canary

#print axioms extCwf
#print axioms extCwfWithTerminal
#print axioms sectionTotal_respects
#print axioms descendSection_mk
#print axioms sectionEquiv
#print axioms pullbackReadoutFamily_natural
#print axioms pullbackSection_natural
#print axioms routeQuotientDra
#print axioms routeQuotientDraWithTerminal
#print axioms relatedFibreEquiv
#print axioms InRightImageUpToFibreEquivalence
#print axioms Canary.codiscreteVaryingFamily_not_in_right_image
#print axioms Canary.constantFamily_in_right_image
#print axioms Canary.right_image_boundary

end Mettapedia.TypeTheory.RouteQuotientDependentRightAdjoint
