import Mettapedia.TypeTheory.JudgmentalEquality
import Mettapedia.Cybernetics.ObservedVariety
import Mathlib.Data.Fintype.EquivFin

/-!
# Scoped proof irrelevance inside a route-sensitive identity layer

This file isolates a deliberately weak identity interface.  A route is
proof-relevant data; a support proposition records only that some route
exists.  Proof irrelevance may hold on a declared region without holding for
the whole route language.

The constructions here are criteria and countermodels, not a selection of K,
univalence, or a production MeTTa identity theory.  They may be revised or
removed if stronger operational or semantic evidence refutes the criteria.

Three facts are proved.

* A route-plural layer can contain a nonempty proof-irrelevant region.
* Proposition-valued support cannot reconstruct which conversion route ran.
* Two materially different constructions can remain structurally
  transportable by an explicit equivalence.

The first fact captures only the scoping shape used by two-level systems; it
does not claim a model of HoTT or derive Hedberg's theorem internally.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ScopedIdentity

open Mettapedia.TypeTheory.JudgmentalEquality

universe uObject uRoute

/-- A proof-relevant route language together with its proposition-valued
support readout.  No eliminator, K rule, or univalence principle is assumed. -/
structure Layer (Object : Type uObject) where
  Route : Object -> Object -> Type uRoute
  refl : forall object, Route object object
  Support : Object -> Object -> Prop
  forget : forall {source target}, Route source target -> Support source target

/-- Global route proof irrelevance: every pair of endpoints has at most one
route.  This is the route-family analogue of UIP, not an assertion that the
route family is an identity type. -/
def RouteUIP {Object : Type uObject} (layer : Layer.{uObject, uRoute} Object) :
    Prop :=
  forall source target, Subsingleton (layer.Route source target)

/-- Proof irrelevance restricted to a declared region of objects. -/
def ScopedRouteUIP {Object : Type uObject}
    (layer : Layer.{uObject, uRoute} Object) (inside : Set Object) : Prop :=
  forall {source target}, source ∈ inside -> target ∈ inside ->
    Subsingleton (layer.Route source target)

/-- Concrete route plurality, stated positively by exhibiting two distinct
routes with the same endpoints. -/
def HasDistinctRoutes {Object : Type uObject}
    (layer : Layer.{uObject, uRoute} Object) : Prop :=
  exists source target,
    exists first second : layer.Route source target, first ≠ second

theorem routeUIP_excludes_distinctRoutes {Object : Type uObject}
    {layer : Layer.{uObject, uRoute} Object}
    (uip : RouteUIP layer) : Not (HasDistinctRoutes layer) := by
  rintro ⟨source, target, first, second, different⟩
  exact different ((uip source target).allEq first second)

/-- Proposition-valued support is proof-irrelevant independently of whether
the retained routes are. -/
theorem support_is_proofIrrelevant {Object : Type uObject}
    (layer : Layer.{uObject, uRoute} Object) (source target : Object) :
    Subsingleton (layer.Support source target) :=
  inferInstance

/-! ## The live judgmental-conversion layer as an instance -/

section Conversion

universe uIndex uState uStep

variable {Index : Type uIndex}
variable (computation : JudgmentalComputation.{uIndex, uState, uStep} Index)
variable (index : Index)

/-- At one judgment index, retained conversion derivations are routes and
ordinary supported conversion is their proof-irrelevant readout. -/
def conversionLayer : Layer (computation.State index) where
  Route := ConversionEvidence computation
  refl := ConversionEvidence.refl
  Support := ConversionEvidence.Support computation
  forget := fun route => route.toSupport

end Conversion

/-! ## A route-plural layer with a strict local bubble -/

namespace BubbleCanary

inductive Region where
  | checked
  | reflective
  deriving DecidableEq, Repr

/-- The checked region has one route; the reflective region retains two. -/
def route : Region -> Region -> Type
  | .checked, .checked => PUnit
  | .reflective, .reflective => Bool
  | _, _ => Empty

def routeRefl : forall region, route region region
  | .checked => PUnit.unit
  | .reflective => false

def layer : Layer Region where
  Route := route
  refl := routeRefl
  Support := fun source target => Nonempty (route source target)
  forget := fun path => ⟨path⟩

def checkedOnly : Set Region := {Region.checked}

def reflectiveOnly : Set Region := {Region.reflective}

/-- The checked region is a genuine proof-irrelevant bubble. -/
theorem checkedOnly_scopedUIP : ScopedRouteUIP layer checkedOnly := by
  intro source target sourceInside targetInside
  have sourceEq : source = .checked := by
    simpa [checkedOnly] using sourceInside
  have targetEq : target = .checked := by
    simpa [checkedOnly] using targetInside
  subst source
  subst target
  change Subsingleton PUnit
  exact inferInstance

/-- The complete route language is not proof-irrelevant. -/
theorem layer_hasDistinctRoutes : HasDistinctRoutes layer := by
  refine ⟨.reflective, .reflective, ?_, ?_, ?_⟩
  · exact (false : Bool)
  · exact (true : Bool)
  · change (false : Bool) ≠ true
    decide

theorem layer_not_routeUIP : Not (RouteUIP layer) :=
  fun uip => routeUIP_excludes_distinctRoutes uip layer_hasDistinctRoutes

/-- The reflective region itself cannot be declared a UIP bubble. -/
theorem reflectiveOnly_not_scopedUIP :
    Not (ScopedRouteUIP layer reflectiveOnly) := by
  intro hypothesis
  have reflectiveInside : Region.reflective ∈ reflectiveOnly := by
    simp [reflectiveOnly]
  have subsingletonRoutes :
      Subsingleton (layer.Route Region.reflective Region.reflective) :=
    hypothesis reflectiveInside reflectiveInside
  change Subsingleton Bool at subsingletonRoutes
  have impossible : (false : Bool) = true :=
    subsingletonRoutes.allEq false true
  exact (by decide : (false : Bool) ≠ true) impossible

end BubbleCanary

/-! ## Support erasure cannot recover process routes -/

namespace ConversionCanary

open JudgmentalEquality.ReceiptCanary

abbrev Route :=
  ConversionEvidence canaryComputation (index := ()) () ()

abbrev Support :=
  ConversionEvidence.Support canaryComputation (index := ()) () ()

/-- A route-sensitive observation of the primitive step label.  Composite,
reflexive, and reversed receipts remain distinguishable from primitive steps. -/
def routeLabel : Route -> Option Bool
  | .step label => some label
  | _ => none

@[simp] theorem routeLabel_first : routeLabel first = some false := rfl

@[simp] theorem routeLabel_second : routeLabel second = some true := rfl

/-- The two retained routes become the same proof after support erasure. -/
theorem first_second_support_equal :
    first.toSupport = second.toSupport :=
  Subsingleton.elim _ _

/-- No function of proof-irrelevant support evidence can reconstruct the
route-sensitive label for every retained conversion receipt. -/
theorem routeLabel_does_not_factor_through_support :
    Not (exists summarize : Support -> Option Bool,
      forall conversion : Route,
        summarize conversion.toSupport = routeLabel conversion) := by
  rintro ⟨summarize, factors⟩
  have firstFactor := factors first
  have secondFactor := factors second
  have labelsEqual : routeLabel first = routeLabel second := by
    calc
      routeLabel first = summarize first.toSupport := firstFactor.symm
      _ = summarize second.toSupport :=
        congrArg summarize first_second_support_equal
      _ = routeLabel second := secondFactor
  exact (by decide : (some false : Option Bool) ≠ some true) labelsEqual

end ConversionCanary

/-! ## Material inspection and structural transport coexist -/

namespace ConstructionCanary

inductive Construction where
  | boolean
  | finiteTwo
  deriving DecidableEq, Repr

def Carrier : Construction -> Type
  | .boolean => Bool
  | .finiteTwo => Fin 2

/-- A material construction comparison retains distinct construction names
and an explicit structural equivalence between their carriers. -/
structure InspectableEquivalence where
  source : Construction
  target : Construction
  materiallyDistinct : source ≠ target
  structurallyEquivalent : Carrier source ≃ Carrier target

noncomputable def booleanFiniteTwoEquivalence : InspectableEquivalence where
  source := .boolean
  target := .finiteTwo
  materiallyDistinct := by decide
  structurallyEquivalent :=
    show Bool ≃ Fin 2 from Fintype.equivOfCardEq (by decide)

/-- Structural transport is invertible while the material construction tags
remain distinguishable. -/
theorem transportable_and_inspectable :
    booleanFiniteTwoEquivalence.source ≠
        booleanFiniteTwoEquivalence.target /\
      forall value : Carrier booleanFiniteTwoEquivalence.source,
        booleanFiniteTwoEquivalence.structurallyEquivalent.symm
            (booleanFiniteTwoEquivalence.structurallyEquivalent value) = value := by
  constructor
  · exact booleanFiniteTwoEquivalence.materiallyDistinct
  · exact booleanFiniteTwoEquivalence.structurallyEquivalent.left_inv

end ConstructionCanary

/-! ## Axiom audit -/

#print axioms routeUIP_excludes_distinctRoutes
#print axioms support_is_proofIrrelevant
#print axioms BubbleCanary.checkedOnly_scopedUIP
#print axioms BubbleCanary.layer_not_routeUIP
#print axioms BubbleCanary.reflectiveOnly_not_scopedUIP
#print axioms ConversionCanary.routeLabel_does_not_factor_through_support
#print axioms ConstructionCanary.transportable_and_inspectable

end Mettapedia.TypeTheory.ScopedIdentity
