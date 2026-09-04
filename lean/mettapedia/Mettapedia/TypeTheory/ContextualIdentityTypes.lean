import Mettapedia.GSLT.Core.ContextualLadder
import Mettapedia.TypeTheory.IdentityEliminationCapabilities

/-!
# Identity formation and intrinsic J over contextual structure

This module isolates the ordinary contextual ingredients of intensional
identity types without selecting a language calculus.  Formation,
reflexivity, substitution stability, dependent elimination, and proof
irrelevance are separate properties.

The eliminator is internal in the relevant sense: its motive is an arbitrary
type over the context of two endpoints and an identity witness.  It is not a
Lean proposition about an external route.  The set-families CwF supplies the
standard equality model.

A second CwF has only context-constant types and Boolean identity witnesses.
It admits the same contextual J shape and beta law, yet has neither endpoint
reflection nor proof irrelevance.  This is a useful negative control: the
force of J depends on the available dependent motives.  It does not license
global UIP or equality reflection merely from the name of the rule.

Substitution stability of the J operation itself is deliberately not bundled
here; it is a further coherence property over reindexed identity contexts.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualIdentityTypes

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ScopedIdentity
open Mettapedia.TypeTheory.IdentityRouteCapabilities
open Mettapedia.TypeTheory.IdentityEliminationCapabilities

universe u v w w'

/-! ## Formation and reflexivity -/

/-- Contextual identity-type formation, stable under substitution. -/
structure IdentityFormation (C : Cwf.{u, v, w, w'}) where
  idTy : {context : C.Ctx} -> (type : C.Ty context) ->
    C.Tm context type -> C.Tm context type -> C.Ty context
  idTy_sub : forall {source target : C.Ctx} (substitution : C.Sub source target)
    (type : C.Ty target) (left right : C.Tm target type),
    C.tySub (idTy type left right) substitution =
      idTy (C.tySub type substitution)
        (C.tmSub left substitution) (C.tmSub right substitution)

/-- Reflexivity, stable under substitution up to the type equality supplied
by identity formation. -/
structure IdentityReflexivity (C : Cwf.{u, v, w, w'})
    (identity : IdentityFormation C) where
  refl : {context : C.Ctx} -> {type : C.Ty context} ->
    (term : C.Tm context type) -> C.Tm context (identity.idTy type term term)
  refl_sub : forall {source target : C.Ctx} (substitution : C.Sub source target)
    {type : C.Ty target} (term : C.Tm target type),
    HEq (C.tmSub (refl term) substitution)
      (refl (C.tmSub term substitution))

/-! ## The generic identity context -/

/-- The type of the second endpoint over `context.type`. -/
def secondEndpointType (C : Cwf.{u, v, w, w'})
    {context : C.Ctx} (type : C.Ty context) :
    C.Ty (C.ext context type) :=
  C.tySub type (C.wk type)

/-- The context carrying two terms of one contextual type. -/
def endpointPairContext (C : Cwf.{u, v, w, w'})
    {context : C.Ctx} (type : C.Ty context) : C.Ctx :=
  C.ext (C.ext context type) (secondEndpointType C type)

/-- The common endpoint type over the two-endpoint context. -/
def endpointType (C : Cwf.{u, v, w, w'})
    {context : C.Ctx} (type : C.Ty context) :
    C.Ty (endpointPairContext C type) :=
  C.tySub (secondEndpointType C type)
    (C.wk (secondEndpointType C type))

/-- The first endpoint in the two-endpoint context. -/
def leftEndpoint (C : Cwf.{u, v, w, w'})
    {context : C.Ctx} (type : C.Ty context) :
    C.Tm (endpointPairContext C type) (endpointType C type) :=
  C.tmSub (C.vz type) (C.wk (secondEndpointType C type))

/-- The second endpoint in the two-endpoint context. -/
def rightEndpoint (C : Cwf.{u, v, w, w'})
    {context : C.Ctx} (type : C.Ty context) :
    C.Tm (endpointPairContext C type) (endpointType C type) :=
  C.vz (secondEndpointType C type)

/-- The identity-witness type over the two-endpoint context. -/
def identityWitnessType (C : Cwf.{u, v, w, w'})
    (identity : IdentityFormation C)
    {context : C.Ctx} (type : C.Ty context) :
    C.Ty (endpointPairContext C type) :=
  identity.idTy (endpointType C type)
    (leftEndpoint C type) (rightEndpoint C type)

/-- The context carrying two endpoints and an identity witness. -/
def identityContext (C : Cwf.{u, v, w, w'})
    (identity : IdentityFormation C)
    {context : C.Ctx} (type : C.Ty context) : C.Ctx :=
  C.ext (endpointPairContext C type) (identityWitnessType C identity type)

/-- The diagonal substitution sending one endpoint to a repeated pair. -/
def endpointDiagonal (C : Cwf.{u, v, w, w'})
    {context : C.Ctx} (type : C.Ty context) :
    C.Sub (C.ext context type) (endpointPairContext C type) :=
  C.pair (C.idS (C.ext context type)) (secondEndpointType C type)
    ((C.tySub_id (secondEndpointType C type)).symm ▸ C.vz type)

/-! ## Intrinsic dependent elimination -/

/-- Contextual identity elimination with beta.

`reflexivitySubstitution` is the canonical map from `context.type` into the
context of two endpoints and a witness.  Its two laws say that it lies over
the endpoint diagonal and that its witness is reflexivity.  The motive of
`j` is an arbitrary object-language type over that identity context. -/
structure IdentityEliminationBeta (C : Cwf.{u, v, w, w'})
    (identity : IdentityFormation C)
    (introduction : IdentityReflexivity C identity) where
  reflexivitySubstitution : forall {context : C.Ctx} (type : C.Ty context),
    C.Sub (C.ext context type) (identityContext C identity type)
  over_diagonal : forall {context : C.Ctx} (type : C.Ty context),
    C.compS (C.wk (identityWitnessType C identity type))
        (reflexivitySubstitution type) = endpointDiagonal C type
  witness_is_refl : forall {context : C.Ctx} (type : C.Ty context),
    HEq
      (C.tmSub (C.vz (identityWitnessType C identity type))
        (reflexivitySubstitution type))
      (introduction.refl (C.vz type))
  j : forall {context : C.Ctx} {type : C.Ty context}
    (motive : C.Ty (identityContext C identity type)),
    C.Tm (C.ext context type)
        (C.tySub motive (reflexivitySubstitution type)) ->
      C.Tm (identityContext C identity type) motive
  beta : forall {context : C.Ctx} {type : C.Ty context}
    (motive : C.Ty (identityContext C identity type))
    (base : C.Tm (C.ext context type)
      (C.tySub motive (reflexivitySubstitution type))),
    C.tmSub (j motive base) (reflexivitySubstitution type) = base

/-! ## Properties which are not part of J -/

/-- Every pair of identity proofs at fixed endpoints is equal. -/
def IdentityProofIrrelevance (C : Cwf.{u, v, w, w'})
    (identity : IdentityFormation C) : Prop :=
  forall {context : C.Ctx} {type : C.Ty context}
    (left right : C.Tm context type),
    Subsingleton (C.Tm context (identity.idTy type left right))

/-- An inhabited identity fibre reflects equality of its endpoint terms. -/
def IdentityEndpointReflection (C : Cwf.{u, v, w, w'})
    (identity : IdentityFormation C) : Prop :=
  forall {context : C.Ctx} {type : C.Ty context}
    {left right : C.Tm context type},
    C.Tm context (identity.idTy type left right) -> left = right

/-! ## From intrinsic identity terms to route families -/

/-- At any context and object type, identity terms form a proof-relevant
route layer.  This construction retains the actual object-language witness;
its proposition-valued support remembers only inhabitation. -/
def termIdentityLayer (C : Cwf.{u, v, w, w'})
    (identity : IdentityFormation C)
    (introduction : IdentityReflexivity C identity)
    {context : C.Ctx} (type : C.Ty context) :
    Layer (C.Tm context type) where
  Route left right := C.Tm context (identity.idTy type left right)
  refl := introduction.refl
  Support left right := Nonempty
    (C.Tm context (identity.idTy type left right))
  forget route := ⟨route⟩

/-- Object-language proof irrelevance is exactly route UIP for every induced
term-identity layer. -/
theorem proofIrrelevance_iff_all_termLayers_routeUIP
    (C : Cwf.{u, v, w, w'})
    (identity : IdentityFormation C)
    (introduction : IdentityReflexivity C identity) :
    IdentityProofIrrelevance C identity <->
      forall {context : C.Ctx} (type : C.Ty context),
        RouteUIP (termIdentityLayer C identity introduction type) := by
  rfl

/-- Endpoint reflection is likewise exactly endpoint reflection of every
induced term-identity route layer. -/
theorem endpointReflection_iff_all_termLayers
    (C : Cwf.{u, v, w, w'})
    (identity : IdentityFormation C)
    (introduction : IdentityReflexivity C identity) :
    IdentityEndpointReflection C identity <->
      forall {context : C.Ctx} (type : C.Ty context),
        EndpointReflection (termIdentityLayer C identity introduction type) := by
  rfl

/-! ## The full set-families equality model -/

namespace Families

open Classical

/-- Fibrewise Lean equality is a substitution-stable identity formation in
the set-families CwF. -/
def identityFormation : IdentityFormation (familiesCwf.{w}) where
  idTy _type left right context := ULift (PLift (left context = right context))
  idTy_sub _ _ _ _ := rfl

/-- Reflexivity in the fibrewise equality model. -/
def identityReflexivity :
    IdentityReflexivity (familiesCwf.{w}) identityFormation where
  refl _ _ := ⟨⟨rfl⟩⟩
  refl_sub := by
    intro source target substitution type term
    exact HEq.rfl

/-- The reflexivity boundary in the set-families model. -/
def reflexivitySubstitution {context : Type w} (type : context -> Type w) :
    (familiesCwf.{w}).Sub ((familiesCwf.{w}).ext context type)
      (identityContext (familiesCwf.{w}) identityFormation type) :=
  fun endpoint => ⟨⟨endpoint, endpoint.2⟩, ⟨⟨rfl⟩⟩⟩

/-- Set-indexed families validate full contextual J by ordinary equality
elimination. -/
def identityElimination :
    IdentityEliminationBeta (familiesCwf.{w}) identityFormation
      identityReflexivity where
  reflexivitySubstitution := reflexivitySubstitution
  over_diagonal _ := rfl
  witness_is_refl _ := HEq.rfl
  j motive base := by
    intro identityPoint
    rcases identityPoint with ⟨⟨⟨context, left⟩, right⟩, equality⟩
    cases equality.down.down
    exact base ⟨context, left⟩
  beta _ _ := rfl

theorem proofIrrelevance :
    IdentityProofIrrelevance (familiesCwf.{w}) identityFormation := by
  intro context type left right
  constructor
  intro first second
  funext point
  rcases first point with ⟨⟨firstEquality⟩⟩
  rcases second point with ⟨⟨secondEquality⟩⟩
  have equalProofs : firstEquality = secondEquality :=
    Subsingleton.elim firstEquality secondEquality
  cases equalProofs
  rfl

theorem endpointReflection :
    IdentityEndpointReflection (familiesCwf.{w}) identityFormation := by
  intro context type left right proof
  funext point
  exact (proof point).down.down

/-! ### Dependent motives reject an indiscrete fake identity -/

/-- A deliberately over-permissive formation: every pair of endpoints has one
witness.  Formation and reflexivity alone cannot reject it. -/
def indiscreteFormation : IdentityFormation (familiesCwf.{0}) where
  idTy _type _left _right _context := PUnit
  idTy_sub _ _ _ _ := rfl

def indiscreteReflexivity :
    IdentityReflexivity (familiesCwf.{0}) indiscreteFormation where
  refl _ _ := .unit
  refl_sub := by
    intro source target substitution type term
    exact HEq.rfl

def boolFamily : (familiesCwf.{0}).Ty PUnit := fun _ => Bool

/-- A genuinely dependent motive which is inhabited only when the two
Boolean endpoints agree. -/
def diagonalOnlyMotive :
    (familiesCwf.{0}).Ty
      (identityContext (familiesCwf.{0}) indiscreteFormation boolFamily) :=
  fun point => if point.1.1.2 = point.1.2 then PUnit else Empty

/-- Every legal reflexivity boundary lies on the diagonal, so the
diagonal-only motive has a base case for any proposed eliminator. -/
def diagonalOnlyBase
    (elimination : IdentityEliminationBeta (familiesCwf.{0})
      indiscreteFormation indiscreteReflexivity) :
    (familiesCwf.{0}).Tm ((familiesCwf.{0}).ext PUnit boolFamily)
      ((familiesCwf.{0}).tySub diagonalOnlyMotive
        (elimination.reflexivitySubstitution boolFamily)) := by
  intro endpoint
  have overDiagonal := congrFun (elimination.over_diagonal boolFamily) endpoint
  have leftOnDiagonal :=
    congrArg (fun pair => pair.1.2) overDiagonal
  have rightOnDiagonal :=
    congrArg (fun pair => pair.2) overDiagonal
  have endpointsEqual :
      (elimination.reflexivitySubstitution boolFamily endpoint).1.1.2 =
        (elimination.reflexivitySubstitution boolFamily endpoint).1.2 := by
    exact leftOnDiagonal.trans rightOnDiagonal.symm
  change
    (if
      (elimination.reflexivitySubstitution boolFamily endpoint).1.1.2 =
        (elimination.reflexivitySubstitution boolFamily endpoint).1.2
    then PUnit.{1} else Empty)
  exact if_pos endpointsEqual ▸ PUnit.unit

/-- Negative control: full contextual dependency can express a motive that
rules out the indiscrete fake identity. -/
theorem no_indiscreteIdentityElimination :
    Not (Nonempty
      (IdentityEliminationBeta (familiesCwf.{0}) indiscreteFormation
        indiscreteReflexivity)) := by
  rintro ⟨elimination⟩
  have impossible :=
    elimination.j diagonalOnlyMotive (diagonalOnlyBase elimination)
      ⟨⟨⟨PUnit.unit, false⟩, true⟩, PUnit.unit⟩
  have empty : Empty := by
    simpa [diagonalOnlyMotive] using impossible
  exact empty.elim

/-- The same contextual core supports the equality identity formation and
the indiscrete formation, but only the former admits dependent J. -/
theorem sameCwf_distinct_identity_elimination_behavior :
    Nonempty
      (IdentityEliminationBeta (familiesCwf.{0}) identityFormation
        identityReflexivity) /\
    Not
      (Nonempty
        (IdentityEliminationBeta (familiesCwf.{0}) indiscreteFormation
          indiscreteReflexivity)) :=
  ⟨⟨identityElimination⟩, no_indiscreteIdentityElimination⟩

end Families

/-! ## A motive-poor model: J without endpoint reflection or UIP -/

namespace ConstantMotiveCanary

/-- A universe-polymorphic two-element type for plural identity witnesses. -/
inductive Two : Type w where
  | first
  | second
  deriving DecidableEq

/-- On the constant-family CwF, Boolean witnesses form a substitution-stable
identity-like family. -/
def identityFormation : IdentityFormation (simpleFamilies.{w}.toCwf) where
  idTy _ _ _ := Two
  idTy_sub _ _ _ _ := rfl

def identityReflexivity :
    IdentityReflexivity (simpleFamilies.{w}.toCwf) identityFormation where
  refl _ _ := .first
  refl_sub := by
    intro source target substitution type term
    exact HEq.rfl

def reflexivitySubstitution {context type : Type w} :
    (simpleFamilies.{w}.toCwf).Sub
      (simpleFamilies.{w}.toCwf.ext context type)
      (identityContext (context := context) simpleFamilies.toCwf
        identityFormation type) :=
  fun endpoint => ((endpoint, endpoint.2), .first)

/-- Because every available type is context-constant, the J motive cannot
inspect the second endpoint or the Boolean witness.  The eliminator therefore
exists while those witnesses remain plural. -/
def identityElimination :
    IdentityEliminationBeta (simpleFamilies.{w}.toCwf) identityFormation
      identityReflexivity where
  reflexivitySubstitution := fun _ => reflexivitySubstitution
  over_diagonal _ := rfl
  witness_is_refl _ := HEq.rfl
  j _ base point := base point.1.1
  beta _ _ := rfl

theorem not_proofIrrelevant :
    Not (IdentityProofIrrelevance (simpleFamilies.{0}.toCwf)
      identityFormation) := by
  intro proofIrrelevant
  let left : (simpleFamilies.{0}.toCwf).Tm PUnit PUnit := fun _ => .unit
  let falseProof : (simpleFamilies.{0}.toCwf).Tm PUnit
      (identityFormation.idTy PUnit left left) := fun _ => .first
  let trueProof : (simpleFamilies.{0}.toCwf).Tm PUnit
      (identityFormation.idTy PUnit left left) := fun _ => .second
  have equal : falseProof = trueProof :=
    (proofIrrelevant left left).allEq falseProof trueProof
  have pointwise := congrFun equal PUnit.unit
  exact (by decide : (Two.first : Two) ≠ Two.second) pointwise

theorem not_endpointReflecting :
    Not (IdentityEndpointReflection (simpleFamilies.{0}.toCwf)
      identityFormation) := by
  intro reflects
  let left : (simpleFamilies.{0}.toCwf).Tm PUnit Bool := fun _ => false
  let right : (simpleFamilies.{0}.toCwf).Tm PUnit Bool := fun _ => true
  let witness : (simpleFamilies.{0}.toCwf).Tm PUnit
      (identityFormation.idTy Bool left right) := fun _ => .first
  have equal : left = right := reflects witness
  have pointwise := congrFun equal PUnit.unit
  exact (by decide : (false : Bool) ≠ true) pointwise

/-- Intrinsic J and beta do not by themselves imply proof irrelevance when
the contextual type theory lacks motives capable of observing paths. -/
theorem elimination_does_not_force_proofIrrelevance :
    Nonempty
      (IdentityEliminationBeta (simpleFamilies.{0}.toCwf)
        identityFormation identityReflexivity) /\
    Not (IdentityProofIrrelevance (simpleFamilies.{0}.toCwf)
      identityFormation) :=
  ⟨⟨identityElimination⟩, not_proofIrrelevant⟩

/-- The same model refutes the stronger inference from J to endpoint
reflection. -/
theorem elimination_does_not_force_endpointReflection :
    Nonempty
      (IdentityEliminationBeta (simpleFamilies.{0}.toCwf)
        identityFormation identityReflexivity) /\
    Not (IdentityEndpointReflection (simpleFamilies.{0}.toCwf)
      identityFormation) :=
  ⟨⟨identityElimination⟩, not_endpointReflecting⟩

/-- One concrete term-identity layer from the motive-poor model. -/
def pluralTermLayer : Layer
    ((simpleFamilies.{0}.toCwf).Tm PUnit Bool) :=
  termIdentityLayer simpleFamilies.toCwf identityFormation
    identityReflexivity Bool

theorem pluralTermLayer_not_endpointReflection :
    Not (EndpointReflection pluralTermLayer) := by
  intro reflects
  let left : (simpleFamilies.{0}.toCwf).Tm PUnit Bool := fun _ => false
  let right : (simpleFamilies.{0}.toCwf).Tm PUnit Bool := fun _ => true
  let witness : pluralTermLayer.Route left right := fun _ => .first
  have equal : left = right := reflects witness
  have pointwise := congrFun equal PUnit.unit
  exact (by decide : (false : Bool) ≠ true) pointwise

/-- The internal J operation of the motive-poor contextual theory does not
manufacture external path induction for its induced route layer.  External
propositional elimination would reflect endpoints, contradicting the
explicit Boolean witness between unequal terms. -/
theorem no_externalPropositionalElimination :
    Not (ExternalPropositionalIdentityElimination pluralTermLayer) := by
  intro elimination
  exact pluralTermLayer_not_endpointReflection
    (identityElimination_implies_endpointReflection elimination)

/-- Paired boundary: intrinsic J is inhabited while external semantic path
induction for the same retained witnesses is impossible. -/
theorem internalJ_does_not_imply_externalPathInduction :
    Nonempty
      (IdentityEliminationBeta (simpleFamilies.{0}.toCwf)
        identityFormation identityReflexivity) /\
    Not (ExternalPropositionalIdentityElimination pluralTermLayer) :=
  ⟨⟨identityElimination⟩, no_externalPropositionalElimination⟩

end ConstantMotiveCanary

#print axioms Families.identityElimination
#print axioms Families.proofIrrelevance
#print axioms Families.endpointReflection
#print axioms Families.no_indiscreteIdentityElimination
#print axioms Families.sameCwf_distinct_identity_elimination_behavior
#print axioms ConstantMotiveCanary.identityElimination
#print axioms ConstantMotiveCanary.elimination_does_not_force_proofIrrelevance
#print axioms ConstantMotiveCanary.elimination_does_not_force_endpointReflection
#print axioms proofIrrelevance_iff_all_termLayers_routeUIP
#print axioms endpointReflection_iff_all_termLayers
#print axioms ConstantMotiveCanary.internalJ_does_not_imply_externalPathInduction

end Mettapedia.TypeTheory.ContextualIdentityTypes
