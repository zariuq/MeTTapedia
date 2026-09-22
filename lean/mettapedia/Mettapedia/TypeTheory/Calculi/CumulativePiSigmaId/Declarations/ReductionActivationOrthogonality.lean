import Mettapedia.OSLF.Framework.ReductionViewIndexedModalities
import Mettapedia.GSLT.Dynamics.SpaceActivationPolicy

/-!
# Reduction views and activation policies over a common presentation

A profile pairs a selected reduction view with an activation policy over
the same pattern carrier.  Modal roles are read from the reduction view;
firing is read from the activation policy.  The interface adds no implication
between these coordinates, and transition provenance remains in receipts.

Concrete independence results require actual profiles and their firing
evidence.  They are not supplied as assumptions of this record.
-/


open Mettapedia.OSLF.Framework
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ReductionActivationOrthogonality

open Mettapedia.GSLT.Dynamics.SpaceActivationPolicy
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.DerivedTyping
open Mettapedia.OSLF.MeTTaIL.Syntax
open ReductionViewIndexedModalities

universe uStore uTrigger uObservation uReceipt

/-- The product of a type-theoretic reduction view and an operational
activation policy over the same pattern carrier.  The record deliberately
adds no implication between the coordinates.  Exact transition provenance is
supplied separately by the policy's receipts. -/
structure Profile (language : LanguageDef) (Store : Type uStore)
    (Trigger : Type uTrigger) (Observation : Type uObservation)
    (Receipt : Type uReceipt) where
  reduction : ReductionView language
  activation : Policy Store Pattern Trigger Observation Receipt

namespace Profile

def role {language : LanguageDef} {Store : Type uStore}
    {Trigger : Type uTrigger} {Observation : Type uObservation}
    {Receipt : Type uReceipt}
    (profile : Profile language Store Trigger Observation Receipt)
    {domain codomain : LangSort language}
    (arrow : SortArrow language domain codomain) : ConstructorRole :=
  profile.reduction.role arrow

def CanFire {language : LanguageDef} {Store : Type uStore}
    {Trigger : Type uTrigger} {Observation : Type uObservation}
    {Receipt : Type uReceipt}
    (profile : Profile language Store Trigger Observation Receipt)
    (store : Store) (cause : Cause Trigger Pattern) : Prop :=
  profile.activation.CanFire store cause

end Profile

#print axioms Profile.role
#print axioms Profile.CanFire

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ReductionActivationOrthogonality
