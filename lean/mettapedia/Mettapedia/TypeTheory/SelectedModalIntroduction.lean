import Mettapedia.TypeTheory.GuardedTimeModeTheory

/-!
# Term introduction along a selected class of modalities

A mode theory says which modal arrows compose.  It does not say that every
arrow has the same term-introduction rule.  In particular, contextual-code
quotation and guarded time can inhabit one product mode theory without making
quotation available along a guarded tick.

This module describes a wide subtheory of selected arrows and restricts modal
term introduction to that subtheory.  Revision-stable arrows form such a wide
subtheory in the product of any mode theory with guarded revision time.  Every
first-axis arrow is selected, while the canonical guard is not.  The two axes
still commute in the ambient product.

No language, surface quotation form, clock calculus, or native mode package is
selected here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.SelectedModalIntroduction

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.ModeTheoryProducts
open Mettapedia.TypeTheory.GuardedTimeModeTheory

/-! ## Wide subtheories -/

/-- A composition-closed, identity-containing selection of arrows of one mode
theory.  This is the strict custom-mode analogue of a wide subcategory. -/
structure WideSubtheory (modes : ModeTheory) where
  selected : {high low : modes.Mode} -> modes.Hom high low -> Prop
  identity_selected : forall mode, selected (modes.id mode)
  comp_selected : forall {first middle last}
    (earlier : modes.Hom first middle) (later : modes.Hom middle last),
    selected earlier -> selected later -> selected (modes.comp earlier later)

namespace WideSubtheory

/-- The full selection containing every modality. -/
def all (modes : ModeTheory) : WideSubtheory modes where
  selected := fun _ => True
  identity_selected := fun _ => trivial
  comp_selected := fun _ _ _ _ => trivial

end WideSubtheory

/-! ## Selected term introduction -/

/-- Term introduction for only the selected modal arrows.  Substitution and
identity stability are required exactly where introduction is admitted.

Unlike `QuotationTermStructure`, this record does not require one term former
for every unrelated modality in a product mode theory. -/
structure SelectedQuotationTermStructure (modes : ModeTheory)
    (cwf : ModalCwF modes) (laws : ModalCwFLaws modes cwf)
    (selection : WideSubtheory modes) where
  introduce : {high low : modes.Mode} -> (modality : modes.Hom high low) ->
    selection.selected modality ->
    {context : cwf.Con low} ->
    {type : cwf.Ty (cwf.lock modality context)} ->
    cwf.Tm (cwf.lock modality context) type ->
      cwf.Tm context (cwf.boxTy modality type)
  introduce_sub : forall {high low : modes.Mode}
    (modality : modes.Hom high low)
    (admitted : selection.selected modality)
    {first last : cwf.Con low}
    {type : cwf.Ty (cwf.lock modality last)}
    (term : cwf.Tm (cwf.lock modality last) type)
    (substitution : cwf.Sub first last),
    HEq
      (cwf.tmSub (introduce modality admitted term) substitution)
      (introduce modality admitted
        (cwf.tmSub term (laws.lockSub modality substitution)))
  introduce_id : forall {mode : modes.Mode} {context : cwf.Con mode}
    {type : cwf.Ty (cwf.lock (modes.id mode) context)}
    (term : cwf.Tm (cwf.lock (modes.id mode) context) type),
    HEq
      (introduce (modes.id mode) (selection.identity_selected mode) term)
      term

namespace SelectedQuotationTermStructure

/-- A global quotation structure restricts to every selected wide
subtheory.  The construction forgets obligations; it does not invent modal
term introduction. -/
def ofGlobal {modes : ModeTheory} {cwf : ModalCwF modes}
    {laws : ModalCwFLaws modes cwf}
    (quotation : QuotationTermStructure modes cwf laws)
    (selection : WideSubtheory modes) :
    SelectedQuotationTermStructure modes cwf laws selection where
  introduce := fun {high} {low} modality _admitted {context} {type} term =>
    quotation.quoteTm modality term
  introduce_sub := by
    intro high low modality admitted first last type term substitution
    exact quotation.quote_sub modality term substitution
  introduce_id := by
    intro mode context type term
    exact quotation.quote_id term

end SelectedQuotationTermStructure

/-! ## Revision-stable modalities -/

/-- In a product with guarded revision time, select precisely the arrows whose
source and target revisions agree.  The other modal coordinate remains
unrestricted. -/
def revisionStable (other : ModeTheory) :
    WideSubtheory (withGuardedTime other) where
  selected := fun {high low} _modality => high.2 = low.2
  identity_selected := fun _ => rfl
  comp_selected := by
    intro first middle last earlier later firstStable secondStable
    exact firstStable.trans secondStable

/-- Every arrow along the non-temporal axis is revision-stable. -/
theorem alongFirst_revisionStable
    {other : ModeTheory} {source target : other.Mode}
    (revision : Nat) (modality : other.Hom source target) :
    (revisionStable other).selected
      (product.alongFirst (first := other) (second := revisionModes)
        revision modality) :=
  rfl

/-- A canonical guarded tick is not revision-stable. -/
theorem guard_not_revisionStable
    {other : ModeTheory} (fixed : other.Mode) (revision : Nat) :
    ¬ (revisionStable other).selected
      (product.alongSecond (first := other) (second := revisionModes)
        fixed (guard revision)) := by
  intro sameRevision
  exact Nat.ne_of_lt (Nat.lt_succ_self revision) sameRevision.symm

/-- A modality cannot both preserve its revision and make strict guarded
progress. -/
theorem revisionStable_excludes_strict
    {other : ModeTheory}
    {high low : (withGuardedTime other).Mode}
    (modality : (withGuardedTime other).Hom high low)
    (stable : (revisionStable other).selected modality) :
    ¬ Strict modality.2 := by
  intro strict
  exact (Nat.ne_of_lt strict) stable.symm

/-- Contextual/staging motion and a guard tick commute in the ambient product,
even though only the former belongs to the revision-stable subtheory. -/
theorem selected_axis_commutes_with_guard
    {other : ModeTheory} {source target : other.Mode}
    (modality : other.Hom source target) (revision : Nat) :
    (withGuardedTime other).comp
        (product.alongFirst (first := other) (second := revisionModes)
          (revision + 1) modality)
        (product.alongSecond (first := other) (second := revisionModes)
          target (guard revision)) =
      (withGuardedTime other).comp
        (product.alongSecond (first := other) (second := revisionModes)
          source (guard revision))
        (product.alongFirst (first := other) (second := revisionModes)
          revision modality) :=
  other_modality_commutes_with_guard modality revision

/-! ## Material selection controls -/

namespace Canary

open Mettapedia.TypeTheory.ModeTheoryProducts.Canary

/-- A nonidentity staging-like arrow at one fixed revision. -/
def stage (revision : Nat) :
    (withGuardedTime additiveModes).Hom ((), revision) ((), revision) :=
  product.alongFirst (first := additiveModes) (second := revisionModes)
    revision (additiveModality 1)

/-- The staging-like arrow is admitted by the revision-stable subtheory. -/
theorem stage_selected (revision : Nat) :
    (revisionStable additiveModes).selected (stage revision) :=
  rfl

/-- The selected staging arrow is genuinely not the ambient identity arrow. -/
theorem stage_not_identity (revision : Nat) :
    stage revision ≠ (withGuardedTime additiveModes).id ((), revision) := by
  intro equalArrows
  have firstCoordinates := congrArg Prod.fst equalArrows
  change (1 : Nat) = 0 at firstCoordinates
  exact Nat.one_ne_zero firstCoordinates

/-- The one-tick guarded arrow lies outside the same selected class. -/
theorem guard_rejected (revision : Nat) :
    ¬ (revisionStable additiveModes).selected
      (product.alongSecond (first := additiveModes) (second := revisionModes)
        () (guard revision)) :=
  guard_not_revisionStable (other := additiveModes) () revision

/-- The positive staging control and negative guard control coexist in one
ambient mode theory, whose axes nevertheless commute. -/
theorem staging_guarding_selection_matrix (revision : Nat) :
    (revisionStable additiveModes).selected (stage (revision + 1)) ∧
      ¬ (revisionStable additiveModes).selected
        (product.alongSecond (first := additiveModes)
          (second := revisionModes) () (guard revision)) ∧
      (withGuardedTime additiveModes).comp
          (stage (revision + 1))
          (product.alongSecond (first := additiveModes)
            (second := revisionModes) () (guard revision)) =
        (withGuardedTime additiveModes).comp
          (product.alongSecond (first := additiveModes)
            (second := revisionModes) () (guard revision))
          (stage revision) :=
  And.intro (stage_selected (revision + 1))
    (And.intro (guard_rejected revision)
      (selected_axis_commutes_with_guard (additiveModality 1) revision))

end Canary

#print axioms SelectedQuotationTermStructure.ofGlobal
#print axioms alongFirst_revisionStable
#print axioms guard_not_revisionStable
#print axioms revisionStable_excludes_strict
#print axioms selected_axis_commutes_with_guard
#print axioms Canary.staging_guarding_selection_matrix

end Mettapedia.TypeTheory.SelectedModalIntroduction
