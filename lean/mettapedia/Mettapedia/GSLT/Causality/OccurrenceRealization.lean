import Mettapedia.GSLT.Causality.OccurrenceHistory
import Mettapedia.CategoryTheory.RunAccount

/-!
# Realizing occurrence histories by execution blocks

An implementation may realize one authored firing by several target firings.
The selected occurrence, its actual endpoints, and every administrative
intermediate state belong to the comparison. Endpoint-only step proofs do
not retain that information.

This module uses the existing occurrence path category and its valuations.
Block realizations extend to functors, compose by expanding the intermediate
blocks, and pull accounts back through those functors. It introduces no new
history or cost monad. Reflection of arbitrary target schedules remains an
additional obligation on a particular implementation.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.GSLT.Causality.OccurrenceHistory

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent

universe uSite vSite wSite uEvent vEvent wEvent uAccount

namespace OccurrencePath

theorem sites_append {theory : GSLT}
    {P : InteractionPresentation.{uSite, uEvent} theory}
    {source middle target : theory.Term}
    (first : OccurrencePath P source middle) (second : OccurrencePath P middle target) :
    (append first second).sites = first.sites ++ second.sites := by
  induction first with
  | refl => rfl
  | cons event rest ih => simp only [append, sites, ih, List.cons_append]

end OccurrencePath

/-- A selected source occurrence is realized by an actual target block.
Distinct source occurrences remain available to the block selection function;
injectivity and backward schedule adequacy are separate properties. -/
structure OccurrenceRealization {source target : GSLT}
    (P : InteractionPresentation.{uSite, uEvent} source)
    (Q : InteractionPresentation.{vSite, vEvent} target) where
  mapTerm : source.Term → target.Term
  mapEquiv : ∀ {first second}, source.Equiv first second →
    target.Equiv (mapTerm first) (mapTerm second)
  mapOccurrence : ∀ {first last}, Occurrence P first last →
    OccurrencePath Q (mapTerm first) (mapTerm last)

namespace OccurrenceRealization

variable {source middle target : GSLT}
  {P : InteractionPresentation.{uSite, uEvent} source}
  {Q : InteractionPresentation.{vSite, vEvent} middle}
  {R : InteractionPresentation.{wSite, wEvent} target}

/-- Expand a retained history in order, without replacing its final state. -/
def mapPath (realization : OccurrenceRealization P Q) :
    {first last : source.Term} → OccurrencePath P first last →
      OccurrencePath Q (realization.mapTerm first) (realization.mapTerm last)
  | _, _, .refl state => .refl (realization.mapTerm state)
  | _, _, .cons event rest =>
      (realization.mapOccurrence event).append (realization.mapPath rest)

@[simp] theorem mapPath_refl (realization : OccurrenceRealization P Q)
    (state : source.Term) :
    realization.mapPath (.refl state) = .refl (realization.mapTerm state) := rfl

theorem mapPath_append (realization : OccurrenceRealization P Q)
    {first junction last : source.Term}
    (earlier : OccurrencePath P first junction) (later : OccurrencePath P junction last) :
    realization.mapPath (earlier.append later) =
      (realization.mapPath earlier).append (realization.mapPath later) := by
  induction earlier with
  | refl => rfl
  | cons event rest ih =>
      simp only [OccurrencePath.append, mapPath, ih]
      exact (OccurrencePath.append_assoc _ _ _).symm

/-- Identity retains each selected occurrence as a singleton block. -/
def id (P : InteractionPresentation.{uSite, uEvent} source) :
    OccurrenceRealization P P where
  mapTerm := _root_.id
  mapEquiv := fun equal => equal
  mapOccurrence := fun event => .cons event (.refl _)

@[simp] theorem mapPath_id {first last : source.Term}
    (path : OccurrencePath P first last) : (id P).mapPath path = path := by
  induction path with
  | refl => rfl
  | cons event rest ih =>
      change OccurrencePath.cons event ((id P).mapPath rest) = .cons event rest
      rw [ih]

/-- Staging realizations expands the entire intermediate occurrence block. -/
def comp (earlier : OccurrenceRealization P Q) (later : OccurrenceRealization Q R) :
    OccurrenceRealization P R where
  mapTerm := later.mapTerm ∘ earlier.mapTerm
  mapEquiv := fun equal => later.mapEquiv (earlier.mapEquiv equal)
  mapOccurrence := fun event => later.mapPath (earlier.mapOccurrence event)

theorem mapPath_comp (earlier : OccurrenceRealization P Q)
    (later : OccurrenceRealization Q R) {first last : source.Term}
    (path : OccurrencePath P first last) :
    (earlier.comp later).mapPath path = later.mapPath (earlier.mapPath path) := by
  induction path with
  | refl => rfl
  | cons event rest ih =>
      change (later.mapPath (earlier.mapOccurrence event)).append
          ((earlier.comp later).mapPath rest) =
        later.mapPath ((earlier.mapOccurrence event).append (earlier.mapPath rest))
      rw [mapPath_append, ih]
      rfl

/-- The existing history category receives the compiler's block functor. -/
def toFunctor (realization : OccurrenceRealization P Q) :
    OccurrenceCat P ⥤ OccurrenceCat Q where
  obj := realization.mapTerm
  map := realization.mapPath
  map_id _ := rfl
  map_comp first second := realization.mapPath_append first second

/-- Charge a source occurrence exactly the cost of its selected target block. -/
def pullValuation {A : Type uAccount} [AddMonoid A]
    (realization : OccurrenceRealization P Q) (valuation : OccurrenceValuation Q A) :
    OccurrenceValuation P A where
  grade event := valuation.onPath (realization.mapOccurrence event)

/-- The complete target account is the sum of the selected block accounts,
including administrative firings. This holds for noncommutative accounts. -/
theorem onPath_mapPath {A : Type uAccount} [AddMonoid A]
    (realization : OccurrenceRealization P Q) (valuation : OccurrenceValuation Q A)
    {first last : source.Term} (path : OccurrencePath P first last) :
    valuation.onPath (realization.mapPath path) =
      (realization.pullValuation valuation).onPath path := by
  induction path with
  | refl => rfl
  | cons event rest ih =>
      simp only [mapPath, OccurrenceValuation.onPath_append, ih,
        OccurrenceValuation.onPath, pullValuation]

/-- Accounts of actual target runs restrict along the existing run functor. -/
def pullAccount {A : Type uAccount} [Monoid A]
    (realization : OccurrenceRealization P Q)
    (account : Mettapedia.Effects.RunAccount (OccurrenceCat Q) A) :
    Mettapedia.Effects.RunAccount (OccurrenceCat P) A :=
  account.comap realization.toFunctor

/-- Staged accounting charges the same actual target path as direct expansion. -/
theorem pullAccount_comp_of {A : Type uAccount} [Monoid A]
    (earlier : OccurrenceRealization P Q) (later : OccurrenceRealization Q R)
    (account : Mettapedia.Effects.RunAccount (OccurrenceCat R) A)
    {first last : source.Term} (path : OccurrencePath P first last) :
    ((earlier.comp later).pullAccount account).of path =
      (earlier.pullAccount (later.pullAccount account)).of path := by
  change account.of ((earlier.comp later).mapPath path) =
    account.of (later.mapPath (earlier.mapPath path))
  rw [mapPath_comp]
  rfl

end OccurrenceRealization

end Mettapedia.GSLT.Causality.OccurrenceHistory
