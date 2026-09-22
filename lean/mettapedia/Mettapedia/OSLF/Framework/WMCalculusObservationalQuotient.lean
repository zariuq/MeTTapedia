import Mettapedia.OSLF.Framework.WMCalculusReadingMorphism

/-!
# The observational quotient of a lawful WM reading

State equality in a world model is behavioral: two states agree when all
queries yield the same evidence. Core laws make revision respect this
agreement, so both revision and extraction descend to a quotient reading.
The original reading maps to that quotient by a full reading morphism.

The quotient's state equality is exactly observational agreement. It is a
semantic quotient, not by itself a dependent identity-type construction for
an authored language.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient

open Mettapedia.OSLF.Framework.WMCalculusSemantics
open Mettapedia.OSLF.Framework.WMCalculusReadingMorphism

variable {State Query V : Type}

/-- Behavioral agreement as a state setoid. -/
def stateSetoid (R : WMReading State Query V) : Setoid State where
  r := R.Agree .state
  iseqv := ⟨R.agree_refl .state, R.agree_symm .state, R.agree_trans .state⟩

/-- States identified by every observation of a reading. -/
abbrev ObsState (R : WMReading State Query V) := Quotient (stateSetoid R)

/-- The semantic quotient map on states. -/
def classOf (R : WMReading State Query V) (state : State) : ObsState R :=
  Quotient.mk (stateSetoid R) state

/-- The quotient identifies precisely behaviorally agreeing states. -/
theorem classOf_eq_iff_agree (R : WMReading State Query V)
    (first second : State) :
    classOf R first = classOf R second ↔ R.Agree .state first second := by
  constructor
  · intro equal
    exact Quotient.exact equal
  · intro agree
    exact Quotient.sound agree

/-- A query's evidence is well defined on observational classes. -/
def extractObs (R : WMReading State Query V)
    (state : ObsState R) (query : Query) : V :=
  Quotient.liftOn state (fun representative => R.extract representative query)
    (fun _ _ agree => agree query)

/-- Core laws make revision compatible with both state arguments modulo
behavioral agreement. -/
def reviseObs (R : WMReading State Query V) (laws : R.CoreLaws)
    (first second : ObsState R) : ObsState R :=
  Quotient.liftOn₂ first second
    (fun first' second' => classOf R (R.revise first' second'))
    (by
      intro first' second' first'' second'' left right
      apply Quotient.sound
      exact R.agree_trans .state
        (laws.reviseRespectsAgree.left first' first'' second' left)
        (laws.reviseRespectsAgree.right first'' second' second'' right))

/-- The original WM signature interpreted on behavioral state classes. -/
def quotientReading (R : WMReading State Query V) (laws : R.CoreLaws) :
    WMReading (ObsState R) Query V where
  revise := reviseObs R laws
  extract := extractObs R
  combine := R.combine
  zero := R.zero
  world := fun name => classOf R (R.world name)
  query := R.query

/-- The quotient reading still satisfies the exact WM core laws. -/
theorem quotientReading_coreLaws (R : WMReading State Query V)
    (laws : R.CoreLaws) : (quotientReading R laws).CoreLaws := by
  refine ⟨?_, laws.combine_comm, laws.combine_assoc, laws.combine_zero⟩
  intro first second query
  induction first using Quotient.inductionOn with
  | _ first' =>
    induction second using Quotient.inductionOn with
    | _ second' =>
      exact laws.extract_revise first' second' query

/-- The quotient map preserves every operation and named valuation of the
authored WM calculus, hence every typed term denotation and native predicate. -/
def quotientMorphism (R : WMReading State Query V) (laws : R.CoreLaws) :
    ReadingMorphism R (quotientReading R laws) where
  mapState := classOf R
  mapQuery := id
  mapEvidence := id
  revise_comm _ _ := rfl
  extract_comm _ _ := rfl
  combine_comm _ _ := rfl
  zero_comm := rfl
  world_comm _ := rfl
  query_comm _ := rfl

/-- Behavioral agreement becomes literal equality in the quotient reading.
The converse is exact because the quotient keeps the full query carrier. -/
theorem quotientReading_agree_iff_eq (R : WMReading State Query V)
    (laws : R.CoreLaws) (first second : ObsState R) :
    (quotientReading R laws).Agree .state first second ↔ first = second := by
  induction first using Quotient.inductionOn with
  | _ first' =>
    induction second using Quotient.inductionOn with
    | _ second' =>
      exact (classOf_eq_iff_agree R first' second').symm

/-- Raw state identity is strictly stronger whenever a reading has two
distinct states with identical observations. -/
theorem classOf_not_injective_of_distinct_agree (R : WMReading State Query V)
    {first second : State} (distinct : first ≠ second)
    (agree : R.Agree .state first second) :
    ¬ Function.Injective (classOf R) := by
  intro injective
  exact distinct (injective ((classOf_eq_iff_agree R first second).2 agree))

end Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient
