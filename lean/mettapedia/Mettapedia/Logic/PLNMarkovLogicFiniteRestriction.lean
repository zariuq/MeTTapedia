import Mettapedia.Logic.PLNMarkovLogicCountable
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite Restriction for Countable MLNs

This module proves the first exact reduction theorem for the infinite-first MLN lane:

if the countable semantics has finite live support, then the full countable query
probability equals the probability of the finite restriction induced by that support.
-/

namespace Mettapedia.Logic.PLNMarkovLogicFiniteRestriction

open scoped ENNReal BigOperators
open Mettapedia.Logic.PLNMarkovLogicAbstract
open Mettapedia.Logic.PLNMarkovLogicCountable

variable {World Query Feature : Type*} [Encodable World]

/-- A finite live support witness: outside the given finite set, world weight vanishes. -/
structure FiniteSupportWitness
    (M : CountableMLNSemantics World Query Feature)
    (support : Finset World) : Prop where
  zero_outside : ∀ w, w ∉ support → M.worldWeight w = 0

/-- Restricted world type induced by a finite support. -/
abbrev RestrictedWorld (support : Finset World) := { w : World // w ∈ support }

/-- Query mass computed only over the finite support. -/
noncomputable def restrictedQueryMass
    (M : CountableMLNSemantics World Query Feature)
    (support : Finset World) (q : Query) : ENNReal :=
  by
    classical
    exact Finset.sum support (fun w => if M.queryHolds q w then M.worldWeight w else 0)

/-- Total mass computed only over the finite support. -/
noncomputable def restrictedTotalMass
    (M : CountableMLNSemantics World Query Feature)
    (support : Finset World) : ENNReal :=
  Finset.sum support (fun w => M.worldWeight w)

/-- The restricted finite-support world mass. -/
noncomputable def restrictedWorldWeight
    (M : CountableMLNSemantics World Query Feature)
    (support : Finset World) (w : RestrictedWorld (World := World) support) : ENNReal :=
  M.worldWeight w.1

/-- Restricted query truth is inherited pointwise. -/
def restrictedQueryHolds
    (M : CountableMLNSemantics World Query Feature)
    (support : Finset World) (q : Query)
    (w : RestrictedWorld (World := World) support) : Prop :=
  M.queryHolds q w.1

theorem queryMass_eq_restrictedQueryMass_of_finiteSupport
    (M : CountableMLNSemantics World Query Feature)
    {support : Finset World} (hs : FiniteSupportWitness M support) (q : Query) :
    CountableMLNSemantics.queryMass M q = restrictedQueryMass M support q := by
  classical
  unfold CountableMLNSemantics.queryMass restrictedQueryMass
  refine (tsum_eq_sum (s := support) ?_).trans rfl
  intro w hw
  have hw' : w ∉ support := by
    intro hmem
    exact hw hmem
  by_cases hq : M.queryHolds q w
  · simp [hq, hs.zero_outside w hw']
  · simp [hq]

theorem totalMass_eq_restrictedTotalMass_of_finiteSupport
    (M : CountableMLNSemantics World Query Feature)
    {support : Finset World} (hs : FiniteSupportWitness M support) :
    CountableMLNSemantics.totalMass M = restrictedTotalMass M support := by
  unfold CountableMLNSemantics.totalMass restrictedTotalMass
  refine (tsum_eq_sum (s := support) ?_).trans rfl
  intro w hw
  exact hs.zero_outside w hw

/-- The finite restriction inherits a mass semantics structure. -/
noncomputable def restrictedMassSemantics
    (M : CountableMLNSemantics World Query Feature)
    {support : Finset World} (hs : FiniteSupportWitness M support) : MassSemantics Query where
  queryMass := restrictedQueryMass M support
  totalMass := restrictedTotalMass M support
  queryMass_le_total := by
    intro q
    rw [← queryMass_eq_restrictedQueryMass_of_finiteSupport M hs q]
    rw [← totalMass_eq_restrictedTotalMass_of_finiteSupport M hs]
    exact M.queryMass_le_totalMass q
  totalMass_ne_top := by
    rw [← totalMass_eq_restrictedTotalMass_of_finiteSupport M hs]
    exact M.totalMass_ne_top

theorem restricted_queryProb_eq_full_queryProb_of_finite_support
    (M : CountableMLNSemantics World Query Feature)
    {support : Finset World} (hs : FiniteSupportWitness M support) (q : Query) :
    (restrictedMassSemantics M hs).queryProb q = (M.toMassSemantics.queryProb q) := by
  have hmass :
      restrictedQueryMass M support q = CountableMLNSemantics.queryMass M q := by
    symm
    exact queryMass_eq_restrictedQueryMass_of_finiteSupport M hs q
  have htotal :
      restrictedTotalMass M support = CountableMLNSemantics.totalMass M := by
    symm
    exact totalMass_eq_restrictedTotalMass_of_finiteSupport M hs
  simp [restrictedMassSemantics, CountableMLNSemantics.toMassSemantics,
    MassSemantics.queryProb, hmass, htotal]

end Mettapedia.Logic.PLNMarkovLogicFiniteRestriction
