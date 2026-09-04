import Mettapedia.TypeTheory.EqualityFamilyObserverFactorization
import Mettapedia.TypeTheory.GuardedTimeModeTheory

/-!
# Finite revision horizons as split observations

A finite validation horizon is a split observation of unbounded revision
indices: revisions beyond the horizon are mapped to the last visible point,
while every visible finite revision has its evident representative.  The
readout is exact below the horizon and deliberately lossy above it.

The dependent-family criterion distinguishes data that survives this finite
view from data that does not.  Constant semantic values factor through every
horizon.  The family of revision-indexed finite histories does not, because
the horizon identifies adjacent revisions whose history fibres have different
cardinalities.

This is a theorem about finite observation, not a claim that the underlying
revision ground is finite or that finite views determine it.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.RevisionHorizonObserverFactorization

open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.EqualityFamilyObserverFactorization
open Mettapedia.TypeTheory.ExtensionalReadout

/-- Truncate an unbounded revision at a finite visible horizon. -/
def truncateRevision (horizon revision : Nat) : Fin (horizon + 1) :=
  ⟨min revision horizon,
    Nat.lt_succ_of_le (Nat.min_le_right revision horizon)⟩

/-- The finite horizon is a split readout of unbounded revisions. -/
def horizonReadout (horizon : Nat) :
    SplitReadout Nat (Fin (horizon + 1)) where
  observe := truncateRevision horizon
  representative := Fin.val
  observe_representative := by
    intro revision
    apply Fin.ext
    simp [truncateRevision, Nat.min_eq_left
      (Nat.le_of_lt_succ revision.isLt)]

/-- Every revision at or below the horizon is its own canonical
representative. -/
@[simp] theorem canonicalize_below_horizon
    (horizon revision : Nat) (visible : revision ≤ horizon) :
    (horizonReadout horizon).canonicalize revision = revision := by
  simp [horizonReadout, SplitReadout.canonicalize, truncateRevision,
    Nat.min_eq_left visible]

/-- The horizon point and its immediate successor have the same finite
observation. -/
theorem horizon_and_successor_same_observation (horizon : Nat) :
    (horizonReadout horizon).observe horizon =
      (horizonReadout horizon).observe (horizon + 1) := by
  apply Fin.ext
  simp [horizonReadout, truncateRevision]

/-- Hence no finite horizon is faithful to all unbounded revision indices. -/
theorem horizonReadout_not_faithful (horizon : Nat) :
    ¬ (horizonReadout horizon).Faithful := by
  intro faithful
  have impossible : horizon = horizon + 1 :=
    faithful (horizon_and_successor_same_observation horizon)
  omega

theorem horizonReadout_not_exact (horizon : Nat) :
    ¬ (horizonReadout horizon).Exact := by
  rw [(horizonReadout horizon).exact_iff_faithful]
  exact horizonReadout_not_faithful horizon

/-- A finite horizon therefore cannot preserve the equality family of the
unbounded revision index. -/
theorem revisionEquality_does_not_factor (horizon : Nat) :
    ¬ Nonempty
      (EqualityFamilyFactorization
        (horizonReadout horizon).observe) := by
  rw [EqualityFamilyFactorization.nonempty_iff_injective]
  exact horizonReadout_not_faithful horizon

/-- Revision-independent semantics survives every finite horizon. -/
def constantFamilyFactors (horizon : Nat) (Value : Type) :
    FamilyFactorization (horizonReadout horizon).observe
      (fun _ => Value) :=
  FamilyFactorization.constant (horizonReadout horizon).observe Value

/-- One finite token for every revision up to and including the current
revision. -/
def finiteHistoryFamily (revision : Nat) : Type := Fin (revision + 1)

theorem adjacent_history_fibres_not_equivalent (horizon : Nat) :
    ¬ Nonempty
      (finiteHistoryFamily horizon ≃
        finiteHistoryFamily (horizon + 1)) := by
  change ¬ Nonempty (Fin (horizon + 1) ≃ Fin (horizon + 1 + 1))
  rintro ⟨equivalence⟩
  have equalCardinality := Fintype.card_congr equivalence
  simp at equalCardinality

/-- The complete revision-indexed finite-history family cannot descend
through a horizon that identifies adjacent revisions. -/
theorem finiteHistoryFamily_does_not_factor (horizon : Nat) :
    ¬ Nonempty
      (FamilyFactorization (horizonReadout horizon).observe
        finiteHistoryFamily) := by
  exact FamilyFactorization.not_nonempty_of_nonEquivalent_fibres
    (left := horizon) (right := horizon + 1)
    (horizon_and_successor_same_observation horizon)
    (adjacent_history_fibres_not_equivalent horizon)

/-- The unbounded revision identity cannot be reconstructed from the finite
horizon either. -/
theorem revision_identity_does_not_descend (horizon : Nat) :
    ¬ (horizonReadout horizon).FactorsObserver (fun revision => revision) := by
  rw [(horizonReadout horizon).factorsObserver_iff_fibreInvariant]
  intro invariant
  have impossible : horizon = horizon + 1 :=
    invariant (horizon_and_successor_same_observation horizon)
  omega

/-- Complete boundary: finite horizons are surjective and exact on their
visible fragment, but they do not preserve unbounded revision equality,
identity, or a growing history family. -/
theorem finite_horizon_observer_boundary (horizon : Nat) :
    Function.Surjective (horizonReadout horizon).observe ∧
      (∀ revision, revision ≤ horizon →
        (horizonReadout horizon).canonicalize revision = revision) ∧
      ¬ (horizonReadout horizon).Exact ∧
      Nonempty
        (FamilyFactorization (horizonReadout horizon).observe
          (fun _revision : Nat => PUnit.{1})) ∧
      ¬ Nonempty
        (FamilyFactorization (horizonReadout horizon).observe
          finiteHistoryFamily) ∧
      ¬ (horizonReadout horizon).FactorsObserver
        (fun revision => revision) :=
  ⟨(horizonReadout horizon).surjective,
    canonicalize_below_horizon horizon,
    horizonReadout_not_exact horizon,
    ⟨constantFamilyFactors horizon PUnit.{1}⟩,
    finiteHistoryFamily_does_not_factor horizon,
    revision_identity_does_not_descend horizon⟩

#print axioms canonicalize_below_horizon
#print axioms horizonReadout_not_exact
#print axioms revisionEquality_does_not_factor
#print axioms adjacent_history_fibres_not_equivalent
#print axioms finiteHistoryFamily_does_not_factor
#print axioms revision_identity_does_not_descend
#print axioms finite_horizon_observer_boundary

end Mettapedia.TypeTheory.RevisionHorizonObserverFactorization
