import Mettapedia.Hyperseed.OpenClawBridge

/-!
# Hyperseed: Regression Test

A tiny finite fixture showing that observations plus closure derive a target query.

Uses a toy observation type, a trivially simple state, and one consequence rule.
-/

namespace Mettapedia.Hyperseed.Regression

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModelFixpointClosure
open scoped ENNReal

/-! ## Toy types -/

/-- Toy query type with three elements. -/
inductive ToyQuery where
  | base
  | derived
  | extra
  deriving DecidableEq, Fintype

/-- Toy observation: just a label. -/
inductive ToyObs where
  | seen

/-- Toy state: a single Evidence value (the state IS evidence). -/
abbrev ToyState := Evidence

/-- Toy world model: evidence for any query is the state itself.
This satisfies `evidence_add` because Evidence addition (hplus) is the
additive monoid structure. -/
noncomputable instance : WorldModel ToyState ToyQuery where
  evidence s _q := s
  evidence_add _W₁ _W₂ _q := rfl

/-! ## Toy kernel -/

/-- A consequence rule: from `base`, derive `derived`.
Sound because both extract the same evidence from the same state. -/
def toyRule : WMConsequenceRuleOn ToyState ToyQuery where
  side := fun _ => True
  premise := .base
  conclusion := .derived
  sound := fun _ => le_refl _

/-- Toy Hyperseed kernel. Ingest is identity (observation doesn't change state). -/
noncomputable def toyKernel : HyperseedKernel ToyObs ToyState ToyQuery where
  ingest _obs s := s
  seedQueries := {ToyQuery.base}
  rules := {toyRule}

/-! ## Regression: observations + closure -/

/-- The seed query `base` is in the Hyperseed closure. -/
theorem base_in_closure (s : ToyState) :
    ToyQuery.base ∈ hyperseedClosure toyKernel s :=
  seed_subset_hyperseedClosure toyKernel s rfl

/-- The derived query is in the Hyperseed closure (via the rule from base). -/
theorem derived_in_closure (s : ToyState) :
    ToyQuery.derived ∈ hyperseedClosure toyKernel s := by
  unfold hyperseedClosure
  apply leastRuleClosure_rule_closed toyKernel.rules s toyKernel.seedQueries
    (r := toyRule)
  · exact Set.mem_singleton toyRule
  · trivial
  · exact base_in_closure s

end Mettapedia.Hyperseed.Regression
