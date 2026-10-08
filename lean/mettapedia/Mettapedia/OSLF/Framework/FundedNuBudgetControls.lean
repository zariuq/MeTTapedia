import Mettapedia.OSLF.Framework.FundedNuBudgetSeparation

/-!
# Affordable-stage and unaffordable-limit controls

A three-cell instruction purse confirms an actual shallow test. At a deeper
stage the same machine retains an intermediate Boolean while withholding its
verdict. One additional cell earns a finite refutation for the chain. The
persistent loop still waits at that question; silence is not read as falsity.

The general results cover every purse, every unfolding question and every
smaller remaining purse, retaining both the public answer and actual spending.
An affordable finite-stage predicate descends to this observation profile;
the original greatest-fixed-point predicate does not.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FundedNuBudgetControls

open Mettapedia.Logic.ModalMuCalculus Inspection Unfolding StackInspection
open FundedNuAssays
open FundedNuAssayControls (continuation)
open NuInfiniteUnfoldingControls FundedNuBudgetSeparation

theorem actual_affordable_stage :
    observation 3 2 (some 3) = (some true, 3) ∧
      satisfies infiniteChains.toLTS Env.empty (continuation.atStage 2) (some 3) :=
  ⟨by decide, (finite_chain_stage 2 3).2 (by decide)⟩

theorem actual_deeper_prefix_is_quiet :
    observation 3 3 (some 3) = (none, 3) ∧
      (receipt 3 3 (some 3)).endpoint.stack = [true] ∧
      (receipt 3 3 (some 3)).endpoint.pending = [.gatherAny 1] := by
  decide

theorem all_questions_agree_at_this_purse : view 3 (some 3) = view 3 none :=
  bounded_views_agree 3 3 le_rfl

theorem every_smaller_purse_still_agrees (budget : Nat) (within : budget ≤ 3) :
    view budget (some 3) = view budget none := bounded_views_agree 3 budget within

theorem actual_limit_predicates_differ :
    satisfies infiniteChains.toLTS Env.empty (.nu continuation.body) none ∧
      ¬ satisfies infiniteChains.toLTS Env.empty (.nu continuation.body) (some 3) :=
  ⟨infinite_loop_original, finite_chain_original_refuted 3⟩

theorem affordable_stage_positive_factor :
    ∃ classify : (Nat → Option Bool × Nat) → Prop, ∀ state : Option Nat,
      classify (view 3 state) ↔
        satisfies infiniteChains.toLTS Env.empty (continuation.atStage 2) state :=
  affordable_stage_descends 3 2 (by decide)

theorem original_predicate_negative_factor :
    ¬ ∃ classify : (Nat → Option Bool × Nat) → Prop, ∀ state : Option Nat,
      classify (view 3 state) ↔ satisfies infiniteChains.toLTS Env.empty (.nu continuation.body) state :=
  bounded_profile_does_not_classify_limit 3

theorem one_cell_changes_available_information :
    observation 4 4 (some 3) = (some false, 4) ∧ observation 4 4 none = (none, 4) :=
  ⟨one_more_cell_earns_refutation 3, persistent_loop_still_waits 3⟩

theorem zero_purse_makes_no_verdict (index : Nat) :
    observation 0 index none = (none, 0) ∧ observation 0 index (some 0) = (none, 0) := by
  have loopEmpty : observation 0 index none = (none, 0) := by
    rw [loop_observation]
    have unaffordable : ¬ index + 1 ≤ 0 := by omega
    simp only [if_neg unaffordable, Nat.zero_min]
  exact ⟨loopEmpty, (bounded_observations_agree 0 0 index le_rfl).trans loopEmpty⟩

theorem actual_new_refutation_certificate :
    ¬ satisfies infiniteChains.toLTS Env.empty (.nu continuation.body) (some 3) := by
  apply refuted_stage_refutes_original infiniteChains.toLTS continuation 4 (some 3)
  have answer : Funded.publicAnswer (receipt 4 4 (some 3)).endpoint = some false :=
    congrArg Prod.fst (one_more_cell_earns_refutation 3)
  have certificate := ((receipt 4 4 (some 3)).answer_sound infiniteChains
    (continuation.atStage 4) (continuation.stage_admitted 4) emptyEnvironment (some 3) [] 4 false answer).2.2
  simpa only [Funded.ModalCertificate, Mettapedia.GSLT.Causality.ComplementaryAssay.verdictOf,
    emptyEnvironment_read] using certificate

end Mettapedia.OSLF.Framework.FundedNuBudgetControls
