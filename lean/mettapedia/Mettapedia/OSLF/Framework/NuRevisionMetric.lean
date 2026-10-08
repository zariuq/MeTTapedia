import Mettapedia.OSLF.Framework.FundedNuAssays
import Mettapedia.OSLF.Framework.AssayRevisionMetric

/-!
# Revision locality for genuine greatest-fixed-point approximations

The answers of this observation scheme are the actual predicates specified by
capture-avoiding finite unfoldings. The existing first-difference construction
therefore measures a revision's first change of approximation, rather than an
unrelated authored test sequence.

Small finite walks retain earlier stage certificates. Under an earned finite
state stabilization bound they also retain the original hypothesis predicate.
The converse is deliberately absent: equal limit predicates can have different
approximation sequences. Prices and occurrence receipts remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.NuRevision

open Mettapedia.Logic.ModalMuCalculus
open Unfolding
open LogicalMetric AssayRevision
open Mettapedia.GSLT.Causality.ComplementaryAssay

universe u v

variable {State : Type u} {Action : Type v}

def scheme (lts : LTS State Action) :
    ObservationScheme (PositiveHMLBody Action) (fun _ => Set State) where
  satisfies stage hypothesis := sat lts Env.empty (hypothesis.atStage stage)

theorem earlier_stage_preserved (lts : LTS State Action)
    {first second : PositiveHMLBody Action} {depth stage : Nat}
    (close : (scheme lts).distance first second < (1 / 2 : ℝ) ^ depth)
    (earlier : stage ≤ depth) (state : State) :
    satisfies lts Env.empty (first.atStage stage) state ↔
      satisfies lts Env.empty (second.atStage stage) state :=
  Set.ext_iff.mp (earlier_answer_preserved (scheme lts) close earlier) state

theorem earlier_certificate_preserved
    (presentation : Inspection.SuccessorPresentation State Action)
    {first second : PositiveHMLBody Action} {depth stage : Nat}
    (close : (scheme presentation.toLTS).distance first second < (1 / 2 : ℝ) ^ depth)
    (earlier : stage ≤ depth) (branch : Verdict) (state : State) :
    FundedNuAssays.StageCertificate presentation (first, stage) branch state ↔
      FundedNuAssays.StageCertificate presentation (second, stage) branch state := by
  cases branch with
  | confirm => exact earlier_stage_preserved presentation.toLTS close earlier state
  | refute => exact not_congr (earlier_stage_preserved presentation.toLTS close earlier state)

theorem finite_walk_certificate_preserved
    (presentation : Inspection.SuccessorPresentation State Action)
    (walk : Nat → PositiveHMLBody Action) (depth count : Nat)
    (small : ∀ position < count,
      (scheme presentation.toLTS).distance (walk position) (walk (position + 1)) <
        (1 / 2 : ℝ) ^ depth)
    {stage : Nat} (earlier : stage ≤ depth) (branch : Verdict) (state : State) :
    FundedNuAssays.StageCertificate presentation (walk 0, stage) branch state ↔
      FundedNuAssays.StageCertificate presentation (walk count, stage) branch state :=
  earlier_certificate_preserved presentation
    (finite_walk_confined (scheme presentation.toLTS) walk depth count small) earlier branch state

theorem stable_original_preserved [Finite State] (lts : LTS State Action)
    {first second : PositiveHMLBody Action} {depth stage : Nat}
    (close : (scheme lts).distance first second < (1 / 2 : ℝ) ^ depth)
    (earlier : stage ≤ depth) (enough : Nat.card State ≤ stage) (state : State) :
    satisfies lts Env.empty (.nu first.body) state ↔
      satisfies lts Env.empty (.nu second.body) state :=
  (finite_stage_equals_original lts first stage enough state).symm.trans
    ((earlier_stage_preserved lts close earlier state).trans
      (finite_stage_equals_original lts second stage enough state))

theorem indistinguishable_original [Finite State] (lts : LTS State Action)
    {first second : PositiveHMLBody Action}
    (same : (scheme lts).Indistinguishable first second) (state : State) :
    satisfies lts Env.empty (.nu first.body) state ↔
      satisfies lts Env.empty (.nu second.body) state := by
  have stageSame : (scheme lts).satisfies (Nat.card State) first =
      (scheme lts).satisfies (Nat.card State) second := congrFun same (Nat.card State)
  exact (finite_stage_equals_original lts first (Nat.card State) le_rfl state).symm.trans
    ((Set.ext_iff.mp stageSame state).trans
      (finite_stage_equals_original lts second (Nat.card State) le_rfl state))

theorem zero_distance_preserves_original [Finite State] (lts : LTS State Action)
    {first second : PositiveHMLBody Action}
    (zero : (scheme lts).distance first second = 0) (state : State) :
    satisfies lts Env.empty (.nu first.body) state ↔
      satisfies lts Env.empty (.nu second.body) state :=
  indistinguishable_original lts ((scheme lts).distance_eq_zero_iff first second |>.1 zero) state

end Mettapedia.OSLF.Framework.NuRevision
