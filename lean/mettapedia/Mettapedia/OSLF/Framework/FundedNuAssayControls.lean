import Mettapedia.OSLF.Framework.NuRevisionMetric

/-!
# Finite unfolding, paid receipt and revision controls

A real two-state chain separates shallow confirmation from limit truth. A
persistent loop supplies a positive greatest-fixed-point witness. Repeated
successor occurrences preserve the entire transition support while increasing
the actual complete inspection price and changing funded completion.

Equal limit predicates need not identify hypothesis revision sequences.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FundedNuAssayControls

open Mettapedia.Logic.ModalMuCalculus Inspection Unfolding
open Mettapedia.GSLT.Causality ProbeCampaign ComplementaryAssay
open FundedNuAssays

def continuation : PositiveHMLBody Unit :=
  ⟨.diamond () (.var 0), rfl, by decide⟩

def falseBody : PositiveHMLBody Unit := ⟨.ff, rfl, rfl⟩

def chain : SuccessorPresentation Bool Unit where
  successors state _ := if state then [false] else []

def repeatedChain : SuccessorPresentation Bool Unit where
  successors state _ := if state then [false, false] else []

def loop : SuccessorPresentation Unit Unit where
  successors _ _ := [()]

theorem initial_stage_confirms :
    inspect chain (continuation.atStage 0) (continuation.stage_admitted 0)
      emptyEnvironment true = (true, 1) := by decide

theorem shallow_stage_confirms :
    inspect chain (continuation.atStage 1) (continuation.stage_admitted 1)
      emptyEnvironment true = (true, 2) := by decide

theorem decisive_stage_refutes :
    inspect chain (continuation.atStage 2) (continuation.stage_admitted 2)
      emptyEnvironment true = (false, 2) := by decide

theorem chain_original_refuted (state : Bool) :
    ¬ satisfies chain.toLTS Env.empty (.nu continuation.body) state := by
  apply refuted_stage_refutes_original chain.toLTS continuation 2 state
  apply (test_falsehood chain (fun _ _ => 1) (continuation, 2) state).1
  cases state <;> decide

theorem shallow_confirmation_is_not_limit_confirmation :
    StageCertificate chain (continuation, 1) .confirm true ∧
      ¬ satisfies chain.toLTS Env.empty (.nu continuation.body) true :=
  ⟨(test_truth chain (fun _ _ => 1) (continuation, 1) true).1 (by decide),
    chain_original_refuted true⟩

theorem persistent_loop_confirmed :
    satisfies loop.toLTS Env.empty (.nu continuation.body) () := by
  refine ⟨Set.univ, Set.mem_univ (), ?_⟩
  intro state _
  refine ⟨(), ?_, ?_⟩
  · exact List.mem_singleton_self ()
  · exact Set.mem_univ ()

theorem repeated_transition_support (source : Bool) (action : Unit) (target : Bool) :
    chain.toLTS.trans source action target ↔ repeatedChain.toLTS.trans source action target := by
  cases source <;> simp [SuccessorPresentation.toLTS, chain, repeatedChain]

theorem repeated_semantics {n : Nat} (environment : Env Bool n)
    (formula : Formula Unit n) (state : Bool) :
    satisfies chain.toLTS environment formula state ↔
      satisfies repeatedChain.toLTS environment formula state :=
  satisfies_congr repeated_transition_support (fun _ _ => Iff.rfl) formula state

theorem repeated_stage_price :
    inspect repeatedChain (continuation.atStage 1) (continuation.stage_admitted 1)
      emptyEnvironment true = (true, 3) := by decide

def request : Request (Question Unit) Bool Unit Nat where
  question := (continuation, 1)
  session := 12
  provider := ()
  client := 7
  arrival := some true

def chainRound := completedRound (protocol chain (fun _ _ => 1)) request 3

def repeatedRound := completedRound (protocol repeatedChain (fun _ _ => 1)) request 3

theorem chain_paid_response : chainRound.responses = {(12, Verdict.confirm, 7, true)} := by decide

theorem chain_paid_ledger : chainRound.remaining = 0 ∧ chainRound.spent = 3 := by
  have remaining : chainRound.remaining = 0 := by decide
  have ledger := chainRound.ledger
  exact ⟨remaining, by omega⟩

theorem repeated_price_prevents_response :
    repeatedRound.responses = 0 ∧ repeatedRound.remaining = 2 ∧ repeatedRound.spent = 1 := by
  have quiet : repeatedRound.responses = 0 := by decide
  have remaining : repeatedRound.remaining = 2 := by decide
  have ledger := repeatedRound.ledger
  exact ⟨quiet, remaining, by omega⟩

theorem shallow_response_does_not_prove_original :
    (12, Verdict.confirm, 7, true) ∈ chainRound.responses ∧
      ¬ satisfies chain.toLTS Env.empty (.nu continuation.body) true :=
  ⟨by rw [chain_paid_response]; exact Multiset.mem_singleton_self _, chain_original_refuted true⟩

def decisiveRequest : Request (Question Unit) Bool Unit Nat :=
  {request with question := (continuation, 2)}

def decisiveRound := completedRound (protocol chain (fun _ _ => 1)) decisiveRequest 3

theorem decisive_paid_response :
    decisiveRound.responses = {(12, Verdict.refute, 7, true)} := by decide

theorem decisive_response_refutes_original :
    ¬ satisfies chain.toLTS Env.empty (.nu continuation.body) true :=
  received_refutation chain (fun _ _ => 1) decisiveRound true
    (by rw [decisive_paid_response]; exact Multiset.mem_singleton_self _)

theorem false_body_original_refuted (state : Bool) :
    ¬ satisfies chain.toLTS Env.empty (.nu falseBody.body) state := by
  intro original
  obtain ⟨candidate, member, closed⟩ := original
  exact closed state member

theorem equal_limits (state : Bool) :
    satisfies chain.toLTS Env.empty (.nu continuation.body) state ↔
      satisfies chain.toLTS Env.empty (.nu falseBody.body) state :=
  iff_of_false (chain_original_refuted state) (false_body_original_refuted state)

theorem different_actual_first_stage :
    (NuRevision.scheme chain.toLTS).satisfies 1 continuation ≠
      (NuRevision.scheme chain.toLTS).satisfies 1 falseBody := by
  intro same
  have atTrue := Set.ext_iff.mp same true
  have confirms : satisfies chain.toLTS Env.empty (continuation.atStage 1) true :=
    (test_truth chain (fun _ _ => 1) (continuation, 1) true).1 (by decide)
  have refutes : ¬ satisfies chain.toLTS Env.empty (falseBody.atStage 1) true := by
    change ¬ False
    exact not_false
  exact refutes (atTrue.mp confirms)

theorem equal_limits_do_not_give_zero_revision_distance :
    (NuRevision.scheme chain.toLTS).distance continuation falseBody ≠ 0 := by
  intro zero
  have same := ((NuRevision.scheme chain.toLTS).distance_eq_zero_iff continuation falseBody).1 zero
  exact different_actual_first_stage (congrFun same 1)

end Mettapedia.OSLF.Framework.FundedNuAssayControls
