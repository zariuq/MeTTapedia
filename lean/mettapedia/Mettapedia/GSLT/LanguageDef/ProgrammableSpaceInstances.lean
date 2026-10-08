import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceRewrite
import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2ReceiptControls

/-!
# Authored rewriting and MM2 agendas in the same space

The retained store contains both an intrinsically scoped lambda request and
an MM2 conjunction-input transaction. Each is admitted under its own language
and receives its own scope, residual and event account. These are two actual
source interpreters, not two tags attached to one invented transition rule.
The MM2 account below counts atomic commits; it is distinct from the native
structural matching work account.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProgrammableSpaceInstances

open Mettapedia.GSLT.Core.ProgrammableSpace
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.Binding
open LambdaContextualRung LambdaScopedAuthoringComparison
open Mettapedia.Languages.ProcessCalculi.MORK

inductive Tag where
  | rewrite
  | transaction
  deriving DecidableEq

def languages : Tag → Language Atom
  | .rewrite => ProgrammableSpaceRewrite.language ProgrammableSpaceRewrite.Lambda.calculus
  | .transaction => ProgrammableSpaceMM2.language

def transactionPolicy (budget : Nat) : Policy ProgrammableSpaceMM2.language where
  State := Nat
  permits spent _ _ _ _ _ _ next := spent < budget ∧ next = spent + 1

def policies : (tag : Tag) → Policy (languages tag)
  | .rewrite => ProgrammableSpaceRewrite.depthPolicy ProgrammableSpaceRewrite.Lambda.calculus 1
  | .transaction => transactionPolicy 4

abbrev Workspace := Space languages policies

def rewriteRequest := encodeTerm openRedex

def atoms : List Atom := ProgrammableSpaceSyntax.encode rewriteRequest ::
  ProgrammableSpaceMM2ReceiptControls.joinSource

def initial : Workspace := ⟨atoms, [], []⟩

def rewritePosition : Fin atoms.length := ⟨0, by decide⟩
def transactionPosition : Fin atoms.length := ⟨6, by decide⟩

theorem rewrite_admitted :
    Admitted languages policies initial .rewrite rewritePosition rewriteRequest :=
  ProgrammableSpaceRewrite.request_admitted _ _

theorem transaction_admitted :
    Admitted languages policies initial .transaction transactionPosition
      ProgrammableSpaceMM2ReceiptControls.joinRequest := by
  exact ProgrammableSpaceMM2ReceiptControls.join_source_admitted

def registered : Workspace :=
  start languages policies
    (start languages policies initial .rewrite (ProgrammableSpaceRewrite.Lambda.scope [.term])
      (0 : Nat) rewritePosition rewriteRequest rewrite_admitted)
    .transaction .leaveInert (0 : Nat) transactionPosition
      ProgrammableSpaceMM2ReceiptControls.joinRequest transaction_admitted

theorem both_agendas_registered : registered.atoms = atoms ∧ registered.pending.length = 2 := by
  exact start_two_languages languages policies initial .rewrite .transaction
    (ProgrammableSpaceRewrite.Lambda.scope [.term]) .leaveInert (0 : Nat) (0 : Nat)
    rewritePosition transactionPosition rewriteRequest
    ProgrammableSpaceMM2ReceiptControls.joinRequest rewrite_admitted transaction_admitted

theorem scopes_retained :
    (registered.pending.map (sessionKey languages policies)).map Sigma.fst =
      [.rewrite, .transaction] := rfl

theorem data_alone_does_not_execute : ¬ ∃ after, Step languages policies initial after :=
  unrequested_space_is_inert languages policies atoms

/-- The other language's stored request is inert during authored beta. -/
theorem rewrite_event_in_mixed_store :
    (languages .rewrite).advance (ProgrammableSpaceRewrite.Lambda.scope [.term]) atoms
      rewriteRequest
      (ProgrammableSpaceRewrite.Lambda.betaReceipt
        (.var .zero : Term sig [.term, .term] .term)
        (.var .zero : Term sig [.term] .term))
      atoms (encodeTerm openTarget) :=
  ProgrammableSpaceRewrite.Lambda.beta_adapter
    (.var .zero : Term sig [.term, .term] .term)
    (.var .zero : Term sig [.term] .term) atoms

/-- Conversely, the authored request remains a stored atom during an actual
MM2 firing. The transaction still retains its two distinct premise paths. -/
theorem transaction_event_in_mixed_store :
    ∃ receipt after,
      (languages .transaction).advance .leaveInert atoms
        (.pending ProgrammableSpaceMM2ReceiptControls.joinRequest) receipt
        (ProgrammableSpaceSyntax.encode rewriteRequest ::
          (ProgrammableSpaceMM2ReceiptControls.context ++
            [ProgrammableSpaceMM2ReceiptControls.reachable])) after := by
  have selected : MM2MatchingBatch.SelectedFor .leaveInert atoms
      ProgrammableSpaceMM2ReceiptControls.joinRequest.directive := by
    unfold MM2MatchingBatch.SelectedFor
    decide +kernel
  obtain ⟨receipt, after, event⟩ := ProgrammableSpaceMM2.selected_has_event
    .leaveInert atoms ProgrammableSpaceMM2ReceiptControls.joinRequest selected
  refine ⟨receipt, after, ?_⟩
  have target : cFireRuleScopedSourceExecFact atoms
      ProgrammableSpaceMM2ReceiptControls.joinRequest.directive =
        ProgrammableSpaceSyntax.encode rewriteRequest ::
          (ProgrammableSpaceMM2ReceiptControls.context ++
            [ProgrammableSpaceMM2ReceiptControls.reachable]) := by decide +kernel
  rw [target] at event
  exact event

def rewriteSession : Session (languages .rewrite) (policies .rewrite) where
  origin := ⟨atoms, rewritePosition⟩
  scope := ProgrammableSpaceRewrite.Lambda.scope [.term]
  request := rewriteRequest
  residual := rewriteRequest
  policyState := (0 : Nat)

def transactionSession : Session (languages .transaction) (policies .transaction) where
  origin := ⟨atoms, transactionPosition⟩
  scope := .leaveInert
  request := ProgrammableSpaceMM2ReceiptControls.joinRequest
  residual := .pending ProgrammableSpaceMM2ReceiptControls.joinRequest
  policyState := (0 : Nat)

def betaReceipt := ProgrammableSpaceRewrite.Lambda.betaReceipt
  (.var .zero : Term sig [.term, .term] .term)
  (.var .zero : Term sig [.term] .term)

def afterRewrite : Workspace where
  atoms := atoms
  pending := [⟨.rewrite, { rewriteSession with
    residual := encodeTerm openTarget
    policyState := (1 : Nat) }⟩, ⟨.transaction, transactionSession⟩]
  history := [⟨.rewrite, {
    origin := rewriteSession.origin
    scope := rewriteSession.scope
    before := atoms
    after := atoms
    residualBefore := rewriteRequest
    residualAfter := encodeTerm openTarget
    receipt := betaReceipt
    policyBefore := (0 : Nat)
    policyAfter := (1 : Nat) }⟩]

theorem actual_rewrite_action : Step languages policies registered afterRewrite :=
  Step.fire (languages := languages) (policies := policies)
    Tag.rewrite atoms atoms [] [⟨Tag.transaction, transactionSession⟩] []
    rewriteSession betaReceipt (encodeTerm openTarget) (1 : Nat)
    rewrite_event_in_mixed_store ⟨by decide, rfl⟩

theorem rewrite_keeps_transaction :
    afterRewrite.pending[1]? = registered.pending[1]? := rfl

theorem retained_event_has_source_and_policy : SoundHistory languages policies afterRewrite :=
  step_history_sound languages policies actual_rewrite_action (by simp [SoundHistory, registered, start, initial])

end Mettapedia.GSLT.LanguageDef.ProgrammableSpaceInstances
