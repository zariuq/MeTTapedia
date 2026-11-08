import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldModel

/-! Executed controls for the fold body: duplicate and error-valued data,
empty input, missing snapshots, order, and a retained pre-publication pause. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldControls

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation
open RecursiveTasks.Contextual RecursiveMachine.Contextual
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open HECollectionFoldModel

def policy : Policy := .unchangedPreservingReady .preserve
def callerFrame : Frame := Controls.argumentAliasFrame
def world : World := ((), [callerFrame])
def errorValue : Entry.Value := .expression .held [.symbol "Error", .symbol "input", .symbol "BadType"]
def values : List Entry.Value := [.grounded (.int 7), .grounded (.int 7), errorValue]
def rows : List Result := values.map (fun value => (value, callerFrame))
def packed (value : Entry.Value) : Entry.Value := .expression .active [value, .grounded (.int 0)]
def pairs : List Entry.Value := values.map packed

theorem row_values : rows.map Prod.fst = values := by simp [rows, Function.comp_def]

theorem fixed_acc : callerFrame.read policy (.var "acc") = .var "acc" := by
  simp only [Frame.read, Entry.Value.substitute]
  exact HEFreshSyntaxBinding.resolve_fresh callerFrame "acc" (by decide)

theorem fixed_item : callerFrame.read policy (.var "item") = .var "item" := by
  simp only [Frame.read, Entry.Value.substitute]
  exact HEFreshSyntaxBinding.resolve_fresh callerFrame "item" (by decide)

theorem stored : List.Forall₂ (StoredPairRel snapshots () world) rows pairs := by
  have each (value : Entry.Value) : StoredPairRel snapshots () world (value, callerFrame) (packed value) :=
    ⟨.int 0, rfl, 0, rfl, rfl⟩
  exact .cons (each _) (.cons (each _) (.cons (each _) .nil))

theorem closed : ∀ row ∈ rows, TypeSubst.typeVars row.1.erase = [] := by
  intro row member
  simp [rows, values, errorValue] at member
  rcases member with rfl | rfl | rfl <;>
    simp [Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList]

theorem duplicates_and_error_source :
    ∃ mark, Stateful.MinimalRel (environment policy) () world [] [] none
      (HECollectionFoldFunction.function pairs (.expression .active []) "acc" "item" "space" .active) callerFrame
      [(.expression mark values, callerFrame)] world (policy := policy) := by
  simpa only [row_values] using source policy world callerFrame "acc" "item" "space" (by decide) (by decide) (by decide)
    fixed_acc fixed_item rows pairs stored closed [] [] none

theorem empty_source :
    ∃ mark, Stateful.MinimalRel (environment policy) () world [] [] none
      (HECollectionFoldFunction.function [] (.expression .active []) "acc" "item" "space" .active) callerFrame
      [(.expression mark [], callerFrame)] world (policy := policy) := by
  simpa only [List.map_nil] using source policy world callerFrame "acc" "item" "space"
    (by decide) (by decide) (by decide) fixed_acc fixed_item [] [] .nil (by simp) [] [] none

theorem duplicate_erasure_changes_result : values ≠ [.grounded (.int 7), errorValue] := by
  intro same
  have size := congrArg List.length same
  simp [values] at size

theorem reverse_append_rejected :
    ¬HECollectionClosedAppend.Step snapshots policy () world
      (.expression .active [.symbol CollectionStdlibSource.appendName, .expression .active [.grounded (.int 1)],
        packed (.grounded (.int 2))])
      (.ok [(.expression .active [.grounded (.int 2), .grounded (.int 1)], Bindings.empty)]) := by
  intro altered
  obtain ⟨captured, _, impossible⟩ := HECollectionClosedAppend.output_root_mark altered
  cases impossible

theorem missing_snapshot_rejected :
    ¬HECollectionClosedAppend.Step snapshots policy () ((), [])
      (.expression .active [.symbol CollectionStdlibSource.appendName, .expression .active [], packed (.grounded (.int 2))])
      (.ok [(.expression .active [.grounded (.int 2)], Bindings.empty)]) := by
  intro altered
  obtain ⟨captured, restored, _⟩ := HECollectionClosedAppend.output_root_mark altered
  obtain ⟨index, _, impossible⟩ := restored
  simp at impossible

def initial : WorldConfiguration Unit World :=
  ⟨world, (), .work (.minimal [] [] none
    (HECollectionFoldFunction.function pairs (.expression .active []) "acc" "item" "space" .active) callerFrame), [], []⟩

def paused (mark : Entry.Status) : WorldConfiguration Unit World :=
  ⟨world, (), .returning [(.expression mark values, callerFrame)], [], []⟩

theorem pause_is_not_completion (mark : Entry.Status) : worldObserve (paused mark) = none := rfl

theorem pause_and_resume : ∃ mark first second,
    let rule := RecursiveExecution.Contextual.Stateful.Protocol.Rule (environment policy) policy
    let reply : List Result := [(.expression mark values, callerFrame)]
    Derivation rule first initial [] (.exhausted (paused mark)) ∧
    Derivation rule second (paused mark) reply (.finished (world, reply)) ∧
    Derivation rule (first + second) initial reply (.finished (world, reply)) := by
  obtain ⟨mark, executed⟩ := retained_run policy world callerFrame "acc" "item" "space"
    (by decide) (by decide) (by decide) fixed_acc fixed_item rows pairs stored closed [] [] none [] []
  have run : WorldSteps (environment policy).view (environment policy).services (environment policy).dispatch
      (environment policy).lookup policy initial (paused mark) (admission := (environment policy).arguments) := by
    simpa only [row_values, initial, paused] using executed
  obtain ⟨first, events, prefixRun, history⟩ := RecursiveExecution.Contextual.Stateful.Protocol.steps_exhausted run
  have emptyEvents : events = [] := by simpa [initial, paused] using history.symm
  subst events
  let reply : List Result := [(.expression mark values, callerFrame)]
  obtain ⟨second, events, suffix⟩ :=
    (RecursiveExecution.Contextual.Stateful.Protocol.completed_iff_steps (environment := environment policy)
      (policy := policy) (paused mark) reply world).mpr
      ⟨_, RecursiveExecution.Contextual.Stateful.drain (environment := environment policy) (policy := policy) () world reply [], rfl, rfl⟩
  obtain ⟨_, _, _, _, suffixHistory⟩ := RecursiveExecution.Contextual.Stateful.Protocol.finished_steps suffix
  have replyEvents : events = reply := by simpa [paused] using suffixHistory.symm
  subst events
  exact ⟨mark, first, second, prefixRun, suffix, by simpa only [List.nil_append] using prefixRun.resume suffix⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldControls
