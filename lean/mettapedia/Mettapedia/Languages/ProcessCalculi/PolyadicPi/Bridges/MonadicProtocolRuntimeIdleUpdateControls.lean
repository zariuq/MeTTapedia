import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeIdleUpdate

/-!
# Idle communication beside a pending tuple and equal messages

The supplied ordinary and persistent traces select literal frame positions
zero and one. An equal output at position two remains in the frame, and an
additional listener uses the same public channel. The pending tuple retains
its original nonempty source readout throughout both firings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeIdleUpdateControls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open MonadicProtocol Capabilities Ownership RuntimeState RuntimeActors ScopedActiveFrontier
open ActiveMarking ActiveOriginErasure ActiveHeaderInvariant ScopedCommunicationInversion
open ActiveUnarySelectedBoundary RuntimeIdleUpdate

abbrev context : Ctx sig := [.nm, .nm]
def channel : Var context .nm := .zero
def datum : Var context .nm := .succ .zero
def body : Proc (.nm :: context) := out1 (.var channel.succ) (.var .zero)
def message : Proc context := out1 (.var channel) (.var datum)
def call : Call context :=
  ⟨.var datum, .var channel,
    out2 (weaken (weaken (.var channel))) (.var .zero) (.var (.succ .zero))⟩
def registry : Fin 1 → Slot context := fun _ => .pending .first call

theorem registry_live : ∀ owner, Live (registry owner) := fun _ => trivial
theorem pending_readout_is_nonempty (owner : Fin 1) :
    (registry owner).source = out2 (.var channel) (.var datum) (.var channel) ∧
      (registry owner).source ≠ nil := ⟨rfl, by intro same; cases same⟩

def frame (persistent : Bool) : List (Proc context) :=
  [message, receiver persistent (.var channel) body, message, rep (inp1 (.var channel) body)]
def outputPosition (persistent : Bool) : Fin (frame persistent).length := ⟨0, by change 0 < 4; decide⟩
def inputPosition (persistent : Bool) : Fin (frame persistent).length := ⟨1, by change 1 < 4; decide⟩
theorem different_positions (persistent : Bool) : inputPosition persistent ≠ outputPosition persistent := by
  intro same
  have impossible : (1 : Nat) = 0 := congrArg Fin.val same
  cases impossible

theorem heads (persistent : Bool) : ∀ atom ∈ frame persistent, IdleFrame.Head atom := by
  intro atom member
  simp only [frame, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same
  · subst atom; exact .output _ _
  · subst atom; cases persistent
    · exact .input1 _ (.out1 _ _)
    · exact .server1 _ (.out1 _ _)
  · subst atom; exact .output _ _
  · subst atom; exact .server1 _ (.out1 _ _)

def targetChannel : Var (World 1 context) .nm := ambient 1 .nm channel
def targetDatum : Var (World 1 context) .nm := ambient 1 .nm datum
def guard : Proc (.nm :: World 1 context) := rename (liftRen (ambient 1) [.nm]) (lower body)
def guardMarks : ActiveMarking.Tree (Origin 1) := ActiveSyntaxMarking.mark (.idle 1) (lower body)
def publication : Proc (World 1 context) := out1 (.var targetChannel) (.var targetDatum)
def listener : Proc (World 1 context) := inp1 (.var targetChannel) guard
def listenerMarks : ActiveMarking.Tree (Origin 1) := .inp1 (.idle 1) guardMarks
def rest (persistent : Bool) : Proc (World 1 context) :=
  assembly registry (parallel (remainingFrame (frame persistent) (outputPosition persistent) (inputPosition persistent)))
def restMarks (persistent : Bool) : ActiveMarking.Tree (Origin 1) :=
  RuntimeIdleUpdate.parallelMarks (rowMarks registry (frame persistent))
    (remainingKeys (frame persistent) (outputPosition persistent) (inputPosition persistent))

theorem guard_fits : Fits guardMarks guard :=
  (ActiveSyntaxMarking.mark_fits (Origin.idle 1 : Origin 1) (lower body)).rename (liftRen (ambient 1) [.nm])
theorem listener_fits : Fits listenerMarks listener := .inp1 (Origin.idle 1) _ guard_fits
theorem rest_fits (persistent : Bool) : Fits (restMarks persistent) (rest persistent) := by
  have fitted := RuntimeIdleUpdate.parallel_fits (rowMarks registry (frame persistent))
    (rowRender registry (frame persistent))
    (remainingKeys (frame persistent) (outputPosition persistent) (inputPosition persistent))
    (row_fits registry (frame persistent))
  rw [rows_remaining_process] at fitted
  exact fitted

theorem original_reordering (persistent : Bool) :
    Transport (assemblyMarks registry (frame persistent)) (assembly registry (parallel (frame persistent)))
      (.par (.out1 (.idle 0)) (.par (receiverMarks persistent (.idle 1) guardMarks) (restMarks persistent)))
      (par publication (par (receiver persistent (.var targetChannel) guard) (rest persistent))) := by
  have moved := permutation_transport (rowMarks registry (frame persistent)) (rowRender registry (frame persistent))
    (keys_permutation (frame persistent) (outputPosition persistent) (inputPosition persistent) (different_positions persistent))
  change Transport
    (RuntimeIdleUpdate.parallelMarks (rowMarks registry (frame persistent)) (keys (frame persistent)))
    (parallel ((keys (frame persistent)).map (rowRender registry (frame persistent))))
    (.par (rowMarks registry (frame persistent) (some (outputPosition persistent)))
      (.par (rowMarks registry (frame persistent) (some (inputPosition persistent))) (restMarks persistent)))
    (par (rowRender registry (frame persistent) (some (outputPosition persistent)))
      (par (rowRender registry (frame persistent) (some (inputPosition persistent)))
        (parallel ((remainingKeys (frame persistent) (outputPosition persistent) (inputPosition persistent)).map
          (rowRender registry (frame persistent)))))) at moved
  rw [rows_source_marks, rows_source_process,
    (row_output registry (frame persistent) (outputPosition persistent) channel datum rfl).1,
    (row_output registry (frame persistent) (outputPosition persistent) channel datum rfl).2,
    (row_receiver registry (frame persistent) (inputPosition persistent) persistent channel body rfl).1,
    (row_receiver registry (frame persistent) (inputPosition persistent) persistent channel body rfl).2,
    rows_remaining_process] at moved
  exact moved

def residual (persistent : Bool) : Proc (World 1 context) :=
  if persistent then par (rep listener) (rest persistent) else rest persistent
def residualMarks (persistent : Bool) : ActiveMarking.Tree (Origin 1) :=
  if persistent then .par (.rep listenerMarks) (restMarks persistent) else restMarks persistent

theorem residual_fits (persistent : Bool) : Fits (residualMarks persistent) (residual persistent) := by
  cases persistent with
  | false => exact rest_fits false
  | true => exact .par (.rep listener_fits) (rest_fits true)

theorem selected_transport (persistent : Bool) :
    Transport (assemblyMarks registry (frame persistent)) (assembly registry (parallel (frame persistent)))
      (.par (.par (.out1 (.idle 0)) listenerMarks) (residualMarks persistent))
      (par (par publication listener) (residual persistent)) := by
  cases persistent with
  | false =>
      exact (original_reordering false).trans
        (.parAssocBack (.out1 (Origin.idle 0)) listenerMarks (restMarks false) publication listener (rest false))
  | true =>
      exact (original_reordering true).trans
        (.trans (.par (.refl (.out1 (Origin.idle 0)) publication)
          (.par (.repUnfold listenerMarks listener) (.refl (restMarks true) (rest true))))
          (.trans (.par (.refl (.out1 (Origin.idle 0)) publication)
            (.parAssoc listenerMarks (.rep listenerMarks) (restMarks true) listener (rep listener) (rest true)))
            (.parAssocBack (.out1 (Origin.idle 0)) listenerMarks (residualMarks true)
              publication listener (residual true))))

def suppliedTarget (persistent : Bool) : Proc (World 1 context) :=
  par (inst guard (.var targetDatum)) (residual persistent)
def selectedExposure (persistent : Bool) :
    Exposure (assembly registry (parallel (frame persistent))) (suppliedTarget persistent) where
  world := World 1 context
  scope := .nil
  redex := par publication listener
  reduct := inst guard (.var targetDatum)
  selected := .unary (.var targetChannel) (.var targetDatum) guard
  frame := residual persistent
  before := (selected_transport persistent).erase
  after := .refl _

def selectedTrace (persistent : Bool) :
    TracedExposure (assemblyMarks registry (frame persistent)) (selectedExposure persistent) where
  binders := .nil
  redexMarks := .par (.out1 (.idle 0)) listenerMarks
  frameMarks := residualMarks persistent
  continuation := .unary (.var targetChannel) (.var targetDatum) guard (Origin.idle 0) (Origin.idle 1)
    guardMarks guard_fits
  frameFits := residual_fits persistent
  transportedFits := .par (.par (.out1 (Origin.idle 0) _ _) listener_fits) (residual_fits persistent)
  transport := selected_transport persistent
  originalInput := by
    cases persistent with
    | false =>
        simp only [assemblyMarks, frame, IdleFrame.marks, receiver, Bool.false_eq_true, if_false]
        simp only [lower_rep, lower_inp1]
        simp only [rep, inp1, ActiveSyntaxMarking.mark]
        exact .right _ (.right _ (.left _ (.inp1 (Origin.idle 1) _)))
    | true =>
        simp only [assemblyMarks, frame, IdleFrame.marks, receiver, if_true]
        simp only [lower_rep, lower_inp1]
        simp only [rep, inp1, ActiveSyntaxMarking.mark]
        exact .right _ (.right _ (.left _ (.rep (.inp1 (Origin.idle 1) _))))
  originalOutput := by
    simp only [assemblyMarks, frame, IdleFrame.marks, message]
    simp only [lower_out1]
    simp only [out1, ActiveSyntaxMarking.mark]
    exact .right _ (.left _ (.out1 (Origin.idle 0)))

theorem supplied_mixed_receipt (persistent : Bool) :
    StepModulo (assembly registry (parallel (frame persistent))) (suppliedTarget persistent) ∧
      StepModulo (registrySource registry (parallel (frame persistent)))
        (par (inst body (.var datum))
          (registrySource registry (parallel (updatedFrame persistent (frame persistent)
            (outputPosition persistent) (inputPosition persistent))))) ∧
      StructuralEq (suppliedTarget persistent)
        (par (rename (ambient 1) (lower (inst body (.var datum))))
          (registryTarget registry (parallel (updatedFrame persistent (frame persistent)
            (outputPosition persistent) (inputPosition persistent))))) := by
  exact ⟨(selectedExposure persistent).sound,
    idle_receipt registry registry_live (frame persistent) (heads persistent)
      (outputPosition persistent) (inputPosition persistent) (different_positions persistent) persistent channel datum body
      rfl rfl (selectedExposure persistent) (selectedTrace persistent) rfl rfl rfl⟩

theorem ordinary_duplicate_is_retained :
    updatedFrame false (frame false) (outputPosition false) (inputPosition false) =
      [message, rep (inp1 (.var channel) body)] := rfl

theorem persistent_original_and_other_server_are_retained :
    updatedFrame true (frame true) (outputPosition true) (inputPosition true) =
      [rep (inp1 (.var channel) body), message, rep (inp1 (.var channel) body)] := rfl

theorem pending_private_debt_is_unchanged : registryRemaining registry = 2 := rfl

/-- The equal unselected output is a different original occurrence. Replacing
the selected mark by its label would fail the supplied trace's premise. -/
theorem equal_outputs_do_not_replace_selected_origin (persistent : Bool) :
    (frame persistent)[0]'(by change 0 < 4; decide) = (frame persistent)[2]'(by change 2 < 4; decide) ∧
      (selectedTrace persistent).continuation.outputOrigin ≠ (Origin.idle 2 : Origin 1) :=
  ⟨rfl, by change (Origin.idle 0 : Origin 1) ≠ Origin.idle 2; intro same; cases same⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeIdleUpdateControls
