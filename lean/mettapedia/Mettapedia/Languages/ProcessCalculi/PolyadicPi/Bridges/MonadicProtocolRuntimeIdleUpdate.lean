import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeActors
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveUnaryPersistentBoundary

/-!
# Literal idle lookup occurrences beside the actual tuple registry

Finite-list extraction transports the original constructor marks together
with their actual processes. The selected frame positions are erased as
positions, so equal terms remain different occurrences. A supplied exposure
and its given trace retain their endpoint and selected origins through this
reordering; the unchanged tuple registry remains in the actual residual.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeIdleUpdate

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Capabilities Ownership RuntimeState RuntimeActors ScopedActiveFrontier
open ActiveMarking ActiveOriginErasure ActiveHeaderInvariant ScopedCommunicationInversion
open ActiveUnarySelectedBoundary

universe u v

/-- Each occurrence keeps its previously supplied mark. -/
def parallelMarks {α : Type u} {Label : Type v} (marked : α → ActiveMarking.Tree Label) :
    List α → ActiveMarking.Tree Label
  | [] => .nil
  | first :: rest => .par (marked first) (parallelMarks marked rest)

/-- A permutation transports actual process constructors and their original
marks in both directions. No structural unfolding reassigns an occurrence. -/
theorem permutation_transport {α : Type u} {Label : Type v} {Γ : Ctx sig}
    (marked : α → ActiveMarking.Tree Label) (render : α → Proc Γ)
    {first second : List α} (permutation : first.Perm second) :
    Transport (parallelMarks marked first) (parallel (first.map render))
      (parallelMarks marked second) (parallel (second.map render)) := by
  induction permutation with
  | nil => exact .refl .nil nil
  | cons head _ ih => exact .par (.refl (marked head) (render head)) ih
  | swap first second rest =>
      exact .trans
        (.parAssocBack (marked second) (marked first) (parallelMarks marked rest)
          (render second) (render first) (parallel (rest.map render)))
        (.trans
          (.par (.parComm (marked second) (marked first) (render second) (render first))
            (.refl (parallelMarks marked rest) (parallel (rest.map render))))
          (.parAssoc (marked first) (marked second) (parallelMarks marked rest)
            (render first) (render second) (parallel (rest.map render))))
  | trans _ _ earlier later => exact .trans earlier later

theorem one_position_permutation {α : Type u} [DecidableEq α]
    (positions : List α) (chosen : α) (present : chosen ∈ positions) :
    positions.Perm (chosen :: positions.erase chosen) := List.perm_cons_erase present

theorem two_position_permutation {α : Type u} [DecidableEq α]
    (positions : List α) (output input : α) (outputPresent : output ∈ positions)
    (inputPresent : input ∈ positions) (different : input ≠ output) :
    positions.Perm (output :: input :: (positions.erase output).erase input) :=
  (one_position_permutation positions output outputPresent).trans
    (.cons output (one_position_permutation (positions.erase output) input
      ((List.mem_erase_of_ne different).mpr inputPresent)))

/-- This helper exposes one literal occurrence while preserving its original
mark; it also applies to registry publications indexed by their positions. -/
theorem one_position_transport {α : Type u} [DecidableEq α] {Label : Type v} {Γ : Ctx sig}
    (marked : α → ActiveMarking.Tree Label) (render : α → Proc Γ)
    (positions : List α) (chosen : α) (present : chosen ∈ positions) :
    Transport (parallelMarks marked positions) (parallel (positions.map render))
      (.par (marked chosen) (parallelMarks marked (positions.erase chosen)))
      (par (render chosen) (parallel ((positions.erase chosen).map render))) :=
  permutation_transport marked render (one_position_permutation positions chosen present)

theorem two_position_transport {α : Type u} [DecidableEq α] {Label : Type v} {Γ : Ctx sig}
    (marked : α → ActiveMarking.Tree Label) (render : α → Proc Γ)
    (positions : List α) (output input : α) (outputPresent : output ∈ positions)
    (inputPresent : input ∈ positions) (different : input ≠ output) :
    Transport (parallelMarks marked positions) (parallel (positions.map render))
      (.par (marked output) (.par (marked input)
        (parallelMarks marked ((positions.erase output).erase input))))
      (par (render output) (par (render input)
        (parallel (((positions.erase output).erase input).map render)))) :=
  permutation_transport marked render
    (two_position_permutation positions output input outputPresent inputPresent different)

/-- Reordering the original source keeps the supplied exposure, exact
continuation and selected origins. Its trace is composed with the real
constructor transport rather than regenerated with arbitrary labels. -/
theorem rebase_trace {Label : Type v} {Γ : Ctx sig}
    {original rebased : ActiveMarking.Tree Label} {source newSource target : Proc Γ}
    {actual : Exposure source target} (traced : TracedExposure original actual)
    (before : Transport rebased newSource original source) :
    ∃ result : TracedExposure rebased (actual.changeSource before.erase),
      result.continuation.inputOrigin = traced.continuation.inputOrigin ∧
        result.continuation.outputOrigin = traced.continuation.outputOrigin := by
  obtain ⟨input⟩ := before.selection_back _ _ ⟨traced.originalInput⟩
  obtain ⟨output⟩ := before.selection_back _ _ ⟨traced.originalOutput⟩
  let result : TracedExposure rebased (actual.changeSource before.erase) :=
    { binders := traced.binders
      redexMarks := traced.redexMarks
      frameMarks := traced.frameMarks
      continuation := traced.continuation
      frameFits := traced.frameFits
      transportedFits := traced.transportedFits
      transport := before.trans traced.transport
      originalInput := input
      originalOutput := output }
  exact ⟨result, rfl, rfl⟩

theorem parallelMarks_map {α : Type u} {β : Type*} {Label : Type v}
    (marked : α → ActiveMarking.Tree Label) (map : β → α) (positions : List β) :
    parallelMarks marked (positions.map map) = parallelMarks (fun position => marked (map position)) positions := by
  induction positions with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, parallelMarks, ih]

/-- Enumerating the original list positions reproduces its original marking
exactly, including the original numerical labels beneath persistent heads. -/
theorem indexed_marks {Label : Type} {Γ : Ctx sig} (labels : Nat → Label)
    (frame : List (Proc Γ)) (offset : Nat) :
    parallelMarks (fun position : Fin frame.length =>
      ActiveSyntaxMarking.mark (labels (offset + position.val)) (lower frame[position.val]))
      (List.finRange frame.length) = IdleFrame.marks labels offset frame := by
  induction frame generalizing offset with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.length_cons, List.finRange_succ, parallelMarks, parallelMarks_map, Fin.val_zero, Nat.add_zero,
        List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ, IdleFrame.marks]
      congr 1
      simpa only [Nat.add_assoc, Nat.add_comm 1] using ih (offset + 1)

theorem indexed_parallel {Γ Δ : Ctx sig} (frame : List (Proc Γ)) (render : Proc Γ → Proc Δ) :
    parallel ((List.finRange frame.length).map (fun position => render frame[position.val])) =
      parallel (frame.map render) := by
  rw [← List.ofFn_eq_map, List.ofFn_getElem_eq_map]

def remainingPositions {Γ : Ctx sig} (frame : List (Proc Γ)) (output input : Fin frame.length) :
    List (Fin frame.length) := ((List.finRange frame.length).erase output).erase input

/-- Removal uses literal original positions, never equality of process terms. -/
def remainingFrame {Γ : Ctx sig} (frame : List (Proc Γ)) (output input : Fin frame.length) : List (Proc Γ) :=
  (remainingPositions frame output input).map (fun position => frame[position.val])

def updatedFrame {Γ : Ctx sig} (persistent : Bool) (frame : List (Proc Γ))
    (output input : Fin frame.length) : List (Proc Γ) :=
  if persistent then frame[input.val] :: remainingFrame frame output input else remainingFrame frame output input

/-- The registry is one unchanged block. Each idle key is an original list
position, so extraction also preserves equal process occurrences. -/
def keys {Γ : Ctx sig} (frame : List (Proc Γ)) : List (Option (Fin frame.length)) :=
  none :: (List.finRange frame.length).map some

def remainingKeys {Γ : Ctx sig} (frame : List (Proc Γ)) (output input : Fin frame.length) :
    List (Option (Fin frame.length)) := none :: (remainingPositions frame output input).map some

def rowMarks {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (frame : List (Proc Γ)) :
    Option (Fin frame.length) → ActiveMarking.Tree (Origin n)
  | none => RuntimeActors.parallelMarks (entries registry)
  | some position => ActiveSyntaxMarking.mark (.idle position.val) (lower frame[position.val])

def rowRender {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (frame : List (Proc Γ)) :
    Option (Fin frame.length) → Proc (World n Γ)
  | none => parallel ((entries registry).map Actor.render)
  | some position => rename (ambient n) (lower frame[position.val])

theorem keys_permutation {Γ : Ctx sig} (frame : List (Proc Γ)) (output input : Fin frame.length)
    (different : input ≠ output) :
    (keys frame).Perm (some output :: some input :: remainingKeys frame output input) := by
  have selected := (two_position_permutation (List.finRange frame.length) output input
    (List.mem_finRange _) (List.mem_finRange _) different).map some
  exact (List.Perm.cons none selected).trans
    ((List.Perm.swap (some output) none _).trans
      (.cons (some output) (List.Perm.swap (some input) none _)))

theorem rows_source_marks {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (frame : List (Proc Γ)) :
    parallelMarks (rowMarks registry frame) (keys frame) = assemblyMarks registry frame := by
  simp only [keys, parallelMarks, rowMarks, parallelMarks_map, assemblyMarks]
  congr 1
  simpa only [Nat.zero_add] using indexed_marks (Origin.idle (n := n)) frame 0

theorem rows_source_process {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (frame : List (Proc Γ)) :
    parallel ((keys frame).map (rowRender registry frame)) = assembly registry (parallel frame) := by
  simp only [keys, List.map_cons, List.map_map, parallel, rowRender, Function.comp_def,
    assembly]
  rw [indexed_parallel frame (fun process => rename (ambient n) (lower process))]
  rw [← IdleFrame.parallel_lower, parallel_rename, List.map_map]
  rfl

theorem rows_remaining_process {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (frame : List (Proc Γ)) (output input : Fin frame.length) :
    parallel ((remainingKeys frame output input).map (rowRender registry frame)) =
      assembly registry (parallel (remainingFrame frame output input)) := by
  simp only [remainingKeys, remainingFrame, List.map_cons, List.map_map, parallel, rowRender,
    Function.comp_def, assembly]
  rw [← IdleFrame.parallel_lower, parallel_rename, List.map_map, List.map_map]
  rfl

theorem remaining_position_distinct {Γ : Ctx sig} (frame : List (Proc Γ))
    (output input position : Fin frame.length) (present : position ∈ remainingPositions frame output input) :
    position ≠ input ∧ position ≠ output := by
  have second := ((List.nodup_finRange frame.length).erase output).mem_erase_iff.mp present
  exact ⟨second.1, ((List.nodup_finRange frame.length).mem_erase_iff.mp second.2).1⟩

theorem remaining_heads {Γ : Ctx sig} (frame : List (Proc Γ)) (output input : Fin frame.length)
    (heads : ∀ atom ∈ frame, IdleFrame.Head atom) :
    ∀ atom ∈ remainingFrame frame output input, IdleFrame.Head atom := by
  intro atom member
  obtain ⟨position, _, same⟩ := List.mem_map.mp member
  subst atom
  exact heads _ (List.getElem_mem position.isLt)

theorem parallel_fits {α : Type u} {Label : Type v} {Γ : Ctx sig}
    (marked : α → ActiveMarking.Tree Label) (render : α → Proc Γ) (positions : List α)
    (fitted : ∀ position, Fits (marked position) (render position)) :
    Fits (parallelMarks marked positions) (parallel (positions.map render)) := by
  induction positions with
  | nil => exact .nil
  | cons first rest ih => exact .par (fitted first) ih

theorem row_fits {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (frame : List (Proc Γ))
    (position : Option (Fin frame.length)) : Fits (rowMarks registry frame position) (rowRender registry frame position) := by
  cases position with
  | none => exact RuntimeActors.parallel_fits _
  | some position => exact (ActiveSyntaxMarking.mark_fits _ _).rename (ambient n)

theorem actor_unused {Γ : Ctx sig} {n : Nat} (actor : Actor n Γ) : ScopedOpening.Vacuous actor.render := by
  cases actor with
  | publication => simp only [Actor.render, out1, ScopedOpening.Vacuous]
  | waiter => simp only [Actor.render]; rw [input_header]; simp only [inp1, ScopedOpening.Vacuous]
  | output => simp only [Actor.render]; rw [output_header]; simp only [out1, ScopedOpening.Vacuous]
  | input => simp only [Actor.render]; rw [input_header]; simp only [inp1, ScopedOpening.Vacuous]

theorem actor_single {Γ : Ctx sig} {n : Nat} (actor : Actor n Γ) : SingleBodies actor.render := by
  cases actor with
  | publication => simp only [Actor.render, out1, SingleBodies]
  | waiter => simp only [Actor.render]; rw [input_header]; simp only [inp1, SingleBodies]
  | output => simp only [Actor.render]; rw [output_header]; simp only [out1, SingleBodies]
  | input => simp only [Actor.render]; rw [input_header]; simp only [inp1, SingleBodies]

theorem actors_unused {Γ : Ctx sig} {n : Nat} (actors : List (Actor n Γ)) :
    ScopedOpening.Vacuous (parallel (actors.map Actor.render)) := by
  induction actors with
  | nil => simp only [List.map_nil, parallel, nil, ScopedOpening.Vacuous]
  | cons first rest ih =>
      simp only [List.map_cons, parallel, par, ScopedOpening.Vacuous]
      exact ⟨actor_unused first, ih⟩

theorem actors_single {Γ : Ctx sig} {n : Nat} (actors : List (Actor n Γ)) :
    SingleBodies (parallel (actors.map Actor.render)) := by
  induction actors with
  | nil => simp only [List.map_nil, parallel, nil, SingleBodies]
  | cons first rest ih =>
      simp only [List.map_cons, parallel, par, SingleBodies]
      exact ⟨actor_single first, ih⟩

theorem assembly_unused {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (frame : List (Proc Γ))
    (heads : ∀ atom ∈ frame, IdleFrame.Head atom) : ScopedOpening.Vacuous (assembly registry (parallel frame)) := by
  simp only [assembly, par, ScopedOpening.Vacuous]
  exact ⟨actors_unused _, (ScopedOpening.vacuous_rename _ _).mpr (IdleFrame.unused frame heads)⟩

theorem assembly_single {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (frame : List (Proc Γ))
    (heads : ∀ atom ∈ frame, IdleFrame.Head atom) : SingleBodies (assembly registry (parallel frame)) := by
  simp only [assembly, par, SingleBodies]
  exact ⟨actors_single _, (singleBodies_rename _ _).mpr (IdleFrame.single frame heads)⟩

theorem actor_count_zero {Γ : Ctx sig} {n : Nat} (selected : Origin n → Bool) (actor : Actor n Γ)
    (notChosen : selected actor.origin = false) : originCount selected actor.marks = 0 := by
  cases actor with
  | publication => simp only [Actor.marks, Actor.render, ActiveSyntaxMarking.mark, out1, originCount,
      notChosen, Bool.false_eq_true, if_false]
  | waiter =>
      simp only [Actor.marks, Actor.render]
      rw [input_header]
      simp only [inp1, ActiveSyntaxMarking.mark, originCount, notChosen, Bool.false_eq_true, if_false]
  | output =>
      simp only [Actor.marks, Actor.render]
      rw [output_header]
      simp only [out1, ActiveSyntaxMarking.mark, originCount, notChosen, Bool.false_eq_true, if_false]
  | input =>
      simp only [Actor.marks, Actor.render]
      rw [input_header]
      simp only [inp1, ActiveSyntaxMarking.mark, originCount, notChosen, Bool.false_eq_true, if_false]

theorem actors_count_zero {Γ : Ctx sig} {n : Nat} (selected : Origin n → Bool) (actors : List (Actor n Γ))
    (notChosen : ∀ actor ∈ actors, selected actor.origin = false) :
    originCount selected (RuntimeActors.parallelMarks actors) = 0 := by
  induction actors with
  | nil => rfl
  | cons first rest ih =>
      simp only [RuntimeActors.parallelMarks, originCount,
        actor_count_zero selected first (notChosen first List.mem_cons_self), zero_add]
      exact ih (fun actor member => notChosen actor (List.mem_cons_of_mem _ member))

theorem idle_count_zero {Label : Type} {Γ : Ctx sig} (selected : Label → Bool)
    (origin : Label) {atom : Proc Γ} (head : IdleFrame.Head atom) (notChosen : selected origin = false) :
    originCount selected (ActiveSyntaxMarking.mark origin (lower atom)) = 0 := by
  cases head with
  | output => rw [lower_out1]; simp only [out1, ActiveSyntaxMarking.mark, originCount, notChosen,
      Bool.false_eq_true, if_false]
  | input1 => rw [lower_inp1]; simp only [inp1, ActiveSyntaxMarking.mark, originCount, notChosen,
      Bool.false_eq_true, if_false]
  | input2 => rw [lower_inp2]; simp only [receivePair, inp1, ActiveSyntaxMarking.mark, originCount, notChosen,
      Bool.false_eq_true, if_false]
  | server1 => rw [lower_rep, lower_inp1]; simp only [rep, inp1, ActiveSyntaxMarking.mark, originCount, notChosen,
      Bool.false_eq_true, if_false]
  | server2 => rw [lower_rep, lower_inp2]; simp only [rep, receivePair, inp1, ActiveSyntaxMarking.mark, originCount,
      notChosen, Bool.false_eq_true, if_false]

theorem parallel_count_zero {α : Type u} {Label : Type v} (selected : Label → Bool)
    (marked : α → ActiveMarking.Tree Label) (positions : List α)
    (zero : ∀ position ∈ positions, originCount selected (marked position) = 0) :
    originCount selected (parallelMarks marked positions) = 0 := by
  induction positions with
  | nil => rfl
  | cons first rest ih =>
      simp only [parallelMarks, originCount, zero first List.mem_cons_self, zero_add]
      exact ih (fun position member => zero position (List.mem_cons_of_mem _ member))

theorem lower_receiver {Γ : Ctx sig} (persistent : Bool) (channel : Name Γ) (body : Proc (.nm :: Γ)) :
    lower (receiver persistent channel body) = receiver persistent channel (lower body) := by
  cases persistent <;> simp only [receiver, Bool.false_eq_true, if_false, if_true, lower_rep, lower_inp1]

theorem rename_receiver {Γ Δ : Ctx sig} (persistent : Bool) (channel : Name Γ)
    (body : Proc (.nm :: Γ)) (environment : Ren sig Γ Δ) :
    rename environment (receiver persistent channel body) =
      receiver persistent (rename environment channel) (rename (liftRen environment [.nm]) body) := by
  cases persistent <;> simp only [receiver, Bool.false_eq_true, if_false, if_true, rename_rep, rename_inp1]

theorem mark_receiver {Label : Type} {Γ : Ctx sig} (persistent : Bool) (origin : Label)
    (channel : Name Γ) (body : Proc (.nm :: Γ)) :
    ActiveSyntaxMarking.mark origin (receiver persistent channel body) =
      receiverMarks persistent origin (ActiveSyntaxMarking.mark origin body) := by
  cases persistent <;> simp only [receiver, receiverMarks, Bool.false_eq_true, if_false, if_true,
    rep, inp1, ActiveSyntaxMarking.mark]

theorem row_output {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (frame : List (Proc Γ))
    (position : Fin frame.length) (channel datum : Var Γ .nm)
    (original : frame[position.val] = out1 (.var channel) (.var datum)) :
    rowMarks registry frame (some position) = .out1 (.idle position.val) ∧
      rowRender registry frame (some position) = out1 (.var (ambient n .nm channel)) (.var (ambient n .nm datum)) := by
  constructor
  · rw [rowMarks, original, lower_out1]
    simp only [out1, ActiveSyntaxMarking.mark]
  · rw [rowRender, original, lower_out1, rename_out1]
    rfl

theorem row_receiver {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (frame : List (Proc Γ))
    (position : Fin frame.length) (persistent : Bool) (channel : Var Γ .nm) (body : Proc (.nm :: Γ))
    (original : frame[position.val] = receiver persistent (.var channel) body) :
    rowMarks registry frame (some position) =
        receiverMarks persistent (.idle position.val) (ActiveSyntaxMarking.mark (.idle position.val) (lower body)) ∧
      rowRender registry frame (some position) = receiver persistent (.var (ambient n .nm channel))
        (rename (liftRen (ambient n) [.nm]) (lower body)) := by
  constructor
  · rw [rowMarks, original, lower_receiver, mark_receiver]
  · rw [rowRender, original, lower_receiver, rename_receiver]
    rfl

theorem remaining_count_zero {Γ : Ctx sig} {n : Nat} [DecidableEq (Origin n)]
    (registry : Fin n → Slot Γ) (frame : List (Proc Γ)) (output input : Fin frame.length)
    (heads : ∀ atom ∈ frame, IdleFrame.Head atom) :
    originCount (fun origin => decide (origin = .idle input.val ∨ origin = .idle output.val))
      (parallelMarks (rowMarks registry frame) (remainingKeys frame output input)) = 0 := by
  simp only [remainingKeys, parallelMarks, rowMarks, originCount, parallelMarks_map]
  have actors : originCount (fun origin => decide (origin = Origin.idle input.val ∨ origin = Origin.idle output.val))
      (RuntimeActors.parallelMarks (entries registry)) = 0 := by
    apply actors_count_zero
    intro actor _
    cases actor <;> simp only [Actor.origin, reduceCtorEq, false_or, decide_false]
  rw [actors, zero_add]
  apply parallel_count_zero
  intro position present
  apply idle_count_zero _ _ (heads _ (List.getElem_mem position.isLt))
  obtain ⟨differentInput, differentOutput⟩ := remaining_position_distinct frame output input position present
  have inputNe : position.val ≠ input.val := fun same => differentInput (Fin.ext same)
  have outputNe : position.val ≠ output.val := fun same => differentOutput (Fin.ext same)
  simp only [Origin.idle.injEq, inputNe, outputNe, false_or, decide_false]

theorem selected_reordering {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (frame : List (Proc Γ)) (output input : Fin frame.length) (different : input ≠ output)
    (persistent : Bool) (channel datum : Var Γ .nm) (body : Proc (.nm :: Γ))
    (originalOutput : frame[output.val] = out1 (.var channel) (.var datum))
    (originalInput : frame[input.val] = receiver persistent (.var channel) body) :
    Transport
      (.par (.out1 (.idle output.val))
        (.par (receiverMarks persistent (.idle input.val) (ActiveSyntaxMarking.mark (.idle input.val) (lower body)))
          (parallelMarks (rowMarks registry frame) (remainingKeys frame output input))))
      (par (out1 (.var (ambient n .nm channel)) (.var (ambient n .nm datum)))
        (par (receiver persistent (.var (ambient n .nm channel)) (rename (liftRen (ambient n) [.nm]) (lower body)))
          (assembly registry (parallel (remainingFrame frame output input)))))
      (assemblyMarks registry frame) (assembly registry (parallel frame)) := by
  have restored := permutation_transport (rowMarks registry frame) (rowRender registry frame)
    (keys_permutation frame output input different).symm
  change Transport
    (.par (rowMarks registry frame (some output)) (.par (rowMarks registry frame (some input))
      (parallelMarks (rowMarks registry frame) (remainingKeys frame output input))))
    (par (rowRender registry frame (some output)) (par (rowRender registry frame (some input))
      (parallel ((remainingKeys frame output input).map (rowRender registry frame)))))
    (parallelMarks (rowMarks registry frame) (keys frame))
    (parallel ((keys frame).map (rowRender registry frame))) at restored
  rw [(row_output registry frame output channel datum originalOutput).1,
    (row_output registry frame output channel datum originalOutput).2,
    (row_receiver registry frame input persistent channel body originalInput).1,
    (row_receiver registry frame input persistent channel body originalInput).2,
    rows_source_marks, rows_source_process, rows_remaining_process] at restored
  exact restored

theorem lower_inst_variable {Γ : Ctx sig} (body : Proc (.nm :: Γ)) (datum : Var Γ .nm) :
    lower (inst body (.var datum)) = inst (lower body) (.var datum) := by
  have opening (process : Proc (.nm :: Γ)) : inst process (.var datum) = rename (nameRen datum) process := by
    unfold inst
    have environment : extend (Term.var datum) =
        (fun sort name => Term.var (nameRen datum sort name)) := by
      funext sort name
      cases name <;> rfl
    rw [environment, bind_var_eq_rename]
  rw [opening, opening]
  exact (lower_rename _ body).symm

theorem residual_registry {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (live : ∀ owner, Live (registry owner)) (frame : List (Proc Γ)) (output input : Fin frame.length)
    (persistent : Bool) (channel : Var Γ .nm) (body : Proc (.nm :: Γ))
    (originalInput : frame[input.val] = receiver persistent (.var channel) body) :
    StructuralEq
      (if persistent then
        par (rep (inp1 (.var (ambient n .nm channel)) (rename (liftRen (ambient n) [.nm]) (lower body))))
          (assembly registry (parallel (remainingFrame frame output input)))
       else assembly registry (parallel (remainingFrame frame output input)))
      (registryTarget registry (parallel (updatedFrame persistent frame output input))) := by
  cases persistent with
  | false => exact (registry_equation registry _ live).symm
  | true =>
      have server := (row_receiver registry frame input true channel body originalInput).2
      change rename (ambient n) (lower frame[input.val]) =
        rep (inp1 (.var (ambient n .nm channel)) (rename (liftRen (ambient n) [.nm]) (lower body))) at server
      have shape : assembly registry (parallel (updatedFrame true frame output input)) =
          par (parallel ((entries registry).map Actor.render))
            (par (rep (inp1 (.var (ambient n .nm channel)) (rename (liftRen (ambient n) [.nm]) (lower body))))
              (rename (ambient n) (lower (parallel (remainingFrame frame output input))))) := by
        simp only [updatedFrame, if_true, parallel, assembly, lower_par, rename_par, server]
      have exchanged := (StructuralEq.parAssoc
        (rep (inp1 (.var (ambient n .nm channel)) (rename (liftRen (ambient n) [.nm]) (lower body))))
        (parallel ((entries registry).map Actor.render))
        (rename (ambient n) (lower (parallel (remainingFrame frame output input))))).symm.trans
          ((StructuralEq.par (.parComm _ _) (.refl _)).trans (.parAssoc _ _ _))
      rw [← shape] at exchanged
      exact exchanged.trans (registry_equation registry _ live).symm

/-- An arbitrary actual idle firing retains its supplied endpoint. The body
and datum are the original frame prefixes at the chosen literal positions;
the target registry is unchanged, including all still-pending tuple owners. -/
theorem supplied_idle_endpoint {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (live : ∀ owner, Live (registry owner)) (frame : List (Proc Γ))
    (heads : ∀ atom ∈ frame, IdleFrame.Head atom)
    (output input : Fin frame.length) (different : input ≠ output)
    (persistent : Bool) (channel datum : Var Γ .nm) (body : Proc (.nm :: Γ))
    (originalOutput : frame[output.val] = out1 (.var channel) (.var datum))
    (originalInput : frame[input.val] = receiver persistent (.var channel) body)
    {target : Proc (World n Γ)} (actual : Exposure (assembly registry (parallel frame)) target)
    (traced : TracedExposure (assemblyMarks registry frame) actual)
    (unary : inputHeader actual.selected = .input1)
    (chosenInput : traced.continuation.inputOrigin = .idle input.val)
    (chosenOutput : traced.continuation.outputOrigin = .idle output.val) :
    StructuralEq target
      (par (rename (ambient n) (lower (inst body (.var datum))))
        (registryTarget registry (parallel (updatedFrame persistent frame output input)))) := by
  classical
  have transported := selected_reordering registry frame output input different persistent channel datum body
    originalOutput originalInput
  obtain ⟨rebased, sameInput, sameOutput⟩ := rebase_trace traced transported
  have originsDifferent : (Origin.idle (n := n) input.val) ≠ .idle output.val := by
    intro same
    exact different (Fin.ext (Origin.idle.inj same))
  have endpoint := ActiveUnaryPersistentBoundary.receiver_endpoint persistent (ambient n .nm channel)
    (ambient n .nm datum) (rename (liftRen (ambient n) [.nm]) (lower body))
    (assembly registry (parallel (remainingFrame frame output input)))
    (.idle input.val) (.idle output.val) originsDifferent
    (ActiveSyntaxMarking.mark (.idle input.val) (lower body))
    (parallelMarks (rowMarks registry frame) (remainingKeys frame output input))
    ((ActiveSyntaxMarking.mark_fits _ _).rename (liftRen (ambient n) [.nm]))
    (by rw [← rows_remaining_process]; exact parallel_fits _ _ _ (row_fits registry frame))
    (assembly_unused registry _ (remaining_heads frame output input heads))
    (assembly_single registry _ (remaining_heads frame output input heads))
    (remaining_count_zero registry frame output input heads)
    (actual.changeSource transported.erase) rebased unary
    (sameInput.trans chosenInput) (sameOutput.trans chosenOutput)
  have opening := rename_inst (ambient n) (lower body) (.var datum)
  rw [← lower_inst_variable] at opening
  change rename (ambient n) (lower (inst body (.var datum))) =
    inst (rename (liftRen (ambient n) [.nm]) (lower body)) (.var (ambient n .nm datum)) at opening
  rw [← opening] at endpoint
  exact endpoint.trans (.par (.refl _) (residual_registry registry live frame output input persistent channel body originalInput))

theorem selected_source_frame {Γ : Ctx sig} (frame : List (Proc Γ))
    (output input : Fin frame.length) (different : input ≠ output)
    (persistent : Bool) (channel datum : Var Γ .nm) (body : Proc (.nm :: Γ))
    (originalOutput : frame[output.val] = out1 (.var channel) (.var datum))
    (originalInput : frame[input.val] = receiver persistent (.var channel) body) :
    StructuralEq (parallel frame)
      (par (out1 (.var channel) (.var datum))
        (par (receiver persistent (.var channel) body) (parallel (remainingFrame frame output input)))) := by
  have extracted := parallel_perm ((two_position_permutation (List.finRange frame.length) output input
    (List.mem_finRange _) (List.mem_finRange _) different).map (fun position => frame[position.val]))
  rw [indexed_parallel frame (fun process => process)] at extracted
  have unchanged : frame.map (fun process => process) = frame := List.map_id frame
  rw [unchanged] at extracted
  simpa only [List.map_cons, parallel, originalOutput, originalInput, remainingFrame, remainingPositions] using extracted

/-- The same original frame prefixes authorize a real source communication,
independently of every target step, trace, protocol state and typing judgment. -/
theorem source_frame_step {Γ : Ctx sig} (frame : List (Proc Γ))
    (output input : Fin frame.length) (different : input ≠ output)
    (persistent : Bool) (channel datum : Var Γ .nm) (body : Proc (.nm :: Γ))
    (originalOutput : frame[output.val] = out1 (.var channel) (.var datum))
    (originalInput : frame[input.val] = receiver persistent (.var channel) body) :
    StepModulo (parallel frame)
      (par (inst body (.var datum)) (parallel (updatedFrame persistent frame output input))) := by
  have extracted := selected_source_frame frame output input different persistent channel datum body originalOutput originalInput
  cases persistent with
  | false =>
      refine ⟨par (par (out1 (.var channel) (.var datum)) (inp1 (.var channel) body))
        (parallel (remainingFrame frame output input)), _,
        extracted.trans (StructuralEq.parAssoc _ _ _).symm,
        .parL _ (.comm1 _ _ _), .refl _⟩
  | true =>
      let kept := par (rep (inp1 (.var channel) body)) (parallel (remainingFrame frame output input))
      have before : StructuralEq (parallel frame)
          (par (par (out1 (.var channel) (.var datum)) (inp1 (.var channel) body)) kept) :=
        extracted.trans
          ((StructuralEq.par (.refl _) (.par (.repUnfold _) (.refl _))).trans
            ((StructuralEq.par (.refl _) (.parAssoc _ _ _)).trans (StructuralEq.parAssoc _ _ _).symm))
      refine ⟨_, par (inst body (.var datum)) kept, before, .parL _ (.comm1 _ _ _), ?_⟩
      simp only [updatedFrame, if_true, parallel, originalInput, receiver, if_true]
      exact .refl _

/-- Tuple source owners remain unchanged while the selected ordinary source
lookup releases its actual continuation into the active frame. -/
theorem source_registry_step {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (frame : List (Proc Γ)) (output input : Fin frame.length) (different : input ≠ output)
    (persistent : Bool) (channel datum : Var Γ .nm) (body : Proc (.nm :: Γ))
    (originalOutput : frame[output.val] = out1 (.var channel) (.var datum))
    (originalInput : frame[input.val] = receiver persistent (.var channel) body) :
    StepModulo (registrySource registry (parallel frame))
      (par (inst body (.var datum)) (registrySource registry (parallel (updatedFrame persistent frame output input)))) := by
  have step := modulo_add_parallel
    (source_frame_step frame output input different persistent channel datum body originalOutput originalInput)
    (parallel ((List.finRange n).map (fun owner => (registry owner).source)))
  have started := modulo_source_equation (StructuralEq.parComm _ _) step
  apply modulo_target_equation started
  exact (StructuralEq.parAssoc _ _ _).trans (.par (.refl _) (.parComm _ _))

/-- A full idle receipt joins independently authored source execution to
the supplied target endpoint. It retains literal residual occurrences and
the same tuple registry rather than activating a pending source readout. -/
theorem idle_receipt {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (live : ∀ owner, Live (registry owner)) (frame : List (Proc Γ))
    (heads : ∀ atom ∈ frame, IdleFrame.Head atom)
    (output input : Fin frame.length) (different : input ≠ output)
    (persistent : Bool) (channel datum : Var Γ .nm) (body : Proc (.nm :: Γ))
    (originalOutput : frame[output.val] = out1 (.var channel) (.var datum))
    (originalInput : frame[input.val] = receiver persistent (.var channel) body)
    {target : Proc (World n Γ)} (actual : Exposure (assembly registry (parallel frame)) target)
    (traced : TracedExposure (assemblyMarks registry frame) actual)
    (unary : inputHeader actual.selected = .input1)
    (chosenInput : traced.continuation.inputOrigin = .idle input.val)
    (chosenOutput : traced.continuation.outputOrigin = .idle output.val) :
    StepModulo (registrySource registry (parallel frame))
        (par (inst body (.var datum)) (registrySource registry (parallel (updatedFrame persistent frame output input)))) ∧
      StructuralEq target
        (par (rename (ambient n) (lower (inst body (.var datum))))
          (registryTarget registry (parallel (updatedFrame persistent frame output input)))) :=
  ⟨source_registry_step registry frame output input different persistent channel datum body originalOutput originalInput,
    supplied_idle_endpoint registry live frame heads output input different persistent channel datum body
      originalOutput originalInput actual traced unary chosenInput chosenOutput⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeIdleUpdate
