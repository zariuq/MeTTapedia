import Mathlib.Data.List.Basic
import Mettapedia.Machines.Cursor.Protocol

/-!
# Ordered primitive protocols with separate terminal continuations

Primitive services may refine local state, retain ordered alternatives, change
the world, fault, or suspend. Sequencing forwards each of these continuations;
it also forwards the enclosing saved failure delimiter. This finite protocol
algebra does not specify any particular primitive service or native lifetime.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedProtocol

abbrev Failure (World Result : Type) := World → Result
abbrev Success (State World Result : Type) :=
  State → Failure World Result → World → Result
abbrev Kernel (State World Fault Pause Result : Type) :=
  State → Success State World Result → Failure World Result →
    Failure World Result → (Fault → World → Result) →
    (Pause → World → Result) → World → Result

variable {State World Fault Pause Result Op : Type}

def done : Kernel State World Fault Pause Result :=
  fun state success pending _ _ _ world => success state pending world

def sequence (first second : Kernel State World Fault Pause Result) :
    Kernel State World Fault Pause Result :=
  fun state success pending saved fault pause world =>
    first state (fun prepared remaining current =>
      second prepared success remaining saved fault pause current)
      pending saved fault pause world

def choice (first second : Kernel State World Fault Pause Result) :
    Kernel State World Fault Pause Result :=
  fun state success pending saved fault pause world =>
    first state success
      (fun current => second state success pending saved fault pause current)
      saved fault pause world

def execute (primitive : Op → Kernel State World Fault Pause Result) :
    List Op → Kernel State World Fault Pause Result
  | [] => done
  | operation :: rest => sequence (primitive operation) (execute primitive rest)

theorem sequence_assoc (first second third : Kernel State World Fault Pause Result) :
    sequence (sequence first second) third = sequence first (sequence second third) := rfl

theorem sequence_done (body : Kernel State World Fault Pause Result) :
    sequence body done = body := by
  funext state success pending saved fault pause world
  simp only [sequence, done]

theorem done_sequence (body : Kernel State World Fault Pause Result) :
    sequence done body = body := rfl

theorem execute_append (primitive : Op → Kernel State World Fault Pause Result)
    (first second : List Op) :
    execute primitive (first ++ second) =
      sequence (execute primitive first) (execute primitive second) := by
  induction first with
  | nil => rfl
  | cons operation first ih =>
      simp only [List.cons_append, execute, ih, sequence_assoc]

def alternatives : List (Kernel State World Fault Pause Result) →
    Kernel State World Fault Pause Result
  | [] => fun _ _ pending _ _ _ world => pending world
  | first :: rest => choice first (alternatives rest)

theorem alternatives_map_congr
    (source target : Op → Kernel State World Fault Pause Result)
    (operations : List Op) (same : ∀ operation ∈ operations, source operation = target operation) :
    alternatives (operations.map source) = alternatives (operations.map target) := by
  congr 1
  exact List.map_congr_left same

namespace Controls

def faulting : Kernel Nat (List String) String Nat (List String) :=
  fun _ _ _ _ fault _ world => fault "bad" (world ++ ["effect"])

def suspended : Kernel Nat (List String) String Nat (List String) :=
  fun _ _ _ _ _ pause world => pause 7 (world ++ ["suspend"])

def later : Kernel Nat (List String) String Nat (List String) :=
  fun state success pending _ _ _ world => success (state + 1) pending (world ++ ["later"])

theorem fault_does_not_run_later :
    sequence faulting later 0 (fun _ _ world => world) id id
      (fun reason world => world ++ [reason]) (fun _ world => world) [] =
      ["effect", "bad"] := rfl

theorem suspension_does_not_become_exhaustion :
    sequence suspended later 0 (fun _ _ world => world)
      (fun world => world ++ ["exhausted"]) id
      (fun _ world => world) (fun _ world => world ++ ["retained"]) [] =
      ["suspend", "retained"] := rfl

end Controls
end Mettapedia.Machines.OrderedProtocol

/-! ## Completed ordered traversal and publication -/

namespace Mettapedia.Machines.OrderedProtocol.Completion

universe uSource uState uResult vSource vState vResult uTarget
variable {source : Type uSource} {state : Type uState} {result : Type uResult}
  {otherSource : Type vSource} {otherState : Type vState} {otherResult : Type vResult}
  {target : Type uTarget}

/-- Relational traversal with one shared state in source order. Each source
element sees the state returned by its predecessor, may emit any finite list
of results, and contributes those results before the tail's results. -/
inductive OrderedStateFlatMapRel
    (step : source → state → List result → state → Prop) :
    List source → state → List result → state → Prop where
  | nil (initial : state) :
      OrderedStateFlatMapRel step [] initial [] initial
  | cons {head : source} {tail : List source}
      {initial middle final : state}
      {headResults tailResults : List result} :
      step head initial headResults middle →
      OrderedStateFlatMapRel step tail middle tailResults final →
      OrderedStateFlatMapRel step (head :: tail) initial
        (headResults ++ tailResults) final

/-- One source transition is the singleton traversal. -/
theorem OrderedStateFlatMapRel.singleton
    {step : source → state → List result → state → Prop}
    {source : source} {initial final : state} {results : List result}
    (transition : step source initial results final) :
    OrderedStateFlatMapRel step [source] initial results final := by
  simpa using OrderedStateFlatMapRel.cons transition
    (OrderedStateFlatMapRel.nil final)

/-- Adjacent traversals compose without reordering their result blocks. -/
theorem OrderedStateFlatMapRel.append
    {step : source → state → List result → state → Prop}
    {left right : List source} {initial middle final : state}
    {leftResults rightResults : List result}
    (leftRun : OrderedStateFlatMapRel step left initial leftResults middle)
    (rightRun : OrderedStateFlatMapRel step right middle rightResults final) :
    OrderedStateFlatMapRel step (left ++ right) initial
      (leftResults ++ rightResults) final := by
  induction leftRun with
  | nil => simpa using rightRun
  | @cons head tail initial firstMiddle middle headResults tailResults
      headStep tailRun inductionHypothesis =>
      simpa [List.append_assoc] using
        OrderedStateFlatMapRel.cons headStep
          (inductionHypothesis rightRun)

/-- A traversal of no sources is forced to emit no results and preserve the
state.  This is the negative boundary that rules out hidden empty-input
effects. -/
theorem OrderedStateFlatMapRel.nil_iff
    {step : source → state → List result → state → Prop}
    {initial final : state} {results : List result} :
    OrderedStateFlatMapRel step [] initial results final ↔
      results = [] ∧ final = initial := by
  constructor
  · intro run
    cases run
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact OrderedStateFlatMapRel.nil _

/-- Cutting a source traversal retains the actually reached middle world.
The suffix is justified by its own completed traversal, not by replaying the
prefix or by starting it in the original world. -/
theorem OrderedStateFlatMapRel.split
    {step : source → state → List result → state → Prop}
    (left right : List source) {initial final : state} {results : List result}
    (run : OrderedStateFlatMapRel step (left ++ right) initial results final) :
    ∃ middle leftResults rightResults, results = leftResults ++ rightResults ∧
      OrderedStateFlatMapRel step left initial leftResults middle ∧
      OrderedStateFlatMapRel step right middle rightResults final := by
  induction left generalizing initial results with
  | nil => exact ⟨initial,[],results,rfl,.nil initial,run⟩
  | cons head tail ih =>
      cases run with
      | cons first remaining =>
          obtain ⟨middle,earlier,later,rfl,before,after⟩ := ih remaining
          exact ⟨middle,_,later,(List.append_assoc _ _ _).symm,.cons first before,after⟩

/-- A completed two-child traversal can be exchanged when the reversed
order reaches the same state and returns the same multiset of results.
The intermediate state and the two result blocks need not be equal. -/
def OrderedStateFlatMapRel.BagSwap
    (step : source → state → List result → state → Prop) (first second : source) : Prop :=
  ∀ {before middle after firstRows secondRows},
    step first before firstRows middle → step second middle secondRows after →
    ∃ reached secondRows' firstRows', step second before secondRows' reached ∧
      step first reached firstRows' after ∧ (secondRows' ++ firstRows').Perm (firstRows ++ secondRows)

/-- Exchanges preserve the whole reached state as well as answer
multiplicity. The equal-item case keeps the original run, not just a
single copy of the item. This is a law about completed traversals;
neither equal costs nor equivalence of ordered prefixes is implied. -/
theorem OrderedStateFlatMapRel.permute
    {step : source → state → List result → state → Prop} {items reordered : List source}
    (schedule : items.Perm reordered)
    (swap : ∀ a ∈ items, ∀ b ∈ items, a ≠ b → BagSwap step a b)
    {before after : state} {rows : List result}
    (run : OrderedStateFlatMapRel step items before rows after) :
    ∃ output, OrderedStateFlatMapRel step reordered before output after ∧ output.Perm rows := by
  induction schedule generalizing before rows with
  | nil => exact ⟨_,run,.refl _⟩
  | cons item schedule ih =>
    cases run with
    | cons first rest =>
      obtain ⟨_, next, same⟩ := ih
        (fun a ha b hb ne => swap a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) ne) rest
      exact ⟨_, .cons first next, same.append_left _⟩
  | swap second first tail =>
    by_cases equal : first = second
    · subst second
      exact ⟨_,run,.refl _⟩
    · cases run with
      | cons earlier rest =>
        cases rest with
        | cons later suffix =>
          obtain ⟨_,_,_, reversedFirst, reversedSecond, same⟩ :=
            swap first (by simp) second (by simp) equal earlier later
          exact ⟨_, .cons reversedFirst (.cons reversedSecond suffix),
            by simpa only [List.append_assoc] using same.append_right _⟩
  | trans first _ ihFirst ihSecond =>
    obtain ⟨_, middle, earlier⟩ := ihFirst swap run
    obtain ⟨_, output, later⟩ := ihSecond
      (fun a ha b hb ne => swap a (first.mem_iff.mpr ha) b (first.mem_iff.mpr hb) ne) middle
    exact ⟨_,output,later.trans earlier⟩

/-- Reordering becomes an equivalence for the completed-bag observer.
Transporting the exchange licence along the permutation handles the converse. -/
theorem OrderedStateFlatMapRel.permute_bag_iff
    {step : source → state → List result → state → Prop} {items reordered : List source}
    (schedule : items.Perm reordered)
    (swap : ∀ a ∈ items, ∀ b ∈ items, a ≠ b → BagSwap step a b)
    (before after : state) (rows : List result) :
    (∃ output, OrderedStateFlatMapRel step items before output after ∧ output.Perm rows) ↔
      ∃ output, OrderedStateFlatMapRel step reordered before output after ∧ output.Perm rows := by
  constructor
  · rintro ⟨_,run,same⟩
    obtain ⟨_,replayed,bag⟩ := run.permute schedule swap
    exact ⟨_,replayed,bag.trans same⟩
  · rintro ⟨_,run,same⟩
    obtain ⟨_,replayed,bag⟩ := run.permute schedule.symm
      (fun a ha b hb ne => swap a (schedule.mem_iff.mpr ha) b (schedule.mem_iff.mpr hb) ne)
    exact ⟨_,replayed,bag.trans same⟩

/-- Local child refinement lifts to the whole ordered traversal. Sources
and results may change representation; their occurrences are still mapped
one for one. Only a relation between worlds is required. -/
theorem OrderedStateFlatMapRel.simulate
    {step : source → state → List result → state → Prop}
    {otherStep : otherSource → otherState → List otherResult → otherState → Prop}
    (sourceMap : source → otherSource) (resultMap : result → otherResult)
    (worlds : state → otherState → Prop)
    (child : ∀ item before rows after, step item before rows after →
      ∀ otherBefore, worlds before otherBefore →
        ∃ otherAfter, otherStep (sourceMap item) otherBefore (rows.map resultMap) otherAfter ∧
          worlds after otherAfter)
    {sources : List source} {initial final : state} {results : List result}
    (run : OrderedStateFlatMapRel step sources initial results final)
    {otherInitial : otherState} (loaded : worlds initial otherInitial) :
    ∃ otherFinal,
      OrderedStateFlatMapRel otherStep (sources.map sourceMap) otherInitial
        (results.map resultMap) otherFinal ∧ worlds final otherFinal := by
  induction run generalizing otherInitial with
  | nil => exact ⟨otherInitial,.nil otherInitial,loaded⟩
  | @cons head tail initial middle final headResults tailResults first _ ih =>
      obtain ⟨otherMiddle,firstRun,middleRelated⟩ := child _ _ _ _ first _ loaded
      obtain ⟨otherFinal,rest,finalRelated⟩ := ih middleRelated
      exact ⟨otherFinal,by simpa only [List.map_cons,List.map_append] using
        OrderedStateFlatMapRel.cons firstRun rest,finalRelated⟩

/-! ## Publication at a completed search boundary -/

/-- Success priority selects from one completed finite phase. Every input
occurrence is classified; equal occurrences are retained separately. This
relation does not itself certify that the supplied list exhausts a recursive
source computation. -/
inductive SuccessPriorityRel (isError : result → Bool) :
    List result → List result → Prop where
  | allErrors {raw : List result} :
      (∀ item ∈ raw, isError item = true) → SuccessPriorityRel isError raw raw
  | successes {raw : List result} :
      (∃ item ∈ raw, isError item = false) →
      SuccessPriorityRel isError raw (raw.filter fun item => !isError item)

theorem SuccessPriorityRel.functional
    {isError : result → Bool} {raw first second : List result}
    (left : SuccessPriorityRel isError raw first)
    (right : SuccessPriorityRel isError raw second) : first = second := by
  cases left with
  | allErrors failed =>
      cases right with
      | allErrors => rfl
      | successes succeeds =>
          obtain ⟨item, member, successful⟩ := succeeds
          simp [failed item member] at successful
  | successes succeeds =>
      cases right with
      | successes => rfl
      | allErrors failed =>
          obtain ⟨item, member, successful⟩ := succeeds
          simp [failed item member] at successful

/-- A completed priority phase has exactly its raw support, subject to the
phase-wide error condition. This law cannot turn a prefix into completion. -/
theorem SuccessPriorityRel.mem_iff
    {isError : result → Bool} {raw published : List result}
    (closed : SuccessPriorityRel isError raw published) (item : result) :
    item ∈ published ↔ item ∈ raw ∧
      (isError item = true → ∀ other ∈ raw, isError other = true) := by
  cases closed with
  | allErrors failed =>
      exact ⟨fun member => ⟨member, fun _ => failed⟩, fun present => present.1⟩
  | successes succeeds =>
      obtain ⟨good, member, successful⟩ := succeeds
      constructor
      · intro present
        obtain ⟨present, kept⟩ := List.mem_filter.mp present
        refine ⟨present, ?_⟩
        intro error
        simp [error] at kept
      · rintro ⟨present, condition⟩
        apply List.mem_filter.mpr
        refine ⟨present, ?_⟩
        cases error : isError item with
        | false => rfl
        | true =>
            have impossible := condition error good member
            rw [successful] at impossible
            cases impossible

/-- Changing representation transports every occurrence in the same order.
The map may identify values; it does not identify their occurrences. -/
theorem SuccessPriorityRel.map
    {isError : result → Bool} {otherError : target → Bool}
    {raw published : List result} (closed : SuccessPriorityRel isError raw published)
    (represent : result → target)
    (classification : ∀ item, otherError (represent item) = isError item) :
    SuccessPriorityRel otherError (raw.map represent) (published.map represent) := by
  cases closed with
  | allErrors failed =>
      apply SuccessPriorityRel.allErrors
      intro item member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      rw [classification]
      exact failed original present
  | successes succeeds =>
      have same : ∀ rows : List result,
          (rows.filter fun item => !isError item).map represent =
            (rows.map represent).filter fun item => !otherError item := by
        intro rows
        induction rows with
        | nil => rfl
        | cons head tail ih =>
            cases error : isError head <;>
              simp [classification, error, ih]
      rw [same]
      obtain ⟨item, member, successful⟩ := succeeds
      exact .successes ⟨represent item, List.mem_map.mpr ⟨item, member, rfl⟩,
        (classification item).trans successful⟩

/-- Reordering one already completed batch reorders its publication by the
same multiset law. This does not reorder effectful source execution. -/
theorem SuccessPriorityRel.perm
    {isError : result → Bool} {raw published otherRaw : List result}
    (closed : SuccessPriorityRel isError raw published) (same : raw.Perm otherRaw) :
    ∃ otherPublished, SuccessPriorityRel isError otherRaw otherPublished ∧
      published.Perm otherPublished := by
  cases closed with
  | allErrors failed =>
      exact ⟨otherRaw,.allErrors (fun item member => failed item (same.mem_iff.mpr member)),same⟩
  | successes succeeds =>
      obtain ⟨item,member,successful⟩ := succeeds
      exact ⟨_,.successes ⟨item,same.mem_iff.mp member,successful⟩,
        same.filter (fun item => !isError item)⟩

/-- Every source item completes before the phase publishes. Result filtering
does not roll back the state already produced by any alternative. -/
inductive PublishedTraversalRel
    (step : source → state → List result → state → Prop) (isError : result → Bool) :
    List source → state → List result → state → Prop where
  | completed {sources : List source} {initial final : state} {raw published : List result} :
      OrderedStateFlatMapRel step sources initial raw final →
      SuccessPriorityRel isError raw published →
      PublishedTraversalRel step isError sources initial published final

theorem PublishedTraversalRel.decompose
    {step : source → state → List result → state → Prop} {isError : result → Bool}
    {sources : List source} {initial final : state} {published : List result}
    (closed : PublishedTraversalRel step isError sources initial published final) :
    ∃ raw, OrderedStateFlatMapRel step sources initial raw final ∧
      SuccessPriorityRel isError raw published := by
  cases closed with
  | completed traversed priority => exact ⟨_, traversed, priority⟩

/-- Changing world/result representations preserves completed publication
when every child refines and the result observer preserves error class.
This does not assume a simulation of the entire evaluator. -/
theorem PublishedTraversalRel.simulate
    {step : source → state → List result → state → Prop}
    {otherStep : otherSource → otherState → List otherResult → otherState → Prop}
    {isError : result → Bool} {otherError : otherResult → Bool}
    (sourceMap : source → otherSource) (resultMap : result → otherResult)
    (worlds : state → otherState → Prop)
    (classification : ∀ item, otherError (resultMap item) = isError item)
    (child : ∀ item before rows after, step item before rows after →
      ∀ otherBefore, worlds before otherBefore →
        ∃ otherAfter, otherStep (sourceMap item) otherBefore (rows.map resultMap) otherAfter ∧
          worlds after otherAfter)
    {sources : List source} {initial final : state} {published : List result}
    (run : PublishedTraversalRel step isError sources initial published final)
    {otherInitial : otherState} (loaded : worlds initial otherInitial) :
    ∃ otherFinal,
      PublishedTraversalRel otherStep otherError (sources.map sourceMap) otherInitial
        (published.map resultMap) otherFinal ∧ worlds final otherFinal := by
  obtain ⟨raw,traversed,priority⟩ := run.decompose
  obtain ⟨otherFinal,otherTraversal,related⟩ :=
    traversed.simulate sourceMap resultMap worlds child loaded
  exact ⟨otherFinal,.completed otherTraversal (priority.map resultMap classification),related⟩

end Mettapedia.Machines.OrderedProtocol.Completion

/-! ## Retaining ordered continuations across bounded cursor visits -/

namespace Mettapedia.Machines.OrderedProtocol.CursorAdapter

open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.Machines.Cursor

variable {Op : Type} {Reply : Op → Type} {Answer Fault World Result : Type}

abbrev Control (Op : Type) (Reply : Op → Type) (Answer Fault : Type) :=
  Except Fault (Prog Op Reply Answer)

abbrev State (Op : Type) (Reply : Op → Type) (Answer Fault : Type) :=
  Nat × Control Op Reply Answer Fault

/-- A pause owns the reached provider world, paid account, actual residual
and enclosing handlers. In particular, sequencing's success continuation and
its saved failure delimiter survive a pause. This is a live closure, not a
serializable checkpoint or permission to replace its captured world. -/
structure Suspension (Op : Type) (Reply : Op → Type) (Answer Fault World Result : Type) where
  state : State Op Reply Answer Fault
  world : World
  success : Success (State Op Reply Answer Fault) World Result
  pending : Failure World Result
  saved : Failure World Result
  fault : (Nat × Fault) → World → Result

variable (step : World → (operation : Op) → World × Except Fault (Reply operation))
  (cost : World → Op → Nat)

/-- Interpret the existing primitive program's observation as an ordered
protocol callback. A fault retains its paid account; a scheduling pause is
neither failure nor successful return. -/
def respond
    (value : Nat × ((Except Fault Answer ⊕ Control Op Reply Answer Fault) × World))
    (success : Success (State Op Reply Answer Fault) World Result)
    (pending saved : Failure World Result)
    (fault : (Nat × Fault) → World → Result)
    (pause : Suspension Op Reply Answer Fault World Result → World → Result) : Result :=
  match value.2 with
  | (.inl (.ok answer), world) => success (value.1, .ok (.ret answer)) pending world
  | (.inl (.error reason), world) => fault (value.1, reason) world
  | (.inr control, world) =>
      pause ⟨(value.1, control), world, success, pending, saved, fault⟩ world

def deliver
    (value : Nat × Outcome (PrimitiveProgram.provider step)
      (PrimitiveProgram.client Op Reply Answer Fault) PUnit.unit)
    (success : Success (State Op Reply Answer Fault) World Result)
    (pending saved : Failure World Result)
    (fault : (Nat × Fault) → World → Result)
    (pause : Suspension Op Reply Answer Fault World Result → World → Result) : Result :=
  respond (value.1, PrimitiveProgram.readOutcome step value.2)
    success pending saved fault pause

/-- One bounded visit of the actual indexed cursor. The saved failure
delimiter remains separate from the current alternative's failure. -/
def execute (fuel : Nat) :
    Kernel (State Op Reply Answer Fault) World (Nat × Fault)
      (Suspension Op Reply Answer Fault World Result) Result :=
  fun state success pending saved fault pause world =>
    deliver step
      (Cursor.resume (PrimitiveProgram.provider step)
        (PrimitiveProgram.client Op Reply Answer Fault) (PrimitiveProgram.charge cost step)
        fuel (state.1, .paused ⟨PUnit.unit, state.2, world⟩))
      success pending saved fault pause

/-- Resume the retained closure, including the continuation installed by an
enclosing sequence or choice. Only the next scheduling allowance changes. -/
def resume (fuel : Nat) (suspended : Suspension Op Reply Answer Fault World Result)
    (pause : Suspension Op Reply Answer Fault World Result → World → Result) : Result :=
  execute step cost fuel suspended.state suspended.success suspended.pending
    suspended.saved suspended.fault pause suspended.world

/-- Compare with the independent direct interpreter of the original primitive
program, retaining the complete reached world, control and accumulated cost. -/
theorem execute_is_direct (fuel : Nat) (state : State Op Reply Answer Fault)
    (success : Success (State Op Reply Answer Fault) World Result)
    (pending saved : Failure World Result)
    (fault : (Nat × Fault) → World → Result)
    (pause : Suspension Op Reply Answer Fault World Result → World → Result) (world : World) :
    execute step cost fuel state success pending saved fault pause world =
      let expected := PrimitiveProgram.direct step cost fuel state.2 world
      respond (state.1 + expected.1, expected.2) success pending saved fault pause := by
  exact congrArg
    (fun value => respond (state.1 + value.1, value.2) success pending saved fault pause)
    (PrimitiveProgram.advance_is_direct step cost fuel state.2 world)

theorem deliver_resume (later : Nat)
    (value : Nat × Outcome (PrimitiveProgram.provider step)
      (PrimitiveProgram.client Op Reply Answer Fault) PUnit.unit)
    (success : Success (State Op Reply Answer Fault) World Result)
    (pending saved : Failure World Result)
    (fault : (Nat × Fault) → World → Result)
    (pause : Suspension Op Reply Answer Fault World Result → World → Result) :
    deliver step value success pending saved fault
        (fun suspended _ => resume step cost later suspended pause) =
      deliver step
        (Cursor.resume (PrimitiveProgram.provider step)
          (PrimitiveProgram.client Op Reply Answer Fault) (PrimitiveProgram.charge cost step)
          later value) success pending saved fault pause := by
  rcases value with ⟨paid, outcome⟩
  cases outcome with
  | paused packet => rcases packet with ⟨index, control, world⟩; cases index; rfl
  | done result =>
      rcases result with ⟨index, answer, world⟩
      cases index
      cases answer <;> rfl

/-- Splitting an allowance resumes the actual residual and its original
handlers. It does not rerun the prefix or drop an enclosing sequence. -/
theorem execute_split (earlier later : Nat) (state : State Op Reply Answer Fault)
    (success : Success (State Op Reply Answer Fault) World Result)
    (pending saved : Failure World Result)
    (fault : (Nat × Fault) → World → Result)
    (pause : Suspension Op Reply Answer Fault World Result → World → Result) (world : World) :
    execute step cost earlier state success pending saved fault
        (fun suspended _ => resume step cost later suspended pause) world =
      execute step cost (earlier + later) state success pending saved fault pause world := by
  unfold execute
  rw [deliver_resume]
  rw [← Cursor.resume_add]

theorem execute_zero (state : State Op Reply Answer Fault)
    (success : Success (State Op Reply Answer Fault) World Result)
    (pending saved : Failure World Result)
    (fault : (Nat × Fault) → World → Result)
    (pause : Suspension Op Reply Answer Fault World Result → World → Result) (world : World) :
    execute step cost 0 state success pending saved fault pause world =
      pause ⟨state, world, success, pending, saved, fault⟩ world := by
  cases state
  rfl

/-- A retained pause carries the success continuation through which an
enclosing sequence will run its suffix, together with both failure handlers. -/
theorem resume_sequence (fuel : Nat) (state : State Op Reply Answer Fault)
    (next : Kernel (State Op Reply Answer Fault) World (Nat × Fault)
      (Suspension Op Reply Answer Fault World Result) Result)
    (success : Success (State Op Reply Answer Fault) World Result)
    (pending saved : Failure World Result)
    (fault : (Nat × Fault) → World → Result)
    (pause : Suspension Op Reply Answer Fault World Result → World → Result) (world : World) :
    resume step cost fuel
        ⟨state, world,
          (fun prepared remaining current => next prepared success remaining saved fault pause current),
          pending, saved, fault⟩ pause =
      sequence (execute step cost fuel) next state success pending saved fault pause world := rfl

namespace Controls

def action (world : List String) (operation : Nat) : List String × Except String Nat :=
  if operation = 0 then (world ++ ["bad"], .error "fault")
  else (world ++ ["step"], .ok operation)

def program (second : Nat) : Prog Nat (fun _ => Nat) Nat :=
  .call 1 fun first => .call second fun last => .ret (first + last)

def suffix : Kernel (State Nat (fun _ => Nat) Nat String) (List String) (Nat × String)
    (Suspension Nat (fun _ => Nat) Nat String (List String) (Nat × List String))
    (Nat × List String) :=
  fun state success pending _ _ _ world => success state pending (world ++ ["suffix"])

def success : Success (State Nat (fun _ => Nat) Nat String) (List String) (Nat × List String) :=
  fun state _ world => (state.1, world)

def failure : Failure (List String) (Nat × List String) := fun world => (99, world ++ ["failure"])

def fault (reason : Nat × String) (world : List String) : Nat × List String :=
  (reason.1, world ++ [reason.2])

def paused (suspended : Suspension Nat (fun _ => Nat) Nat String (List String) (Nat × List String))
    (_ : List String) : Nat × List String := (suspended.state.1, suspended.world ++ ["paused"])

theorem actual_sequence_survives_pause :
    sequence (execute action (fun _ _ => 1) 1) suffix (7, .ok (program 2))
      success failure failure fault
      (fun suspended _ => resume action (fun _ _ => 1) 3 suspended paused) [] =
      (9, ["step", "step", "suffix"]) := rfl

theorem fault_after_resume_does_not_run_suffix :
    sequence (execute action (fun _ _ => 1) 1) suffix (7, .ok (program 0))
      success failure failure fault
      (fun suspended _ => resume action (fun _ _ => 1) 3 suspended paused) [] =
      (9, ["step", "bad", "fault"]) := rfl

theorem resumed_suffix_keeps_the_original_saved_failure :
    sequence (execute action (fun _ _ => 1) 1)
      (fun _ _ _ saved _ _ world => saved world) (7, .ok (program 2)) success
      (fun world => (11, world ++ ["pending"]))
      (fun world => (22, world ++ ["saved"])) fault
      (fun suspended _ => resume action (fun _ _ => 1) 3 suspended paused) [] =
      (22, ["step", "step", "saved"]) := rfl

theorem zero_cut_retains_world_paid_account_and_delimiters :
    execute action (fun _ _ => 1) 0 (7, .ok (program 2)) success
      (fun world => (11, world ++ ["pending"]))
      (fun world => (22, world ++ ["saved"])) fault
      (fun suspended _ =>
        (suspended.state.1,
          (suspended.pending suspended.world).2 ++ (suspended.saved suspended.world).2))
      ["before"] = (7, ["before", "pending", "before", "saved"]) := rfl

end Controls
end Mettapedia.Machines.OrderedProtocol.CursorAdapter
