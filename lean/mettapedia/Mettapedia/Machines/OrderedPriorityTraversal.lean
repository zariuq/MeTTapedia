import Mettapedia.Machines.HEProducerCompletion

/-!
# Ordered stateful traversal with incremental success publication

A work item runs by local child transitions, not a completed-evaluation service.
Its returned occurrences pass through the existing preferred-success bank before
the next work item starts in the reached world. Errors remain provisional until
this phase closes. Neither the control nor a saved work item copies the world.

The independent reference is ordered stateful flat-map followed by the existing
success-priority relation. Completed derivations construct finite executions;
arbitrary prefixes do not require termination. Child-internal publication and
the owning language's operand scheduling remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedPriorityTraversal

open OrderedProtocol.Completion
namespace Bank
export HEProducerCompletion (empty ingest collect present Represents)
end Bank

variable {Work Child World Value : Type}

inductive Control (Work Child Value : Type) where
  | pending (work : List Work)
  | running (child : Child) (work : List Work)
  | returning (rows : List Value) (work : List Work)
  | closed
  deriving Repr

def Control.isClosed : Control Work Child Value → Bool
  | .closed => true
  | _ => false

structure State (Work Child World Value : Type) where
  control : Control Work Child Value
  world : World
  bank : HEProducerCompletion.Bank Value
  deriving Repr

def initial (work : List Work) (world : World) : State Work Child World Value :=
  ⟨.pending work, world, HEProducerCompletion.empty⟩

/-- Before closure only irreversible successes are public. Closure releases
fallback errors exactly when no successful occurrence was found. -/
def output (isError : Value → Bool) (state : State Work Child World Value) : List Value :=
  if state.control.isClosed then HEProducerCompletion.present isError true state.bank
  else state.bank.streamedRev.reverse

inductive ControlStep (start : Work → Child)
    (advance : World → Child → World → Child → Prop)
    (finished : Child → Option (List Value)) :
    Control Work Child Value → World → List Value →
      Control Work Child Value → World → Prop where
  | enter {head rest world} :
      ControlStep start advance finished (.pending (head :: rest)) world []
        (.running (start head) rest) world
  | child {before after rest world reached} :
      advance world before reached after →
      ControlStep start advance finished (.running before rest) world []
        (.running after rest) reached
  | returned {child rest rows world} :
      finished child = some rows →
      ControlStep start advance finished (.running child rest) world []
        (.returning rows rest) world
  | accept {row rows rest world} :
      ControlStep start advance finished (.returning (row :: rows) rest) world [row]
        (.returning rows rest) world
  | next {rest world} :
      ControlStep start advance finished (.returning [] rest) world [] (.pending rest) world
  | close {world} :
      ControlStep start advance finished (.pending []) world [] .closed world

inductive Step (start : Work → Child)
    (advance : World → Child → World → Child → Prop)
    (finished : Child → Option (List Value)) (isError : Value → Bool) :
    State Work Child World Value → List Value → State Work Child World Value → Prop where
  | advance {before after world reached rows bank} :
      ControlStep start advance finished before world rows after reached →
      Step start advance finished isError ⟨before,world,bank⟩ rows
        ⟨after,reached,HEProducerCompletion.collect isError true rows bank⟩

inductive Steps (start : Work → Child)
    (advance : World → Child → World → Child → Prop)
    (finished : Child → Option (List Value)) (isError : Value → Bool) :
    State Work Child World Value → List Value → State Work Child World Value → Prop where
  | refl (state) : Steps start advance finished isError state [] state
  | cons {before middle after first rest} :
      Step start advance finished isError before first middle →
      Steps start advance finished isError middle rest after →
      Steps start advance finished isError before (first ++ rest) after

theorem Steps.single {start : Work → Child} {advance finished isError}
    {before after : State Work Child World Value} {rows}
    (edge : Step start advance finished isError before rows after) :
    Steps start advance finished isError before rows after := by
  simpa using Steps.cons edge (.refl after)

theorem Steps.trans {start : Work → Child} {advance finished isError}
    {before middle after : State Work Child World Value} {first rest}
    (earlier : Steps start advance finished isError before first middle)
    (later : Steps start advance finished isError middle rest after) :
    Steps start advance finished isError before (first ++ rest) after := by
  induction earlier with
  | refl => simpa using later
  | cons edge _ ih => simpa only [List.append_assoc] using Steps.cons edge (ih later)

theorem collect_append (isError : Value → Bool) (left right : List Value)
    (bank : HEProducerCompletion.Bank Value) :
    HEProducerCompletion.collect isError true (left ++ right) bank =
      HEProducerCompletion.collect isError true right
        (HEProducerCompletion.collect isError true left bank) := by
  induction left generalizing bank with
  | nil => rfl
  | cons head tail ih => exact ih _

theorem Steps.bank_eq {start : Work → Child} {advance finished isError}
    {before after : State Work Child World Value} {rows}
    (path : Steps start advance finished isError before rows after) :
    after.bank = HEProducerCompletion.collect isError true rows before.bank := by
  induction path with
  | refl => rfl
  | cons edge _ ih => cases edge; simpa only [collect_append] using ih

theorem Steps.represents {start : Work → Child} {advance finished isError}
    {before after : State Work Child World Value} {prior rows}
    (path : Steps start advance finished isError before rows after)
    (represented : HEProducerCompletion.Represents isError true prior before.bank) :
    HEProducerCompletion.Represents isError true (prior ++ rows) after.bank := by
  rw [path.bank_eq]
  exact HEProducerCompletion.collect_represents isError true prior rows before.bank represented

theorem initial_represents (isError : Value → Bool) (work : List Work) (world : World) :
    HEProducerCompletion.Represents isError true []
      (initial (Child := Child) (Value := Value) work world).bank := by
  simp [HEProducerCompletion.Represents, initial, HEProducerCompletion.empty]

/-- No unfinished phase publishes an error, even if errors have already
changed the world while being computed. -/
theorem open_output_nonerror (isError : Value → Bool)
    {state : State Work Child World Value} {rows : List Value}
    (represented : HEProducerCompletion.Represents isError true rows state.bank)
    (openPhase : state.control.isClosed = false) :
    ∀ row ∈ output isError state, isError row = false := by
  intro row member
  have streamed : state.bank.streamedRev.reverse = rows.filter (fun value => !isError value) := by
    simpa using represented.1
  have filtered : row ∈ rows.filter (fun value => !isError value) := by
    simpa [output, openPhase, streamed] using member
  simpa using (List.mem_filter.mp filtered).2

theorem closed_output_priority {start : Work → Child} {advance finished isError}
    {work : List Work} {world : World} {after : State Work Child World Value} {rows}
    (path : Steps start advance finished isError (initial work world) rows after)
    (closed : after.control.isClosed = true) :
    SuccessPriorityRel isError rows (output isError after) := by
  have represented : HEProducerCompletion.Represents isError true rows after.bank := by
    simpa using path.represents (initial_represents isError work world)
  rw [output, closed, if_pos rfl,
    HEProducerCompletion.present_represents isError true rows after.bank represented]
  exact HEProducerCompletion.reference_success_priority isError rows

/-- Independent source reading of suspended control. No machine transition
consults this relation or asks for a recursive completed evaluation. -/
def Residual (meaning : Work → World → List Value → World → Prop)
    (childMeaning : Child → World → List Value → World → Prop) :
    Control Work Child Value → World → List Value → World → Prop
  | .pending work, world, rows, final => OrderedStateFlatMapRel meaning work world rows final
  | .running child work, world, rows, final =>
      ∃ first middle rest, childMeaning child world first middle ∧
        OrderedStateFlatMapRel meaning work middle rest final ∧ rows = first ++ rest
  | .returning ready work, world, rows, final =>
      ∃ rest, OrderedStateFlatMapRel meaning work world rest final ∧ rows = ready ++ rest
  | .closed, world, rows, final => rows = [] ∧ final = world

theorem ControlStep.source_back
    {start : Work → Child} {advance finished}
    {meaning : Work → World → List Value → World → Prop}
    {childMeaning : Child → World → List Value → World → Prop}
    (entry : ∀ work world rows final,
      childMeaning (start work) world rows final → meaning work world rows final)
    (back : ∀ world before reached after rows final,
      advance world before reached after →
      childMeaning after reached rows final → childMeaning before world rows final)
    (terminal : ∀ child world rows, finished child = some rows → childMeaning child world rows world)
    {before after : Control Work Child Value} {world reached emitted rows final}
    (edge : ControlStep start advance finished before world emitted after reached)
    (residual : Residual meaning childMeaning after reached rows final) :
    Residual meaning childMeaning before world (emitted ++ rows) final := by
  cases edge with
  | enter =>
      obtain ⟨first,middle,rest,child,tail,same⟩ := residual
      simpa only [Residual,List.nil_append,same] using OrderedStateFlatMapRel.cons (entry _ _ _ _ child) tail
  | child advanced =>
      obtain ⟨first,middle,rest,child,tail,same⟩ := residual
      exact ⟨first,middle,rest,back _ _ _ _ _ _ advanced child,tail,by simpa using same⟩
  | returned done =>
      obtain ⟨rest,tail,same⟩ := residual
      exact ⟨_,_,rest,terminal _ _ _ done,tail,by simpa using same⟩
  | accept =>
      obtain ⟨rest,tail,same⟩ := residual
      exact ⟨rest,tail,by simp only [List.cons_append,List.nil_append,same]⟩
  | next => exact ⟨rows,residual,by simp⟩
  | close =>
      obtain ⟨rfl,rfl⟩ := residual
      exact .nil _

theorem Steps.source_back
    {start : Work → Child} {advance finished isError}
    {meaning : Work → World → List Value → World → Prop}
    {childMeaning : Child → World → List Value → World → Prop}
    (entry : ∀ work world rows final,
      childMeaning (start work) world rows final → meaning work world rows final)
    (back : ∀ world before reached after rows final,
      advance world before reached after →
      childMeaning after reached rows final → childMeaning before world rows final)
    (terminal : ∀ child world rows, finished child = some rows → childMeaning child world rows world)
    {before after : State Work Child World Value} {emitted rows final}
    (path : Steps start advance finished isError before emitted after)
    (residual : Residual meaning childMeaning after.control after.world rows final) :
    Residual meaning childMeaning before.control before.world (emitted ++ rows) final := by
  induction path generalizing rows with
  | refl => simpa using residual
  | cons edge _ ih =>
      cases edge with
      | advance advanced =>
          simpa only [List.append_assoc] using advanced.source_back entry back terminal (ih residual)

theorem Steps.child_path {start : Work → Child} {advance finished isError}
    {before after : Child} {world reached : World}
    (path : Relation.ReflTransGen
      (fun first last : World × Child => advance first.1 first.2 last.1 last.2)
      (world,before) (reached,after)) (work : List Work) (bank : HEProducerCompletion.Bank Value) :
    Steps start advance finished isError ⟨.running before work,world,bank⟩ []
      ⟨.running after work,reached,bank⟩ := by
  suffices ∀ first last : World × Child,
      Relation.ReflTransGen
        (fun first last : World × Child => advance first.1 first.2 last.1 last.2) first last →
      Steps start advance finished isError ⟨.running first.2 work,first.1,bank⟩ []
        ⟨.running last.2 work,last.1,bank⟩ from this _ _ path
  intro first last path
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl _
  | head advanced _ ih => exact Steps.cons (.advance (.child advanced)) ih

theorem Steps.returned_rows {start : Work → Child} {advance finished isError}
    (rows : List Value) (work : List Work) (world : World) (bank : HEProducerCompletion.Bank Value) :
    Steps start advance finished isError ⟨.returning rows work,world,bank⟩ rows
      ⟨.pending work,world,HEProducerCompletion.collect isError true rows bank⟩ := by
  induction rows generalizing bank with
  | nil => exact .single (.advance .next)
  | cons row rows ih => exact .cons (.advance .accept) (ih _)

/-- Every independently completed ordered source traversal constructs a
streaming execution from local child executions, with the same reached world. -/
theorem source_executes
    {start : Work → Child} {advance finished isError}
    {meaning : Work → World → List Value → World → Prop}
    (childComplete : ∀ work world rows final, meaning work world rows final →
      ∃ child, Relation.ReflTransGen
        (fun first last : World × Child => advance first.1 first.2 last.1 last.2)
        (world,start work) (final,child) ∧ finished child = some rows)
    {work : List Work} {world final : World} {rows}
    (source : OrderedStateFlatMapRel meaning work world rows final)
    (bank : HEProducerCompletion.Bank Value) :
    Steps start advance finished isError ⟨.pending work,world,bank⟩ rows
      ⟨.closed,final,HEProducerCompletion.collect isError true rows bank⟩ := by
  induction source generalizing bank with
  | nil => exact .single (.advance .close)
  | @cons head tail world middle final first rest firstSource _ ih =>
      obtain ⟨child,executed,done⟩ := childComplete _ _ _ _ firstSource
      have earlierPath : Steps start advance finished isError
          ⟨.pending (head :: tail),world,bank⟩ first
          ⟨.pending tail,middle,HEProducerCompletion.collect isError true first bank⟩ := by
        simpa only [List.nil_append] using
          (Steps.single (Step.advance ControlStep.enter)).trans
            ((Steps.child_path executed tail bank).trans
              ((Steps.single (Step.advance (ControlStep.returned done))).trans
                (Steps.returned_rows first tail middle bank)))
      simpa only [List.nil_append,List.append_nil,collect_append] using earlierPath.trans (ih _)

theorem closed_has_no_step {start : Work → Child} {advance finished isError}
    {world : World} {bank : HEProducerCompletion.Bank Value}
    {after : State Work Child World Value} {rows} :
    ¬Step start advance finished isError ⟨.closed,world,bank⟩ rows after := by
  intro edge
  cases edge with
  | advance impossible => cases impossible

/-- A finite scheduler visit requests at most one local child transition.
Failure to supply such a transition leaves the phase pending, not completed. -/
def tick (start : Work → Child) (next : World → Child → Option (World × Child))
    (finished : Child → Option (List Value)) (isError : Value → Bool)
    (state : State Work Child World Value) : Option (State Work Child World Value) :=
  match state.control with
  | .closed => none
  | .pending [] => some {state with control := .closed}
  | .pending (head :: rest) => some {state with control := .running (start head) rest}
  | .running child rest =>
      match finished child with
      | some rows => some {state with control := .returning rows rest}
      | none => (next state.world child).map fun reply =>
          {state with control := .running reply.2 rest, world := reply.1}
  | .returning [] rest => some {state with control := .pending rest}
  | .returning (row :: rows) rest => some {state with
      control := .returning rows rest
      bank := HEProducerCompletion.ingest isError true state.bank row}

theorem tick_sound {start : Work → Child} {advance finished isError}
    {next : World → Child → Option (World × Child)}
    (localSound : ∀ world child reached after,
      next world child = some (reached,after) → advance world child reached after)
    {before after : State Work Child World Value}
    (computed : tick start next finished isError before = some after) :
    ∃ rows, Step start advance finished isError before rows after := by
  rcases before with ⟨control,world,bank⟩
  cases control with
  | closed => simp [tick] at computed
  | pending work =>
      cases work with
      | nil => cases computed; exact ⟨[],.advance .close⟩
      | cons head rest => cases computed; exact ⟨[],.advance .enter⟩
  | returning rows work =>
      cases rows with
      | nil => cases computed; exact ⟨[],.advance .next⟩
      | cons row rest => cases computed; exact ⟨[row],.advance .accept⟩
  | running child work =>
      cases done : finished child with
      | some rows =>
          simp only [tick,done,Option.some.injEq] at computed
          subst after
          exact ⟨[],.advance (.returned done)⟩
      | none =>
          cases replied : next world child with
          | none => simp [tick,done,replied] at computed
          | some reply =>
              simp only [tick,done,replied,Option.map_some,Option.some.injEq] at computed
              subst after
              exact ⟨[],.advance (.child (localSound _ _ _ _ replied))⟩

def core (start : Work → Child) (next : World → Child → Option (World × Child))
    (finished : Child → Option (List Value)) (isError : Value → Bool) :
    MachineCore (List Work × World) where
  State := State Work Child World Value
  load := fun input => initial input.1 input.2
  step := tick start next finished isError

theorem runSlice_sound {start : Work → Child} {advance finished isError}
    {next : World → Child → Option (World × Child)}
    (localSound : ∀ world child reached after,
      next world child = some (reached,after) → advance world child reached after)
    (fuel : Nat) (state : State Work Child World Value) :
    ∃ rows, Steps start advance finished isError state rows
      ((core start next finished isError).runSlice fuel state).1 := by
  induction fuel generalizing state with
  | zero => exact ⟨[],.refl _⟩
  | succ fuel ih =>
      cases computed : tick start next finished isError state with
      | none => exact ⟨[],by simpa [core,MachineCore.runSlice,computed] using Steps.refl state⟩
      | some after =>
          obtain ⟨first,edge⟩ := tick_sound localSound computed
          obtain ⟨later,path⟩ := ih after
          exact ⟨first ++ later,by
            simpa [core,MachineCore.runSlice,computed] using Steps.cons edge path⟩

/-- First demand inspects published output, not a provisional error bank.
The next work item is never entered after this guard succeeds. -/
def firstTick (start : Work → Child) (next : World → Child → Option (World × Child))
    (finished : Child → Option (List Value)) (isError : Value → Bool)
    (state : State Work Child World Value) : Option (State Work Child World Value) :=
  if (output isError state).isEmpty then tick start next finished isError state else none

def firstCore (start : Work → Child) (next : World → Child → Option (World × Child))
    (finished : Child → Option (List Value)) (isError : Value → Bool) :
    MachineCore (List Work × World) where
  State := State Work Child World Value
  load := fun input => initial input.1 input.2
  step := firstTick start next finished isError

theorem firstTick_is_tick {start : Work → Child} {next finished isError}
    {before after : State Work Child World Value}
    (computed : firstTick start next finished isError before = some after) :
    tick start next finished isError before = some after := by
  unfold firstTick at computed
  split at computed
  · exact computed
  · contradiction

theorem firstSlice_sound {start : Work → Child} {advance finished isError}
    {next : World → Child → Option (World × Child)}
    (localSound : ∀ world child reached after,
      next world child = some (reached,after) → advance world child reached after)
    (fuel : Nat) (state : State Work Child World Value) :
    ∃ rows, Steps start advance finished isError state rows
      ((firstCore start next finished isError).runSlice fuel state).1 := by
  induction fuel generalizing state with
  | zero => exact ⟨[],.refl _⟩
  | succ fuel ih =>
      cases computed : firstTick start next finished isError state with
      | none => exact ⟨[],by simpa [firstCore,MachineCore.runSlice,computed] using Steps.refl state⟩
      | some after =>
          obtain ⟨first,edge⟩ := tick_sound localSound (firstTick_is_tick computed)
          obtain ⟨later,path⟩ := ih after
          exact ⟨first ++ later,by
            simpa [firstCore,MachineCore.runSlice,computed] using Steps.cons edge path⟩

theorem first_output_stops {start : Work → Child} {next finished isError}
    (state : State Work Child World Value) (published : (output isError state).isEmpty = false)
    (fuel : Nat) :
    (firstCore start next finished isError).runSlice fuel state = (state,0) := by
  apply MachineCore.runSlice_of_final
  simp [firstCore,firstTick,published]

/-- Scheduler-budget splitting retains actual world, pending children and
error history. It does not reconstruct the initial request. -/
theorem first_split {start : Work → Child} {next finished isError}
    (state : State Work Child World Value) (first later : Nat) :
    (firstCore start next finished isError).runSlice (first + later) state =
      let earlier := (firstCore start next finished isError).runSlice first state
      let resumed := (firstCore start next finished isError).runSlice later earlier.1
      (resumed.1,earlier.2 + resumed.2) :=
  MachineCore.runSlice_add (firstCore start next finished isError) first later state

theorem open_output_safe_prefix (isError : Value → Bool)
    {state : State Work Child World Value} {seen future published : List Value}
    (represented : HEProducerCompletion.Represents isError true seen state.bank)
    (openPhase : state.control.isClosed = false)
    (priority : SuccessPriorityRel isError (seen ++ future) published) :
    ∃ later, published = output isError state ++ later := by
  have streamed : output isError state = seen.filter (fun value => !isError value) := by
    have same := represented.1
    simpa [output,openPhase] using same
  rw [streamed]
  cases priority with
  | allErrors failed =>
      have none : seen.filter (fun value => !isError value) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro value member
        simp [failed value (List.mem_append_left future member)]
      exact ⟨seen ++ future,by simp [none]⟩
  | successes _ => exact ⟨future.filter (fun value => !isError value),List.filter_append _ _⟩

end Mettapedia.Machines.OrderedPriorityTraversal
