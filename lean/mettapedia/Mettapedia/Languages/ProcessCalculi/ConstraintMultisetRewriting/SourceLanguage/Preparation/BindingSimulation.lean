import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.BindingPlans
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Continuations

/-!
# Simulation of a compiled binding region

All the code in a region prepares one private constraint extension.
Its solvability suffices for the liveness of every proper prefix.
A schedule can run the region as a unit when it retains the selected
alternative throughout. Other alternatives, frames, pending cells and
space contents are preserved, including at a handback boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.BindingSimulation

open Mettapedia.OSLF.Binding hiding instantiate
open Mettapedia.OSLF.Binding.ContextualFamily
open BindingPlans
open Evaluation (Evaluator Reply)
open Machine (State Transition Scheduler)

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
  {Storage Ty : Type} {D : Discipline S Γ star}

/-- The ordered context of a selected alternative. -/
structure Surrounding (κ : Keys S) (Γ : Ctx S) (star : S.Srt) (Ty : Type) where
  before : List (Branch κ Γ star Ty)
  after : List (Branch κ Γ star Ty)

def Surrounding.state (around : Surrounding κ Γ star Ty) (world : ExecutionWorld Storage)
    (branch : Branch κ Γ star Ty) : State κ Γ star Ty Storage :=
  ⟨world, around.before ++ branch :: around.after⟩

def Surrounding.position (around : Surrounding κ Γ star Ty) (world : ExecutionWorld Storage)
    (branch : Branch κ Γ star Ty) : Fin (around.state world branch).agenda.length :=
  ⟨around.before.length, by simp [state]⟩

private theorem Surrounding.selected (around : Surrounding κ Γ star Ty)
    (world : ExecutionWorld Storage) (branch : Branch κ Γ star Ty) :
    (around.state world branch).agenda.get (around.position world branch) = branch := by
  simp [state, position, List.get_eq_getElem, List.getElem_append_right (Nat.le_refl _)]

private theorem Surrounding.replace (around : Surrounding κ Γ star Ty)
    (world : ExecutionWorld Storage) (branch next : Branch κ Γ star Ty) :
    OrderedAgenda.replace (around.state world branch).agenda (around.position world branch) [next] =
      (around.state world next).agenda := by
  simp only [state, position, OrderedAgenda.replace, List.take_left]
  rw [← List.drop_drop, List.drop_left]
  simp [List.append_assoc]

variable (machine : Evaluator κ D Storage) (strategy : Strategy κ Γ star D.Ty)

def Keeps (schedule : Scheduler machine strategy) (around : Surrounding κ Γ star D.Ty) : Prop :=
  ∀ world branch, (schedule (around.state world branch)).map (fun chosen => chosen.val.val) =
    some around.before.length

variable {machine strategy} (schedule : Scheduler machine strategy)

structure Reaches (moves : Nat) (before after : State κ Γ star D.Ty Storage) : Prop where
  state : (Machine.run machine strategy schedule moves before).1 = after
  debit : (Machine.run machine strategy schedule moves before).2.length = moves

theorem Reaches.append {first later : Nat} {start middle finish : State κ Γ star D.Ty Storage}
    (one : Reaches schedule first start middle) (two : Reaches schedule later middle finish) :
    Reaches schedule (first + later) start finish := by
  constructor
  · rw [Machine.run_add]
    simpa only [one.state] using two.state
  · rw [Machine.run_add]
    simp only [one.state, List.length_append, one.debit, two.debit]

theorem Reaches.charged {moves : Nat} {start finish : State κ Γ star D.Ty Storage}
    (execution : Reaches schedule moves start finish) :
    ∃ work, ChargedRun D machine.program machine.supply strategy
      (start.source machine.spaces) work (finish.source machine.spaces) ∧
      work.length = moves ∧ moves ≤ units work := by
  let work := (Machine.run machine strategy schedule moves start).2
  have trace := Machine.run_charged machine strategy schedule moves start
  change ChargedRun D machine.program machine.supply strategy (start.source machine.spaces) work
    ((Machine.run machine strategy schedule moves start).1.source machine.spaces) at trace
  rw [execution.state] at trace
  refine ⟨work, trace, execution.debit, ?_⟩
  calc
    moves = work.length := execution.debit.symm
    _ ≤ units work := reductions_bounded_by_work work

private theorem selectedAdvance (before : State κ Γ star D.Ty Storage)
    (position : Fin before.agenda.length) {branch : Branch κ Γ star D.Ty}
    (selected : before.agenda.get position = branch) (live : Solvable branch.store)
    {reply : Reply machine before.world branch}
    (reduces : Evaluation.reduce machine before.world branch = some reply) :
    Machine.advanceAt machine strategy before position =
      some ⟨⟨reply.world', OrderedAgenda.replace before.agenda position reply.branches⟩,
        charge strategy (before.source machine.spaces) branch reply.branches⟩ := by
  subst branch
  simp only [Machine.advanceAt, (machine.solver.satisfiable_iff _).mpr live, if_true, reduces]
  rfl

variable {schedule} {around : Surrounding κ Γ star D.Ty}

private theorem oneMove (kept : Keeps machine strategy schedule around)
    (world : ExecutionWorld Storage) (branch next : Branch κ Γ star D.Ty)
    (live : Solvable branch.store) (reply : Reply machine world branch)
    (reduces : Evaluation.reduce machine world branch = some reply) (one : reply.branches = [next]) :
    Reaches schedule 1 (around.state world branch) (around.state reply.world' next) := by
  let state := around.state world branch
  let position := around.position world branch
  have chosen := kept world branch
  cases scheduling : schedule state with
  | none =>
    change (schedule state).map _ = _ at chosen
    rw [scheduling] at chosen
    cases chosen
  | some pick =>
    have eqPosition : pick.val = position := by
      apply Fin.ext
      change (schedule state).map _ = _ at chosen
      change pick.val.val = around.before.length
      simpa only [scheduling, Option.map_some, Option.some.injEq] using chosen
    have advances : Machine.advance machine strategy schedule state =
        some ⟨around.state reply.world' next,
          charge strategy (state.source machine.spaces) branch [next]⟩ := by
      unfold Machine.advance
      rw [scheduling]
      change Machine.advanceAt machine strategy state pick.val = _
      rw [eqPosition]
      have actual := selectedAdvance (strategy := strategy) state position
        (around.selected world branch) live reduces
      rw [actual, one]
      congr 2
      exact congrArg (State.mk reply.world') (around.replace world branch next)
    constructor <;> simp [Machine.run, advances, state]

private theorem solvable_prefix {knowledge extra : List (Constraint κ Γ star)}
    (full : Solvable (knowledge ++ extra)) : Solvable knowledge := by
  obtain ⟨X, target, solution, models⟩ := full
  exact ⟨X, target, solution, fun equation member => models equation (List.mem_append_left _ member)⟩

def laterWorld (world : ExecutionWorld Storage) (opens : Nat) : ExecutionWorld Storage :=
  {world with scope := world.scope + opens}

@[simp] private theorem laterWorld_zero (world : ExecutionWorld Storage) :
    laterWorld world 0 = world := by cases world; rfl

private theorem laterWorld_bind (world : ExecutionWorld Storage) (producer body : Nat) :
    laterWorld (laterWorld world producer).fresh body = laterWorld world (producer + 1 + body) := by
  simp only [laterWorld, ExecutionWorld.fresh]
  congr 1
  omega

/-- Compilation fuses the finite lexical control while retaining its exact
source cost in reductions. Only the region's admitted binding facts
are added, in source order, and there is no source dispatch in the plan.
The schedule assumption also accounts for older and younger alternatives. -/
theorem lower_refines [DecidableEq κ.Key] {code : Comp κ Γ star D.Ty} {ending : ExitKind}
    (shape : Fragment κ Γ star D.Ty ending code) (kept : Keeps machine strategy schedule around)
    (context : Context κ) (origin offset : Nat) (entry : List Nat) (table : ScopeTable)
    (world : ExecutionWorld Storage) (knowledge : List (Constraint κ Γ star))
    (frames : List (Frame κ Γ star D.Ty)) (cells : List (Data κ Γ star × Comp κ Γ star D.Ty))
    (older : context.earlier offset) (clock : world.scope = origin + offset)
    (live : Solvable (knowledge ++ ((lower shape context offset).execute origin entry offset table).1.2)) :
    let result := (lower shape context offset).execute origin entry offset table
    Reaches schedule shape.moves
      (around.state world ⟨knowledge, .eval (code.inst (relabel κ (scopeNames (context.scopes table) entry))),
        frames, cells⟩)
      (around.state (laterWorld world shape.bindings)
        ⟨knowledge ++ result.1.2, ExitKind.focus result.2 ending, frames, cells⟩) := by
  induction shape generalizing context offset table world knowledge frames with
  | hold datum =>
    simp only [lower, Plan.execute, executeBindings, Operand.read_compile, Fragment.moves,
      Fragment.bindings, laterWorld_zero, List.append_nil] at live ⊢
    let value := instantiate (relabel κ (scopeNames (context.scopes table) entry)) datum
    exact oneMove kept world ⟨knowledge, .eval (.ret value), frames, cells⟩
      ⟨knowledge, .value value, frames, cells⟩ live
      ⟨world, [⟨knowledge, .value value, frames, cells⟩], .ret _ _ _ _ _⟩ rfl rfl
  | call datum =>
    simp only [lower, Plan.execute, executeBindings, Operand.read_compile, Fragment.moves,
      Fragment.bindings, laterWorld_zero, List.append_nil, ExitKind.focus]
    exact ⟨rfl, rfl⟩
  | @binding bound body ending site pattern producer continuation ihProducer ihBody =>
    let assignment := relabel κ (scopeNames (context.scopes table) entry)
    let producerResult := (lower producer context offset).execute origin entry offset table
    let atBind := offset + producer.bindings
    let inner : Context κ := (site, atBind) :: context
    let middle := laterWorld world producer.bindings
    let extended := Function.update producerResult.1.1 atBind
      ((origin + atBind) :: context.scopes producerResult.1.1 site)
    let equation := ((Operand.compile inner pattern).read extended entry, producerResult.2)
    let continuationResult :=
      (lower continuation inner (atBind + 1)).execute origin entry (atBind + 1) extended
    rw [execute_lower_binding] at live
    have liveProducer : Solvable (knowledge ++ producerResult.1.2) := by
      apply solvable_prefix (extra := equation :: continuationResult.1.2)
      simpa only [List.append_assoc] using live
    have liveContinuation :
        Solvable ((knowledge ++ producerResult.1.2 ++ [equation]) ++ continuationResult.1.2) := by
      simpa only [List.append_assoc, List.singleton_append] using live
    let frame : Frame κ Γ star D.Ty := .bindTo site (instantiate assignment pattern) (body.inst assignment)
    have begin : Reaches schedule 1
        (around.state world ⟨knowledge, .eval ((Comp.let_ site pattern bound body).inst assignment), frames, cells⟩)
        (around.state world ⟨knowledge, .eval (bound.inst assignment), frame :: frames, cells⟩) :=
      oneMove kept world _ _ (solvable_prefix liveProducer)
        ⟨world, [_], .letStart _ _ _ _ _ _ _ _⟩ rfl rfl
    have first := ihProducer context offset table world knowledge (frame :: frames) older clock liveProducer
    have middleClock : middle.scope = origin + atBind := by
      change world.scope + producer.bindings = _
      rw [clock, Nat.add_assoc]
    have oldScopes : context.scopes producerResult.1.1 = context.scopes table :=
      Context.scopes_after_bindings context origin entry (lower producer context offset).code offset table older
    have newScopes : Context.scopes inner extended =
        Function.update (context.scopes table) site (middle.scope :: context.scopes table site) := by
      calc
        _ = Function.update (context.scopes producerResult.1.1) site
            ((origin + atBind) :: context.scopes producerResult.1.1 site) :=
          Context.scopes_push context site atBind origin producerResult.1.1
            (Context.earlier_of_le older (by dsimp [atBind]; omega))
        _ = _ := by rw [middleClock, oldScopes]
    have openedPattern : equation.1 = instantiate (openAt κ site middle.scope) (instantiate assignment pattern) := by
      change (Operand.compile inner pattern).read extended entry = _
      rw [Operand.read_compile, instantiate_open]
      change instantiate (relabel κ (scopeNames (Context.scopes inner extended) entry)) pattern = _
      rw [newScopes]
    have openedBody :
        (body.inst assignment).inst (openAt κ site middle.scope) =
          body.inst (relabel κ (scopeNames (Context.scopes inner extended) entry)) := by
      rw [comp_open, newScopes]
    have bind : Reaches schedule 1
        (around.state middle
          ⟨knowledge ++ producerResult.1.2, .value producerResult.2, frame :: frames, cells⟩)
        (around.state middle.fresh ⟨knowledge ++ producerResult.1.2 ++ [equation],
          .eval (body.inst (relabel κ (scopeNames (Context.scopes inner extended) entry))), frames, cells⟩) := by
      rw [← openedBody, show equation = (equation.1, equation.2) from rfl, openedPattern]
      exact oneMove kept middle _ _ liveProducer
        ⟨middle.fresh, [_], .letBind _ _ _ _ _ _ _ _⟩ rfl rfl
    have last := ihBody inner (atBind + 1) extended middle.fresh
      (knowledge ++ producerResult.1.2 ++ [equation]) frames
      (Context.push_earlier site (Context.earlier_of_le older (by dsimp [atBind]; omega)))
      (by change middle.scope + 1 = origin + (atBind + 1); rw [middleClock, Nat.add_assoc])
      liveContinuation
    have reaches := Reaches.append schedule (Reaches.append schedule (Reaches.append schedule begin first) bind) last
    dsimp only
    rw [execute_lower_binding]
    simpa only [Fragment.moves, Fragment.bindings, middle, laterWorld_bind, List.append_assoc, List.singleton_append]
      using reaches

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.BindingSimulation
