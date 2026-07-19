/-
# Bounded typed-hole refinement for the Pure dependent fragment

The policy chooses only four action families: select the current hole, choose a
de Bruijn head, acknowledge the checker-computed spine length, and finish.  Pi
introduction, slot order, context extension, and dependent substitution are
deterministic checker work.  The bounded `canComplete` search filters raw steps
exactly as the sealed Gauthier mask does.
-/

import Mathlib.Tactic
import Mettapedia.GSLT.LanguageDef.RefinementInterface
import Mettapedia.GSLT.LanguageDef.Pure.Statics

namespace Mettapedia.GSLT.LanguageDef.PureRefinement

open Mettapedia.GSLT.LanguageDef.RefinementInterface
open Mettapedia.GSLT.LanguageDef.Pure

/-- Policy-visible action vocabulary. -/
inductive Action where
  | selectHole : Nat → Action
  | selectBoundHead : Nat → Action
  | createDependentSpine : Nat → Action
  | finish
  deriving DecidableEq, Repr

/-- Obligations exposed by the generic interface. -/
inductive Hole where
  | term : Nat → Ctx → Expr → Hole
  | finalize
  deriving Repr

/-- Continuations for deterministic lambda introduction and ordered spines. -/
inductive Frame where
  | lambda : Expr → Frame
  | spine :
      Ctx → Nat → List Nf → Expr → Expr → Frame
  deriving Repr

/-- The four elaboration phases plus completed and accepted terms. -/
inductive Core where
  | needHole : Nat → Ctx → Expr → List Frame → Core
  | needHead : Nat → Ctx → Expr → List Frame → Core
  | needSpine : Nat → Ctx → Expr → List Frame → Nat → Expr → Core
  | done : Nf → Core
  | finished : Nf → Core
  deriving Repr

/-- Automatically introduce every Pi before exposing a head-choice hole. -/
def prepare (holeId : Nat) : Ctx → Expr → List Frame → Core
  | context, .pi domain body, frames =>
      prepare holeId (domain :: context) body (.lambda domain :: frames)
  | context, target, frames => .needHole holeId context target frames

/-- Deliver a completed subterm through lambda/spine continuations. -/
def deliver : Nf → List Frame → Option Core
  | term, [] => some (.done term)
  | term, .lambda domain :: rest => deliver (.lam domain term) rest
  | term, .spine context head arguments body expected :: rest =>
      let arguments := arguments ++ [term]
      let application := Nf.head head arguments
      let nextType := Expr.subst0 term.erase body
      if nextType = expected then
        deliver application rest
      else
        match nextType with
        | .pi domain nextBody =>
            some
              (prepare 0 context domain
                (.spine context head arguments nextBody expected :: rest))
        | _ => none

/-- Continue a checker-owned spine after a (possibly empty) argument prefix. -/
def startSpineWith (context : Ctx) (expected : Expr) (frames : List Frame)
    (head : Nat) (arguments : List Nf) (headType : Expr) : Option Core :=
  match headType with
  | .pi domain body =>
      some
        (prepare 0 context domain
          (.spine context head arguments body expected :: frames))
  | _ =>
      if headType = expected then deliver (.head head arguments) frames else none

/-- Start the exact number of argument slots certified by the selected head type. -/
def startSpine (context : Ctx) (expected : Expr) (frames : List Frame)
    (head : Nat) (headType : Expr) : Option Core :=
  startSpineWith context expected frames head [] headType

/-- One unbudgeted checker transition. -/
def rawStep (goal : Expr) : Core → Action → Option Core
  | .needHole holeId context target frames, .selectHole selected =>
      if selected = holeId then some (.needHead holeId context target frames) else none
  | .needHead holeId context target frames, .selectBoundHead index => do
      let headType ← ctxLookup context index
      some (.needSpine holeId context target frames index headType)
  | .needSpine _ context target frames head headType,
      .createDependentSpine arity =>
      if arity = headType.piArity then
        startSpine context target frames head headType
      else
        none
  | .done term, .finish =>
      if inferNf [] term = some goal then some (.finished term) else none
  | _, _ => none

/-- Finite raw action enumeration; failed candidates are removed by `rawStep`. -/
def rawActions : Core → List Action
  | .needHole holeId _ _ _ => [.selectHole holeId]
  | .needHead _ context _ _ =>
      (List.range context.length).map Action.selectBoundHead
  | .needSpine _ _ _ _ _ headType =>
      [.createDependentSpine headType.piArity]
  | .done _ => [.finish]
  | .finished _ => []

def rawRun (goal : Expr) : List Action → Core → Option Core
  | [], core => some core
  | action :: rest, core => do
      let next ← rawStep goal core action
      rawRun goal rest next

def rawRunFrom? (goal : Expr) (actions : List Action) : Option Core → Option Core
  | none => none
  | some core => rawRun goal actions core

def Core.isFinished : Core → Bool
  | .finished _ => true
  | _ => false

/-- Exact bounded reachability to a checker-accepted terminal core. -/
def canComplete (goal : Expr) (core : Core) : Nat → Bool
  | 0 => core.isFinished
  | remaining + 1 =>
      core.isFinished ||
        (rawActions core).any fun action =>
          match rawStep goal core action with
          | none => false
          | some next => canComplete goal next remaining

/-- Budgeted runtime state. -/
structure State where
  core : Core
  tokensEmitted : Nat
  maxLen : Nat
  deriving Repr

def initial (goal : Expr) (maxLen : Nat) : State :=
  { core := prepare 0 [] goal []
    tokensEmitted := 0
    maxLen := maxLen }

def Core.holes : Core → List Hole
  | .needHole holeId context target _ => [.term holeId context target]
  | .needHead holeId context target _ => [.term holeId context target]
  | .needSpine holeId context target _ _ _ => [.term holeId context target]
  | .done _ => [.finalize]
  | .finished _ => []

def terminal (state : State) : Prop :=
  state.core.isFinished = true

instance terminalDecidable (state : State) : Decidable (terminal state) := by
  unfold terminal
  infer_instance

def viable (goal : Expr) (state : State) : Prop :=
  terminal state ∨
    (state.tokensEmitted ≤ state.maxLen ∧
      canComplete goal state.core (state.maxLen - state.tokensEmitted) = true)

/-- A proposed action is legal only when its successor still has a bounded completion. -/
def actionLegal (goal : Expr) (state : State) (action : Action) : Bool :=
  if state.tokensEmitted < state.maxLen then
    match rawStep goal state.core action with
    | none => false
    | some next =>
        canComplete goal next (state.maxLen - (state.tokensEmitted + 1))
  else
    false

def step? (goal : Expr) (state : State) (action : Action) : Option State :=
  if actionLegal goal state action then
    match rawStep goal state.core action with
    | none => none
    | some next =>
        some
          { core := next
            tokensEmitted := state.tokensEmitted + 1
            maxLen := state.maxLen }
  else
    none

mutual
/-- Fuelled canonical action serialization.  Pi lambdas are checker-created. -/
def encodeNfFuel : Nat → Ctx → Nf → List Action
  | 0, _, _ => []
  | fuel + 1, context, .lam domain body =>
      encodeNfFuel fuel (domain :: context) body
  | fuel + 1, context, .head index arguments =>
      let arity := (ctxLookup context index).map Expr.piArity |>.getD 0
      [.selectHole 0, .selectBoundHead index,
        .createDependentSpine arity] ++
      encodeArgsFuel fuel context arguments

def encodeArgsFuel : Nat → Ctx → List Nf → List Action
  | 0, _, _ => []
  | _fuel + 1, _, [] => []
  | fuel + 1, context, argument :: rest =>
      encodeNfFuel fuel context argument ++ encodeArgsFuel fuel context rest
end

def encode (term : Nf) : List Action :=
  encodeNfFuel (term.weight + 1) [] term ++ [.finish]

/-- Decode by the raw checker, then independently recheck the resulting term. -/
def decode (goal : Expr) (trace : List Action) : Option Nf :=
  match rawRun goal trace (prepare 0 [] goal []) with
  | some (.finished term) =>
      if inferNf [] term = some goal then some term else none
  | _ => none

theorem rawRun_append (goal : Expr) (first second : List Action) (core : Core) :
    rawRun goal (first ++ second) core =
      match rawRun goal first core with
      | none => none
      | some middle => rawRun goal second middle := by
  induction first generalizing core with
  | nil => rfl
  | cons action rest ih =>
      simp only [List.cons_append, rawRun]
      cases hstep : rawStep goal core action with
      | none => rfl
      | some next => exact ih next

theorem prepare_atomic {holeId : Nat} {context : Ctx} {target : Expr}
    {frames : List Frame} (hatomic : target.Atomic) :
    prepare holeId context target frames =
      .needHole holeId context target frames := by
  cases target <;> simp [prepare, Expr.Atomic] at hatomic ⊢

/-- Filling one dependent slot computes the next checker-owned slot by substitution. -/
theorem deliver_spine_eq_startSpineWith {context : Ctx} {head : Nat}
    {arguments : List Nf} {body expected : Expr} {frames : List Frame}
    (argument : Nf) (hatomic : expected.Atomic) :
    deliver argument (.spine context head arguments body expected :: frames) =
      startSpineWith context expected frames head (arguments ++ [argument])
        (Expr.subst0 argument.erase body) := by
  generalize hnext : Expr.subst0 argument.erase body = nextType
  cases nextType <;> cases expected <;>
    simp [deliver, startSpineWith, hnext, Expr.Atomic] at hatomic ⊢

/-- The three visible head-selection actions reduce exactly to checker spine creation. -/
theorem rawRun_headPrefix (goal : Expr) {context : Ctx} {index : Nat}
    {headType target : Expr} {frames : List Frame} (rest : List Action)
    (hlookup : ctxLookup context index = some headType)
    (hatomic : target.Atomic) :
    rawRun goal
        ([.selectHole 0, .selectBoundHead index,
          .createDependentSpine headType.piArity] ++ rest)
        (prepare 0 context target frames) =
      rawRunFrom? goal rest
        (startSpineWith context target frames index [] headType) := by
  rw [prepare_atomic hatomic]
  simp [rawRun, rawStep, hlookup, startSpine]
  cases startSpineWith context target frames index [] headType <;>
    rfl

/-- Canonical traces simulate semantic terms and ordered semantic spines. -/
theorem encodeFuel_simulation (goal : Expr) : ∀ fuel,
    (∀ context term type frames,
      term.weight < fuel →
      HasType context term type →
      rawRun goal (encodeNfFuel fuel context term)
          (prepare 0 context type frames) = deliver term frames) ∧
    (∀ context headType arguments resultType head builtArgs frames,
      Nf.listWeight arguments < fuel →
      SpineHasType context headType arguments resultType →
      resultType.Atomic →
      rawRunFrom? goal (encodeArgsFuel fuel context arguments)
          (startSpineWith context resultType frames head builtArgs headType) =
        deliver (.head head (builtArgs ++ arguments)) frames) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor <;> intro <;> omega
  | succ fuel ih =>
      constructor
      · intro context term type frames hweight htype
        cases htype with
        | lam hbody =>
            simp only [Nf.weight] at hweight
            simpa [encodeNfFuel, prepare, deliver] using
              ih.1 _ _ _ (.lambda _ :: frames) (by omega) hbody
        | head hlookup hspine hatomic =>
            rename_i index headType arguments
            simp only [Nf.weight] at hweight
            have hprefix :=
              rawRun_headPrefix goal
                (context := context) (index := index)
                (headType := headType) (target := type) (frames := frames)
                (encodeArgsFuel fuel context arguments) hlookup hatomic
            have htail :=
              ih.2 context headType arguments type index [] frames
                (by omega) hspine hatomic
            simpa [encodeNfFuel, hlookup] using hprefix.trans htail
      · intro context headType arguments resultType head builtArgs frames
          hweight htype hatomic
        cases htype with
        | nil =>
            cases hdeliver : deliver (.head head builtArgs) frames <;>
              cases headType <;>
                simp [encodeArgsFuel, rawRunFrom?, startSpineWith, rawRun,
                  Expr.Atomic, hdeliver] at hatomic ⊢
        | @cons _ domain body argument rest _ hargument hrest =>
            simp only [Nf.listWeight] at hweight
            have hargumentRun :=
              ih.1 context argument domain
                (.spine context head builtArgs body resultType :: frames)
                (by omega) hargument
            have hrestRun :=
              ih.2 context (Expr.subst0 argument.erase body) rest resultType
                head (builtArgs ++ [argument]) frames (by omega) hrest hatomic
            change
              rawRun goal
                  (encodeNfFuel fuel context argument ++
                    encodeArgsFuel fuel context rest)
                  (prepare 0 context domain
                    (.spine context head builtArgs body resultType :: frames)) =
                deliver (.head head (builtArgs ++ argument :: rest)) frames
            rw [rawRun_append, hargumentRun]
            change
              rawRunFrom? goal (encodeArgsFuel fuel context rest)
                  (deliver argument
                    (.spine context head builtArgs body resultType :: frames)) =
                deliver (.head head (builtArgs ++ argument :: rest)) frames
            rw [deliver_spine_eq_startSpineWith argument hatomic, hrestRun]
            simp [List.append_assoc]

/-! ## Exact bounded-completion metatheory -/

/-- The finite action enumeration contains every successful raw transition. -/
theorem rawStep_mem_rawActions {goal : Expr} {core next : Core} {action : Action}
    (hstep : rawStep goal core action = some next) :
    action ∈ rawActions core := by
  cases core with
  | needHole holeId context target frames =>
      cases action with
      | selectHole selected =>
          simp only [rawStep] at hstep
          by_cases hselected : selected = holeId
          · subst selected
            simp [rawActions]
          · simp [hselected] at hstep
      | selectBoundHead index => simp [rawStep] at hstep
      | createDependentSpine arity => simp [rawStep] at hstep
      | finish => simp [rawStep] at hstep
  | needHead holeId context target frames =>
      cases action with
      | selectHole selected => simp [rawStep] at hstep
      | selectBoundHead index =>
          simp only [rawStep] at hstep
          cases hlookup : ctxLookup context index with
          | none => simp [hlookup] at hstep
          | some headType =>
              simp [rawActions, ctxLookup_some_lt hlookup]
      | createDependentSpine arity => simp [rawStep] at hstep
      | finish => simp [rawStep] at hstep
  | needSpine holeId context target frames head headType =>
      cases action with
      | selectHole selected => simp [rawStep] at hstep
      | selectBoundHead index => simp [rawStep] at hstep
      | createDependentSpine arity =>
          by_cases harity : arity = headType.piArity
          · simp [rawActions, harity]
          · simp [rawStep, harity] at hstep
      | finish => simp [rawStep] at hstep
  | done term =>
      cases action with
      | selectHole selected => simp [rawStep] at hstep
      | selectBoundHead index => simp [rawStep] at hstep
      | createDependentSpine arity => simp [rawStep] at hstep
      | finish => simp [rawActions]
  | finished term => simp [rawStep] at hstep

/-- A raw accepted suffix is a constructive witness for the bounded decision. -/
theorem canComplete_of_rawRun (goal : Expr) :
    ∀ (actions : List Action) (core finalCore : Core) (remaining : Nat),
      actions.length ≤ remaining →
      rawRun goal actions core = some finalCore →
      finalCore.isFinished = true →
      canComplete goal core remaining = true
  | [], core, finalCore, remaining, _hlength, hrun, hfinished => by
      simp only [rawRun, Option.some.injEq] at hrun
      subst finalCore
      cases remaining <;> simp [canComplete, hfinished]
  | action :: rest, core, finalCore, remaining, hlength, hrun, hfinished => by
      cases remaining with
      | zero => simp at hlength
      | succ remaining =>
          simp only [rawRun] at hrun
          cases hstep : rawStep goal core action with
          | none =>
              rw [hstep] at hrun
              contradiction
          | some next =>
              rw [hstep] at hrun
              have htail : canComplete goal next remaining = true :=
                canComplete_of_rawRun goal rest next finalCore remaining
                  (by simpa using hlength) hrun hfinished
              simp only [canComplete, Bool.or_eq_true]
              right
              simp only [List.any_eq_true]
              exact
                ⟨action, rawStep_mem_rawActions hstep,
                  by simp [hstep, htail]⟩

/-- The bounded decision returns an explicit accepted raw suffix. -/
theorem canComplete_witness (goal : Expr) :
    ∀ (remaining : Nat) (core : Core),
      canComplete goal core remaining = true →
      ∃ actions finalCore,
        actions.length ≤ remaining ∧
        rawRun goal actions core = some finalCore ∧
        finalCore.isFinished = true
  | 0, core, hcomplete => by
      exact ⟨[], core, by simp, rfl, by simpa [canComplete] using hcomplete⟩
  | remaining + 1, core, hcomplete => by
      simp only [canComplete, Bool.or_eq_true] at hcomplete
      rcases hcomplete with hfinished | hbranch
      · exact ⟨[], core, by simp, rfl, hfinished⟩
      · simp only [List.any_eq_true] at hbranch
        rcases hbranch with ⟨action, _hmem, hchosen⟩
        cases hstep : rawStep goal core action with
        | none => simp [hstep] at hchosen
        | some next =>
            simp only [hstep] at hchosen
            rcases canComplete_witness goal remaining next hchosen with
              ⟨rest, finalCore, hlength, hrun, hfinished⟩
            exact
              ⟨action :: rest, finalCore, by simp; omega,
                by simp [rawRun, hstep, hrun], hfinished⟩

/-! ## The Pure instance and its interface laws -/

/-- Every semantically typed normal form is executed by its canonical raw trace. -/
theorem rawRun_encode {goal : Expr} {term : Nf}
    (htype : HasType [] term goal) :
    rawRun goal (encode term) (prepare 0 [] goal []) = some (.finished term) := by
  have hsimulation :=
    (encodeFuel_simulation goal (term.weight + 1)).1 [] term goal []
      (by omega) htype
  unfold encode
  rw [rawRun_append, hsimulation]
  simp [deliver, rawRun, rawStep, inferNf_complete htype]

theorem decode_encode {goal : Expr} {term : Nf}
    (htype : HasType [] term goal) :
    decode goal (encode term) = some term := by
  simp [decode, rawRun_encode htype, inferNf_complete htype]

/-- The root-parametric interface specialized to one closed Pure Pi goal. -/
abbrev pureRoot (goal : Expr) : RefinementInterface where
  State := State
  Hole := Hole
  Action := Action
  Program := Nf
  initial := initial goal
  holes := fun state => state.core.holes
  legal := fun state action => actionLegal goal state action = true
  apply? := step? goal
  terminal := terminal
  decode := decode goal
  wellFormed := fun term => HasType [] term goal
  programCost := fun term => (encode term).length
  encode := encode
  invariant := viable goal
  canComplete := viable goal
  budgetOK := fun budget =>
    canComplete goal (prepare 0 [] goal []) budget = true

theorem actionLegal_eq_true_iff (goal : Expr) (state : State) (action : Action) :
    actionLegal goal state action = true ↔
      state.tokensEmitted < state.maxLen ∧
      ∃ next,
        rawStep goal state.core action = some next ∧
        canComplete goal next
          (state.maxLen - (state.tokensEmitted + 1)) = true := by
  unfold actionLegal
  by_cases htime : state.tokensEmitted < state.maxLen
  · rw [if_pos htime]
    cases hstep : rawStep goal state.core action with
    | none => simp
    | some next => simp [htime]
  · simp [htime]

theorem exists_step_iff_actionLegal (goal : Expr) (state : State) (action : Action) :
    (∃ next, step? goal state action = some next) ↔
      actionLegal goal state action = true := by
  constructor
  · rintro ⟨next, hstep⟩
    by_cases hlegal : actionLegal goal state action = true
    · exact hlegal
    · simp [step?, hlegal] at hstep
  · intro hlegal
    rcases (actionLegal_eq_true_iff goal state action).mp hlegal with
      ⟨_time, next, hraw, _hcomplete⟩
    exact
      ⟨{ core := next
         tokensEmitted := state.tokensEmitted + 1
         maxLen := state.maxLen }, by
        simp [step?, hlegal, hraw]⟩

/-- Every successful filtered step preserves bounded viability. -/
theorem step_preserves_viable {goal : Expr} {state next : State} {action : Action}
    (_hviable : viable goal state)
    (hstep : step? goal state action = some next) :
    viable goal next := by
  have hlegal : actionLegal goal state action = true :=
    (exists_step_iff_actionLegal goal state action).mp ⟨next, hstep⟩
  rcases (actionLegal_eq_true_iff goal state action).mp hlegal with
    ⟨htime, nextCore, hraw, hcomplete⟩
  simp [step?, hlegal, hraw] at hstep
  subst next
  by_cases hfinished : nextCore.isFinished = true
  · exact Or.inl hfinished
  · right
    constructor
    · change state.tokensEmitted + 1 ≤ state.maxLen
      omega
    · exact hcomplete

/-- A successful filtered step also certifies viability of its source state. -/
theorem viable_of_step {goal : Expr} {state next : State} {action : Action}
    (hstep : step? goal state action = some next) :
    viable goal state := by
  have hlegal : actionLegal goal state action = true :=
    (exists_step_iff_actionLegal goal state action).mp ⟨next, hstep⟩
  rcases (actionLegal_eq_true_iff goal state action).mp hlegal with
    ⟨htime, nextCore, hraw, hcomplete⟩
  right
  constructor
  · omega
  · have hremaining :
        state.maxLen - state.tokensEmitted =
          state.maxLen - (state.tokensEmitted + 1) + 1 := by
        omega
    rw [hremaining]
    simp only [canComplete, Bool.or_eq_true]
    right
    simp only [List.any_eq_true]
    exact
      ⟨action, rawStep_mem_rawActions hraw,
        by simp [hraw, hcomplete]⟩

/-- A raw bounded completion survives the viability filter action-for-action. -/
theorem run_of_rawRun (goal : Expr) :
    ∀ (actions : List Action) (core finalCore : Core)
      (tokensEmitted maxLen : Nat),
      tokensEmitted + actions.length ≤ maxLen →
      rawRun goal actions core = some finalCore →
      finalCore.isFinished = true →
      (pureRoot goal).run actions
          { core := core, tokensEmitted := tokensEmitted, maxLen := maxLen } =
        some
          { core := finalCore
            tokensEmitted := tokensEmitted + actions.length
            maxLen := maxLen }
  | [], core, finalCore, tokensEmitted, maxLen,
      _hbudget, hrun, _hfinished => by
      simp only [rawRun, Option.some.injEq] at hrun
      subst finalCore
      rfl
  | action :: rest, core, finalCore, tokensEmitted, maxLen,
      hbudget, hrun, hfinished => by
      simp only [rawRun] at hrun
      cases hraw : rawStep goal core action with
      | none =>
          rw [hraw] at hrun
          contradiction
      | some nextCore =>
          rw [hraw] at hrun
          have htime : tokensEmitted < maxLen := by
            simp only [List.length_cons] at hbudget
            omega
          have htailLength :
              rest.length ≤ maxLen - (tokensEmitted + 1) := by
            simp only [List.length_cons] at hbudget
            omega
          have htailComplete :
              canComplete goal nextCore (maxLen - (tokensEmitted + 1)) = true :=
            canComplete_of_rawRun goal rest nextCore finalCore
              (maxLen - (tokensEmitted + 1)) htailLength hrun hfinished
          have hlegal :
              actionLegal goal
                { core := core
                  tokensEmitted := tokensEmitted
                  maxLen := maxLen } action = true :=
            (actionLegal_eq_true_iff goal _ _).mpr
              ⟨htime, nextCore, hraw, htailComplete⟩
          have hfiltered :
              step? goal
                { core := core
                  tokensEmitted := tokensEmitted
                  maxLen := maxLen } action =
                some
                  { core := nextCore
                    tokensEmitted := tokensEmitted + 1
                    maxLen := maxLen } := by
            simp [step?, hlegal, hraw]
          simp only [RefinementInterface.run, hfiltered]
          have htailBudget :
              (tokensEmitted + 1) + rest.length ≤ maxLen := by
            simp only [List.length_cons] at hbudget
            omega
          have htailRun :=
            run_of_rawRun goal rest nextCore finalCore
              (tokensEmitted + 1) maxLen htailBudget hrun hfinished
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htailRun

/-- Interface completion is exactly the terminal-or-bounded viability predicate. -/
theorem hasCompletion_iff_viable (goal : Expr) (state : State) :
    (pureRoot goal).HasCompletion state ↔ viable goal state := by
  constructor
  · rintro ⟨suffix, finalState, hrun, hterminal⟩
    cases suffix with
    | nil =>
        simp only [RefinementInterface.run, Option.some.injEq] at hrun
        subst finalState
        exact Or.inl hterminal
    | cons action rest =>
        simp only [RefinementInterface.run] at hrun
        cases hstep : step? goal state action with
        | none =>
            rw [hstep] at hrun
            contradiction
        | some next => exact viable_of_step hstep
  · intro hviable
    rcases hviable with hterminal | ⟨hbudget, hcomplete⟩
    · exact ⟨[], state, rfl, hterminal⟩
    · rcases canComplete_witness goal
          (state.maxLen - state.tokensEmitted) state.core hcomplete with
        ⟨suffix, finalCore, hlength, hraw, hfinished⟩
      have hrunBudget : state.tokensEmitted + suffix.length ≤ state.maxLen := by
        omega
      let finalState : State :=
        { core := finalCore
          tokensEmitted := state.tokensEmitted + suffix.length
          maxLen := state.maxLen }
      exact
        ⟨suffix, finalState,
          run_of_rawRun goal suffix state.core finalCore
            state.tokensEmitted state.maxLen hrunBudget hraw hfinished,
          hfinished⟩

theorem terminal_iff_holes_empty (state : State) :
    terminal state ↔ state.core.holes = [] := by
  cases state with
  | mk core tokensEmitted maxLen =>
      cases core <;> simp [terminal, Core.holes, Core.isFinished]

theorem decode_sound {goal : Expr} {trace : List Action} {term : Nf}
    (hdecode : decode goal trace = some term) :
    HasType [] term goal := by
  unfold decode at hdecode
  cases hrun : rawRun goal trace (prepare 0 [] goal []) with
  | none => simp [hrun] at hdecode
  | some finalCore =>
      rw [hrun] at hdecode
      cases finalCore <;> try simp at hdecode
      rename_i accepted
      by_cases hinfer : inferNf [] accepted = some goal
      · simp [hinfer] at hdecode
        subst term
        exact inferNf_sound hinfer
      · simp [hinfer] at hdecode

/-- All T3 per-root obligations are discharged without additional assumptions. -/
def pureLaws (goal : Expr) : RefinementLaws (pureRoot goal) where
  legal_iff_apply := by
    intro state action
    exact (exists_step_iff_actionLegal goal state action).symm
  terminal_iff_holes_empty := terminal_iff_holes_empty
  initial_invariant := by
    intro budget hbudget
    exact Or.inr ⟨by simp [initial], by simpa [initial] using hbudget⟩
  apply_invariant := by
    intro state action next hviable hstep
    exact step_preserves_viable hviable hstep
  sound := by
    intro budget trace finalState term _hrun _hterminal hdecode
    exact decode_sound hdecode
  complete := by
    intro budget term _hbudget htype hcost
    have hraw := rawRun_encode htype
    have hrun :=
      run_of_rawRun goal (encode term) (prepare 0 [] goal []) (.finished term)
        0 budget (by simpa using hcost) hraw rfl
    have hrun' :
        (pureRoot goal).run ((pureRoot goal).encode term)
            ((pureRoot goal).initial budget) =
          some
            { core := .finished term
              tokensEmitted := (encode term).length
              maxLen := budget } := by
      simpa [pureRoot, initial] using hrun
    exact
      ⟨{ core := .finished term
         tokensEmitted := (encode term).length
         maxLen := budget }, hrun', rfl, decode_encode htype⟩
  invariant_canComplete := by
    intro state hviable
    exact hviable
  canComplete_iff_hasCompletion := by
    intro state
    exact (hasCompletion_iff_viable goal state).symm

/-! ## Executable phase and dependency fixtures -/

def identityGoal : Expr :=
  .pi .sort (.pi (.bvar 0) (.bvar 1))

def identityTerm : Nf :=
  .lam .sort (.lam (.bvar 0) (.head 0 []))

def identityTrace : List Action :=
  [.selectHole 0, .selectBoundHead 0, .createDependentSpine 0, .finish]

example : rawRun identityGoal identityTrace (prepare 0 [] identityGoal []) =
    some (.finished identityTerm) := by
  norm_num [identityGoal, identityTrace, identityTerm, rawRun, rawStep, prepare,
    startSpine, startSpineWith, deliver, ctxLookup, ctxLookupAux, Expr.lift, Expr.piArity,
    inferNf, inferNfFuel, inferSpineFuel, Nf.weight, Nf.listWeight, Expr.atomic]

example : rawStep identityGoal (prepare 0 [] identityGoal []) (.selectHole 1) = none := by
  norm_num [identityGoal, rawStep, prepare]

example : rawStep identityGoal
    (.needSpine 0 [.sort] (.bvar 0) [] 0 (.pi .sort .sort))
    (.createDependentSpine 0) = none := by
  norm_num [rawStep, Expr.piArity]

end Mettapedia.GSLT.LanguageDef.PureRefinement
