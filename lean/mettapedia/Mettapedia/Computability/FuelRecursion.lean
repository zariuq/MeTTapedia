import Mathlib.Computability.Partrec

/-!
# Recursion within a fuel is computable

A function given within a fuel calls itself, with one less fuel, on finitely many arguments computed from its own:
`run 0 x = base x` and `run (k + 1) x = combine k x ((calls k x).map (run k))`. Its arguments need not be smaller than
`x` in any sense; the fuel alone bounds the recursion. When `base`, `calls` and `combine` are computable, so is `run`
(`run_computable`).

The proof runs a machine with a stack of tasks and a stack of values. A task either evaluates an argument within a
fuel, replacing itself by the tasks for its calls and a task that combines their values, or combines the values the
calls left on top of the value stack. Each step is computable, and the machine run to its end is the fixed point of its
step, which is partial recursive (`Partrec.fix`). From a task that evaluates, the machine leaves exactly the value of
the recursion on the value stack (`fix_evaluate`).
-/

set_option autoImplicit false

namespace Mettapedia.Computability.FuelRecursion

variable (base : ℕ → ℕ) (calls : ℕ → ℕ → List ℕ) (combine : ℕ → ℕ → List ℕ → ℕ)

/-- **The recursion within a fuel.** -/
def run : ℕ → ℕ → ℕ
  | 0, x => base x
  | k + 1, x => combine k x ((calls k x).map (run k))

@[simp] theorem run_zero (x : ℕ) : run base calls combine 0 x = base x := rfl

theorem run_succ (k x : ℕ) :
    run base calls combine (k + 1) x = combine k x ((calls k x).map (run base calls combine k)) := rfl

/-- A task of the machine: `(true, k, x)` evaluates `x` within the fuel `k`; `(false, k, x)` combines the values of
the calls of `x` within the fuel `k + 1`. -/
abbrev Task := Bool × ℕ × ℕ

/-- A state of the machine: the tasks to do, and the values computed. -/
abbrev State := List Task × List ℕ

/-- The tasks that evaluate the calls of `x` within the fuel `k`, then combine their values. -/
def expand (k x : ℕ) (tasks : List Task) : List Task :=
  (calls k x).map (fun call => (true, k, call)) ++ (false, k, x) :: tasks

/-- Combine the values of the calls of `x` within the fuel `k`, the last call's value on top. -/
def collect (k x : ℕ) (values : List ℕ) : List ℕ :=
  combine k x ((values.take (calls k x).length).reverse) :: values.drop (calls k x).length

/-- Carry out the task on top of the state. -/
def perform (state : State) (task : Task) : ℕ ⊕ State :=
  cond task.1
    (Nat.casesOn (motive := fun _ => ℕ ⊕ State) task.2.1 (.inr (state.1.tail, base task.2.2 :: state.2))
      fun k => .inr (expand calls k task.2.2 state.1.tail, state.2))
    (.inr (state.1.tail, collect calls combine task.2.1 task.2.2 state.2))

/-- **One step of the machine**: with no task left, the value on top is the result. -/
def step (state : State) : ℕ ⊕ State :=
  Option.casesOn (motive := fun _ => ℕ ⊕ State) state.1.head? (.inl state.2.headI)
    (perform base calls combine state)

/-- The machine as a partial function. -/
def machine : State →. ℕ ⊕ State := fun state => Part.some (step base calls combine state)

theorem fix_forward {state next : State} (stepped : step base calls combine state = .inr next) :
    (machine base calls combine).fix state = (machine base calls combine).fix next :=
  PFun.fix_fwd_eq (by simp [machine, stepped])

/-- **Tasks that evaluate a list of arguments** leave their values on the value stack, the last on top. -/
theorem fix_evaluate_all (k : ℕ)
    (evaluate : ∀ (x : ℕ) (tasks : List Task) (values : List ℕ),
      (machine base calls combine).fix ((true, k, x) :: tasks, values) =
        (machine base calls combine).fix (tasks, run base calls combine k x :: values)) :
    ∀ (arguments : List ℕ) (tasks : List Task) (values : List ℕ),
      (machine base calls combine).fix (arguments.map (fun argument => (true, k, argument)) ++ tasks, values) =
        (machine base calls combine).fix (tasks, (arguments.map (run base calls combine k)).reverse ++ values)
  | [], tasks, values => by simp
  | argument :: rest, tasks, values => by
      simp only [List.map_cons, List.cons_append]
      rw [evaluate, fix_evaluate_all k evaluate rest]
      simp [List.reverse_cons, List.append_assoc]

/-- **A task that evaluates leaves the value of the recursion.** -/
theorem fix_evaluate : ∀ (k x : ℕ) (tasks : List Task) (values : List ℕ),
    (machine base calls combine).fix ((true, k, x) :: tasks, values) =
      (machine base calls combine).fix (tasks, run base calls combine k x :: values)
  | 0, x, tasks, values => fix_forward base calls combine rfl
  | k + 1, x, tasks, values => by
      rw [fix_forward base calls combine (next := (expand calls k x tasks, values)) rfl]
      unfold expand
      rw [fix_evaluate_all base calls combine k (fix_evaluate k) (calls k x) ((false, k, x) :: tasks) values]
      rw [fix_forward base calls combine (next := (tasks, collect calls combine k x
        (((calls k x).map (run base calls combine k)).reverse ++ values))) rfl]
      have length : ((calls k x).map (run base calls combine k)).reverse.length = (calls k x).length := by simp
      simp only [collect, List.take_left' length, List.drop_left' length, List.reverse_reverse, run_succ]

/-- **The machine computes the recursion.** -/
theorem fix_run (k x : ℕ) :
    (machine base calls combine).fix ([(true, k, x)], []) = Part.some (run base calls combine k x) := by
  rw [fix_evaluate]
  exact Part.eq_some_iff.mpr (PFun.fix_stop (by simp [machine, step]))

/-! ## Computability -/

section Computability

variable {base calls combine}

theorem expand_computable (hCalls : Computable₂ calls) :
    Computable fun input : ℕ × ℕ × List Task => expand calls input.1 input.2.1 input.2.2 := by
  have tag : Primrec fun pair : List ℕ × ℕ => pair.1.map fun call => ((true, pair.2, call) : Task) :=
    Primrec.list_map Primrec.fst
      (Primrec.pair (Primrec.const true) (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂
  have tasks : Computable fun input : ℕ × ℕ × List Task =>
      (input.1, input.2.1, input.2.2).2.2 := Computable.snd.comp Computable.snd
  refine (Primrec.list_append.to_comp).comp ?_ ?_
  · exact tag.to_comp.comp (Computable.pair (hCalls.comp Computable.fst (Computable.fst.comp Computable.snd))
      Computable.fst)
  · exact (Primrec.list_cons.to_comp).comp
      (Computable.pair (Computable.const false) (Computable.pair Computable.fst (Computable.fst.comp Computable.snd)))
      tasks

theorem collect_computable (hCalls : Computable₂ calls)
    (hCombine : Computable fun input : ℕ × ℕ × List ℕ => combine input.1 input.2.1 input.2.2) :
    Computable fun input : ℕ × ℕ × List ℕ => collect calls combine input.1 input.2.1 input.2.2 := by
  have count : Computable fun input : ℕ × ℕ × List ℕ => (calls input.1 input.2.1).length :=
    Primrec.list_length.to_comp.comp (hCalls.comp Computable.fst (Computable.fst.comp Computable.snd))
  have values : Computable fun input : ℕ × ℕ × List ℕ => input.2.2 := Computable.snd.comp Computable.snd
  have taken : Computable fun input : ℕ × ℕ × List ℕ => (input.2.2.take (calls input.1 input.2.1).length).reverse :=
    Primrec.list_reverse.to_comp.comp ((Primrec.list_take.to_comp).comp count values)
  refine (Primrec.list_cons.to_comp).comp ?_ ((Primrec.list_drop.to_comp).comp count values)
  exact hCombine.comp (Computable.pair Computable.fst (Computable.pair (Computable.fst.comp Computable.snd) taken))

theorem step_computable (hBase : Computable base) (hCalls : Computable₂ calls)
    (hCombine : Computable fun input : ℕ × ℕ × List ℕ => combine input.1 input.2.1 input.2.2) :
    Computable (step base calls combine) := by
  have tail : Computable fun input : State × Task => input.1.1.tail :=
    Primrec.list_tail.to_comp.comp (Computable.fst.comp Computable.fst)
  have values : Computable fun input : State × Task => input.1.2 := Computable.snd.comp Computable.fst
  have inr : Computable (Sum.inr : State → ℕ ⊕ State) := Computable.sumInr
  have evaluateZero : Computable fun input : State × Task =>
      (Sum.inr (input.1.1.tail, base input.2.2.2 :: input.1.2) : ℕ ⊕ State) :=
    inr.comp (Computable.pair tail ((Primrec.list_cons.to_comp).comp
      (hBase.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))) values))
  have evaluateSucc : Computable fun input : (State × Task) × ℕ =>
      (Sum.inr (expand calls input.2 input.1.2.2.2 input.1.1.1.tail, input.1.1.2) : ℕ ⊕ State) := by
    have arguments : Computable fun input : (State × Task) × ℕ =>
        (input.2, input.1.2.2.2, input.1.1.1.tail) :=
      Computable.pair Computable.snd (Computable.pair
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))) (tail.comp Computable.fst))
    have expanded : Computable fun input : (State × Task) × ℕ =>
        expand calls input.2 input.1.2.2.2 input.1.1.1.tail :=
      Computable.comp (f := fun triple : ℕ × ℕ × List Task => expand calls triple.1 triple.2.1 triple.2.2)
        (g := fun input : (State × Task) × ℕ => (input.2, input.1.2.2.2, input.1.1.1.tail))
        (expand_computable hCalls) arguments
    exact Computable.comp (f := (Sum.inr : State → ℕ ⊕ State))
      (g := fun input : (State × Task) × ℕ => (expand calls input.2 input.1.2.2.2 input.1.1.1.tail, input.1.1.2))
      inr (Computable.pair expanded (values.comp Computable.fst))
  have collected : Computable fun input : State × Task =>
      (Sum.inr (input.1.1.tail, collect calls combine input.2.2.1 input.2.2.2 input.1.2) : ℕ ⊕ State) :=
    inr.comp (Computable.pair tail ((collect_computable hCalls hCombine).comp (Computable.pair
      (Computable.fst.comp (Computable.snd.comp Computable.snd))
      (Computable.pair (Computable.snd.comp (Computable.snd.comp Computable.snd)) values))))
  have evaluated : Computable fun input : State × Task =>
      (Nat.casesOn (motive := fun _ => ℕ ⊕ State) input.2.2.1 (.inr (input.1.1.tail, base input.2.2.2 :: input.1.2))
        fun k => .inr (expand calls k input.2.2.2 input.1.1.tail, input.1.2) : ℕ ⊕ State) :=
    Computable.nat_casesOn (Computable.fst.comp (Computable.snd.comp Computable.snd)) evaluateZero evaluateSucc
  have performs : Computable fun input : State × Task => perform base calls combine input.1 input.2 :=
    (Computable.cond (Computable.fst.comp Computable.snd) evaluated collected).of_eq fun _ => rfl
  have stepped := Computable.option_casesOn (Primrec.list_head?.to_comp.comp Computable.fst)
    (Computable.sumInl.comp (Primrec.list_headI.to_comp.comp Computable.snd)) performs
  exact stepped.of_eq fun _ => rfl

/-- **Recursion within a fuel is computable** when its base, its calls and its combination are. -/
theorem run_computable (hBase : Computable base) (hCalls : Computable₂ calls)
    (hCombine : Computable fun input : ℕ × ℕ × List ℕ => combine input.1 input.2.1 input.2.2) :
    Computable₂ (run base calls combine) := by
  have fixed : Partrec (machine base calls combine).fix :=
    Partrec.fix (step_computable hBase hCalls hCombine)
  have initial : Computable fun input : ℕ × ℕ => (([(true, input.1, input.2)], []) : State) :=
    Computable.pair ((Primrec.list_cons.to_comp).comp
      (Computable.pair (Computable.const true) (Computable.pair Computable.fst Computable.snd))
      (Computable.const []))
      (Computable.const [])
  exact (fixed.comp initial).of_eq fun input => fix_run base calls combine input.1 input.2

end Computability


/-! ## Recursion within a fuel, in rounds

A function may need values of its own recursion that depend on values it has already received: a normalization that
absorbs copies one at a time looks for the next copy among what is left after the last. `talk` allows this. Within the
fuel `k + 1`, the argument `x` holds a dialogue of `rounds k x` rounds: each round asks for the values within the fuel
`k` of the arguments `ask k x answers` computes from the answers of the rounds so far, and at the end
`finish k x answers` gives the value. When the base, the number of rounds, the questions and the finish are
computable, so is `talk` (`talk_computable`). The machine keeps, for each dialogue under way, a task that resumes it
once the values of its last round are on the value stack.
-/

namespace Rounds

variable (base : ℕ → ℕ) (rounds : ℕ → ℕ → ℕ) (ask : ℕ → ℕ → List (List ℕ) → List ℕ)
  (finish : ℕ → ℕ → List (List ℕ) → ℕ)

/-- The rest of a dialogue within the fuel `k + 1`, with `r` rounds left and the answers of the rounds so far, the
values within the fuel `k` given by `value`. -/
def converse (value : ℕ → ℕ) (k x : ℕ) : ℕ → List (List ℕ) → ℕ
  | 0, answers => finish k x answers
  | r + 1, answers => converse value k x r (answers ++ [(ask k x answers).map value])

/-- **The recursion within a fuel, in rounds.** -/
def talk : ℕ → ℕ → ℕ
  | 0, x => base x
  | k + 1, x => converse ask finish (talk k) k x (rounds k x) []

@[simp] theorem talk_zero (x : ℕ) : talk base rounds ask finish 0 x = base x := rfl

theorem talk_succ (k x : ℕ) :
    talk base rounds ask finish (k + 1) x =
      converse ask finish (talk base rounds ask finish k) k x (rounds k x) [] := rfl

/-- A task: `inl (k, x)` evaluates `x` within the fuel `k`; `inr (k, x, r, answers, pending)` resumes the dialogue of
`x` within the fuel `k + 1`, with `r` rounds left after the round whose `pending` values are on the stack. -/
abbrev Task := (ℕ × ℕ) ⊕ (ℕ × ℕ × ℕ × List (List ℕ) × ℕ)

/-- A state of the machine: the tasks to do, and the values computed. -/
abbrev State := List Task × List ℕ

/-- The answers of a dialogue once the values of its last round are taken off the stack. -/
def received (values : List ℕ) (answers : List (List ℕ)) (pending : ℕ) : List (List ℕ) :=
  answers ++ [(values.take pending).reverse]

/-- Finish a dialogue. -/
def ending (tasks : List Task) (values : List ℕ) (k x : ℕ) (answers : List (List ℕ)) : ℕ ⊕ State :=
  .inr (tasks, finish k x answers :: values)

/-- Ask the next round of a dialogue, which then has `r` rounds left. -/
def asking (tasks : List Task) (values : List ℕ) (k x : ℕ) (answers : List (List ℕ)) (r : ℕ) : ℕ ⊕ State :=
  .inr ((ask k x answers).map (fun question => .inl (k, question)) ++
    .inr (k, x, r, answers, (ask k x answers).length) :: tasks, values)

/-- Resume a dialogue: take the values of its last round, then finish it or ask the next round. -/
def resume (tasks : List Task) (values : List ℕ) (k x r : ℕ) (answers : List (List ℕ)) (pending : ℕ) :
    ℕ ⊕ State :=
  Nat.casesOn (motive := fun _ => ℕ ⊕ State) r
    (ending finish tasks (values.drop pending) k x (received values answers pending))
    fun r' => asking ask tasks (values.drop pending) k x (received values answers pending) r'

/-- Start evaluating `x` within the fuel `k`. -/
def evaluating (tasks : List Task) (values : List ℕ) (k x : ℕ) : ℕ ⊕ State :=
  Nat.casesOn (motive := fun _ => ℕ ⊕ State) k (.inr (tasks, base x :: values))
    fun k' => Nat.casesOn (motive := fun _ => ℕ ⊕ State) (rounds k' x) (ending finish tasks values k' x [])
      fun r' => asking ask tasks values k' x [] r'

/-- Carry out the task on top of the state. -/
def perform (state : State) (task : Task) : ℕ ⊕ State :=
  Sum.casesOn (motive := fun _ => ℕ ⊕ State) task
    (fun evaluate => evaluating base rounds ask finish state.1.tail state.2 evaluate.1 evaluate.2)
    fun dialogue => resume ask finish state.1.tail state.2 dialogue.1 dialogue.2.1 dialogue.2.2.1
      dialogue.2.2.2.1 dialogue.2.2.2.2

/-- **One step of the machine**: with no task left, the value on top is the result. -/
def step (state : State) : ℕ ⊕ State :=
  Option.casesOn (motive := fun _ => ℕ ⊕ State) state.1.head? (.inl state.2.headI)
    (perform base rounds ask finish state)

/-- The machine as a partial function. -/
def machine : State →. ℕ ⊕ State := fun state => Part.some (step base rounds ask finish state)

theorem fix_forward {state next : State} (stepped : step base rounds ask finish state = .inr next) :
    (machine base rounds ask finish).fix state = (machine base rounds ask finish).fix next :=
  PFun.fix_fwd_eq (by simp [machine, stepped])

/-- Tasks that evaluate a list of arguments leave their values on the value stack, the last on top. -/
theorem fix_evaluate_all (k : ℕ)
    (evaluate : ∀ (x : ℕ) (tasks : List Task) (values : List ℕ),
      (machine base rounds ask finish).fix (.inl (k, x) :: tasks, values) =
        (machine base rounds ask finish).fix (tasks, talk base rounds ask finish k x :: values)) :
    ∀ (arguments : List ℕ) (tasks : List Task) (values : List ℕ),
      (machine base rounds ask finish).fix (arguments.map (fun argument => .inl (k, argument)) ++ tasks, values) =
        (machine base rounds ask finish).fix
          (tasks, (arguments.map (talk base rounds ask finish k)).reverse ++ values)
  | [], tasks, values => by simp
  | argument :: rest, tasks, values => by
      simp only [List.map_cons, List.cons_append]
      rw [evaluate, fix_evaluate_all k evaluate rest]
      simp [List.reverse_cons, List.append_assoc]

/-- A round asked of a dialogue runs the dialogue to its end. -/
theorem fix_asked (k x : ℕ)
    (evaluate : ∀ (x : ℕ) (tasks : List Task) (values : List ℕ),
      (machine base rounds ask finish).fix (.inl (k, x) :: tasks, values) =
        (machine base rounds ask finish).fix (tasks, talk base rounds ask finish k x :: values)) :
    ∀ (r : ℕ) (answers : List (List ℕ)) (tasks : List Task) (values : List ℕ),
      (machine base rounds ask finish).fix ((ask k x answers).map (fun question => .inl (k, question)) ++
          .inr (k, x, r, answers, (ask k x answers).length) :: tasks, values) =
        (machine base rounds ask finish).fix
          (tasks, converse ask finish (talk base rounds ask finish k) k x (r + 1) answers :: values)
  | r, answers, tasks, values => by
      rw [fix_evaluate_all base rounds ask finish k evaluate]
      have length : ((ask k x answers).map (talk base rounds ask finish k)).reverse.length =
          (ask k x answers).length := by simp
      cases r with
      | zero =>
          rw [fix_forward base rounds ask finish (next := (tasks, finish k x
            (answers ++ [(ask k x answers).map (talk base rounds ask finish k)]) :: values))
            (by simp [step, perform, resume, ending, received, List.take_left' length, List.drop_left' length])]
          rfl
      | succ r =>
          rw [fix_forward base rounds ask finish
            (next := ((ask k x (answers ++ [(ask k x answers).map (talk base rounds ask finish k)])).map
                (fun question => .inl (k, question)) ++
              .inr (k, x, r, answers ++ [(ask k x answers).map (talk base rounds ask finish k)],
                (ask k x (answers ++ [(ask k x answers).map (talk base rounds ask finish k)])).length) :: tasks,
              values))
            (by simp [step, perform, resume, asking, received, List.take_left' length, List.drop_left' length])]
          rw [fix_asked k x evaluate r]
          rfl

/-- **A task that evaluates leaves the value of the recursion.** -/
theorem fix_evaluate : ∀ (k x : ℕ) (tasks : List Task) (values : List ℕ),
    (machine base rounds ask finish).fix (.inl (k, x) :: tasks, values) =
      (machine base rounds ask finish).fix (tasks, talk base rounds ask finish k x :: values)
  | 0, x, tasks, values => fix_forward base rounds ask finish rfl
  | k + 1, x, tasks, values => by
      rw [talk_succ]
      cases count : rounds k x with
      | zero =>
          rw [fix_forward base rounds ask finish (next := (tasks, finish k x [] :: values))
            (by simp [step, perform, evaluating, ending, count])]
          rfl
      | succ r =>
          rw [fix_forward base rounds ask finish (next := ((ask k x []).map (fun question => .inl (k, question)) ++
              .inr (k, x, r, [], (ask k x []).length) :: tasks, values))
            (by simp [step, perform, evaluating, asking, count])]
          exact fix_asked base rounds ask finish k x (fix_evaluate k) r [] tasks values

/-- **The machine computes the recursion.** -/
theorem fix_talk (k x : ℕ) :
    (machine base rounds ask finish).fix ([.inl (k, x)], []) = Part.some (talk base rounds ask finish k x) := by
  rw [fix_evaluate]
  exact Part.eq_some_iff.mpr (PFun.fix_stop (by simp [machine, step]))

section Computability

variable {base rounds ask finish}

/-- The tuple a dialogue is resumed from: tasks, values, fuel, argument, rounds left, answers, pending values. -/
abbrev Resumption := List Task × List ℕ × ℕ × ℕ × ℕ × List (List ℕ) × ℕ

/-- The tuple a dialogue is asked or finished from: tasks, values, fuel, argument, answers. -/
abbrev Turn := List Task × List ℕ × ℕ × ℕ × List (List ℕ)

theorem ending_computable
    (hFinish : Computable fun input : ℕ × ℕ × List (List ℕ) => finish input.1 input.2.1 input.2.2) :
    Computable fun input : Turn => ending finish input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2 := by
  have value := Computable.comp (f := fun triple : ℕ × ℕ × List (List ℕ) => finish triple.1 triple.2.1 triple.2.2)
    (g := fun input : Turn => (input.2.2.1, input.2.2.2.1, input.2.2.2.2)) hFinish
    (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.snd))
      (Computable.pair (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
        (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))))
  exact Computable.sumInr.comp (Computable.pair Computable.fst ((Primrec.list_cons.to_comp).comp value
    (Computable.fst.comp Computable.snd)))

theorem asking_computable
    (hAsk : Computable fun input : ℕ × ℕ × List (List ℕ) => ask input.1 input.2.1 input.2.2) :
    Computable fun input : Turn × ℕ =>
      asking ask input.1.1 input.1.2.1 input.1.2.2.1 input.1.2.2.2.1 input.1.2.2.2.2 input.2 := by
  have kOf : Computable fun input : Turn × ℕ => input.1.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have xOf : Computable fun input : Turn × ℕ => input.1.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  have answers : Computable fun input : Turn × ℕ => input.1.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  have questions := Computable.comp (f := fun triple : ℕ × ℕ × List (List ℕ) => ask triple.1 triple.2.1 triple.2.2)
    (g := fun input : Turn × ℕ => (input.1.2.2.1, input.1.2.2.2.1, input.1.2.2.2.2))
    hAsk (Computable.pair kOf (Computable.pair xOf answers))
  have tagged : Primrec fun pair : List ℕ × ℕ => pair.1.map fun question => (.inl (pair.2, question) : Task) :=
    Primrec.list_map Primrec.fst (Primrec.sumInl.comp (Primrec.pair (Primrec.snd.comp Primrec.fst)
      Primrec.snd)).to₂
  have evaluations := Computable.comp
    (f := fun pair : List ℕ × ℕ => pair.1.map fun question => (.inl (pair.2, question) : Task))
    (g := fun input : Turn × ℕ => (ask input.1.2.2.1 input.1.2.2.2.1 input.1.2.2.2.2, input.1.2.2.1))
    tagged.to_comp (Computable.pair questions kOf)
  have resumed : Computable fun input : Turn × ℕ =>
      (.inr (input.1.2.2.1, input.1.2.2.2.1, input.2, input.1.2.2.2.2,
        (ask input.1.2.2.1 input.1.2.2.2.1 input.1.2.2.2.2).length) : Task) :=
    Computable.sumInr.comp (Computable.pair kOf (Computable.pair xOf (Computable.pair Computable.snd
      (Computable.pair answers (Primrec.list_length.to_comp.comp questions)))))
  exact Computable.sumInr.comp (Computable.pair ((Primrec.list_append.to_comp).comp evaluations
    ((Primrec.list_cons.to_comp).comp resumed (Computable.fst.comp Computable.fst)))
    (Computable.fst.comp (Computable.snd.comp Computable.fst)))

theorem resume_computable
    (hAsk : Computable fun input : ℕ × ℕ × List (List ℕ) => ask input.1 input.2.1 input.2.2)
    (hFinish : Computable fun input : ℕ × ℕ × List (List ℕ) => finish input.1 input.2.1 input.2.2) :
    Computable fun input : Resumption =>
      resume ask finish input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2.1 input.2.2.2.2.2.1
        input.2.2.2.2.2.2 := by
  have values : Computable fun input : Resumption => input.2.1 := Computable.fst.comp Computable.snd
  have pending : Computable fun input : Resumption => input.2.2.2.2.2.2 :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      Computable.snd))))
  have answers : Computable fun input : Resumption => input.2.2.2.2.2.1 :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      Computable.snd))))
  have receivedOf : Computable fun input : Resumption => received input.2.1 input.2.2.2.2.2.1 input.2.2.2.2.2.2 :=
    (Primrec.list_concat.to_comp).comp answers
      (Primrec.list_reverse.to_comp.comp ((Primrec.list_take.to_comp).comp pending values))
  have turn : Computable fun input : Resumption =>
      ((input.1, input.2.1.drop input.2.2.2.2.2.2, input.2.2.1, input.2.2.2.1,
        received input.2.1 input.2.2.2.2.2.1 input.2.2.2.2.2.2) : Turn) :=
    Computable.pair Computable.fst (Computable.pair ((Primrec.list_drop.to_comp).comp pending values)
      (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.snd))
        (Computable.pair (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
          receivedOf)))
  have ended := Computable.comp (f := fun input : Turn =>
      ending finish input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2)
    (g := fun input : Resumption => ((input.1, input.2.1.drop input.2.2.2.2.2.2, input.2.2.1, input.2.2.2.1,
      received input.2.1 input.2.2.2.2.2.1 input.2.2.2.2.2.2) : Turn)) (ending_computable hFinish) turn
  have asked := Computable.comp (f := fun input : Turn × ℕ =>
      asking ask input.1.1 input.1.2.1 input.1.2.2.1 input.1.2.2.2.1 input.1.2.2.2.2 input.2)
    (g := fun input : Resumption × ℕ => (((input.1.1, input.1.2.1.drop input.1.2.2.2.2.2.2, input.1.2.2.1,
      input.1.2.2.2.1, received input.1.2.1 input.1.2.2.2.2.2.1 input.1.2.2.2.2.2.2) : Turn), input.2))
    (asking_computable hAsk) (Computable.pair (turn.comp Computable.fst) Computable.snd)
  exact Computable.nat_casesOn (f := fun input : Resumption => input.2.2.2.2.1)
    (g := fun input : Resumption => ending finish input.1 (input.2.1.drop input.2.2.2.2.2.2) input.2.2.1
      input.2.2.2.1 (received input.2.1 input.2.2.2.2.2.1 input.2.2.2.2.2.2))
    (h := fun (input : Resumption) (r : ℕ) => asking ask input.1 (input.2.1.drop input.2.2.2.2.2.2) input.2.2.1
      input.2.2.2.1 (received input.2.1 input.2.2.2.2.2.1 input.2.2.2.2.2.2) r)
    (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))))
    ended asked

theorem evaluating_computable (hBase : Computable base) (hRounds : Computable₂ rounds)
    (hAsk : Computable fun input : ℕ × ℕ × List (List ℕ) => ask input.1 input.2.1 input.2.2)
    (hFinish : Computable fun input : ℕ × ℕ × List (List ℕ) => finish input.1 input.2.1 input.2.2) :
    Computable fun input : List Task × List ℕ × ℕ × ℕ =>
      evaluating base rounds ask finish input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  have atZero : Computable fun input : List Task × List ℕ × ℕ × ℕ =>
      (.inr (input.1, base input.2.2.2 :: input.2.1) : ℕ ⊕ State) :=
    Computable.sumInr.comp (Computable.pair Computable.fst ((Primrec.list_cons.to_comp).comp
      (hBase.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))) (Computable.fst.comp Computable.snd)))
  have turn : Computable fun input : (List Task × List ℕ × ℕ × ℕ) × ℕ =>
      ((input.1.1, input.1.2.1, input.2, input.1.2.2.2, []) : Turn) :=
    Computable.pair (Computable.fst.comp Computable.fst) (Computable.pair
      (Computable.fst.comp (Computable.snd.comp Computable.fst)) (Computable.pair Computable.snd
        (Computable.pair (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
          (Computable.const []))))
  have ended := Computable.comp (f := fun input : Turn =>
      ending finish input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2)
    (g := fun input : (List Task × List ℕ × ℕ × ℕ) × ℕ => ((input.1.1, input.1.2.1, input.2, input.1.2.2.2, []) :
      Turn)) (ending_computable hFinish) turn
  have asked := Computable.comp (f := fun input : Turn × ℕ =>
      asking ask input.1.1 input.1.2.1 input.1.2.2.1 input.1.2.2.2.1 input.1.2.2.2.2 input.2)
    (g := fun input : ((List Task × List ℕ × ℕ × ℕ) × ℕ) × ℕ =>
      (((input.1.1.1, input.1.1.2.1, input.1.2, input.1.1.2.2.2, []) : Turn), input.2))
    (asking_computable hAsk) (Computable.pair (turn.comp Computable.fst) Computable.snd)
  have roundsOf := Computable.comp (f := fun pair : ℕ × ℕ => rounds pair.1 pair.2)
    (g := fun input : (List Task × List ℕ × ℕ × ℕ) × ℕ => (input.2, input.1.2.2.2)) hRounds
    (Computable.pair Computable.snd (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))))
  have atSucc := Computable.nat_casesOn (f := fun input : (List Task × List ℕ × ℕ × ℕ) × ℕ =>
      rounds input.2 input.1.2.2.2)
    (g := fun input => ending finish input.1.1 input.1.2.1 input.2 input.1.2.2.2 [])
    (h := fun input r => asking ask input.1.1 input.1.2.1 input.2 input.1.2.2.2 [] r) roundsOf ended asked
  exact Computable.nat_casesOn (f := fun input : List Task × List ℕ × ℕ × ℕ => input.2.2.1)
    (g := fun input : List Task × List ℕ × ℕ × ℕ => (.inr (input.1, base input.2.2.2 :: input.2.1) : ℕ ⊕ State))
    (h := fun (input : List Task × List ℕ × ℕ × ℕ) (k : ℕ) =>
      Nat.casesOn (motive := fun _ => ℕ ⊕ State) (rounds k input.2.2.2)
        (ending finish input.1 input.2.1 k input.2.2.2 []) fun r => asking ask input.1 input.2.1 k input.2.2.2 [] r)
    (Computable.fst.comp (Computable.snd.comp Computable.snd)) atZero atSucc

theorem step_computable (hBase : Computable base) (hRounds : Computable₂ rounds)
    (hAsk : Computable fun input : ℕ × ℕ × List (List ℕ) => ask input.1 input.2.1 input.2.2)
    (hFinish : Computable fun input : ℕ × ℕ × List (List ℕ) => finish input.1 input.2.1 input.2.2) :
    Computable (step base rounds ask finish) := by
  have tail : Computable fun input : State × Task => input.1.1.tail :=
    Primrec.list_tail.to_comp.comp (Computable.fst.comp Computable.fst)
  have values : Computable fun input : State × Task => input.1.2 := Computable.snd.comp Computable.fst
  have evaluated := Computable.comp
    (f := fun input : List Task × List ℕ × ℕ × ℕ =>
      evaluating base rounds ask finish input.1 input.2.1 input.2.2.1 input.2.2.2)
    (g := fun input : (State × Task) × ℕ × ℕ => (input.1.1.1.tail, input.1.1.2, input.2.1, input.2.2))
    (evaluating_computable hBase hRounds hAsk hFinish)
    (Computable.pair (tail.comp Computable.fst) (Computable.pair (values.comp Computable.fst) Computable.snd))
  have resumed := Computable.comp
    (f := fun input : Resumption => resume ask finish input.1 input.2.1 input.2.2.1 input.2.2.2.1 input.2.2.2.2.1
      input.2.2.2.2.2.1 input.2.2.2.2.2.2)
    (g := fun input : (State × Task) × ℕ × ℕ × ℕ × List (List ℕ) × ℕ => (input.1.1.1.tail, input.1.1.2, input.2))
    (resume_computable hAsk hFinish)
    (Computable.pair (tail.comp Computable.fst) (Computable.pair (values.comp Computable.fst) Computable.snd))
  have performs := Computable.sumCasesOn (f := fun input : State × Task => input.2)
    (g := fun (input : State × Task) (evaluate : ℕ × ℕ) =>
      evaluating base rounds ask finish input.1.1.tail input.1.2 evaluate.1 evaluate.2)
    (h := fun (input : State × Task) (dialogue : ℕ × ℕ × ℕ × List (List ℕ) × ℕ) =>
      resume ask finish input.1.1.tail input.1.2 dialogue.1 dialogue.2.1 dialogue.2.2.1 dialogue.2.2.2.1
        dialogue.2.2.2.2)
    Computable.snd evaluated resumed
  have stepped := Computable.option_casesOn (o := fun state : State => state.1.head?)
    (f := fun state : State => (.inl state.2.headI : ℕ ⊕ State))
    (g := fun (state : State) (task : Task) => perform base rounds ask finish state task)
    (Primrec.list_head?.to_comp.comp Computable.fst)
    (Computable.sumInl.comp (Primrec.list_headI.to_comp.comp Computable.snd))
    (performs.of_eq fun _ => rfl)
  exact stepped.of_eq fun _ => rfl

/-- **Recursion within a fuel, in rounds, is computable** when its base, its number of rounds, its questions and its
finish are. -/
theorem talk_computable (hBase : Computable base) (hRounds : Computable₂ rounds)
    (hAsk : Computable fun input : ℕ × ℕ × List (List ℕ) => ask input.1 input.2.1 input.2.2)
    (hFinish : Computable fun input : ℕ × ℕ × List (List ℕ) => finish input.1 input.2.1 input.2.2) :
    Computable₂ (talk base rounds ask finish) := by
  have fixed : Partrec (machine base rounds ask finish).fix :=
    Partrec.fix (step_computable hBase hRounds hAsk hFinish)
  have initial : Computable fun input : ℕ × ℕ => (([.inl (input.1, input.2)], []) : State) :=
    Computable.pair ((Primrec.list_cons.to_comp).comp
      (Computable.sumInl.comp (Computable.pair Computable.fst Computable.snd)) (Computable.const []))
      (Computable.const [])
  exact (fixed.comp initial).of_eq fun input => fix_talk base rounds ask finish input.1 input.2

end Computability

end Rounds

end Mettapedia.Computability.FuelRecursion
