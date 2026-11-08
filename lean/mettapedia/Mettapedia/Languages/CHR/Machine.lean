import Mettapedia.Languages.CHR.Operational

/-! The refined CHR machine of `metta/gslt/lib/gslt_chr_machine.metta`,
definition by definition. One `tick` is one bounded step: finishing a goal
list, running one goal, starting or ending a rule occurrence for the active
constraint, or trying one partner candidate. The store keeps one slot per
constraint key, newest occurrence first; partners are tried in head order,
newest first, never the active constraint or an earlier pick.

This module states the machine only. Its refinement of `Step` and the
correspondence of the MeTTa source with it are separate. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

/-- A constraint key: name and arity. -/
abbrev Key := String × Nat

def Head.key (head : Head) : Key := (head.name, head.arguments.length)

/-- A stored occurrence: its identifier and argument values. -/
structure Occ where
  id : Nat
  values : List Value
  deriving Repr, DecidableEq

/-- One slot per key, each newest first. -/
abbrev Store := List (Key × List Occ)

def slot (key : Key) : Store → List Occ
  | [] => []
  | (other, occurrences) :: rest => if other = key then occurrences else slot key rest

def put (key : Key) (occurrences : List Occ) : Store → Store
  | [] => [(key, occurrences)]
  | (other, old) :: rest =>
    if other = key then (key, occurrences) :: rest else (other, old) :: put key occurrences rest

def without (id : Nat) : List Occ → List Occ
  | [] => []
  | occurrence :: rest => if occurrence.id = id then rest else occurrence :: without id rest

def alive (id : Nat) : List Occ → Bool
  | [] => false
  | occurrence :: rest => occurrence.id == id || alive id rest

/-- A rule occurrence of the program table: rule index, head index into
`kept ++ removed`, and the rule. -/
structure At where
  rule : Nat
  head : Nat
  body : Rule
  deriving Repr, DecidableEq

structure Pick where
  key : Key
  id : Nat
  deriving Repr, DecidableEq

def removePicks : List Pick → Store → Store
  | [], store => store
  | pick :: rest, store => removePicks rest (put pick.key (without pick.id (slot pick.key store)) store)

def ids (picks : List Pick) : List Nat := picks.map Pick.id

/-- One partner-search frame: the head at `index`, the heads after it, the
candidates still to try for it, and the bindings, picks and used identifiers
of the heads before it. -/
structure Frame where
  index : Nat
  heads : List Head
  candidates : List Occ
  environment : Environment
  picks : List Pick
  used : List Nat
  deriving Repr, DecidableEq

inductive Task where
  | seeds (heads : List Head)
  | goals (environment : Environment) (goals : List Goal)
  | scan (active : Nat) (key : Key) (values : List Value) (remaining : List At)
  | search (active : Nat) (key : Key) (values : List Value) (occurrence : At) (after : List At)
      (frames : List Frame)
  deriving Repr, DecidableEq

inductive Status where
  | running
  | failed
  | faulted (reason : ArithmeticFault)
  deriving Repr, DecidableEq

structure State where
  tasks : List Task
  store : Store
  history : List CHR.Key
  next : Nat
  status : Status
  /-- Seed identifiers, newest first. -/
  seeds : List Nat
  deriving Repr, DecidableEq

/-- For each key, its rule occurrences in the order of `occurrences`. -/
abbrev Table := List (Key × List At)

def occurrencesOf (key : Key) : Table → List At
  | [] => []
  | (other, occurrences) :: rest => if other = key then occurrences else occurrencesOf key rest

/-- The table the preparer emits for a program. -/
def table (program : Program) : Table :=
  let keys := (program.rules.flatMap fun rule => rule.heads.map Head.key).eraseDups
  keys.map fun key => (key, (occurrences program).filterMap fun occurrence => do
    let rule ← program.rules[occurrence.rule]?
    let head ← rule.heads[occurrence.head]?
    if Head.key head = key then some ⟨occurrence.rule, occurrence.head, rule⟩ else none)

/-! ## Matching -/

mutual
  def matchTerm : Term → Value → Environment → Option Environment
    | .value datum, value, environment => if datum = value then some environment else none
    | .var index, value, environment =>
      match lookup environment index with
      | none => some ((index, value) :: environment)
      | some bound => if bound = value then some environment else none
    | .tuple terms, .tuple fields, environment => matchTerms terms fields environment
    | .tuple _, _, _ => none
  def matchTerms : List Term → List Value → Environment → Option Environment
    | [], [], environment => some environment
    | term :: terms, value :: values, environment =>
      match matchTerm term value environment with
      | none => none
      | some bound => matchTerms terms values bound
    | _, _, _ => none
end

/-! ## Instantiation, structurally as in the MeTTa source -/

mutual
  def instantiateTerm (environment : Environment) : Term → Option Value
    | .value datum => some datum
    | .var index => lookup environment index
    | .tuple terms =>
      match instantiateTerms environment terms with
      | none => none
      | some values => some (.tuple values)
  def instantiateTerms (environment : Environment) : List Term → Option (List Value)
    | [] => some []
    | term :: rest =>
      match instantiateTerm environment term with
      | none => none
      | some value =>
        match instantiateTerms environment rest with
        | none => none
        | some values => some (value :: values)
end

mutual
  theorem instantiateTerm_eq (environment : Environment) :
      (term : Term) → instantiateTerm environment term = term.instantiate environment
    | .value datum => by simp [instantiateTerm, Term.instantiate]
    | .var index => by simp [instantiateTerm, Term.instantiate]
    | .tuple terms => by
      rw [instantiateTerm, Term.instantiate, instantiateTerms_eq environment terms]
      cases terms.mapM (Term.instantiate environment) <;> rfl
  theorem instantiateTerms_eq (environment : Environment) :
      (terms : List Term) → instantiateTerms environment terms = terms.mapM (Term.instantiate environment)
    | [] => rfl
    | term :: rest => by
      rw [instantiateTerms, instantiateTerm_eq environment term, instantiateTerms_eq environment rest]
      simp only [List.mapM_cons]
      cases term.instantiate environment <;> cases rest.mapM (Term.instantiate environment) <;> rfl
end

/-! ## Steps -/

def start (seeds : List Head) : State := ⟨[.seeds seeds], [], [], 0, .running, []⟩

/-- The candidates for one head position: only the active constraint fills
its own position; any other position draws from the slot of its key. -/
def candidates (index position active : Nat) (values : List Value) (head : Head) (store : Store) :
    List Occ :=
  if index = position then [⟨active, values⟩] else slot (Head.key head) store

/-- Introduce a constraint: give it the next identifier, store it, and
activate it before `resume`. A tell that cannot be instantiated faults with
the task list unchanged. -/
def introduce (table : Table) (head : Head) (environment : Environment) (resume : Task)
    (original tail : List Task) (state : State) (seeds : List Nat) : State :=
  match instantiateTerms environment head.arguments with
  | none => { state with tasks := original, status := .faulted (.uninstantiated (.tuple head.arguments)), seeds }
  | some values =>
    let key := Head.key head
    { state with
      tasks := .scan state.next key values (occurrencesOf key table) :: resume :: tail
      store := put key (⟨state.next, values⟩ :: slot key state.store) state.store
      next := state.next + 1
      seeds }

def goal (table : Table) (environment : Environment) (current : Goal) (goals : List Goal)
    (tail : List Task) (state : State) : State :=
  match current with
  | .tell head =>
    introduce table head environment (.goals environment goals) (.goals environment (current :: goals) :: tail)
      tail state state.seeds
  | .assign index expression =>
    match expression.eval environment with
    | .error reason => { state with status := .faulted reason }
    | .ok result =>
      match lookup environment index with
      | none => { state with tasks := .goals ((index, .integer result) :: environment) goals :: tail }
      | some old =>
        if old = .integer result then { state with tasks := .goals environment goals :: tail }
        else { state with status := .failed }
  | .fail => { state with status := .failed }

def scan (active : Nat) (key : Key) (values : List Value) (remaining : List At) (tail : List Task)
    (state : State) : State :=
  if !alive active (slot key state.store) then { state with tasks := tail }
  else
    match remaining with
    | [] => { state with tasks := tail }
    | occurrence :: after =>
      let heads := occurrence.body.kept ++ occurrence.body.removed
      match heads with
      | [] => { state with tasks := .scan active key values after :: tail }
      | first :: _ =>
        let frame : Frame := ⟨0, heads, candidates 0 occurrence.head active values first state.store, [], [], []⟩
        { state with tasks := Task.search active key values occurrence after [frame] :: tail }

/-- Commit a complete selection: remove the removed heads, record a
propagation, and run the body before the active constraint continues at the
same occurrence, unless the active constraint was removed. -/
def fire (active : Nat) (key : Key) (values : List Value) (occurrence : At) (after : List At)
    (environment : Environment) (picks : List Pick) (tail : List Task) (state : State) : State :=
  let removedPicks := picks.drop occurrence.body.kept.length
  let continuation := if active ∈ ids removedPicks then tail
    else .scan active key values (occurrence :: after) :: tail
  { state with
    tasks := .goals environment occurrence.body.body :: continuation
    store := removePicks removedPicks state.store
    history := if occurrence.body.propagation then ⟨occurrence.rule, ids picks⟩ :: state.history
      else state.history }

/-- A complete selection fires when it is fresh and its guards hold; a
faulting guard stops the run; otherwise the search continues. -/
def complete (active : Nat) (key : Key) (values : List Value) (occurrence : At) (after : List At)
    (stay : List Frame) (environment : Environment) (picks : List Pick) (tail : List Task)
    (state : State) : State :=
  let retry := { state with tasks := .search active key values occurrence after stay :: tail }
  if occurrence.body.propagation ∧ (⟨occurrence.rule, ids picks⟩ : CHR.Key) ∈ state.history then retry
  else
    match guardsEval environment occurrence.body.guards with
    | .error reason => { retry with status := .faulted reason }
    | .ok true => fire active key values occurrence after environment picks tail state
    | .ok false => retry

def search (active : Nat) (key : Key) (values : List Value) (occurrence : At) (after : List At)
    (frames : List Frame) (tail : List Task) (state : State) : State :=
  match frames with
  | [] => { state with tasks := .scan active key values after :: tail }
  | frame :: below =>
    match frame.candidates with
    | [] => { state with tasks := .search active key values occurrence after below :: tail }
    | candidate :: others =>
      let stay := { frame with candidates := others } :: below
      let retry := { state with tasks := .search active key values occurrence after stay :: tail }
      if candidate.id ∈ frame.used ∨ (frame.index ≠ occurrence.head ∧ candidate.id = active) then retry
      else
        match frame.heads with
        | [] => retry
        | head :: later =>
          match matchTerms head.arguments candidate.values frame.environment with
          | none => retry
          | some bound =>
            let chosen := frame.picks ++ [⟨Head.key head, candidate.id⟩]
            match later with
            | [] => complete active key values occurrence after stay bound chosen tail state
            | nextHead :: _ =>
              let deeper : Frame := ⟨frame.index + 1, later,
                candidates (frame.index + 1) occurrence.head active values nextHead state.store,
                bound, chosen, candidate.id :: frame.used⟩
              { state with tasks := Task.search active key values occurrence after (deeper :: stay) :: tail }

def tick (table : Table) (state : State) : State :=
  match state.status, state.tasks with
  | .running, task :: tail =>
    match task with
    | .seeds [] => { state with tasks := tail }
    | .seeds (head :: heads) =>
      introduce table head [] (.seeds heads) state.tasks tail state (state.next :: state.seeds)
    | .goals _ [] => { state with tasks := tail }
    | .goals environment (current :: goals) => goal table environment current goals tail state
    | .scan active key values remaining => scan active key values remaining tail state
    | .search active key values occurrence after frames =>
      search active key values occurrence after frames tail state
  | _, _ => state

/-- At most `budget` ticks. -/
def advance (table : Table) : Nat → State → State
  | 0, state => state
  | budget + 1, state =>
    match state.status, state.tasks with
    | .running, _ :: _ => advance table budget (tick table state)
    | _, _ => state

end Mettapedia.Languages.CHR.Machine
