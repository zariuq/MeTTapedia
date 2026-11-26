import Mettapedia.Machines.TIsa.Derivation.Machine

/-!
# The instruction set of the transform calculus

The instruction set is read off the transitions of the abstract machine (`Derivation.step`). The
machine's control component is the rule's code (its goals), the scan of a premise, a success
continuation, a choice point, or the publication of a firing; each transition executes the
instruction that component names (`Config.current`). Fourteen instructions cover the eighteen
transitions:

| instruction | transition |
|---|---|
| `search` | start the program's search at the store |
| `tryRule` | enter the next rule with the empty match; the other rules become a choice point |
| `premise role pattern` | open a choice point over the store's occurrences |
| `candidate` | try the next occurrence: if allowed and matched, extend the match, keep the rest of the scan as the newest choice point and resume the success continuation; otherwise drop it |
| `determinate goal` | a tell, a check, a collect pattern or a produced term: continue, or fail |
| `proceed` | the code is done: apply the continuation (success, or the rest of the publication) |
| `resume` | continue the rule's code after a matched premise |
| `fail` | nothing is left to try here: go to the newest choice point |
| `retry` | resume the newest choice point: the rest of a scan, or the rest of the rules |
| `quiesce` | no choice point is left: the run ends quiescent |
| `fund` | pay one unit for the firing and commit, discarding every choice point; with no allowance left, the run ends exhausted |
| `take` | remove a taken occurrence |
| `make` | add a made value under the next fresh identity |
| `restart` | schedule the next search on the published store |

`execute` gives each instruction its execution semantics on configurations, and the machine is
exactly the loop that executes the current instruction (`step_eq_execute`). Only `take` and `make`
change the store, and only `fund` changes the allowance (`store_changes`, `allowance_changes`).
The symbolic controller adds `checkSolution` for testing a principal solution and `publish` for
installing its residual equations and entire occurrence delta together.

## What t-ISA p1 already has

`Machines/TIsa/StoreInstructions` extends t-ISA's semantics with the instructions it lacks and proves the firing
loop's simulation. Against p1 (`TIsa/SEMANTICS.txt`):

* **in p1**: the choice point of a premise and its `candidate`/`retry` are `EARLY_EXIT_LOOP` over the
  store's indices; `proceed` and `resume` are the loop body's nesting; `fail` is the loop's latch;
  `tryRule` and the rule-level `retry` are `SEQ` of rule blocks guarded by `IF`; `fund` is `FUND`,
  with `EXHAUSTED` when the allowance ends first; `quiesce` is `RETURN REFUSED`; commit is a
  Boolean continuation register cleared by `IMM` and `RETURN FIRED`; `restart` is the caller's next
  leaf invocation (one firing per invocation, as the t-ISA cost model counts source steps);
* **added**: the store and its size (`SIZE`), matching a premise against an occurrence (`MATCH`),
  determinate goals over bindings and the store (`TEST`), opening a rule's match (`OPEN`), and
  publication (`TAKE`, `MAKE`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation

universe u v w

/-- **The instructions of the transform calculus' abstract machine.** -/
inductive Instruction (T : Type u) where
  | search
  | tryRule
  | premise (role : Role) (pattern : T)
  | candidate
  | determinate (goal : Determinate T)
  | proceed
  | resume
  | fail
  | retry
  | quiesce
  | fund
  | take
  | make
  | restart
  | checkSolution
  | publish

variable {T : Type u} {V : Type v} {B : Type w}

/-- **The instruction a configuration executes next.** -/
def Config.current : Config T V B → Option (Instruction T)
  | .run .. => some .search
  | .rules _ _ [] _ => some .fail
  | .rules _ _ (_ :: _) _ => some .tryRule
  | .solve _ _ [] .. => some .proceed
  | .solve _ _ (.premise role pattern :: _) .. => some (.premise role pattern)
  | .solve _ _ (.determinate d :: _) .. => some (.determinate d)
  | .scan _ _ _ _ _ [] .. => some .fail
  | .scan _ _ _ _ _ (_ :: _) .. => some .candidate
  | .succeed _ _ (.goals ..) .. => some .resume
  | .succeed _ _ .fire .. => some .fund
  | .fail _ _ (.scan ..) => some .retry
  | .fail _ _ (.rules ..) => some .retry
  | .fail _ _ .quiescent => some .quiesce
  | .taking _ _ (_ :: _) _ => some .take
  | .taking _ _ [] _ => some .proceed
  | .making _ _ (_ :: _) => some .make
  | .making _ _ [] => some .restart
  | .halt _ => none

variable [DecidableEq V] (M : Matcher T V B) (P : List (Rule T))

/-- **The execution semantics of the instructions.** An instruction executes at a configuration
whose control component is of its kind, with the instruction's own operands, and is undefined
elsewhere. -/
def Instruction.execute : Instruction T → Config T V B → Option (Config T V B)
  | .search, .run a s => some (.rules a s P .quiescent)
  | .tryRule, .rules a s (r :: rs) fk => some (.solve a s (goals r) (Match.start M) .fire (.rules rs fk))
  | .premise role pattern, .solve a s (.premise _ _ :: gs) m sk fk =>
      some (.scan a s role pattern (.goals gs sk) s.occurrences m fk)
  | .candidate, .scan a s role pattern next (x :: rest) m fk =>
      match attempt M role pattern m x with
      | some m' => some (.succeed a s next m' (.scan role pattern next rest m fk))
      | none => some (.scan a s role pattern next rest m fk)
  | .determinate d, .solve a s (.determinate _ :: gs) m sk fk =>
      match d.apply M s m with
      | some m' => some (.solve a s gs m' sk fk)
      | none => some (.fail a s fk)
  | .proceed, .solve a s [] m sk fk => some (.succeed a s sk m fk)
  | .proceed, .taking a s [] ws => some (.making a s ws)
  | .resume, .succeed a s (.goals gs next) m fk => some (.solve a s gs m next fk)
  | .fail, .rules a s [] fk => some (.fail a s fk)
  | .fail, .scan a s _ _ _ [] _ fk => some (.fail a s fk)
  | .retry, .fail a s (.scan role pattern next rest m fk) => some (.scan a s role pattern next rest m fk)
  | .retry, .fail a s (.rules rs fk) => some (.rules a s rs fk)
  | .quiesce, .fail _ s .quiescent => some (.halt (.quiescent s))
  | .fund, .succeed 0 s .fire _ _ => some (.halt (.exhausted s))
  | .fund, .succeed (a + 1) s .fire m _ => some (.taking a s m.taken m.made)
  | .take, .taking a s (o :: os) ws => some (.taking a (s.remove o) os ws)
  | .make, .making a s (w :: ws) => some (.making a (s.add w) ws)
  | .restart, .making a s [] => some (.run a s)
  | _, _ => none

/-- **The machine executes the current instruction.** -/
theorem step_eq_execute (c : Config T V B) :
    step M P c = c.current.bind fun i => i.execute M P c := by
  cases c with
  | run a s => rfl
  | rules a s rs fk => cases rs <;> rfl
  | solve a s gs m sk fk =>
      cases gs with
      | nil => rfl
      | cons g gs =>
          cases g with
          | premise role pattern => rfl
          | determinate d => rfl
  | scan a s role pattern next cands m fk => cases cands <;> rfl
  | succeed a s sk m fk =>
      cases sk with
      | goals gs next => rfl
      | fire => cases a <;> rfl
  | fail a s fk => cases fk <;> rfl
  | taking a s os ws => cases os <;> rfl
  | making a s ws => cases ws <;> rfl
  | halt o => rfl

/-- The store of a configuration. -/
def Config.store : Config T V B → Option (Store V)
  | .run _ s | .rules _ s .. | .solve _ s .. | .scan _ s .. | .succeed _ s .. | .fail _ s _
  | .taking _ s .. | .making _ s _ => some s
  | .halt _ => none

/-- The allowance of a configuration. -/
def Config.allowance : Config T V B → Option ℕ
  | .run a _ | .rules a .. | .solve a .. | .scan a .. | .succeed a .. | .fail a .. | .taking a ..
  | .making a .. => some a
  | .halt _ => none

/-- **Only `take` and `make` change the store.** -/
theorem store_changes {c c' : Config T V B} (stepped : step M P c = some c')
    (running : c'.store.isSome) (changed : c'.store ≠ c.store) :
    c.current = some .take ∨ c.current = some .make := by
  cases c with
  | run a s => cases stepped; simp_all [Config.store]
  | rules a s rs fk => cases rs <;> (cases stepped; simp_all [Config.store])
  | solve a s gs m sk fk =>
      cases gs with
      | nil => cases stepped; simp_all [Config.store]
      | cons g gs =>
          cases g with
          | premise role pattern => cases stepped; simp_all [Config.store]
          | determinate d =>
              simp only [step] at stepped
              split at stepped <;> (cases stepped; simp_all [Config.store])
  | scan a s role pattern next cands m fk =>
      cases cands with
      | nil => cases stepped; simp_all [Config.store]
      | cons x rest =>
          simp only [step] at stepped
          split at stepped <;> (cases stepped; simp_all [Config.store])
  | succeed a s sk m fk =>
      cases sk with
      | goals gs next => cases stepped; simp_all [Config.store]
      | fire => cases a <;> (cases stepped; simp_all [Config.store])
  | fail a s fk => cases fk <;> (cases stepped; simp_all [Config.store])
  | taking a s os ws =>
      cases os with
      | nil => cases stepped; simp_all [Config.store]
      | cons o os => exact Or.inl rfl
  | making a s ws =>
      cases ws with
      | nil => cases stepped; simp_all [Config.store]
      | cons w ws => exact Or.inr rfl
  | halt o => cases stepped

/-- **Only `fund` changes the allowance**, by paying one unit. -/
theorem allowance_changes {c c' : Config T V B} (stepped : step M P c = some c')
    (running : c'.allowance.isSome) (changed : c'.allowance ≠ c.allowance) :
    c.current = some .fund ∧ ∃ a, c.allowance = some (a + 1) ∧ c'.allowance = some a := by
  cases c with
  | run a s => cases stepped; simp_all [Config.allowance]
  | rules a s rs fk => cases rs <;> (cases stepped; simp_all [Config.allowance])
  | solve a s gs m sk fk =>
      cases gs with
      | nil => cases stepped; simp_all [Config.allowance]
      | cons g gs =>
          cases g with
          | premise role pattern => cases stepped; simp_all [Config.allowance]
          | determinate d =>
              simp only [step] at stepped
              split at stepped <;> (cases stepped; simp_all [Config.allowance])
  | scan a s role pattern next cands m fk =>
      cases cands with
      | nil => cases stepped; simp_all [Config.allowance]
      | cons x rest =>
          simp only [step] at stepped
          split at stepped <;> (cases stepped; simp_all [Config.allowance])
  | succeed a s sk m fk =>
      cases sk with
      | goals gs next => cases stepped; simp_all [Config.allowance]
      | fire =>
          cases a with
          | zero => cases stepped; simp_all [Config.allowance]
          | succ a =>
              cases stepped
              exact ⟨rfl, a, rfl, rfl⟩
  | fail a s fk => cases fk <;> (cases stepped; simp_all [Config.allowance])
  | taking a s os ws => cases os <;> (cases stepped; simp_all [Config.allowance])
  | making a s ws => cases ws <;> (cases stepped; simp_all [Config.allowance])
  | halt o => cases stepped

end Mettapedia.Machines.TIsa.Derivation
