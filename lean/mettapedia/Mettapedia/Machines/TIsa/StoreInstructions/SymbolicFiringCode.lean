import Mettapedia.Machines.TIsa.StoreInstructions.SymbolicTestCode
import Mettapedia.Machines.TIsa.StoreInstructions.SymbolicPublication

/-!
# The code of a selected symbolic firing

The emitted program opens a match, loads its selected occurrence
ports, records tells, resolves one equation problem, tests guards
and settles collects, then pays for and publishes the firing. The
logical decision and the published terms are derived independently
of the register execution.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.SymbolicFiringCode

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open FirstOrderLicence (certain potential)
open RuleSyntax.FirstOrderLicence (firingChecks)
open RuleSyntax.JointFirings.SymmetricMatches (ResultModel)
open Derivation (Match)
open Derivation.SymbolicFiring (Rules LiveWorld act problem inferSeen Attempt Pending Accepted
  proposeCollections evaluateInferred attempts attempts_cover_models)
open SymbolicExecution (Goal Frame Work Code enter storeOf)
open SymbolicPrepared (Prepared body entered level emitPorts)

universe u p
variable {σ : LPSignature.{u,u,p,u}} {rules : Rules σ} {before : LiveWorld σ}
local notation "Trial" => Prepared (rules := rules) (before := before)

def collectPatterns (a : Trial) : List (Term σ) := a.seed.firing.collectOpened (act σ)

def goals (a : Trial) : List (Goal σ) :=
  SymbolicTestCode.tells (body a).tell ++
    .resolve :: (SymbolicTestCode.checks (body a).checks ++
      SymbolicTestCode.collects (collectPatterns a) ++ SymbolicTestCode.makes (body a).produce)

def compile (a : Trial) : Code σ :=
  emitPorts a (SymbolicTestCode.emit (level a) (goals a)
    (SymbolicPublication.emit (level a) a.seed.firing.selection.taken.length (body a).produce.length))

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

def settled (answer : Subst σ) (pattern : Term σ) : Bool :=
  decide (potential answer before.state.label before.state.present pattern ⊆
    certain answer before.state.label before.state.present pattern)

def seen (a : Trial) (answer : Subst σ) : List (Finset ℕ) :=
  (collectPatterns a).map (certain answer before.state.label before.state.present)

def checksPass (a : Trial) (answer : Subst σ) : Bool :=
  (body a).checks.all (FirstOrderLicence.check answer before.state.label before.state.present)

def accepts (a : Trial) (answer : Subst σ) : Bool :=
  checksPass a answer && (collectPatterns a).all (settled (before := before) answer)

def beforeSolve (a : Trial) : Match (Term σ) (Work σ) :=
  SymbolicTestCode.afterTells (entered a) (body a).tell

def checked (a : Trial) (answer : Subst σ) : Match (Term σ) (Work σ) :=
  { beforeSolve a with bindings := { (beforeSolve a).bindings with answer := some answer } }

def finished (a : Trial) (answer : Subst σ) : Match (Term σ) (Work σ) :=
  { checked a answer with seen := seen a answer, made := (body a).produce }

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem beforeSolve_problem (a : Trial) :
    (beforeSolve a).bindings.problem before.state.knowledge = problem a.seed := by
  rw [beforeSolve, SymbolicTestCode.afterTells_problem, SymbolicPrepared.information]

theorem finished_fields (a : Trial) (answer : Subst σ) :
    (finished a answer).taken = a.seed.firing.selection.taken ∧
      (finished a answer).read = a.seed.firing.selection.read ∧
      (finished a answer).bindings.problem before.state.knowledge = problem a.seed ∧
      (finished a answer).bindings.answer = some answer := by
  have ports : (beforeSolve a).taken = (entered a).taken ∧ (beforeSolve a).read = (entered a).read := by
    unfold beforeSolve
    cases (body a).tell <;> exact ⟨rfl, rfl⟩
  exact ⟨ports.1.trans (SymbolicPrepared.taken_exact a), ports.2.trans (SymbolicPrepared.read_exact a),
    beforeSolve_problem a, rfl⟩

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
private theorem checked_empty (a : Trial) (answer : Subst σ) :
    (checked a answer).seen = [] ∧ (checked a answer).made = [] := by
  unfold checked beforeSolve
  have empty := SymbolicPrepared.entered_empty_outputs a
  cases (body a).tell <;> exact empty

private theorem checks_exact (a : Trial) (answer : Subst σ) :
    (body a).checks.all (SymbolicExecution.guard answer (storeOf before).occurrences) = checksPass a answer := by
  unfold checksPass
  congr 1
  funext condition
  rw [storeOf, SymbolicExecution.guard_exact answer before.state.label before.live before.distinct,
    before.visible]

private theorem collects_exact (answer : Subst σ) (patterns : List (Term σ)) :
    patterns.mapM (SymbolicExecution.collect answer (storeOf before).occurrences) =
      if patterns.all (settled (before := before) answer)
      then some (patterns.map (certain answer before.state.label before.state.present)) else none := by
  induction patterns with
  | nil => rfl
  | cons first rest ih =>
    have readFirst : SymbolicExecution.collect answer (storeOf before).occurrences first =
        if potential answer before.state.label before.state.present first ⊆
            certain answer before.state.label before.state.present first
        then some (certain answer before.state.label before.state.present first) else none := by
      rw [storeOf, SymbolicExecution.collect_exact, before.visible]
    rw [List.mapM_cons, readFirst, ih]
    by_cases stable : potential answer before.state.label before.state.present first ⊆
        certain answer before.state.label before.state.present first <;>
      cases remaining : rest.all (settled (before := before) answer) <;>
      simp [settled, stable, remaining]

theorem test_tape (a : Trial) :
    SymbolicTestCode.apply before.state.knowledge (storeOf before) (goals a) (entered a) =
      match unifyTotal (problem a.seed) with
      | none => none
      | some answer => if accepts a answer then some (finished a answer) else none := by
  rw [goals, SymbolicTestCode.apply_append, SymbolicTestCode.apply_tells, Option.bind_some]
  change (SymbolicExecution.resolve before.state.knowledge (beforeSolve a)).bind
    (SymbolicTestCode.apply before.state.knowledge (storeOf before)
      (SymbolicTestCode.checks (body a).checks ++ SymbolicTestCode.collects (collectPatterns a) ++
        SymbolicTestCode.makes (body a).produce)) = _
  rw [SymbolicExecution.resolve_exact, beforeSolve_problem]
  cases unifyTotal (problem a.seed) with
  | none => rfl
  | some answer =>
    change SymbolicTestCode.apply before.state.knowledge (storeOf before) _ (checked a answer) = _
    rw [List.append_assoc, SymbolicTestCode.apply_append,
      SymbolicTestCode.apply_checks _ _ answer _ (checked a answer) rfl, checks_exact]
    cases guardOK : checksPass a answer with
    | false => simp [accepts, guardOK]
    | true =>
      simp only [guardOK, if_true, Option.bind_some, accepts, Bool.true_and]
      rw [SymbolicTestCode.apply_append, SymbolicTestCode.apply_collects _ _ answer _ (checked a answer) rfl,
        collects_exact (before := before)]
      cases stable : (collectPatterns a).all (settled (before := before) answer) with
      | false => simp
      | true =>
        let collected := { checked a answer with seen := (checked a answer).seen ++ seen a answer }
        change SymbolicTestCode.apply before.state.knowledge (storeOf before)
          (SymbolicTestCode.makes (body a).produce) collected = some (finished a answer)
        rw [SymbolicTestCode.apply_makes _ _ answer _ collected rfl]
        obtain ⟨noSeen, noMade⟩ := checked_empty a answer
        simp [collected, finished, noSeen, noMade]

theorem seen_exact (a : Trial) (answer : Subst σ) : seen a answer = inferSeen a.seed answer := by
  unfold seen inferSeen
  rw [SymbolicPrepared.row_exact a]
  rfl

def chosen (a : Trial) (answer : Subst σ) :
    Derivation.SymbolicFiring.Selection (program := rules.program) before.state :=
  a.seed.withSeen (seen a answer) (by simp [seen, collectPatterns, RuleSyntax.Firing.collectOpened])

private theorem chosen_checks (a : Trial) (answer : Subst σ) :
    firingChecks answer before.state (chosen a answer).firing = accepts a answer := by
  change ((body a).checks.all (FirstOrderLicence.check answer (a.seed.firing.row (act σ) before.state) before.state.present) &&
      (((collectPatterns a).zip (seen a answer)).all (fun p => FirstOrderLicence.collect answer
        (a.seed.firing.row (act σ) before.state) before.state.present p.1 p.2))) = _
  rw [SymbolicPrepared.row_exact a]
  unfold accepts checksPass seen
  congr 1
  generalize collectPatterns a = patterns
  induction patterns with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.all_cons, ih]
    have headCheck :
        FirstOrderLicence.collect answer before.state.label before.state.present head
          (certain answer before.state.label before.state.present head) =
        settled (before := before) answer head := by simp [settled, FirstOrderLicence.collect]
    rw [headCheck]

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
private theorem sameClaims (a : Trial) {l r : List (Finset ℕ)} (same : l = r)
    (left : a.seed.firing.rule.collect.length = l.length)
    (right : a.seed.firing.rule.collect.length = r.length) :
    a.seed.withSeen l left = a.seed.withSeen r right := by cases same; rfl

theorem source_decision (a : Trial) :
    evaluateInferred a.seed = match unifyTotal (problem a.seed) with
      | none => none
      | some answer => if accepts a answer then some (answer, chosen a answer) else none := by
  unfold evaluateInferred
  cases solved : unifyTotal (problem a.seed) with
  | none => simp [proposeCollections, solved]
  | some answer =>
    have selected : proposeCollections a.seed = some (answer, chosen a answer) := by
      unfold proposeCollections
      rw [solved]
      change some (answer, a.seed.withSeen (inferSeen a.seed answer) _) = _
      unfold chosen
      exact congrArg (fun s => some (answer, s)) (sameClaims a (seen_exact a answer).symm _ _)
    rw [selected]
    change (if firingChecks answer before.state (chosen a answer).firing then some (answer, chosen a answer) else none) = _
    rw [chosen_checks]

/-- One complete run of a selected firing. Its acceptance is the
source's all-solutions decision. Only success with fuel changes
the occurrence store, and that success retains the source's
unresolved equations as well as their principal answer. -/
theorem run (a : Trial) (machine : P1WordExecution.State) (fits : before.live.length < 2 ^ 64) :
    let initial := enter machine before
    let result := SymbolicExecution.execute before.state.knowledge initial (compile a)
    match evaluateInferred a.seed with
    | none => ∃ after, result = .returned .refused 0 after ∧ after.store = initial.store ∧ SameFuel initial after
    | some (answer, selected) =>
      if machine.budget - machine.spent < (1 : Word) then
        ∃ after, result = .returned .exhausted ExitStatus.exhausted.word after ∧
          after.store = initial.store ∧ SameFuel initial after
      else
        ∃ (after : Frame σ) (payload : Word)
            (reserved : selected.firing.selection.made = before.reserve 0 selected.firing.selection.made.length),
          result = .returned .completed payload after ∧ after.store = storeOf (before.commit selected.firing reserved) ∧
          (after.levels (level a)).bindings.problem before.state.knowledge = problem selected ∧
          (after.levels (level a)).bindings.answer = some answer ∧ after.machine.spent = machine.spent + 1 := by
  dsimp only
  let action : Code σ := SymbolicPublication.emit (level a) a.seed.firing.selection.taken.length (body a).produce.length
  obtain ⟨pending, visible, free, starting, began⟩ := SymbolicPrepared.execute_prefix a machine fits
    (SymbolicTestCode.emit (level a) (goals a) action)
  have full : SymbolicExecution.execute before.state.knowledge (enter machine before) (compile a) =
      SymbolicExecution.execute before.state.knowledge pending (SymbolicTestCode.emit (level a) (goals a) action) := began
  have tests := SymbolicTestCode.execute_emit before.state.knowledge pending (level a) (goals a) action
  rw [visible, starting] at tests
  have rejected (failed : SymbolicTestCode.apply before.state.knowledge (storeOf before) (goals a) (entered a) = none) :
      ∃ after, SymbolicExecution.execute before.state.knowledge (enter machine before) (compile a) =
        .returned .refused 0 after ∧ after.store = (enter machine before).store ∧ SameFuel (enter machine before) after := by
    have no := tests
    rw [failed] at no
    obtain ⟨after, unchanged, unpaid, refused⟩ := no
    exact ⟨after, full.trans refused, unchanged, free.trans unpaid⟩
  rw [source_decision]
  cases solved : unifyTotal (problem a.seed) with
  | none => exact rejected (by rw [test_tape, solved])
  | some answer =>
    by_cases accepted : accepts a answer = true
    · simp only [accepted, if_true]
      have applied : SymbolicTestCode.apply before.state.knowledge (storeOf before) (goals a) (entered a) =
          some (finished a answer) := by simp [test_tape, solved, accepted]
      rw [applied] at tests
      obtain ⟨staged, sameStore, stillFree, ready, handed⟩ := tests
      have money := free.trans stillFree
      have issued : SymbolicExecution.execute before.state.knowledge (enter machine before) (compile a) =
          SymbolicExecution.execute before.state.knowledge staged action := full.trans handed
      obtain ⟨takeEqual, _, knowledge, answered⟩ := finished_fields a answer
      have takes : (staged.levels (level a)).taken.length = a.seed.firing.selection.taken.length := by rw [ready, takeEqual]
      have makes : (staged.levels (level a)).made.length = (body a).produce.length :=
        congrArg (fun m : Match (Term σ) (Work σ) => m.made.length) ready
      have publish := SymbolicPublication.execute_emit before.state.knowledge staged (level a) _ _ takes makes
      have budget : staged.machine.budget = machine.budget := money.budget
      have spent : staged.machine.spent = machine.spent := money.spent
      rw [budget, spent] at publish
      by_cases empty : machine.budget - machine.spent < (1 : Word)
      · rw [if_pos empty] at publish ⊢
        exact ⟨staged, issued.trans publish, sameStore, money⟩
      · rw [if_neg empty] at publish ⊢
        obtain ⟨after, ran, keptLevel, output, paid⟩ := publish
        let selected := chosen a answer
        have reserved : selected.firing.selection.made = before.reserve 0 selected.firing.selection.made.length :=
          a.allocation
        refine ⟨after, _, reserved, issued.trans ran, ?_, ?_, ?_, paid⟩
        · rw [output, sameStore, ready, takeEqual]
          exact (SymbolicPublication.storeOf_commit before selected.firing selected.shaped reserved).symm
        · rw [keptLevel, ready, knowledge]
          rfl
        · rw [keptLevel, ready, answered]
    · simp only [accepted]
      exact rejected (by simp [test_tape, solved, accepted])

theorem decision_of_search {a : Trial} {success : Accepted rules before}
    (found : a.check = some success) :
    evaluateInferred a.seed = some (success.solution, success.selected) := by
  simp only [Attempt.check, Attempt.solve] at found
  split at found
  · cases found
  · rename_i answer selection proposed
    simp only [Option.bind_some, Pending.check] at found
    split at found
    · rename_i passes
      obtain rfl := (Option.some.inj found).symm
      change evaluateInferred a.seed = some (answer, selection)
      unfold evaluateInferred
      rw [proposed]
      change (if firingChecks answer before.state selection.firing then some (answer, selection) else none) = _
      rw [if_pos passes]
    · cases found

/-- Every admitted source firing has a compiled selected run with
the same result models, including freshenings of the source's local
unknowns. The compilation is along the already proved search
space; it does not select or fix a ground solution. -/
theorem covers_source_models (slots : σ.vars ≃ ℕ)
    (source : RuleSyntax.Firing ℕ (RuleSyntax.OneFrame.ext (FirstOrder.action σ)) rules.program before.state.frame)
    (admitted : source.Admits (act σ) before.state)
    (machine : P1WordExecution.State) (fits : before.live.length < 2 ^ 64)
    (funded : ¬machine.budget - machine.spent < (1 : Word)) :
    ∃ a ∈ attempts slots rules before, ∃ (success : Accepted rules before) (after : Frame σ),
      (∀ incoming output,
        ResultModel before.state source incoming output ↔
          ResultModel before.state success.selected.firing incoming output) ∧
      (∃ payload, SymbolicExecution.execute before.state.knowledge (enter machine before) (compile a) =
        .returned .completed payload after) ∧
      after.store = storeOf success.publish ∧
      (after.levels (level a)).bindings.problem before.state.knowledge = success.publish.state.knowledge := by
  obtain ⟨a, belongs, success, found, _, models⟩ := attempts_cover_models slots rules before source admitted
  have executes := run a machine fits
  dsimp only at executes
  rw [decision_of_search found] at executes
  change (if machine.budget - machine.spent < (1 : Word) then _ else _) at executes
  rw [if_neg funded] at executes
  obtain ⟨after, payload, _, ran, published, knowledge, _, _⟩ := executes
  exact ⟨a, belongs, success, after, models, ⟨payload, ran⟩, published, knowledge⟩

end Mettapedia.Machines.TIsa.StoreInstructions.SymbolicFiringCode
