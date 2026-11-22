import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualQueryAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.CountedTransitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegrationRows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.NativeMatchKernel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.AnswerCollection
import Mettapedia.Machines.Cursor.StampedSnapshots

/-!
# A tmetta equation with a held match body

For a read of one fixed space, compile an equation to a hosted call returning a
match request. Its carried pattern, template and caller knowledge are the input
to the contextual match rule. Count choices by equation and row occurrence.
This observation forgets fresh administrative names. It retains the caller's
logical names when a constrained answer is reopened.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTa

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting Hosting.Alternatives
open RuleSyntax.StepWeb.Counted
namespace Query
abbrev D := numbers.discipline

/-- The source equation `(= lhs (match &self pattern template))`. -/
structure Clause where
  site : List Nat
  lhs : MData
  pattern : MData
  template : MData

private def requesting (store : List (Constraint mkeys [] ())) (pattern template : MData)
    (frames : List (Frame mkeys [] () MTy)) : Branch mkeys [] () MTy :=
  ⟨store, .eval (.query (sym "&self") pattern (.ret template)), frames, []⟩

def requestObservation {B : Interface.Frames.Frame MSig}
    (pattern template stack : NativeQuery.MatchKernel.Body B) : Observation MSig B.arity :=
  observe (NativeQuery.MatchKernel.Hosted.request mettaNodes (symAt "&self") pattern template stack)

/-- The request issued by the hosted call retains the pattern, held template
and continuation under one assignment of the caller's names. -/
theorem request_readback {P : SourceLanguage.Program mkeys [] () MTy} {n : Nat}
    {s : HostState MSig} {occurrence : Nat} {B : Interface.Frames.Frame MSig}
    {store : List (Constraint mkeys [] ())} {p t : MData} {frames : List (Frame mkeys [] () MTy)}
    (hosted : Represents mettaNodes P n (requesting store p t frames) s occurrence)
    (pattern template stack : NativeQuery.MatchKernel.Body B) :
    rowReads s occurrence B (requestObservation pattern template stack) ↔
      ∃ point : Assignment (fam mkeys) B.arity, Models point store ∧
        instantiate point p = pattern ∧ instantiate point t = template ∧
        encStack mettaNodes (instantiate point) frames = stack := by
  rw [hosted.reads]
  constructor
  · rintro ⟨point, model, same⟩
    have terms : NativeQuery.MatchKernel.Hosted.request mettaNodes (F := B) (symAt "&self")
        (instantiate point p) (instantiate point t) (encStack mettaNodes (instantiate point) frames) =
      NativeQuery.MatchKernel.Hosted.request mettaNodes (symAt "&self") pattern template stack := observe_injective same
    obtain ⟨_, pat, body, rest⟩ := NativeQuery.MatchKernel.Hosted.request_inj mettaNodes terms
    exact ⟨point, model, pat, body, rest⟩
  · rintro ⟨point, model, pat, body, rest⟩
    refine ⟨point, model, ?_⟩
    change requestObservation (instantiate point p) (instantiate point t)
      (encStack mettaNodes (instantiate point) frames) = _
    rw [pat, body, rest]

def Clause.equation (e : Clause) : Equation mkeys [] () MTy :=
  ⟨e.site, e.lhs, .query (sym "&self") e.pattern (.ret e.template)⟩

def program (clauses : List Clause) : SourceLanguage.Program mkeys [] () MTy :=
  ⟨clauses.map Clause.equation, .apply⟩

section Compilation
variable (clauses : List Clause) (rows : List (Row mkeys [] ())) (call : MData)
abbrev Origin := Fin clauses.length × Fin rows.length

def callStore (e : Clause) (t : MData) : List (Constraint mkeys [] ()) :=
  [(instantiate (copyAt mkeys 0) e.lhs, t)]

def opened (t : MData) := instantiate (copyAt mkeys 0) t

def answer (which : Origin clauses rows) : Branch mkeys [] () MTy :=
  let e := clauses[which.1]
  ⟨callStore e call ++ rowUse 1 rows[which.2] (opened e.pattern),
    .value (opened e.template), [], []⟩

def world (rows : List (Row mkeys [] ())) : World mkeys [] () :=
  ⟨0, 0, fun handle => if handle = csym "&self" then rows else 0⟩

/-- The two admitted services at a specified origin. The intermediate hosted
state must represent the *opened request*, including its constraint store. -/
def Fires (which : Origin clauses rows) : Prop :=
  let e := clauses[which.1]
  let p := program clauses
  let s := start mettaNodes p (.apply call)
  let k := freshId s
  let intermediate := requesting (callStore e call) (opened e.pattern) (opened e.template) []
  (∃ t, HeldFires mettaNodes p (origin mettaNodes (.eqn which.1)) s p.equations.length t k ∧
    Represents mettaNodes p 1 intermediate t k) ∧
    (NativeQuery.MatchKernel.firing 1 (callStore e call) (opened e.pattern) (opened e.template) rows[which.2]).Admits
      NativeQuery.MatchKernel.X
      (NativeQuery.MatchKernel.initial 1 (callStore e call) (opened e.pattern) (opened e.template) rows[which.2])

theorem fires_iff (which : Origin clauses rows)
    (unopened : ∀ t ∈ (Comp.apply call : Comp mkeys [] () MTy).data, ∀ x ∈ support t, x.scopes = []) :
    Fires clauses rows call which ↔ Solvable (answer clauses rows call which).store := by
  let e := clauses[which.1]
  let p := program clauses
  let s := start mettaNodes p (.apply call)
  constructor
  · intro h
    exact (NativeQuery.MatchKernel.admitted_iff_source ..).mp h.2
  · intro h
    have read := (NativeQuery.MatchKernel.admitted_iff_source 1 (callStore e call)
      (opened e.pattern) (opened e.template) rows[which.2]).mpr h
    obtain ⟨V, arity, point, known⟩ := h
    have callLive : Solvable (callStore e call) :=
      ⟨V, arity, point, ((models_append point _ _).mp known).1⟩
    have get : p.equations[which.1.val]? = some e.equation := by
      simp [p, program, e, which.1.isLt]
    have rep := start_represents mettaNodes p (.apply call) unopened
    have inProgram := schema_mem mettaNodes (P := p) (List.mem_of_getElem? get)
    obtain ⟨admitted, next⟩ := fire_simple_canonical mettaNodes inProgram ⟨rfl, rfl, rfl⟩ rfl rep
      (fun _ q => transfer_schema mettaNodes e.equation rfl rep.fresh q) callLive
      (freshId_not_mem s) (entails_of_no_checks rfl rfl) (branchBelow_call rep.fresh e.equation) rep.noPending
    have named : FiresNamed mettaNodes p (.eqn which.1) s p.equations.length _ (freshId s) :=
      ⟨schema mettaNodes e.equation, by simp [ruleNamed, get], _, rfl, admitted, rfl, rfl, rfl⟩
    exact ⟨⟨_, heldFires_of_firesNamed named, next⟩, read⟩

/-- The solver runs on the very equations used in admission and capture.
A residual carries both its answer substitution and the outstanding problem. -/
def solve {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
    [DecidableEq (Name κ)] [DecidableEq S.Srt] [∀ s, DecidableEq (S.Op s)]
    (fuel : Nat) (store : List (Constraint κ Γ star)) :=
  ContextualFrameWorklist.run fuel (fam κ) (ContextualResidual.observeProblem store)

namespace NativeSolver
open ContextualResidual ContextualFrameWorklist

section
variable {S : Signature} {V : Type} [DecidableEq V] [DecidableEq S.Srt]
  [∀ sort, DecidableEq (S.Op sort)] {source : V → MetaArity S}

private def allowed (equation : Equation (Observation S source)) : Bool :=
  ContextualPatternFragment.check equation.1.2.2 && ContextualPatternFragment.check equation.2.2.2

/-- Normalize the whole conjunction, then choose supported equations from it.
An unchecked equation stays in the residual while other equations can bind
its head or arguments. -/
private def runNative (fuel : Nat) {Names : Type} [DecidableEq Names]
    (declaration : Names → MetaArity S) (problem : Problem declaration) : Result problem :=
  if ContextualPatternFragment.checkProblem problem then
    run fuel declaration problem
  else
    runWithRefuter (fun _ k => ContextualEquationRefutation.choose k allowed) fuel declaration problem
      (fun _ k => (ContextualSolverSelect.choose k allowed).map ContextualSolverCases.Choice.perform)

def attempt (fuel : Nat) (problem : Problem source) : Result problem :=
  runNative fuel source problem

def resume {problem : Problem source} (prior : Result problem) (fuel : Nat)
    (input : Problem source) : Result (problem ++ input) :=
  prior.resumeUsing fuel input runNative

theorem attempt_eq_on_patterns (fuel : Nat) (problem : Problem source)
    (supported : ContextualPatternFragment.ProblemPattern problem) :
    attempt fuel problem = run fuel source problem := by
  simp [attempt, runNative, (ContextualPatternFragment.checkProblem_iff problem).mpr supported]

theorem finishes_on_patterns (problem : Problem source)
    (supported : ContextualPatternFragment.ProblemPattern problem) :
    ∃ fuel, ContextualPatternTermination.Finished (attempt fuel problem) := by
  obtain ⟨fuel, finished⟩ := ContextualPatternTermination.finishes problem supported
  exact ⟨fuel, attempt_eq_on_patterns fuel problem supported ▸ finished⟩

omit [DecidableEq V] in
/-- Resumption takes the supported route when the retained and new work,
viewed in the saved declaration, form a structural-pattern problem. -/
theorem resume_finishes_on_patterns {problem : Problem source} (prior : Result problem)
    (input : Problem source)
    (supported : ∀ update, prior = .residual update →
      ContextualPatternFragment.ProblemPattern (update.remaining ++ mapProblem update.answer input)) :
    ∃ fuel, ContextualPatternTermination.Finished (resume prior fuel input) := by
  cases prior with
  | refuted impossible =>
    exact ⟨0, .refuted fun next candidate models =>
      impossible next candidate ((models_append candidate problem input).mp models).1⟩
  | residual update =>
    let _ := update.equality
    obtain ⟨fuel, finished⟩ := finishes_on_patterns _ (supported update rfl)
    exact ⟨fuel, finished.after (update.keep_right input)⟩

end

variable {S : Signature} {V W : Type} {source : V → MetaArity S} {target : W → MetaArity S}

/-- Read models through a decision, including the entire retained residual. -/
def modelsThrough {problem : Problem source} (result : Result problem)
    (point : Assignment source target) : Prop :=
  match result with
  | .refuted _ => False
  | .residual next => ∃ image : Assignment next.declaration target,
    ContextualResidual.Models image next.remaining ∧ Assignment.compose image next.answer = point

theorem modelsThrough_exact {problem : Problem source} (result : Result problem)
    (point : Assignment source target) :
    modelsThrough result point ↔ ContextualResidual.Models point problem := by
  cases result with
  | refuted impossible =>
    exact ⟨False.elim, impossible target point⟩
  | residual next =>
    constructor
    · rintro ⟨image, remaining, rfl⟩
      exact next.valid.sound target image remaining
    · intro known
      obtain ⟨image, remaining, same⟩ := next.valid.complete target point known
      exact ⟨image, remaining, (funext same).symm⟩

theorem closed_successful_iff {problem : Problem source} (result : Result problem)
    (closed : ContextualQueryAnswers.closed result = true) :
    ContextualQueryAnswers.successful result = true ↔
      ∃ (W : Type) (target : W → MetaArity S) (point : Assignment source target),
        ContextualResidual.Models point problem := by
  cases result with
  | refuted impossible =>
    constructor
    · intro no
      cases no
    · rintro ⟨_, decl, point, model⟩
      exact (impossible decl point model).elim
  | residual next =>
    have empty := List.isEmpty_iff.mp closed
    exact ⟨fun _ => ⟨_, _, next.answer, next.completed empty⟩, fun _ => closed⟩

/-- Both policies preserve exactly the old names' models of the completed
input prefix. They can report different amounts of remaining work. -/
theorem resume_models_agree [DecidableEq V] [DecidableEq S.Srt]
    [∀ sort, DecidableEq (S.Op sort)] (firstFuel fuel : Nat)
    (problem input : Problem source) (point : Assignment source target) :
    modelsThrough (resume (attempt firstFuel problem) fuel input) point ↔
      modelsThrough ((run firstFuel source problem).resume fuel input) point :=
  (modelsThrough_exact _ _).trans (modelsThrough_exact _ _).symm

theorem resume_completed_agree [DecidableEq V] [DecidableEq S.Srt]
    [∀ sort, DecidableEq (S.Op sort)] (firstFuel fuel : Nat) (problem input : Problem source)
    (native : ContextualQueryAnswers.closed (resume (attempt firstFuel problem) fuel input) = true)
    (logical : ContextualQueryAnswers.closed ((run firstFuel source problem).resume fuel input) = true) :
    ContextualQueryAnswers.successful (resume (attempt firstFuel problem) fuel input) = true ↔
      ContextualQueryAnswers.successful ((run firstFuel source problem).resume fuel input) = true :=
  (closed_successful_iff _ native).trans (closed_successful_iff _ logical).symm

end NativeSolver

theorem solved_iff (fuel : Nat) (store : List (Constraint mkeys [] ()))
    (complete : ContextualQueryAnswers.closed (solve fuel store) = true) :
    ContextualQueryAnswers.successful (solve fuel store) = true ↔ Solvable store := by
  cases computed : solve fuel store with
  | refuted no =>
    constructor
    · intro h; cases h
    · rintro ⟨_, decl, candidate, model⟩
      exact (no decl candidate ((ContextualResidual.models_observeProblem _ _).mpr model)).elim
  | residual update =>
    rw [computed] at complete
    have empty := List.isEmpty_iff.mp complete
    exact ⟨fun _ => ⟨_, _, update.answer, (ContextualResidual.models_observeProblem _ _).mp
      (update.completed empty)⟩, fun _ => complete⟩

/-- A waking input refines the entire saved store. If its solver still
has residual equations, a caller model must factor through both the
returned assignment and those equations. -/
theorem resume_models {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
    {V : Type} {arity : V → MetaArity S}
    [DecidableEq (Name κ)] [DecidableEq S.Srt] [∀ s, DecidableEq (S.Op s)]
    (store input : List (Constraint κ Γ star)) (firstFuel fuel : Nat)
    (caller : Assignment (fam κ) arity) :
    Models caller (store ++ input) ↔
      match (solve firstFuel store).resume fuel (ContextualResidual.observeProblem input) with
      | .refuted _ => False
      | .residual next =>
        ∃ remaining : Assignment next.declaration arity,
          ContextualResidual.Models remaining next.remaining ∧
          Assignment.compose remaining next.answer = caller := by
  have observeAppend : ContextualResidual.observeProblem (store ++ input) =
      ContextualResidual.observeProblem store ++ ContextualResidual.observeProblem input :=
    List.map_append
  change ContextualFrameUnifier.Models caller (store ++ input) ↔ _
  rw [← ContextualResidual.models_observeProblem, observeAppend]
  cases (solve firstFuel store).resume fuel (ContextualResidual.observeProblem input) with
  | refuted impossible =>
    exact ⟨fun solved => impossible arity caller solved, False.elim⟩
  | residual next =>
    constructor
    · intro solved
      obtain ⟨remaining, known, same⟩ := next.valid.complete arity caller solved
      exact ⟨remaining, known, (funext same).symm⟩
    · rintro ⟨remaining, known, rfl⟩
      exact next.valid.sound arity remaining known

theorem finite_pattern_decision (i : Origin clauses rows)
    (patterned : ContextualPatternFragment.ProblemPattern
      (ContextualResidual.observeProblem (answer clauses rows call i).store))
    (unopened : ∀ t ∈ (Comp.apply call : Comp mkeys [] () MTy).data, ∀ x ∈ support t, x.scopes = []) :
    ∃ fuel, ContextualQueryAnswers.closed (solve fuel (answer clauses rows call i).store) = true ∧
      (ContextualQueryAnswers.successful (solve fuel (answer clauses rows call i).store) = true ↔ Fires clauses rows call i) := by
  obtain ⟨fuel, finished⟩ := ContextualPatternTermination.finishes _ patterned
  have complete : ContextualQueryAnswers.closed (solve fuel (answer clauses rows call i).store) = true := by
    change ContextualPatternTermination.Finished (solve fuel (answer clauses rows call i).store) at finished
    generalize computed : solve fuel (answer clauses rows call i).store = result at finished ⊢
    cases finished with
    | solved u empty => simp [ContextualQueryAnswers.closed, empty]
    | refuted => rfl
  exact ⟨fuel, complete, (solved_iff fuel _ complete).trans (fires_iff clauses rows call i unopened).symm⟩

/-- The repeated spine in `λx. F(x,x) = λx. z` fails the pattern test.
A constant function nevertheless solves it and admits the actual row read. -/
theorem repeated_spine_is_live :
    let v := (Term.var .zero : Term (signature MSig (fam mkeys)) [()] ())
    let application : Term (signature MSig (fam mkeys)) [()] () :=
      .op (.inr (.mk ⟨[], ⟨[4], 0, ([(), ()], ())⟩⟩)) (.cons v (.cons v .nil))
    let pat := lamAt application
    let row : Row mkeys [] () := ⟨lamAt (symAt "z"), []⟩
    ContextualPatternFragment.check pat = false ∧
      (NativeQuery.MatchKernel.firing 0 [] pat (sym "ok") row).Admits NativeQuery.MatchKernel.X
        (NativeQuery.MatchKernel.initial 0 [] pat (sym "ok") row) := by
  intro v application pat row
  constructor
  · decide +revert
  · apply NativeQuery.MatchKernel.admitted_of_source
    refine ⟨Empty, noNames, fun _ => symAt "z", ?_⟩
    intro e he
    obtain rfl := List.mem_singleton.mp he
    rfl

/-- Returning an unmatched call requires completed refutation of every
head occurrence. An equation with an empty body answer still matches. -/
def allHeadsRefuted (cs : List Clause) (t : MData) (fuel : Nat) : Bool :=
  cs.all fun c =>
    match solve fuel (callStore c t) with
    | .refuted _ => true
    | .residual _ => false

theorem unmatched_sound (cs : List Clause) (t : MData) (fuel : Nat)
    (done_ : allHeadsRefuted cs t fuel = true) :
    ∀ c ∈ cs, ¬ Solvable (callStore c t) := by
  intro c mem
  have refused := List.all_eq_true.mp done_ c mem
  rintro ⟨_, decl, σ, model⟩
  cases computed : solve fuel (callStore c t) with
  | refuted impossible => exact impossible decl σ ((ContextualResidual.models_observeProblem _ _).mpr model)
  | residual u => simp [computed] at refused

/-- A completed admission remains a historical fact even if a later input
refutes every pending sibling. Those siblings alone cannot produce fallback. -/
def unmatchedAfterInput (hadAdmission : Bool) (clauses : List Clause) (call : MData)
    (firstFuel fuel : Nat) (input : List (Constraint mkeys [] ())) : Bool :=
  !hadAdmission && clauses.all fun clause =>
    match (solve firstFuel (callStore clause call)).resume fuel
      (ContextualResidual.observeProblem input) with
    | .refuted _ => true
    | .residual _ => false

theorem unmatchedAfterInput_sound (hadAdmission : Bool) (clauses : List Clause) (call : MData)
    (firstFuel fuel : Nat) (input : List (Constraint mkeys [] ()))
    (complete : unmatchedAfterInput hadAdmission clauses call firstFuel fuel input = true) :
    hadAdmission = false ∧ ∀ e ∈ clauses, ¬ Solvable (callStore e call ++ input) := by
  simp only [unmatchedAfterInput, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at complete
  refine ⟨complete.1, fun e found live => ?_⟩
  obtain ⟨V, arity, caller, known⟩ := live
  have encoded := (resume_models (callStore e call) input firstFuel fuel caller).mp known
  have result := complete.2 e found
  cases next : (solve firstFuel (callStore e call)).resume fuel (ContextualResidual.observeProblem input) with
  | refuted impossible =>
    rw [next] at encoded
    exact encoded
  | residual update =>
    simp only [next, Bool.false_eq_true] at result

private def countStores (fuel : Nat) : List (List (Constraint mkeys [] ())) → Option Nat
  | [] => some 0
  | store :: rest => do
    let result := solve fuel store
    guard (ContextualQueryAnswers.closed result)
    let n ← countStores fuel rest
    return if ContextualQueryAnswers.successful result then n + 1 else n

open Classical in
private theorem countStores_exact (fuel : Nat) (stores : List (List (Constraint mkeys [] ()))) (n : Nat)
    (counted : countStores fuel stores = some n) : n = (stores.filter (fun k => decide (Solvable k))).length := by
  induction stores generalizing n with
  | nil => simpa [countStores] using counted.symm
  | cons k ks ih =>
    cases closed : ContextualQueryAnswers.closed (solve fuel k) with
    | false => simp [countStores, closed] at counted
    | true =>
      have decides := solved_iff fuel k closed
      cases tailCount : countStores fuel ks with
      | none => simp [countStores, closed, tailCount] at counted
      | some m =>
        have tail := ih m tailCount
        by_cases yes : Solvable k
        · have accepted := decides.mpr yes
          simp [countStores, closed, accepted, tailCount] at counted
          simp [yes, ← tail, ← counted]
        · have refused : ContextualQueryAnswers.successful (solve fuel k) = false := by
            cases h : ContextualQueryAnswers.successful (solve fuel k)
            · rfl
            · exact (yes (decides.mp h)).elim
          simp [countStores, closed, refused, tailCount] at counted
          simp [yes, ← tail, ← counted]

def candidateStores (caller : List (Constraint mkeys [] ())) :=
  (List.finRange clauses.length).flatMap fun i => (List.finRange rows.length).map fun j =>
    caller ++ (answer clauses rows call (i, j)).store

/-- An incomplete job prevents publication of a count. Each completed job
contributes one occurrence exactly when its *joint* caller store has a model. -/
def countAt (fuel : Nat) (caller : List (Constraint mkeys [] ())) : Option Nat :=
  countStores fuel (candidateStores clauses rows call caller)

open Classical in
theorem countAt_exact (fuel n : Nat) (caller : List (Constraint mkeys [] ()))
    (computed : countAt clauses rows call fuel caller = some n) :
    n = ((candidateStores clauses rows call caller).filter (fun k => decide (Solvable k))).length :=
  countStores_exact _ _ _ computed

/-- One row per admitted origin. The same rule or row text can occur twice. -/
noncomputable def answers (clauses : List Clause) (rows : List (Row mkeys [] ())) (call : MData) : AnswerCollection.AnswerSpace mkeys [] () D := by
  classical
  let indices := (Finset.univ : Finset (Origin clauses rows)).filter (Fires clauses rows call)
  -- Every admitted read has a live, finished snapshot, including open answers.
  refine ⟨indices.val.map (answer clauses rows call), ?_⟩
  intro b member
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp member
  have fired := (Finset.mem_filter.mp (show i ∈ indices from hi)).2
  exact ⟨⟨rfl, _, rfl⟩, (NativeQuery.MatchKernel.admitted_iff_source ..).mp fired.2⟩

/-- At a fixed caller assignment the read produces exactly the recorded value
and constraints, existentially hiding the fresh slots of the transform rule. -/
theorem answer_models (i : Origin clauses rows) {B : Interface.Frames.Frame MSig}
    (σ : Assignment (fam mkeys) B.arity) (value : NativeQuery.MatchKernel.Body B) :
    let e := clauses[i.1]
    let f := NativeQuery.MatchKernel.firing 1 (callStore e call) (opened e.pattern) (opened e.template) rows[i.2]
    let s := NativeQuery.MatchKernel.initial 1 (callStore e call) (opened e.pattern) (opened e.template) rows[i.2]
    (Models σ (answer clauses rows call i).store ∧ instantiate σ (opened e.template) = value) ↔
      ∃ u : Assignment (RuleSyntax.Contextual.extend MSig NativeQuery.MatchKernel.callerFrame NativeQuery.MatchKernel.locals).arity B.arity,
        Assignment.compose u (RuleSyntax.Contextual.weakenNames MSig NativeQuery.MatchKernel.callerFrame NativeQuery.MatchKernel.locals) = σ ∧
        NativeQuery.MatchKernel.X.Models u (f.result NativeQuery.MatchKernel.X s).knowledge ∧
        instantiateObservation u ((f.result NativeQuery.MatchKernel.X s).label 2) = observe value := by
  dsimp only
  let e := clauses[i.1]
  have projected := NativeQuery.MatchKernel.projected_models 1 (callStore e call)
    (opened e.pattern) (opened e.template) rows[i.2] (future := B) σ
  constructor
  · rintro ⟨model, rfl⟩
    obtain ⟨u, restrict, known⟩ := projected.mp model
    exact ⟨u, restrict, known,
      (NativeQuery.MatchKernel.output_template _ _ _ _ _ u known).trans
        (by rw [restrict])⟩
  · rintro ⟨u, restrict, known, output⟩
    refine ⟨projected.mpr ⟨u, restrict, known⟩, ?_⟩
    change Assignment.compose u (RuleSyntax.Contextual.weakenNames MSig NativeQuery.MatchKernel.callerFrame NativeQuery.MatchKernel.locals) = σ at restrict
    rw [NativeQuery.MatchKernel.output_template _ _ _ _ _ u known, restrict] at output
    exact observe_injective output

/-- The extensional collect query really is attainable by collector administration.
An enumerator must finish checking each origin to use this complete readout. -/
theorem reaches_reify
    (unopened : ∀ t ∈ (Comp.apply call : Comp mkeys [] () MTy).data, ∀ x ∈ support t, x.scopes = []) :
    let candidates := (Finset.univ : Finset (Origin clauses rows)).val.map (answer clauses rows call)
    ∃ final, Relation.ReflTransGen (AnswerCollection.Admin (D := D))
        (AnswerCollection.State.initial ⟨world rows, candidates⟩) final ∧
      ∃ valid, AnswerCollection.reify final valid = some (answers clauses rows call) := by
  classical
  let origins := (Finset.univ : Finset (Origin clauses rows)).val
  let work := origins.map (answer clauses rows call)
  obtain ⟨final, path, valid, bag, closed, counted⟩ := AnswerCollection.collect_finished
    (D := D) (world rows) work.toList (by
      intro b hb
      have mem : b ∈ work := Multiset.mem_toList.mp hb
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp mem
      exact ⟨rfl, _, rfl⟩)
  rw [Multiset.coe_toList] at path counted
  refine ⟨final, path, valid, ?_⟩
  rw [closed]
  congr 1
  cases bag with
  | mk recorded ready =>
    simp only at counted
    suffices same : recorded = (answers clauses rows call).rows by cases same; rfl
    rw [counted]
    change (origins.map _).filter _ = (origins.filter _).map _
    rw [Multiset.filter_map]
    congr 1
    apply Multiset.filter_congr
    intro i _
    exact (fires_iff clauses rows call i unopened).symm

end Compilation

/-! ## Opening a selected occurrence

The caller's activated variables are already in scope when a row is
selected. The authored names of that row get an occurrence-local scope.
The same opened row and its equations feed the existing query firing. -/

def storedOpening {S : Signature} {κ : Keys S} (scope : Nat) : Assignment (fam κ) (fam κ) :=
  relabel κ fun name => if name.scopes = [] then [scope] else name.scopes

theorem storedOpening_captured (scope : Nat) (name : Name mkeys) (activated : name.scopes ≠ []) :
    storedOpening scope name = generator (fam mkeys) name := by
  cases name with
  | mk scopes key =>
      change scopes ≠ [] at activated
      change generator (fam mkeys) ⟨(if scopes = [] then [scope] else scopes), key⟩ =
        generator (fam mkeys) ⟨scopes, key⟩
      rw [if_neg activated]

theorem storedOpening_authored (scope : Nat) (key : mkeys.Key) :
    storedOpening scope ⟨[], key⟩ = generator (fam mkeys) ⟨[scope], key⟩ := rfl

abbrev openStoredRow {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
    (scope : Nat) (row : Row κ Γ star) :=
  NativeQuery.MatchKernel.openRow (storedOpening scope) row

namespace CapturedRow

open NativeQuery.MatchKernel

private def captured := foD [4] [0] 0
def row : Row mkeys [] () := ⟨captured, []⟩
private def caller : List (Constraint mkeys [] ()) := [(captured, sym "red")]

/-- One read has already equated a shared capture with red. The next
read of blue must respect that image even using another occurrence scope.
Opening every name as a schema local would incorrectly admit the read. -/
theorem capture_changes_admission :
    (¬ (Opened.firing caller (sym "blue") (sym "seen") (openStoredRow 5 row)).Admits X
        (Opened.initial caller (sym "blue") (sym "seen") (openStoredRow 5 row))) ∧
    (firing 5 caller (sym "blue") (sym "seen") row).Admits X
      (initial 5 caller (sym "blue") (sym "seen") row) := by
  have kept : (openStoredRow 5 row).atom = captured := by
    change instantiate (storedOpening 5) (foD [4] [0] 0) = _
    rw [instantiate_foD, storedOpening_captured _ _ (by decide)]
    rfl
  constructor
  · intro admitted
    obtain ⟨target, arity, assign, models⟩ := Opened.source_of_admitted caller _ _ _ admitted
    have before := ((models_append assign _ _).mp models).1 _ (List.mem_cons_self ..)
    have read := ((models_append assign _ _).mp models).2 _ (List.mem_cons_self ..)
    change instantiate assign (sym "blue") = instantiate assign (openStoredRow 5 row).atom at read
    rw [kept] at read
    have conflict : (symAt (target := arity) "blue") = symAt "red" := read.trans before
    injection conflict with _ _ op
    simp at op
  · apply admitted_of_source
    exact ⟨Empty, noNames, closeNames [(([4], [0], 0), csym "red"),
      (([5, 4], [0], 0), csym "blue")] (csym "unused"), by decide⟩

end CapturedRow

namespace Versioned

open NativeQuery.MatchKernel
open Mettapedia.Machines.Cursor
open Mettapedia.Machines.Cursor.StampedSnapshots
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)

/-- The slots an occurrence reader visits at the start revision, in traversal
order. Equal payloads at distinct slots belong to distinct alternatives. -/
def liveRows {Row : Type} (view : Store Row) : List (Nat × Row) :=
  (snapshot view (StampedSnapshots.start view)).filterMap id

theorem mem_liveRows {Row : Type} (view : Store Row) (position : Nat) (row : Row) :
    (position, row) ∈ liveRows view ↔
      position < view.next ∧ atTime view view.clock position = some (position, row) := by
  have position_of_slot {i : Nat} (selected : atTime view view.clock i = some (position, row)) :
      i = position := by
    unfold atTime at selected
    cases found : view.row i with
    | none => simp [found] at selected
    | some item =>
      rw [found] at selected
      change (if visible view.clock item then some (i, item.value) else none) =
        some (position, row) at selected
      split at selected
      · exact (Prod.mk.inj (Option.some.inj selected)).1
      · simp at selected
  simp only [liveRows, snapshot, StampedSnapshots.start, List.mem_filterMap, id_eq,
    List.mem_map, List.mem_range]
  constructor
  · rintro ⟨_, ⟨i, earlier, rfl⟩, found⟩
    have same := position_of_slot found
    subst i
    exact ⟨earlier, found⟩
  · rintro ⟨within, found⟩
    exact ⟨_, ⟨position, within, rfl⟩, found⟩

def liveIds {Row : Type} (view : Store Row) : Finset Nat :=
  (liveRows view).map Prod.fst |>.toFinset

theorem mem_liveIds {Row : Type} (view : Store Row) (position : Nat) :
    position ∈ liveIds view ↔ ∃ row, (position, row) ∈ liveRows view := by
  simp only [liveIds, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨i, row⟩, member, rfl⟩
    exact ⟨row, member⟩
  · rintro ⟨row, member⟩
    exact ⟨(position, row), member, rfl⟩

section Ground

variable {S : Signature} {star : S.Srt} (N : Nodes S [] star)

local notation "ClosedTerm" => Term S [] star
local notation "ReadBody" => Hosted.BodyAt [] star
local notation "ReadTerm" => RuleSyntax.Contextual.Terms S
local notation "ReadFrames" => Interface.Frames.contextual S
local notation "ReadExtensions" => RuleSyntax.Contextual.declarations S

/-- The selected occurrence and the revision live beside the hosted request.
Different row occurrences keep distinct identities even when the facts agree.
The borrowed view contributes its current revision independently of the
revision requested by a pending selection. -/
def rowId (host : HostState S) (occurrence : Nat) := freshId host + 2 * occurrence
def revisionId (host : HostState S) (epoch : Nat) := freshId host + 2 * epoch + 1

def withRead (host : HostState S) (address : ClosedTerm) (view : Store ClosedTerm) (occurrence : Nat) :
    HostState S :=
  let selected := atTime view view.clock occurrence
  { host with
    present := insert (revisionId host view.clock)
      (if selected.isSome then insert (rowId host occurrence) host.present else host.present)
    label := fun id =>
      if id = revisionId host view.clock then observe (Hosted.revision N (Rigid.includeTerm host.frame.arity address))
      else if id = rowId host occurrence then
        (selected.map fun (_, term) =>
          observe (Hosted.fact N (Rigid.includeTerm host.frame.arity address) (Rigid.includeTerm host.frame.arity term))).getD
            (host.label id)
      else host.label id }

variable (host : HostState S) (address : Term S [] star) (view : Store (Term S [] star)) (occurrence : Nat)

private theorem below {i : Nat} (present : i ∈ host.present) : i < freshId host := by
  have bound : id i ≤ host.present.sup id := Finset.le_sup present
  exact Nat.lt_succ_of_le bound

theorem host_label {i : Nat} (present : i ∈ host.present) :
    (withRead N host address view occurrence).label i = host.label i := by
  have small := below host present
  simp [withRead, rowId, revisionId,
    show i ≠ freshId host + 2 * view.clock + 1 by omega,
    show i ≠ freshId host + 2 * occurrence by omega]

private theorem chosen_label {datum : ClosedTerm} (found : atTime view view.clock occurrence = some (occurrence, datum)) :
    (withRead N host address view occurrence).label (rowId host occurrence) =
      observe (Hosted.fact N (Rigid.includeTerm host.frame.arity address) (Rigid.includeTerm host.frame.arity datum)) := by
  have distinct : rowId host occurrence ≠ revisionId host view.clock := by unfold rowId revisionId; omega
  simp [withRead, distinct, found]

theorem stale_absent {time : Nat} (stale : time ≠ view.clock) :
    revisionId host time ∉ (withRead N host address view occurrence).present := by
  have rev : revisionId host time ≠ revisionId host view.clock := by unfold revisionId; omega
  have row : revisionId host time ≠ rowId host occurrence := by unfold revisionId rowId; omega
  have absent : revisionId host time ∉ host.present := by
    intro h
    have bound := below host h
    unfold revisionId at bound
    omega
  simp only [withRead, Finset.mem_insert, rev, false_or]
  split <;> simp [row, absent]

variable {prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
  (member : Hosted.rule (S := S) (Γ := []) (star := star) N ∈ prog)
  (control time : Nat)

abbrev select :=
  NativeQuery.MatchKernel.Hosted.firing N member (withRead N host address view occurrence) control
    (rowId host occurrence) (revisionId host time) (freshId (withRead N host address view occurrence))

theorem stale_refused (stale : time ≠ view.clock) :
    ¬ (select N host address view occurrence member control time).Admits ReadFrames (withRead N host address view occurrence) :=
  Hosted.stale_refused N member (withRead N host address view occurrence) control (rowId host occurrence)
    (revisionId host time) (freshId (withRead N host address view occurrence))
    (stale_absent N host address view occurrence stale)

/-- Source matching in the addressed view is exactly admission of the
concrete versioned firing. The returned row uses the original stack and
template under a solution that restricts to the same caller. -/
theorem current_models {target : Interface.Frames.Frame S} {datum : ClosedTerm}
    (found : atTime view view.clock occurrence = some (occurrence, datum))
    (present : control ∈ host.present)
    (space pattern template stack : ReadBody host.frame)
    (waiting : host.label control = observe (Hosted.request N space pattern template stack))
    (caller : Assignment host.frame.arity target.arity) (value : ReadTerm target) :
    let state := withRead N host address view occurrence
    let f := select N host address view occurrence member control view.clock
    ((ReadFrames).Models caller host.knowledge ∧
      instantiate caller space = Rigid.includeTerm target.arity address ∧
      instantiate caller pattern = Rigid.includeTerm target.arity datum ∧
      observe (Hosted.returned N (instantiate caller template) (instantiate caller stack)) = value) ↔
    ∃ point : Assignment (f.result ReadFrames state).frame.arity target.arity,
      Assignment.compose point ((ReadExtensions).weaken f.ext) = caller ∧
      (ReadFrames).Models point (f.result ReadFrames state).knowledge ∧
      instantiateObservation point ((f.result ReadFrames state).label (freshId state)) = value := by
  have model := NativeQuery.MatchKernel.Hosted.models N member (withRead N host address view occurrence)
    control (rowId host occurrence) (revisionId host view.clock) (freshId (withRead N host address view occurrence))
    space pattern template stack (Rigid.includeTerm host.frame.arity address)
    (Rigid.includeTerm host.frame.arity datum) (Rigid.includeTerm host.frame.arity address)
    ((host_label N host address view occurrence present).trans waiting)
    (chosen_label N host address view occurrence found) (by simp [withRead]) caller value
  rw [Rigid.instantiate_include caller address, Rigid.instantiate_include caller datum] at model
  exact ⟨fun ⟨known, loc, fits, out⟩ => model.mp ⟨known, loc, loc, fits, out⟩,
    fun out => let result := model.mpr out; ⟨result.1, result.2.1, result.2.2.2⟩⟩

private theorem enabled_read {present : Finset Nat} {request row stamp output : Nat}
    (controlHere : request ∈ present) (rowHere : row ∈ present) (stampHere : stamp ∈ present)
    (controlRow : request ≠ row) (controlStamp : request ≠ stamp) (fresh : output ∉ present) :
    Enabled (fun _ : Nat => ()) present
      ((⟨[request], [row, stamp], [output]⟩ : Selection Nat).commit (T := Unit)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Selection.commit, controlHere]
  · simp [Selection.commit, Finset.insert_subset_iff, rowHere, stampHere]
  · simp [Selection.commit, controlRow, controlStamp]
  · simpa [Selection.commit] using fresh
  · simp [Selection.commit]

theorem enabled (present : control ∈ host.present) {datum : ClosedTerm}
    (found : atTime view view.clock occurrence = some (occurrence, datum)) :
    let state := withRead N host address view occurrence
    Enabled (fun _ : Nat => ()) state.present
      ((⟨[control], [rowId host occurrence, revisionId host view.clock], [freshId state]⟩ : Selection Nat).commit (T := Unit)) := by
  have small := below host present
  have diffRow : control ≠ rowId host occurrence := by unfold rowId; omega
  have diffRev : control ≠ revisionId host view.clock := by unfold revisionId; omega
  apply enabled_read _ _ _ diffRow diffRev (freshId_not_mem _)
  · simp [withRead, found, present]
  · simp [withRead, found]
  · simp [withRead]

theorem fires_iff {datum : ClosedTerm} (found : atTime view view.clock occurrence = some (occurrence, datum))
    (present : control ∈ host.present) (space pattern template stack : ReadBody host.frame)
    (waiting : host.label control = observe (Hosted.request N space pattern template stack)) :
    (select N host address view occurrence member control time).Admits ReadFrames (withRead N host address view occurrence) ↔
      time = view.clock ∧
      ∃ (target : Interface.Frames.Frame S) (caller : Assignment host.frame.arity target.arity),
        (ReadFrames).Models caller host.knowledge ∧
        instantiate caller space = Rigid.includeTerm target.arity address ∧
        instantiate caller pattern = Rigid.includeTerm target.arity datum := by
  by_cases current : time = view.clock
  · subst time
    simp only [eq_self, true_and, NativeQuery.MatchKernel.Hosted.admitted_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, target, point, models⟩
      let state := withRead N host address view occurrence
      let f := select N host address view occurrence member control view.clock
      let caller : Assignment host.frame.arity target.arity := Assignment.compose point ((ReadExtensions).weaken f.ext)
      have answer := (current_models N host address view occurrence member control found present
        space pattern template stack waiting caller
        (instantiateObservation point ((f.result ReadFrames state).label (freshId state)))).mpr
        ⟨point, rfl, models, rfl⟩
      exact ⟨target, caller, answer.1, answer.2.1, answer.2.2.1⟩
    · rintro ⟨target, caller, known, loc, fits⟩
      obtain ⟨point, _, model, _⟩ := (current_models N host address view occurrence member control found
        present space pattern template stack waiting caller _).mp ⟨known, loc, fits, rfl⟩
      exact ⟨enabled N host address view occurrence control present found, target, point, model⟩
  · simp only [current, false_and, iff_false]
    exact stale_refused N host address view occurrence member control time current

end Ground

theorem issued_request {P : SourceLanguage.Program mkeys [] () MTy} (clause : Clause)
    {before host : HostState MSig} {input output : Nat}
    (issued : FiresAt (translate mettaNodes P) (schema mettaNodes clause.equation)
      before input host output) :
    ∃ space pattern template stack : Body host.frame,
      host.label output = observe (Hosted.request mettaNodes space pattern template stack) := by
  obtain ⟨⟨code, inProgram, extension, opening, positions, seen⟩,
    codeEq, admitted, _, made, rfl⟩ := issued
  change code = schema mettaNodes clause.equation at codeEq
  subst code
  let f : RuleSyntax.Firing Nat E (translate mettaNodes P) before.frame :=
    ⟨schema mettaNodes clause.equation, inProgram, extension, opening, positions, seen⟩
  let requestLabel : Body (schema mettaNodes clause.equation).locals :=
    Hosted.request mettaNodes (symAt "&self") (instantiate asUnknowns clause.pattern)
      (instantiate asUnknowns clause.template) schemaStack
  have published : (output, instantiateObservation opening (observe requestLabel)) ∈
      f.selection.made.zip (f.opened X).produce := by
    change positions.made = [output] at made
    change (output, instantiateObservation opening (observe requestLabel)) ∈
      positions.made.zip [instantiateObservation opening (observe requestLabel)]
    rw [made]
    exact List.mem_singleton_self _
  have label := f.result_label_made admitted.1 published
  refine ⟨instantiate opening (symAt "&self"), instantiate opening (instantiate asUnknowns clause.pattern),
    instantiate opening (instantiate asUnknowns clause.template), instantiate opening schemaStack, ?_⟩
  change (f.result X before).label output = _
  exact label.trans (congrArg observe (Hosted.instantiate_request mettaNodes (B := E.target extension) opening _ _ _ _))

/-- After an issued request is hosted, the versioned read needs exactly the
original caller's solution of the match problem. No intermediate state is
reconstructed from the printed result. -/
theorem after_call {P : SourceLanguage.Program mkeys [] () MTy} {n : Nat}
    {before host : HostState MSig} {input output time : Nat}
    (clause : Clause) (datum : MClosed) (view : Store MClosed) (occurrence : Nat)
    (found : atTime view view.clock occurrence = some (occurrence, datum))
    (issued : FiresAt (translate mettaNodes P) (schema mettaNodes clause.equation) before input host output)
    (store : List (Constraint mkeys [] ())) (pattern template : MData) (frames : List (Frame mkeys [] () MTy))
    (hosted : Represents mettaNodes P n (requesting store pattern template frames) host output)
    {prog : RuleSyntax.Program Tm} (member : (Hosted.rule mettaNodes) ∈ prog) :
    (select mettaNodes host (csym "&self") view occurrence member output time).Admits X
      (withRead mettaNodes host (csym "&self") view occurrence) ↔
    time = view.clock ∧ Solvable (store ++ [(pattern, Rigid.includeTerm (fam mkeys) datum)]) := by
  have present : output ∈ host.present := by rw [hosted.present]; exact Finset.mem_insert_self _ _
  obtain ⟨sp, pat, body, stack, waiting⟩ := issued_request clause issued
  rw [fires_iff mettaNodes host (csym "&self") view occurrence member output time found present sp pat body stack waiting]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨target, caller, known, location, fits⟩
    have read : rowReads host output target (requestObservation (Rigid.includeTerm target.arity datum)
        (instantiate caller body) (instantiate caller stack)) := by
      refine ⟨caller, known, ?_⟩
      rw [waiting]
      change observe (instantiate caller (Hosted.request mettaNodes sp pat body stack)) = _
      rw [Hosted.instantiate_request mettaNodes (B := target), location, fits]
      rfl
    obtain ⟨point, solved, matching, _, _⟩ := (request_readback hosted _ _ _).mp read
    refine ⟨target.Names, target.arity, point, (models_append point _ _).mpr ⟨solved, ?_⟩⟩
    exact (models_singleton point _).mpr (matching.trans (Rigid.instantiate_include point datum).symm)
  · rintro ⟨names, arity, point, solved⟩
    let target : Interface.Frames.Frame MSig := ⟨names, arity⟩
    obtain ⟨known, matchEq⟩ := (models_append point _ _).mp solved
    have fits : instantiate point pattern = Rigid.includeTerm target.arity datum :=
      ((models_singleton point _).mp matchEq).trans (Rigid.instantiate_include point datum)
    obtain ⟨caller, lawful, same⟩ := (request_readback (B := target) hosted
      (Rigid.includeTerm target.arity datum) (instantiate point template)
      (encStack mettaNodes (instantiate point) frames)).mpr ⟨point, known, fits, rfl, rfl⟩
    rw [waiting] at same
    change observe (instantiate caller (Hosted.request mettaNodes sp pat body stack)) = _ at same
    rw [Hosted.instantiate_request mettaNodes (B := target)] at same
    obtain ⟨location, matched, _, _⟩ := Hosted.request_inj mettaNodes (observe_injective same)
    exact ⟨target, caller, lawful, location, matched⟩

section Schematic

open RuleSyntax.SchematicRows (Closure)
open RuleSyntax.Contextual (weakenNames canonicalOpening)
open RuleSyntax.BindingIntegration.Rows
open RuleSyntax.SchematicRows.HeldReadGenericSources (hosted)

variable {S : Signature} {star : S.Srt} (N : Nodes S [] star)

local notation "ClosedTerm" => Term S [] star
local notation "ReadBody" => Hosted.BodyAt [] star
local notation "ReadTerm" => RuleSyntax.Contextual.Terms S
local notation "ReadFrames" => Interface.Frames.contextual S
local notation "ReadExtensions" => RuleSyntax.Contextual.declarations S

private def revisionState (host : HostState S) (address : ClosedTerm) (time : Nat) : HostState S :=
  withRead N host address ⟨time, 0, fun _ => none⟩ 0

def closureAt {F : Interface.Frames.Frame S} (view : Store Nat)
    (catalogue : Nat → Closure ReadTerm F) (i : Nat) : Closure ReadTerm F :=
  catalogue (((atTime view view.clock i).map Prod.snd).getD 0)

theorem closureAt_exact {F : Interface.Frames.Frame S} (view : Store Nat)
    (catalogue : Nat → Closure ReadTerm F) {i key : Nat} (present : (i, key) ∈ liveRows view) :
    closureAt view catalogue i = catalogue key := by
  simp [closureAt, ((mem_liveRows view i key).mp present).2]

variable (host : HostState S) (address : Term S [] star) (view : Store Nat)
  (catalogue : Nat → Closure (RuleSyntax.Contextual.Terms S) host.frame) (occurrence : Nat)

/-- First materialize the selected persistent schema in its own fresh
contextual declarations. Its code and capture arguments come from the
same live occurrence inventory as the version check. -/
abbrev openSchema :=
  activation (revisionState N host address view.clock) (liveIds view) (closureAt view catalogue)
    occurrence (rowId host occurrence)

abbrev openedState := (openSchema N host address view catalogue occurrence).result ReadFrames |>.toState

variable {prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)}
  (member : Hosted.rule (S := S) (Γ := []) (star := star) N ∈ prog) (control time : Nat)

abbrev readSchema :=
  let s := openedState N host address view catalogue occurrence
  Hosted.firing N member s control (rowId host occurrence) (revisionId host time) (freshId s)

private theorem opening_fresh :
    rowId host occurrence ∉ (revisionState N host address view.clock).present := by
  have different : rowId host occurrence ≠ revisionId host view.clock := by unfold rowId revisionId; omega
  have absent : rowId host occurrence ∉ host.present := by
    intro here
    have small := below host here
    unfold rowId at small
    omega
  simp [revisionState, withRead, atTime, different, absent]

theorem stale_schema_read (stale : time ≠ view.clock) :
    ¬ (readSchema N host address view catalogue occurrence member control time).Admits ReadFrames
      (openedState N host address view catalogue occurrence) := by
  apply Hosted.stale_refused N
  rw [activation_present]
  have absent := stale_absent N host address (⟨view.clock, 0, fun _ => none⟩ : Store ClosedTerm) 0 stale
  change revisionId host time ∉ (revisionState N host address view.clock).present at absent
  have different : revisionId host time ≠ rowId host occurrence := by unfold revisionId rowId; omega
  simp [absent, different]

private theorem opened_labels {key : Nat}
    (here : (occurrence, key) ∈ liveRows view) (present : control ∈ host.present)
    (space pattern template stack : ReadBody host.frame)
    (waiting : host.label control = observe (Hosted.request N space pattern template stack))
    (value : ReadBody (catalogue key).schema.locals)
    (label : (catalogue key).schema.value = observe
      (Hosted.fact N (Rigid.includeTerm (catalogue key).schema.locals.arity address) value)) :
    let s := openedState N host address view catalogue occurrence
    let locals := (closureAt view catalogue occurrence).schema.locals
    let lift := weakenNames S host.frame locals
    let loc : ReadBody s.frame := Rigid.includeTerm s.frame.arity address
    s.label control = observe (Hosted.request N (instantiate lift space) (instantiate lift pattern)
      (instantiate lift template) (instantiate lift stack)) ∧
    s.label (revisionId host view.clock) = observe (Hosted.revision N loc) ∧
    ∃ body : ReadBody locals, s.label (rowId host occurrence) = observe
      (Hosted.fact N loc (instantiate (canonicalOpening S host.frame locals) body)) := by
  let base := revisionState N host address view.clock
  let s := openedState N host address view catalogue occurrence
  let lift := weakenNames S host.frame (closureAt view catalogue occurrence).schema.locals
  let opened := canonicalOpening S host.frame (closureAt view catalogue occurrence).schema.locals
  have held := closureAt_exact view catalogue here
  have small := below host present
  have diffRow : control ≠ rowId host occurrence := by unfold rowId; omega
  have baseControl : base.label control = host.label control :=
    host_label N host address (⟨view.clock, 0, fun _ => none⟩ : Store ClosedTerm) 0 present
  have baseStamp : base.label (revisionId host view.clock) =
      observe (Hosted.revision N (Rigid.includeTerm host.frame.arity address)) := by
    simp [base, revisionState, withRead]
  let loc : ReadBody s.frame := Rigid.includeTerm s.frame.arity address
  have issued : s.label control = observe (Hosted.request N (instantiate lift space)
      (instantiate lift pattern) (instantiate lift template) (instantiate lift stack)) := by
    rw [activation_label_other _ _ _ _ _ _ diffRow, baseControl, waiting]
    exact congrArg observe (Hosted.instantiate_request N (B := s.frame) lift _ _ _ _)
  have version : s.label (revisionId host view.clock) = observe (Hosted.revision N loc) := by
    have different : revisionId host view.clock ≠ rowId host occurrence := by unfold rowId revisionId; omega
    rw [activation_label_other _ _ _ _ _ _ different, baseStamp]
    change observe (instantiate lift (Hosted.revision N (Rigid.includeTerm host.frame.arity address))) = _
    rw [Hosted.instantiate_revision N (B := s.frame), Rigid.instantiate_include lift address]
    rfl
  obtain ⟨body, stored⟩ : ∃ body : ReadBody (closureAt view catalogue occurrence).schema.locals,
      (closureAt view catalogue occurrence).schema.value =
        observe (Hosted.fact N (Rigid.includeTerm (closureAt view catalogue occurrence).schema.locals.arity address) body) := by
    rw [held]
    exact ⟨value, label⟩
  have rowLabel : s.label (rowId host occurrence) = observe (Hosted.fact N loc (instantiate opened body)) := by
    rw [activation_output, stored]
    change observe (instantiate opened (Hosted.fact N (Rigid.includeTerm _ address) body)) = _
    rw [Hosted.instantiate_fact N (B := s.frame), Rigid.instantiate_include opened address]
    rfl
  exact ⟨issued, version, body, rowLabel⟩

/-- The two-firing result projects exactly to the chosen caller assignment,
including names that are absent from the selected pattern. The template and
stack are interpreted by that same assignment. -/
theorem schema_answer_models {target : Interface.Frames.Frame S} {key : Nat}
    (here : (occurrence, key) ∈ liveRows view) (present : control ∈ host.present)
    (space pattern template stack : ReadBody host.frame)
    (waiting : host.label control = observe (Hosted.request N space pattern template stack))
    (value : ReadBody (catalogue key).schema.locals)
    (label : (catalogue key).schema.value = observe
      (Hosted.fact N (Rigid.includeTerm (catalogue key).schema.locals.arity address) value))
    (wellFormed : (catalogue key).WellFormed)
    (caller : Assignment host.frame.arity target.arity) (returnedValue : ReadTerm target) :
    let s := openedState N host address view catalogue occurrence
    let f := readSchema N host address view catalogue occurrence member control view.clock
    let lift := weakenNames S host.frame (closureAt view catalogue occurrence).schema.locals
    ((ReadFrames).Models caller host.knowledge ∧ instantiate caller space = Rigid.includeTerm target.arity address ∧
      (catalogue key).ReadsAt ReadFrames caller (observe (Hosted.fact N (Rigid.includeTerm target.arity address)
        (instantiate caller pattern))) ∧
      observe (Hosted.returned N (instantiate caller template) (instantiate caller stack)) = returnedValue) ↔
    ∃ point : Assignment (f.result ReadFrames s).frame.arity target.arity,
      (Assignment.compose point ((ReadExtensions).weaken f.ext)).compose lift = caller ∧
      (ReadFrames).Models point (f.result ReadFrames s).knowledge ∧
      instantiateObservation point ((f.result ReadFrames s).label (freshId s)) = returnedValue := by
  dsimp only
  let base := revisionState N host address view.clock
  let s := openedState N host address view catalogue occurrence
  let f := readSchema N host address view catalogue occurrence member control view.clock
  let locals := (closureAt view catalogue occurrence).schema.locals
  let lift := weakenNames S host.frame locals
  let loc : ReadBody s.frame := Rigid.includeTerm s.frame.arity address
  let opened := canonicalOpening S host.frame locals
  let reply := observe (Hosted.fact N (Rigid.includeTerm target.arity address) (instantiate caller pattern))
  have held := closureAt_exact view catalogue here
  have well : (closureAt view catalogue occurrence).WellFormed := held ▸ wellFormed
  obtain ⟨issued, version, body, rowLabel⟩ :=
    opened_labels N host address view catalogue occurrence control here present space pattern template stack
      waiting value label
  have materialize := activation_models_iff base (liveIds view) (closureAt view catalogue)
    occurrence (rowId host occurrence) well caller reply
  have read (u : Assignment s.frame.arity target.arity) :=
    Hosted.models N member s control (rowId host occurrence) (revisionId host view.clock)
      (freshId s) _ _ _ _ loc (instantiate opened body) loc issued rowLabel version u returnedValue
  have lifted (u : Assignment s.frame.arity target.arity) (same : Assignment.compose u lift = caller)
      (term : ReadBody host.frame) : instantiate u (instantiate lift term) = instantiate caller term :=
    (instantiate_comp lift u term).trans (congrArg (instantiate · term) same)
  constructor
  · rintro ⟨known, located, reads, valueEq⟩
    have readFrom : (closureAt view catalogue occurrence).ReadsAt ReadFrames caller reply := by rwa [held]
    obtain ⟨u, same, openKnown, rowRead⟩ := materialize.mp ⟨known, readFrom⟩
    change instantiateObservation u (s.label (rowId host occurrence)) = reply at rowRead
    rw [rowLabel] at rowRead
    change observe (instantiate u (Hosted.fact N loc (instantiate opened body))) = reply at rowRead
    rw [Hosted.instantiate_fact N (B := target)] at rowRead
    have fits := (vec2_inj (N.args_eq (observe_injective rowRead))).2.symm
    have locates : instantiate u (instantiate lift space) = instantiate u loc := by
      exact (lifted u same space).trans (located.trans (Rigid.instantiate_include u address).symm)
    have returns : observe (Hosted.returned N (instantiate u (instantiate lift template))
        (instantiate u (instantiate lift stack))) = returnedValue := by
      rwa [lifted u same template, lifted u same stack]
    obtain ⟨point, restrict, model, made⟩ := (read u).mp
      ⟨openKnown, locates, locates, (lifted u same pattern).trans fits, returns⟩
    have restrict' : Assignment.compose point ((ReadExtensions).weaken f.ext) = u := restrict
    exact ⟨point, (congrArg (fun g => Assignment.compose g lift) restrict').trans same, model, made⟩
  · rintro ⟨point, same, models, made⟩
    let u : Assignment s.frame.arity target.arity := Assignment.compose point ((ReadExtensions).weaken f.ext)
    obtain ⟨openKnown, located, _, fits, valueEq⟩ := (read u).mpr ⟨point, rfl, models, made⟩
    have rowRead : instantiateObservation u (s.label (rowId host occurrence)) = reply := by
      rw [rowLabel]
      change observe (instantiate u (Hosted.fact N loc (instantiate opened body))) = reply
      rw [Hosted.instantiate_fact N (B := target), Rigid.instantiate_include, ← fits, lifted u same pattern]
    obtain ⟨known, reads⟩ := materialize.mpr ⟨u, same, openKnown, rowRead⟩
    rw [held] at reads
    change observe (Hosted.returned N (instantiate u (instantiate lift template))
      (instantiate u (instantiate lift stack))) = returnedValue at valueEq
    rw [lifted u same template, lifted u same stack] at valueEq
    exact ⟨known, (lifted u same space).symm.trans (located.trans (Rigid.instantiate_include u address)),
      reads, valueEq⟩

private theorem schema_read_enabled (present : control ∈ host.present) :
    Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Enabled
      (fun _ : Nat => ()) (openedState N host address view catalogue occurrence).present
      (⟨[control], [rowId host occurrence, revisionId host view.clock],
        [freshId (openedState N host address view catalogue occurrence)]⟩ : Selection Nat).commit := by
  let base := revisionState N host address view.clock
  let s := openedState N host address view catalogue occurrence
  have controlHere : control ∈ base.present := by simp [base, revisionState, withRead, atTime, present]
  have stampHere : revisionId host view.clock ∈ base.present := by simp [base, revisionState, withRead]
  have small := below host present
  have diffRow : control ≠ rowId host occurrence := by unfold rowId; omega
  have diffStamp : control ≠ revisionId host view.clock := by unfold revisionId; omega
  exact enabled_read (present := s.present) (request := control)
    (row := rowId host occurrence) (stamp := revisionId host view.clock)
    (output := freshId s)
    (by rw [activation_present]; exact Finset.mem_union_left _ controlHere)
    (by rw [activation_present]; simp)
    (by rw [activation_present]; exact Finset.mem_union_left _ stampHere)
    diffRow diffStamp (freshId_not_mem s)

/-- The two firings reflect the selected occurrence's actual closure reading.
All capture constraints come from that closure and the caller's knowledge. -/
theorem schema_admits_iff {key : Nat}
    (here : (occurrence, key) ∈ liveRows view) (present : control ∈ host.present)
    (space pattern template stack : ReadBody host.frame)
    (waiting : host.label control = observe (Hosted.request N space pattern template stack))
    (value : ReadBody (catalogue key).schema.locals)
    (label : (catalogue key).schema.value = observe
      (Hosted.fact N (Rigid.includeTerm (catalogue key).schema.locals.arity address) value))
    (wellFormed : (catalogue key).WellFormed) :
    let s := openedState N host address view catalogue occurrence
    ((openSchema N host address view catalogue occurrence).Admits ReadFrames ∅ ∧
      (readSchema N host address view catalogue occurrence member control time).Admits ReadFrames s) ↔
    time = view.clock ∧
      ∃ (target : Interface.Frames.Frame S) (caller : Assignment host.frame.arity target.arity),
        (ReadFrames).Models caller host.knowledge ∧ instantiate caller space = Rigid.includeTerm target.arity address ∧
        (catalogue key).ReadsAt ReadFrames caller (observe (Hosted.fact N (Rigid.includeTerm target.arity address)
          (instantiate caller pattern))) := by
  by_cases current : time = view.clock
  · subst time
    simp only [eq_self, true_and]
    let base := revisionState N host address view.clock
    let s := openedState N host address view catalogue occurrence
    let f := readSchema N host address view catalogue occurrence member control view.clock
    let lift := weakenNames S host.frame (closureAt view catalogue occurrence).schema.locals
    have held := closureAt_exact view catalogue here
    have well : (closureAt view catalogue occurrence).WellFormed := held ▸ wellFormed
    have premises {target : Interface.Frames.Frame S} (caller : Assignment host.frame.arity target.arity)
        (result : ReadTerm target) :=
      schema_answer_models N host address view catalogue occurrence member control here present
        space pattern template stack waiting value label wellFormed caller result
    constructor
    · rintro ⟨_, read⟩
      obtain ⟨target, point, solved⟩ := read.2.2.1
      let caller : Assignment host.frame.arity target.arity :=
        (Assignment.compose point ((ReadExtensions).weaken f.ext)).compose lift
      obtain ⟨known, addressAt, reads, _⟩ :=
        (premises caller _).mpr ⟨point, rfl, solved, rfl⟩
      exact ⟨target, caller, known, addressAt, reads⟩
    · rintro ⟨target, caller, known, locates, reads⟩
      obtain ⟨point, _, model, _⟩ := (premises caller _).mp ⟨known, locates, reads, rfl⟩
      have reading := show (closureAt view catalogue occurrence).ReadsAt ReadFrames caller _ by rwa [held]
      refine ⟨activation_admitted_of_reading base (liveIds view) (closureAt view catalogue)
        occurrence (rowId host occurrence) ((mem_liveIds view occurrence).mpr ⟨key, here⟩)
        (opening_fresh N host address view occurrence) well caller known _ reading, ?_⟩
      exact (Hosted.admitted_iff ..).mpr
        ⟨schema_read_enabled N host address view catalogue occurrence control present, target, point, model⟩
  · simp only [current, false_and, iff_false]
    exact fun both => stale_schema_read N host address view catalogue occurrence member control time current both.2

open Classical in
/-- The complete stamped traversal selects exactly the admitted schematic reads
in slot order. The equality concerns occurrence lists, including duplicate
payloads and repeated uses of one schema. -/
theorem schema_collect_exact (host : HostState S) (address : ClosedTerm)
    (view : Store Nat) (catalogue : Nat → Closure ReadTerm host.frame)
    {prog : RuleSyntax.Program ReadTerm} (member : (Hosted.rule N) ∈ prog)
    (control time : Nat) (present : control ∈ host.present)
    (space pattern template stack : ReadBody host.frame)
    (waiting : host.label control = observe (Hosted.request N space pattern template stack))
    (located : ∀ i key, (i, key) ∈ liveRows view → (catalogue key).WellFormed ∧
      ∃ body : ReadBody (catalogue key).schema.locals, (catalogue key).schema.value =
        observe (Hosted.fact N (Rigid.includeTerm (catalogue key).schema.locals.arity address) body)) :
    (liveRows view).filter (fun (i, _) => decide
      ((openSchema N host address view catalogue i).Admits ReadFrames ∅ ∧
        (readSchema N host address view catalogue i member control time).Admits ReadFrames
          (openedState N host address view catalogue i))) =
    (liveRows view).filter (fun (_, key) => decide (time = view.clock ∧
      ∃ (target : Interface.Frames.Frame S) (caller : Assignment host.frame.arity target.arity),
        (ReadFrames).Models caller host.knowledge ∧ instantiate caller space = Rigid.includeTerm target.arity address ∧
        (catalogue key).ReadsAt ReadFrames caller (observe (Hosted.fact N (Rigid.includeTerm target.arity address)
          (instantiate caller pattern))))) := by
  apply List.filter_congr
  rintro ⟨i, key⟩ here
  obtain ⟨wellFormed, body, label⟩ := located i key here
  have same := schema_admits_iff N host address view catalogue i member control time here
    present space pattern template stack waiting body label wellFormed
  simp only [same]

end Schematic

end Versioned

namespace Edges
def x := foD [] [0] 0
def tag := foD [] [1] 0
def y := foD [] [1] 1
def q (v : MData) := tuple [sym "q", v]
def edge (u v : MData) := tuple [sym "edge", u, v]
def clause : Clause := ⟨[1], q tag, edge tag y, y⟩
def fact : Row mkeys [] () := ⟨edge (sym "a") (sym "b"), []⟩
abbrev clauses := [clause, clause]
abbrev facts := [fact, fact]
noncomputable abbrev bag := answers clauses facts (q x)

private theorem admitted (i : Origin clauses facts) : Fires clauses facts (q x) i := by
  apply (fires_iff ..).mpr
  · refine ⟨Empty, noNames, closeNames [(([], [0], 0), csym "a"),
      (([0], [1], 0), csym "a"), (([0], [1], 1), csym "b")] (csym "unused"), ?_⟩
    rcases i with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    change a < 2 at ha
    change b < 2 at hb
    interval_cases a <;> interval_cases b <;> decide +revert
  · intro t ht n hn
    simp [Comp.data] at ht
    subst t
    have name : n = fo [] [0] 0 := by simpa [q, x, tuple, tupleArgs, sym, foD, support, supportArgs] using hn
    rw [name]

section CurrentView

open Mettapedia.Machines.Cursor.StampedSnapshots
open NativeQuery.MatchKernel (X E Tm)

private def closedFact := ctuple [csym "edge", csym "a", csym "b"]
private def view : Store MClosed := add (add empty closedFact) closedFact
private def readProgram : RuleSyntax.Program Tm :=
  translate mettaNodes (program clauses) ∪ {(NativeQuery.MatchKernel.Hosted.rule mettaNodes)}
private theorem readRule : (NativeQuery.MatchKernel.Hosted.rule mettaNodes) ∈ readProgram :=
  .inr (Set.mem_singleton _)

/-- Each counted equation origin feeds a versioned read of its selected
physical fact into the same scoped request and caller continuation. -/
theorem versioned_occurrences (i : Origin clauses facts) :
    let startState := start mettaNodes (program clauses) (.apply (q x))
    let control := freshId startState
    ∃ host, HeldFires mettaNodes (program clauses) (origin mettaNodes (.eqn i.1)) startState
        (program clauses).equations.length host control ∧
      ((Versioned.select mettaNodes host (csym "&self") view i.2 readRule control view.clock).Admits X
        (Versioned.withRead mettaNodes host (csym "&self") view i.2)) ∧
      ¬ (Versioned.select mettaNodes host (csym "&self") (add view (csym "unrelated")) i.2 readRule control view.clock).Admits X
        (Versioned.withRead mettaNodes host (csym "&self") (add view (csym "unrelated")) i.2) := by
  obtain ⟨⟨host, call, scope⟩, read⟩ := admitted i
  have found : atTime view view.clock i.2 = some (i.2.val, closedFact) := by
    rcases i with ⟨_, j⟩
    fin_cases j <;> rfl
  have code := heldFires_firesAt call
  have fromClause : (heldState mettaNodes (program clauses)
      (start mettaNodes (program clauses) (.apply (q x)))).codeOf
        (origin mettaNodes (.eqn i.1)) = schema mettaNodes clause.equation := by
    change heldRule mettaNodes (program clauses) i.1 = _
    rw [heldRule_lt (by exact i.1.isLt)]
    rcases i with ⟨j, k⟩
    fin_cases j <;> rfl
  rw [fromClause] at code
  have live := (NativeQuery.MatchKernel.admitted_iff_source ..).mp read
  have exactStore : Solvable (callStore clause (q x) ++
      [(opened clause.pattern, Rigid.includeTerm (fam mkeys) closedFact)]) := by
    rcases i with ⟨j, k⟩
    fin_cases j <;> fin_cases k <;> exact live
  have retained : Represents mettaNodes (program clauses) 1
      (requesting (callStore clause (q x)) (opened clause.pattern) (opened y) []) host
      (freshId (start mettaNodes (program clauses) (.apply (q x)))) := by
    rcases i with ⟨j, k⟩
    fin_cases j <;> exact scope
  refine ⟨host, call, (Versioned.after_call clause closedFact view i.2 found code _ _ _ _ retained readRule).mpr
    ⟨rfl, exactStore⟩, ?_⟩
  apply Versioned.stale_refused
  simp [add]

end CurrentView

theorem count_four : bag.rows.card = 4 := by
  classical
  have all : Finset.univ.filter (Fires clauses facts (q x)) = Finset.univ :=
    Finset.filter_true_of_mem (fun i _ => admitted i)
  simp [bag, answers, all]

def caller : Branch mkeys [] () MTy := ⟨[(x, sym "z")], .value x, [], []⟩

/-- All solutions agree on the value *and* its public capture even when the
captured value does not mention the caller variable. -/
theorem binding_images (i : Origin clauses facts) {V : Type} {arity : V → MetaArity MSig}
    (point : Assignment (fam mkeys) arity) (captured : Models point (answer clauses facts (q x) i).store) :
    instantiate point x = symAt "a" ∧ instantiate point (opened y) = symAt "b" := by
  have hc : clauses[i.1] = clause := by exact (show ∀ n : Fin 2, clauses[n] = clause by intro n; fin_cases n <;> rfl) i.1
  have hf : facts[i.2] = fact := by exact (show ∀ n : Fin 2, facts[n] = fact by intro n; fin_cases n <;> rfl) i.2
  simp only [answer, hc, hf] at captured
  have applied := captured _ (List.mem_cons_self ..)
  have selected := captured _ (List.Mem.tail _ (List.mem_singleton_self _))
  change tupleAt [symAt "q", instantiate point (opened tag)] = tupleAt [symAt "q", instantiate point x] at applied
  change tupleAt [symAt "edge", instantiate point (opened tag), instantiate point (opened y)] =
    tupleAt [symAt "edge", symAt "a", symAt "b"] at selected
  have callArg := (tuple2_inj applied).2
  have edgeArg := (tuple3_inj selected).2.1
  exact ⟨callArg.symm.trans edgeArg, (tuple3_inj selected).2.2⟩

private theorem incompatible (i : Origin clauses facts) :
    ¬ Solvable (AnswerCollection.resume (D := D) caller (answer clauses facts (q x) i)).store := by
  rintro ⟨V, arity, point, model⟩
  obtain ⟨outer, captured⟩ := (AnswerCollection.resume_models point _ _).mp model
  have hx := outer _ (List.mem_singleton_self _)
  have clash : (symAt (target := arity) "z") = symAt "a" := hx.symm.trans (binding_images i point captured).1
  injection clash with _ _ op
  simp at op

theorem reflect_count_zero : ((bag.reflect (world facts) caller).answers (D := D)).card = 0 := by
  classical
  have empty : ((bag.reflect (world facts) caller).branches.filter
      (fun b => b.Finished (D := D) ∧ Solvable b.store)) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro b member h
    change b ∈ bag.rows.map (AnswerCollection.resume caller) at member
    obtain ⟨cap, hcap, rfl⟩ := Multiset.mem_map.mp member
    unfold bag answers at hcap
    dsimp only at hcap
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hcap
    exact incompatible i h.2
  simp only [Config.answers, empty, Multiset.map_zero, Multiset.card_zero]
/-- Independent execution of the authored match body by the source moves.
The two queries run at different fresh scopes. Their selected rows are closed. -/
abbrev sourceEq := clause.equation
variable (sourceP : SourceLanguage.Program mkeys [] () MTy)
private abbrev W := world facts
private abbrev called := callBranch D 0 [] (q x) [] [] sourceEq
private abbrev snapshot := answer clauses facts (q x) (0, 0)
private abbrev returning : Branch mkeys [] () MTy := { snapshot with focus := .eval (.ret (opened y)) }

private theorem snapshot_live : Solvable snapshot.store :=
  (NativeQuery.MatchKernel.admitted_iff_source ..).mp (admitted (0, 0)).2

private theorem called_live : Solvable called.store := by
  obtain ⟨V, decl, σ, model⟩ := snapshot_live
  exact ⟨V, decl, σ, ((models_append σ _ _).mp model).1⟩

private theorem query_move (w : World mkeys [] ()) (factsAt : w.spaces (csym "&self") = ↑facts) :
    Move D sourceP (fun n => cnum n) w called w.fresh ({returning, returning}) := by
  have addressed : Determines called.store (sym "&self") (csym "&self") :=
    ⟨called_live, fun _ _ _ => rfl⟩
  have step := Move.query (D := D) (P := sourceP) (supply := (fun n => cnum n)) w called.store (sym "&self")
    (opened clause.pattern) (.ret (opened y)) [] [] (csym "&self") addressed
  rw [factsAt] at step
  exact step

theorem source_run (definitions : sourceP.equations = [sourceEq, sourceEq]) :
    Runs D sourceP (fun n => cnum n) (Config.initial W.spaces (.apply (q x)))
      ⟨W.fresh.fresh.fresh, {snapshot, snapshot, snapshot, snapshot}⟩ := by
  have applyMove := Move.apply (D := D) (P := sourceP) (supply := (fun n => cnum n)) W [] (q x) [] []
    ⟨sourceEq, definitions ▸ List.mem_cons_self, called_live⟩
  have callStep : SourceLanguage.Step D sourceP (fun n => cnum n)
      (Config.initial W.spaces (.apply (q x))) ⟨W.fresh, {called, called}⟩ :=
    by
      have step := Step.single (D := D) live_nil applyMove
      rw [definitions] at step
      exact step
  have sameRows : W.spaces (csym "&self") = ↑facts := by simp [W, world]
  have first : SourceLanguage.Step D sourceP (fun n => cnum n) ⟨W.fresh, {called, called}⟩
      ⟨W.fresh.fresh, {called, returning, returning}⟩ :=
    Step.of_eq (rest := {called}) rfl (by
      change called ::ₘ ({returning, returning} : Multiset _) = {returning, returning} + {called}
      rw [add_comm, Multiset.singleton_add])
      called_live (query_move sourceP _ sameRows)
  have second : SourceLanguage.Step D sourceP (fun n => cnum n)
      ⟨W.fresh.fresh, {called, returning, returning}⟩
      ⟨W.fresh.fresh.fresh, {returning, returning, returning, returning}⟩ :=
    Step.of_eq (rest := {returning, returning}) rfl rfl called_live (query_move sourceP _ sameRows)
  have finish : SourceLanguage.Step D sourceP (fun n => cnum n)
      ⟨W.fresh.fresh.fresh, {returning}⟩ ⟨W.fresh.fresh.fresh, {snapshot}⟩ :=
    Step.single snapshot_live (.ret _ _ _ _ _)
  have replace (n : Nat) : Runs D sourceP (fun n => cnum n)
      ⟨W.fresh.fresh.fresh, Multiset.replicate n returning⟩
      ⟨W.fresh.fresh.fresh, Multiset.replicate n snapshot⟩ := by
    induction n with
    | zero => exact .refl
    | succ n ih =>
      have firstOne := finish.frame (Multiset.replicate n returning)
      have remaining := ih.frame ({snapshot} : Multiset _)
      rw [add_comm (Multiset.replicate n returning), add_comm (Multiset.replicate n snapshot)] at remaining
      simp only [Multiset.singleton_add] at remaining
      simp only [Multiset.singleton_add] at firstOne
      simpa only [Multiset.replicate_succ] using (Relation.ReflTransGen.single firstOne).trans remaining
  exact (((Relation.ReflTransGen.single callStep).tail first).tail second).trans (by simpa only [Multiset.replicate_succ, Multiset.replicate_zero, Multiset.cons_zero, Multiset.insert_eq_cons] using replace 4)

/-- The source collector reaches the same full bag as the counted transform
readout, down to its captured equations. -/
theorem source_reifies_target (definitions : sourceP.equations = [sourceEq, sourceEq]) :
    ∃ final, AnswerCollection.CollectorRuns D sourceP (fun n => cnum n)
        (AnswerCollection.State.initial (Config.initial W.spaces (.apply (q x)))) final ∧
      ∃ valid, AnswerCollection.reify final valid = some bag := by
  classical
  have rowsEq : bag.rows = Multiset.replicate 4 snapshot := by
    rw [← count_four]
    apply Multiset.eq_replicate_of_mem
    intro b member
    unfold bag answers at member
    dsimp only at member
    obtain ⟨⟨i, j⟩, _, rfl⟩ := Multiset.mem_map.mp member
    fin_cases i <;> fin_cases j <;> rfl
  let work := List.replicate 4 snapshot
  obtain ⟨final, path, valid, b, closed, rowCount⟩ := AnswerCollection.collect_finished
    (D := D) W.fresh.fresh.fresh work (by
      intro a ha
      obtain rfl := (List.eq_of_mem_replicate ha)
      exact ⟨rfl, _, rfl⟩)
  have lifted {before after : Config mkeys [] () MTy} (r : Runs D sourceP (fun n => cnum n) before after) :
      AnswerCollection.CollectorRuns D sourceP (fun n => cnum n) (AnswerCollection.State.initial before)
        (AnswerCollection.State.initial after) :=
    r.lift AnswerCollection.State.initial (fun _ _ step => AnswerCollection.CollectorStep.drive [] 0 step)
  have actual := lifted (source_run sourceP definitions)
  refine ⟨final, actual.trans (Relation.ReflTransGen.mono (fun _ _ step => AnswerCollection.CollectorStep.admin step) _ _ path), valid, ?_⟩
  rw [closed]
  have same : b.rows = bag.rows := by
    rw [rowCount, rowsEq]
    change (Multiset.replicate 4 snapshot).filter _ = _
    apply Multiset.filter_eq_self.mpr
    intro a ha
    rw [Multiset.eq_of_mem_replicate ha]
    exact snapshot_live
  cases b
  unfold bag answers at same ⊢
  congr 2

end Edges
end Query
end Mettapedia.Languages.MeTTa.ContextualTransform.TMeTTa
