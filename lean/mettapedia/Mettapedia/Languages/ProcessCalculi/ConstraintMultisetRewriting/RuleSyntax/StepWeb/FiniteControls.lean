import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteHosting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.CommControls

/-!
# The finite program: the manuscript's example, a second redex shape, and the controls

The step is the one-match step of a program at the one frame of structural substitution on patterns, with
the five choices stated in `FiniteComm`: a bag store, one match, guards asked after the firing's own tells
(the rules have none), a fixed set of rules beside the store, one store of knowledge. The program is the
three-rule `program` of `FiniteComm`, the same in every example below.

## The manuscript's example

`for((0) <- @0)0 | for(y <- @0)y`. Represented, the receiver is `for(y <- @0)@y` (`predot_receiver`); the
sender has no variable and is its own representation. The comm rule opened by `T1 ↦ t1, T2 ↦ t2, X ↦ x0,
K1 ↦ k1, K2 ↦ k2` is fresh there (`example_fresh`). Through `comm_one_firing_closed` the firing is admitted,
the manuscript's COMM gives `0 | @((0))`, and every solution reads identity `3` as `@((0))`
(`example_reads`). Kernel evaluation computes the result (`example_result`, `example_knowledge`), and a
solution exists (`example_solution`).

## A second redex shape, the same rule

`for(f(x) <- @0)x | for(f((0)) <- @0)0` is fired by the same rule of the same program
(`second_shape_comm`): the program does not depend on the redex.

## Controls

* **Pre-dotting** (`undotted_misreads`): with the receiver stored as written, `for(y <- @0)y`, the same
  firing is admitted, and every solution reads identity `3` as `(0)`, the value, not the manuscript's
  `@((0))`. The representation's quotes are needed by this program.
* **Residual principal bindings** (`nonground_principal_reading`, `nonground_two_readings`):
  `for(y <- @0)y | for(w <- @0)0` has no ground principal unifier, but is admitted. The completed
  principal binding reads its result as `@w`; two solutions instantiate it differently, as `@0` and
  as `@(@0)`. Groundness is not required for admission or this symbolic readback.
* **The variable convention** (`canary_misreads`): on the manuscript's canary
  `for(a <- @0)a | for(0 <- @0)a`, where the second input's free `a` is the first input's bound name, every
  solution reads the second made row as `0`: neither the literal, capturing reduct's `@0` nor the corrected
  reduct's free `a`.
* **First-order continuations** (`subst_node_misreads`): with the receiver's continuation an explicit
  substitution node `(bvar 0)[y/0]`, every solution reads the made row as `(bvar 0)[@((0))/0]`, which keeps
  the node; the manuscript's dot eliminates it and gives `@((0))`.

## The example through the correspondence

The example is a hosted process (`example_hostedProcess`) whose bag is ground-unifiable
(`example_groundUnifiable`); its COMM is a step of the bag presentation (`example_bagComm`); and from its
initial state, housekeeping firings and one communication reach a state that represents the parts of the
manuscript's reduct (`example_run`).

## What is not shown

Whether every finite program needs the representation's quotes: `undotted_misreads` is about this
program only.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteProgram.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero nQuote applyDot SC tProc demoChan)
open MeTTaOperationsComm (psubst pvars patternAction PSubst dotted GroundPrincipal storePVars firstOrder
  psubst_of_pvars_nil)
open Comm (X E renameBy ruleVars)
open Comm.Controls (zeroTerm y w sender receiver source unifier reduct start unifier_groundPrincipal
  example_manuscript)
open OneFrame (embed)

/-! ## The manuscript's example -/

/-- The represented receiver: `for(y <- @0)@y`. -/
theorem predot_receiver : predot receiver = pFor y demoChan (nQuote y) := by
  show predot (pFor y demoChan y) = _
  rw [predot_pFor]
  decide +kernel

/-- The sender has no variable: it is its own representation. -/
theorem predot_sender : predot sender = sender := predot_ground sender (by decide +kernel)

/-- The represented sender at `0`, the represented receiver at `1`. -/
def rows : ℕ → Pattern := fun n => if n = 0 then predot sender else if n = 1 then predot receiver else pZero

/-- The renaming that opens the comm rule. -/
def rename : String → String := fun v =>
  if v = "T1" then "t1" else if v = "T2" then "t2" else if v = "X" then "x0" else if v = "K1" then "k1"
  else if v = "K2" then "k2" else v

/-- The COMM firing of the example, making `2` and `3`. -/
abbrev firing : Firing ℕ E program PUnit.unit := commAt (renameBy rename) 0 1 2 3

theorem rename_injective : ∀ x ∈ ruleVars commRule, ∀ x' ∈ ruleVars commRule, rename x = rename x' → x = x' := by
  decide +kernel

theorem rename_ruleVars : ∀ x ∈ ruleVars commRule, rename x ∈ ["t1", "t2", "x0", "k1", "k2"] := by
  decide +kernel

/-- **The opening is fresh** at every state whose present rows `0` and `1` have no variable named `t1`,
`t2`, `x0`, `k1` or `k2`, and whose knowledge is empty. -/
theorem fresh_at (lab : ℕ → Pattern) (avoid₀ : ∀ v ∈ ["t1", "t2", "x0", "k1", "k2"], v ∉ pvars (lab 0))
    (avoid₁ : ∀ v ∈ ["t1", "t2", "x0", "k1", "k2"], v ∉ pvars (lab 1)) :
    (commAt (renameBy rename) 0 1 2 3).Fresh X (embed lab start) := by
  refine Comm.fresh_of_renaming (embed lab start) (commAt (renameBy rename) 0 1 2 3) rename rfl
    rename_injective ?_
  intro x inVars m mentions
  have renamed : rename x ∈ ["t1", "t2", "x0", "k1", "k2"] := rename_ruleVars x inVars
  rcases mentions with known | known | ⟨o, present, rfl⟩
  · simp [embed, start] at known
  · simp [embed, start] at known
  · have zeroOrOne : o = 0 ∨ o = 1 := by simpa [embed, start] using present
    rcases zeroOrOne with rfl | rfl
    · exact avoid₀ _ renamed
    · exact avoid₁ _ renamed

theorem example_fresh : firing.Fresh X (embed rows start) :=
  fresh_at rows (by decide +kernel) (by decide +kernel)

/-- The example's redex satisfies the variable convention. -/
theorem example_apart : MeTTaCalculus.Corrected.Apart zeroTerm pZero y y :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **The example fired by the finite program**, through `comm_one_firing_closed`. -/
theorem example_comm :
    (RuleSyntax.step X ℕ E program).Admits (s := embed rows start) firing ∧
      MeTTaCalculus.ReflectionClosure.Step GroundPrincipal SC source
        (par (applyDot unifier pZero) (applyDot unifier y)) ∧
      ∀ σ : PSubst, patternAction.Models σ (firing.result X (embed rows start)).knowledge →
        psubst σ ((firing.result X (embed rows start)).label 2) = applyDot unifier pZero ∧
          psubst σ ((firing.result X (embed rows start)).label 3) = applyDot unifier y :=
  comm_one_firing_closed rows zeroTerm y demoChan pZero y unifier unifier_groundPrincipal example_apart
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) start 0 1 2 3 rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ⟨fun _ => none, fun _ member => absurd member List.not_mem_nil⟩
    example_fresh

/-- **The result, by kernel evaluation**: the inputs `0` and `1` are replaced by `2` and `3`, labelled by
the opened continuations `k1` and `k2`. -/
theorem example_result : (firing.result X (embed rows start)).present = {2, 3} ∧
    (firing.result X (embed rows start)).label 2 = .fvar "k1" ∧
    (firing.result X (embed rows start)).label 3 = .fvar "k2" := by
  decide +kernel

/-- **The knowledge after the firing, by kernel evaluation**: the opened take patterns equated with the
represented rows, and the opened tell `t1 = t2`. -/
theorem example_knowledge : (firing.result X (embed rows start)).knowledge =
    [(pFor (.fvar "t1") (.fvar "x0") (.fvar "k1"), sender),
      (pFor (.fvar "t2") (.fvar "x0") (.fvar "k2"), pFor y demoChan (nQuote y)),
      (.fvar "t1", .fvar "t2")] := by
  decide +kernel

/-- **Every solution reads identity `3` as `@((0))`**, the manuscript's reduct. -/
theorem example_reads (σ : PSubst)
    (solved : patternAction.Models σ (firing.result X (embed rows start)).knowledge) :
    psubst σ ((firing.result X (embed rows start)).label 3) = nQuote zeroTerm := by
  rw [(example_comm.2.2 σ solved).2]
  decide +kernel

/-- The solution that reads the example's redex. -/
def exampleSolution : PSubst := fun v =>
  if v = "t1" ∨ v = "t2" ∨ v = "y" then some zeroTerm else if v = "x0" then some demoChan
  else if v = "k1" then some pZero else if v = "k2" then some (nQuote zeroTerm) else none

/-- **A solution of the knowledge after the firing** exists. -/
theorem example_solution :
    patternAction.Models exampleSolution (firing.result X (embed rows start)).knowledge := by
  rw [example_knowledge]
  show ∀ e : Pattern × Pattern, e ∈ _ → psubst _ e.1 = psubst _ e.2
  decide +kernel

/-- The manuscript's reduct is `0 | @((0))`. -/
theorem example_reduct : par (applyDot unifier pZero) (applyDot unifier y) = reduct := by decide +kernel

/-! ## A second redex shape, the same rule -/

/-- The pattern variable `x`. -/
def x : Pattern := .fvar "x"

/-- `f(x)`. -/
def fx : Pattern := .apply "f" [x]

/-- `f((0))`. -/
def fZero : Pattern := .apply "f" [zeroTerm]

/-- `x ↦ (0)`. -/
def secondUnifier : Bindings := [("x", zeroTerm)]

theorem secondUnifier_groundPrincipal : GroundPrincipal fx fZero secondUnifier where
  keys := by decide +kernel
  covers := by
    intro v member
    have vars : pvars fx ++ pvars fZero = ["x"] := by decide +kernel
    rw [vars, List.mem_singleton] at member
    subst member
    exact ⟨zeroTerm, by decide +kernel, by decide +kernel⟩
  solves := by decide +kernel
  principal := by
    intro σ equation v member value found
    have vars : pvars fx ++ pvars fZero = ["x"] := by decide +kernel
    rw [vars, List.mem_singleton] at member
    subst member
    have same : value = zeroTerm := by
      simpa [secondUnifier, Mettapedia.OSLF.MeTTaIL.Match.Bindings.lookup] using found.symm
    subst same
    simpa [fx, fZero, x, psubst, MeTTaOperationsComm.psubst.psubstList, zeroTerm, tProc, pZero] using
      equation

/-- The second redex's represented rows: `for(f(x) <- @0)@x` at `0`, `for(f((0)) <- @0)0` at `1`. -/
def secondRows : ℕ → Pattern := fun n =>
  if n = 0 then predot (pFor fx demoChan x) else if n = 1 then predot (pFor fZero demoChan pZero) else pZero

/-- **A second redex shape, fired by the same rule of the same program.** -/
theorem second_shape_comm :
    (RuleSyntax.step X ℕ E program).Admits (s := embed secondRows start) firing ∧
      MeTTaCalculus.ReflectionClosure.Step GroundPrincipal SC
        (par (pFor fx demoChan x) (pFor fZero demoChan pZero)) (par (nQuote zeroTerm) pZero) ∧
      ∀ σ : PSubst, patternAction.Models σ (firing.result X (embed secondRows start)).knowledge →
        psubst σ ((firing.result X (embed secondRows start)).label 2) = nQuote zeroTerm ∧
          psubst σ ((firing.result X (embed secondRows start)).label 3) = pZero := by
  obtain ⟨admitted, manuscript, reads⟩ := comm_one_firing_closed secondRows fx fZero demoChan x pZero
    secondUnifier secondUnifier_groundPrincipal
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) start 0 1 2 3 rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ⟨fun _ => none, fun _ member => absurd member List.not_mem_nil⟩
    (fresh_at secondRows (by decide +kernel) (by decide +kernel))
  have dotX : applyDot secondUnifier x = nQuote zeroTerm := by decide +kernel
  have dotZero : applyDot secondUnifier pZero = pZero := by decide +kernel
  rw [dotX, dotZero] at manuscript
  refine ⟨admitted, manuscript, fun σ solved => ?_⟩
  rw [← dotX, ← dotZero]
  exact reads σ solved

/-! ## Control: the representation's quotes -/

/-- The example's rows as written, without the representation. -/
def plainRows : ℕ → Pattern := fun n => if n = 0 then sender else if n = 1 then receiver else pZero

/-- **Control: pre-dotting.** With the receiver stored as written, the same firing of the same program is
admitted, and every solution reads identity `3` as the value `(0)`, not the manuscript's `@((0))`. -/
theorem undotted_misreads :
    (RuleSyntax.step X ℕ E program).Admits (s := embed plainRows start) firing ∧
      (∀ σ : PSubst, patternAction.Models σ (firing.result X (embed plainRows start)).knowledge →
        psubst σ ((firing.result X (embed plainRows start)).label 3) = zeroTerm) ∧
      zeroTerm ≠ applyDot unifier y := by
  refine ⟨comm_admits_inputs plainRows zeroTerm y demoChan pZero y start 0 1 2 3 (fun _ _ => rfl)
    (fun _ _ => rfl) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (σ₀ := fun v => if v = "y" then some zeroTerm else none)
    (fun _ member => absurd member List.not_mem_nil) (by decide +kernel)
    (fresh_at plainRows (by decide +kernel) (by decide +kernel)), fun σ solved => ?_, by decide +kernel⟩
  obtain ⟨-, unify, -, -, body₂⟩ := comm_reads_inputs plainRows zeroTerm y demoChan demoChan pZero y start
    0 1 2 3 (fun _ _ => rfl) (fun _ _ => rfl) (by decide +kernel) (renameBy rename) solved
  rw [body₂, ← unify]
  rfl

/-! ## Control: a ground principal unifier -/

/-- `for(y <- @0)y` at `0` and `for(w <- @0)0` at `1`, represented. -/
def pairRows : ℕ → Pattern := fun n =>
  if n = 0 then predot (pFor y demoChan y) else if n = 1 then predot (pFor w demoChan pZero) else pZero

/-- No ground principal unifier of `y` and `w` exists. -/
theorem no_groundPrincipal : ¬ ∃ bs, GroundPrincipal y w bs := by
  rintro ⟨bs, gp⟩
  obtain ⟨v, found, -⟩ := gp.covers "y" (by decide +kernel)
  have toZero : pZero = v :=
    gp.principal (fun _ => some pZero) (by decide +kernel) "y" (by decide +kernel) v found
  have toQuote : nQuote pZero = v :=
    gp.principal (fun _ => some (nQuote pZero)) (by decide +kernel) "y" (by decide +kernel) v found
  exact absurd (toZero.trans toQuote.symm) (by decide +kernel)

/-- A solution of the pair's firing that reads `y` and `w` as `0`. -/
def zeroSolution : PSubst := fun v =>
  if v = "y" ∨ v = "w" ∨ v = "t1" ∨ v = "t2" then some pZero else if v = "x0" then some demoChan
  else if v = "k1" then some (nQuote pZero) else if v = "k2" then some pZero else none

/-- A solution of the pair's firing that reads `y` and `w` as `@0`. -/
def quoteSolution : PSubst := fun v =>
  if v = "y" ∨ v = "w" ∨ v = "t1" ∨ v = "t2" then some (nQuote pZero) else if v = "x0" then some demoChan
  else if v = "k1" then some (nQuote (nQuote pZero)) else if v = "k2" then some pZero else none

def pairUnifier : Bindings := [("y", w)]

theorem pairUnifier_principal : MeTTaCalculus.Corrected.Principal y w pairUnifier :=
  MeTTaCalculus.Corrected.unify_principal (by decide +kernel)

/-- The existing admitted open example has one symbolic principal readback.
Its distinct ground observations are instances, not a failure of principality. -/
theorem nonground_principal_reading (point : PSubst)
    (solved : patternAction.Models point (firing.result X (embed pairRows start)).knowledge) :
    psubst point ((firing.result X (embed pairRows start)).label 2) = nQuote (psubst point w) := by
  have reads := (comm_reads_principal pairRows start y w demoChan y pZero pairUnifier
    pairUnifier_principal 0 1 2 3 (renameBy rename)
    (fun σ _ => congrArg (psubst σ) (by decide +kernel))
    (fun σ _ => congrArg (psubst σ) (by decide +kernel))
    (by decide) point solved (by decide) (by decide)).1
  have completed : applyDot
      (MeTTaCalculus.Corrected.completeBindings (pvars y ++ pvars w) pairUnifier) y = nQuote w := by
    decide +kernel
  rwa [completed, MeTTaOperationsComm.psubst_nQuote] at reads

/-- **Control: a ground principal unifier.** The patterns `y` and `w` have no ground principal unifier.
The firing of the same program is admitted, and two solutions of the knowledge after it read the made row
`2` differently, as `@0` and as `@(@0)`. -/
theorem nonground_two_readings :
    (¬ ∃ bs, GroundPrincipal y w bs) ∧
      (RuleSyntax.step X ℕ E program).Admits (s := embed pairRows start) firing ∧
      patternAction.Models zeroSolution (firing.result X (embed pairRows start)).knowledge ∧
      patternAction.Models quoteSolution (firing.result X (embed pairRows start)).knowledge ∧
      psubst zeroSolution ((firing.result X (embed pairRows start)).label 2) = nQuote pZero ∧
      psubst quoteSolution ((firing.result X (embed pairRows start)).label 2) = nQuote (nQuote pZero) := by
  have zeroModel : patternAction.Models zeroSolution (firing.result X (embed pairRows start)).knowledge := by
    show ∀ e : Pattern × Pattern, e ∈ _ → psubst _ e.1 = psubst _ e.2
    decide +kernel
  have quoteModel : patternAction.Models quoteSolution (firing.result X (embed pairRows start)).knowledge := by
    show ∀ e : Pattern × Pattern, e ∈ _ → psubst _ e.1 = psubst _ e.2
    decide +kernel
  refine ⟨no_groundPrincipal, comm_admits pairRows y w demoChan y pZero start 0 1 2 3 (fun _ _ => rfl)
    (fun _ _ => rfl) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (σ₀ := fun _ => some pZero)
    (fun _ member => absurd member List.not_mem_nil) (by decide +kernel)
    (fresh_at pairRows (by decide +kernel) (by decide +kernel)), zeroModel, quoteModel, ?_, ?_⟩
  · exact (nonground_principal_reading zeroSolution zeroModel).trans (by decide +kernel)
  · exact (nonground_principal_reading quoteSolution quoteModel).trans (by decide +kernel)

/-! ## Control: the variable convention -/

/-- The name `a`. -/
def a : Pattern := .fvar "a"

/-- The manuscript's canary, represented: `for(a <- @0)a` at `0`, `for(0 <- @0)a` at `1`. -/
def canaryRows : ℕ → Pattern := fun n =>
  if n = 0 then predot (pFor a demoChan a) else if n = 1 then predot (pFor pZero demoChan a) else pZero

/-- **Control: the variable convention.** On the canary, where the second input's free `a` is the first
input's bound name, the convention fails; the firing of the same program is admitted, and every solution
reads the second made row as `0`: neither the literal reduct's `@0` nor the corrected reduct's `a`. -/
theorem canary_misreads :
    ¬ MeTTaCalculus.Corrected.Apart a a pZero a ∧
      (RuleSyntax.step X ℕ E program).Admits (s := embed canaryRows start) firing ∧
      (∀ σ : PSubst, patternAction.Models σ (firing.result X (embed canaryRows start)).knowledge →
        psubst σ ((firing.result X (embed canaryRows start)).label 3) = pZero) ∧
      pZero ≠ nQuote pZero ∧ pZero ≠ a := by
  have second : predot (pFor pZero demoChan a) = pFor pZero demoChan a := by
    rw [predot_pFor]
    decide +kernel
  refine ⟨fun apart => apart.leftOutside "a" (by decide +kernel) (by decide +kernel),
    comm_admits canaryRows a pZero demoChan a a start 0 1 2 3 (fun _ _ => rfl) (fun _ _ => rfl)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (σ₀ := fun _ => some pZero) (fun _ member => absurd member List.not_mem_nil)
      (by decide +kernel) (fresh_at canaryRows (by decide +kernel) (by decide +kernel)),
    fun σ solved => ?_, by decide +kernel, by decide +kernel⟩
  obtain ⟨-, unify, -, -, body₂⟩ := comm_reads_inputs canaryRows a pZero (predot demoChan) demoChan
    (dotted (pvars a) (predot a)) a start 0 1 2 3 (fun σ _ => congrArg (psubst σ) (predot_pFor a demoChan a))
    (fun σ _ => congrArg (psubst σ) second) (by decide +kernel) (renameBy rename) solved
  rw [body₂]
  exact unify.trans (MeTTaOperationsComm.psubst_pZero σ)

/-! ## Control: first-order continuations -/

/-- The receiver `for(y <- @0)(bvar 0)[y/0]`, whose continuation is an explicit substitution node. -/
def substReceiver : Pattern := pFor y demoChan Comm.Controls.substBody

/-- The sender at `0` and the receiver with the substitution node at `1`, represented. -/
def substRows : ℕ → Pattern := fun n =>
  if n = 0 then predot sender else if n = 1 then predot substReceiver else pZero

/-- **Control: first-order continuations.** The receiver's continuation `(bvar 0)[y/0]` is an explicit
substitution node, so it is not first-order. The COMM firing of the same program is admitted, and every
solution reads the made row `3` as `(bvar 0)[@((0))/0]`, which keeps the node; the manuscript's dot
eliminates the node and gives `@((0))`. -/
theorem subst_node_misreads :
    firstOrder Comm.Controls.substBody = false ∧
      (RuleSyntax.step X ℕ E program).Admits (s := embed substRows start) firing ∧
      (∀ σ : PSubst, patternAction.Models σ (firing.result X (embed substRows start)).knowledge →
        psubst σ ((firing.result X (embed substRows start)).label 3) = .subst (.bvar 0) (nQuote zeroTerm)) ∧
      applyDot unifier Comm.Controls.substBody = nQuote zeroTerm ∧
      Pattern.subst (.bvar 0) (nQuote zeroTerm) ≠ nQuote zeroTerm := by
  refine ⟨by decide +kernel, comm_admits substRows zeroTerm y demoChan pZero Comm.Controls.substBody start
    0 1 2 3 (fun _ _ => rfl) (fun _ _ => rfl) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (σ₀ := fun _ => some zeroTerm)
    (fun _ member => absurd member List.not_mem_nil) (by decide +kernel)
    (fresh_at substRows (by decide +kernel) (by decide +kernel)), fun σ solved => ?_, by decide +kernel,
    by decide +kernel⟩
  obtain ⟨-, unify, -, -, body₂⟩ := comm_reads_inputs substRows zeroTerm y demoChan (predot demoChan) pZero
    (dotted (pvars y) (predot Comm.Controls.substBody)) start 0 1 2 3
    (fun σ _ => congrArg (psubst σ) predot_sender)
    (fun σ _ => congrArg (psubst σ) (predot_pFor y demoChan Comm.Controls.substBody))
    (by decide +kernel) (renameBy rename) solved
  have shape : dotted (pvars y) (predot Comm.Controls.substBody) = .subst (.bvar 0) (nQuote y) := by
    decide +kernel
  rw [body₂, shape]
  show Pattern.subst (.bvar 0) (nQuote (psubst σ y)) = _
  rw [← unify, psubst_of_pvars_nil σ zeroTerm (by decide +kernel)]

/-! ## The example through the correspondence -/

/-- The example's parallel parts: the sender and the receiver. -/
theorem parts_source : parts source = [sender, receiver] := by decide +kernel

/-- The parts of the manuscript's reduct `0 | @((0))`: the null process is dropped. -/
theorem parts_reduct : parts reduct = [nQuote zeroTerm] := by decide +kernel

/-- **The example is a hosted process.** -/
theorem example_hostedProcess : HostedProcess source := by
  refine ⟨fun c member => ?_, ?_⟩
  · rw [parts_source] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨by decide +kernel, .inl (by decide +kernel)⟩
    · exact ⟨by decide +kernel, .inr ⟨y, demoChan, y, rfl, by decide +kernel, by decide +kernel,
        by decide +kernel⟩⟩
  · rw [parts_source, List.pairwise_pair]
    decide +kernel

/-- A value of a binding list is a value of one of its entries. -/
theorem value_mem {bs : Bindings} {z : String} {v : Pattern} (found : bs.lookup z = some v) :
    ∃ k, (k, v) ∈ bs := by
  unfold Mettapedia.OSLF.MeTTaIL.Match.Bindings.lookup at found
  obtain ⟨e, look, rfl⟩ := Option.map_eq_some_iff.mp found
  exact ⟨e.1, List.mem_of_find?_eq_some look⟩

/-- The example's unifier has first-order values. -/
theorem unifier_values : ∀ z v, unifier.lookup z = some v → firstOrder v = true := by
  intro z v found
  obtain ⟨k, member⟩ := value_mem found
  simp only [unifier, List.mem_singleton, Prod.mk.injEq] at member
  rw [member.2]
  decide +kernel

/-- The same unifier, with the patterns in the other order. -/
theorem unifier_groundPrincipal_swapped : GroundPrincipal y zeroTerm unifier where
  keys := by decide +kernel
  covers := by
    intro v member
    have vars : pvars y ++ pvars zeroTerm = ["y"] := by decide +kernel
    rw [vars, List.mem_singleton] at member
    subst member
    exact ⟨zeroTerm, by decide +kernel, by decide +kernel⟩
  solves := by decide +kernel
  principal := by
    intro σ equation v member value found
    have vars : pvars y ++ pvars zeroTerm = ["y"] := by decide +kernel
    rw [vars, List.mem_singleton] at member
    subst member
    obtain ⟨k, inside⟩ := value_mem found
    simp only [unifier, List.mem_singleton, Prod.mk.injEq] at inside
    rw [inside.2]
    exact equation.trans (psubst_of_pvars_nil σ zeroTerm (by decide +kernel))

/-- **The example's bag is ground-unifiable**: the hypothesis of the fourth clause holds there. -/
theorem example_groundUnifiable : GroundUnifiable (parts source : Multiset Pattern) := by
  intro t x A u B first second _
  rw [parts_source] at first second
  have senderNe : sender ≠ receiver := by decide +kernel
  rcases List.mem_cons.mp (Multiset.mem_coe.mp first) with isSender | rest
  · rw [isSender] at second
    have remaining : ((↑[sender, receiver] : Multiset Pattern).erase sender) = ↑[receiver] := by
      rw [Multiset.coe_erase, List.erase_cons_head]
    rw [remaining] at second
    have isReceiver := List.mem_singleton.mp (Multiset.mem_coe.mp second)
    obtain ⟨rfl, -, -⟩ := pFor_inj isSender
    obtain ⟨rfl, -, -⟩ := pFor_inj isReceiver
    exact ⟨unifier, unifier_groundPrincipal, unifier_values⟩
  · have isReceiver := List.mem_singleton.mp rest
    rw [isReceiver] at second
    have remaining : ((↑[sender, receiver] : Multiset Pattern).erase receiver) = ↑[sender] := by
      rw [Multiset.coe_erase, List.erase_cons_tail (by simpa using senderNe), List.erase_cons_head]
    rw [remaining] at second
    have isSender := List.mem_singleton.mp (Multiset.mem_coe.mp second)
    obtain ⟨rfl, -, -⟩ := pFor_inj isReceiver
    obtain ⟨rfl, -, -⟩ := pFor_inj isSender
    exact ⟨unifier, unifier_groundPrincipal_swapped, unifier_values⟩

/-- **The example's COMM as a step of the bag presentation**: the sender and the receiver are replaced by
`@((0))`, the parts of the manuscript's reduct. -/
theorem example_bagComm : BagComm (parts source : Multiset Pattern) (parts reduct : Multiset Pattern) := by
  have step := BagComm.comm zeroTerm y demoChan pZero y unifier 0 unifier_groundPrincipal example_apart
    unifier_values
  have target : (parts (applyDot unifier pZero) : Multiset Pattern) +
      (parts (applyDot unifier y) : Multiset Pattern) + 0 = (parts reduct : Multiset Pattern) := by
    rw [show applyDot unifier pZero = pZero by decide +kernel,
      show applyDot unifier y = nQuote zeroTerm by decide +kernel, parts_pZero,
      show parts (nQuote zeroTerm) = [nQuote zeroTerm] by decide +kernel, parts_reduct]
    rfl
  have start' : (parts source : Multiset Pattern) = pFor zeroTerm demoChan pZero ::ₘ pFor y demoChan y ::ₘ 0 := by
    rw [parts_source]
    rfl
  rw [start', ← target]
  exact step

/-- **The example runs through the correspondence**: from the initial state of the example, housekeeping
firings and one communication of the finite program reach a state that represents the parts of the
manuscript's reduct. -/
theorem example_run : ∃ s₁ s₂ : State Comm.Tm ℕ,
    Relation.ReflTransGen Administers (initial (parts source)) s₁ ∧ Communicates s₁ s₂ ∧
      Represents s₂ (parts reduct : Multiset Pattern) :=
  communication_complete (initial_represents source example_hostedProcess) example_bagComm

#print axioms parts_source
#print axioms example_hostedProcess
#print axioms unifier_values
#print axioms unifier_groundPrincipal_swapped
#print axioms example_groundUnifiable
#print axioms example_bagComm
#print axioms example_run
#print axioms predot_receiver
#print axioms rename_injective
#print axioms example_fresh
#print axioms example_comm
#print axioms example_result
#print axioms example_knowledge
#print axioms example_reads
#print axioms example_solution
#print axioms example_reduct
#print axioms secondUnifier_groundPrincipal
#print axioms second_shape_comm
#print axioms undotted_misreads
#print axioms no_groundPrincipal
#print axioms pairUnifier_principal
#print axioms nonground_principal_reading
#print axioms nonground_two_readings
#print axioms canary_misreads
#print axioms subst_node_misreads

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteProgram.Controls
