import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.CommOneFiring

/-!
# The manuscript's COMM as one firing: a computed example and the controls

The step is the one-match step of a program at the one frame of patterns (`CommOneFiring`): the store is
a bag of occurrences, a firing is one match, guards are asked after the firing's own tells (the comm
rule has none), the program is the fixed one-rule program of one redex shape, and there is one store of
knowledge.

## A computed example

`for((0) <- @0)0 | for(y <- @0)y`: the first guard offers the term `(0)` on `@0`, the second receives on
`@0` and continues as the received name. The unifier `y ↦ (0)` is ground and principal
(`unifier_groundPrincipal`, from the corrected unifier). The manuscript's COMM gives `0 | @((0))`
(`example_manuscript`), which is also what the tree's executable corrected step computes
(`example_executable`). The step fires the comm rule opened by `y ↦ z`, which is fresh
(`example_fresh`). Kernel evaluation computes the result: the inputs `0` and `1` are replaced by `2` and
`3`, labelled `0` and `@z` (`example_result`), with the knowledge that equates the opened take patterns
with the rows and tells `(0) = z` (`example_knowledge`). Every solution of that knowledge reads `3` as
`@((0))` (`example_reads`), and one solution exists (`example_solution`).

## Controls, one for each side condition

* **The patterns' variables apart from the knowledge** (`apart_needed`): where the knowledge binds `y`
  to `0`, the manuscript's COMM still fires, and the step refuses the COMM firing at every opening.
* **A principal unifier** (`nonprincipal_misreads`): `y ↦ 0, w ↦ 0` is a ground unifier of `y` and `w`
  that is not principal; after the admitted firing, a solution reads the made row as `@(@0)`, not
  `@0`. When a principal unifier is not ground, the manuscript's own dot depends on its orientation
  (`Corrected.manuscript_dot_depends_on_orientation`); the step then reads the uniform dot
  (`comm_one_firing_corrected`).
* **First-order continuations** (`subst_misreads`): the step keeps an explicit substitution node of a
  continuation as syntax, the manuscript's dot eliminates it, and no solution reads the dot.
* **Closed processes** (`open_two_readings`): with a free name `z` in a continuation, two solutions read
  the made row differently, and one of them does not read the manuscript's dot; the reading through each
  solution is the dot read through it (`comm_one_firing_open`).
* **Distinct made identities that are not present** (`made_coincide_refused`, `made_present_refused`).
* **A fresh opening** (`unopened_refused`): the rule unopened at the example's state is not fresh, and
  the firing is refused. The tree's own control is `RuleSyntax.Examples.capture_not_fresh`.
* **Label keeping** (`example_never_keeping`, `example_through_firstOrder`): the labels of
  `comm_adequacy` put the unopened row `@y` on `3`; no fresh opening keeps it. With `3` labelled by the
  opened row `@z`, the firing passes through `firstOrder_eq`.
* **The variable convention of the corrected version** (`canary_reads_literally`,
  `renamed_canary_corrected`): on the manuscript's canary `for(a <- @0)a | for(0 <- @0)a`, the side
  conditions of `comm_one_firing` hold and every solution reads the second made row as `@0`: the literal,
  capturing reduct `@0 | @0`; the convention fails there, and the executable corrected step gives
  `@0 | a`. Renamed apart, `for(a1 <- @0)a1 | for(0 <- @0)a` satisfies the convention, and every solution
  reads the made rows as `@0` and as `a` read through it: the corrected reduct.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Comm.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero nQuote applyDot SC tProc demoChan)
open MeTTaOperationsComm (psubst pvars patternAction PSubst dotted commRule commSelection GroundPrincipal
  comm_problem storePVars psubst_of_pvars_nil)
open OneFrame (embed keeping firstOrderOn)
open LogicOverTheStep.StepSpan (Succ)

/-! ## A computed example -/

/-- The process `0` as a term: `(0)`. -/
def zeroTerm : Pattern := tProc pZero

/-- The pattern variable `y`. -/
def y : Pattern := .fvar "y"

/-- `for((0) <- @0)0`. -/
def sender : Pattern := pFor zeroTerm demoChan pZero

/-- `for(y <- @0)y`. -/
def receiver : Pattern := pFor y demoChan y

/-- The redex. -/
def source : Pattern := par sender receiver

/-- The unifier `y ↦ (0)`. -/
def unifier : Bindings := [("y", zeroTerm)]

/-- The manuscript's reduct, `0 | @((0))`. -/
def reduct : Pattern := par pZero (nQuote zeroTerm)

/-- The sender at identity `0`, the receiver at `1`. -/
def labels : ℕ → Pattern := fun n => if n = 0 then sender else if n = 1 then receiver else pZero

/-- No knowledge; identities `0` and `1` present. -/
def start : Configuration Pattern ℕ := ⟨[], {0, 1}⟩

/-- The opening that renames the rule's `y` to `z`. -/
def toZ : PSubst := renameBy fun _ => "z"

/-- The COMM firing at that opening, making identities `2` and `3`. -/
abbrev firing : Firing ℕ E (commProgram zeroTerm y demoChan pZero y) PUnit.unit :=
  commFiring zeroTerm y demoChan pZero y toZ 0 1 2 3

theorem unify_found : MeTTaCalculus.Corrected.unify zeroTerm y = some unifier := by decide +kernel

/-- **The unifier is ground and principal**, found by the corrected unifier. -/
theorem unifier_groundPrincipal : GroundPrincipal zeroTerm y unifier := by
  refine groundPrincipal_of_principal (MeTTaCalculus.Corrected.unify_principal unify_found) ?_
  intro x member
  have vars : pvars zeroTerm ++ pvars y = ["y"] := by decide +kernel
  rw [vars, List.mem_singleton] at member
  subst member
  exact ⟨zeroTerm, by decide +kernel, by decide +kernel⟩

/-- The rule's only variable is `y`, so renaming every variable to `z` is injective on its variables. -/
theorem example_injective : ∀ x ∈ ruleVars (commSchema zeroTerm y demoChan pZero y),
    ∀ x' ∈ ruleVars (commSchema zeroTerm y demoChan pZero y),
      (fun _ : String => "z") x = (fun _ : String => "z") x' → x = x' := by
  decide +kernel

/-- **The opening `y ↦ z` is fresh** at every state whose present rows are the example's two rows. -/
theorem example_fresh (lab : ℕ → Pattern) (at0 : lab 0 = sender) (at1 : lab 1 = receiver) :
    firing.Fresh X (embed lab start) := by
  refine fresh_of_renaming (embed lab start) firing (fun _ => "z") rfl example_injective ?_
  intro x _ m mentions
  rcases mentions with known | known | ⟨o, present, rfl⟩
  · simp [embed, start] at known
  · simp [embed, start] at known
  · have zeroOrOne : o = 0 ∨ o = 1 := by simpa [embed, start] using present
    rcases zeroOrOne with rfl | rfl
    · show "z" ∉ pvars (lab 0)
      rw [at0]
      decide +kernel
    · show "z" ∉ pvars (lab 1)
      rw [at1]
      decide +kernel

/-- **The example fired by the step**, through `comm_one_firing`. -/
theorem example_comm :
    (RuleSyntax.step X ℕ E (commProgram zeroTerm y demoChan pZero y)).Admits (s := embed labels start)
        firing ∧
      MeTTaCalculus.ReflectionClosure.Step GroundPrincipal SC source
        (par (applyDot unifier pZero) (applyDot unifier y)) ∧
      ∀ σ : PSubst, patternAction.Models σ (firing.result X (embed labels start)).knowledge →
        psubst σ ((firing.result X (embed labels start)).label 2) = applyDot unifier pZero ∧
          psubst σ ((firing.result X (embed labels start)).label 3) = applyDot unifier y :=
  comm_one_firing labels zeroTerm y demoChan pZero y unifier unifier_groundPrincipal (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) start 0 1 2 3 rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨fun _ => none, fun _ member => absurd member List.not_mem_nil⟩
    (example_fresh labels rfl rfl)

/-- The manuscript's reduct is `0 | @((0))`. -/
theorem example_reduct : par (applyDot unifier pZero) (applyDot unifier y) = reduct := by decide +kernel

/-- **The manuscript relates the redex to its reduct.** -/
theorem example_manuscript : MeTTaCalculus.ReflectionClosure.Step GroundPrincipal SC source reduct :=
  example_reduct ▸ example_comm.2.1

/-- **The tree's executable corrected step computes the same reduct.** -/
theorem example_executable : MeTTaCalculus.Corrected.cstep source = [reduct] := by decide +kernel

/-- **The result, by kernel evaluation**: the inputs `0` and `1` are replaced by `2` and `3`, labelled
`0` and `@z`. -/
theorem example_result : (firing.result X (embed labels start)).present = {2, 3} ∧
    (firing.result X (embed labels start)).label 2 = pZero ∧
    (firing.result X (embed labels start)).label 3 = nQuote (.fvar "z") := by
  decide +kernel

/-- **The knowledge after the firing, by kernel evaluation**: the opened take patterns equated with the
rows, and the opened tell `(0) = z`. -/
theorem example_knowledge : (firing.result X (embed labels start)).knowledge =
    [(sender, sender), (pFor (.fvar "z") demoChan (.fvar "z"), receiver), (zeroTerm, .fvar "z")] := by
  decide +kernel

/-- **Every solution reads identity `3` as `@((0))`.** -/
theorem example_reads (σ : PSubst)
    (solved : patternAction.Models σ (firing.result X (embed labels start)).knowledge) :
    psubst σ ((firing.result X (embed labels start)).label 3) = nQuote zeroTerm := by
  rw [(example_comm.2.2 σ solved).2]
  decide +kernel

/-- **A solution of the knowledge after the firing**: `y` and `z` both read `(0)`. -/
theorem example_solution :
    patternAction.Models (fun v => if v = "y" ∨ v = "z" then some zeroTerm else none)
      (firing.result X (embed labels start)).knowledge := by
  rw [example_knowledge]
  show ∀ e : Pattern × Pattern, e ∈ _ → psubst _ e.1 = psubst _ e.2
  decide +kernel

/-! ## The patterns' variables apart from the knowledge -/

/-- The example's rows, with the knowledge binding the receiver's pattern variable `y` to `0`. -/
def bound : Configuration Pattern ℕ := ⟨[(y, pZero)], {0, 1}⟩

/-- **Control: the patterns' variables apart from the knowledge.** The condition fails at `bound`; the
manuscript's COMM fires on the redex, and the step refuses the COMM firing at every opening. -/
theorem apart_needed :
    ¬ (∀ x ∈ pvars zeroTerm ++ pvars y, x ∉ storePVars bound.equations) ∧
      MeTTaCalculus.ReflectionClosure.Step GroundPrincipal SC source reduct ∧
      ∀ ρ : PSubst, ¬ (RuleSyntax.step X ℕ E (commProgram zeroTerm y demoChan pZero y)).Admits
        (s := embed labels bound) (commFiring zeroTerm y demoChan pZero y ρ 0 1 2 3) := by
  refine ⟨by decide +kernel, example_manuscript, fun ρ admitted => ?_⟩
  obtain ⟨_, σ, solved⟩ := ((RuleSyntax.admits_iff _).mp admitted).2.2.2.1
  have key : (commFiring zeroTerm y demoChan pZero y ρ 0 1 2 3).information X (embed labels bound) =
      (commSelection 0 1 2 3).problem labels ((commRule zeroTerm y demoChan pZero y).map (psubst ρ))
        bound :=
    OneFrame.information_eq bound _
  rw [key] at solved
  obtain ⟨unopened, -, -⟩ := opened_refines labels labels zeroTerm y demoChan pZero y ρ bound 0 1 2 3
    rfl rfl rfl rfl solved
  rw [comm_problem] at unopened
  have known : psubst σ y = psubst σ pZero := unopened (y, pZero) (by simp [bound])
  have told : psubst σ zeroTerm = psubst σ y := unopened (zeroTerm, y) (by simp)
  have collapse : zeroTerm = pZero := told.trans known
  exact absurd collapse (by decide +kernel)

/-! ## A principal unifier -/

/-- The pattern variable `w`. -/
def w : Pattern := .fvar "w"

/-- `for(y <- @0)y` at `0` and `for(w <- @0)0` at `1`. -/
def pairLabels : ℕ → Pattern := fun n =>
  if n = 0 then pFor y demoChan y else if n = 1 then pFor w demoChan pZero else pZero

/-- The principal unifier of `y` and `w`. -/
def pairUnifier : Bindings := [("y", w)]

/-- A ground unifier of `y` and `w`, both to `0`, which is not principal. -/
def groundGuess : Bindings := [("y", pZero), ("w", pZero)]

/-- The opening `y ↦ y1`, `w ↦ w1`. -/
def toOnes : PSubst := renameBy fun v => if v = "y" then "y1" else "w1"

/-- The COMM firing of the two receivers. -/
abbrev pairFiring : Firing ℕ E (commProgram y w demoChan y pZero) PUnit.unit :=
  commFiring y w demoChan y pZero toOnes 0 1 2 3

theorem pair_unify : MeTTaCalculus.Corrected.unify y w = some pairUnifier := by decide +kernel

theorem pair_fresh : pairFiring.Fresh X (embed pairLabels start) := by
  refine fresh_of_renaming (embed pairLabels start) pairFiring (fun v => if v = "y" then "y1" else "w1")
    rfl (by decide +kernel) ?_
  intro x _ m mentions
  rcases mentions with known | known | ⟨o, present, rfl⟩
  · simp [embed, start] at known
  · simp [embed, start] at known
  · have zeroOrOne : o = 0 ∨ o = 1 := by simpa [embed, start] using present
    rcases zeroOrOne with rfl | rfl
    · show (if x = "y" then "y1" else "w1") ∉ pvars (pairLabels 0)
      split <;> decide +kernel
    · show (if x = "y" then "y1" else "w1") ∉ pvars (pairLabels 1)
      split <;> decide +kernel

theorem pair_admitted : (RuleSyntax.step X ℕ E (commProgram y w demoChan y pZero)).Admits
    (s := embed pairLabels start) pairFiring :=
  comm_admitted pairLabels y w demoChan y pZero pairUnifier
    (MeTTaCalculus.Corrected.unify_principal pair_unify) start 0 1 2 3 rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨fun _ => none, fun _ member => absurd member List.not_mem_nil⟩ pair_fresh

theorem groundGuess_not_principal : ¬ GroundPrincipal y w groundGuess := by
  intro gp
  have wrong := gp.principal (fun _ => some (nQuote pZero)) (by decide +kernel) "y" (by decide +kernel)
    pZero (by decide +kernel)
  exact absurd wrong (by decide +kernel)

/-- **Control: a principal unifier.** `y ↦ 0, w ↦ 0` unifies `y` and `w` and is ground, but it is not
principal. The step's COMM firing of the two receivers is admitted, and the knowledge after it has a
solution that reads the made row as `@(@0)`, not as the dot `@0` of that unifier. -/
theorem nonprincipal_misreads :
    psubst groundGuess.lookup y = psubst groundGuess.lookup w ∧ ¬ GroundPrincipal y w groundGuess ∧
      applyDot groundGuess y = nQuote pZero ∧
      (RuleSyntax.step X ℕ E (commProgram y w demoChan y pZero)).Admits (s := embed pairLabels start)
        pairFiring ∧
      ∃ σ : PSubst, patternAction.Models σ (pairFiring.result X (embed pairLabels start)).knowledge ∧
        psubst σ ((pairFiring.result X (embed pairLabels start)).label 2) = nQuote (nQuote pZero) ∧
        psubst σ ((pairFiring.result X (embed pairLabels start)).label 2) ≠ applyDot groundGuess y := by
  refine ⟨by decide +kernel, groundGuess_not_principal, by decide +kernel, pair_admitted,
    fun _ => some (nQuote pZero), ?_, by decide +kernel, by decide +kernel⟩
  show ∀ e : Pattern × Pattern, e ∈ _ → psubst _ e.1 = psubst _ e.2
  decide +kernel

/-! ## First-order continuations -/

/-- A continuation with an explicit substitution node: `(bvar 0)[y/0]`. -/
def substBody : Pattern := .subst (.bvar 0) y

/-- The sender at `0`, and at `1` the receiver `for(y <- @0)substBody`. -/
def substLabels : ℕ → Pattern := fun n =>
  if n = 0 then sender else if n = 1 then pFor y demoChan substBody else pZero

/-- The COMM firing, opened by `y ↦ z`. -/
abbrev substFiring : Firing ℕ E (commProgram zeroTerm y demoChan pZero substBody) PUnit.unit :=
  commFiring zeroTerm y demoChan pZero substBody toZ 0 1 2 3

theorem subst_fresh : substFiring.Fresh X (embed substLabels start) := by
  refine fresh_of_renaming (embed substLabels start) substFiring (fun _ => "z") rfl (by decide +kernel) ?_
  intro x _ m mentions
  rcases mentions with known | known | ⟨o, present, rfl⟩
  · simp [embed, start] at known
  · simp [embed, start] at known
  · have zeroOrOne : o = 0 ∨ o = 1 := by simpa [embed, start] using present
    rcases zeroOrOne with rfl | rfl
    · show "z" ∉ pvars (substLabels 0)
      decide +kernel
    · show "z" ∉ pvars (substLabels 1)
      decide +kernel

/-- **Control: first-order continuations.** The continuation `substBody` has an explicit substitution
node. The COMM firing is admitted (admission asks nothing of the continuations), and every solution reads
the made row as the structural dot, which keeps the node (`comm_one_firing_structural`); the
manuscript's dot eliminates the node and gives `@((0))`, and no solution of any knowledge reads the
step's made row as that. -/
theorem subst_misreads :
    MeTTaOperationsComm.firstOrder substBody = false ∧ applyDot unifier substBody = nQuote zeroTerm ∧
      structuralDot unifier substBody = .subst (.bvar 0) (nQuote zeroTerm) ∧
      (RuleSyntax.step X ℕ E (commProgram zeroTerm y demoChan pZero substBody)).Admits
        (s := embed substLabels start) substFiring ∧
      (∀ σ : PSubst, patternAction.Models σ (substFiring.result X (embed substLabels start)).knowledge →
        psubst σ ((substFiring.result X (embed substLabels start)).label 3) =
          .subst (.bvar 0) (nQuote zeroTerm)) ∧
      ∀ σ : PSubst,
        psubst σ ((substFiring.result X (embed substLabels start)).label 3) ≠ applyDot unifier substBody := by
  have dot : applyDot unifier substBody = nQuote zeroTerm := by decide +kernel
  have structural : structuralDot unifier substBody = .subst (.bvar 0) (nQuote zeroTerm) := by
    decide +kernel
  obtain ⟨admitted, reads⟩ := comm_one_firing_structural substLabels zeroTerm y demoChan pZero substBody
    unifier unifier_groundPrincipal start 0 1 2 3 rfl rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨fun _ => none, fun _ member => absurd member List.not_mem_nil⟩ subst_fresh
  refine ⟨by decide +kernel, dot, structural, admitted, fun σ solved => ?_, fun σ same => ?_⟩
  · rw [(reads σ solved).2, structural]
    exact psubst_of_pvars_nil σ _ (by decide +kernel)
  · have row : (substFiring.result X (embed substLabels start)).label 3 =
        .subst (.bvar 0) (nQuote (.fvar "z")) := by
      decide +kernel
    rw [row, dot] at same
    exact Pattern.noConfusion same

/-! ## Closed processes -/

/-- The free name `z`. -/
def z : Pattern := .fvar "z"

/-- The sender at `0`, and at `1` the receiver `for(y <- @0)z`, whose continuation is a free name. -/
def openLabels : ℕ → Pattern := fun n =>
  if n = 0 then sender else if n = 1 then pFor y demoChan z else pZero

/-- The opening `y ↦ y1`, `z ↦ z1`. -/
def toPrimes : PSubst := renameBy fun v => if v = "y" then "y1" else "z1"

/-- The COMM firing at that opening. -/
abbrev openFiring : Firing ℕ E (commProgram zeroTerm y demoChan pZero z) PUnit.unit :=
  commFiring zeroTerm y demoChan pZero z toPrimes 0 1 2 3

theorem open_fresh : openFiring.Fresh X (embed openLabels start) := by
  refine fresh_of_renaming (embed openLabels start) openFiring (fun v => if v = "y" then "y1" else "z1")
    rfl (by decide +kernel) ?_
  intro x _ m mentions
  rcases mentions with known | known | ⟨o, present, rfl⟩
  · simp [embed, start] at known
  · simp [embed, start] at known
  · have zeroOrOne : o = 0 ∨ o = 1 := by simpa [embed, start] using present
    rcases zeroOrOne with rfl | rfl
    · show (if x = "y" then "y1" else "z1") ∉ pvars (openLabels 0)
      split <;> decide +kernel
    · show (if x = "y" then "y1" else "z1") ∉ pvars (openLabels 1)
      split <;> decide +kernel

/-- **Control: closed processes.** The continuation `z` is not bound by the patterns. The COMM firing is
admitted and every solution reads the made row as the manuscript's dot read through it
(`comm_one_firing_open`), but two solutions read it as `0` and as `@0`: no fixed pattern is the reading,
and the first is not the dot `z`. -/
theorem open_two_readings :
    ¬ (∀ x ∈ pvars z, x ∈ pvars zeroTerm ++ pvars y) ∧ applyDot unifier z = z ∧
      (RuleSyntax.step X ℕ E (commProgram zeroTerm y demoChan pZero z)).Admits (s := embed openLabels start)
        openFiring ∧
      (∀ σ : PSubst, patternAction.Models σ (openFiring.result X (embed openLabels start)).knowledge →
        psubst σ ((openFiring.result X (embed openLabels start)).label 3) = psubst σ (applyDot unifier z)) ∧
      patternAction.Models (fun v => if v = "y" ∨ v = "y1" then some zeroTerm else some pZero)
        (openFiring.result X (embed openLabels start)).knowledge ∧
      patternAction.Models (fun v => if v = "y" ∨ v = "y1" then some zeroTerm else some (nQuote pZero))
        (openFiring.result X (embed openLabels start)).knowledge ∧
      psubst (fun v => if v = "y" ∨ v = "y1" then some zeroTerm else some pZero)
          ((openFiring.result X (embed openLabels start)).label 3) = pZero ∧
      psubst (fun v => if v = "y" ∨ v = "y1" then some zeroTerm else some (nQuote pZero))
          ((openFiring.result X (embed openLabels start)).label 3) = nQuote pZero := by
  obtain ⟨admitted, -, reads⟩ := comm_one_firing_open openLabels zeroTerm y demoChan pZero z unifier
    unifier_groundPrincipal (by decide +kernel) (by decide +kernel) start 0 1 2 3 rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨fun _ => none, fun _ member => absurd member List.not_mem_nil⟩ open_fresh
  refine ⟨by decide +kernel, by decide +kernel, admitted, fun σ solved => (reads σ solved).2, ?_, ?_,
    by decide +kernel, by decide +kernel⟩
  · show ∀ e : Pattern × Pattern, e ∈ _ → psubst _ e.1 = psubst _ e.2
    decide +kernel
  · show ∀ e : Pattern × Pattern, e ∈ _ → psubst _ e.1 = psubst _ e.2
    decide +kernel

/-! ## Distinct made identities that are not present -/

/-- **Control: distinct made identities.** -/
theorem made_coincide_refused :
    ¬ (RuleSyntax.step X ℕ E (commProgram zeroTerm y demoChan pZero y)).Admits (s := embed labels start)
      (commFiring zeroTerm y demoChan pZero y toZ 0 1 2 2) := by
  intro admitted
  exact absurd ((RuleSyntax.admits_iff _).mp admitted).2.1.2.1 (by decide +kernel)

/-- **Control: made identities that are not present.** -/
theorem made_present_refused :
    ¬ (RuleSyntax.step X ℕ E (commProgram zeroTerm y demoChan pZero y)).Admits (s := embed labels start)
      (commFiring zeroTerm y demoChan pZero y toZ 0 1 0 3) := by
  intro admitted
  exact absurd ((RuleSyntax.admits_iff _).mp admitted).2.2.1.fresh (by decide +kernel)

/-! ## A fresh opening -/

/-- The comm rule unopened at the example's state shares the receiver's `y`: it is not fresh. -/
theorem unopened_not_fresh :
    ¬ (commFiring zeroTerm y demoChan pZero y (fun _ => none) 0 1 2 3 :
      Firing ℕ E (commProgram zeroTerm y demoChan pZero y) PUnit.unit).Fresh X (embed labels start) := by
  intro fresh
  obtain ⟨u, state, rule⟩ := fresh PUnit.unit (fun _ => some pZero) (fun _ => none)
  have onState := state receiver (Or.inr (Or.inr ⟨1, by decide +kernel, rfl⟩))
  have onRule := rule receiver (by decide +kernel)
  change psubst u (psubst (fun _ => none) receiver) = psubst (fun _ => some pZero) receiver at onState
  change psubst u (psubst (fun _ => none) receiver) = psubst (fun _ => none) receiver at onRule
  exact absurd (onState.symm.trans onRule) (by decide +kernel)

/-- **Control: a fresh opening.** The firing of the unopened rule is refused. -/
theorem unopened_refused :
    ¬ (RuleSyntax.step X ℕ E (commProgram zeroTerm y demoChan pZero y)).Admits (s := embed labels start)
      (commFiring zeroTerm y demoChan pZero y (fun _ => none) 0 1 2 3) :=
  fun admitted => unopened_not_fresh ((RuleSyntax.admits_iff _).mp admitted).1

/-! ## Label keeping -/

/-- **Control: label keeping.** The labels of `comm_adequacy` put the unopened made row `@y` on identity
`3`; no fresh opening keeps it. -/
theorem example_never_keeping (ρ : PSubst)
    (fresh : (commFiring zeroTerm y demoChan pZero y ρ 0 1 2 3 :
      Firing ℕ E (commProgram zeroTerm y demoChan pZero y) PUnit.unit).Fresh X (embed labels start)) :
    psubst ρ (dotted (pvars zeroTerm ++ pvars y) y) ≠ dotted (pvars zeroTerm ++ pvars y) y :=
  opened_row_moves₂ labels start zeroTerm y demoChan pZero y ρ 0 1 2 3 rfl (by decide +kernel) fresh
    (x := "y") (by decide +kernel)

/-- The labels that put the opened made rows `0` and `@z` on identities `2` and `3`. -/
def keptLabels : ℕ → Pattern := fun n =>
  if n = 0 then sender else if n = 1 then receiver else if n = 2 then pZero else nQuote (.fvar "z")

/-- **With the opened made rows on the made identities, the firing passes through `firstOrder_eq`**: it
is a transition of the label-keeping step of the program, and of the first-order step restricted to the
fresh openings of the program. -/
theorem example_through_firstOrder :
    Succ (keeping patternAction (commProgram zeroTerm y demoChan pZero y)) (embed keptLabels start)
        (embed keptLabels ((commSelection 0 1 2 3).result keptLabels
          ((commRule zeroTerm y demoChan pZero y).map (psubst toZ)) start)) ∧
      Succ (firstOrderOn patternAction keptLabels (commProgram zeroTerm y demoChan pZero y)) start
        ((commSelection 0 1 2 3).result keptLabels ((commRule zeroTerm y demoChan pZero y).map (psubst toZ))
          start) :=
  comm_firstOrderOn keptLabels zeroTerm y demoChan pZero y unifier unifier_groundPrincipal
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) start 0 1 2 3 rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ⟨fun _ => none, fun _ member => absurd member List.not_mem_nil⟩
    (example_fresh keptLabels rfl rfl) (by decide +kernel) (by decide +kernel)

/-! ## The manuscript's canary: the literal reading and the variable convention -/

/-- The free name `a`. -/
def a : Pattern := .fvar "a"

/-- The canary's rows, `for(a <- @0)a` at `0` and `for(0 <- @0)a` at `1`: the second's free `a` is
written with the first's bound name. -/
def canaryLabels : ℕ → Pattern := fun n =>
  if n = 0 then pFor a demoChan a else if n = 1 then pFor pZero demoChan a else pZero

/-- The unifier `a ↦ 0`. -/
def canaryUnifier : Bindings := [("a", pZero)]

theorem canary_unify : MeTTaCalculus.Corrected.unify a pZero = some canaryUnifier := by decide +kernel

theorem canary_groundPrincipal : GroundPrincipal a pZero canaryUnifier := by
  refine groundPrincipal_of_principal (MeTTaCalculus.Corrected.unify_principal canary_unify) ?_
  intro x member
  have vars : pvars a ++ pvars pZero = ["a"] := by decide +kernel
  rw [vars, List.mem_singleton] at member
  subst member
  exact ⟨pZero, by decide +kernel, by decide +kernel⟩

/-- The COMM firing of the canary, opened by `a ↦ b`. -/
abbrev canaryFiring : Firing ℕ E (commProgram a pZero demoChan a a) PUnit.unit :=
  commFiring a pZero demoChan a a (renameBy fun _ => "b") 0 1 2 3

theorem canary_fresh : canaryFiring.Fresh X (embed canaryLabels start) := by
  refine fresh_of_renaming (embed canaryLabels start) canaryFiring (fun _ => "b") rfl (by decide +kernel) ?_
  intro x _ m mentions
  rcases mentions with known | known | ⟨o, present, rfl⟩
  · simp [embed, start] at known
  · simp [embed, start] at known
  · have zeroOrOne : o = 0 ∨ o = 1 := by simpa [embed, start] using present
    rcases zeroOrOne with rfl | rfl
    · show "b" ∉ pvars (canaryLabels 0)
      decide +kernel
    · show "b" ∉ pvars (canaryLabels 1)
      decide +kernel

/-- **Control: the variable convention.** On the manuscript's canary `for(a <- @0)a | for(0 <- @0)a`, the
side conditions of `comm_one_firing` hold, and every solution reads the second made row as `@0`: the
step follows the literal rule, which identifies the second process's free `a` with the first's bound
`a`. The variable convention fails there, and the corrected step keeps `a` free: its reduct is
`@0 | a`. -/
theorem canary_reads_literally :
    (∀ σ : PSubst, patternAction.Models σ (canaryFiring.result X (embed canaryLabels start)).knowledge →
      psubst σ ((canaryFiring.result X (embed canaryLabels start)).label 3) = nQuote pZero) ∧
      ¬ MeTTaCalculus.Corrected.Apart a a pZero a ∧
      MeTTaCalculus.Corrected.cstep MeTTaCalculus.demoCommSource = [par (nQuote pZero) a] := by
  obtain ⟨-, -, reads⟩ := comm_one_firing canaryLabels a pZero demoChan a a canaryUnifier
    canary_groundPrincipal (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    start 0 1 2 3 rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨fun _ => none, fun _ member => absurd member List.not_mem_nil⟩ canary_fresh
  refine ⟨fun σ solved => ?_, fun apart => apart.leftOutside "a" (by decide +kernel) (by decide +kernel),
    by decide +kernel⟩
  rw [(reads σ solved).2]
  decide +kernel

/-- The renamed canary's rows, `for(a1 <- @0)a1` at `0` and `for(0 <- @0)a` at `1`. -/
def renamedLabels : ℕ → Pattern := fun n =>
  if n = 0 then pFor (.fvar "a1") demoChan (.fvar "a1") else if n = 1 then pFor pZero demoChan a else pZero

/-- The unifier `a1 ↦ 0`. -/
def renamedUnifier : Bindings := [("a1", pZero)]

theorem renamed_unify : MeTTaCalculus.Corrected.unify (.fvar "a1") pZero = some renamedUnifier := by
  decide +kernel

/-- The COMM firing of the renamed canary, opened by `a1 ↦ b1`, `a ↦ b`. -/
abbrev renamedFiring : Firing ℕ E (commProgram (.fvar "a1") pZero demoChan (.fvar "a1") a) PUnit.unit :=
  commFiring (.fvar "a1") pZero demoChan (.fvar "a1") a (renameBy fun v => if v = "a1" then "b1" else "b")
    0 1 2 3

theorem renamed_fresh : renamedFiring.Fresh X (embed renamedLabels start) := by
  refine fresh_of_renaming (embed renamedLabels start) renamedFiring
    (fun v => if v = "a1" then "b1" else "b") rfl (by decide +kernel) ?_
  intro x _ m mentions
  rcases mentions with known | known | ⟨o, present, rfl⟩
  · simp [embed, start] at known
  · simp [embed, start] at known
  · have zeroOrOne : o = 0 ∨ o = 1 := by simpa [embed, start] using present
    rcases zeroOrOne with rfl | rfl
    · show (if x = "a1" then "b1" else "b") ∉ pvars (renamedLabels 0)
      split <;> decide +kernel
    · show (if x = "a1" then "b1" else "b") ∉ pvars (renamedLabels 1)
      split <;> decide +kernel

/-- **The canary renamed apart, through the corrected step.** With the first input's bound name renamed,
the variable convention holds; the COMM firing is admitted, the corrected step relates the redex to its
reduct, and every solution `σ` reads the made rows as `@0` and as the free name `a` read through `σ`: the
corrected reduct `@0 | a`, which the tree's executable corrected step computes. -/
theorem renamed_canary_corrected :
    (RuleSyntax.step X ℕ E (commProgram (.fvar "a1") pZero demoChan (.fvar "a1") a)).Admits
        (s := embed renamedLabels start) renamedFiring ∧
      MeTTaCalculus.Corrected.Step MeTTaCalculus.Corrected.conventional
        (par (pFor (.fvar "a1") demoChan (.fvar "a1")) (pFor pZero demoChan a))
        (par (applyDot renamedUnifier (.fvar "a1")) (applyDot renamedUnifier a)) ∧
      (∀ σ : PSubst, patternAction.Models σ (renamedFiring.result X (embed renamedLabels start)).knowledge →
        psubst σ ((renamedFiring.result X (embed renamedLabels start)).label 2) = nQuote pZero ∧
          psubst σ ((renamedFiring.result X (embed renamedLabels start)).label 3) = psubst σ a) ∧
      MeTTaCalculus.Corrected.cstep (par (pFor (.fvar "a1") demoChan (.fvar "a1")) (pFor pZero demoChan a)) =
        [par (nQuote pZero) a] := by
  obtain ⟨admitted, manuscript, -, bound⟩ := comm_one_firing_corrected renamedLabels (.fvar "a1") pZero
    demoChan (.fvar "a1") a renamedUnifier (MeTTaCalculus.Corrected.unify_principal renamed_unify)
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by decide +kernel) (by decide +kernel) start 0 1 2 3 rfl rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    ⟨fun _ => none, fun _ member => absurd member List.not_mem_nil⟩ renamed_fresh
  have binds : ∀ v ∈ pvars (.fvar "a1") ++ pvars a, v ∈ pvars (.fvar "a1") ++ pvars pZero →
      ∃ w, renamedUnifier.lookup v = some w := by
    intro v _ inPattern
    have vars : pvars (.fvar "a1") ++ pvars pZero = ["a1"] := by decide +kernel
    rw [vars, List.mem_singleton] at inPattern
    subst inPattern
    exact ⟨pZero, by decide +kernel⟩
  have dot₂ : applyDot renamedUnifier (.fvar "a1") = nQuote pZero := by decide +kernel
  have dot₃ : applyDot renamedUnifier a = a := by decide +kernel
  refine ⟨admitted, manuscript, fun σ solved => ?_, by decide +kernel⟩
  obtain ⟨read₂, read₃⟩ := bound binds σ solved
  rw [dot₂, psubst_of_pvars_nil σ (nQuote pZero) (by decide +kernel)] at read₂
  rw [dot₃] at read₃
  exact ⟨read₂, read₃⟩

#print axioms unifier_groundPrincipal
#print axioms example_fresh
#print axioms example_comm
#print axioms example_manuscript
#print axioms example_executable
#print axioms example_result
#print axioms example_knowledge
#print axioms example_reads
#print axioms example_solution
#print axioms apart_needed
#print axioms nonprincipal_misreads
#print axioms subst_misreads
#print axioms open_two_readings
#print axioms made_coincide_refused
#print axioms made_present_refused
#print axioms unopened_refused
#print axioms example_never_keeping
#print axioms example_through_firstOrder
#print axioms canary_reads_literally
#print axioms renamed_canary_corrected

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Comm.Controls
