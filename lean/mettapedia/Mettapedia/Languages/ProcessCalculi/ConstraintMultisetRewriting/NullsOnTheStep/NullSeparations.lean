import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.NullKinds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.IssuedNamesControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RationalStep

/-!
# The emptinesses on the step are separated

Every pair below must differ, and differs on an actual step. Except for the occurs check, the
controls run on the first-order step over ground terms, restricted to a four-rule theory (`sp`):

* `spawn`: if `U` is absent, make `T`;
* `consume`: take `T`, make `U`;
* `drop`: take `T`, make nothing;
* `clash`: tell `T = U`.

## Separations

* **The empty container is not the empty answer set** (`emptyStore_has_successor`,
  `store_without_successor`): the empty store has a successor, and the store holding `U` has none.
* **Absence is not refusal** (`absence_admits`, `refusal_without_absence`,
  `failed_absence_forbids`): where `U` is absent, the guard of `spawn` holds and `spawn` is admitted;
  `consume` is refused at the empty store although it asks no absence; where `U` is present, `spawn`
  is prepared and forbidden.
* **No answers is not one empty answer** (`one_empty_answer`): at the store holding `T`, `drop` leaves
  the empty store, so the state has an answer, and it is empty; the store holding `U` has none.
* **The empty answer set is not the empty type** (`no_successor_with_candidates`): at the store
  holding `U` every candidate is refused, and candidates exist.
* **No solution is not a refusal of permission** (`clash_unsolvable`, `clash_not_forbidden`,
  `spawn_forbidden`): `clash` is refused at every state because its information has no solution;
  `spawn` at the store holding `U` is refused although its information has one.
* **No well-founded solution is relative to the frames** (`occurs_check_relative`): the firing telling
  `X = f(X)` has no solution over finite trees at any configuration, while over rational trees the
  same rule is admitted. Its null is scoped to the frames, not to the firing.

"No verdict" is separated from admission and from refusal in `SchemaGuards`; the two nulls of
absence (known absent, not known present) are separated by `KnowledgeTensorWeight.undetermined_separates`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Separations

open NamesOnTheStep NamesOnTheStep.IssuingControls

def spawn : RuleInstance Expr := rule [] [] [factT] [.absent factU]
def consume : RuleInstance Expr := rule [factT] [] [factU]
def drop : RuleInstance Expr := rule [factT] [] []
def clash : RuleInstance Expr := ⟨[], [], [(factT, factU)], [], []⟩

/-- The theory: its four rules. -/
abbrev theory (f : Fir) : Prop :=
  f.rule = spawn ∨ f.rule = consume ∨ f.rule = drop ∨ f.rule = clash

/-- The first-order step over ground terms, restricted to the theory; nothing is issued. -/
abbrev sp := withLedger base ((fun _ _ f fresh => theory f ∧ fresh = []) : Disc)

def emptyS : Conf × Set ℕ := (⟨[], ∅⟩, ∅)
def onlyU : Conf × Set ℕ := (⟨[], {(factU, 0)}⟩, ∅)
def onlyT : Conf × Set ℕ := (⟨[], {(factT, 0)}⟩, ∅)

def spawnAt : Fir × List ℕ := (⟨spawn, [], ⟨[], [], [(factT, 0)]⟩⟩, [])
def dropAt : Fir × List ℕ := (⟨drop, [], ⟨[(factT, 0)], [], []⟩⟩, [])
def clashAt : Fir × List ℕ := (⟨clash, [], ⟨[], [], []⟩⟩, [])

/-! ## Reading refusals -/

/-- A firing that takes `T` is refused where no `T` is present. -/
theorem takes_T_refused {σ : Conf × Set ℕ} (absentT : ∀ o ∈ σ.1.present, o.1 ≠ factT)
    (f : Fir × List ℕ) (takesT : f.1.rule.take = [factT]) : ¬ sp.Admits (s := σ) f := by
  intro admitted
  have valid := valid_of admitted
  have takes := takes_match valid
  rw [takesT] at takes
  obtain ⟨o, taken, isT⟩ := match_one takes
  exact absentT o (taken_present valid (by rw [taken]; simp)) isT.symm

/-- `clash` has no solution at any state. -/
theorem clash_unsolvable (σ : Conf × Set ℕ) (f : Fir × List ℕ) (isClash : f.1.rule = clash) :
    Unsolvable sp (s := σ) f := by
  rintro ⟨_, u, solved⟩
  have same : factT = factU := solved (factT, factU) (by
    show (factT, factU) ∈ f.1.selection.problem Prod.fst f.1.rule σ.1
    rw [isClash]
    simp [Selection.problem, clash])
  simp [factT, factU] at same

/-! ## The empty container and the empty answer set -/

theorem spawn_admitted : sp.Admits (s := emptyS) spawnAt := by
  refine admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl ?_
    ⟨Or.inl rfl, rfl⟩
  intro c member
  simp only [spawn, rule, List.mem_singleton] at member
  subst member
  exact absent_holds (by decide)

/-- **The store holding `U` has no successor.** -/
theorem onlyU_no_successor : NoSuccessor sp onlyU := by
  intro f admitted
  have valid := valid_of admitted
  rcases admitted.2.1 with isSpawn | isConsume | isDrop | isClash
  · exact absent_refuted valid (p := factU) (by rw [isSpawn]; simp [spawn, rule])
      (o := (factU, 0)) (by decide) rfl
  · exact takes_T_refused (by decide) f (by rw [isConsume]; rfl) admitted
  · exact takes_T_refused (by decide) f (by rw [isDrop]; rfl) admitted
  · exact unsolvable_refused (clash_unsolvable onlyU f isClash) admitted

/-- **The empty container is not the empty answer set**, one way. -/
theorem emptyStore_has_successor : EmptyStore sp emptyS ∧ ¬ NoSuccessor sp emptyS :=
  ⟨rfl, fun none => none spawnAt spawn_admitted⟩

/-- **The empty container is not the empty answer set**, the other way. -/
theorem store_without_successor : ¬ EmptyStore sp onlyU ∧ NoSuccessor sp onlyU :=
  ⟨fun empty => by
      have none : ({(factU, 0)} : Finset Occ) = ∅ := empty
      simp at none, onlyU_no_successor⟩

/-! ## Absence and refusal -/

/-- **Absence admits**: where `U` is absent, the guard holds and `spawn` is admitted. -/
theorem absence_admits :
    (Check.absent factU).Holds ground () Prod.fst emptyS.1.present ∧ sp.Admits (s := emptyS) spawnAt :=
  ⟨absent_holds (by decide), spawn_admitted⟩

/-- **Refusal without absence**: `consume` asks no absence, and is refused at the empty store. -/
theorem refusal_without_absence :
    consume.checks = [] ∧ ∀ f : Fir × List ℕ, f.1.rule = consume → ¬ sp.Admits (s := emptyS) f :=
  ⟨rfl, fun f isConsume => takes_T_refused (by decide) f (by rw [isConsume]; rfl)⟩

/-- `spawn` is prepared at the store holding `U`. -/
theorem spawn_prepared : sp.Prepares (s := onlyU) spawnAt := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl⟩, by decide, PUnit.unit, (), ?_⟩
  intro e member
  exact absurd (show e ∈ ([] : List (Equation Expr)) from member) List.not_mem_nil

/-- **Failed absence forbids**: at the store holding `U`, `spawn` is prepared and refused. -/
theorem spawn_forbidden : Forbidden sp (s := onlyU) spawnAt :=
  ⟨spawn_prepared, onlyU_no_successor spawnAt⟩

/-! ## No answers, one empty answer -/

theorem drop_admitted : sp.Admits (s := onlyT) dropAt :=
  admits_of (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
    ⟨Or.inr (Or.inr (Or.inl rfl)), rfl⟩

/-- **One answer, and it is the empty store**: not the empty answer set of the store holding `U`. -/
theorem one_empty_answer : EmptyAnswer sp onlyT ∧ ¬ NoSuccessor sp onlyT ∧ NoSuccessor sp onlyU :=
  ⟨⟨dropAt, drop_admitted, by decide⟩, fun none => none dropAt drop_admitted, onlyU_no_successor⟩

/-! ## The empty answer set and the empty type -/

/-- **Every candidate refused is not no candidate.** -/
theorem no_successor_with_candidates :
    NoSuccessor sp onlyU ∧ ¬ NoCandidate (Firing := fun _ : Conf × Set ℕ => Fir × List ℕ) onlyU :=
  ⟨onlyU_no_successor, fun none => none.false spawnAt⟩

/-! ## No solution and refusal of permission -/

/-- **No solution is not a refusal of permission.** -/
theorem clash_not_forbidden (σ : Conf × Set ℕ) :
    Refused sp (s := σ) clashAt ∧ ¬ Forbidden sp (s := σ) clashAt :=
  ⟨unsolvable_refused (clash_unsolvable σ clashAt rfl),
    unsolvable_not_forbidden (clash_unsolvable σ clashAt rfl)⟩

/-- **A refusal of permission has a solution**: `spawn` at the store holding `U`. -/
theorem forbidden_has_solution :
    Forbidden sp (s := onlyU) spawnAt ∧ ¬ Unsolvable sp (s := onlyU) spawnAt :=
  ⟨spawn_forbidden, fun unsolvable => unsolvable (forbidden_solvable spawn_forbidden)⟩

/-! ## No well-founded solution is relative to the frames -/

section Occurs

open Mettapedia.Logic.LP
open Rational Rational.Controls

/-- Over finite trees, the firing telling `X = f(X)` has no solution, at every configuration. -/
theorem finite_no_solution {O : Type*} [DecidableEq O] (label : O → Term ctlSig)
    (C : Configuration (Term ctlSig) O) :
    Unsolvable (AnnotatedRuns.firstOrder (FirstOrder.action ctlSig) label).toStep (s := C)
      (tellLoopFinite (O := O)) := by
  rintro ⟨_, θ, solved⟩
  apply finite_occurs
  refine ⟨θ, fun e member => solved e ?_⟩
  obtain rfl := List.mem_singleton.mp member
  show (X, un .f X) ∈ (tellLoopFinite (O := O)).selection.problem label
    (tellLoopFinite (O := O)).rule C
  simp [Selection.problem, tellLoopFinite]

/-- **The occurs-check null is scoped to the frames**: over finite trees the firing has no solution
anywhere, so it is refused, and never by permission; over rational trees the same rule is admitted. -/
theorem occurs_check_relative {O : Type*} [DecidableEq O] (finiteLabel : O → Term ctlSig)
    (rationalLabel : O → RTree ctlSig) (present : Finset O) :
    (∀ C : Configuration (Term ctlSig) O,
      Refused (AnnotatedRuns.firstOrder (FirstOrder.action ctlSig) finiteLabel).toStep (s := C)
          (tellLoopFinite (O := O)) ∧
        ¬ Forbidden (AnnotatedRuns.firstOrder (FirstOrder.action ctlSig) finiteLabel).toStep (s := C)
          (tellLoopFinite (O := O))) ∧
      (rationalStep ctlSig rationalLabel).Admits (s := ⟨[], present⟩) (tellLoop (O := O)) :=
  ⟨fun C => ⟨unsolvable_refused (finite_no_solution finiteLabel C),
      unsolvable_not_forbidden (finite_no_solution finiteLabel C)⟩,
    tellLoop_admitted rationalLabel present⟩

end Occurs

#print axioms emptyStore_has_successor
#print axioms store_without_successor
#print axioms absence_admits
#print axioms refusal_without_absence
#print axioms spawn_forbidden
#print axioms one_empty_answer
#print axioms no_successor_with_candidates
#print axioms clash_not_forbidden
#print axioms forbidden_has_solution
#print axioms occurs_check_relative

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Separations
