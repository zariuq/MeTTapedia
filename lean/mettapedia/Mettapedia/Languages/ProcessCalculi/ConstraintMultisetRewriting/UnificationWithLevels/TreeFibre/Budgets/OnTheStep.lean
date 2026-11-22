import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Budgets.UnifierControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.RankSettlerControls

/-!
# Exhaustion on the step: an observation, never a refusal

The step whose admission is the question is the converting step with the semantic settler
(`convertingStep levels O (Settler.ideal levels)`): its admission asks the information to be solvable, each made row
to convert along an initial solution, the enabling and the guards. It takes no budget.

**On a firing that only tells** (it takes, reads, makes, guards and queries nothing, `OnlyTells`), admission is the
solvability of its information, for every settler (`onlyTells_admits_iff`). So every budgeted decision procedure of
stores decides it soundly: **solved implies admitted** (`admits_of_equal`), **refuted implies not admitted**
(`not_admits_of_different`), and **exhausted implies neither**: the cross firing, telling the cross store, is
exhausted at every budget by every decision of stores and admitted (`cross_exhausted_admitted`); the firing telling
`U0 : U1 ≐ U0 : U2` is exhausted at every depth of phases and refused (`het_exhausted_refused`).

**On firings with rows** and without guards or queries, the computable settler's families decide admission at the
answer (`admits?`, which declines every firing with guards or queries); read against the semantic step, that is a
budgeted decision procedure of the semantic step's admission (`admission`): yes means admitted, no means refused
(`ideal_iff_of_admits`), for every list of families. With the families at a budget of rounds (`budgetedFamilies`):
* the lifting firing, whose made row is typed only after the match, is exhausted at budgets `0` and `1` and admitted
  at `2` (`lift_exhausted_then_admitted`);
* the cross firing is exhausted at every budget, for every list of families, though admitted
  (`cross_admission_exhausted`): law 4 needs its hypothesis here too;
* the firing telling `U0 : U1 ≐ U0 : U2` is exhausted at budget `0` and refused at budget `1`
  (`het_exhausted_then_refused`).

**A settler that runs out inside the step is a state-changing checker.** The computable converting step settles along
its settler's answer and falls back to the present step when the settler postpones; at budget `1` it refuses the
lifting firing and at budget `2` it admits it, while the semantic step admits it (`lift_cliff`). So exhaustion there
is read as refusal.

**The report.** The handler that runs the decision reports its verdict beside the step (`report`, `handle`): the
state the step reaches is the semantic step's result, the same at every budget, so every later answer is unchanged
(`handle_state_budget_free`, `later_budget_free`); the report is sound (`report_equal`, `report_different`) and makes
no row.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre.Budgets.OnTheStep

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (State Firing)
open NativeTypesOnTheStep
open NativeTypesOnTheStep.Computing

/-! ## Firings that only tell -/

section Generic

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} (levels : LevelModel rules L)
variable {O : Type} [DecidableEq O]

/-- **A firing that only tells**: it takes, reads, makes, guards and queries nothing. -/
structure OnlyTells {s : State rules O} (f : Firing levels s) : Prop where
  taken : f.taken = []
  read : f.read = []
  takes : f.takes = []
  reads : f.reads = []
  makes : f.makes = []
  guards : f.guards = []
  queries : f.queries = []

/-- **A firing that only tells is admitted exactly when its information has a solution**, for every settler. -/
theorem onlyTells_admits_iff (settler : Settler levels) {s : State rules O} {f : Firing levels s}
    (tells : OnlyTells levels f) :
    (convertingStep levels O settler).Admits f ↔ (frames levels).Solvable f.information := by
  constructor
  · exact fun admitted => admitted.2.2.1
  · intro solvable
    have made : f.made = [] := by simp [Interface.DependentFull.Firing.made, tells.makes]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, (Interface.DependentFull.enabled_iff f).mpr ⟨?_, ?_, ?_, ?_⟩, solvable, ?_⟩
    · simp [tells.taken]
    · simp [made]
    · simp [tells.takes, tells.taken]
    · simp [tells.reads, tells.read]
    · simp [tells.makes]
    · simp [tells.taken]
    · simp [tells.read]
    · simp [tells.taken]
    · simp [made]
    · intro Δ τ _
      refine ⟨?_, ?_⟩
      · rw [tells.guards]
        exact Frames.models_nil (X := frames levels) τ
      · simp [tells.queries]

end Generic

section Verdicts

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable {O : Type} [DecidableEq O]

/-- **Solved implies admitted**, on a firing that only tells, for every budgeted decision procedure of stores. -/
theorem admits_of_equal (D : Procedure (HasSolution (S := S))) (settler : Settler S.levels) {s : State S.R O}
    {f : Firing S.levels s} (tells : OnlyTells S.levels f) {k : Nat}
    (yes : D.verdict k ⟨f.helpers.frame, f.information⟩ = .equal) : (convertingStep S.levels O settler).Admits f :=
  (onlyTells_admits_iff S.levels settler tells).mpr (D.equal_sound yes)

/-- **Refuted implies not admitted.** -/
theorem not_admits_of_different (D : Procedure (HasSolution (S := S))) (settler : Settler S.levels)
    {s : State S.R O} {f : Firing S.levels s} (tells : OnlyTells S.levels f) {k : Nat}
    (no : D.verdict k ⟨f.helpers.frame, f.information⟩ = .different) :
    ¬ (convertingStep S.levels O settler).Admits f :=
  fun admitted => D.different_sound no ((onlyTells_admits_iff S.levels settler tells).mp admitted)

end Verdicts

/-! ## The tower's step -/

section Tower

open Interface.DependentFull.Controls (setting emptyState)
open ContextualDependentSweep.Witnesses (ctxCross crossStore ctxSmall largeFamily cross_identity)
open NativeTypesOnTheStep.ComputableControls (admits? admits?_sound liftFiring lift_separation)

/-- Firings of the tower's step. -/
abbrev Firings : Type := Σ s : State setting.R Nat, Firing setting.levels s

/-- **Admission by the semantic step.** -/
def IdealAdmits (q : Firings) : Prop :=
  (convertingStep setting.levels Nat (Settler.ideal setting.levels)).Admits q.2

/-! ### Exhausted implies neither, on firings that only tell -/

/-- The state over the cross store's telescope, knowing nothing. -/
def crossState : State setting.R Nat := ⟨ctxCross, [], ∅, fun _ => Elimination.last ctxSmall largeFamily⟩

/-- **The cross firing**: it tells the cross store. -/
def crossFiring : Firing setting.levels crossState where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := []
  tells := crossStore
  guards := []
  queries := []

theorem crossFiring_tells : OnlyTells setting.levels crossFiring := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Exhausted at every budget by every decision of stores, and admitted.** -/
theorem cross_exhausted_admitted
    (attempt : Nat → ∀ {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)), Option (Decided problem))
    (k : Nat) :
    (ofDecided attempt).procedure.verdict k ⟨crossFiring.helpers.frame, crossFiring.information⟩ = .undecided ∧
      IdealAdmits ⟨_, crossFiring⟩ :=
  ⟨undecided_of_no_principal attempt cross_identity
      (fun answer => ContextualDependentSweep.Witnesses.cross_no_principal answer) k,
    (onlyTells_admits_iff setting.levels (Settler.ideal setting.levels) crossFiring_tells).mpr cross_identity⟩

/-- **The firing telling `U0 : U1 ≐ U0 : U2`.** -/
def hetFiring : Firing setting.levels emptyState where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := []
  tells := TowerControls.hetStore
  guards := []
  queries := []

theorem hetFiring_tells : OnlyTells setting.levels hetFiring := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Exhausted at every depth of phases, and refused.** -/
theorem het_exhausted_refused (k : Nat) :
    TowerControls.towerPhasesDepth.procedure.verdict k ⟨hetFiring.helpers.frame, hetFiring.information⟩ =
        .undecided ∧ ¬ IdealAdmits ⟨_, hetFiring⟩ :=
  ⟨TowerControls.het_phases_exhausted k,
    fun admitted => TowerControls.het_unsolvable
      ((onlyTells_admits_iff setting.levels (Settler.ideal setting.levels) hetFiring_tells).mp admitted)⟩

/-! ### Admission decided at the answer, read against the semantic step -/

/-- A first decisive family is a decisive family of the list. -/
theorem decidedBy_of_first {Δ : Context setting.R} {I : EquationStore (TotalTerm Δ)} :
    ∀ {families : List (NativeTypesOnTheStep.Family setting.levels)},
      (firstDecisionAt setting.levels I families).Decisive → DecidedBy setting.levels families I
  | [], decisive => False.elim decisive
  | F :: rest, decisive => by
      unfold firstDecisionAt at decisive
      cases h : F I with
      | settled M σ initial => exact ⟨F, List.mem_cons_self, by show (F I).Decisive; rw [h]; trivial⟩
      | refuted absent => exact ⟨F, List.mem_cons_self, by show (F I).Decisive; rw [h]; trivial⟩
      | undecided =>
          rw [h] at decisive
          obtain ⟨G, member, decisiveG⟩ := decidedBy_of_first decisive
          exact ⟨G, List.mem_cons_of_mem _ member, decisiveG⟩

/-- **A store the families leave undecided, all of them, is undecided first.** -/
theorem first_undecided {Δ : Context setting.R} {I : EquationStore (TotalTerm Δ)}
    (undecided : ∀ F : NativeTypesOnTheStep.Family setting.levels, ¬ (F I).Decisive) :
    ∀ families : List (NativeTypesOnTheStep.Family setting.levels),
      firstDecisionAt setting.levels I families = .undecided
  | [] => rfl
  | F :: rest => by
      unfold firstDecisionAt
      cases h : F I with
      | settled M σ initial => exact (undecided F (by rw [h]; trivial)).elim
      | refuted absent => exact (undecided F (by rw [h]; trivial)).elim
      | undecided => exact first_undecided undecided rest

/-- An answer of `admits?` comes from a decisive family. -/
theorem decidedBy_of_admits {families : List (NativeTypesOnTheStep.Family setting.levels)}
    {s : State setting.R Nat} {f : Firing setting.levels s} {b : Bool} (decided : admits? families f = some b) :
    DecidedBy setting.levels families f.information := by
  apply decidedBy_of_first
  unfold admits? at decided
  split at decided
  · cases first : firstDecisionAt setting.levels f.information families with
    | settled M σ initial => trivial
    | refuted absent => trivial
    | undecided =>
        rw [first] at decided
        simp at decided
  · cases decided

/-- **An answer of `admits?` is the semantic step's admission**: yes is admitted, no is refused. -/
theorem ideal_iff_of_admits {families : List (NativeTypesOnTheStep.Family setting.levels)}
    {s : State setting.R Nat} {f : Firing setting.levels s} {b : Bool} (decided : admits? families f = some b) :
    b = true ↔ IdealAdmits ⟨s, f⟩ :=
  (admits?_sound families decided).trans
    (ofFamilies_converting_iff_ideal setting.levels families (decidedBy_of_admits decided))

/-- When every family leaves the information undecided, `admits?` answers nothing. -/
theorem admits_none_of_undecided {families : List (NativeTypesOnTheStep.Family setting.levels)}
    {s : State setting.R Nat} {f : Firing setting.levels s}
    (undecided : firstDecisionAt setting.levels f.information families = .undecided) : admits? families f = none := by
  unfold admits?
  split
  · simp only [undecided]
  · rfl

/-- The answer of `admits?`, with what it means for the semantic step. -/
def admissionAt (families : List (NativeTypesOnTheStep.Family setting.levels)) {s : State setting.R Nat}
    (f : Firing setting.levels s) : Option {b : Bool // b = true ↔ IdealAdmits ⟨s, f⟩} :=
  match h : admits? families f with
  | none => none
  | some b => some ⟨b, ideal_iff_of_admits h⟩

/-- **The semantic step's admission as a budgeted decision**: at each budget, the computable settler's families at
that budget decide admission at their answer, or decline. -/
def admission (families : Nat → List (NativeTypesOnTheStep.Family setting.levels)) : Decider IdealAdmits where
  Answer q := {b : Bool // b = true ↔ IdealAdmits q}
  attempt k q := admissionAt (families k) q.2
  sign a := a.val
  yes a h := a.property.mp h
  no a h admitted := by
    have holds := a.property.mpr admitted
    rw [h] at holds
    cases holds

theorem admission_none {families : Nat → List (NativeTypesOnTheStep.Family setting.levels)} {k : Nat} {q : Firings}
    (h : admits? (families k) q.2 = none) : (admission families).attempt k q = none := by
  show admissionAt (families k) q.2 = none
  unfold admissionAt
  split
  · rfl
  · rename_i b heq
    exact absurd (heq.symm.trans h) (by simp)

theorem admission_some {families : Nat → List (NativeTypesOnTheStep.Family setting.levels)} {k : Nat} {q : Firings}
    {b : Bool} (h : admits? (families k) q.2 = some b) :
    ∃ a, (admission families).attempt k q = some a ∧ a.val = b := by
  show ∃ a, admissionAt (families k) q.2 = some a ∧ a.val = b
  unfold admissionAt
  split
  · rename_i heq
    exact absurd (heq.symm.trans h) (by simp)
  · rename_i b' heq
    exact ⟨_, rfl, Option.some.inj (heq.symm.trans h)⟩

/-- **The computable settler's families at a budget of rounds.** -/
def budgetedFamilies (k : Nat) : List (NativeTypesOnTheStep.Family setting.levels) :=
  [driverFamily setting.levels ContextualDependentWorklist.Controls.step k, OlderUnknown.olderFamily k,
    MillerFamily.millerFamily k]

theorem lift_kernel :
    admits? (budgetedFamilies 0) liftFiring = none ∧ admits? (budgetedFamilies 1) liftFiring = none ∧
      admits? (budgetedFamilies 2) liftFiring = some true ∧
      (firstDecisionAt setting.levels liftFiring.information (budgetedFamilies 1)).isSettled = false := by
  decide +kernel

/-- **Exhausted at budgets `0` and `1`, admitted at `2`.** -/
theorem lift_exhausted_then_admitted :
    (admission budgetedFamilies).procedure.verdict 1 ⟨_, liftFiring⟩ = .undecided ∧
      (admission budgetedFamilies).procedure.verdict 2 ⟨_, liftFiring⟩ = .equal := by
  obtain ⟨zero, one, two, _⟩ := lift_kernel
  obtain ⟨a, ha, hval⟩ := admission_some (families := budgetedFamilies) (k := 2) (q := ⟨_, liftFiring⟩) two
  have before : ∀ j, j ≤ 1 → (admission budgetedFamilies).attempt j ⟨_, liftFiring⟩ = none := by
    intro j le
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact admission_none (families := budgetedFamilies) (k := 0) zero
    · exact admission_none (families := budgetedFamilies) (k := 1) one
  obtain ⟨exhausted, next⟩ := (admission budgetedFamilies).verdict_first before ha
  refine ⟨exhausted, ?_⟩
  rw [next]
  simp [Decider.verdictOf, admission, hval]

/-- **The cross firing is exhausted at every budget, for every list of families**, though the semantic step admits
it. -/
theorem cross_admission_exhausted (families : Nat → List (NativeTypesOnTheStep.Family setting.levels)) (k : Nat) :
    (admission families).procedure.verdict k ⟨_, crossFiring⟩ = .undecided ∧ IdealAdmits ⟨_, crossFiring⟩ :=
  ⟨(admission families).undecided_of_none fun j _ =>
      admission_none (families := families) (k := j)
        (admits_none_of_undecided
          (first_undecided (fun F => OlderUnknown.Controls.cross_undecided F) (families j))),
    (cross_exhausted_admitted (fun _ _ _ => none) 0).2⟩

theorem het_kernel :
    admits? (budgetedFamilies 0) hetFiring = none ∧ admits? (budgetedFamilies 1) hetFiring = some false := by
  decide +kernel

/-- **Exhausted at budget `0`, refused at budget `1`.** -/
theorem het_exhausted_then_refused :
    (admission budgetedFamilies).procedure.verdict 0 ⟨_, hetFiring⟩ = .undecided ∧
      (admission budgetedFamilies).procedure.verdict 1 ⟨_, hetFiring⟩ = .different ∧ ¬ IdealAdmits ⟨_, hetFiring⟩ := by
  obtain ⟨zero, one⟩ := het_kernel
  obtain ⟨a, ha, hval⟩ := admission_some (families := budgetedFamilies) (k := 1) (q := ⟨_, hetFiring⟩) one
  have before : ∀ j, j ≤ 0 → (admission budgetedFamilies).attempt j ⟨_, hetFiring⟩ = none := by
    intro j le
    rw [Nat.le_zero.mp le]
    exact admission_none (families := budgetedFamilies) (k := 0) zero
  obtain ⟨exhausted, next⟩ := (admission budgetedFamilies).verdict_first before ha
  refine ⟨exhausted, ?_, (het_exhausted_refused 0).2⟩
  rw [next]
  simp [Decider.verdictOf, admission, hval]

/-! ### A settler that runs out inside the step -/

theorem ofFamilies_postponed {families : List (NativeTypesOnTheStep.Family setting.levels)} {Δ : Context setting.R}
    {I : EquationStore (TotalTerm Δ)} (unsettled : (firstDecisionAt setting.levels I families).isSettled = false) :
    Settler.ofFamilies setting.levels families I = .postponed := by
  unfold Settler.ofFamilies
  cases h : firstDecisionAt setting.levels I families with
  | settled M σ initial =>
      rw [h] at unsettled
      cases unsettled
  | refuted absent => rfl
  | undecided => rfl

/-- **The computable step reads exhaustion as refusal**: with the families at budget `1` its settler postpones the
lifting firing and the step refuses it; at budget `2` it admits it; the semantic step admits it. -/
theorem lift_cliff :
    ¬ (convertingStep setting.levels Nat (Settler.ofFamilies setting.levels (budgetedFamilies 1))).Admits liftFiring ∧
      (convertingStep setting.levels Nat (Settler.ofFamilies setting.levels (budgetedFamilies 2))).Admits liftFiring ∧
      IdealAdmits ⟨_, liftFiring⟩ := by
  obtain ⟨_, _, two, unsettled⟩ := lift_kernel
  refine ⟨fun admitted => lift_separation.2 ?_, (admits?_sound (budgetedFamilies 2) two).mp rfl,
    (ideal_iff_of_admits two).mp rfl⟩
  exact (converting_admits_iff_of_postponed setting.levels _ (ofFamilies_postponed unsettled)).mp admitted

/-! ### The report: an observation beside the step -/

/-- **The handler's report on a firing at budget `k`.** -/
def report (families : Nat → List (NativeTypesOnTheStep.Family setting.levels)) (k : Nat) (q : Firings) :
    Budgeted.Verdict :=
  (admission families).procedure.verdict k q

open Classical in
/-- **The step with the handler**: the state the semantic step reaches, when it admits, and the report beside it. -/
noncomputable def handle (families : Nat → List (NativeTypesOnTheStep.Family setting.levels)) (k : Nat)
    (q : Firings) : Option (State setting.R Nat) × Budgeted.Verdict :=
  (if admitted : IdealAdmits q then
      some ((convertingStep setting.levels Nat (Settler.ideal setting.levels)).result q.2 admitted)
    else none,
    report families k q)

/-- **The state reached does not depend on the budget.** -/
theorem handle_state_budget_free (families : Nat → List (NativeTypesOnTheStep.Family setting.levels)) (k k' : Nat)
    (q : Firings) : (handle families k q).1 = (handle families k' q).1 :=
  rfl

/-- **So every later answer is the same at every budget.** -/
theorem later_budget_free {α : Type} (later : Option (State setting.R Nat) → α)
    (families : Nat → List (NativeTypesOnTheStep.Family setting.levels)) (k k' : Nat) (q : Firings) :
    later (handle families k q).1 = later (handle families k' q).1 :=
  congrArg later (handle_state_budget_free families k k' q)

/-- **A yes in the report is admission.** -/
theorem report_equal {families : Nat → List (NativeTypesOnTheStep.Family setting.levels)} {k : Nat} {q : Firings}
    (yes : report families k q = .equal) : IdealAdmits q :=
  (admission families).procedure.equal_sound yes

/-- **A no in the report is refusal.** -/
theorem report_different {families : Nat → List (NativeTypesOnTheStep.Family setting.levels)} {k : Nat}
    {q : Firings} (no : report families k q = .different) : ¬ IdealAdmits q :=
  (admission families).procedure.different_sound no

end Tower

end TreeFibre.Budgets.OnTheStep

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

section Audit
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Budgets.OnTheStep
#print axioms onlyTells_admits_iff
#print axioms admits_of_equal
#print axioms not_admits_of_different
#print axioms cross_exhausted_admitted
#print axioms het_exhausted_refused
#print axioms decidedBy_of_admits
#print axioms ideal_iff_of_admits
#print axioms admission
#print axioms lift_exhausted_then_admitted
#print axioms cross_admission_exhausted
#print axioms het_exhausted_then_refused
#print axioms lift_cliff
#print axioms handle_state_budget_free
#print axioms later_budget_free
#print axioms report_equal
#print axioms report_different
end Audit
