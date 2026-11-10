import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DisequalityControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderChecks

/-!
# Conflicting evidence is not an inconsistent store

Evidence and opposition are rows: occurrences in the space, such as an evidence row `ev(p)` and an
opposing row `opp(p)`. An inconsistent store is knowledge: equations with no solution. The two are
kept apart by the step itself.

## An inconsistent store admits nothing (any instance of the interface)

`not_admits_of_not_solvable`: at a state whose knowledge has no solution, **no firing of any instance
of `Interface.Step` is admitted**, and every run from it is empty (`run_word_of_not_solvable`). This
is the interface's form of `FirstOrderChecks.Controls.an_inconsistent_store_cannot_license_a_check`.
In the first-order instance the step never enters such a store: from consistent knowledge, every run
ends in consistent knowledge (`firstOrder_run_consistent`).

## Conflicting rows are data (`Rows`)

* Both rows can be made, and a firing that reads both runs: `conflict_runs` is the run
  `makeEvidence; makeOpposition; weigh`, and the knowledge after the two rows are present is
  consistent (`conflict_consistent`).
* **The rows constrain.** `weigh` reads both rows and is refused while the opposition is missing
  (`weigh_refused_without_opposition`). `accept` reads the evidence under the guard that no
  opposition is present: admitted with the evidence alone (`accept_admitted_with_evidence`) and
  refused once the opposition is present (`accept_refused_with_opposition`).
* **Telling `X = true` and `X = false` is an inconsistent store.** Each tell alone is admitted; after
  `X = true` the tell `X = false` is refused (`tell_false_refused_after_true`), and a state whose
  knowledge holds both admits no firing at all (`both_tells_admit_nothing`).

## Four ways of not finding `p(a)` (`Family`)

One minimized family of states of the step with disequations (`Disequality.step`), over rows
`opp(a)` (row `1`) and `p(X)` (row `2`):

| member | state | absence guard "no `p(a)`" | read `opp(a)` | tell `X = a` | read `p(a)` |
|---|---|---|---|---|---|
| covered absence | nothing present | admitted | refused | admitted | refused |
| refutation row | `opp(a)` present | admitted | admitted | admitted | refused |
| incomplete search | `p(X)` present, `X` open | refused | refused | admitted | admitted |
| disequality | `p(X)` present, `X ≠ a` | admitted | refused | refused | refused |

`table` proves the sixteen verdicts and `profiles_distinct` that no two members have the same
outcome on these four probes. At the incomplete member a scan that skips the open row would license
the absence (`incomplete_scan_would_license`), and it lacks coverage (`skipping_scan_not_covering`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Evidence

open Mettapedia.Logic.LP
open Interface (Frames)
open AnnotatedRuns (firstOrder)
open MeTTaCalculus.OccurrenceCommits (Enabled)

/-! ## An inconsistent store admits nothing -/

section Generic

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}

/-- **No firing of any instance is admitted at knowledge without a solution.** -/
theorem not_admits_of_not_solvable (P : Interface.Step X O State Firing) {s : State}
    (inconsistent : ¬ X.Solvable (P.knowledge s)) (f : Firing s) : ¬ P.Admits f :=
  fun admitted => inconsistent (P.solvable_knowledge admitted)

/-- Every run from knowledge without a solution is empty. -/
theorem run_word_of_not_solvable (P : Interface.Step X O State Firing) {s : State}
    (inconsistent : ¬ X.Solvable (P.knowledge s)) (r : P.Run s) : r.word = [] := by
  cases r with
  | nil => rfl
  | cons f admitted _ => exact absurd admitted (not_admits_of_not_solvable P inconsistent f)

end Generic

section FirstOrderRuns

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

/-- **The first-order step never enters an inconsistent store**: from consistent knowledge, every
run ends in consistent knowledge. -/
theorem firstOrder_run_consistent : ∀ {C : Configuration T O} (r : (firstOrder A label).Run C),
    A.Consistent C.equations → A.Consistent r.last.equations
  | _, .nil _, consistent => consistent
  | _, .cons _ admitted rest, _ => firstOrder_run_consistent rest admitted.firing.consistent

end FirstOrderRuns

/-! ## Conflicting rows are data -/

namespace Rows

open Disequality.Controls (signature A app X E_iff apply_X apply_a apply_b apply_const apply_app
  apply_identity app_eq_app app_ne_const const_ne_app const_eq_const bind bind_zero enabled_empty)

/-- The proposition `p`. -/
def p : Term signature := .const 7

/-- Row `0` is evidence for `p`, row `1` its opposition, row `2` a record that they conflict,
row `3` a record that `p` was accepted. -/
def rows : Nat → Term signature
  | 0 => app 5 p
  | 1 => app 6 p
  | 2 => app 7 p
  | 3 => app 8 p
  | _ => .const 0

abbrev Fir := AnnotatedRuns.Firing (Term signature) (Subst signature) Nat
abbrev P := firstOrder (S := Subst signature) A rows

def start : Configuration (Term signature) Nat := ⟨[], ∅⟩

/-- Make the evidence row. -/
def makeEvidence : Fir := ⟨⟨[], [], [], [], [rows 0]⟩, [], ⟨[], [], [0]⟩⟩
/-- Make the opposing row. -/
def makeOpposition : Fir := ⟨⟨[], [], [], [], [rows 1]⟩, [], ⟨[], [], [1]⟩⟩
/-- Read both rows and record the conflict. -/
def weigh : Fir := ⟨⟨[], [rows 0, rows 1], [], [], [rows 2]⟩, [], ⟨[], [0, 1], [2]⟩⟩
/-- Read the evidence when no opposition is present, and record acceptance. -/
def accept : Fir := ⟨⟨[], [rows 0], [], [.absent (rows 1)], [rows 3]⟩, [], ⟨[], [0], [3]⟩⟩
/-- Tell `X = v`. -/
def tellTruth (v : Nat) : Fir := ⟨⟨[], [], [(X, .const v)], [], []⟩, [], ⟨[], [], []⟩⟩

def withEvidence : Configuration (Term signature) Nat := makeEvidence.result rows start
def withBoth : Configuration (Term signature) Nat := makeOpposition.result rows withEvidence

/-- A ground store whose every equation has equal sides is solved by the identity. -/
theorem identity_models (store : EquationStore (Term signature))
    (reflexive : ∀ e ∈ store, e.1 = e.2) : A.Models A.identity store := by
  intro e member
  show A.apply A.identity e.1 = A.apply A.identity e.2
  rw [reflexive e member]

theorem makeEvidence_admitted : P.Admits (s := start) makeEvidence :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨_, identity_models _ (by
      intro e member
      simp [makeEvidence, Selection.problem, Selection.equations, start] at member)⟩,
      by simp [makeEvidence]⟩

theorem makeOpposition_admitted : P.Admits (s := withEvidence) makeOpposition :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨_, identity_models _ (by
      intro e member
      simp [makeOpposition, makeEvidence, withEvidence, AnnotatedRuns.Firing.result, Selection.result,
        Selection.problem, Selection.equations, start] at member)⟩,
      by simp [makeOpposition]⟩

theorem weigh_admitted : P.Admits (s := withBoth) weigh :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨_, identity_models _ (by
      intro e member
      simp [weigh, makeOpposition, makeEvidence, withBoth, withEvidence, AnnotatedRuns.Firing.result,
        Selection.result, Selection.problem, Selection.equations, start] at member
      rcases member with rfl | rfl <;> rfl)⟩,
      by simp [weigh]⟩

/-- **Both rows are made, and a firing reading both runs.** -/
theorem conflict_runs :
    ∃ r : P.Run start, r.word.map Sigma.snd = [makeEvidence, makeOpposition, weigh] :=
  ⟨.cons makeEvidence makeEvidence_admitted (.cons makeOpposition makeOpposition_admitted
    (.cons weigh weigh_admitted (.nil _))), rfl⟩

/-- **With both rows present, the knowledge is consistent.** -/
theorem conflict_consistent :
    0 ∈ withBoth.present ∧ 1 ∈ withBoth.present ∧ A.Consistent withBoth.equations ∧
      (Frames.ofSubstitution A).Solvable (a := PUnit.unit) (P.knowledge withBoth) :=
  ⟨by decide, by decide, ⟨_, identity_models _ (by
      intro e member
      simp [makeOpposition, makeEvidence, withBoth, withEvidence, AnnotatedRuns.Firing.result,
        Selection.result, Selection.problem, Selection.equations, start] at member)⟩,
    (Frames.ofSubstitution_solvable_iff A _).mpr ⟨_, identity_models _ (by
      intro e member
      simp [P, firstOrder, makeOpposition, makeEvidence, withBoth, withEvidence,
        AnnotatedRuns.Firing.result, Selection.result, Selection.problem, Selection.equations,
        start] at member)⟩⟩

/-- **The rows constrain**: `weigh` needs the opposing row. -/
theorem weigh_refused_without_opposition : ¬ P.Admits (s := withEvidence) weigh :=
  fun admitted => absurd admitted.firing.occurrences.kept_subset (by decide)

theorem accept_admitted_with_evidence : P.Admits (s := withEvidence) accept := by
  refine (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨_, identity_models _ (by
      intro e member
      simp [accept, makeEvidence, withEvidence, AnnotatedRuns.Firing.result, Selection.result,
        Selection.problem, Selection.equations, start] at member
      subst member
      rfl)⟩, ?_⟩
  intro check member σ _
  simp only [accept, List.mem_singleton] at member
  subst member
  intro o present same
  have only : o = 0 := by
    simpa [withEvidence, makeEvidence, AnnotatedRuns.Firing.result, Selection.result,
      MeTTaCalculus.OccurrenceCommits.fire, Selection.commit, start] using present
  subst only
  simp [rows] at same

/-- **The opposition constrains**: once it is present, `accept` is refused. -/
theorem accept_refused_with_opposition : ¬ P.Admits (s := withBoth) accept := by
  intro admitted
  obtain ⟨σ, model⟩ := admitted.firing.consistent
  exact admitted.firing.checks (.absent (rows 1)) (by simp [accept]) σ model 1 (by decide) rfl

/-- The configuration after `X = v`. -/
def told (v : Nat) : Configuration (Term signature) Nat := (tellTruth v).result rows start

theorem tellTruth_admitted (v : Nat) : P.Admits (s := start) (tellTruth v) :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, enabled_empty _, ⟨bind (.const v), by
      intro e member
      simp [tellTruth, Selection.problem, Selection.equations, start] at member
      subst member
      simp [SubstitutionAction.Solves]⟩, by simp [tellTruth]⟩

/-- **After `X = true`, the tell `X = false` is refused**: the step does not enter the inconsistent
store. -/
theorem tell_false_refused_after_true : ¬ P.Admits (s := told 1) (tellTruth 0) := by
  intro admitted
  obtain ⟨σ, model⟩ := admitted.firing.consistent
  have first : σ 0 = .const 1 := model (X, .const 1) (by
    simp [tellTruth, told, AnnotatedRuns.Firing.result, Selection.result, Selection.problem,
      Selection.equations, start])
  have second : σ 0 = .const 0 := model (X, .const 0) (by
    simp [tellTruth, told, AnnotatedRuns.Firing.result, Selection.result, Selection.problem,
      Selection.equations, start])
  rw [first] at second
  simp at second

/-- Knowledge holding `X = true` and `X = false`. -/
def bothTold : Configuration (Term signature) Nat := ⟨[(X, .const 1), (X, .const 0)], withBoth.present⟩

theorem bothTold_inconsistent : ¬ (Frames.ofSubstitution A).Solvable (a := PUnit.unit) (P.knowledge bothTold) := by
  rintro ⟨_, σ, model⟩
  have first : σ 0 = .const 1 := model (X, .const 1) (by simp [P, firstOrder, bothTold])
  have second : σ 0 = .const 0 := model (X, .const 0) (by simp [P, firstOrder, bothTold])
  rw [first] at second
  simp at second

/-- **An inconsistent store admits no firing at all**, though it holds the same rows as `withBoth`,
where `weigh` runs. -/
theorem both_tells_admit_nothing :
    (∀ f : Fir, ¬ P.Admits (s := bothTold) f) ∧ bothTold.present = withBoth.present ∧
      P.Admits (s := withBoth) weigh :=
  ⟨not_admits_of_not_solvable P.toStep (s := bothTold) bothTold_inconsistent, rfl, weigh_admitted⟩

end Rows

/-! ## Four ways of not finding `p(a)` -/

namespace Family

open Disequality (Separates plain step Firing State separates_nil)
open Disequality.Controls (signature A app X a E_iff apply_X apply_a apply_b apply_const apply_app
  apply_identity app_eq_app app_ne_const const_ne_app const_eq_const bind bind_zero apartFrame
  enabled_empty enabled_make)

/-- Row `1` is the opposition `opp(a)`, row `2` the open row `p(X)`, row `10` a marker. -/
def rows : Nat → Term signature
  | 1 => app 1 a
  | 2 => app 0 X
  | 10 => .const 9
  | _ => .const 0

abbrev P := step A rows

/-- The members of the family. -/
inductive Member
  | covered
  | refuted
  | incomplete
  | disequal
  deriving DecidableEq

/-- The four probes. -/
inductive Probe
  | absentP
  | readOpp
  | bindA
  | findP
  deriving DecidableEq

/-- The state of each member. -/
def state : Member → State A Nat
  | .covered => plain ⟨[], ∅⟩
  | .refuted => plain ⟨[], {1}⟩
  | .incomplete => plain ⟨[], {2}⟩
  | .disequal => ⟨⟨[], {2}⟩, apartFrame⟩

/-- The first-order firing of each probe. -/
def probe : Probe → AnnotatedRuns.Firing (Term signature) (Subst signature) Nat
  | .absentP => ⟨⟨[], [], [], [.absent (app 0 a)], [rows 10]⟩, [], ⟨[], [], [10]⟩⟩
  | .readOpp => ⟨⟨[], [app 1 a], [], [], []⟩, [], ⟨[], [1], []⟩⟩
  | .bindA => ⟨⟨[], [], [(X, a)], [], []⟩, [], ⟨[], [], []⟩⟩
  | .findP => ⟨⟨[], [app 0 a], [], [], []⟩, [], ⟨[], [2], []⟩⟩

/-- **The outcome of a member**: which probes its state admits. -/
def profile (m : Member) (π : Probe) : Prop := P.Admits (Firing.ofBase (state m) (probe π))

theorem equations_nil (m : Member) : (state m).configuration.equations = [] := by
  cases m <;> rfl

theorem separates_target' (m : Member) (π : Probe) (σ : Subst signature) :
    Separates A σ (Firing.ofBase (state m) (probe π)).target.1 ↔
      Separates A σ (state m).disequations.1 := by
  show Separates A σ ((state m).disequations.1 ++ []) ↔ _
  rw [List.append_nil]

/-! ### The absence guard -/

theorem absentP_admitted (m : Member) (fresh : 10 ∉ (state m).configuration.present)
    (clear : ∀ σ, Separates A σ (state m).disequations.1 → ∀ o ∈ (state m).configuration.present,
      A.apply σ (app 0 a) ≠ A.apply σ (rows o)) : profile m .absentP := by
  refine ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, enabled_make fresh,
    ⟨A.identity, ?_, ?_⟩, fun σ _ separated => ⟨?_, by simp [probe, Firing.ofBase]⟩⟩
  · intro e member
    simp [Selection.problem, Selection.equations, probe, Firing.ofBase, equations_nil] at member
  · exact (separates_target' m .absentP _).mpr (state m).disequations.2
  · intro check member
    simp only [probe, Firing.ofBase, List.mem_singleton] at member
    subst member
    exact clear σ ((separates_target' m .absentP σ).mp separated)

theorem absentP_incomplete_refused : ¬ profile .incomplete .absentP := by
  rintro ⟨-, -, -, -, -, -, -, asks⟩
  refine (asks (bind a) (by
    intro e member
    simp [Selection.problem, Selection.equations, probe, Firing.ofBase, equations_nil] at member)
    (by simp [Firing.target, Firing.ofBase, state, plain])).1 _ (List.mem_singleton_self _) 2
    (by simp [state, plain]) ?_
  simp [rows]

/-! ### Reading the opposition -/

theorem readOpp_refuted_admitted : profile .refuted .readOpp := by
  refine ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, ⟨by simp [probe, Firing.ofBase, Selection.commit, state, plain],
      by simp [probe, Firing.ofBase, Selection.commit, state, plain],
      by simp [probe, Firing.ofBase, Selection.commit],
      by simp [probe, Firing.ofBase, Selection.commit],
      by simp [Selection.commit]⟩,
    ⟨A.identity, ?_, by simp [Firing.target, Firing.ofBase, state, plain]⟩,
    fun _ _ _ => ⟨by simp [probe, Firing.ofBase], by simp [probe, Firing.ofBase]⟩⟩
  intro e member
  simp [Selection.problem, Selection.equations, probe, Firing.ofBase, state, plain] at member
  subst member
  exact rfl

theorem readOpp_refused (m : Member) (missing : 1 ∉ (state m).configuration.present) :
    ¬ profile m .readOpp := by
  rintro ⟨-, -, -, -, -, occurrences, -, -⟩
  exact missing (occurrences.kept_subset (by simp [probe, Firing.ofBase, Selection.commit]))

/-! ### Binding `X = a` -/

theorem bindA_admitted (m : Member) (plainState : (state m).disequations.1 = []) :
    profile m .bindA := by
  refine ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, enabled_empty _, ⟨bind a, ?_, ?_⟩,
    fun _ _ _ => ⟨by simp [probe, Firing.ofBase], by simp [probe, Firing.ofBase]⟩⟩
  · intro e member
    simp [Selection.problem, Selection.equations, probe, Firing.ofBase, equations_nil] at member
    subst member
    simp [SubstitutionAction.Solves]
  · rw [separates_target' m .bindA, plainState]
    exact separates_nil _

theorem bindA_disequal_refused : ¬ profile .disequal .bindA := by
  rintro ⟨-, -, -, -, -, -, ⟨σ, solved, separated⟩, -⟩
  have bound : A.E (A.apply σ X) (A.apply σ a) := solved (X, a) (by
    simp [Selection.problem, Selection.equations, probe, Firing.ofBase])
  exact separated (X, a) (List.mem_append_left _ (List.mem_singleton_self _)) bound

/-! ### Reading `p(a)` -/

theorem findP_incomplete_admitted : profile .incomplete .findP := by
  refine ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, ⟨by simp [probe, Firing.ofBase, Selection.commit, state, plain],
      by simp [probe, Firing.ofBase, Selection.commit, state, plain],
      by simp [probe, Firing.ofBase, Selection.commit],
      by simp [probe, Firing.ofBase, Selection.commit],
      by simp [Selection.commit]⟩,
    ⟨bind a, ?_, by simp [Firing.target, Firing.ofBase, state, plain]⟩,
    fun _ _ _ => ⟨by simp [probe, Firing.ofBase], by simp [probe, Firing.ofBase]⟩⟩
  intro e member
  simp [Selection.problem, Selection.equations, probe, Firing.ofBase, state, plain] at member
  subst member
  simp [SubstitutionAction.Solves, rows]

theorem findP_refused (m : Member) (missing : 2 ∉ (state m).configuration.present) :
    ¬ profile m .findP := by
  rintro ⟨-, -, -, -, -, occurrences, -, -⟩
  exact missing (occurrences.kept_subset (by simp [probe, Firing.ofBase, Selection.commit]))

theorem findP_disequal_refused : ¬ profile .disequal .findP := by
  rintro ⟨-, -, -, -, -, -, ⟨σ, solved, separated⟩, -⟩
  have read : A.E (A.apply σ (app 0 a)) (A.apply σ (rows 2)) := solved (app 0 a, rows 2) (by
    simp [Selection.problem, Selection.equations, probe, Firing.ofBase, state])
  have h : a = σ 0 := by simpa [rows] using read
  apply separated (X, a) (List.mem_append_left _ (List.mem_singleton_self _))
  show A.E (A.apply σ X) (A.apply σ a)
  simp only [E_iff, apply_X, apply_a]
  exact h.symm

/-! ### The table -/

/-- **The sixteen verdicts.** -/
theorem table :
    (profile .covered .absentP ∧ ¬ profile .covered .readOpp ∧ profile .covered .bindA ∧
      ¬ profile .covered .findP) ∧
    (profile .refuted .absentP ∧ profile .refuted .readOpp ∧ profile .refuted .bindA ∧
      ¬ profile .refuted .findP) ∧
    (¬ profile .incomplete .absentP ∧ ¬ profile .incomplete .readOpp ∧
      profile .incomplete .bindA ∧ profile .incomplete .findP) ∧
    (profile .disequal .absentP ∧ ¬ profile .disequal .readOpp ∧ ¬ profile .disequal .bindA ∧
      ¬ profile .disequal .findP) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact absentP_admitted .covered (by simp [state, plain]) (by simp [state, plain])
  · exact readOpp_refused .covered (by simp [state, plain])
  · exact bindA_admitted .covered rfl
  · exact findP_refused .covered (by simp [state, plain])
  · refine absentP_admitted .refuted (by simp [state, plain]) ?_
    intro σ _ o present
    simp only [state, plain, Finset.mem_singleton] at present
    subst present
    simp [rows]
  · exact readOpp_refuted_admitted
  · exact bindA_admitted .refuted rfl
  · exact findP_refused .refuted (by simp [state, plain])
  · exact absentP_incomplete_refused
  · exact readOpp_refused .incomplete (by simp [state, plain])
  · exact bindA_admitted .incomplete rfl
  · exact findP_incomplete_admitted
  · refine absentP_admitted .disequal (by simp [state]) ?_
    intro σ separated o present
    simp only [state, Finset.mem_singleton] at present
    subst present
    have apart := separated (X, a) (List.mem_singleton_self _)
    simp only [E_iff, apply_X, apply_a] at apart
    intro same
    apply apart
    have h : a = σ 0 := by simpa [rows] using same
    exact h.symm
  · exact readOpp_refused .disequal (by simp [state])
  · exact bindA_disequal_refused
  · exact findP_disequal_refused

/-- **No two members coincide**: the four ways of not finding `p(a)` have pairwise different
outcomes. -/
theorem profiles_distinct (m₁ m₂ : Member) (different : m₁ ≠ m₂) : profile m₁ ≠ profile m₂ := by
  obtain ⟨⟨c1, c2, c3, c4⟩, ⟨r1, r2, r3, r4⟩, ⟨i1, i2, i3, i4⟩, ⟨d1, d2, d3, d4⟩⟩ := table
  intro same
  have at_ : ∀ π, profile m₁ π ↔ profile m₂ π := fun π => by rw [same]
  cases m₁ <;> cases m₂
  all_goals first
    | exact different rfl
    | exact c2 ((at_ .readOpp).mpr r2)
    | exact i1 ((at_ .absentP).mp c1)
    | exact d3 ((at_ .bindA).mp c3)
    | exact c2 ((at_ .readOpp).mp r2)
    | exact i1 ((at_ .absentP).mp r1)
    | exact d3 ((at_ .bindA).mp r3)
    | exact i1 ((at_ .absentP).mpr c1)
    | exact i1 ((at_ .absentP).mpr r1)
    | exact i1 ((at_ .absentP).mpr d1)
    | exact d3 ((at_ .bindA).mpr c3)
    | exact d3 ((at_ .bindA).mpr r3)
    | exact i1 ((at_ .absentP).mp d1)

/-! ### Incomplete search -/

/-- **A scan that skips the open row would license the absence** that the step refuses at the
incomplete member, while the covering scan does not. -/
theorem incomplete_scan_would_license :
    FirstOrderChecks.acceptsCertainCheck (signature := signature) [] rows ∅ (.absent (app 0 a)) = true ∧
      FirstOrderChecks.acceptsCertainCheck (signature := signature) [] rows {2} (.absent (app 0 a)) = false ∧
      ¬ profile .incomplete .absentP := by
  refine ⟨by cbv, by cbv, absentP_incomplete_refused⟩

/-- The skipping scan lacks coverage. -/
theorem skipping_scan_not_covering :
    ¬ Check.CoversMatches A [] rows ∅ {2} (app 0 a) := by
  intro covered
  have impossible := covered (bind a) (by simp) 2 (by simp) (by simp [rows])
  simp at impossible

#print axioms not_admits_of_not_solvable
#print axioms run_word_of_not_solvable
#print axioms firstOrder_run_consistent
#print axioms Rows.conflict_runs
#print axioms Rows.conflict_consistent
#print axioms Rows.weigh_refused_without_opposition
#print axioms Rows.accept_admitted_with_evidence
#print axioms Rows.accept_refused_with_opposition
#print axioms Rows.tell_false_refused_after_true
#print axioms Rows.both_tells_admit_nothing
#print axioms table
#print axioms profiles_distinct
#print axioms incomplete_scan_would_license
#print axioms skipping_scan_not_covering

end Family

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Evidence
