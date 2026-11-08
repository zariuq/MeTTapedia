import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TransformQualification
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-!
# Minimized examples on the one-frame step: open unification and resources

Each example is a pair of firings of the one-frame instance `AnnotatedRuns.firstOrder` over
first-order terms, with a positive and a separating verdict.

## Open unification

Rows `0 : p(1)` and `1 : p(2)`. The firing `readAs x o` reads row `o` through the pattern `p(x)`.

* **Intentional caller sharing.** After `readAs 0 0` binds `X₀ = 1`, the second read through the same
  caller variable is refused (`shared_second_read_refused`): the two reads are correlated.
* **Fresh local variables.** Through a fresh variable the second read is admitted
  (`fresh_second_read_admitted`).
* **Compatible and incompatible shared constraints.** `tell v` tells `X₀ = v`. Each tell is
  admitted alone (`tell_admitted`); after `tell 1`, `tell 2` is refused and conversely
  (`tells_conflict`). The two failed compositions leave **observably different prefixes**: after
  `tell 1` every solution has `X₀ = 1`, after `tell 2` every solution has `X₀ = 2`
  (`prefixes_differ`). A compatible pair, `tell 1` with the fresh read, runs
  (`compatible_run`).

## Resources

Rows `0 : c` and `1 : c` carry the same value.

* **Occurrence multiplicity.** Taking `c` twice takes the two occurrences (`take_two_admitted`).
* **Distinct takes.** Taking occurrence `0` twice is refused (`take_same_twice_refused`).
* **Aliased reads.** Reading occurrence `0` through two read positions is admitted
  (`aliased_read_admitted`).
* **Read before consume.** Reading `0` and then taking it is a run (`read_then_take`); after the take,
  the read is refused (`read_after_take_refused`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TransformQualification.Examples

open Mettapedia.Logic.LP
open AnnotatedRuns (Firing firstOrder)
open ConstraintMultisetRewriting.Controls (signature f)

abbrev Fir := Firing (Term signature) (Subst signature) Nat

/-! ## Open unification -/

namespace OpenUnification

/-- Rows `0 : p(1)` and `1 : p(2)`. -/
def rows : Nat → Term signature
  | 0 => f (.const 1)
  | 1 => f (.const 2)
  | _ => .const 0

abbrev P := firstOrder (S := Subst signature) (FirstOrder.action signature) rows

def start : Configuration (Term signature) Nat := ⟨[], {0, 1}⟩

/-- Read row `o` through the pattern `p(X_x)`. -/
def readAs (x o : Nat) : Fir := ⟨⟨[], [f (.var x)], [], [], []⟩, [], ⟨[], [o], []⟩⟩

/-- Tell `X₀ = v`. -/
def tell (v : Nat) : Fir := ⟨⟨[], [], [(.var 0, .const v)], [], []⟩, [], ⟨[], [], []⟩⟩

/-- Every variable to `v`. -/
def all (v : Nat) : Subst signature := fun _ => .const v

/-- The variable `X₀` to `1`, every other variable to `2`. -/
def split : Subst signature := fun x => if x = 0 then .const 1 else .const 2

theorem read_first_admitted : P.Admits (s := start) (readAs 0 0) := by
  refine (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨all 1, ?_⟩, by simp [readAs]⟩
  intro equation member
  simp [readAs, Selection.problem, Selection.equations, start, rows] at member
  subst member
  rfl

/-- The configuration after the first read. -/
def afterRead : Configuration (Term signature) Nat := (readAs 0 0).result rows start

theorem shared_second_read_refused : ¬ P.Admits (s := afterRead) (readAs 0 1) := by
  intro admitted
  obtain ⟨σ, model⟩ := admitted.firing.consistent
  have first : f (σ 0) = f (.const 1) := model (f (.var 0), f (.const 1)) (by
    simp [readAs, afterRead, Firing.result, Selection.result, Selection.problem, Selection.equations,
      start, rows])
  have second : f (σ 0) = f (.const 2) := model (f (.var 0), f (.const 2)) (by
    simp [readAs, afterRead, Firing.result, Selection.result, Selection.problem, Selection.equations,
      start, rows])
  rw [first] at second
  have children := eq_of_heq (Term.app.inj second).2
  have impossible := congrFun children 0
  cases impossible

theorem fresh_second_read_admitted : P.Admits (s := afterRead) (readAs 1 1) := by
  refine (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨split, ?_⟩, by simp [readAs]⟩
  intro equation member
  simp [readAs, afterRead, Firing.result, Selection.result, Selection.problem, Selection.equations,
    start, rows] at member
  rcases member with rfl | rfl <;> rfl

theorem tell_admitted (v : Nat) : P.Admits (s := start) (tell v) := by
  have enabled : MeTTaCalculus.OccurrenceCommits.Enabled rows start.present
      ((⟨[], [], []⟩ : Selection Nat).commit (T := Term signature)) := by decide
  refine (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, enabled, ⟨all v, ?_⟩, by simp [tell]⟩
  intro equation member
  simp [tell, Selection.problem, Selection.equations, start] at member
  subst member
  rfl

/-- The configuration after `tell v`. -/
def told (v : Nat) : Configuration (Term signature) Nat := (tell v).result rows start

theorem tell_refused_after {v w : Nat} (different : v ≠ w) : ¬ P.Admits (s := told v) (tell w) := by
  intro admitted
  obtain ⟨σ, model⟩ := admitted.firing.consistent
  have first : σ 0 = .const v := model (.var 0, .const v) (by
    simp [tell, told, Firing.result, Selection.result, Selection.problem, Selection.equations, start])
  have second : σ 0 = .const w := model (.var 0, .const w) (by
    simp [tell, told, Firing.result, Selection.result, Selection.problem, Selection.equations, start])
  rw [first] at second
  exact different (Term.const.inj second)

/-- **Incompatible shared constraints**: each tell alone, never both, in either order. -/
theorem tells_conflict :
    P.Admits (s := start) (tell 1) ∧ P.Admits (s := start) (tell 2) ∧
      ¬ P.Admits (s := told 1) (tell 2) ∧ ¬ P.Admits (s := told 2) (tell 1) :=
  ⟨tell_admitted 1, tell_admitted 2, tell_refused_after (by decide), tell_refused_after (by decide)⟩

/-- **The failure prefixes differ observably**: after `tell 1` every solution sends `X₀` to `1`,
after `tell 2` to `2`. -/
theorem prefixes_differ :
    (FirstOrder.action signature).Entails (told 1).equations
        (fun σ => Subst.applyTerm σ (.var 0) = .const 1) ∧
      (FirstOrder.action signature).Entails (told 2).equations
        (fun σ => Subst.applyTerm σ (.var 0) = .const 2) ∧
      ¬ (FirstOrder.action signature).Entails (told 2).equations
        (fun σ => Subst.applyTerm σ (.var 0) = .const 1) := by
  refine ⟨fun σ model => model (.var 0, .const 1) (by
      simp [tell, told, Firing.result, Selection.result, Selection.problem, Selection.equations, start]),
    fun σ model => model (.var 0, .const 2) (by
      simp [tell, told, Firing.result, Selection.result, Selection.problem, Selection.equations, start]),
    fun entails => ?_⟩
  have wrong := entails (all 2) (by
    intro equation member
    simp [tell, told, Firing.result, Selection.result, Selection.problem, Selection.equations,
      start] at member
    subst member
    rfl)
  change Term.const (σ := signature) 2 = .const 1 at wrong
  cases wrong

/-- **A compatible pair runs**: `tell 1`, then the fresh read of `p(2)`. -/
theorem compatible_run :
    ∃ r : P.Run start, r.word.map Sigma.snd = [tell 1, readAs 1 1] := by
  have second : P.Admits (s := told 1) (readAs 1 1) := by
    refine (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
      ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨split, ?_⟩, by simp [readAs]⟩
    intro equation member
    simp [readAs, tell, told, Firing.result, Selection.result, Selection.problem, Selection.equations,
      start, rows] at member
    rcases member with rfl | rfl <;> rfl
  exact ⟨.cons (tell 1) (tell_admitted 1) (.cons (readAs 1 1) second (.nil _)), rfl⟩

end OpenUnification

/-! ## Resources -/

namespace Resources

/-- Rows `0 : c` and `1 : c` carry the same value `c`. -/
def rows : Nat → Term signature
  | 0 => .const 5
  | 1 => .const 5
  | _ => .const 6

abbrev P := firstOrder (S := Subst signature) (FirstOrder.action signature) rows

def start : Configuration (Term signature) Nat := ⟨[], {0, 1}⟩

def c : Term signature := .const 5

def takeTwo : Fir := ⟨⟨[c, c], [], [], [], []⟩, [], ⟨[0, 1], [], []⟩⟩
def takeSameTwice : Fir := ⟨⟨[c, c], [], [], [], []⟩, [], ⟨[0, 0], [], []⟩⟩
def readTwice : Fir := ⟨⟨[], [c, c], [], [], []⟩, [], ⟨[], [0, 0], []⟩⟩
def readZero : Fir := ⟨⟨[], [c], [], [], []⟩, [], ⟨[], [0], []⟩⟩
def takeZero : Fir := ⟨⟨[c], [], [], [], []⟩, [], ⟨[0], [], []⟩⟩

/-- Every store of this example is ground, so the identity solves it. -/
theorem ground_models (store : EquationStore (Term signature))
    (ground : ∀ e ∈ store, e = (c, c)) :
    (FirstOrder.action signature).Models (Subst.id signature) store := by
  intro equation member
  rw [ground equation member]
  rfl

theorem take_two_admitted : P.Admits (s := start) takeTwo :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨_, ground_models _ (by
      intro e member
      simp [takeTwo, Selection.problem, Selection.equations, start, rows, c] at member
      exact member)⟩, by simp [takeTwo]⟩

theorem take_same_twice_refused : ¬ P.Admits (s := start) takeSameTwice :=
  fun admitted => absurd admitted.firing.take_distinct (by decide)

theorem aliased_read_admitted : P.Admits (s := start) readTwice :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨_, ground_models _ (by
      intro e member
      simp [readTwice, Selection.problem, Selection.equations, start, rows, c] at member
      exact member)⟩, by simp [readTwice]⟩

theorem read_zero_admitted : P.Admits (s := start) readZero :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨_, ground_models _ (by
      intro e member
      simp [readZero, Selection.problem, Selection.equations, start, rows, c] at member
      exact member)⟩, by simp [readZero]⟩

theorem take_zero_admitted_after_read :
    P.Admits (s := readZero.result rows start) takeZero :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨_, ground_models _ (by
      intro e member
      simp [readZero, takeZero, Firing.result, Selection.result, Selection.problem, Selection.equations,
        start, rows, c] at member
      exact member)⟩, by simp [takeZero]⟩

/-- **Read before consume**: reading `0` and then taking it is a run of the step. -/
theorem read_then_take : ∃ r : P.Run start, r.word.map Sigma.snd = [readZero, takeZero] :=
  ⟨.cons readZero read_zero_admitted (.cons takeZero take_zero_admitted_after_read (.nil _)), rfl⟩

theorem take_zero_admitted : P.Admits (s := start) takeZero :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨_, ground_models _ (by
      intro e member
      simp [takeZero, Selection.problem, Selection.equations, start, rows, c] at member
      exact member)⟩, by simp [takeZero]⟩

/-- **Consume before read fails**: after the take, the read of `0` is refused. -/
theorem read_after_take_refused : ¬ P.Admits (s := takeZero.result rows start) readZero :=
  fun admitted => absurd admitted.firing.occurrences.kept_subset (by decide)

end Resources

#print axioms OpenUnification.read_first_admitted
#print axioms OpenUnification.shared_second_read_refused
#print axioms OpenUnification.fresh_second_read_admitted
#print axioms OpenUnification.tell_admitted
#print axioms OpenUnification.tell_refused_after
#print axioms OpenUnification.tells_conflict
#print axioms OpenUnification.prefixes_differ
#print axioms OpenUnification.compatible_run
#print axioms Resources.take_two_admitted
#print axioms Resources.take_same_twice_refused
#print axioms Resources.aliased_read_admitted
#print axioms Resources.read_then_take
#print axioms Resources.take_zero_admitted
#print axioms Resources.read_after_take_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TransformQualification.Examples
