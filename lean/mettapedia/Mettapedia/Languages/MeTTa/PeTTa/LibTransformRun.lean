import Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep

/-!
# A transform call is a run of occurrence commits

`LibTransformStep.fire_publishes` treats one firing. A `transform` call is more: its
proposals are fixed at the call, and each becomes a branch that fires against the store the
earlier branches left, or fires nothing (`LibTransform.transformWith_drain`). This module
states the whole call on represented stores.

* `Run`: along the list of proposals, each branch either is refused, because no candidate
  of its guided sources has a selection at the rows as they are then, or fires: a candidate
  of that branch has a selection, the selection is an enabled commit, and the rows after
  are a permutation of the ordered publication, representing the model's committed store.
* `transform_is_run`: a `(transform SPACE SOURCES TEMPLATE)` call whose instances go to the
  caller is such a run over its proposals; the store it leaves is the run's last store, and
  its answers are the fired candidates' instances in order.
* `Run.steps_le`: a call fires at most one commit for each proposal.
* `Halted`, `run_nil_iff_halted`, `halted_drain`: a transform is halted when no candidate
  of any of its proposals has a selection; a call's run has no step exactly then, and the
  call leaves the store as it is and answers nothing. `HaltedFamily`,
  `haltedFamily_stable`: for a family of transforms, halted means each of them is, and then
  no sequence of calls changes the store. A driver that stopped is not this evidence; the
  refusal of every candidate is.

The refusal is stated in the step's terms (no selection), not as a failed computation, so
the theorem says both what fires and what cannot.

Scope: the occurrence level, for all sources of the model. Instances routed into the store
itself (`transformInto`) make occurrences and are not covered here.

Examples, computed by the kernel: `Controls.two_takes_two_copies` (two copies, two
proposals, both branches fire), `Controls.one_take_one_copy`, and the refusal
`Controls.take_and_read_refused` (a take and a read of one atom with one copy stored: the
proposal is refused and the store is left as it was).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting (Selection)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.OrderedStore
  (publish)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)
open LibTransform

variable {O : Type} [DecidableEq O]

/-- A run of branches over represented stores. `Run label src rows s guides steps rows' s'`:
from the rows `rows` representing `s`, the branches of `guides`, in order, fire the
candidates and selections `steps` and leave the rows `rows'` representing `s'`. -/
inductive Run (label : O → Atom) (src : Sources) :
    List O → Store → List Footprint → List (Candidate × Selection O) → List O → Store → Prop
  /-- No branch left. -/
  | done (rows : List O) (s : Store) : Run label src rows s [] [] rows s
  /-- The branch is refused: no candidate of its guided sources has a selection. -/
  | refused {rows rows' : List O} {s s' : Store} {g : Footprint} {guides : List Footprint}
      {steps : List (Candidate × Selection O)}
      (none : ∀ c ∈ candidates s g src, ¬ ∃ sel : Selection O, Realizes label rows c.footprint sel)
      (rest : Run label src rows s guides steps rows' s') :
      Run label src rows s (g :: guides) steps rows' s'
  /-- The branch fires a candidate with a selection: an enabled commit, published in order. -/
  | fired {rows mid rows' : List O} {s s' : Store} {g : Footprint} {guides : List Footprint}
      {steps : List (Candidate × Selection O)} {c : Candidate} {sel : Selection O}
      (candidate : c ∈ candidates s g src)
      (real : Realizes label rows c.footprint sel)
      (enabled : Enabled label rows.toFinset (sel.commit (T := Atom)))
      (published : mid.Perm (publish rows sel))
      (represented : Represents label mid (commit c.footprint s))
      (rest : Run label src mid (commit c.footprint s) guides steps rows' s') :
      Run label src rows s (g :: guides) ((c, sel) :: steps) rows' s'

/-- A run fires at most one commit for each branch. -/
theorem Run.steps_le {label : O → Atom} {src : Sources} {rows rows' : List O} {s s' : Store}
    {guides : List Footprint} {steps : List (Candidate × Selection O)}
    (run : Run label src rows s guides steps rows' s') : steps.length ≤ guides.length := by
  induction run with
  | done => exact Nat.le_refl _
  | refused _ _ ih => exact Nat.le_succ_of_le ih
  | fired _ _ _ _ _ _ ih => exact Nat.succ_le_succ ih

/-- A run ends at rows that represent its last store. -/
theorem Run.represents {label : O → Atom} {src : Sources} {rows rows' : List O} {s s' : Store}
    {guides : List Footprint} {steps : List (Candidate × Selection O)}
    (run : Run label src rows s guides steps rows' s') (rep : Represents label rows s) :
    Represents label rows' s' := by
  induction run with
  | done => exact rep
  | refused _ _ ih => exact ih rep
  | fired _ _ _ _ represented _ ih => exact ih represented

/-- The fold of branches over a list of guides, with instances going to the caller, is a
run over those guides. -/
theorem fold_is_run {label : O → Atom} (src : Sources) (emit : Subst → Answers) :
    ∀ (guides : List Footprint) (acc : List Atom × Store) (rows : List O),
      Represents label rows acc.2 →
      ∃ (steps : List (Candidate × Selection O)) (rows' : List O),
        Run label src rows acc.2 guides steps rows'
          (guides.foldl (branchStep toCaller src emit) acc).2 ∧
        (guides.foldl (branchStep toCaller src emit) acc).1 =
          acc.1 ++ steps.flatMap fun step => step.1.instances emit
  | [], acc, rows, _ => ⟨[], rows, Run.done rows acc.2, by simp⟩
  | g :: guides, acc, rows, rep => by
      cases fired : LibTransform.fire acc.2 g src emit with
      | none =>
          have same : branchStep toCaller src emit acc g = acc := by
            simp [branchStep, fired]
          obtain ⟨steps, rows', run, answers⟩ := fold_is_run src emit guides acc rows rep
          refine ⟨steps, rows', ?_, ?_⟩
          · rw [List.foldl_cons, same]
            exact Run.refused ((fire_eq_none_iff_unrealized rep).mp fired) run
          · rw [List.foldl_cons, same]
            exact answers
      | some result =>
          obtain ⟨s', out⟩ := result
          obtain ⟨pre, c, post, split, _, ⟨sel, real⟩, rfl, rfl⟩ :=
            (fire_eq_some_iff_first_realized rep).mp fired
          have next : branchStep toCaller src emit acc g =
              (acc.1 ++ c.instances emit, commit c.footprint acc.2) := by
            simp [branchStep, fired]
          obtain ⟨mid, published, represented⟩ := commit_publishes rep real
          obtain ⟨steps, rows', run, answers⟩ :=
            fold_is_run src emit guides (acc.1 ++ c.instances emit, commit c.footprint acc.2)
              mid represented
          refine ⟨(c, sel) :: steps, rows', ?_, ?_⟩
          · rw [List.foldl_cons, next]
            exact Run.fired (by rw [split]; simp) real real.enabled published represented run
          · rw [List.foldl_cons, next, answers]
            simp [List.append_assoc]

/-- **A transform call is a run of occurrence commits.** On a store represented by `rows`,
the call `(transform SPACE SOURCES TEMPLATE)` is a run over its proposals, taken at the
call: each branch fires an enabled commit of a candidate of its guided sources, or is
refused because none has a selection. The store the call leaves is the run's last store,
represented by its last rows, and the call's answers are the fired candidates' instances
in order. -/
theorem transform_is_run {label : O → Atom} {rows : List O} {s : Store}
    (rep : Represents label rows s) (src : Sources) (template : Atom) :
    ∃ (steps : List (Candidate × Selection O)) (rows' : List O),
      Run label src rows s (proposals s src) steps rows'
        ((transform src template s).drain).2 ∧
      Represents label rows' ((transform src template s).drain).2 ∧
      ((transform src template s).drain).1 =
        steps.flatMap fun step => step.1.instances (instances template) := by
  obtain ⟨steps, rows', run, answers⟩ :=
    fold_is_run (label := label) src (instances template) (proposals s src) ([], s) rows rep
  rw [transform, transformWith_drain]
  exact ⟨steps, rows', run, run.represents rep, by simpa using answers⟩

/-! ## Halting -/

/-- A transform is halted at a represented store when no candidate of any of its proposals
has a selection: every branch would be refused. This is a statement about every candidate,
not about a driver having stopped. -/
def Halted (label : O → Atom) (src : Sources) (rows : List O) (s : Store) : Prop :=
  ∀ g ∈ proposals s src, ∀ c ∈ candidates s g src,
    ¬ ∃ sel : Selection O, Realizes label rows c.footprint sel

/-- A run that fires nothing refused every branch, at rows and a store it never changed. -/
theorem Run.refused_of_nil {label : O → Atom} {src : Sources} {rows rows' : List O}
    {s s' : Store} {guides : List Footprint}
    (run : Run label src rows s guides [] rows' s') :
    (∀ g ∈ guides, ∀ c ∈ candidates s g src,
        ¬ ∃ sel : Selection O, Realizes label rows c.footprint sel) ∧ rows' = rows ∧ s' = s := by
  generalize none : ([] : List (Candidate × Selection O)) = steps at run
  induction run with
  | done => exact ⟨by simp, rfl, rfl⟩
  | refused refusal _ ih =>
      obtain ⟨others, sameRows, sameStore⟩ := ih none
      refine ⟨fun g member => ?_, sameRows, sameStore⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact refusal
      · exact others g member
  | fired => cases none

/-- Where every branch is refused, a run fires nothing. -/
theorem Run.nil_of_refused {label : O → Atom} {src : Sources} {rows rows' : List O}
    {s s' : Store} {guides : List Footprint} {steps : List (Candidate × Selection O)}
    (run : Run label src rows s guides steps rows' s')
    (refused : ∀ g ∈ guides, ∀ c ∈ candidates s g src,
      ¬ ∃ sel : Selection O, Realizes label rows c.footprint sel) : steps = [] := by
  induction run with
  | done => rfl
  | refused _ _ ih => exact ih fun g member => refused g (List.mem_cons_of_mem _ member)
  | fired candidate real =>
      exact absurd ⟨_, real⟩ (refused _ (List.mem_cons_self ..) _ candidate)

/-- **A transform call fires nothing exactly when the transform is halted.** For a run of
the call over its proposals: it has no step if and only if no candidate of any proposal has
a selection; and then the rows and the store are the ones it started from. -/
theorem run_nil_iff_halted {label : O → Atom} {src : Sources} {rows rows' : List O}
    {s s' : Store} {steps : List (Candidate × Selection O)}
    (run : Run label src rows s (proposals s src) steps rows' s') :
    steps = [] ↔ Halted label src rows s := by
  constructor
  · rintro rfl
    exact run.refused_of_nil.1
  · exact run.nil_of_refused

/-- Halting, as the model computes it: every branch fires nothing. -/
theorem halted_iff_fire_none {label : O → Atom} {rows : List O} {s : Store}
    (rep : Represents label rows s) (src : Sources) (emit : Subst → Answers) :
    Halted label src rows s ↔ ∀ g ∈ proposals s src, LibTransform.fire s g src emit = none :=
  forall₂_congr fun _ _ => (fire_eq_none_iff_unrealized rep).symm

/-- A halted transform leaves the store as it is and answers nothing. -/
theorem halted_drain {label : O → Atom} {rows : List O} {s : Store}
    (rep : Represents label rows s) {src : Sources} (template : Atom)
    (halted : Halted label src rows s) :
    (transform src template s).drain = ([], s) := by
  obtain ⟨steps, rows', run, _, answers⟩ := transform_is_run rep src template
  have none : steps = [] := (run_nil_iff_halted run).mpr halted
  subst none
  have same := run.refused_of_nil.2.2
  exact Prod.ext (by simpa using answers) same

/-- A family of transforms is halted when each of them is: the completeness a driver needs
before it may report that nothing can fire. -/
def HaltedFamily (label : O → Atom) (family : List Sources) (rows : List O) (s : Store) :
    Prop :=
  ∀ src ∈ family, Halted label src rows s

/-- At a halted family, calling its transforms in any order, any number of times, leaves
the store as it is. -/
theorem haltedFamily_stable {label : O → Atom} {rows : List O} {s : Store}
    (rep : Represents label rows s) {family : List Sources}
    (halted : HaltedFamily label family rows s) :
    ∀ calls : List (Sources × Atom), (∀ call ∈ calls, call.1 ∈ family) →
      calls.foldl (fun store call => ((transform call.1 call.2 store).drain).2) s = s
  | [], _ => rfl
  | call :: calls, inFamily => by
      have here := halted_drain rep call.2 (halted call.1 (inFamily call (List.mem_cons_self ..)))
      rw [List.foldl_cons, here]
      exact haltedFamily_stable rep halted calls fun c member =>
        inFamily c (List.mem_cons_of_mem _ member)

namespace Controls

/-- The source that takes `a`, with no later conjuncts. -/
def takeA : Sources := ⟨[.pat .take a], [], none⟩

/-- Two stored copies of `a`: both branches fire and the store is left with `b`. -/
theorem two_takes_two_copies :
    (transform takeA (.symbol "took") [a, b, a]).drain =
      ([.symbol "took", .symbol "took"], [b]) := by
  decide

/-- With one copy there is one proposal; it fires, and the store is left with `b`. -/
theorem one_take_one_copy :
    (transform takeA (.symbol "took") [a, b]).drain = ([.symbol "took"], [b]) := by
  decide

/-- The source that takes one `a` and reads another. With one copy the one proposal is
refused, and the store is left as it was. -/
def takeAndReadA : Sources := ⟨[.pat .take a, .pat .read a], [], none⟩

theorem take_and_read_refused :
    (transform takeAndReadA (.symbol "both") [a, b]).drain = ([], [a, b]) := by
  decide

/-- That transform is halted there: its one proposal has no candidate with a selection. -/
theorem take_and_read_halted : Halted label takeAndReadA [0, 1] [a, b] :=
  (halted_iff_fire_none ⟨by decide, by decide⟩ takeAndReadA fun _ => []).mpr (by decide)

/-- The transform that takes `a` is not halted there: its proposal can fire. -/
theorem take_not_halted : ¬ Halted label takeA [0, 1] [a, b] := fun halted =>
  absurd ((halted_iff_fire_none ⟨by decide, by decide⟩ takeA fun _ => []).mp halted) (by decide)

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep
