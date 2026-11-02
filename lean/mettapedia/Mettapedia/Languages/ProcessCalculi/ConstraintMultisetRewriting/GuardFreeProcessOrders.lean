import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ConditionalSchedule
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SubstitutionStability

/-!
# Independent check-free firings commute (the swap lemma behind the process reading)

Uses `Selection.Valid`, `Selection.result`, `ConditionalSchedule.Executable`
and `ConditionalSchedule.follow`. Two adjacent firings `f; g` may be exchanged when

* both have no checks (the positive fragment);
* `f` makes nothing that `g` takes or reads (no causality `f ≺ g`);
* `f` reads nothing that `g` takes (no asymmetric conflict `f ↗ g`);
* `g` makes no identity that `f` took (no identity reuse).

The exchanged schedule is executable, and both schedules end in the same present
occurrences with equivalent equation stores. Executability depends on a configuration only
through the models of its equations and its present occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardFreeProcessOrders

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

/-- What a firing adds to the equation store; it does not depend on the configuration. -/
def added (rule : RuleInstance T) (selection : Selection O) : EquationStore T :=
  Selection.equations label rule.take selection.taken ++
    Selection.equations label rule.read selection.read ++ rule.tell

omit [DecidableEq O] in
theorem problem_eq (rule : RuleInstance T) (selection : Selection O) (before : Configuration T O) :
    selection.problem label rule before = before.equations ++ added label rule selection := by
  simp [Selection.problem, added, List.append_assoc]

theorem result_equations (rule : RuleInstance T) (selection : Selection O) (before : Configuration T O) :
    (selection.result label rule before).equations = before.equations ++ added label rule selection :=
  problem_eq label rule selection before

/-- Two configurations with the same occurrences and equivalent equations. -/
def SameUpTo (C D : Configuration T O) : Prop :=
  A.Equivalent C.equations D.equations ∧ C.present = D.present

omit [DecidableEq O] in
theorem SameUpTo.refl (C : Configuration T O) : SameUpTo A C C := ⟨fun _ => Iff.rfl, rfl⟩

theorem equivalent_append {one two : EquationStore T} (same : A.Equivalent one two)
    (extra : EquationStore T) : A.Equivalent (one ++ extra) (two ++ extra) := by
  intro σ
  rw [A.models_append, A.models_append, same σ]

theorem valid_congr {rule : RuleInstance T} {selection : Selection O} {C D : Configuration T O}
    (same : SameUpTo A C D) :
    selection.Valid A label rule C ↔ selection.Valid A label rule D := by
  have problems : A.Equivalent (selection.problem label rule C) (selection.problem label rule D) := by
    rw [problem_eq, problem_eq]
    exact equivalent_append A same.1 _
  constructor
  · intro valid
    refine ⟨valid.take_distinct, valid.output_distinct, valid.take_length, valid.read_length,
      valid.outputs, same.2 ▸ valid.occurrences, ?_, ?_⟩
    · exact (SubstitutionAction.equivalent_consistent A problems).mp valid.consistent
    · intro check member σ solved
      rw [← same.2]
      exact valid.checks check member σ ((problems σ).mpr solved)
  · intro valid
    refine ⟨valid.take_distinct, valid.output_distinct, valid.take_length, valid.read_length,
      valid.outputs, same.2 ▸ valid.occurrences, ?_, ?_⟩
    · exact (SubstitutionAction.equivalent_consistent A problems).mpr valid.consistent
    · intro check member σ solved
      rw [same.2]
      exact valid.checks check member σ ((problems σ).mp solved)

theorem result_congr (rule : RuleInstance T) (selection : Selection O) {C D : Configuration T O}
    (same : SameUpTo A C D) :
    SameUpTo A (selection.result label rule C) (selection.result label rule D) := by
  refine ⟨?_, ?_⟩
  · change A.Equivalent (selection.problem label rule C) (selection.problem label rule D)
    rw [problem_eq, problem_eq]
    exact equivalent_append A same.1 _
  · change fire C.present _ = fire D.present _
    rw [same.2]

theorem executable_congr :
    ∀ (schedule : List (ConditionalSchedule.Firing T O)) {C D : Configuration T O},
      SameUpTo A C D →
        (ConditionalSchedule.Executable A label C schedule ↔
          ConditionalSchedule.Executable A label D schedule)
  | [], _, _, same => SubstitutionAction.equivalent_consistent A same.1
  | firing :: rest, _, _, same => by
      change (_ ∧ _) ↔ (_ ∧ _)
      rw [valid_congr A label same, executable_congr rest (result_congr A label firing.1 firing.2 same)]

theorem follow_congr :
    ∀ (schedule : List (ConditionalSchedule.Firing T O)) {C D : Configuration T O},
      SameUpTo A C D →
        SameUpTo A (ConditionalSchedule.follow label C schedule) (ConditionalSchedule.follow label D schedule)
  | [], _, _, same => same
  | firing :: rest, _, _, same => follow_congr rest (result_congr A label firing.1 firing.2 same)

/-- No causality from `f` to `g`: `f` makes nothing that `g` takes or reads. -/
def NoCause (f g : ConditionalSchedule.Firing T O) : Prop :=
  ∀ o ∈ f.2.made, o ∉ g.2.taken ∧ o ∉ g.2.read

/-- No asymmetric conflict from `f` to `g`: `f` reads nothing that `g` takes. -/
def NoAsym (f g : ConditionalSchedule.Firing T O) : Prop :=
  ∀ o ∈ f.2.read, o ∉ g.2.taken

/-- `g` makes no identity that `f` took. -/
def NoReuse (f g : ConditionalSchedule.Firing T O) : Prop :=
  ∀ o ∈ g.2.made, o ∉ f.2.taken

/-- **Swap lemma.** -/
theorem swap_valid {f g : ConditionalSchedule.Firing T O} {C : Configuration T O}
    (fFree : f.1.checks = []) (gFree : g.1.checks = [])
    (noCause : NoCause f g) (noAsym : NoAsym f g) (noReuse : NoReuse f g)
    (first : f.2.Valid A label f.1 C)
    (second : g.2.Valid A label g.1 (f.2.result label f.1 C)) :
    g.2.Valid A label g.1 C ∧ f.2.Valid A label f.1 (g.2.result label g.1 C) ∧
      SameUpTo A (g.2.result label g.1 (f.2.result label f.1 C))
        (f.2.result label f.1 (g.2.result label g.1 C)) := by
  obtain ⟨σ, solved⟩ := second.consistent
  rw [problem_eq, result_equations, A.models_append, A.models_append] at solved
  obtain ⟨⟨oldSolved, fSolved⟩, gSolved⟩ := solved
  have fT := first.occurrences
  have gT := second.occurrences
  -- g at C
  have gValid : g.2.Valid A label g.1 C := by
    refine ⟨second.take_distinct, second.output_distinct, second.take_length, second.read_length,
      second.outputs, ⟨?_, ?_, gT.apart, ?_, ?_⟩, ⟨σ, ?_⟩, ?_⟩
    · intro o taken
      have inFire := gT.taken_subset taken
      rcases mem_fire.mp inFire with ⟨present, _⟩ | made
      · exact present
      · have made' : o ∈ f.2.made := by simpa [Selection.commit] using made
        have taken' : o ∈ g.2.taken := by simpa [Selection.commit] using taken
        exact absurd taken' (noCause o made').1
    · intro o read
      have inFire := gT.kept_subset read
      rcases mem_fire.mp inFire with ⟨present, _⟩ | made
      · exact present
      · have made' : o ∈ f.2.made := by simpa [Selection.commit] using made
        have read' : o ∈ g.2.read := by simpa [Selection.commit] using read
        exact absurd read' (noCause o made').2
    · refine Finset.disjoint_left.mpr fun o made present => ?_
      have notAfter : o ∉ fire C.present (f.2.commit (T := T)) :=
        Finset.disjoint_left.mp gT.fresh made
      have made' : o ∈ g.2.made := by simpa [Selection.commit] using made
      apply notAfter
      refine mem_fire.mpr (Or.inl ⟨present, ?_⟩)
      have notTaken := noReuse o made'
      simpa [Selection.commit] using notTaken
    · intro query member
      cases member
    · rw [problem_eq, A.models_append]
      exact ⟨oldSolved, gSolved⟩
    · intro check member
      rw [gFree] at member
      cases member
  -- f after g
  have fValid : f.2.Valid A label f.1 (g.2.result label g.1 C) := by
    refine ⟨first.take_distinct, first.output_distinct, first.take_length, first.read_length,
      first.outputs, ⟨?_, ?_, fT.apart, ?_, ?_⟩, ⟨σ, ?_⟩, ?_⟩
    · intro o taken
      refine mem_fire.mpr (Or.inl ⟨fT.taken_subset taken, fun gTaken => ?_⟩)
      have inAfter := gT.taken_subset gTaken
      exact Finset.disjoint_left.mp (disjoint_taken_fire fT) taken inAfter
    · intro o read
      refine mem_fire.mpr (Or.inl ⟨fT.kept_subset read, fun gTaken => ?_⟩)
      have read' : o ∈ f.2.read := by simpa [Selection.commit] using read
      have gTaken' : o ∈ g.2.taken := by simpa [Selection.commit] using gTaken
      exact noAsym o read' gTaken'
    · refine Finset.disjoint_left.mpr fun o made inAfter => ?_
      rcases mem_fire.mp inAfter with ⟨present, _⟩ | gMade
      · exact Finset.disjoint_left.mp fT.fresh made present
      · exact Finset.disjoint_left.mp gT.fresh gMade (made_subset_fire made)
    · intro query member
      cases member
    · rw [problem_eq, result_equations, A.models_append, A.models_append]
      exact ⟨⟨oldSolved, gSolved⟩, fSolved⟩
    · intro check member
      rw [fFree] at member
      cases member
  refine ⟨gValid, fValid, ?_, ?_⟩
  · intro τ
    rw [result_equations, result_equations, result_equations, result_equations]
    simp only [A.models_append]
    tauto
  · change fire (fire C.present (f.2.commit (T := T))) (g.2.commit (T := T)) =
      fire (fire C.present (g.2.commit (T := T))) (f.2.commit (T := T))
    ext o
    have cause := fun made => noCause o made
    have reuse := fun made => noReuse o made
    simp only [mem_fire, Selection.commit, List.mem_toFinset] at cause reuse ⊢
    constructor
    · rintro (⟨(⟨present, notF⟩ | fMade), notG⟩ | gMade)
      · exact Or.inl ⟨Or.inl ⟨present, notG⟩, notF⟩
      · exact Or.inr fMade
      · exact Or.inl ⟨Or.inr gMade, reuse gMade⟩
    · rintro (⟨(⟨present, notG⟩ | gMade), notF⟩ | fMade)
      · exact Or.inl ⟨Or.inl ⟨present, notF⟩, notG⟩
      · exact Or.inr gMade
      · exact Or.inl ⟨Or.inr fMade, (cause fMade).1⟩

/-- **Adjacent independent check-free firings commute in every executable schedule**, with
the same final occurrences and an equivalent final equation store. -/
theorem executable_swap {f g : ConditionalSchedule.Firing T O}
    {rest : List (ConditionalSchedule.Firing T O)} {C : Configuration T O}
    (fFree : f.1.checks = []) (gFree : g.1.checks = [])
    (noCause : NoCause f g) (noAsym : NoAsym f g) (noReuse : NoReuse f g)
    (executable : ConditionalSchedule.Executable A label C (f :: g :: rest)) :
    ConditionalSchedule.Executable A label C (g :: f :: rest) ∧
      SameUpTo A (ConditionalSchedule.follow label C (f :: g :: rest))
        (ConditionalSchedule.follow label C (g :: f :: rest)) := by
  obtain ⟨first, second, later⟩ := executable
  obtain ⟨gValid, fValid, same⟩ := swap_valid A label fFree gFree noCause noAsym noReuse first second
  exact ⟨⟨gValid, fValid, (executable_congr A label rest same).mp later⟩,
    follow_congr A label rest same⟩

omit [DecidableEq O] in
theorem SameUpTo.trans {C D E : Configuration T O} (first : SameUpTo A C D) (second : SameUpTo A D E) :
    SameUpTo A C E :=
  ⟨fun σ => (first.1 σ).trans (second.1 σ), first.2.trans second.2⟩

/-- **Bubbling one firing to the front** past firings it is independent of. -/
theorem bubble {h : ConditionalSchedule.Firing T O} (hFree : h.1.checks = []) :
    ∀ (before : List (ConditionalSchedule.Firing T O)) (after : List (ConditionalSchedule.Firing T O))
      (C : Configuration T O),
      (∀ y ∈ before, y.1.checks = [] ∧ NoCause y h ∧ NoAsym y h ∧ NoReuse y h) →
      ConditionalSchedule.Executable A label C (before ++ h :: after) →
      ConditionalSchedule.Executable A label C (h :: (before ++ after)) ∧
        SameUpTo A (ConditionalSchedule.follow label C (before ++ h :: after))
          (ConditionalSchedule.follow label C (h :: (before ++ after)))
  | [], _, C, _, executable => ⟨executable, SameUpTo.refl A _⟩
  | y :: rest, after, C, independent, executable => by
      obtain ⟨yValid, later⟩ := executable
      obtain ⟨yFree, cause, asym, reuse⟩ := independent y List.mem_cons_self
      obtain ⟨moved, sameLater⟩ := bubble hFree rest after (y.2.result label y.1 C)
        (fun z member => independent z (List.mem_cons_of_mem _ member)) later
      obtain ⟨swapped, sameSwap⟩ := executable_swap A label yFree hFree cause asym reuse
        (C := C) (rest := rest ++ after) ⟨yValid, moved⟩
      exact ⟨swapped, sameLater.trans A sameSwap⟩

/-- The later firing `y` has no causal or asymmetric-conflict edge to the earlier `x`. -/
def LaterIndependent (x y : ConditionalSchedule.Firing T O) : Prop := NoCause y x ∧ NoAsym y x

/-- **Every linearization of the process order replays.** Let `schedule` be executable, with
check-free firings and no identity reuse (a later firing never makes what an earlier one took).
Any permutation in which no later firing has a causal or asymmetric-conflict edge to an earlier
one is executable too, and ends in the same occurrences with an equivalent equation store. -/
theorem linearization_executes :
    ∀ (order schedule : List (ConditionalSchedule.Firing T O)) (C : Configuration T O),
      schedule.Perm order →
      (∀ x ∈ schedule, x.1.checks = []) →
      schedule.Pairwise NoReuse →
      order.Pairwise LaterIndependent →
      ConditionalSchedule.Executable A label C schedule →
      ConditionalSchedule.Executable A label C order ∧
        SameUpTo A (ConditionalSchedule.follow label C schedule) (ConditionalSchedule.follow label C order)
  | [], schedule, C, perm, _, _, _, executable => by
      have empty : schedule = [] := List.Perm.eq_nil perm
      subst empty
      exact ⟨executable, SameUpTo.refl A _⟩
  | h :: order, schedule, C, perm, free, noReuse, respects, executable => by
      have member : h ∈ schedule := perm.symm.subset List.mem_cons_self
      obtain ⟨before, after, rfl⟩ := List.append_of_mem member
      have restPerm : (before ++ after).Perm order :=
        (List.perm_middle.symm.trans perm).cons_inv
      have hFree : h.1.checks = [] := free h (by simp)
      obtain ⟨headIndependent, restRespects⟩ := List.pairwise_cons.mp respects
      obtain ⟨reuseBefore, reuseRest, reuseCross⟩ := List.pairwise_append.mp noReuse
      obtain ⟨reuseHead, reuseAfter⟩ := List.pairwise_cons.mp reuseRest
      have independent : ∀ y ∈ before, y.1.checks = [] ∧ NoCause y h ∧ NoAsym y h ∧ NoReuse y h := by
        intro y inBefore
        have inOrder : y ∈ order := restPerm.subset (List.mem_append_left _ inBefore)
        obtain ⟨cause, asym⟩ := headIndependent y inOrder
        exact ⟨free y (List.mem_append_left _ inBefore), cause, asym,
          reuseCross y inBefore h List.mem_cons_self⟩
      obtain ⟨front, sameFront⟩ := bubble A label hFree before after C independent executable
      obtain ⟨hValid, restExecutable⟩ := front
      have restFree : ∀ x ∈ before ++ after, x.1.checks = [] := by
        intro x inRest
        rcases List.mem_append.mp inRest with inBefore | inAfter
        · exact free x (List.mem_append_left _ inBefore)
        · exact free x (List.mem_append_right _ (List.mem_cons_of_mem _ inAfter))
      have restNoReuse : (before ++ after).Pairwise NoReuse :=
        List.pairwise_append.mpr ⟨reuseBefore, reuseAfter,
          fun x inBefore y inAfter => reuseCross x inBefore y (List.mem_cons_of_mem _ inAfter)⟩
      obtain ⟨orderExecutable, sameRest⟩ := linearization_executes order (before ++ after)
        (h.2.result label h.1 C) restPerm restFree restNoReuse restRespects restExecutable
      exact ⟨⟨hValid, orderExecutable⟩, sameFront.trans A sameRest⟩

/-! ## The converse: every run respects the process order

An occurrence net makes each identity at most once and never makes an identity that was
initially present. Under these two conditions a run never lets a later firing make or read
what an earlier one took or read. -/

/-- No firing makes an identity that is present at the start. -/
def FreshFrom (C : Configuration T O) (schedule : List (ConditionalSchedule.Firing T O)) : Prop :=
  ∀ x ∈ schedule, ∀ o ∈ x.2.made, o ∉ C.present

/-- Distinct firings make disjoint identities. -/
def UniqueMakers (schedule : List (ConditionalSchedule.Firing T O)) : Prop :=
  schedule.Pairwise fun x y => ∀ o ∈ x.2.made, o ∉ y.2.made

/-- An absent identity that nothing makes is never read or taken. -/
theorem absent_stays :
    ∀ (schedule : List (ConditionalSchedule.Firing T O)) (D : Configuration T O) (o : O),
      ConditionalSchedule.Executable A label D schedule → o ∉ D.present →
      (∀ z ∈ schedule, o ∉ z.2.made) → ∀ y ∈ schedule, o ∉ y.2.read ∧ o ∉ y.2.taken
  | [], _, _, _, _, _, _, member => absurd member List.not_mem_nil
  | z :: rest, D, o, executable, absent, unmade, y, member => by
      obtain ⟨valid, later⟩ := executable
      rcases List.mem_cons.mp member with same | inRest
      · subst same
        constructor
        · intro read
          exact absent (valid.occurrences.kept_subset (by simpa [Selection.commit] using read))
        · intro taken
          exact absent (valid.occurrences.taken_subset (by simpa [Selection.commit] using taken))
      · refine absent_stays rest _ o later ?_ (fun w hw => unmade w (List.mem_cons_of_mem _ hw)) y inRest
        intro inAfter
        rcases mem_fire.mp inAfter with ⟨present, _⟩ | made
        · exact absent present
        · exact unmade z List.mem_cons_self (by simpa [Selection.commit] using made)

theorem fresh_after {x : ConditionalSchedule.Firing T O} {rest : List (ConditionalSchedule.Firing T O)}
    {C : Configuration T O} (fresh : FreshFrom C (x :: rest))
    (xUnique : ∀ y ∈ rest, ∀ o ∈ x.2.made, o ∉ y.2.made) :
    FreshFrom (x.2.result label x.1 C) rest := by
  intro y member o made inAfter
  rcases mem_fire.mp inAfter with ⟨present, _⟩ | xMade
  · exact fresh y (List.mem_cons_of_mem _ member) o made present
  · exact xUnique y member o (by simpa [Selection.commit] using xMade) made

/-- **Every run respects causality and asymmetric conflict.** -/
theorem runs_respect_order :
    ∀ (order : List (ConditionalSchedule.Firing T O)) (C : Configuration T O),
      ConditionalSchedule.Executable A label C order → FreshFrom C order → UniqueMakers order →
      order.Pairwise LaterIndependent
  | [], _, _, _, _ => List.Pairwise.nil
  | x :: rest, C, executable, fresh, unique => by
      obtain ⟨valid, later⟩ := executable
      obtain ⟨xUnique, restUnique⟩ := List.pairwise_cons.mp unique
      refine List.pairwise_cons.mpr ⟨?_, runs_respect_order rest _ later
        (fresh_after label fresh xUnique) restUnique⟩
      intro y member
      constructor
      · intro o made
        have notInitial := fresh y (List.mem_cons_of_mem _ member) o made
        constructor
        · intro taken
          exact notInitial (valid.occurrences.taken_subset (by simpa [Selection.commit] using taken))
        · intro read
          exact notInitial (valid.occurrences.kept_subset (by simpa [Selection.commit] using read))
      · intro o read taken
        have initial : o ∈ C.present :=
          valid.occurrences.taken_subset (by simpa [Selection.commit] using taken)
        have gone : o ∉ (x.2.result label x.1 C).present := by
          intro inAfter
          rcases mem_fire.mp inAfter with ⟨_, notTaken⟩ | made
          · exact notTaken (by simpa [Selection.commit] using taken)
          · exact Finset.disjoint_left.mp valid.occurrences.fresh made initial
        have unmade : ∀ z ∈ rest, o ∉ z.2.made := fun z hz made =>
          fresh z (List.mem_cons_of_mem _ hz) o made initial
        exact (absent_stays A label rest _ o later gone unmade y member).1 read

/-- Under the occurrence-net conditions a later firing never makes what an earlier one took. -/
theorem no_reuse_of_fresh :
    ∀ (schedule : List (ConditionalSchedule.Firing T O)) (C : Configuration T O),
      ConditionalSchedule.Executable A label C schedule → FreshFrom C schedule →
      UniqueMakers schedule → schedule.Pairwise NoReuse
  | [], _, _, _, _ => List.Pairwise.nil
  | x :: rest, C, executable, fresh, unique => by
      obtain ⟨valid, later⟩ := executable
      obtain ⟨xUnique, restUnique⟩ := List.pairwise_cons.mp unique
      refine List.pairwise_cons.mpr ⟨?_, no_reuse_of_fresh rest _ later
        (fresh_after label fresh xUnique) restUnique⟩
      intro y member o made taken
      exact fresh y (List.mem_cons_of_mem _ member) o made
        (valid.occurrences.taken_subset (by simpa [Selection.commit] using taken))

/-- **The runs of a check-free occurrence-net schedule are exactly the linearizations of its
causality and asymmetric conflict**, and every run ends in the same occurrences with an
equivalent equation store. -/
theorem runs_are_exactly_linearizations
    (schedule order : List (ConditionalSchedule.Firing T O)) (C : Configuration T O)
    (perm : schedule.Perm order) (free : ∀ x ∈ schedule, x.1.checks = [])
    (fresh : FreshFrom C schedule) (unique : UniqueMakers schedule)
    (executable : ConditionalSchedule.Executable A label C schedule) :
    (ConditionalSchedule.Executable A label C order ↔ order.Pairwise LaterIndependent) ∧
      (ConditionalSchedule.Executable A label C order →
        SameUpTo A (ConditionalSchedule.follow label C schedule) (ConditionalSchedule.follow label C order)) := by
  have freshOrder : FreshFrom C order := fun x member => fresh x (perm.symm.subset member)
  have symmetric : ∀ x y : ConditionalSchedule.Firing T O,
      (∀ o ∈ x.2.made, o ∉ y.2.made) → ∀ o ∈ y.2.made, o ∉ x.2.made :=
    fun x y apart o inY inX => apart o inX inY
  have uniqueOrder : UniqueMakers order := (List.Perm.pairwise_iff (fun {x} {y} => symmetric x y) perm).mp unique
  have reuse := no_reuse_of_fresh A label schedule C executable fresh unique
  have forward : ConditionalSchedule.Executable A label C order → order.Pairwise LaterIndependent :=
    fun run => runs_respect_order A label order C run freshOrder uniqueOrder
  refine ⟨⟨forward, fun respects =>
    (linearization_executes A label order schedule C perm free reuse respects executable).1⟩, ?_⟩
  intro run
  exact (linearization_executes A label order schedule C perm free reuse (forward run) executable).2

/-! ## Guard-free transport: admitted instances by substitution and frame

A check-free schedule stays executable after substituting every term by a substitution
compatible with its final equation store (the instance law) and after adding occurrences it
neither makes nor finds present (the frame law). These are the two moves of universal schema
promotion; the absence-guard and scope-restriction controls show each hypothesis is needed. -/

theorem follow_equations_prefix :
    ∀ (schedule : List (ConditionalSchedule.Firing T O)) (C : Configuration T O),
      ∃ extra, (ConditionalSchedule.follow label C schedule).equations = C.equations ++ extra
  | [], C => ⟨[], by simp [ConditionalSchedule.follow]⟩
  | x :: rest, C => by
      obtain ⟨extra, same⟩ := follow_equations_prefix rest (x.2.result label x.1 C)
      refine ⟨added label x.1 x.2 ++ extra, ?_⟩
      change (ConditionalSchedule.follow label (x.2.result label x.1 C) rest).equations = _
      rw [same, result_equations, List.append_assoc]

theorem valid_frame {rule : RuleInstance T} {selection : Selection O} {C : Configuration T O}
    (free : rule.checks = []) (valid : selection.Valid A label rule C) {frame : Finset O}
    (apartMade : Disjoint selection.made.toFinset frame) :
    selection.Valid A label rule ⟨C.equations, C.present ∪ frame⟩ :=
  ⟨valid.take_distinct, valid.output_distinct, valid.take_length, valid.read_length, valid.outputs,
    valid.occurrences.frame_of_positive rfl apartMade, valid.consistent,
    fun check member => by rw [free] at member; cases member⟩

/-- **Frame law for check-free schedules.** -/
theorem executable_frame :
    ∀ (schedule : List (ConditionalSchedule.Firing T O)) (C : Configuration T O) (frame : Finset O),
      (∀ x ∈ schedule, x.1.checks = []) → Disjoint C.present frame →
      (∀ x ∈ schedule, Disjoint x.2.made.toFinset frame) →
      ConditionalSchedule.Executable A label C schedule →
      ConditionalSchedule.Executable A label ⟨C.equations, C.present ∪ frame⟩ schedule ∧
        ConditionalSchedule.follow label ⟨C.equations, C.present ∪ frame⟩ schedule =
          ⟨(ConditionalSchedule.follow label C schedule).equations,
            (ConditionalSchedule.follow label C schedule).present ∪ frame⟩
  | [], _, _, _, _, _, executable => ⟨executable, rfl⟩
  | x :: rest, C, frame, free, apart, madeApart, executable => by
      obtain ⟨valid, later⟩ := executable
      have framed := valid_frame A label (free x List.mem_cons_self) valid (madeApart x List.mem_cons_self)
      have takenApart : Disjoint (x.2.commit (T := T)).taken frame :=
        Finset.disjoint_of_subset_left valid.occurrences.taken_subset apart
      have resultSame : x.2.result label x.1 ⟨C.equations, C.present ∪ frame⟩ =
          ⟨(x.2.result label x.1 C).equations, (x.2.result label x.1 C).present ∪ frame⟩ := by
        change Configuration.mk (x.2.problem label x.1 ⟨C.equations, C.present ∪ frame⟩)
            (fire (C.present ∪ frame) (x.2.commit (T := T))) =
          Configuration.mk (x.2.problem label x.1 C) (fire C.present (x.2.commit (T := T)) ∪ frame)
        rw [fire_union_frame takenApart]
        rfl
      have apartAfter : Disjoint (x.2.result label x.1 C).present frame := by
        change Disjoint (fire C.present (x.2.commit (T := T))) frame
        refine Finset.disjoint_left.mpr fun o inFire inFrame => ?_
        rcases mem_fire.mp inFire with ⟨present, _⟩ | made
        · exact Finset.disjoint_left.mp apart present inFrame
        · exact Finset.disjoint_left.mp (madeApart x List.mem_cons_self) made inFrame
      obtain ⟨restExecutable, restFollow⟩ := executable_frame rest (x.2.result label x.1 C) frame
        (fun y hy => free y (List.mem_cons_of_mem _ hy)) apartAfter
        (fun y hy => madeApart y (List.mem_cons_of_mem _ hy)) later
      refine ⟨⟨framed, ?_⟩, ?_⟩
      · rw [resultSame]
        exact restExecutable
      · change ConditionalSchedule.follow label (x.2.result label x.1 ⟨C.equations, C.present ∪ frame⟩) rest = _
        rw [resultSame]
        exact restFollow

/-- Substitute every term of a firing's rule; the occurrence choices are unchanged. -/
def mapFiring (θ : S) (x : ConditionalSchedule.Firing T O) : ConditionalSchedule.Firing T O :=
  (x.1.map (A.apply θ), x.2)

/-- **Instance law for schedules**: a substitution compatible with the final store maps an
executable schedule to an executable schedule of the instantiated rules. Checks are kept and
transported (`SubstitutionStability.valid_map`). -/
theorem executable_map (θ : S) :
    ∀ (schedule : List (ConditionalSchedule.Firing T O)) (C : Configuration T O),
      ConditionalSchedule.Executable A label C schedule →
      A.Consistent (A.applyStore θ (ConditionalSchedule.follow label C schedule).equations) →
      ConditionalSchedule.Executable A (fun o => A.apply θ (label o))
          (SubstitutionStability.configuration A θ C) (schedule.map (mapFiring A θ)) ∧
        ConditionalSchedule.follow (fun o => A.apply θ (label o))
            (SubstitutionStability.configuration A θ C) (schedule.map (mapFiring A θ)) =
          SubstitutionStability.configuration A θ (ConditionalSchedule.follow label C schedule)
  | [], _, _, compatible => ⟨compatible, rfl⟩
  | x :: rest, C, executable, compatible => by
      obtain ⟨valid, later⟩ := executable
      have prefixCompatible : A.Consistent (A.applyStore θ (x.2.problem label x.1 C)) := by
        obtain ⟨σ, solved⟩ := compatible
        obtain ⟨extra, same⟩ := follow_equations_prefix label rest (x.2.result label x.1 C)
        refine ⟨σ, ?_⟩
        change A.Models σ (A.applyStore θ
          (ConditionalSchedule.follow label (x.2.result label x.1 C) rest).equations) at solved
        rw [same] at solved
        simp only [SubstitutionAction.applyStore, List.map_append] at solved
        exact ((A.models_append _ _ _).mp solved).1
      have mapped := SubstitutionStability.valid_map A θ label valid prefixCompatible
      obtain ⟨restExecutable, restFollow⟩ := executable_map θ rest (x.2.result label x.1 C) later compatible
      have resultSame := SubstitutionStability.result_map A θ label x.1 x.2 C
      refine ⟨⟨mapped, ?_⟩, ?_⟩
      · change ConditionalSchedule.Executable A (fun o => A.apply θ (label o))
          (x.2.result (fun o => A.apply θ (label o)) (x.1.map (A.apply θ))
            (SubstitutionStability.configuration A θ C)) (rest.map (mapFiring A θ))
        rw [resultSame]
        exact restExecutable
      · change ConditionalSchedule.follow (fun o => A.apply θ (label o))
          (x.2.result (fun o => A.apply θ (label o)) (x.1.map (A.apply θ))
            (SubstitutionStability.configuration A θ C)) (rest.map (mapFiring A θ)) = _
        rw [resultSame]
        exact restFollow

/-- **Guard-free admitted instances.** A check-free schedule, instantiated by a substitution
compatible with its final store and placed beside a frame it neither makes nor finds, still
runs, and ends in the instantiated final store beside the same frame. -/
theorem admitted_instance (θ : S) (schedule : List (ConditionalSchedule.Firing T O))
    (C : Configuration T O) (frame : Finset O)
    (free : ∀ x ∈ schedule, x.1.checks = [])
    (executable : ConditionalSchedule.Executable A label C schedule)
    (compatible : A.Consistent (A.applyStore θ (ConditionalSchedule.follow label C schedule).equations))
    (apart : Disjoint C.present frame)
    (madeApart : ∀ x ∈ schedule, Disjoint x.2.made.toFinset frame) :
    ConditionalSchedule.Executable A (fun o => A.apply θ (label o))
        ⟨A.applyStore θ C.equations, C.present ∪ frame⟩ (schedule.map (mapFiring A θ)) ∧
      ConditionalSchedule.follow (fun o => A.apply θ (label o))
          ⟨A.applyStore θ C.equations, C.present ∪ frame⟩ (schedule.map (mapFiring A θ)) =
        ⟨A.applyStore θ (ConditionalSchedule.follow label C schedule).equations,
          (ConditionalSchedule.follow label C schedule).present ∪ frame⟩ := by
  obtain ⟨mappedExecutable, mappedFollow⟩ := executable_map A label θ schedule C executable compatible
  have mappedFree : ∀ x ∈ schedule.map (mapFiring A θ), x.1.checks = [] := by
    intro x member
    obtain ⟨y, inSchedule, rfl⟩ := List.mem_map.mp member
    simp [mapFiring, RuleInstance.map, free y inSchedule]
  have mappedApart : ∀ x ∈ schedule.map (mapFiring A θ), Disjoint x.2.made.toFinset frame := by
    intro x member
    obtain ⟨y, inSchedule, rfl⟩ := List.mem_map.mp member
    exact madeApart y inSchedule
  obtain ⟨framedExecutable, framedFollow⟩ := executable_frame A (fun o => A.apply θ (label o))
    (schedule.map (mapFiring A θ)) (SubstitutionStability.configuration A θ C) frame mappedFree apart
    mappedApart mappedExecutable
  refine ⟨framedExecutable, ?_⟩
  rw [show (⟨A.applyStore θ C.equations, C.present ∪ frame⟩ : Configuration T O) =
      ⟨(SubstitutionStability.configuration A θ C).equations,
        (SubstitutionStability.configuration A θ C).present ∪ frame⟩ from rfl, framedFollow, mappedFollow]
  rfl


end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardFreeProcessOrders
