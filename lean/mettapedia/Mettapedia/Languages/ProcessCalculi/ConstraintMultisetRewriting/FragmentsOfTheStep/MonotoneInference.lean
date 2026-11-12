import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.GroundFirings
import Mathlib.Order.FixedPoints

/-!
# Monotone inference: runs reach Datalog's least model

A rule set is in the **monotone fragment** (`Monotone`) when its rules take nothing and check
nothing: they read and make. Over ground terms:

* `Derivable R start`: Datalog's derivations from the facts `start`; a rule whose reads are derived
  and whose tells have identical sides derives what it makes.
* `derivable_eq_lfp`: the derivable facts are the **least fixed point** of the immediate-consequence
  operator above `start` (`consequence`): the least model.
* `run_derivable`: every fact present after a run is derivable from the start's facts (for every rule
  set; the derivations read only reads and makes).
* `derivable_reached`: on the monotone fragment, every derivable fact is present after some run.
* `eventual_facts`: from every store a run reaches, the facts that some further run makes present are
  exactly the least model of the start's facts. `confluent`: **any two runs from one store have the
  same eventual facts**, so the order of firing never matters for what can be inferred.
  `reachable_eq_lfp`: the reachable facts are the least fixed point.

The step keeps multiplicities: a monotone rule can fire again on the same reads and make another
copy, so runs need not end. Confluence and the least model are statements about facts, the labels
present, as in Datalog's set semantics.

## Controls

* Positive: `Controls.closure_reaches_path`: transitive closure over the edges `1 → 2 → 3`; the path
  `1 → 3` is derivable and some run makes it present.
* Negative, just outside: `Controls.choice_not_confluent`: two rules that both take `a`, one making `b`
  and one making `c`. From `{a}` one run reaches `{b}` and another `{c}`; `c` stays reachable from the
  second and never from the first, so `confluent` fails once rules take.
* Negative, just outside: `Controls.absence_not_confluent`: make `left` where `other` is absent, and
  `other` where `left` is absent. From the empty store the two runs part ways for good: `confluent`
  fails once rules check absence, and the two outcomes are two minimal stable stores rather than one
  least model.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep

open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open NamesOnTheStep NamesOnTheStep.IssuingControls GroundFirings
open HeatingBisimulation (RuleSet)

namespace MonotoneInference

/-- **The monotone fragment**: rules take nothing and check nothing. -/
def Monotone (R : RuleSet Expr) : Prop := ∀ rule, R rule → rule.take = [] ∧ rule.checks = []

/-- **Datalog's derivations** from the facts `start`. -/
inductive Derivable (R : RuleSet Expr) (start : Set Expr) : Expr → Prop
  | start {p : Expr} : p ∈ start → Derivable R start p
  | rule {r : RuleInstance Expr} {p : Expr} : R r → (∀ e ∈ r.tell, e.1 = e.2) →
      (∀ q ∈ r.read, Derivable R start q) → p ∈ r.produce → Derivable R start p

/-- The immediate-consequence operator above the facts `start`. -/
def consequence (R : RuleSet Expr) (start : Set Expr) : Set Expr →o Set Expr where
  toFun M := start ∪ {p | ∃ r, R r ∧ (∀ e ∈ r.tell, e.1 = e.2) ∧ (∀ q ∈ r.read, q ∈ M) ∧ p ∈ r.produce}
  monotone' := by
    intro M N sub p member
    rcases member with inStart | ⟨r, member, tells, reads, made⟩
    · exact Or.inl inStart
    · exact Or.inr ⟨r, member, tells, fun q inRead => sub (reads q inRead), made⟩

/-- **The derivable facts are the least fixed point of the immediate-consequence operator**:
Datalog's least model. -/
theorem derivable_eq_lfp (R : RuleSet Expr) (start : Set Expr) :
    {p | Derivable R start p} = OrderHom.lfp (consequence R start) := by
  apply le_antisymm
  · intro p derived
    induction derived with
    | start member =>
        rw [← OrderHom.map_lfp]
        exact Or.inl member
    | rule member tells _ made earlier =>
        rw [← OrderHom.map_lfp]
        exact Or.inr ⟨_, member, tells, earlier, made⟩
  · apply OrderHom.lfp_le
    intro p member
    rcases member with inStart | ⟨r, member, tells, reads, made⟩
    · exact Derivable.start inStart
    · exact Derivable.rule member tells reads made

theorem derivable_mono {R : RuleSet Expr} {start start' : Set Expr} (sub : start ⊆ start')
    {p : Expr} (derived : Derivable R start p) : Derivable R start' p := by
  induction derived with
  | start member => exact Derivable.start (sub member)
  | rule member tells _ made earlier => exact Derivable.rule member tells earlier made

theorem forall₂_left {P : Expr → Occ → Prop} :
    ∀ {patterns : List Expr} {selected : List Occ}, List.Forall₂ P patterns selected →
      ∀ q ∈ patterns, ∃ o ∈ selected, P q o
  | _, _, .nil, _, member => absurd member List.not_mem_nil
  | _, _, .cons head tail, q, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons.mpr (Or.inl rfl), head⟩
      · obtain ⟨o, inSelected, holds⟩ := forall₂_left tail q later
        exact ⟨o, List.mem_cons_of_mem _ inSelected, holds⟩

/-- One firing keeps every fact derivable. -/
theorem step_derivable {R : RuleSet Expr} {start : Set Expr} {C C' : Conf} (step : GroundStep R C C')
    (derived : ∀ p ∈ facts C, Derivable R start p) : ∀ p ∈ facts C', Derivable R start p := by
  obtain ⟨r, member, sel, valid, rfl⟩ := step
  rintro p ⟨o, present, rfl⟩
  change o ∈ fire C.present (sel.commit (T := Expr)) at present
  rw [mem_fire] at present
  rcases present with ⟨old, _⟩ | made
  · exact derived _ ⟨o, old, rfl⟩
  · have produced : o.1 ∈ r.produce := made_label valid (by simpa [Selection.commit] using made)
    refine Derivable.rule member (tells_trivial valid) (fun q inRead => ?_) produced
    obtain ⟨o', inSelected, same⟩ := forall₂_left (reads_match valid) q inRead
    exact derived q ⟨o', read_present valid inSelected, same.symm⟩

/-- **Soundness**: every fact present after a run is derivable from the start's facts. -/
theorem run_derivable {R : RuleSet Expr} {C C' : Conf}
    (run : Relation.ReflTransGen (GroundStep R) C C') : ∀ p ∈ facts C', Derivable R (facts C) p := by
  induction run with
  | refl => exact fun p member => Derivable.start member
  | tail _ step earlier => exact step_derivable step earlier

/-- Facts only grow along monotone runs. -/
theorem facts_mono {R : RuleSet Expr} (monotone : Monotone R) {C C' : Conf}
    (run : Relation.ReflTransGen (GroundStep R) C C') : facts C ⊆ facts C' := by
  induction run with
  | refl => exact fun _ member => member
  | tail _ step earlier =>
      obtain ⟨r, member, sel, valid, rfl⟩ := step
      intro p inFacts
      obtain ⟨o, present, same⟩ := earlier inFacts
      exact ⟨o, taken_nil_present (monotone r member).1 valid present, same⟩

theorem run_knowledge {R : RuleSet Expr} {C C' : Conf} (trivial : ∀ e ∈ C.equations, e.1 = e.2)
    (run : Relation.ReflTransGen (GroundStep R) C C') : ∀ e ∈ C'.equations, e.1 = e.2 := by
  induction run with
  | refl => exact trivial
  | tail _ step _ => exact groundStep_knowledge step

/-- Occurrences carrying every pattern of a list, all present. -/
theorem select_reads : ∀ (patterns : List Expr) {C : Conf}, (∀ q ∈ patterns, q ∈ facts C) →
    ∃ selected : List Occ, patterns = selected.map Prod.fst ∧ ∀ o ∈ selected, o ∈ C.present
  | [], _, _ => ⟨[], rfl, by simp⟩
  | q :: rest, C, all => by
      obtain ⟨o, present, same⟩ := all q (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨selected, mapped, inside⟩ :=
        select_reads rest (fun q' member => all q' (List.mem_cons_of_mem _ member))
      refine ⟨o :: selected, by rw [List.map_cons, ← mapped, same], ?_⟩
      intro o' member
      rcases List.mem_cons.mp member with rfl | later
      · exact present
      · exact inside o' later

/-- **A monotone rule fires wherever its reads are facts**, making its makes facts. -/
theorem fire_rule {R : RuleSet Expr} (monotone : Monotone R) {r : RuleInstance Expr} (member : R r)
    (tells : ∀ e ∈ r.tell, e.1 = e.2) {C : Conf} (trivial : ∀ e ∈ C.equations, e.1 = e.2)
    (reads : ∀ q ∈ r.read, q ∈ facts C) :
    ∃ C', GroundStep R C C' ∧ ∀ p ∈ r.produce, p ∈ facts C' := by
  obtain ⟨noTakes, noChecks⟩ := monotone r member
  obtain ⟨selected, mapped, inside⟩ := select_reads r.read reads
  obtain ⟨made, distinct, away, outputs⟩ := fresh_outputs r.produce C.present
  let sel : Selection Occ := ⟨[], selected, made⟩
  have enabled : Enabled Prod.fst C.present (sel.commit (T := Expr)) := by
    refine ⟨by simp [sel, Selection.commit], ?_, by simp [sel, Selection.commit], away,
      fun _ query => by simp [Selection.commit] at query⟩
    intro o inKept
    exact inside o (by simpa [sel, Selection.commit] using inKept)
  have solved : ground.Models () (sel.problem Prod.fst r C) := by
    intro e inProblem
    simp only [Selection.problem, List.mem_append] at inProblem
    rcases inProblem with ((old | taken) | read) | told
    · exact trivial e old
    · simp [sel, noTakes, Selection.equations] at taken
    · rw [mapped] at read
      exact equations_self read
    · exact tells e told
  have valid : sel.Valid ground Prod.fst r C :=
    ⟨List.nodup_nil, distinct, by simp [sel, noTakes], by rw [mapped, List.length_map], outputs,
      enabled, ⟨(), solved⟩, by simp [noChecks]⟩
  refine ⟨_, ⟨r, member, sel, valid, rfl⟩, fun p produced => ?_⟩
  rw [← outputs] at produced
  obtain ⟨o, inMade, rfl⟩ := List.mem_map.mp produced
  exact ⟨o, made_present inMade, rfl⟩

/-- Every fact of a list, each reachable from every store holding the start, is reached together. -/
theorem reach_all {R : RuleSet Expr} (monotone : Monotone R) {start : Set Expr} :
    ∀ (patterns : List Expr), (∀ q ∈ patterns, ∀ C : Conf, (∀ e ∈ C.equations, e.1 = e.2) →
        start ⊆ facts C → ∃ C', Relation.ReflTransGen (GroundStep R) C C' ∧ q ∈ facts C') →
      ∀ C : Conf, (∀ e ∈ C.equations, e.1 = e.2) → start ⊆ facts C →
        ∃ C', Relation.ReflTransGen (GroundStep R) C C' ∧ ∀ q ∈ patterns, q ∈ facts C'
  | [], _, C, _, _ => ⟨C, .refl, by simp⟩
  | q :: rest, each, C, trivial, sub => by
      obtain ⟨C₁, first, here⟩ := each q (List.mem_cons.mpr (Or.inl rfl)) C trivial sub
      obtain ⟨C₂, second, there⟩ := reach_all monotone rest
        (fun q' member => each q' (List.mem_cons_of_mem _ member)) C₁ (run_knowledge trivial first)
        (sub.trans (facts_mono monotone first))
      refine ⟨C₂, first.trans second, ?_⟩
      intro q' member
      rcases List.mem_cons.mp member with rfl | later
      · exact facts_mono monotone second here
      · exact there q' later

/-- **Completeness**: on the monotone fragment every derivable fact is present after some run. -/
theorem derivable_reached {R : RuleSet Expr} (monotone : Monotone R) {start : Set Expr} {p : Expr}
    (derived : Derivable R start p) :
    ∀ C : Conf, (∀ e ∈ C.equations, e.1 = e.2) → start ⊆ facts C →
      ∃ C', Relation.ReflTransGen (GroundStep R) C C' ∧ p ∈ facts C' := by
  induction derived with
  | start member => exact fun C _ sub => ⟨C, .refl, sub member⟩
  | rule member tells _ made earlier =>
      intro C trivial sub
      obtain ⟨C₁, first, all⟩ := reach_all monotone _ earlier C trivial sub
      obtain ⟨C₂, step, makes⟩ := fire_rule monotone member tells (run_knowledge trivial first) all
      exact ⟨C₂, first.tail step, makes _ made⟩

/-- **Eventual facts are the least model**: from every store a run reaches, the facts some
further run makes present are exactly those derivable from the start's facts. -/
theorem eventual_facts {R : RuleSet Expr} (monotone : Monotone R) {C C' : Conf}
    (trivial : ∀ e ∈ C.equations, e.1 = e.2) (run : Relation.ReflTransGen (GroundStep R) C C')
    (p : Expr) :
    (∃ C'', Relation.ReflTransGen (GroundStep R) C' C'' ∧ p ∈ facts C'') ↔ Derivable R (facts C) p := by
  constructor
  · rintro ⟨C'', more, present⟩
    exact run_derivable (run.trans more) p present
  · intro derived
    exact derivable_reached monotone (derivable_mono (facts_mono monotone run) derived) C'
      (run_knowledge trivial run) (fun _ member => member)

/-- **Confluence of inference**: any two runs from one store have the same eventual facts. -/
theorem confluent {R : RuleSet Expr} (monotone : Monotone R) {C C₁ C₂ : Conf}
    (trivial : ∀ e ∈ C.equations, e.1 = e.2) (first : Relation.ReflTransGen (GroundStep R) C C₁)
    (second : Relation.ReflTransGen (GroundStep R) C C₂) (p : Expr) :
    (∃ D, Relation.ReflTransGen (GroundStep R) C₁ D ∧ p ∈ facts D) ↔
      ∃ D, Relation.ReflTransGen (GroundStep R) C₂ D ∧ p ∈ facts D :=
  (eventual_facts monotone trivial first p).trans (eventual_facts monotone trivial second p).symm

/-- **The reachable facts are the least fixed point** above the start's facts. -/
theorem reachable_eq_lfp {R : RuleSet Expr} (monotone : Monotone R) {C : Conf}
    (trivial : ∀ e ∈ C.equations, e.1 = e.2) :
    {p | ∃ C', Relation.ReflTransGen (GroundStep R) C C' ∧ p ∈ facts C'} =
      OrderHom.lfp (consequence R (facts C)) := by
  rw [← derivable_eq_lfp]
  ext p
  exact eventual_facts monotone trivial .refl p

end MonotoneInference

/-! ## Controls -/

namespace MonotoneInference.Controls

def node (n : ℕ) : Expr := .sym n
def edge (a b : ℕ) : Expr := .app (.app (.sym 30) (node a)) (node b)
def path (a b : ℕ) : Expr := .app (.app (.sym 31) (node a)) (node b)

/-- An edge is a path. -/
def base (a b : ℕ) : RuleInstance Expr := rule [] [edge a b] [path a b]
/-- A path then an edge is a path. -/
def extend (a b c : ℕ) : RuleInstance Expr := rule [] [path a b, edge b c] [path a c]

/-- Transitive closure, as ground instances. -/
def closure : RuleSet Expr := fun r => (∃ a b, r = base a b) ∨ ∃ a b c, r = extend a b c

theorem closure_monotone : Monotone closure := by
  rintro _ (⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩) <;> exact ⟨rfl, rfl⟩

/-- The edges `1 → 2 → 3`. -/
def graph : Conf := ⟨[], {(edge 1 2, 0), (edge 2 3, 0)}⟩

theorem edge_fact {a b : ℕ} (present : (edge a b, 0) ∈ graph.present) : edge a b ∈ facts graph :=
  ⟨_, present, rfl⟩

theorem path_one_three : Derivable closure (facts graph) (path 1 3) := by
  have onePath : Derivable closure (facts graph) (path 1 2) :=
    Derivable.rule (r := base 1 2) (Or.inl ⟨1, 2, rfl⟩) (by simp [base, rule])
      (fun q member => by
        simp only [base, rule, List.mem_singleton] at member
        subst member
        exact Derivable.start (edge_fact (by decide)))
      (by simp [base, rule])
  refine Derivable.rule (r := extend 1 2 3) (Or.inr ⟨1, 2, 3, rfl⟩) (by simp [extend, rule])
    (fun q member => ?_) (by simp [extend, rule])
  simp only [extend, rule, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact onePath
  · exact Derivable.start (edge_fact (by decide))

/-- **Positive control.** Transitive closure reaches the path `1 → 3`. -/
theorem closure_reaches_path :
    Monotone closure ∧ ∃ C', Relation.ReflTransGen (GroundStep closure) graph C' ∧ path 1 3 ∈ facts C' :=
  ⟨closure_monotone, (eventual_facts closure_monotone (by simp [graph]) .refl _).mpr path_one_three⟩

def item : Expr := .sym 50
def left : Expr := .sym 51
def right : Expr := .sym 52

def toLeft : RuleInstance Expr := rule [item] [] [left]
def toRight : RuleInstance Expr := rule [item] [] [right]

/-- Two rules that both take `item`. -/
def choice : RuleSet Expr := fun r => r = toLeft ∨ r = toRight

def single : Conf := ⟨[], {(item, 0)}⟩
def leftAt : Selection Occ := ⟨[(item, 0)], [], [(left, 0)]⟩
def rightAt : Selection Occ := ⟨[(item, 0)], [], [(right, 0)]⟩

def afterLeft : Conf := leftAt.result Prod.fst toLeft single
def afterRight : Conf := rightAt.result Prod.fst toRight single

theorem afterLeft_present : afterLeft.present = {(left, 0)} := by decide

/-- Nothing fires once `item` is gone. -/
theorem afterLeft_stuck (D : Conf) : ¬ GroundStep choice afterLeft D := by
  rintro ⟨r, member, sel, valid, -⟩
  have takes := takes_match valid
  have takesItem : r.take = [item] := by
    rcases member with rfl | rfl <;> rfl
  rw [takesItem] at takes
  obtain ⟨o, taken, labelled⟩ := match_one takes
  have present := taken_present valid (o := o) (by simp [taken])
  rw [afterLeft_present, Finset.mem_singleton] at present
  subst present
  exact absurd labelled (by decide)

/-- **Negative control.** Once rules take, two runs from `{item}` part ways: `right` stays reachable
after the run to `right` and never after the run to `left`. -/
theorem choice_not_confluent :
    ¬ Monotone choice ∧
      Relation.ReflTransGen (GroundStep choice) single afterLeft ∧
      Relation.ReflTransGen (GroundStep choice) single afterRight ∧
      (∃ D, Relation.ReflTransGen (GroundStep choice) afterRight D ∧ right ∈ facts D) ∧
      ¬ ∃ D, Relation.ReflTransGen (GroundStep choice) afterLeft D ∧ right ∈ facts D := by
  have leftValid : leftAt.Valid ground Prod.fst toLeft single :=
    ground_valid (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
  have rightValid : rightAt.Valid ground Prod.fst toRight single :=
    ground_valid (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (no_checks rfl)
  refine ⟨fun monotone => ?_, .single ⟨toLeft, Or.inl rfl, leftAt, leftValid, rfl⟩,
    .single ⟨toRight, Or.inr rfl, rightAt, rightValid, rfl⟩,
    ⟨afterRight, .refl, (right, 0), by decide, rfl⟩, ?_⟩
  · have noTakes := (monotone toLeft (Or.inl rfl)).1
    simp [toLeft, rule] at noTakes
  · rintro ⟨D, run, o, present, labelled⟩
    rcases Relation.ReflTransGen.cases_head run with rfl | ⟨_, step, _⟩
    · rw [afterLeft_present, Finset.mem_singleton] at present
      subst present
      exact absurd labelled (by decide)
    · exact afterLeft_stuck _ step

def other : Expr := .sym 53

/-- Make `left` where `other` is absent. -/
def leftUnlessOther : RuleInstance Expr := rule [] [] [left] [.absent other]
/-- Make `other` where `left` is absent. -/
def otherUnlessLeft : RuleInstance Expr := rule [] [] [other] [.absent left]

/-- Two rules, each guarded by the absence of what the other makes. -/
def guarded : RuleSet Expr := fun r => r = leftUnlessOther ∨ r = otherUnlessLeft

def empty : Conf := ⟨[], ∅⟩
def makeLeftAt : Selection Occ := ⟨[], [], [(left, 0)]⟩
def makeOtherAt : Selection Occ := ⟨[], [], [(other, 0)]⟩

def withLeft : Conf := makeLeftAt.result Prod.fst leftUnlessOther empty
def withOther : Conf := makeOtherAt.result Prod.fst otherUnlessLeft empty

/-- What every store reached from `withLeft` satisfies: `left` is present and `other` is not. -/
def LeftOnly (C : Conf) : Prop := (∃ o ∈ C.present, o.1 = left) ∧ ∀ o ∈ C.present, o.1 ≠ other

theorem leftOnly_step {C C' : Conf} (before : LeftOnly C) (step : GroundStep guarded C C') :
    LeftOnly C' := by
  obtain ⟨r, member, sel, valid, rfl⟩ := step
  obtain ⟨⟨o, present, isLeft⟩, noOther⟩ := before
  rcases member with rfl | rfl
  · have keeps := taken_nil_present rfl valid
    refine ⟨⟨o, keeps present, isLeft⟩, fun o' member' => ?_⟩
    change o' ∈ MeTTaCalculus.OccurrenceCommits.fire C.present (sel.commit (T := Expr)) at member'
    rw [MeTTaCalculus.OccurrenceCommits.mem_fire] at member'
    rcases member' with ⟨old, _⟩ | made
    · exact noOther o' old
    · have produced := made_label valid (by simpa [Selection.commit] using made)
      have labelled : o'.1 = left := List.mem_singleton.mp produced
      rw [labelled]
      decide
  · exact absurd valid (fun refused => absent_refuted refused (p := left) (List.mem_singleton.mpr rfl)
      present isLeft)

theorem leftOnly_reached {D : Conf} (run : Relation.ReflTransGen (GroundStep guarded) withLeft D) :
    LeftOnly D := by
  induction run with
  | refl =>
      exact ⟨⟨(left, 0), made_present (r := leftUnlessOther) (sel := makeLeftAt) (C := empty)
        (by simp [makeLeftAt]), rfl⟩, by decide⟩
  | tail _ step earlier => exact leftOnly_step earlier step

/-- **Negative control.** Absence guards break inference: from the empty store one run makes
`left` and another `other`; `other` stays reachable after the second and never after the first, and
neither fact is in every run's eventual facts. -/
theorem absence_not_confluent :
    ¬ Monotone guarded ∧
      Relation.ReflTransGen (GroundStep guarded) empty withLeft ∧
      Relation.ReflTransGen (GroundStep guarded) empty withOther ∧
      (∃ D, Relation.ReflTransGen (GroundStep guarded) withOther D ∧ other ∈ facts D) ∧
      ¬ ∃ D, Relation.ReflTransGen (GroundStep guarded) withLeft D ∧ other ∈ facts D := by
  have leftValid : makeLeftAt.Valid ground Prod.fst leftUnlessOther empty :=
    ground_valid (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (by
      intro c member
      simp only [leftUnlessOther, rule, List.mem_singleton] at member
      subst member
      exact absent_holds (by decide))
  have otherValid : makeOtherAt.Valid ground Prod.fst otherUnlessLeft empty :=
    ground_valid (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl (by
      intro c member
      simp only [otherUnlessLeft, rule, List.mem_singleton] at member
      subst member
      exact absent_holds (by decide))
  refine ⟨fun monotone => ?_, .single ⟨_, Or.inl rfl, makeLeftAt, leftValid, rfl⟩,
    .single ⟨_, Or.inr rfl, makeOtherAt, otherValid, rfl⟩,
    ⟨withOther, .refl, (other, 0), made_present (r := otherUnlessLeft) (sel := makeOtherAt)
      (C := empty) (by simp [makeOtherAt]), rfl⟩, ?_⟩
  · have noChecks := (monotone leftUnlessOther (Or.inl rfl)).2
    simp [leftUnlessOther, rule] at noChecks
  · rintro ⟨D, run, o, present, labelled⟩
    exact (leftOnly_reached run).2 o present labelled

end MonotoneInference.Controls

open MonotoneInference in
#print axioms derivable_eq_lfp
open MonotoneInference in
#print axioms run_derivable
open MonotoneInference in
#print axioms derivable_reached
open MonotoneInference in
#print axioms eventual_facts
open MonotoneInference in
#print axioms confluent
open MonotoneInference in
#print axioms reachable_eq_lfp
#print axioms MonotoneInference.Controls.closure_reaches_path
#print axioms MonotoneInference.Controls.choice_not_confluent
#print axioms MonotoneInference.Controls.absence_not_confluent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep
