import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Answers.Bags

/-!
# One set of rules, one start state, two bags

`Answers.Bags.same_translation` gives two programs with one set of rules and two bags; their start
states differ (one more equation row). Here the two programs have the same rules **and the same start
state**, and still two bags.

* `PA` is `(= (f) one)`, `(= (f) one)`, `(= (f) two)`; `PB` is `(= (f) one)`, `(= (f) two)`,
  `(= (f) two)`; the query is `(f)`.
* `same_rules`: one translation. `same_start`: one start state. `same_step`: so a firing of the one
  translated program is a firing of the other, and `same_step_answers`: the answers the step shows are
  one set.
* `pa_answers`, `pb_answers`, `bags_differ`: runs of the source reach configurations that end, with the
  bags `{two, one, one}` for `PA` and `{two, two, one}` for `PB`.

So no function of the rules and the start state gives the bag of answers of every program of the first
fragment.

**Against `Alternatives.bag_of_rule_classes`**, which reads the bag from the step's histories by rules:
its hypotheses are the first fragment (program and query), a query whose names are unopened, a run that
ends, and pairwise distinct schemas of the equations. `PA` and its run meet every hypothesis but the
last (`pa_meets_the_rest`), and fails that one (`pa_not_distinct`): two of its equations have one
schema. The same holds of `PB` (`pb_not_distinct`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Answers.SameStart

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Answers.Bags
open Classical

def twoT : MData := sym "two"
def twoC : MClosed := csym "two"

def e1 : SourceLanguage.Equation mkeys [] () MTy := ⟨[400], fT, .ret oneT⟩
def e1' : SourceLanguage.Equation mkeys [] () MTy := ⟨[401], fT, .ret oneT⟩
def e2' : SourceLanguage.Equation mkeys [] () MTy := ⟨[401], fT, .ret twoT⟩
def e2 : SourceLanguage.Equation mkeys [] () MTy := ⟨[402], fT, .ret twoT⟩

/-- `(= (f) one)`, `(= (f) one)`, `(= (f) two)`. -/
def PA : SourceLanguage.Program mkeys [] () MTy := ⟨[e1, e1', e2], fun t => .apply t⟩
/-- `(= (f) one)`, `(= (f) two)`, `(= (f) two)`. -/
def PB : SourceLanguage.Program mkeys [] () MTy := ⟨[e1, e2', e2], fun t => .apply t⟩

/-- **One translation.** -/
theorem same_rules : translate N PA = translate N PB := by
  ext r
  constructor
  · rintro (control | ⟨e, member, rfl⟩)
    · exact .inl control
    · have member' : e ∈ [e1, e1', e2] := member
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at member'
      rcases member' with rfl | rfl | rfl
      · exact .inr ⟨e1, List.mem_cons_self, rfl⟩
      · exact .inr ⟨e1, List.mem_cons_self, rfl⟩
      · exact .inr ⟨e2, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩
  · rintro (control | ⟨e, member, rfl⟩)
    · exact .inl control
    · have member' : e ∈ [e1, e2', e2] := member
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at member'
      rcases member' with rfl | rfl | rfl
      · exact .inr ⟨e1, List.mem_cons_self, rfl⟩
      · exact .inr ⟨e2, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩
      · exact .inr ⟨e2, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩

/-- **One start state**: three equation rows `eqn((f))` and the query's alternative, in both. -/
theorem same_start : Hosting.start N PA q = Hosting.start N PB q := by
  have labels : startLabel N PA q = startLabel N PB q := by
    funext o
    unfold startLabel
    by_cases h : o < 3
    · have hA : o < PA.equations.length := h
      have hB : o < PB.equations.length := h
      rw [dif_pos hA, dif_pos hB]
      have lhsA : (PA.equations.get ⟨o, hA⟩).lhs = fT := by
        interval_cases o <;> rfl
      have lhsB : (PB.equations.get ⟨o, hB⟩).lhs = fT := by
        interval_cases o <;> rfl
      rw [lhsA, lhsB]
    · have hA : ¬ o < PA.equations.length := h
      have hB : ¬ o < PB.equations.length := h
      rw [dif_neg hA, dif_neg hB]
  show (⟨startFrame mkeys, [], insert PA.equations.length (Finset.range PA.equations.length),
      startLabel N PA q⟩ : HostState MSig) =
    ⟨startFrame mkeys, [], insert PB.equations.length (Finset.range PB.equations.length), startLabel N PB q⟩
  rw [labels]
  rfl

/-- **One step**: a firing of the one translated program is a firing of the other. -/
theorem same_step (s s' : HostState MSig) : Fires N PA s s' ↔ Fires N PB s s' := by
  unfold Fires
  rw [same_rules]

/-- **So the answers the step shows are the same set.** -/
theorem same_step_answers : stepAnswers N PA q = stepAnswers N PB q := by
  unfold stepAnswers
  rw [same_start]
  have fires : Fires N PA = Fires N PB := by
    funext s s'
    exact propext (same_step s s')
  rw [fires]

abbrev X2 : Branch mkeys [] () MTy := ⟨[(fT, fT)], .eval (.ret twoT), [], []⟩
abbrev Y2 : Branch mkeys [] () MTy := ⟨[(fT, fT)], .value twoT, [], []⟩

theorem determines_two : Determines ([(fT, fT)] : List (Constraint mkeys [] ())) twoT twoC :=
  ⟨live_ff, fun _ _ _ => rfl⟩

theorem matchedA : ∃ e' ∈ PA.equations, Solvable ([] ++ [(instantiate (copyAt mkeys 0) e'.lhs, fT)]) :=
  ⟨e1, List.mem_cons_self, live_ff⟩

theorem matchedB : ∃ e' ∈ PB.equations, Solvable ([] ++ [(instantiate (copyAt mkeys 0) e'.lhs, fT)]) :=
  ⟨e1, List.mem_cons_self, live_ff⟩

/-- The configuration `PA`'s run ends in. -/
def finalA : Config mkeys [] () MTy := ⟨W1, {Y2, Y, Y}⟩
/-- The configuration `PB`'s run ends in. -/
def finalB : Config mkeys [] () MTy := ⟨W1, {Y2, Y2, Y}⟩

theorem pa_runs : Runs D PA supply (Config.initial sp q) finalA := by
  refine Relation.ReflTransGen.tail (b := ⟨W1, {Y, Y, X2}⟩) ?_
    (Step.of_eq (D := D) (P := PA) (supply := supply) (b := X2) (rest := {Y, Y})
      ((congrArg (fun m => Y ::ₘ m) (Multiset.cons_swap Y X2 0)).trans (Multiset.cons_swap Y X2 {Y})) rfl
      live_ff (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨W1, {Y, X, X2}⟩) ?_
    (Step.of_eq (D := D) (P := PA) (supply := supply) (b := X) (rest := {Y, X2}) (Multiset.cons_swap _ _ _) rfl
      live_ff (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨W1, {X, X, X2}⟩) ?_
    (Step.of_eq (D := D) (P := PA) (supply := supply) (b := X) (rest := {X, X2}) rfl rfl live_ff
      (.ret _ _ _ _ _))
  exact Relation.ReflTransGen.single (Step.of_eq (rest := 0) rfl rfl live_nil (.apply W0 [] fT [] [] matchedA))

theorem pb_runs : Runs D PB supply (Config.initial sp q) finalB := by
  refine Relation.ReflTransGen.tail (b := ⟨W1, {Y2, Y, X2}⟩) ?_
    (Step.of_eq (D := D) (P := PB) (supply := supply) (b := X2) (rest := {Y2, Y})
      ((congrArg (fun m => Y2 ::ₘ m) (Multiset.cons_swap Y X2 0)).trans (Multiset.cons_swap Y2 X2 {Y})) rfl
      live_ff (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨W1, {Y, X2, X2}⟩) ?_
    (Step.of_eq (D := D) (P := PB) (supply := supply) (b := X2) (rest := {Y, X2}) (Multiset.cons_swap _ _ _) rfl
      live_ff (.ret _ _ _ _ _))
  refine Relation.ReflTransGen.tail (b := ⟨W1, {X, X2, X2}⟩) ?_
    (Step.of_eq (D := D) (P := PB) (supply := supply) (b := X) (rest := {X2, X2}) rfl rfl live_ff
      (.ret _ _ _ _ _))
  exact Relation.ReflTransGen.single (Step.of_eq (rest := 0) rfl rfl live_nil (.apply W0 [] fT [] [] matchedB))

/-- **`PA` answers `{two, one, one}`.** -/
theorem pa_answers : Config.answers (D := D) finalA = {{twoC}, {oneC}, {oneC}} := by
  show Config.answers (D := D) ⟨W1, Y2 ::ₘ Y ::ₘ {Y}⟩ = _
  rw [answers_cons_finished (D := D) ⟨rfl, _, rfl⟩ live_ff, answers_cons_finished (D := D) ⟨rfl, _, rfl⟩ live_ff,
    answers_singleton (D := D) ⟨rfl, _, rfl⟩ live_ff,
    answer_of_determines (D := D) (b := Y2) rfl determines_two,
    answer_of_determines (D := D) (b := Y) rfl determines_one]
  rfl

/-- **`PB` answers `{two, two, one}`.** -/
theorem pb_answers : Config.answers (D := D) finalB = {{twoC}, {twoC}, {oneC}} := by
  show Config.answers (D := D) ⟨W1, Y2 ::ₘ Y2 ::ₘ {Y}⟩ = _
  rw [answers_cons_finished (D := D) ⟨rfl, _, rfl⟩ live_ff, answers_cons_finished (D := D) ⟨rfl, _, rfl⟩ live_ff,
    answers_singleton (D := D) ⟨rfl, _, rfl⟩ live_ff,
    answer_of_determines (D := D) (b := Y2) rfl determines_two,
    answer_of_determines (D := D) (b := Y) rfl determines_one]
  rfl

theorem one_ne_two : ({oneC} : Set MClosed) ≠ {twoC} := by
  intro same
  have terms : oneC = twoC := Set.singleton_eq_singleton_iff.mp same
  simp [oneC, twoC, csym] at terms

/-- **The two bags differ.** -/
theorem bags_differ : Config.answers (D := D) finalA ≠ Config.answers (D := D) finalB := by
  rw [pa_answers, pb_answers]
  intro same
  have counts := congrArg (Multiset.count ({oneC} : Set MClosed)) same
  simp [Multiset.count_cons, one_ne_two.symm] at counts

/-- **`PA` fails the hypothesis `distinct` of the bag theorem**: two of its equations have one
schema. -/
theorem pa_not_distinct : ¬ (PA.equations.map (schema N)).Nodup := by
  intro nodup
  have pair : (schema N e1 :: schema N e1' :: [schema N e2]).Nodup := nodup
  exact (List.nodup_cons.mp pair).1 (List.mem_cons_self)

/-- **So does `PB`.** -/
theorem pb_not_distinct : ¬ (PB.equations.map (schema N)).Nodup := by
  intro nodup
  have pair : (schema N e1 :: schema N e2' :: [schema N e2]).Nodup := nodup
  exact (List.nodup_cons.mp (List.nodup_cons.mp pair).2).1 (List.mem_singleton_self _)

/-- The configuration `PA`'s run ends in has no live alternative that can move. -/
theorem pa_quiet : finalA.Quiescent (D := D) PA supply := by
  intro b member _ w' bs
  have cases : b = Y2 ∨ b = Y ∨ b = Y := by simpa [finalA] using member
  rcases cases with rfl | rfl | rfl <;> exact Move.value_still

/-- **`PA` and its run meet every other hypothesis of the bag theorem**: the first fragment, a query
whose names are unopened, and a run that ends. -/
theorem pa_meets_the_rest :
    PlainProgram PA ∧ PlainComp q ∧ (∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) ∧
      Runs D PA supply (Config.initial sp q) finalA ∧ finalA.Quiescent (D := D) PA supply := by
  refine ⟨?_, trivial, q_unopened, pa_runs, pa_quiet⟩
  intro e member
  have member' : e ∈ [e1, e1', e2] := member
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member'
  rcases member' with rfl | rfl | rfl <;> trivial

#print axioms same_rules
#print axioms same_start
#print axioms same_step
#print axioms same_step_answers
#print axioms pa_runs
#print axioms pb_runs
#print axioms pa_answers
#print axioms pb_answers
#print axioms bags_differ
#print axioms pa_not_distinct
#print axioms pb_not_distinct
#print axioms pa_quiet
#print axioms pa_meets_the_rest

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Answers.SameStart
