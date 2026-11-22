import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.StaticControls

/-!
# When two programs are equivalent at every state: mutual answering of firings

## Every frame action, every barb family (`AnswersUpTo`)

`AnswersUpTo P P'`: at every state, every admitted firing of `P` has an admitted firing of `P'` at the
same state whose result is congruent to its result, both under `P`.

* **`programs_iff_answersUpTo`**: `P` and `P'` are congruent at every state exactly when each answers
  the other up to the congruence. The direction from answering is `congruent_of_answersUpTo`, which also
  gives congruence beside every further program `Q`; the converse is one step of the bisimulation game
  followed by the hypothesis at the answer's result.

This is exact and general, and it still mentions the congruence (of states under one program).

## One frame: explicitly, by the static equivalence (`AnswersStatic`)

`AnswersStatic P P'`: every admitted firing of `P` at every state has an admitted firing of `P'` at
the same state whose result is statically equivalent (`Static`) to its result.

* **A sound proof method for every pair of programs** (`congruent_of_answersStatic`): mutual static
  answering gives congruence at every state, beside every program.
* **Exact for programs that leave a constant unused** (`programs_iff`): for bounded `P`, `P'`
  (finite programs are), congruence at every state is exactly mutual static answering. Absence and
  count queries are allowed in `P` and `P'`: positivity is not needed. The proof is `static_of_congruent`
  applied to the results of a firing and its answer.
* **Per state** (`answers_of_congruent`): congruent systems with bounded programs answer each other's
  firings with statically equivalent results; with the congruence closed under contexts
  (`Congruent.applyAll_same`), this is the necessary condition used to separate programs at one state:
  find a context and a firing of the one side at the state it reaches that the other side cannot answer
  statically.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uO uT uH uE uOcc uB

/-! ## Every frame action -/

section General

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {B : Type uB} {obs : B → State Tm O → Prop}

variable (X O E obs) in
/-- **One program answers another up to the congruence**: at every state, every admitted firing of
`P` has an admitted firing of `P'` whose result is congruent to its result under `P`. -/
def AnswersUpTo (P P' : Program Tm) : Prop :=
  ∀ (s : State Tm O) (f : Firing O E P s.frame), f.Admits X s →
    ∃ g : Firing O E P' s.frame, g.Admits X s ∧
      Congruent X O E obs ⟨P, f.result X s⟩ ⟨P, g.result X s⟩

/-- **Mutual answering up to the congruence gives congruence**, at every state and beside every
program. -/
theorem congruent_of_answersUpTo {P P' : Program Tm} (forward : AnswersUpTo X O E obs P P')
    (backward : AnswersUpTo X O E obs P' P) (Q : Program Tm) (s : State Tm O) :
    Congruent X O E obs ⟨P ∪ Q, s⟩ ⟨P' ∪ Q, s⟩ := by
  let R : System Tm O → System Tm O → Prop := fun S T => S.state = T.state ∧ ∃ Q : Program Tm,
    (S.program = P ∪ Q ∧ T.program = P' ∪ Q) ∨ (S.program = P' ∪ Q ∧ T.program = P ∪ Q)
  refine congruent_of_upTo (R := R) ?_ ?_ ?_ ?_ ⟨rfl, Q, .inl ⟨rfl, rfl⟩⟩
  · rintro S T ⟨same, Q, orient⟩
    refine ⟨same.symm, Q, ?_⟩
    rcases orient with ⟨left, right⟩ | ⟨left, right⟩
    · exact .inr ⟨right, left⟩
    · exact .inl ⟨right, left⟩
  · rintro S T ⟨same, -⟩ β holds
    rw [← same]
    exact holds
  · rintro ⟨SP, Ss⟩ ⟨TP, Ts⟩ ⟨same, Q, orient⟩ ⟨S'P, S's⟩ ⟨programSame, f, admitted, reached⟩
    simp only at same programSame
    subst same programSame
    have reached' : f.result X Ss = S's := reached
    subst reached'
    rcases orient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases (Set.mem_union _ _ _).mp f.member with inP | inQ
      · obtain ⟨g, admittedG, related⟩ := forward Ss (reprogram f inP) admitted
        exact ⟨⟨P' ∪ Q, g.result X Ss⟩, reduces_of_admits (reprogram g (Or.inl g.member)) admittedG,
          ⟨P ∪ Q, g.result X Ss⟩, ⟨P' ∪ Q, g.result X Ss⟩, related.addRules Q,
          ⟨rfl, Q, .inl ⟨rfl, rfl⟩⟩, Congruent.refl _⟩
      · exact ⟨⟨P' ∪ Q, f.result X Ss⟩, reduces_of_admits (reprogram f (Or.inr inQ)) admitted,
          ⟨P ∪ Q, f.result X Ss⟩, ⟨P' ∪ Q, f.result X Ss⟩, Congruent.refl _,
          ⟨rfl, Q, .inl ⟨rfl, rfl⟩⟩, Congruent.refl _⟩
    · rcases (Set.mem_union _ _ _).mp f.member with inP' | inQ
      · obtain ⟨g, admittedG, related⟩ := backward Ss (reprogram f inP') admitted
        exact ⟨⟨P ∪ Q, g.result X Ss⟩, reduces_of_admits (reprogram g (Or.inl g.member)) admittedG,
          ⟨P' ∪ Q, g.result X Ss⟩, ⟨P ∪ Q, g.result X Ss⟩, related.addRules Q,
          ⟨rfl, Q, .inr ⟨rfl, rfl⟩⟩, Congruent.refl _⟩
      · exact ⟨⟨P ∪ Q, f.result X Ss⟩, reduces_of_admits (reprogram f (Or.inr inQ)) admitted,
          ⟨P' ∪ Q, f.result X Ss⟩, ⟨P ∪ Q, f.result X Ss⟩, Congruent.refl _,
          ⟨rfl, Q, .inr ⟨rfl, rfl⟩⟩, Congruent.refl _⟩
  · rintro ⟨SP, Ss⟩ ⟨TP, Ts⟩ ⟨same, Q, orient⟩ c applies
    simp only at same
    subst same
    refine ⟨1, by rw [Basic.rename_one]; exact applies, ?_⟩
    rw [Basic.rename_one]
    cases c with
    | rows ids label => exact ⟨rfl, Q, orient⟩
    | rules added =>
        refine ⟨rfl, Q ∪ added, ?_⟩
        rcases orient with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .inl ⟨Set.union_assoc _ _ _, Set.union_assoc _ _ _⟩
        · exact .inr ⟨Set.union_assoc _ _ _, Set.union_assoc _ _ _⟩
    | tell equations => exact ⟨rfl, Q, orient⟩
    | extend extension => exact ⟨rfl, Q, orient⟩

/-- **Congruence at every state gives answering up to the congruence.** -/
theorem answersUpTo_of_congruent {P P' : Program Tm}
    (related : ∀ s : State Tm O, Congruent X O E obs ⟨P, s⟩ ⟨P', s⟩) :
    AnswersUpTo X O E obs P P' := by
  intro s f admitted
  obtain ⟨T', moved, results⟩ := candidate_congruent.reduces (related s) (reduces_of_admits f admitted)
  obtain ⟨program, g, admittedG, reached⟩ := moved
  have reached' : g.result X s = T'.state := reached
  obtain ⟨TP, Ts⟩ := T'
  simp only at program reached'
  subst program reached'
  exact ⟨g, admittedG, results.trans (related (g.result X s)).symm⟩

/-- **Two programs are congruent at every state exactly when each answers the other up to the
congruence**, for every frame action and barb family. -/
theorem programs_iff_answersUpTo {P P' : Program Tm} :
    (∀ s : State Tm O, Congruent X O E obs ⟨P, s⟩ ⟨P', s⟩) ↔
      AnswersUpTo X O E obs P P' ∧ AnswersUpTo X O E obs P' P := by
  constructor
  · intro related
    exact ⟨answersUpTo_of_congruent related, answersUpTo_of_congruent fun s => (related s).symm⟩
  · rintro ⟨forward, backward⟩ s
    have both := congruent_of_answersUpTo forward backward ∅ s
    rw [Set.union_empty, Set.union_empty] at both
    exact both

end General

/-! ## One frame: by the static equivalence -/

section OneFrame

open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c)
open RuleSyntax.Controls (atoms action)
open AtOneFrame (Sys Cong)

/-- **One program answers another statically**: every admitted firing of `P` at every state has an
admitted firing of `P'` at the same state whose result is statically equivalent to its result. -/
def AnswersStatic (P P' : Program Tm) : Prop :=
  ∀ (s : State Tm ℕ) (f : Firing ℕ E P s.frame), f.Admits X s →
    ∃ g : Firing ℕ E P' s.frame, g.Admits X s ∧ Static (f.result X s) (g.result X s)

theorem answersUpTo_of_answersStatic {P P' : Program Tm} (answers : AnswersStatic P P') :
    AnswersUpTo X ℕ E (MayBarb X) P P' := fun s f admitted =>
  let ⟨g, admittedG, static⟩ := answers s f admitted
  ⟨g, admittedG, congruent_of_static P static⟩

theorem answersStatic_of_answersUpTo {P P' : Program Tm} (bounded : Bounded P)
    (answers : AnswersUpTo X ℕ E (MayBarb X) P P') : AnswersStatic P P' := fun s f admitted =>
  let ⟨g, admittedG, related⟩ := answers s f admitted
  ⟨g, admittedG, static_of_congruent bounded bounded related⟩

/-- **A sound proof method for every pair of programs**: mutual static answering gives congruence at
every state, beside every program. -/
theorem congruent_of_answersStatic {P P' : Program Tm} (forward : AnswersStatic P P')
    (backward : AnswersStatic P' P) (Q : Program Tm) (s : State Tm ℕ) : Cong ⟨P ∪ Q, s⟩ ⟨P' ∪ Q, s⟩ :=
  congruent_of_answersUpTo (answersUpTo_of_answersStatic forward)
    (answersUpTo_of_answersStatic backward) Q s

/-- **The equivalence of programs, explicitly**: for programs that leave a constant unused, congruence
at every state is exactly mutual static answering of firings. -/
theorem programs_iff {P P' : Program Tm} (boundP : Bounded P) (boundP' : Bounded P') :
    (∀ s : State Tm ℕ, Cong ⟨P, s⟩ ⟨P', s⟩) ↔ AnswersStatic P P' ∧ AnswersStatic P' P := by
  rw [programs_iff_answersUpTo]
  exact ⟨fun ⟨forward, backward⟩ => ⟨answersStatic_of_answersUpTo boundP forward,
      answersStatic_of_answersUpTo boundP' backward⟩,
    fun ⟨forward, backward⟩ => ⟨answersUpTo_of_answersStatic forward,
      answersUpTo_of_answersStatic backward⟩⟩

/-- **Per state**: congruent systems with bounded programs answer each other's firings with
statically equivalent results. -/
theorem answers_of_congruent {P P' : Program Tm} (boundP : Bounded P) (boundP' : Bounded P')
    {s t : State Tm ℕ} (related : Cong ⟨P, s⟩ ⟨P', t⟩) (f : Firing ℕ E P s.frame)
    (admitted : f.Admits X s) :
    ∃ g : Firing ℕ E P' t.frame, g.Admits X t ∧ Static (f.result X s) (g.result X t) := by
  obtain ⟨T', moved, results⟩ := candidate_congruent.reduces related (reduces_of_admits f admitted)
  obtain ⟨program, g, admittedG, reached⟩ := moved
  have reached' : g.result X t = T'.state := reached
  obtain ⟨TP, Ts⟩ := T'
  simp only at program reached'
  subst program reached'
  exact ⟨g, admittedG, static_of_congruent boundP boundP' results⟩

/-- **Congruence of systems reduces to congruence of programs at one state**: beside bounded
programs, `⟨P, s⟩` and `⟨P', t⟩` are congruent exactly when `s` and `t` are statically equivalent and
`⟨P, s⟩` and `⟨P', s⟩` are congruent. -/
theorem congruent_iff_static_and_same {P P' : Program Tm} (boundP : Bounded P)
    (boundP' : Bounded P') (s t : State Tm ℕ) :
    Cong ⟨P, s⟩ ⟨P', t⟩ ↔ Static s t ∧ Cong ⟨P, s⟩ ⟨P', s⟩ := by
  constructor
  · intro related
    have static := static_of_congruent boundP boundP' related
    exact ⟨static, related.trans (congruent_of_static P' static).symm⟩
  · rintro ⟨static, related⟩
    exact related.trans (congruent_of_static P' static)

end OneFrame

#print axioms congruent_of_answersUpTo
#print axioms answersUpTo_of_congruent
#print axioms programs_iff_answersUpTo
#print axioms answersUpTo_of_answersStatic
#print axioms answersStatic_of_answersUpTo
#print axioms congruent_of_answersStatic
#print axioms programs_iff
#print axioms answers_of_congruent
#print axioms congruent_iff_static_and_same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization
