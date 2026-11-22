import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Congruence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.DependentEq
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleInstanceSets

/-!
# The step of a program is the least step of its rules

A firing of the step of a program uses one rule. So the step of a program is assembled from the steps of its
rules, and from nothing else. For every frame action, every type of identities and every extension:

* **Monotone in the program** (`firing_mono`, `succ_mono`): a firing of `P` is a firing of every larger
  program, admitted exactly when it was, with the same result. This is `Equivalence.reprogram` with
  `Equivalence.admits_reprogram` and `Equivalence.result_reprogram`.
* **The firings of a program are the firings of its rules, one rule at a time** (`firingsByRule`): an
  equivalence between the firings of `P` at a frame and the pairs of a rule of `P` and a firing of the program
  of that one rule; it keeps admission and results (`firingsByRule_admits`, `firingsByRule_result`).
* **The step of a union is the union of the steps** (`succ_union`): on transition relations.
* **The step of the empty program has no transition** (`succ_empty`).
* **The union over the rules** (`succ_iff_rule`): the transition relation of the step of `P` is the union over
  the rules of `P` of the transition relations of the steps of one rule.
* **Least** (`succ_least`): a relation on states contains the transitions of the step of `P` exactly when it
  contains the transitions of the step of each rule of `P`.

## A program is a set of rules

The union of programs is idempotent, because a program is a set: `P ∪ P = P`. So

* the step of `P ∪ P` has the transitions of the step of `P` (`succ_union_self`), and
* it has the firings of `P` and no more (`firingsUnionSelf`, an equivalence that keeps admission and results:
  `firingsUnionSelf_admits`, `firingsUnionSelf_result`).

A rule stated twice is one rule: it adds no transition and no firing. The index of `firingsByRule` is the set of
rules of the program, so these two equivalences count firings by rule; the other statements of this module are
about transition relations and count nothing.

## Upward: the program of all rules

Every program is contained in the program of all rules (`Set.univ`), and the step of `P` is the step of all
rules restricted to the firings whose rule is in `P` (`succ_iff_restrict`). The step of all rules is, through the
maps of `FirstOrderEq` and `DependentEq`, the older first-order step and the dependent full step restricted to
the firings that open some rule freshly (`firstOrder_all`, `dependent_all`: the instances of
`OneFrame.firstOrder_eq` and `Dependent.dependent_eq` at the program of all rules).

What the unrestricted older steps have beyond the step of all rules is stated in `DependentEq`: their firings
are rule instances at the state's frame, which may mention the state's own unknowns (an instance that captures a
caller's unknown is refused by the step of a program, `Examples.capture_refused`, and fires as an instance,
`OneFrame.Controls.instanceSet_captures`), and their predicate queries are arbitrary regions with arbitrary
answers.

## Controls

* The union is not empty: the token firing is a transition of the demonstration program and of the program of
  its one rule (`Controls.consume_of_rule`).
* Monotonicity needs the inclusion: that transition is not a transition of the program of another rule
  (`Controls.consume_not_absent`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence (reprogram)

universe uO uT uH uE uOcc

section Generic

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {X : Frames Tm Hom}
  {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}

/-! ## Monotone in the program -/

/-- **A firing of a program is a firing of every larger program**, admitted exactly when it was, with the same
result. -/
theorem firing_mono {P Q : Program Tm} (sub : P ⊆ Q) {s : State Tm O} (f : Firing O E P s.frame) :
    ((step X O E Q).Admits (s := s) (reprogram f (sub f.member)) ↔ (step X O E P).Admits (s := s) f) ∧
      (reprogram f (sub f.member)).result X s = f.result X s :=
  ⟨Iff.rfl, rfl⟩

/-- **The step is monotone in the program**: a transition of the step of `P` is a transition of the step of
every larger program. -/
theorem succ_mono {P Q : Program Tm} (sub : P ⊆ Q) {s t : State Tm O}
    (reached : Succ (step X O E P).toStep s t) : Succ (step X O E Q).toStep s t := by
  obtain ⟨f, admitted, rfl⟩ := reached
  exact ⟨reprogram f (sub f.member), admitted, rfl⟩

/-! ## A firing uses one rule -/

/-- **The firings of a program are the firings of its rules, one rule at a time.** -/
def firingsByRule (P : Program Tm) (a : Obj) :
    Firing O E P a ≃ Σ r : {r : Rule Tm // r ∈ P}, Firing O E ({r.1} : Program Tm) a where
  toFun f := ⟨⟨f.rule, f.member⟩, reprogram f (Set.mem_singleton _)⟩
  invFun x := reprogram x.2 (by
    have same : x.2.rule = x.1.1 := Set.mem_singleton_iff.mp x.2.member
    rw [same]
    exact x.1.2)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨r, inP⟩, ⟨rule, member, ext, opening, selection, seen⟩⟩
    have same : rule = r := Set.mem_singleton_iff.mp member
    subst same
    rfl

/-- The equivalence keeps admission. -/
theorem firingsByRule_admits (P : Program Tm) {s : State Tm O} (f : Firing O E P s.frame) :
    (step X O E ({f.rule} : Program Tm)).Admits (s := s) (firingsByRule (O := O) (E := E) P s.frame f).2 ↔
      (step X O E P).Admits (s := s) f :=
  Iff.rfl

/-- The equivalence keeps results. -/
theorem firingsByRule_result (P : Program Tm) {s : State Tm O} (f : Firing O E P s.frame) :
    (firingsByRule (O := O) (E := E) P s.frame f).2.result X s = f.result X s :=
  rfl

/-! ## Unions, the empty program, and the union over the rules -/

/-- **The step of a union is the union of the steps.** -/
theorem succ_union (P Q : Program Tm) (s t : State Tm O) :
    Succ (step X O E (P ∪ Q)).toStep s t ↔
      Succ (step X O E P).toStep s t ∨ Succ (step X O E Q).toStep s t := by
  constructor
  · rintro ⟨f, admitted, rfl⟩
    rcases (Set.mem_union _ _ _).mp f.member with inP | inQ
    · exact Or.inl ⟨reprogram f inP, admitted, rfl⟩
    · exact Or.inr ⟨reprogram f inQ, admitted, rfl⟩
  · rintro (reached | reached)
    · exact succ_mono Set.subset_union_left reached
    · exact succ_mono Set.subset_union_right reached

/-- **The step of the empty program has no transition.** -/
theorem succ_empty (s t : State Tm O) : ¬ Succ (step X O E (∅ : Program Tm)).toStep s t := by
  rintro ⟨f, -, -⟩
  exact (Set.mem_empty_iff_false _).mp f.member

/-- **The transition relation of the step of a program is the union over its rules** of the transition
relations of the steps of one rule. -/
theorem succ_iff_rule (P : Program Tm) (s t : State Tm O) :
    Succ (step X O E P).toStep s t ↔ ∃ r ∈ P, Succ (step X O E ({r} : Program Tm)).toStep s t := by
  constructor
  · rintro ⟨f, admitted, rfl⟩
    exact ⟨f.rule, f.member, reprogram f (Set.mem_singleton _), admitted, rfl⟩
  · rintro ⟨r, member, reached⟩
    exact succ_mono (Set.singleton_subset_iff.mpr member) reached

/-- **Least**: a relation on states contains the transitions of the step of a program exactly when it contains
the transitions of the step of each of its rules. -/
theorem succ_least (P : Program Tm) (R : State Tm O → State Tm O → Prop) :
    (∀ s t, Succ (step X O E P).toStep s t → R s t) ↔
      ∀ r ∈ P, ∀ s t, Succ (step X O E ({r} : Program Tm)).toStep s t → R s t := by
  constructor
  · intro below r member s t reached
    exact below s t (succ_mono (Set.singleton_subset_iff.mpr member) reached)
  · intro each s t reached
    obtain ⟨r, member, single⟩ := (succ_iff_rule P s t).mp reached
    exact each r member s t single

/-! ## A program is a set of rules: a rule stated twice is one rule -/

/-- **The step of `P ∪ P` has the transitions of the step of `P`.** -/
theorem succ_union_self (P : Program Tm) (s t : State Tm O) :
    Succ (step X O E (P ∪ P)).toStep s t ↔ Succ (step X O E P).toStep s t := by
  rw [succ_union]
  exact or_self_iff

/-- **The firings of `P ∪ P` are the firings of `P`.** -/
def firingsUnionSelf (P : Program Tm) (a : Obj) : Firing O E (P ∪ P) a ≃ Firing O E P a where
  toFun f := reprogram f (((Set.mem_union _ _ _).mp f.member).elim id id)
  invFun g := reprogram g (Or.inl g.member)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The equivalence keeps admission. -/
theorem firingsUnionSelf_admits (P : Program Tm) {s : State Tm O} (f : Firing O E (P ∪ P) s.frame) :
    (step X O E P).Admits (s := s) (firingsUnionSelf (O := O) (E := E) P s.frame f) ↔
      (step X O E (P ∪ P)).Admits (s := s) f :=
  Iff.rfl

/-- The equivalence keeps results. -/
theorem firingsUnionSelf_result (P : Program Tm) {s : State Tm O} (f : Firing O E (P ∪ P) s.frame) :
    (firingsUnionSelf (O := O) (E := E) P s.frame f).result X s = f.result X s :=
  rfl

/-! ## Upward: the program of all rules -/

/-- **The step of a program is the step of all rules restricted to its rules.** -/
theorem succ_iff_restrict (P : Program Tm) (s t : State Tm O) :
    Succ (step X O E P).toStep s t ↔
      Succ (Spaces.restrict (step X O E (Set.univ : Program Tm)).toStep (fun {_s} f => f.rule ∈ P)) s t := by
  constructor
  · rintro ⟨f, admitted, rfl⟩
    exact ⟨reprogram f (Set.mem_univ _), ⟨admitted, f.member⟩, rfl⟩
  · rintro ⟨f, ⟨admitted, inP⟩, rfl⟩
    exact ⟨reprogram f inP, admitted, rfl⟩

end Generic

/-! ## The older steps restricted to fresh openings of rules are the step of all rules -/

section FirstOrder

universe u v w

variable {T : Type u} {S : Type v} (A : SubstitutionAction T S) {O : Type w} [DecidableEq O]

/-- **The first-order step restricted to the firings that open some rule freshly is the label-keeping step of
the program of all rules**, through `OneFrame.embed`: the instance of `OneFrame.firstOrder_eq` at `Set.univ`. -/
theorem firstOrder_all (label : O → T) (C C' : Configuration T O) :
    Succ (OneFrame.firstOrderOn A label Set.univ) C C' ↔
      Succ (OneFrame.keeping A Set.univ) (OneFrame.embed label C) (OneFrame.embed label C') :=
  OneFrame.firstOrder_eq C C'

end FirstOrder

section DependentFull

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

variable {Head : Type} {rules : Rules Head} {O : Type} [DecidableEq O] {L : Type} [UniverseLevel.LevelOrder L]

/-- **The dependent full step restricted to the firings that open some rule freshly is the step of the program
of all rules**, through `Dependent.toState`: the instance of `Dependent.dependent_eq` at `Set.univ`. -/
theorem dependent_all (levels : LevelModel rules L) (s s' : Interface.DependentFull.State rules O) :
    Succ (Dependent.dependentOn levels (Set.univ : Program (Dependent.Terms rules))) s s' ↔
      Succ (step (frames levels) O Dependent.helperExtensions
        (Set.univ : Program (Dependent.Terms rules))).toStep (Dependent.toState s) (Dependent.toState s') :=
  Dependent.dependent_eq s s'

end DependentFull

/-! ## Controls -/

namespace Controls

open Examples (Tm X E demo consume absentNine tokenState consumeFiring consume_admitted consume_result_present)

/-- **The union is not empty**: the token firing is a transition of the demonstration program, hence of the
program of one of its rules. -/
theorem consume_of_rule :
    ∃ t, Succ (step X ℕ E demo).toStep tokenState t ∧
      ∃ r ∈ demo, Succ (step X ℕ E ({r} : Program Tm)).toStep tokenState t :=
  ⟨consumeFiring.result X tokenState, ⟨consumeFiring, consume_admitted, rfl⟩,
    (succ_iff_rule demo _ _).mp ⟨consumeFiring, consume_admitted, rfl⟩⟩

/-- **Monotonicity needs the inclusion**: the token transition of the demonstration program is not a transition
of the program of the absence rule alone, which takes and makes nothing. -/
theorem consume_not_absent :
    ∃ t, Succ (step X ℕ E demo).toStep tokenState t ∧
      ¬ Succ (step X ℕ E ({absentNine} : Program Tm)).toStep tokenState t := by
  refine ⟨consumeFiring.result X tokenState, ⟨consumeFiring, consume_admitted, rfl⟩, ?_⟩
  rintro ⟨f, admitted, reached⟩
  have isRule : f.rule = absentNine := Set.mem_singleton_iff.mp f.member
  obtain ⟨-, ⟨-, -, takeLength, -, produceLength, -⟩, -⟩ := (admits_iff f).mp admitted
  rw [isRule] at takeLength produceLength
  have noneTaken : f.selection.taken = [] := List.eq_nil_of_length_eq_zero takeLength.symm
  have noneMade : f.selection.made = [] := List.eq_nil_of_length_eq_zero produceLength.symm
  have fired : fire tokenState.present (f.selection.commit (T := Unit)) = {0} := by
    simp [fire, Selection.commit, noneTaken, noneMade, tokenState]
  have present : fire tokenState.present (f.selection.commit (T := Unit)) = {1} :=
    (congrArg State.present reached).trans consume_result_present
  exact absurd (fired.symm.trans present) (by decide)

end Controls

#print axioms firing_mono
#print axioms succ_mono
#print axioms firingsByRule
#print axioms firingsByRule_admits
#print axioms succ_union
#print axioms succ_empty
#print axioms succ_iff_rule
#print axioms succ_least
#print axioms succ_union_self
#print axioms firingsUnionSelf
#print axioms firingsUnionSelf_admits
#print axioms succ_iff_restrict
#print axioms firstOrder_all
#print axioms dependent_all
#print axioms Controls.consume_of_rule
#print axioms Controls.consume_not_absent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation
