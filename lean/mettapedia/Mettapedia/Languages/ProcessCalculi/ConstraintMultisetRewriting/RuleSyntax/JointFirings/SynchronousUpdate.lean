import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Independent
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Clashes

/-!
# What a bag adds to the step of the program: a synchronous update, and nothing in between

## The none query judged at the entry state (`Synchronous`)

Two rules over ground rows: `addUnless 1 2` makes a `1` unless a `2` is present; `addUnless 2 1` makes a `2`
unless a `1` is present. From the empty state:

* **the bag of one match of each is admitted** (`both_admitted`), both none checks read at the entry
  state, and its result holds a `1` and a `2` (`both_result`); it is one step of the bag step
  (`bag_reaches`);
* **no run of the step of the program reaches a state holding a `1` and a `2`** (`no_run_reaches`):
  every firing of either rule checks that the other kind is not present and adds only its own kind
  (`addUnless_step`), so along every run at most one kind is present (`reachable_one_kind`).

So the bag's result is reached by no order of its members, nor by any other run: the foundation's form of
the synchronous update of `OccurrenceCommits.Waves` (`Controls.every_synchronous_update`). Members with
none checks are where `OneAfterAnother.peel` needs positive rules.

## Nothing comes between the members (`Between`)

Two tokens and the rule that takes a token and makes a spent row; beside them, a neighbour rule `peek`
that reads a token and a spent row together. The bag of the two takes (`spend`) is admitted and is a run
of its members (`spend_run`). The neighbour cannot fire at the entry state (`peek_not_at_entry`) nor at
the bag's result (`peek_not_after`), and it can fire at the state between the two members, in either
order (`peek_between_first`, `peek_between_second`). So an observer tells the one bag step from every
run of its members: the foundation's form of `StoreInteraction.AtomicObservation`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open OneFrame (Terms frames ext)

namespace Synchronous

open Mettapedia.Logic.LP
open Examples (Tm X E c)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- **Make a `p` unless a `q` is present.** -/
def addUnless (p q : ℕ) : Rule Tm := ⟨PUnit.unit, ⟨[], [], [], [.predicate .none (c q)], [c p]⟩, []⟩

/-- **The program**: make a `1` unless a `2` is present; make a `2` unless a `1` is present. -/
def program : Program Tm := {addUnless 1 2, addUnless 2 1}

/-- The empty state. -/
def empty : State Tm ℕ := ⟨PUnit.unit, [], ∅, fun _ => c 0⟩

theorem addUnless_ground (p q : ℕ) : ∀ t ∈ (addUnless p q).terms, ∀ σ : Subst atoms, action.apply σ t = t := by
  intro t member σ
  have listed : t ∈ [c q, c p] := by simpa [addUnless, Rule.terms, checkTerms] using member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl <;> rfl

/-- **A firing of `addUnless p q`**, at a state with no knowledge: no present row is a `q`, the result knows
nothing, and every row of the result is the new `p` or an old row with its old label. -/
theorem addUnless_step {p q : ℕ} {s : State Tm ℕ} (known : s.knowledge = [])
    {g : Firing ℕ E program PUnit.unit} (isRule : g.rule = addUnless p q) (admitted : g.Admits X s) :
    (∀ o ∈ s.present, s.label o ≠ c q) ∧ (g.result X s).knowledge = [] ∧
      ∀ o ∈ (g.result X s).present,
        (g.result X s).label o = c p ∨ (o ∈ s.present ∧ (g.result X s).label o = s.label o) := by
  obtain ⟨rule, member, ext, opening, ⟨taken, read, made⟩, seen⟩ := g
  dsimp only at isRule
  subst isRule
  obtain ⟨⟨-, -, -, takeLength, readLength, produceLength, -⟩, -, -, asks⟩ := admitted
  have noTake : taken = [] := List.length_eq_zero_iff.mp (show taken.length = 0 from takeLength.symm)
  have noRead : read = [] := List.length_eq_zero_iff.mp (show read.length = 0 from readLength.symm)
  obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp (show made.length = 1 from produceLength.symm)
  subst noTake noRead
  have info : Firing.information X s
      (⟨addUnless p q, member, ext, opening, ⟨[], [], [n]⟩, seen⟩ : Firing ℕ E program PUnit.unit) = [] := by
    unfold Firing.information
    rw [known]
    rfl
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) (Subst.id atoms)
      (Firing.information X s
        (⟨addUnless p q, member, ext, opening, ⟨[], [], [n]⟩, seen⟩ : Firing ℕ E program PUnit.unit)) := by
    rw [info]
    intro e inside
    exact absurd inside List.not_mem_nil
  refine ⟨fun o present same => ?_, info, fun o inside => ?_⟩
  · have holds := (asks PUnit.unit (Subst.id atoms) solved).1 (.predicate .none (c q)) (List.mem_singleton_self _)
      o present
    apply holds
    show Subst.applyTerm (Subst.id atoms) (c q) =
      Subst.applyTerm (Subst.id atoms) (Subst.applyTerm (Subst.id atoms) (s.label o))
    rw [same]
    rfl
  · have labelled : ∀ o', (Firing.result X s
        (⟨addUnless p q, member, ext, opening, ⟨[], [], [n]⟩, seen⟩ : Firing ℕ E program PUnit.unit)).label o' =
        if o' = n then c p else s.label o' := by
      intro o'
      show relabel (fun o'' => Subst.applyTerm (Subst.id atoms) (s.label o'')) [n] [c p] o' = _
      by_cases same : o' = n
      · simp only [relabel, if_pos same]
      · simp only [relabel, if_neg same]
        exact action.apply_identity _
    rw [labelled o]
    by_cases same : o = n
    · exact Or.inl (if_pos same)
    · refine Or.inr ⟨?_, if_neg same⟩
      rcases mem_fire.mp inside with ⟨inS, -⟩ | isMade
      · exact inS
      · exact absurd (List.mem_singleton.mp (List.mem_toFinset.mp isMade)) same

/-- **Along every run from the empty state at most one kind is present**, nothing is known, and every
present row is a `1` or a `2`. -/
theorem reachable_one_kind {s' : State Tm ℕ}
    (reach : Relation.ReflTransGen (Succ (step X ℕ E program).toStep) empty s') :
    s'.knowledge = [] ∧ (∀ o ∈ s'.present, s'.label o = c 1 ∨ s'.label o = c 2) ∧
      ¬ ((∃ o ∈ s'.present, s'.label o = c 1) ∧ ∃ o ∈ s'.present, s'.label o = c 2) := by
  induction reach with
  | refl =>
      refine ⟨rfl, fun o inside => absurd inside (Finset.notMem_empty o), ?_⟩
      rintro ⟨⟨o, inside, -⟩, -⟩
      exact absurd inside (Finset.notMem_empty o)
  | tail _ step' earlier =>
      obtain ⟨known, kinds, -⟩ := earlier
      obtain ⟨g, admitted, rfl⟩ := step'
      rw [result_eq g admitted]
      have different : (c 1 : Term atoms) ≠ c 2 := fun same => absurd (Term.const.inj same) (by decide)
      rcases g.member with isRule | isRule
      · obtain ⟨none, known', rows⟩ := addUnless_step known isRule admitted
        refine ⟨known', fun o inside => ?_, ?_⟩
        · rcases rows o inside with one | ⟨old, same⟩
          · exact Or.inl one
          · rw [same]
            exact kinds o old
        · rintro ⟨-, o, inside, isTwo⟩
          rcases rows o inside with one | ⟨old, same⟩
          · exact different (one.symm.trans isTwo)
          · exact none o old (same.symm.trans isTwo)
      · have isRule' : g.rule = addUnless 2 1 := isRule
        obtain ⟨none, known', rows⟩ := addUnless_step known isRule' admitted
        refine ⟨known', fun o inside => ?_, ?_⟩
        · rcases rows o inside with two | ⟨old, same⟩
          · exact Or.inr two
          · rw [same]
            exact kinds o old
        · rintro ⟨⟨o, inside, isOne⟩, -⟩
          rcases rows o inside with two | ⟨old, same⟩
          · exact different (isOne.symm.trans two)
          · exact none o old (same.symm.trans isOne)

/-- Make a `1` as identity `10`. -/
def makeOne : OneMember action ℕ program := ⟨addUnless 1 2, Or.inl rfl, Subst.id atoms, ⟨[], [], [10]⟩, []⟩

/-- Make a `2` as identity `11`. -/
def makeTwo : OneMember action ℕ program := ⟨addUnless 2 1, Or.inr rfl, Subst.id atoms, ⟨[], [], [11]⟩, []⟩

/-- **The bag of the two.** -/
def both : Bag ℕ E program PUnit.unit := bagOf action [makeOne, makeTwo]

theorem both_members {m : OneMember action ℕ program} (inside : m ∈ both.members) :
    m = makeOne ∨ m = makeTwo := by
  have listed : m ∈ [makeOne, makeTwo] := inside
  rcases List.mem_cons.mp listed with first | rest
  · exact Or.inl first
  · exact Or.inr (List.mem_singleton.mp rest)

/-- **The bag is admitted at the empty state**, each none read there. -/
theorem both_admitted : Bag.AdmitsOwn X empty both := by
  refine ⟨⟨fresh_of_ground_bag action empty _ fun m inside => ?_, by decide, by decide,
      fun m inside => ?_⟩, ⟨by decide, by decide, by decide, by decide,
        fun q member => by simp [Selection.commit] at member⟩,
      ⟨PUnit.unit, Subst.id atoms, fun e inside => ?_⟩, fun m inside b σ _ => ⟨fun check member => ?_,
        fun q member => ?_⟩⟩
  · rcases both_members inside with rfl | rfl
    · exact addUnless_ground 1 2
    · exact addUnless_ground 2 1
  · rcases both_members inside with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · have none : Bag.information X empty both = [] := rfl
    rw [none] at inside
    exact absurd inside List.not_mem_nil
  · rcases both_members inside with rfl | rfl <;>
    · rw [List.mem_singleton.mp member]
      intro o present
      exact absurd present (Finset.notMem_empty o)
  · rcases both_members inside with rfl | rfl <;> exact absurd member List.not_mem_nil

/-- **Its result holds a `1` and a `2`.** -/
theorem both_result : (Bag.result X empty both).present = {10, 11} ∧
    (Bag.result X empty both).label 10 = c 1 ∧ (Bag.result X empty both).label 11 = c 2 :=
  ⟨by decide, rfl, rfl⟩

/-- **It is one step of the bag step.** -/
theorem bag_reaches : Succ (bagStep X ℕ E program).toStep empty (Bag.result X empty both) :=
  ⟨both, ⟨List.cons_ne_nil _ _, Bag.admits_of_admitsOwn X both_admitted⟩, rfl⟩

/-- **No run of the step of the program reaches it**, nor any state holding a `1` and a `2`. -/
theorem no_run_reaches :
    ¬ Relation.ReflTransGen (Succ (step X ℕ E program).toStep) empty (Bag.result X empty both) :=
  fun reach => (reachable_one_kind reach).2.2
    ⟨⟨10, by decide, both_result.2.1⟩, ⟨11, by decide, both_result.2.2⟩⟩

end Synchronous

namespace Between

open Mettapedia.Logic.LP
open Examples (Tm X E c)
open EveryControls (consume_ground twoTokens)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- **The neighbour**: read a token `1` and a spent row `2` together, make a `5`. -/
def peek : Rule Tm := ⟨PUnit.unit, ⟨[], [c 1, c 2], [], [], [c 5]⟩, []⟩

/-- **The program**: spend a token; the neighbour. -/
def watched : Program Tm := {Examples.consume, peek}

/-- Spend the token at `o`, make `n`. -/
def spendAt (o n : ℕ) : OneMember action ℕ watched :=
  ⟨Examples.consume, Or.inl rfl, Subst.id atoms, ⟨[o], [], [n]⟩, []⟩

/-- **The bag of the two spends.** -/
def spend : Bag ℕ E watched PUnit.unit := bagOf action [spendAt 0 10, spendAt 1 11]

theorem peek_ground : ∀ t ∈ peek.terms, ∀ σ : Subst atoms, action.apply σ t = t := by
  intro t member σ
  have listed : t ∈ [c 1, c 2, c 5] := member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl <;> rfl

theorem spend_members {m : OneMember action ℕ watched} (inside : m ∈ spend.members) :
    m = spendAt 0 10 ∨ m = spendAt 1 11 := by
  have listed : m ∈ [spendAt 0 10, spendAt 1 11] := inside
  rcases List.mem_cons.mp listed with first | rest
  · exact Or.inl first
  · exact Or.inr (List.mem_singleton.mp rest)

theorem spend_admitted : Bag.AdmitsOwn X twoTokens spend := by
  refine ⟨⟨fresh_of_ground_bag action twoTokens _ fun m inside => ?_, by decide, by decide,
      fun m inside => ?_⟩, ⟨by decide, by decide, by decide, by decide,
        fun q member => by simp [Selection.commit] at member⟩,
      ⟨PUnit.unit, Subst.id atoms, Shop.solves_identical fun e member => ?_⟩,
      fun m inside b σ _ => ?_⟩
  · rcases spend_members inside with rfl | rfl <;> exact consume_ground
  · rcases spend_members inside with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · have listed : e ∈ [(c 1, c 1), (c 1, c 1)] := member
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at listed
    rw [listed]
  · rcases spend_members inside with rfl | rfl <;>
      exact ⟨fun check member => absurd member List.not_mem_nil,
        fun q member => absurd member List.not_mem_nil⟩

/-- **The bag of the two spends is a run of its members.** -/
theorem spend_run :
    Relation.ReflTransGen (Succ (step X ℕ E watched).toStep) twoTokens (Bag.result X twoTokens spend) :=
  run_of_admitsOwn action [spendAt 0 10, spendAt 1 11] twoTokens
    (fun r inside => by
      rcases spend_members inside with rfl | rfl <;>
        exact ⟨fun c member => absurd member List.not_mem_nil, rfl⟩)
    spend_admitted

/-- **The neighbour needs a token and a spent row**: at a state whose present rows carry constants, an
admitted firing of `peek` reads a row labelled `1` and a row labelled `2`. -/
theorem peek_needs {s : State Tm ℕ} (constants : ∀ o ∈ s.present, ∃ k, s.label o = c k)
    {g : Firing ℕ E watched PUnit.unit} (isPeek : g.rule = peek) (admitted : g.Admits X s) :
    (∃ o ∈ s.present, s.label o = c 1) ∧ ∃ o ∈ s.present, s.label o = c 2 := by
  obtain ⟨rule, member, ext, opening, ⟨taken, read, made⟩, seen⟩ := g
  dsimp only at isPeek
  subst isPeek
  obtain ⟨⟨-, -, -, -, readLength, -, -⟩, enabled, ⟨_, σ, solved⟩, -⟩ := admitted
  obtain ⟨o₁, o₂, rfl⟩ := List.length_eq_two.mp (show read.length = 2 from readLength.symm)
  have present₁ : o₁ ∈ s.present := enabled.kept_subset (List.mem_toFinset.mpr List.mem_cons_self)
  have present₂ : o₂ ∈ s.present :=
    enabled.kept_subset (List.mem_toFinset.mpr (List.mem_cons_of_mem _ List.mem_cons_self))
  have readOf : ∀ (o : ℕ) (k : ℕ), o ∈ s.present →
      Subst.applyTerm σ (c k) = Subst.applyTerm σ (Subst.applyTerm (Subst.id atoms) (s.label o)) →
      s.label o = c k := by
    intro o k present same
    obtain ⟨k', labelled⟩ := constants o present
    rw [labelled] at same ⊢
    have equal : (Term.const k : Term atoms) = Term.const k' := same
    rw [Term.const.inj equal]
  have first : Subst.applyTerm σ (c 1) =
      Subst.applyTerm σ (Subst.applyTerm (Subst.id atoms) (s.label o₁)) :=
    solved (c 1, Subst.applyTerm (Subst.id atoms) (s.label o₁))
      (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
  have second : Subst.applyTerm σ (c 2) =
      Subst.applyTerm σ (Subst.applyTerm (Subst.id atoms) (s.label o₂)) :=
    solved (c 2, Subst.applyTerm (Subst.id atoms) (s.label o₂))
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  exact ⟨⟨o₁, present₁, readOf o₁ 1 present₁ first⟩, ⟨o₂, present₂, readOf o₂ 2 present₂ second⟩⟩

/-- **The neighbour cannot fire at the entry state**: no spent row. -/
theorem peek_not_at_entry (g : Firing ℕ E watched PUnit.unit) (isPeek : g.rule = peek) :
    ¬ g.Admits X twoTokens := fun admitted => by
  obtain ⟨-, o, -, two⟩ := peek_needs (fun _ _ => ⟨1, rfl⟩) isPeek admitted
  exact absurd (Term.const.inj two) (by decide)

/-- The labels of the bag's result. -/
theorem spend_labels : ∀ o ∈ (Bag.result X twoTokens spend).present,
    (Bag.result X twoTokens spend).label o = c 2 := by
  intro o inside
  have rows : (Bag.result X twoTokens spend).present = {10, 11} := by decide
  rw [rows] at inside
  rcases Finset.mem_insert.mp inside with rfl | rest
  · rfl
  · rw [Finset.mem_singleton.mp rest]
    rfl

/-- **The neighbour cannot fire at the bag's result**: no token. -/
theorem peek_not_after (g : Firing ℕ E watched PUnit.unit) (isPeek : g.rule = peek) :
    ¬ g.Admits X (Bag.result X twoTokens spend) := fun admitted => by
  obtain ⟨⟨o, inside, one⟩, -⟩ := peek_needs
    (fun o inside => ⟨2, spend_labels o inside⟩) isPeek admitted
  rw [spend_labels o inside] at one
  exact absurd (Term.const.inj one) (by decide)

/-- Peek at a token at `o₁` and a spent row at `o₂`. -/
def peekAt (o₁ o₂ : ℕ) : Firing ℕ E watched PUnit.unit :=
  ⟨peek, Or.inr rfl, PUnit.unit, Subst.id atoms, ⟨[], [o₁, o₂], [20]⟩, []⟩

/-- **Between the two spends, in the order first then second, the neighbour fires.** -/
theorem peek_between_first :
    (spendAt 0 10).firing.Admits X twoTokens ∧
      (peekAt 1 10).Admits X ((spendAt 0 10).firing.result X twoTokens) := by
  refine ⟨Bag.admits_member X (fun _ _ => ⟨Subst.id atoms⟩) spend_admitted List.mem_cons_self, ?_⟩
  refine ⟨⟨Examples.fresh_of_ground action _ (peekAt 1 10) peek_ground, List.nodup_nil,
    List.nodup_singleton 20, rfl, rfl, rfl, rfl⟩, ⟨by decide, by decide, by decide, by decide,
      fun q member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, Subst.id atoms, Shop.solves_identical fun e member => ?_⟩,
    fun _ _ _ => ⟨fun check member => absurd member List.not_mem_nil,
      fun q member => absurd member List.not_mem_nil⟩⟩
  have listed : e ∈ [(c 1, c 1), (c 1, c 1), (c 2, c 2)] := member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl <;> rfl

/-- **Between the two spends, in the order second then first, the neighbour fires.** -/
theorem peek_between_second :
    (spendAt 1 11).firing.Admits X twoTokens ∧
      (peekAt 0 11).Admits X ((spendAt 1 11).firing.result X twoTokens) := by
  refine ⟨Bag.admits_member X (fun _ _ => ⟨Subst.id atoms⟩) spend_admitted
    (List.mem_cons_of_mem _ List.mem_cons_self), ?_⟩
  refine ⟨⟨Examples.fresh_of_ground action _ (peekAt 0 11) peek_ground, List.nodup_nil,
    List.nodup_singleton 20, rfl, rfl, rfl, rfl⟩, ⟨by decide, by decide, by decide, by decide,
      fun q member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, Subst.id atoms, Shop.solves_identical fun e member => ?_⟩,
    fun _ _ _ => ⟨fun check member => absurd member List.not_mem_nil,
      fun q member => absurd member List.not_mem_nil⟩⟩
  have listed : e ∈ [(c 1, c 1), (c 1, c 1), (c 2, c 2)] := member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl <;> rfl

end Between

#print axioms Synchronous.addUnless_step
#print axioms Synchronous.reachable_one_kind
#print axioms Synchronous.both_admitted
#print axioms Synchronous.both_result
#print axioms Synchronous.bag_reaches
#print axioms Synchronous.no_run_reaches
#print axioms Between.spend_admitted
#print axioms Between.spend_run
#print axioms Between.peek_needs
#print axioms Between.peek_not_at_entry
#print axioms Between.peek_not_after
#print axioms Between.peek_between_first
#print axioms Between.peek_between_second

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
