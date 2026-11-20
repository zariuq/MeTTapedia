import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Maximal

/-!
# Matches that want one row: three readings, and what separates them

Two matches of a bag may select one row: both take it, or one takes what the other reads. Three readings
are coherent.

* **Refuse** (`Bag.Admits`, `Bag.AdmitsOwn`): the joint selection is enabled as one commit, so the takes
  of the members are apart and no member reads what another takes. A bag of two matches that take one
  row is not admitted.
* **At the entry state, takes allowed to coincide** (`Bag.AdmitsAtEntry`): every member is admitted on
  its own at the entry state, the bag is jointly fresh, its made identities are apart, and the joint
  information is solvable with every member's guards at its solutions. A row taken by two members is
  taken once, and a member may read a row another takes. This is the reading of a store that is a set:
  removing a row twice removes it once.
* **A compatible part** (`Bag.AdmitsPart`): what is committed is a part of the bag that is admitted
  under the first reading and that no further member of the bag can join.

How they are related:

* `Bag.admitsAtEntry_of_admitsOwn`: the first reading (guards at each member's own information) implies
  the second. `Bag.admitsOwn_iff_admitsAtEntry`: it is the second with the takes apart and the joint
  selection enabled as one commit.

## The control that separates them (`Shop`)

One coin and two wants; the rule `buy` takes a coin, reads a want and makes a bought row. Its two
matches take the one coin.

* `Shop.both_refused`: the bag of the two matches is refused under the first reading.
* `Shop.both_atEntry`, `Shop.both_result`: it is admitted under the second, and its result has no coin
  and two bought rows.
* `Shop.part_first`, `Shop.part_result`, `Shop.parts_single`: a compatible part has one member, and its
  result has no coin and one bought row.

So the three readings give three different outcomes at one state (`Shop.three_readings`).

## A reader and a taker of one row (`ReadTake`)

`ReadTake.refused`: the bag of a match that reads a token and a match that takes it is refused under the
first reading. `ReadTake.atEntry`: it is admitted under the second. `ReadTake.reader_first`: its result
is reached by firing the reader first and then the taker; `ReadTake.taker_first_stops`: after the taker
the reader cannot fire. So a reader and a taker of one row run in one order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open OneFrame (Terms frames ext)

universe uO uT uH uE uOcc

/-! ## The readings -/

section Readings

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

namespace Bag

variable (X : Frames Tm Hom) {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {P : Program Tm} (s : State Tm O)

/-- **Joint admission at the entry state, takes allowed to coincide**: the bag is jointly fresh, its
made identities are apart, every member is admitted on its own at the entry state, and the joint
information is solvable with the guards of every member at every joint solution. -/
def AdmitsAtEntry (f : Bag O E P s.frame) : Prop :=
  f.Fresh X s ∧ f.selection.made.Nodup ∧ (∀ m ∈ f.members, m.firing.Admits X s) ∧
    X.Solvable (f.information X s) ∧ X.Entails (f.information X s) (fun _ σ => f.Holds X s σ)

/-- **A compatible part of a bag**: members of the bag, jointly admitted with their takes apart, that
no further member of the bag can join. -/
def AdmitsPart (f : Bag O E P s.frame) (l : List (Member O E P f.ext)) : Prop :=
  (∀ m ∈ l, m ∈ f.members) ∧ (⟨f.ext, l⟩ : Bag O E P s.frame).Admits X s ∧
    ∀ m ∈ f.members, m ∉ l → ¬ (⟨f.ext, m :: l⟩ : Bag O E P s.frame).Admits X s

variable {X s}

/-- **Guards at each member's own information give admission at the entry state.** -/
theorem admitsAtEntry_of_admitsOwn (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b))
    {f : Bag O E P s.frame} (own : f.AdmitsOwn X s) : f.AdmitsAtEntry X s :=
  ⟨own.1.1, own.1.2.2.1, fun _ inside => admits_member X inhabited own inside, own.2.2.1,
    (admits_of_admitsOwn X own).2.2.2⟩

/-- **The reading that refuses is the reading at the entry state with the takes apart and the joint
selection enabled as one commit.** -/
theorem admitsOwn_iff_admitsAtEntry
    (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b)) {f : Bag O E P s.frame} :
    f.AdmitsOwn X s ↔ f.AdmitsAtEntry X s ∧ f.selection.taken.Nodup ∧
      Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) := by
  constructor
  · intro own
    exact ⟨admitsAtEntry_of_admitsOwn inhabited own, own.1.2.1, own.2.1⟩
  · rintro ⟨⟨fresh, made, members, solvable, -⟩, taken, enabled⟩
    exact ⟨⟨fresh, taken, made, fun m inside => (members m inside).1.2.2.2⟩, enabled, solvable,
      fun m inside => (members m inside).2.2.2⟩

end Bag

end Readings

/-! ## The control: two matches take one coin -/

namespace Shop

open Mettapedia.Logic.LP
open Examples (Tm X E c)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- Take a coin `1`, read a want `7`, make a bought row `2`. -/
def buy : Rule Tm := ⟨PUnit.unit, ⟨[c 1], [c 7], [], [], [c 2]⟩, []⟩

/-- **The program.** -/
def shop : Program Tm := {buy}

/-- The label of each row: a coin at `0`, wants elsewhere. -/
def kind : ℕ → ℕ
  | 0 => 1
  | _ => 7

/-- **One coin at `0` and two wants at `1` and `2`.** -/
def market : State Tm ℕ := ⟨PUnit.unit, [], {0, 1, 2}, fun o => c (kind o)⟩

/-- Take the coin, read the want at `w`, make the identity `n`. -/
def buyFor (w n : ℕ) : OneMember action ℕ shop := ⟨buy, rfl, Subst.id atoms, ⟨[0], [w], [n]⟩, []⟩

/-- **The bag of the two matches.** -/
def both : Bag ℕ E shop PUnit.unit := bagOf action [buyFor 1 10, buyFor 2 11]

theorem buy_ground : ∀ t ∈ buy.terms, ∀ σ : Subst atoms, action.apply σ t = t := by
  intro t member σ
  have listed : t ∈ [c 1, c 7, c 2] := member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl <;> rfl

theorem first_information :
    (buyFor 1 10).firing.information X market = [(c 1, c 1), (c 7, c 7)] := rfl

theorem second_information :
    (buyFor 2 11).firing.information X market = [(c 1, c 1), (c 7, c 7)] := rfl

theorem both_information :
    Bag.information X market both = [(c 1, c 1), (c 7, c 7), (c 1, c 1), (c 7, c 7)] := rfl

/-- The identity solves every list of equations with identical sides. -/
theorem solves_identical {l : List (Equation (Term atoms))} (identical : ∀ e ∈ l, e.1 = e.2) :
    X.Models (a := PUnit.unit) (b := PUnit.unit) (Subst.id atoms) l := by
  intro e member
  show Subst.applyTerm (Subst.id atoms) e.1 = Subst.applyTerm (Subst.id atoms) e.2
  rw [identical e member]

theorem first_admitted : (buyFor 1 10).firing.Admits X market := by
  refine ⟨⟨Examples.fresh_of_ground action market (buyFor 1 10).firing buy_ground,
    List.nodup_singleton 0, List.nodup_singleton 10, rfl, rfl, rfl, rfl⟩,
    ⟨by decide, by decide, by decide, by decide, fun q member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, Subst.id atoms, solves_identical fun e member => ?_⟩,
    fun b σ _ => ⟨fun check member => absurd member List.not_mem_nil,
      fun q member => absurd member List.not_mem_nil⟩⟩
  rw [first_information] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem second_admitted : (buyFor 2 11).firing.Admits X market := by
  refine ⟨⟨Examples.fresh_of_ground action market (buyFor 2 11).firing buy_ground,
    List.nodup_singleton 0, List.nodup_singleton 11, rfl, rfl, rfl, rfl⟩,
    ⟨by decide, by decide, by decide, by decide, fun q member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, Subst.id atoms, solves_identical fun e member => ?_⟩,
    fun b σ _ => ⟨fun check member => absurd member List.not_mem_nil,
      fun q member => absurd member List.not_mem_nil⟩⟩
  rw [second_information] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem both_members {m : OneMember action ℕ shop} (inside : m ∈ both.members) :
    m = buyFor 1 10 ∨ m = buyFor 2 11 := by
  have listed : m ∈ [buyFor 1 10, buyFor 2 11] := inside
  rcases List.mem_cons.mp listed with first | rest
  · exact Or.inl first
  · exact Or.inr (List.mem_singleton.mp rest)

/-- **Refused when the takes must be apart**: the coin is taken twice. -/
theorem both_refused : ¬ Bag.Admits X market both := fun admitted => by
  have taken : ([0, 0] : List ℕ).Nodup := admitted.1.2.1
  exact absurd taken (by decide)

/-- **Admitted at the entry state with takes allowed to coincide.** -/
theorem both_atEntry : Bag.AdmitsAtEntry X market both := by
  refine ⟨fresh_of_ground_bag action market _ fun m inside => ?_, by decide, fun m inside => ?_,
    ⟨PUnit.unit, Subst.id atoms, solves_identical fun e member => ?_⟩,
    fun b σ _ m inside => ?_⟩
  · rcases both_members inside with rfl | rfl <;> exact buy_ground
  · rcases both_members inside with rfl | rfl
    · exact first_admitted
    · exact second_admitted
  · rw [both_information] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl
  · rcases both_members inside with rfl | rfl <;>
      exact ⟨fun check member => absurd member List.not_mem_nil,
        fun q member => absurd member List.not_mem_nil⟩

/-- **Its result**: no coin, the two wants, two bought rows. -/
theorem both_result : (Bag.result X market both).present = {1, 2, 10, 11} := by decide

theorem both_bought : (Bag.result X market both).label 10 = c 2 ∧
    (Bag.result X market both).label 11 = c 2 := ⟨rfl, rfl⟩

/-- **A compatible part with the first match.** -/
theorem part_first : Bag.AdmitsPart X market both [buyFor 1 10] := by
  refine ⟨fun m inside => ?_, ?_, fun m inside outside => ?_⟩
  · rw [List.mem_singleton.mp inside]
    exact List.mem_cons_self
  · exact (Bag.admits_single X market (buyFor 1 10)).mpr first_admitted
  · rcases both_members inside with rfl | rfl
    · exact absurd List.mem_cons_self outside
    · intro admitted
      have taken : ([0, 0] : List ℕ).Nodup := admitted.1.2.1
      exact absurd taken (by decide)

/-- Its result: no coin, the two wants, one bought row. -/
theorem part_result :
    (Bag.result X market (⟨PUnit.unit, [buyFor 1 10]⟩ : Bag ℕ E shop PUnit.unit)).present =
      {1, 2, 10} := by decide

/-- **Every compatible part has at most one member**: every member takes the coin. -/
theorem parts_single {l : List (OneMember action ℕ shop)} (part : Bag.AdmitsPart X market both l) :
    l.length ≤ 1 := by
  obtain ⟨within, admitted, -⟩ := part
  have takesCoin : ∀ m ∈ l, m.selection.taken = [0] := by
    intro m inside
    rcases both_members (within m inside) with rfl | rfl <;> rfl
  match l, within, takesCoin, admitted with
  | [], _, _, _ => exact Nat.zero_le _
  | [_], _, _, _ => exact le_refl _
  | first :: second :: rest, _, takes, admitted =>
      exfalso
      have nodup : (first.selection.taken ++ (second.selection.taken ++
          (rest.flatMap fun m => m.selection.taken))).Nodup := admitted.1.2.1
      rw [takes first List.mem_cons_self, takes second (List.mem_cons_of_mem _ List.mem_cons_self)]
        at nodup
      exact (List.nodup_cons.mp nodup).1 (by simp)

/-- **The three readings give three outcomes at one state**: refused; both bought, the coin taken
once; one bought. -/
theorem three_readings :
    ¬ Bag.Admits X market both ∧
      (Bag.AdmitsAtEntry X market both ∧ (Bag.result X market both).present = {1, 2, 10, 11}) ∧
      (Bag.AdmitsPart X market both [buyFor 1 10] ∧
        (Bag.result X market (⟨PUnit.unit, [buyFor 1 10]⟩ : Bag ℕ E shop PUnit.unit)).present =
          {1, 2, 10}) ∧
      ∀ l, Bag.AdmitsPart X market both l → l.length ≤ 1 :=
  ⟨both_refused, ⟨both_atEntry, both_result⟩, ⟨part_first, part_result⟩,
    fun _ part => parts_single part⟩

end Shop

/-! ## A reader and a taker of one row -/

namespace ReadTake

open Mettapedia.Logic.LP
open Examples (Tm X E c)
open EveryControls (copy copy_ground consume_ground tokensAt)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- **The program**: read a token and make a `2`; take a token and make a `2`. -/
def program : Program Tm := {copy, Examples.consume}

/-- One token at `0`. -/
def one : State Tm ℕ := tokensAt {0}

/-- Read the token, make `10`. -/
def reader : OneMember action ℕ program := ⟨copy, Or.inl rfl, Subst.id atoms, ⟨[], [0], [10]⟩, []⟩

/-- Take the token, make `11`. -/
def taker : OneMember action ℕ program :=
  ⟨Examples.consume, Or.inr rfl, Subst.id atoms, ⟨[0], [], [11]⟩, []⟩

/-- **The bag of the reader and the taker.** -/
def pair : Bag ℕ E program PUnit.unit := bagOf action [reader, taker]

theorem reader_admitted : reader.firing.Admits X one := by
  refine ⟨⟨Examples.fresh_of_ground action one reader.firing copy_ground,
    List.nodup_nil, List.nodup_singleton 10, rfl, rfl, rfl, rfl⟩,
    ⟨by decide, by decide, by decide, by decide, fun q member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, Subst.id atoms, Shop.solves_identical fun e member => ?_⟩,
    fun b σ _ => ⟨fun check member => absurd member List.not_mem_nil,
      fun q member => absurd member List.not_mem_nil⟩⟩
  have listed : e ∈ [(c 1, c 1)] := member
  rw [List.mem_singleton.mp listed]

theorem taker_admitted : taker.firing.Admits X one := by
  refine ⟨⟨Examples.fresh_of_ground action one taker.firing consume_ground,
    List.nodup_singleton 0, List.nodup_singleton 11, rfl, rfl, rfl, rfl⟩,
    ⟨by decide, by decide, by decide, by decide, fun q member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, Subst.id atoms, Shop.solves_identical fun e member => ?_⟩,
    fun b σ _ => ⟨fun check member => absurd member List.not_mem_nil,
      fun q member => absurd member List.not_mem_nil⟩⟩
  have listed : e ∈ [(c 1, c 1)] := member
  rw [List.mem_singleton.mp listed]

theorem pair_members {m : OneMember action ℕ program} (inside : m ∈ pair.members) :
    m = reader ∨ m = taker := by
  have listed : m ∈ [reader, taker] := inside
  rcases List.mem_cons.mp listed with first | rest
  · exact Or.inl first
  · exact Or.inr (List.mem_singleton.mp rest)

/-- **Refused when no member may read what another takes.** -/
theorem refused : ¬ Bag.Admits X one pair := fun admitted =>
  Finset.disjoint_left.mp admitted.2.1.apart (show 0 ∈ ([0] : List ℕ).toFinset by decide)
    (show 0 ∈ ([0] : List ℕ).toFinset by decide)

/-- **Admitted at the entry state.** -/
theorem atEntry : Bag.AdmitsAtEntry X one pair := by
  refine ⟨fresh_of_ground_bag action one _ fun m inside => ?_, by decide, fun m inside => ?_,
    ⟨PUnit.unit, Subst.id atoms, Shop.solves_identical fun e member => ?_⟩,
    fun b σ _ m inside => ?_⟩
  · rcases pair_members inside with rfl | rfl
    · exact copy_ground
    · exact consume_ground
  · rcases pair_members inside with rfl | rfl
    · exact reader_admitted
    · exact taker_admitted
  · have listed : e ∈ [(c 1, c 1), (c 1, c 1)] := member
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at listed
    rw [listed]
  · rcases pair_members inside with rfl | rfl <;>
      exact ⟨fun check member => absurd member List.not_mem_nil,
        fun q member => absurd member List.not_mem_nil⟩

theorem pair_result : (Bag.result X one pair).present = {10, 11} := by decide

/-- After the reader. -/
def afterReader : State Tm ℕ := reader.firing.result X one

theorem taker_after_reader : taker.firing.Admits X afterReader := by
  refine ⟨⟨Examples.fresh_of_ground action afterReader taker.firing consume_ground,
    List.nodup_singleton 0, List.nodup_singleton 11, rfl, rfl, rfl, rfl⟩,
    ⟨by decide, by decide, by decide, by decide, fun q member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, Subst.id atoms, Shop.solves_identical fun e member => ?_⟩,
    fun b σ _ => ⟨fun check member => absurd member List.not_mem_nil,
      fun q member => absurd member List.not_mem_nil⟩⟩
  have listed : e ∈ [(c 1, c 1), (c 1, c 1)] := member
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at listed
  rw [listed]

/-- **The reader first, then the taker, reach the rows of the bag's result.** -/
theorem reader_first :
    Succ (step X ℕ E program).toStep one afterReader ∧
      Succ (step X ℕ E program).toStep afterReader (taker.firing.result X afterReader) ∧
      (taker.firing.result X afterReader).present = (Bag.result X one pair).present := by
  refine ⟨⟨reader.firing, reader_admitted, rfl⟩, ⟨taker.firing, taker_after_reader, rfl⟩, ?_⟩
  rw [pair_result]
  decide

/-- **After the taker the reader cannot fire**: the token is gone. -/
theorem taker_first_stops : ¬ reader.firing.Admits X (taker.firing.result X one) := fun admitted =>
  absurd (admitted.2.1.kept_subset (show 0 ∈ ([0] : List ℕ).toFinset by decide)) (by decide)

end ReadTake

#print axioms Bag.admitsAtEntry_of_admitsOwn
#print axioms Bag.admitsOwn_iff_admitsAtEntry
#print axioms Shop.first_admitted
#print axioms Shop.both_refused
#print axioms Shop.both_atEntry
#print axioms Shop.both_result
#print axioms Shop.part_first
#print axioms Shop.part_result
#print axioms Shop.parts_single
#print axioms Shop.three_readings
#print axioms ReadTake.refused
#print axioms ReadTake.atEntry
#print axioms ReadTake.pair_result
#print axioms ReadTake.reader_first
#print axioms ReadTake.taker_first_stops

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
