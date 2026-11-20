import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Every
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.PartialRecursive
import Mettapedia.GSLT.Meredith.GSLT

/-!
# One active row: the bag step is the step of the program

## At a state with at most one present row

Over every frame action, when every rule of the program has a take pattern:

* **`Bag.members_le_one`**: a jointly admitted bag at a state with at most one present row has at most
  one member: its takes are apart and present, and every member takes a row.
* **`bagStep_iff_step`**: so there the bag step and the step of the program have the same successors.
* **`every_is_one`**: and `every` over a set of rules is one match: when some firing of the rules is
  admitted, a bag admitted as `every` is that one match.

## The machine of the partial recursive functions

`Machines.PartialRecursive.program` has nineteen rules, each taking one row and making one row. From the
pending evaluation of a code, every state reached has one present row (`present_one_along`). So:

* **`reach_iff`**: from the start state, the bag step and the step of the program reach the same states;
* **`bag_halts_iff`**: the bag step halts with `w` from the pending evaluation of `c` on `v` exactly when
  `w ∈ c.eval v` (`PartialRecursive.halts_iff` transported).

On a machine whose configuration is one row, the candidates for what one step commits coincide: one
match, any compatible bag, a maximal bag, and every match of a rule are the same steps.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)

universe uO uT uH uE uOcc

/-! ## At most one present row -/

section General

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {P : Program Tm}

/-- A list of items each counting at least one is no longer than their total count. -/
theorem length_le_sum {α : Type*} (g : α → ℕ) :
    ∀ (l : List α), (∀ a ∈ l, 1 ≤ g a) → l.length ≤ (l.map g).sum
  | [], _ => le_refl 0
  | a :: rest, each => by
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have later := length_le_sum g rest fun a' inside => each a' (List.mem_cons_of_mem _ inside)
      have first := each a List.mem_cons_self
      omega

/-- **At a state with at most one present row, a jointly admitted bag of rules that take has at most
one member.** -/
theorem Bag.members_le_one {s : State Tm O} {f : Bag O E P s.frame} (few : s.present.card ≤ 1)
    (takes : ∀ m ∈ f.members, m.rule.body.take ≠ []) (admitted : f.Admits X s) :
    f.members.length ≤ 1 := by
  obtain ⟨⟨-, nodup, -, lengths⟩, enabled, -, -⟩ := admitted
  have total : f.members.length ≤ f.selection.taken.length := by
    show f.members.length ≤ (f.members.flatMap fun m => m.selection.taken).length
    rw [List.length_flatMap]
    refine length_le_sum _ f.members fun m inside => ?_
    have same := (lengths m inside).1
    have positive : 0 < m.rule.body.take.length := List.length_pos_of_ne_nil (takes m inside)
    omega
  have bounded : f.selection.taken.length ≤ s.present.card := by
    rw [← List.toFinset_card_of_nodup nodup]
    exact Finset.card_le_card enabled.taken_subset
  omega

/-- A list of at most one item that holds `m` is `[m]`. -/
theorem eq_singleton_of_length_le_one {α : Type*} {l : List α} {m : α} (short : l.length ≤ 1)
    (inside : m ∈ l) : l = [m] := by
  match l, short, inside with
  | [_], _, inside => rw [List.mem_singleton.mp inside]
  | _ :: _ :: _, short, _ => exact absurd short (by simp)

variable (O E P) in
/-- **At a state with at most one present row, the bag step and the step of the program have the same
successors**, when every rule of the program takes. -/
theorem bagStep_iff_step {s : State Tm O} (few : s.present.card ≤ 1)
    (takes : ∀ r ∈ P, r.body.take ≠ []) (s' : State Tm O) :
    Succ (bagStep X O E P).toStep s s' ↔ Succ (step X O E P).toStep s s' := by
  constructor
  · rintro ⟨f, ⟨nonempty, admitted⟩, rfl⟩
    have short := Bag.members_le_one X few (fun m _ => takes m.rule m.member) admitted
    have one : f.members.length = 1 := by
      have positive := List.length_pos_of_ne_nil nonempty
      omega
    exact (succ_iff_single X O E P s _).mpr ⟨f, one, ⟨nonempty, admitted⟩, rfl⟩
  · exact succ_bagStep_of_succ X O E P

/-- **`every` is one match there**: when a firing of the rules is admitted, a bag admitted as `every`
over them is that one match. -/
theorem every_is_one {s : State Tm O} (few : s.present.card ≤ 1) (takes : ∀ r ∈ P, r.body.take ≠ [])
    {Q : Set (Rule Tm)} {f : Bag O E P s.frame} (every : f.AdmitsEvery X s Q)
    {g : Firing O E P s.frame} (inQ : g.rule ∈ Q) (admitted : g.Admits X s) :
    ∃ m, f.members = [m] ∧ m.key = firingKey g := by
  obtain ⟨m, inside, sameKey⟩ := List.mem_map.mp (every.2.2.2 g inQ admitted)
  exact ⟨m, eq_singleton_of_length_le_one
    (Bag.members_le_one X few (fun m _ => takes m.rule m.member) every.admits) inside, sameKey⟩

end General

/-! ## The machine of the partial recursive functions -/

namespace Partrec

open Mettapedia.Logic.LP
open Presentation.Schematic (SState schematicStep)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.PartialRecursive
  (program start HaltedWith halts_iff rule)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (rowRule)

/-- The frame action of the machine. -/
abbrev Xm := Presentation.Schematic.X

/-- Its extensions. -/
abbrev Em := Presentation.Schematic.E

/-- **Every rule of the machine takes a row.** -/
theorem program_takes : ∀ r ∈ ({r | r ∈ program} : Program _), r.body.take ≠ [] := by
  intro r inside
  obtain ⟨n, -, rfl⟩ := List.mem_map.mp inside
  simp [rule, rowRule]

/-- **A firing of the machine keeps one present row.** -/
theorem present_one_after {s : SState ℕ} (one : s.present.card = 1)
    {g : Firing ℕ Em {r | r ∈ program} s.frame} (admitted : g.Admits Xm s) :
    (g.result Xm s).present.card = 1 := by
  obtain ⟨a, isA⟩ := Finset.card_eq_one.mp one
  obtain ⟨n, -, isRule⟩ := List.mem_map.mp g.member
  obtain ⟨⟨-, -, -, takeLength, -, produceLength, -⟩, enabled, -, -⟩ := admitted
  rw [← isRule] at takeLength produceLength
  obtain ⟨o, taken⟩ := List.length_eq_one_iff.mp (show g.selection.taken.length = 1 from takeLength.symm)
  obtain ⟨n', made⟩ := List.length_eq_one_iff.mp (show g.selection.made.length = 1 from produceLength.symm)
  have present : o ∈ s.present := enabled.taken_subset (List.mem_toFinset.mpr (by rw [taken]; simp))
  rw [isA, Finset.mem_singleton] at present
  have rows : (g.result Xm s).present = {n'} := by
    ext x
    show x ∈ fire s.present (g.selection.commit (T := Unit)) ↔ x ∈ ({n'} : Finset ℕ)
    rw [mem_fire, isA]
    simp only [Selection.commit, List.mem_toFinset, taken, made, Finset.mem_singleton,
      List.mem_singleton]
    constructor
    · rintro (⟨same, notTaken⟩ | same)
      · exact absurd (same.trans present.symm) notTaken
      · exact same
    · exact Or.inr
  rw [rows, Finset.card_singleton]

/-- **Every state the step of the machine reaches from a pending evaluation has one present row.** -/
theorem present_one_along {c : Turing.ToPartrec.Code} {v : List ℕ} {s' : SState ℕ}
    (reach : Relation.ReflTransGen (Succ (schematicStep ℕ program).toStep) (start c v) s') :
    s'.present.card = 1 := by
  induction reach with
  | refl => rfl
  | tail _ step' earlier =>
      obtain ⟨g, admitted, rfl⟩ := step'
      exact present_one_after earlier admitted

/-- **From the pending evaluation, the bag step and the step of the machine reach the same states.** -/
theorem reach_iff (c : Turing.ToPartrec.Code) (v : List ℕ) (s' : SState ℕ) :
    Relation.ReflTransGen (Succ (bagStep Xm ℕ Em {r | r ∈ program}).toStep) (start c v) s' ↔
      Relation.ReflTransGen (Succ (schematicStep ℕ program).toStep) (start c v) s' := by
  constructor
  · intro reach
    induction reach with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ step' earlier =>
        refine Relation.ReflTransGen.tail earlier ?_
        exact (bagStep_iff_step Xm ℕ Em {r | r ∈ program} (present_one_along earlier).le program_takes
          _).mp step'
  · intro reach
    induction reach with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ step' earlier =>
        exact Relation.ReflTransGen.tail earlier (succ_bagStep_of_succ Xm ℕ Em {r | r ∈ program} step')

/-- **The bag step computes what the machine computes**: from the pending evaluation of `c` on `v` it
reaches a state that reads as the halted row with output `w` exactly when `w ∈ c.eval v`. -/
theorem bag_halts_iff (c : Turing.ToPartrec.Code) (v w : List ℕ) :
    (∃ s', Relation.ReflTransGen (Succ (bagStep Xm ℕ Em {r | r ∈ program}).toStep) (start c v) s' ∧
      HaltedWith w s') ↔ w ∈ c.eval v := by
  rw [← halts_iff c v w]
  constructor
  · rintro ⟨s', reach, halted⟩
    exact ⟨s', (Mettapedia.GSLT.Meredith.multiStep_iff_reflTransGen _ _ _).mpr
      ((reach_iff c v s').mp reach), halted⟩
  · rintro ⟨s', path, halted⟩
    exact ⟨s', (reach_iff c v s').mpr
      ((Mettapedia.GSLT.Meredith.multiStep_iff_reflTransGen _ _ _).mp path), halted⟩

end Partrec

#print axioms Bag.members_le_one
#print axioms bagStep_iff_step
#print axioms every_is_one
#print axioms Partrec.program_takes
#print axioms Partrec.present_one_after
#print axioms Partrec.present_one_along
#print axioms Partrec.reach_iff
#print axioms Partrec.bag_halts_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
