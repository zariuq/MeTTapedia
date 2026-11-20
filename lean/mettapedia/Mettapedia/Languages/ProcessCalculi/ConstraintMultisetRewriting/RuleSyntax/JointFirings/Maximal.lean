import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.EveryControls

/-!
# A maximal bag of matches

**A maximal jointly admitted bag of distinct matches** (`Bag.AdmitsMaximal`): the bag is jointly
admitted, its keys are distinct, and every jointly admitted bag of distinct matches that has its keys has
no other key.

* Its steps are steps of the bag step (`Bag.AdmitsMaximal.admits`).
* **What "maximal" asks is a none query** (`Bag.admitsMaximal_iff`): there is no jointly admitted bag of
  distinct matches with the same matches and one more. Like the completeness of `every`, it is read at the
  entry state over every selection of present rows, and it is not kept when rows are added.
* **Not kept when a row is added** (`MaximalControls.lone_maximal`, `MaximalControls.lone_not_maximal`):
  with one token, the bag that takes it is maximal; with a second token beside it, the same bag is still
  jointly admitted and is no longer maximal.

Keys must be distinct for the notion to exist at all: a rule that only reads can be fired any number of
times on one match in one bag (`EveryControls.twice_admitted`), so without distinct keys a bag of a reading
rule always has a larger one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open OneFrame (Terms frames ext)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

namespace Bag

variable (X : Frames Tm Hom) {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {P : Program Tm} (s : State Tm O)

/-- **A maximal jointly admitted bag of distinct matches.** -/
def AdmitsMaximal (f : Bag O E P s.frame) : Prop :=
  f.Admits X s ∧ f.Distinct ∧ ∀ f' : Bag O E P s.frame, f'.Admits X s → f'.Distinct →
    (∀ k ∈ f.members.map Member.key, k ∈ f'.members.map Member.key) →
    ∀ k ∈ f'.members.map Member.key, k ∈ f.members.map Member.key

variable {X s}

theorem AdmitsMaximal.admits {f : Bag O E P s.frame} (maximal : f.AdmitsMaximal X s) : f.Admits X s :=
  maximal.1

/-- **What "maximal" asks is a none query**: no jointly admitted bag of distinct matches has the same
matches and one more. -/
theorem admitsMaximal_iff (f : Bag O E P s.frame) :
    f.AdmitsMaximal X s ↔ f.Admits X s ∧ f.Distinct ∧
      ¬ ∃ f' : Bag O E P s.frame, f'.Admits X s ∧ f'.Distinct ∧
        (∀ k ∈ f.members.map Member.key, k ∈ f'.members.map Member.key) ∧
        ∃ k ∈ f'.members.map Member.key, k ∉ f.members.map Member.key := by
  constructor
  · rintro ⟨admitted, distinct, maximal⟩
    exact ⟨admitted, distinct, fun ⟨f', admitted', distinct', sub, k, inside, outside⟩ =>
      outside (maximal f' admitted' distinct' sub k inside)⟩
  · rintro ⟨admitted, distinct, none⟩
    refine ⟨admitted, distinct, fun f' admitted' distinct' sub k inside => ?_⟩
    by_contra outside
    exact none ⟨f', admitted', distinct', sub, k, inside, outside⟩

end Bag

namespace MaximalControls

open Mettapedia.Logic.LP
open Examples (Tm X E c)
open EveryControls (tokens tokensAt twoTokens takeAt takeAt_admitted spendBoth spendBoth_every)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- The bag that takes the first token. -/
def lone : Bag ℕ E tokens PUnit.unit := bagOf action [takeAt 0 10]

theorem lone_admitted {W : Finset ℕ} (present : 0 ∈ W) (fresh : 10 ∉ W) :
    Bag.Admits X (tokensAt W) lone :=
  (Bag.admits_single X (tokensAt W) (takeAt 0 10)).mpr (takeAt_admitted present fresh)

/-- **The key of every member of a jointly admitted bag of the program**: the rule, one present token,
no read. -/
theorem member_key {W : Finset ℕ} {f : Bag ℕ E tokens PUnit.unit}
    (admitted : Bag.Admits X (tokensAt W) f) {m : Member ℕ E tokens f.ext} (inside : m ∈ f.members) :
    ∃ o ∈ W, m.key = (Examples.consume, [o], []) := by
  obtain ⟨⟨-, -, -, lengths⟩, enabled, -, -⟩ := admitted
  obtain ⟨takeLength, readLength, -, -⟩ := lengths m inside
  have isConsume : m.rule = Examples.consume := m.member
  rw [isConsume] at takeLength readLength
  obtain ⟨o, takenEq⟩ := List.length_eq_one_iff.mp
    (show m.selection.taken.length = 1 from takeLength.symm)
  have readEq : m.selection.read = [] :=
    List.length_eq_zero_iff.mp (show m.selection.read.length = 0 from readLength.symm)
  have isTaken : o ∈ m.selection.taken := by
    rw [takenEq]
    exact List.mem_cons_self
  refine ⟨o, enabled.taken_subset
    (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨m, inside, isTaken⟩)), ?_⟩
  show (m.rule, m.selection.taken, m.selection.read) = (Examples.consume, [o], [])
  rw [isConsume, takenEq, readEq]

/-- **With one token, the bag that takes it is maximal.** -/
theorem lone_maximal : Bag.AdmitsMaximal X (tokensAt {0}) lone := by
  refine ⟨lone_admitted (by decide) (by decide), List.nodup_singleton _,
    fun f' admitted' _ _ k inside => ?_⟩
  obtain ⟨m, inM, rfl⟩ := List.mem_map.mp inside
  obtain ⟨o, present, key⟩ := member_key admitted' inM
  rw [key, Finset.mem_singleton.mp present]
  exact List.mem_cons_self

/-- **With a second token beside it, the same bag is jointly admitted and no longer maximal.** -/
theorem lone_not_maximal :
    Bag.Admits X twoTokens lone ∧ ¬ Bag.AdmitsMaximal X twoTokens lone := by
  refine ⟨lone_admitted (by decide) (by decide), fun ⟨_, _, maximal⟩ => ?_⟩
  have inside := maximal spendBoth spendBoth_every.admits spendBoth_every.2.2.1
    (fun k inK => by
      rw [List.mem_singleton.mp (show k ∈ [(takeAt 0 10).key] from inK)]
      exact List.mem_cons_self)
    (takeAt 1 11).key (List.mem_cons_of_mem _ List.mem_cons_self)
  have same : (takeAt 1 11).key = (takeAt 0 10).key :=
    List.mem_singleton.mp (show (takeAt 1 11).key ∈ [(takeAt 0 10).key] from inside)
  have differ : ([1] : List ℕ) ≠ [0] := by decide
  exact differ (congrArg (fun k : Rule Tm × List ℕ × List ℕ => k.2.1) same)

end MaximalControls

#print axioms Bag.admitsMaximal_iff
#print axioms MaximalControls.member_key
#print axioms MaximalControls.lone_maximal
#print axioms MaximalControls.lone_not_maximal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
