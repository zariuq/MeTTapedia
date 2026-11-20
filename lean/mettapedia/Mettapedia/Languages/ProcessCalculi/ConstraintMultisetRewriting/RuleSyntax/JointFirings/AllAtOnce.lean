import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Clashes

/-!
# One rule, one step of `every`, as many rows as there are tokens

The program `EveryControls.tokens` is one rule: take a token `1`, make a `2`. A firing of the program
makes one row. At the state of `n` tokens, the bag that spends every token (`spendAll n`):

* is admitted as `every` over the program (`spendAll_every`), for every `n`;
* makes `n` rows in one step (`spendAll_made`).

So the step of `every` over a finite program commits an unbounded number of rows at once. A firing of the
one-match step commits at most as many new rows as its rule makes (`OccurrenceCorePlacement.added_card_le`
on the first-order step), and no finite list of rules rewrites "every copy of `a` into a copy of `b`" at
once (`Representation.allAtOnce_not_finite`). The bag step is not a finite program of one-match firings
in disguise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.AllAtOnce

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Logic.LP
open Examples (Tm X E c)
open EveryControls (tokens tokensAt takeAt firing_shape consume_ground)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- **The bag that spends the tokens at `0, …, n - 1`**, making `n, …, 2n - 1`. -/
def spendAll (n : ℕ) : Bag ℕ E tokens PUnit.unit :=
  bagOf action ((List.range n).map fun o => takeAt o (n + o))

theorem spendAll_members {n : ℕ} {m : OneMember action ℕ tokens} (inside : m ∈ (spendAll n).members) :
    ∃ o < n, m = takeAt o (n + o) := by
  obtain ⟨o, inRange, rfl⟩ := List.mem_map.mp inside
  exact ⟨o, List.mem_range.mp inRange, rfl⟩

theorem spendAll_taken (n : ℕ) : (spendAll n).selection.taken = List.range n := by
  show ((List.range n).map fun o => takeAt o (n + o)).flatMap (fun m => m.selection.taken) = _
  rw [List.flatMap_map]
  exact List.flatMap_singleton' _

theorem spendAll_made (n : ℕ) : (spendAll n).selection.made = (List.range n).map fun o => n + o := by
  show ((List.range n).map fun o => takeAt o (n + o)).flatMap (fun m => m.selection.made) = _
  rw [List.flatMap_map]
  exact List.flatMap_pure_eq_map _ _

theorem spendAll_read (n : ℕ) : (spendAll n).selection.read = [] := by
  show ((List.range n).map fun o => takeAt o (n + o)).flatMap (fun m => m.selection.read) = []
  rw [List.flatMap_map]
  exact List.flatMap_eq_nil_iff.mpr fun _ _ => rfl

/-- **Spending every token is admitted as `every`, for every number of tokens.** -/
theorem spendAll_every (n : ℕ) :
    Bag.AdmitsEvery X (tokensAt (Finset.range n)) tokens (spendAll n) := by
  have madeNodup : ((List.range n).map fun o => n + o).Nodup :=
    (List.nodup_range).map fun a b same => by simpa using same
  refine ⟨⟨⟨fresh_of_ground_bag action _ _ fun m inside => ?_, ?_, ?_, fun m inside => ?_⟩,
      ⟨fun o member => ?_, fun o member => ?_, Finset.disjoint_left.mpr fun _ _ kept => ?_,
        Finset.disjoint_left.mpr fun o made present => ?_, fun q member => by
          simp [Selection.commit] at member⟩,
      ⟨PUnit.unit, Subst.id atoms, Shop.solves_identical fun e member => ?_⟩,
      fun m inside b σ _ => ?_⟩, fun m inside => m.member, ?_, fun g _ admitted => ?_⟩
  · obtain ⟨o, -, rfl⟩ := spendAll_members inside
    exact consume_ground
  · rw [spendAll_taken]
    exact List.nodup_range
  · rw [spendAll_made]
    exact madeNodup
  · obtain ⟨o, -, rfl⟩ := spendAll_members inside
    exact ⟨rfl, rfl, rfl, rfl⟩
  · have inside : o ∈ (spendAll n).selection.taken := List.mem_toFinset.mp member
    rw [spendAll_taken] at inside
    exact Finset.mem_range.mpr (List.mem_range.mp inside)
  · have inside : o ∈ (spendAll n).selection.read := List.mem_toFinset.mp member
    rw [spendAll_read] at inside
    exact absurd inside List.not_mem_nil
  · have inside : _ ∈ (spendAll n).selection.read := List.mem_toFinset.mp kept
    rw [spendAll_read] at inside
    exact absurd inside List.not_mem_nil
  · have inside : o ∈ (spendAll n).selection.made := List.mem_toFinset.mp made
    rw [spendAll_made] at inside
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp inside
    have below : n + k < n := Finset.mem_range.mp present
    omega
  · rcases List.mem_append.mp member with known | own
    · exact absurd known List.not_mem_nil
    · obtain ⟨m, inside, inOwn⟩ := List.mem_flatMap.mp own
      obtain ⟨o, -, rfl⟩ := spendAll_members inside
      have listed : e ∈ [(c 1, c 1)] := inOwn
      rw [List.mem_singleton.mp listed]
  · obtain ⟨o, -, rfl⟩ := spendAll_members inside
    exact ⟨fun check member => absurd member List.not_mem_nil,
      fun q member => absurd member List.not_mem_nil⟩
  · show (((List.range n).map fun o => takeAt o (n + o)).map Member.key).Nodup
    rw [List.map_map]
    exact (List.nodup_range).map fun a b same => by
      simpa [takeAt, Member.key] using same
  · obtain ⟨o, made, present, rule, selection⟩ := firing_shape g admitted
    have key : firingKey g = (Examples.consume, [o], []) := by
      unfold firingKey
      rw [rule, selection]
    rw [key]
    refine List.mem_map.mpr ⟨takeAt o (n + o), List.mem_map.mpr ⟨o, ?_, rfl⟩, rfl⟩
    exact List.mem_range.mpr (Finset.mem_range.mp present)

/-- **It makes `n` rows in one step**: the rows of its result that were not there are `n`, every one of
them made. -/
theorem spendAll_made_rows (n : ℕ) :
    ((Bag.result X (tokensAt (Finset.range n)) (spendAll n)).present \ Finset.range n).card = n := by
  have rows : (Bag.result X (tokensAt (Finset.range n)) (spendAll n)).present \ Finset.range n =
      ((List.range n).map fun o => n + o).toFinset := by
    ext o
    have unfolded : o ∈ (Bag.result X (tokensAt (Finset.range n)) (spendAll n)).present ↔
        o ∈ fire (Finset.range n) ((spendAll n).selection.commit (T := Unit)) := Iff.rfl
    rw [Finset.mem_sdiff, unfolded, mem_fire, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨⟨present, -⟩ | made, outside⟩
      · exact absurd present outside
      · have inside : o ∈ (spendAll n).selection.made := List.mem_toFinset.mp made
        rw [spendAll_made] at inside
        exact List.mem_map.mp inside
    · rintro ⟨k, inRange, rfl⟩
      refine ⟨Or.inr (List.mem_toFinset.mpr ?_), fun inside => ?_⟩
      · rw [spendAll_made]
        exact List.mem_map.mpr ⟨k, inRange, rfl⟩
      · have below := Finset.mem_range.mp inside
        omega
  rw [rows, List.toFinset_card_of_nodup ((List.nodup_range).map fun a b same => by simpa using same),
    List.length_map, List.length_range]

#print axioms spendAll_taken
#print axioms spendAll_made
#print axioms spendAll_every
#print axioms spendAll_made_rows

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.AllAtOnce
