import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Exactness

/-!
# Region-local observations and independent commits

The scope of a query is a predicate on fixed labels. Its observation can
read the entire selected region, including an empty answer or a minimum.
An outside update leaves that observation alone. Commutation of *effects*
also requires disjoint read, take, and make footprints in both directions.
These are laws of the existing occurrence commits, not an acquisition or
locking protocol.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.LocalReadScope

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v

variable {O : Type u} [DecidableEq O] {Label : Type v}

/-- Any observer of a fixed-label region may ignore a writer outside that
region. The observer can be Boolean, collecting, or an aggregate. -/
theorem observes_fire_outside {Answer : Type*} (observe : Finset O → Answer)
    (label : O → Label) (space : Label → Bool) (present : Finset O) (writer : Commit O Label)
    (outside : ∀ o ∈ writer.writes, space (label o) = false) :
    observe (regionOf label (fire present writer) space) =
      observe (regionOf label present space) :=
  congrArg observe (regionOf_fire_of_no_write outside)

/-- The entire footprint of a commit is local to a scope. For a query,
what matters is its declared region, not only the rows found there. -/
structure Local (label : O → Label) (space : Label → Bool) (c : Commit O Label) : Prop where
  taken : ∀ o ∈ c.taken, space (label o) = true
  kept : ∀ o ∈ c.kept, space (label o) = true
  made : ∀ o ∈ c.made, space (label o) = true
  query : ∀ q ∈ c.queries, ∀ label, q.region label = true → space label = true

omit [DecidableEq O] in
private theorem disjoint_of_regions {label : O → Label} {left right : Label → Bool}
    (apart : ∀ t, left t = true → right t = true → False) {xs ys : Finset O}
    (leftRows : ∀ o ∈ xs, left (label o) = true) (rightRows : ∀ o ∈ ys, right (label o) = true) :
    Disjoint xs ys :=
  Finset.disjoint_left.mpr fun o hx hy => apart _ (leftRows o hx) (rightRows o hy)

private theorem not_spoils {label : O → Label} {left right : Label → Bool} {c d : Commit O Label}
    (apart : ∀ t, left t = true → right t = true → False)
    (first : Local label left c) (second : Local label right d) :
    ¬ Spoils label c d := by
  rintro (kept | ⟨q, read, o, wrote, observes⟩)
  · exact kept (disjoint_of_regions apart first.taken second.kept)
  · have written : left (label o) = true := by
      rcases Finset.mem_union.mp wrote with taken | made
      · exact first.taken o taken
      · exact first.made o made
    exact apart _ written (second.query q read _ observes)

/-- Two locally enabled commits in disjoint scopes can execute in both
orders with the same physical result. Both locality hypotheses include
reads and outputs, not just the consumed inputs. -/
theorem commute_disjoint_scopes {label : O → Label} {left right : Label → Bool} {c d : Commit O Label}
    {present : Finset O} (apart : ∀ t, left t = true → right t = true → False)
    (first : Local label left c) (second : Local label right d)
    (enabledC : Enabled label present c) (enabledD : Enabled label present d) :
    Enabled label (fire present c) d ∧ Enabled label (fire present d) c ∧
      fire (fire present c) d = fire (fire present d) c := by
  have independent : Independent label c d := by
    refine ⟨?_, not_spoils apart first second,
      not_spoils (fun t hr hl => apart t hl hr) second first⟩
    rintro (take | make)
    · exact take (disjoint_of_regions apart first.taken second.taken)
    · exact make (disjoint_of_regions apart first.made second.made)
  obtain ⟨cd, dc⟩ := (independent_iff_both_orders enabledC enabledD).mp independent
  exact ⟨cd, dc, fire_comm enabledC enabledD⟩

/-- At a cut, the candidate is present in the region and no current
competitor has lower cost. Equal scores do not pick a winner. -/
def Minimum (label : O → Label) (space : Label → Bool) (cost : O → Nat)
    (chosen : O) (present : Finset O) : Prop :=
  chosen ∈ regionOf label present space ∧
    ∀ other ∈ regionOf label present space, cost chosen ≤ cost other

omit [DecidableEq O] in
theorem minimum_of_exact_cut {label : O → Label} {space : Label → Bool}
    {cost : O → Nat} {chosen : O} {before after : Finset O}
    (same : regionOf label after space = regionOf label before space) :
    Minimum label space cost chosen after ↔ Minimum label space cost chosen before := by
  unfold Minimum
  rw [same]

theorem minimum_fire_outside {label : O → Label} {space : Label → Bool}
    {cost : O → Nat} {chosen : O} {present : Finset O} {writer : Commit O Label}
    (outside : ∀ o ∈ writer.writes, space (label o) = false) :
    Minimum label space cost chosen (fire present writer) ↔
      Minimum label space cost chosen present :=
  minimum_of_exact_cut (regionOf_fire_of_no_write outside)

/-- A finer validation than equality of the full read: keep the chosen
occurrence and rule out a strictly cheaper newly made row. Any row that
was not newly made already belonged to the old region. -/
theorem minimum_survives_nonbeating_writer {label : O → Label} {space : Label → Bool}
    {cost : O → Nat} {chosen : O} {present : Finset O} {writer : Commit O Label}
    (before : Minimum label space cost chosen present)
    (retained : chosen ∉ writer.taken)
    (newcomers : ∀ o ∈ writer.made, space (label o) = true → cost chosen ≤ cost o) :
    Minimum label space cost chosen (fire present writer) := by
  have chosenRegion := mem_regionOf.mp before.1
  refine ⟨mem_regionOf.mpr ⟨mem_fire.mpr (Or.inl ⟨chosenRegion.1, retained⟩), chosenRegion.2⟩, ?_⟩
  intro other member
  obtain ⟨live, inside⟩ := mem_regionOf.mp member
  rcases mem_fire.mp live with ⟨old, _⟩ | made
  · exact before.2 _ (mem_regionOf.mpr ⟨old, inside⟩)
  · exact newcomers _ made inside

namespace Controls

/-- Occurrences 0 (cost 4) and 2 (cost 1) are in the bid space; 1 is outside
even though its score is lower. -/
def bidSpace (o : Nat) : Bool := o != 1

def price : Nat → Nat
  | 0 => 4
  | 2 => 1
  | _ => 0

private theorem first_minimum : Minimum id bidSpace price 0 ({0} : Finset Nat) := by
  simp [Minimum, bidSpace, price, regionOf]

theorem cheaper_elsewhere_preserves_choice :
    Minimum id bidSpace price 0 (fire {0} (Commit.makeOne 1 : Commit Nat Nat)) := by
  apply (minimum_fire_outside ?_).mpr first_minimum
  intro o written
  have same : o = 1 := by simpa [Commit.writes] using written
  simp [same, bidSpace]

theorem cheaper_here_refuses_even_with_chosen_present :
    0 ∈ fire {0} (Commit.makeOne 2 : Commit Nat Nat) ∧
      ¬ Minimum id bidSpace price 0 (fire {0} (Commit.makeOne 2 : Commit Nat Nat)) := by
  constructor
  · exact mem_fire.mpr (Or.inl ⟨Finset.mem_singleton_self 0, by simp⟩)
  · intro accepted
    have rival : 2 ∈ regionOf id (fire {0} (Commit.makeOne 2 : Commit Nat Nat)) bidSpace :=
      mem_regionOf.mpr ⟨mem_fire.mpr (Or.inr (Finset.mem_singleton_self 2)), rfl⟩
    have impossible : 4 ≤ 1 := accepted.2 2 rival
    exact (by decide : ¬ 4 ≤ 1) impossible

def bidRead : Commit Nat Nat := ⟨∅, ∅, ∅, [⟨bidSpace, {0}⟩]⟩

theorem outside_write_commutes_with_exact_read :
    Enabled id (fire {0} bidRead) (Commit.makeOne 1 : Commit Nat Nat) ∧
      Enabled id (fire {0} (Commit.makeOne 1 : Commit Nat Nat)) bidRead ∧
      fire (fire {0} bidRead) (Commit.makeOne 1 : Commit Nat Nat) =
        fire (fire {0} (Commit.makeOne 1 : Commit Nat Nat)) bidRead := by
  apply commute_disjoint_scopes (left := bidSpace) (right := fun o => !bidSpace o)
  · intro o both opposite
    simp only [both, Bool.not_true, Bool.false_eq_true] at opposite
  · refine ⟨by simp [bidRead], by simp [bidRead], by simp [bidRead], ?_⟩
    intro q member
    have eq : q = ⟨bidSpace, {0}⟩ := List.mem_singleton.mp member
    subst q
    exact fun _ inside => inside
  · refine ⟨by simp, by simp, ?_, by simp⟩
    intro o member
    have same : o = 1 := Finset.mem_singleton.mp member
    subst o
    rfl
  · decide
  · decide

/-- A shared linear token is not independent just because neither
commit contains a whole-region observation. -/
theorem positive_shared_take_does_not_commute_in_admission :
    ¬ Enabled (id : Nat → Nat) (fire {0} (Commit.takeOne 0 : Commit Nat Nat)) (Commit.takeOne 0) := by
  decide

end Controls

#print axioms observes_fire_outside
#print axioms commute_disjoint_scopes
#print axioms minimum_of_exact_cut
#print axioms minimum_fire_outside
#print axioms minimum_survives_nonbeating_writer
#print axioms Controls.cheaper_elsewhere_preserves_choice
#print axioms Controls.cheaper_here_refuses_even_with_chosen_present
#print axioms Controls.outside_write_commutes_with_exact_read
#print axioms Controls.positive_shared_take_does_not_commute_in_admission

end Mettapedia.GSLT.Compilation.LocalReadScope
