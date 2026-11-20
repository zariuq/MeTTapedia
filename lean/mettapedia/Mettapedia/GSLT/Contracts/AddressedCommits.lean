import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Waves

/-!
# Independence of addressed commits

An address is a function of a label, not an equality policy for labels.
Selected occurrences, predicate reads, and new occurrence identities have
different interference conditions. In particular a write to an address
is not by itself an interference with someone using a different occurrence
there. A predicate that observes the address may be spoiled by that write.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.AddressedCommits

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {O R Address : Type*} [DecidableEq O]
variable (label : O → R) (address : R → Address)

/-- Locations of selected positive witnesses. -/
def selected (c : Commit O R) : Set Address :=
  {location | ∃ o ∈ c.uses, address (label o) = location}

/-- Locations the queries could observe, also when there are no matching rows. -/
def observed (c : Commit O R) : Set Address :=
  {location | ∃ q ∈ c.queries, ∃ atom, q.region atom = true ∧ address atom = location}

def written (c : Commit O R) : Set Address :=
  {location | ∃ o ∈ c.writes, address (label o) = location}

omit [DecidableEq O] in
theorem observed_eq_empty_of_positive {c : Commit O R} (positive : c.Positive) :
    observed address c = ∅ := by
  ext location
  simp [observed, Commit.Positive] at positive ⊢
  simp [positive]

/-- Three checks suffice: separation of selected inputs, of writes from
the other queries, and of proposed output identities. Selected inputs
need not be separated from publication at the *address* level. -/
theorem independent_of_separated {c d : Commit O R}
    (inputs : Disjoint (selected label address c) (selected label address d))
    (writesC : Disjoint (written label address c) (observed address d))
    (writesD : Disjoint (written label address d) (observed address c))
    (fresh : Disjoint c.made d.made) :
    Independent label c d := by
  have uses : Disjoint c.uses d.uses := Finset.disjoint_left.mpr fun {o} hc hd =>
    Set.disjoint_left.mp inputs ⟨o, hc, rfl⟩ ⟨o, hd, rfl⟩
  have noSpoil {e f : Commit O R} (apart : Disjoint e.uses f.uses)
      (outside : Disjoint (written label address e) (observed address f)) :
      ¬ Spoils label e f := by
    rintro (takes | ⟨q, member, o, write, hit⟩)
    · apply takes
      exact Finset.disjoint_left.mpr fun {_} hc hd =>
        Finset.disjoint_left.mp apart (Commit.mem_uses.mpr (.inl hc)) (Commit.mem_uses.mpr (.inr hd))
    · exact Set.disjoint_left.mp outside ⟨o, write, rfl⟩ ⟨q, member, label o, hit, rfl⟩
  refine ⟨?_, noSpoil uses writesC, noSpoil uses.symm writesD⟩
  rintro (takes | sameOutput)
  · apply takes
    exact Finset.disjoint_left.mpr fun {_} hc hd =>
      Finset.disjoint_left.mp uses (Commit.mem_uses.mpr (.inl hc)) (Commit.mem_uses.mpr (.inl hd))
  · exact sameOutput fresh

theorem independent_of_positive {c d : Commit O R}
    (pc : c.Positive) (pd : d.Positive)
    (inputs : Disjoint (selected label address c) (selected label address d))
    (fresh : Disjoint c.made d.made) :
    Independent label c d :=
  independent_of_separated label address inputs
    (by simp [observed_eq_empty_of_positive address pd])
    (by simp [observed_eq_empty_of_positive address pc]) fresh

/-- A scheduler can choose any interleaving from a separated wave.
It does not choose which redexes comprise the wave. -/
theorem addressed_wave {store : Finset O} {wave ordered : List (Commit O R)}
    (enabled : ∀ c ∈ wave, Enabled label store c)
    (separated : wave.Pairwise fun c d =>
      Disjoint (selected label address c) (selected label address d) ∧
      Disjoint (written label address c) (observed address d) ∧
      Disjoint (written label address d) (observed address c) ∧
      Disjoint c.made d.made)
    (permutation : wave.Perm ordered) :
    Executable label store ordered ∧ fireList store ordered = fire store (effectOf wave) := by
  have pairs : wave.Pairwise (Independent label) := separated.imp fun separation =>
    independent_of_separated label address separation.1 separation.2.1
      separation.2.2.1 separation.2.2.2
  refine ⟨executable_of_pairwise_independent
    (fun c h => enabled c (permutation.symm.subset h))
    ((permutation.pairwise_iff (fun h => h.symm)).mp pairs), ?_⟩
  have matched := MatchedAt.of_enabled enabled
  exact (fireList_perm matched permutation).symm.trans (fireList_eq_fire_effectOf matched)

namespace Controls

/-- Two branches take different inputs and each publishes on the other's
channel. Their concrete selections do not read the new rows. -/
private def ports (o : Nat) : Bool := o == 0 || o == 3
private def first : Commit Nat Bool := ⟨{0}, ∅, {2}, []⟩
private def second : Commit Nat Bool := ⟨{1}, ∅, {3}, []⟩

theorem cross_channel_publication :
    Independent ports first second ∧
    ¬ Disjoint (written ports id first) (selected ports id second) := by
  constructor
  · refine independent_of_positive ports id (c := first) (d := second) rfl rfl ?_ ?_
    · rw [Set.disjoint_left]
      rintro loc ⟨o, ho, rfl⟩ ⟨p, hp, same⟩
      simp [first, Commit.uses] at ho
      simp [second, Commit.uses] at hp
      subst o p
      cases same
    · simp [first, second]
  · intro apart
    have inside : false ∈ written ports id first := ⟨2, by simp [first, Commit.writes], rfl⟩
    exact Set.disjoint_left.mp apart inside ⟨1, by simp [second, Commit.uses], rfl⟩

private def scansSecond : Commit Nat Bool :=
  { first with queries := [⟨fun x => !x, {1}⟩] }

/-- The addressed rule now asks for the entire second region. The
previous exact independence cannot be inferred from input channels. -/
theorem second_query_is_spoiled : ¬ Independent ports scansSecond second := by
  intro independent
  apply independent.2.2
  exact .inr ⟨_, List.mem_cons_self, 1, by simp [second], rfl⟩

end Controls

#print axioms independent_of_separated
#print axioms addressed_wave
#print axioms Controls.cross_channel_publication
#print axioms Controls.second_query_is_spoiled

end Mettapedia.GSLT.Contracts.AddressedCommits
