import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Exactness

/-!
# Transporting observed-region conditions through a commit

A query after a commit is not generally the same query before it. Its expected
occurrences must first lose the commit's fresh output and regain the matching
occurrences that the commit consumes. Two finite compatibility checks account
for impossible observations of the output or of consumed occurrences.

The construction operates on the existing query and commit representations.
The equivalence is proved against their independent store semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v

variable {O : Type u} [DecidableEq O] {R : Type v}

namespace PredicateQuery

/-- The query's required observation before `c` fires. -/
def pullback (q : PredicateQuery O R) (label : O → R) (c : Commit O R) :
    PredicateQuery O R where
  region := q.region
  seen := (q.seen \ c.made) ∪ regionOf label c.taken q.region

/-- Output membership and consumed-occurrence checks independent of the store. -/
def Compatible (q : PredicateQuery O R) (label : O → R) (c : Commit O R) : Prop :=
  q.seen ∩ c.made = regionOf label c.made q.region ∧ Disjoint q.seen c.taken

instance (q : PredicateQuery O R) (label : O → R) (c : Commit O R) :
    Decidable (q.Compatible label c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Transport of an exact observation, including the fixed compatibility checks. -/
theorem holds_fire_iff_pullback (q : PredicateQuery O R) (label : O → R)
    (store : Finset O) (c : Commit O R) (taken : c.taken ⊆ store)
    (fresh : Disjoint c.made store) :
    q.Holds label (fire store c) ↔
      q.Compatible label c ∧ (q.pullback label c).Holds label store := by
  have fresh' := Finset.disjoint_left.mp fresh
  simp only [Holds, Compatible, pullback]
  constructor
  · intro h
    have hmem (o : O) := Finset.ext_iff.mp h o
    simp only [mem_regionOf, mem_fire] at hmem
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · ext o
      simp only [Finset.mem_inter, mem_regionOf]
      have := hmem o
      grind
    · apply Finset.disjoint_left.mpr
      intro o seen consumed
      have := hmem o
      have := fresh' (a := o)
      have := taken consumed
      grind
    · ext o
      simp only [Finset.mem_union, Finset.mem_sdiff, mem_regionOf]
      have := hmem o
      have := fresh' (a := o)
      have := taken (x := o)
      grind
  · rintro ⟨⟨output, removed⟩, input⟩
    have removed' := Finset.disjoint_left.mp removed
    ext o
    have hm := Finset.ext_iff.mp output o
    have hi := Finset.ext_iff.mp input o
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, mem_regionOf] at hm hi
    simp only [mem_regionOf, mem_fire]
    have := removed' (a := o)
    have := fresh' (a := o)
    grind

/-- Enabledness supplies precisely the hypotheses used by query transport. -/
theorem holds_fire_iff_of_enabled (q : PredicateQuery O R) {label : O → R}
    {store : Finset O} {c : Commit O R} (enabled : Enabled label store c) :
    q.Holds label (fire store c) ↔
      q.Compatible label c ∧ (q.pullback label c).Holds label store :=
  q.holds_fire_iff_pullback label store c enabled.taken_subset enabled.fresh

end PredicateQuery

/-- A required occurrence after an update either comes from the output, or
must already exist and survive consumption. -/
theorem subset_fire_iff (required store : Finset O) (c : Commit O R) :
    required ⊆ fire store c ↔
      required \ c.made ⊆ store ∧ Disjoint (required \ c.made) c.taken := by
  simp only [Finset.subset_iff, mem_fire, Finset.mem_sdiff, Finset.disjoint_left]
  constructor
  · intro h
    constructor <;> intro o
    · intro member
      have := h member.1
      grind
    · intro member taken
      have := h member.1
      grind
  · rintro ⟨present, apart⟩ o member
    by_cases made : o ∈ c.made
    · exact Or.inr made
    · exact Or.inl ⟨present ⟨member, made⟩, apart ⟨member, made⟩⟩

/-- An excluded occurrence after an update must be absent from the output;
an old occurrence need only be excluded if it is not consumed. -/
theorem disjoint_fire_iff (excluded store : Finset O) (c : Commit O R) :
    Disjoint excluded (fire store c) ↔
      Disjoint excluded c.made ∧ Disjoint (excluded \ c.taken) store := by
  simp only [Finset.disjoint_left, mem_fire, Finset.mem_sdiff]
  constructor
  · intro h
    exact ⟨fun o excluded made => h excluded (Or.inr made),
      fun o excluded present => h excluded.1 (Or.inl ⟨present, excluded.2⟩)⟩
  · rintro ⟨output, initial⟩ o excluded (old | made)
    · exact initial ⟨excluded, old.2⟩ old.1
    · exact output excluded made

/-- Transport the complete list, preserving query occurrences and order. -/
theorem queries_hold_fire_iff (qs : List (PredicateQuery O R)) {label : O → R}
    {store : Finset O} {c : Commit O R} (enabled : Enabled label store c) :
    (∀ q ∈ qs, q.Holds label (fire store c)) ↔
      (∀ q ∈ qs, q.Compatible label c) ∧
        ∀ q ∈ qs.map (fun q => q.pullback label c), q.Holds label store := by
  constructor
  · intro h
    refine ⟨fun q member => ((q.holds_fire_iff_of_enabled enabled).mp (h q member)).1, ?_⟩
    intro q member
    obtain ⟨original, inQs, rfl⟩ := List.mem_map.mp member
    exact ((original.holds_fire_iff_of_enabled enabled).mp (h original inQs)).2
  · rintro ⟨compatible, before⟩ q member
    apply (q.holds_fire_iff_of_enabled enabled).mpr
    exact ⟨compatible q member, before _ (List.mem_map.mpr ⟨q, member, rfl⟩)⟩

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
