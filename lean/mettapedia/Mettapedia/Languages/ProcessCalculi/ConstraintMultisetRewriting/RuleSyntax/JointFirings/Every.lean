import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Members

/-!
# Every match of a rule, committed at once

## What "every match" quantifies over

A firing of a program carries an opening and the identities of its made rows, so one match has many
firings. What identifies a match is its key (`firingKey`, `Member.key`): the rule and the rows selected
for its take and read patterns. `every` quantifies over keys:

* a bag is **within** a set of rules when every member fires one of them (`Bag.Within`);
* it has **distinct** keys when no match occurs twice (`Bag.Distinct`);
* it is **complete** for the set of rules at a state when the key of every firing of one of the rules
  that the step of the program admits there is the key of a member (`Bag.Complete`).

**`every` over a set of rules** (`Bag.AdmitsEvery`) is: jointly admitted with the guards of each member
at its own information (so each member is itself an admitted firing: `Bag.admits_member`), within the
rules, with distinct keys, complete. A set of rules rather than one rule, so that a rule presented by
its instances is covered.

Completeness is an ask of admission, read at the entry state. It is the none query of a further match: a
statement over every selection of present rows and every opening, where a check or a collect query of the
rule reads the rows through one solution of the firing's information.

## What follows

* **The same matches** (`AdmitsEvery.keys_perm`): two bags admitted as `every` over one set of rules at
  one state have the same keys, each once. So they take the same rows (`AdmitsEvery.taken_iff`) and have
  as many members (`AdmitsEvery.length_eq`); they differ only by their openings, the identities of their
  made rows and the order of their members. `every` has at most one result up to these.
* **`every` cannot tell apart what no row tells apart** (`every_exchange`, `every_cannot_tell_apart`,
  `every_same_label`): a permutation of the occurrences that keeps labels and presence carries admitted
  firings to admitted firings (`exchanged_admits`), so a complete bag takes a present row exactly when
  it takes its image. In particular, of two present rows with one label, `every` takes both or neither.
  The step of the program takes one of them (`EveryControls`). So a step relation that has only `every`
  cannot fire exactly one of two matches that no row tells apart.

Conversely no finite program of the one-match step fires all matches at once
(`Representation.allAtOnce_not_finite`). Neither of `every` and `one` is a restriction of the other as a
step relation; both are restrictions of the bag step (`Bag.AdmitsEvery` implies `Bag.Admits`; one
member: `Singletons`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-! ## Keys, completeness, `every` -/

section Keys

variable {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

/-- **The key of a firing**: its rule and the rows selected for its take and read patterns. -/
def firingKey {a : Obj} (g : Firing O E P a) : Rule Tm × List O × List O :=
  (g.rule, g.selection.taken, g.selection.read)

theorem firingKey_firing {a : Obj} {x : E.Ext a} (m : Member O E P x) : firingKey m.firing = m.key :=
  rfl

namespace Bag

/-- Every member fires a rule of the set. -/
def Within {a : Obj} (Q : Set (Rule Tm)) (f : Bag O E P a) : Prop := ∀ m ∈ f.members, m.rule ∈ Q

/-- No match occurs twice. -/
def Distinct {a : Obj} (f : Bag O E P a) : Prop := (f.members.map Member.key).Nodup

/-- A present row is taken by the bag exactly when it is taken by the match of one of its keys. -/
theorem mem_taken_iff_key {a : Obj} (f : Bag O E P a) (o : O) :
    o ∈ f.selection.taken ↔ ∃ k ∈ f.members.map Member.key, o ∈ k.2.1 := by
  constructor
  · intro inside
    obtain ⟨m, inM, inTaken⟩ := List.mem_flatMap.mp inside
    exact ⟨m.key, List.mem_map_of_mem inM, inTaken⟩
  · rintro ⟨k, inside, inTaken⟩
    obtain ⟨m, inM, rfl⟩ := List.mem_map.mp inside
    exact List.mem_flatMap.mpr ⟨m, inM, inTaken⟩

variable (X : Frames Tm Hom) [DecidableEq O] (s : State Tm O)

/-- **Complete for a set of rules**: the key of every admitted firing of one of the rules is the key of
a member. -/
def Complete (Q : Set (Rule Tm)) (f : Bag O E P s.frame) : Prop :=
  ∀ g : Firing O E P s.frame, g.rule ∈ Q → g.Admits X s → firingKey g ∈ f.members.map Member.key

/-- **`every` over a set of rules**: jointly admitted with the guards of each member at its own
information, within the rules, each match once, every match. -/
def AdmitsEvery (Q : Set (Rule Tm)) (f : Bag O E P s.frame) : Prop :=
  f.AdmitsOwn X s ∧ f.Within Q ∧ f.Distinct ∧ f.Complete X s Q

variable {X s}

theorem AdmitsEvery.admits {Q : Set (Rule Tm)} {f : Bag O E P s.frame} (every : f.AdmitsEvery X s Q) :
    f.Admits X s := admits_of_admitsOwn X every.1

/-- **Two bags admitted as `every` have the same keys, each once.** -/
theorem AdmitsEvery.keys_perm (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b))
    {Q : Set (Rule Tm)} {f f' : Bag O E P s.frame} (first : f.AdmitsEvery X s Q)
    (second : f'.AdmitsEvery X s Q) :
    (f.members.map Member.key).Perm (f'.members.map Member.key) := by
  refine (List.perm_ext_iff_of_nodup first.2.2.1 second.2.2.1).mpr fun k => ?_
  constructor
  · intro inside
    obtain ⟨m, inM, rfl⟩ := List.mem_map.mp inside
    exact second.2.2.2 m.firing (first.2.1 m inM) (admits_member X inhabited first.1 inM)
  · intro inside
    obtain ⟨m, inM, rfl⟩ := List.mem_map.mp inside
    exact first.2.2.2 m.firing (second.2.1 m inM) (admits_member X inhabited second.1 inM)

/-- **They take the same rows.** -/
theorem AdmitsEvery.taken_iff (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b))
    {Q : Set (Rule Tm)} {f f' : Bag O E P s.frame} (first : f.AdmitsEvery X s Q)
    (second : f'.AdmitsEvery X s Q) (o : O) :
    o ∈ f.selection.taken ↔ o ∈ f'.selection.taken := by
  have same := first.keys_perm inhabited second
  rw [mem_taken_iff_key, mem_taken_iff_key]
  constructor
  · rintro ⟨k, inside, inTaken⟩
    exact ⟨k, same.mem_iff.mp inside, inTaken⟩
  · rintro ⟨k, inside, inTaken⟩
    exact ⟨k, same.mem_iff.mpr inside, inTaken⟩

/-- **They have as many members.** -/
theorem AdmitsEvery.length_eq (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b))
    {Q : Set (Rule Tm)} {f f' : Bag O E P s.frame} (first : f.AdmitsEvery X s Q)
    (second : f'.AdmitsEvery X s Q) : f.members.length = f'.members.length := by
  have same := (first.keys_perm inhabited second).length_eq
  rw [List.length_map, List.length_map] at same
  exact same

end Bag

end Keys

/-! ## Exchanging occurrences -/

section Exchange

variable (X : Frames Tm Hom) {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {P : Program Tm} {s : State Tm O}

/-- **A firing with its selected rows carried along a permutation of the occurrences.** The opening, the
made identities and the seen sets stay. -/
abbrev exchanged (π : Equiv.Perm O) (g : Firing O E P s.frame) : Firing O E P s.frame :=
  ⟨g.rule, g.member, g.ext, g.opening,
    ⟨g.selection.taken.map π, g.selection.read.map π, g.selection.made⟩, g.seen⟩

variable {π : Equiv.Perm O}

omit [DecidableEq O] in
theorem matching_exchanged (labels : ∀ o, s.label (π o) = s.label o) (g : Firing O E P s.frame)
    (patterns : List (Tm (E.target g.ext))) (selected : List O) :
    (exchanged π g).matching X s patterns (selected.map π) = g.matching X s patterns selected := by
  unfold Firing.matching
  rw [List.zipWith_map_right]
  exact Scope.zipWith_congr_right _ _ _ _ fun o _ p => by
    show (p, X.act (E.weaken g.ext) (s.label (π o))) = (p, X.act (E.weaken g.ext) (s.label o))
    rw [labels o]

omit [DecidableEq O] in
/-- **Exchanging rows with one label does not change the information.** -/
theorem exchanged_information (labels : ∀ o, s.label (π o) = s.label o) (g : Firing O E P s.frame) :
    (exchanged π g).information X s = g.information X s := by
  show X.applyStore (E.weaken g.ext) s.knowledge ++
      (exchanged π g).matching X s (g.opened X).take (g.selection.taken.map π) ++
      (exchanged π g).matching X s (g.opened X).read (g.selection.read.map π) ++ (g.opened X).tell =
    X.applyStore (E.weaken g.ext) s.knowledge ++ g.matching X s (g.opened X).take g.selection.taken ++
      g.matching X s (g.opened X).read g.selection.read ++ (g.opened X).tell
  rw [matching_exchanged X labels, matching_exchanged X labels]

/-- **A permutation of the occurrences that keeps labels and presence carries admitted firings to
admitted firings.** -/
theorem exchanged_admits (labels : ∀ o, s.label (π o) = s.label o)
    (present : ∀ o, π o ∈ s.present ↔ o ∈ s.present) {g : Firing O E P s.frame}
    (admitted : g.Admits X s) : (exchanged π g).Admits X s := by
  obtain ⟨⟨fresh, taken, made, takeLength, readLength, produceLength, collectLength⟩, enabled,
    solvable, asks⟩ := admitted
  have same := exchanged_information X labels g
  refine ⟨⟨fresh, taken.map π.injective, made, ?_, ?_, produceLength, collectLength⟩, ?_, ?_, ?_⟩
  · show g.rule.body.take.length = (g.selection.taken.map π).length
    rw [List.length_map]
    exact takeLength
  · show g.rule.body.read.length = (g.selection.read.map π).length
    rw [List.length_map]
    exact readLength
  · refine ⟨fun o member => ?_, fun o member => ?_, ?_, enabled.fresh, fun q member => ?_⟩
    · obtain ⟨o₀, inside, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
      exact (present o₀).mpr (enabled.taken_subset (List.mem_toFinset.mpr inside))
    · obtain ⟨o₀, inside, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
      exact (present o₀).mpr (enabled.kept_subset (List.mem_toFinset.mpr inside))
    · refine Finset.disjoint_left.mpr fun o isTaken isKept => ?_
      obtain ⟨o₁, inTaken, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp isTaken)
      obtain ⟨o₂, inRead, sameRow⟩ := List.mem_map.mp (List.mem_toFinset.mp isKept)
      have equal : o₂ = o₁ := π.injective sameRow
      exact Finset.disjoint_left.mp enabled.apart (List.mem_toFinset.mpr inTaken)
        (List.mem_toFinset.mpr (equal ▸ inRead))
    · simp [Selection.commit] at member
  · exact Eq.mpr (congrArg (fun store => X.Solvable store) same) solvable
  · intro b σ solved
    exact asks b σ (Eq.mp (congrArg (fun store => X.Models σ store) same) solved)

variable {X}

/-- **A complete bag takes a row only if it takes its image** under a permutation of the occurrences
that keeps labels and presence. -/
theorem every_exchange (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b))
    {Q : Set (Rule Tm)} {f : Bag O E P s.frame} (every : f.AdmitsEvery X s Q)
    (labels : ∀ o, s.label (π o) = s.label o) (present : ∀ o, π o ∈ s.present ↔ o ∈ s.present)
    {o : O} (isTaken : o ∈ f.selection.taken) : π o ∈ f.selection.taken := by
  obtain ⟨m, inM, inTaken⟩ := List.mem_flatMap.mp isTaken
  have admitted := Bag.admits_member X inhabited every.1 inM
  have listed := every.2.2.2 (exchanged π m.firing) (every.2.1 m inM)
    (exchanged_admits X labels present admitted)
  obtain ⟨m', inM', sameKey⟩ := List.mem_map.mp listed
  have sameTaken : m'.selection.taken = m.selection.taken.map π := congrArg (fun k => k.2.1) sameKey
  refine List.mem_flatMap.mpr ⟨m', inM', ?_⟩
  show π o ∈ m'.selection.taken
  rw [sameTaken]
  exact List.mem_map_of_mem inTaken

/-- **`every` cannot tell apart what no row tells apart**: after a complete bag, a present row is still
present exactly when its image under a permutation that keeps labels and presence is. -/
theorem every_cannot_tell_apart (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b))
    {Q : Set (Rule Tm)} {f : Bag O E P s.frame} (every : f.AdmitsEvery X s Q)
    (labels : ∀ o, s.label (π o) = s.label o) (present : ∀ o, π o ∈ s.present ↔ o ∈ s.present)
    {o : O} (here : o ∈ s.present) :
    o ∈ (f.result X s).present ↔ π o ∈ (f.result X s).present := by
  have enabled := every.1.2.1
  have notMade : ∀ o', o' ∈ s.present → o' ∉ (f.selection.commit (T := Unit)).made :=
    fun o' inside made => Finset.disjoint_left.mp enabled.fresh made inside
  have back : ∀ o', π.symm (π o') = o' := fun o' => π.symm_apply_apply o'
  have labels' : ∀ o', s.label (π.symm o') = s.label o' := fun o' => by
    have := labels (π.symm o')
    rw [π.apply_symm_apply] at this
    exact this.symm
  have present' : ∀ o', π.symm o' ∈ s.present ↔ o' ∈ s.present := fun o' => by
    have := present (π.symm o')
    rw [π.apply_symm_apply] at this
    exact this.symm
  have taken : o ∈ f.selection.taken ↔ π o ∈ f.selection.taken :=
    ⟨fun isTaken => every_exchange inhabited every labels present isTaken, fun isTaken => by
      have := every_exchange (π := π.symm) inhabited every labels' present' isTaken
      rw [back o] at this
      exact this⟩
  show o ∈ fire s.present (f.selection.commit (T := Unit)) ↔
    π o ∈ fire s.present (f.selection.commit (T := Unit))
  rw [mem_fire, mem_fire]
  constructor
  · rintro (⟨-, kept⟩ | made)
    · exact Or.inl ⟨(present o).mpr here, fun gone => kept
        (List.mem_toFinset.mpr (taken.mpr (List.mem_toFinset.mp gone)))⟩
    · exact absurd made (notMade o here)
  · rintro (⟨-, kept⟩ | made)
    · exact Or.inl ⟨here, fun gone => kept
        (List.mem_toFinset.mpr (taken.mp (List.mem_toFinset.mp gone)))⟩
    · exact absurd made (notMade (π o) ((present o).mpr here))

/-- **Of two present rows with one label, `every` takes both or neither.** -/
theorem every_same_label (inhabited : ∀ (r : Rule Tm) (b : Obj), Nonempty (Hom r.locals b))
    {Q : Set (Rule Tm)} {f : Bag O E P s.frame} (every : f.AdmitsEvery X s Q) {o₁ o₂ : O}
    (same : s.label o₁ = s.label o₂) (in₁ : o₁ ∈ s.present) (in₂ : o₂ ∈ s.present) :
    o₁ ∈ (f.result X s).present ↔ o₂ ∈ (f.result X s).present := by
  have labels : ∀ o, s.label (Equiv.swap o₁ o₂ o) = s.label o := by
    intro o
    by_cases first : o = o₁
    · rw [first, Equiv.swap_apply_left]
      exact same.symm
    · by_cases second : o = o₂
      · rw [second, Equiv.swap_apply_right]
        exact same
      · rw [Equiv.swap_apply_of_ne_of_ne first second]
  have present : ∀ o, Equiv.swap o₁ o₂ o ∈ s.present ↔ o ∈ s.present := by
    intro o
    by_cases first : o = o₁
    · rw [first, Equiv.swap_apply_left]
      exact ⟨fun _ => in₁, fun _ => in₂⟩
    · by_cases second : o = o₂
      · rw [second, Equiv.swap_apply_right]
        exact ⟨fun _ => in₂, fun _ => in₁⟩
      · rw [Equiv.swap_apply_of_ne_of_ne first second]
  have moved := every_cannot_tell_apart (π := Equiv.swap o₁ o₂) inhabited every labels present in₁
  rw [Equiv.swap_apply_left] at moved
  exact moved

end Exchange

#print axioms Bag.mem_taken_iff_key
#print axioms Bag.AdmitsEvery.keys_perm
#print axioms Bag.AdmitsEvery.taken_iff
#print axioms Bag.AdmitsEvery.length_eq
#print axioms exchanged_information
#print axioms exchanged_admits
#print axioms every_exchange
#print axioms every_cannot_tell_apart
#print axioms every_same_label

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
