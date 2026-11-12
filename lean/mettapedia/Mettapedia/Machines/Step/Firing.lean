import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Tactic

/-!
# The algebra of a firing: frame, independence, and what `absent` changes

A store is a multiset of atoms.  A firing is a rule instance, its variables
already bound: the atoms it reads, the atoms it takes, a predicate no stored
atom may satisfy (its `absent` conditions), and the atoms it delivers.  It is
enabled when the takes are stored, each read atom is stored apart from the
takes, and no stored atom satisfies the predicate; firing removes the takes and
adds the outputs.  A rule is a firing for each binding (`Rule`).

* **Frame** (`frame`, `enabled_add_iff`): an enabled firing stays enabled in a
  larger store exactly when no added atom satisfies its `absent` predicate, and
  then it leaves the added atoms as they are.
* **Locality** (`enabled_congr`, `count_fire`): whether a firing is enabled
  depends only on the multiplicities of the atoms it reads and takes and on
  whether some stored atom satisfies its predicate; its effect on an atom's
  multiplicity is the atom's own takes and outputs.
* **`absent` is the non-monotone part** (`Enabled.mono`): with no stored atom
  satisfying the predicate, enabledness is preserved by any larger store.
  `Controls.absent_not_monotone` is the failure with one.
* **Independence** (`Indep`): the takes of both are stored together, each
  read atom is stored apart from both takes, and the outputs of each avoid the
  other's predicate.  Independent firings commute (`indep_commute`).  The
  relation is exact: the clause on outputs is necessary in every case
  (`commute_absent_exact`), and when neither firing's outputs are atoms the
  other reads or takes, commuting is equivalent to independence
  (`commute_iff_indep`).  When both orders are enabled the stores they reach
  are equal with no further condition (`fire_comm_of_enabled`).
* **Waves** (`Wave`, `wave_runs`, `wave_perm`): a list of firings whose takes
  are stored together, whose reads are stored apart from all the takes, and
  whose outputs pairwise avoid the others' predicates fires in any order, each
  enabled at its turn, to the same store.
* **Validation against one snapshot is not enough** (`join`,
  `Controls.write_skew`): two firings can each be enabled, their joint takes
  and reads be available, and still neither order fire both, because each
  delivers what the other requires absent.

The predicate is an arbitrary property of atoms, so the atoms an `absent`
condition watches need not be finitely many; independence only tests the
finitely many outputs against it.

Positive examples: `Controls.frame_example`, `Controls.commute_example`.
Negative examples: `Controls.absent_not_monotone`, `Controls.write_skew`,
`Controls.read_take_conflict`, `Controls.pairwise_is_not_joint`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Step

/-- A rule instance: what it reads, takes, requires absent, and delivers. -/
structure Firing (α : Type*) where
  reads : Multiset α
  takes : Multiset α
  absent : α → Prop
  outputs : Multiset α

namespace Firing

variable {α : Type*} [DecidableEq α]

/-- The takes are stored, each read atom is stored apart from the takes, and no
stored atom satisfies the `absent` predicate. -/
def Enabled (f : Firing α) (s : Multiset α) : Prop :=
  f.takes ≤ s ∧ (∀ a ∈ f.reads, a ∈ s - f.takes) ∧ ∀ a ∈ s, ¬ f.absent a

/-- The store after the firing. -/
def fire (f : Firing α) (s : Multiset α) : Multiset α := s - f.takes + f.outputs

theorem mem_sub_iff {a : α} {s t : Multiset α} : a ∈ s - t ↔ t.count a < s.count a := by
  rw [← Multiset.count_pos, Multiset.count_sub]
  omega

theorem enabled_iff_count (f : Firing α) (s : Multiset α) :
    Enabled f s ↔ (∀ a, f.takes.count a ≤ s.count a) ∧
      (∀ a ∈ f.reads, f.takes.count a < s.count a) ∧ ∀ a ∈ s, ¬ f.absent a := by
  unfold Enabled
  rw [Multiset.le_iff_count]
  simp only [mem_sub_iff]

/-- **Locality of the effect.** -/
theorem count_fire (f : Firing α) (s : Multiset α) (a : α) :
    (fire f s).count a = s.count a - f.takes.count a + f.outputs.count a := by
  simp [fire, Multiset.count_add, Multiset.count_sub]

theorem mem_fire {f : Firing α} {s : Multiset α} {a : α} (mem : a ∈ fire f s) :
    a ∈ s ∨ a ∈ f.outputs := by
  rcases Multiset.mem_add.mp mem with h | h
  · exact Or.inl (Multiset.mem_of_le (Multiset.sub_le_self _ _) h)
  · exact Or.inr h

/-- **The frame property.**  An enabled firing fires alike beside any atoms
that do not satisfy its `absent` predicate, and leaves them as they are. -/
theorem frame {f : Firing α} {s : Multiset α} (en : Enabled f s) (fr : Multiset α)
    (clear : ∀ a ∈ fr, ¬ f.absent a) :
    Enabled f (s + fr) ∧ fire f (s + fr) = fire f s + fr := by
  rw [enabled_iff_count] at en ⊢
  obtain ⟨ht, hr, ha⟩ := en
  refine ⟨⟨fun a => ?_, fun a har => ?_, fun a has => ?_⟩, ?_⟩
  · rw [Multiset.count_add]
    have := ht a
    omega
  · rw [Multiset.count_add]
    have := hr a har
    omega
  · rcases Multiset.mem_add.mp has with h | h
    · exact ha a h
    · exact clear a h
  · ext a
    simp only [count_fire, Multiset.count_add]
    have := ht a
    omega

/-- The frames that keep an enabled firing enabled are exactly those that avoid
its `absent` predicate. -/
theorem enabled_add_iff {f : Firing α} {s : Multiset α} (en : Enabled f s) (fr : Multiset α) :
    Enabled f (s + fr) ↔ ∀ a ∈ fr, ¬ f.absent a :=
  ⟨fun h a ha => h.2.2 a (Multiset.mem_add.mpr (Or.inr ha)), fun h => (frame en fr h).1⟩

/-- **A firing depends only on its footprint**: the multiplicities of the atoms
it reads and takes, and whether a stored atom satisfies its predicate. -/
theorem enabled_congr (f : Firing α) {s s' : Multiset α}
    (same : ∀ a ∈ f.takes + f.reads, s.count a = s'.count a)
    (watch : (∃ a ∈ s, f.absent a) ↔ ∃ a ∈ s', f.absent a) :
    Enabled f s ↔ Enabled f s' := by
  have key : ∀ t t' : Multiset α, (∀ a ∈ f.takes + f.reads, t.count a = t'.count a) →
      ((∃ a ∈ t, f.absent a) ↔ ∃ a ∈ t', f.absent a) → Enabled f t → Enabled f t' := by
    intro t t' eq w en
    rw [enabled_iff_count] at en ⊢
    obtain ⟨ht, hr, ha⟩ := en
    refine ⟨fun a => ?_, fun a har => ?_, fun a hat hab => ?_⟩
    · by_cases mem : a ∈ f.takes
      · rw [← eq a (Multiset.mem_add.mpr (Or.inl mem))]
        exact ht a
      · rw [Multiset.count_eq_zero_of_notMem mem]
        exact Nat.zero_le _
    · rw [← eq a (Multiset.mem_add.mpr (Or.inr har))]
      exact hr a har
    · obtain ⟨b, hb, hbad⟩ := w.mpr ⟨a, hat, hab⟩
      exact ha b hb hbad
  exact ⟨key s s' same watch, key s' s (fun a ha => (same a ha).symm) watch.symm⟩

/-- **Without `absent`, enabledness is monotone in the store.** -/
theorem Enabled.mono {f : Firing α} {s s' : Multiset α} (en : Enabled f s) (le : s ≤ s')
    (clear : ∀ a ∈ s', ¬ f.absent a) : Enabled f s' :=
  ⟨en.1.trans le, fun a ha => Multiset.mem_of_le (tsub_le_tsub_right le _) (en.2.1 a ha), clear⟩

/-- Reads alone leave the store as it is. -/
theorem fire_of_reads {f : Firing α} (noTakes : f.takes = 0) (noOutputs : f.outputs = 0)
    (s : Multiset α) : fire f s = s := by
  simp [fire, noTakes, noOutputs]

/-! ## Independence -/

/-- Two firings are independent in a store: their takes are stored together,
each read atom is stored apart from both takes, and the outputs of each avoid
the other's `absent` predicate. -/
structure Indep (f g : Firing α) (s : Multiset α) : Prop where
  takes : f.takes + g.takes ≤ s
  readsLeft : ∀ a ∈ f.reads, a ∈ s - (f.takes + g.takes)
  readsRight : ∀ a ∈ g.reads, a ∈ s - (f.takes + g.takes)
  outLeft : ∀ a ∈ f.outputs, ¬ g.absent a
  outRight : ∀ a ∈ g.outputs, ¬ f.absent a

theorem Indep.symm {f g : Firing α} {s : Multiset α} (ind : Indep f g s) : Indep g f s where
  takes := by rw [add_comm]; exact ind.takes
  readsLeft := by rw [add_comm]; exact ind.readsRight
  readsRight := by rw [add_comm]; exact ind.readsLeft
  outLeft := ind.outRight
  outRight := ind.outLeft

/-- One half of the diamond: after `f`, the independent `g` is still enabled. -/
theorem Indep.enabled_after {f g : Firing α} {s : Multiset α} (ind : Indep f g s)
    (eg : Enabled g s) : Enabled g (fire f s) := by
  have ht := Multiset.le_iff_count.mp ind.takes
  rw [enabled_iff_count]
  refine ⟨fun a => ?_, fun a har => ?_, fun a mem => ?_⟩
  · have := ht a
    rw [Multiset.count_add] at this
    rw [count_fire]
    omega
  · have := mem_sub_iff.mp (ind.readsRight a har)
    rw [Multiset.count_add] at this
    rw [count_fire]
    omega
  · rcases mem_fire mem with h | h
    · exact eg.2.2 a h
    · exact ind.outLeft a h

/-- When both orders are enabled, they reach the same store. -/
theorem fire_comm_of_enabled {f g : Firing α} {s : Multiset α} (ef : Enabled f s)
    (eg : Enabled g s) (efg : Enabled g (fire f s)) (egf : Enabled f (fire g s)) :
    fire g (fire f s) = fire f (fire g s) := by
  ext a
  have h1 := Multiset.le_iff_count.mp ef.1 a
  have h2 := Multiset.le_iff_count.mp eg.1 a
  have h3 := Multiset.le_iff_count.mp efg.1 a
  have h4 := Multiset.le_iff_count.mp egf.1 a
  simp only [count_fire] at h3 h4 ⊢
  omega

/-- **Independent firings commute.**  Each stays enabled after the other, and
the two orders reach the same store. -/
theorem indep_commute {f g : Firing α} {s : Multiset α} (ef : Enabled f s) (eg : Enabled g s)
    (ind : Indep f g s) :
    Enabled g (fire f s) ∧ Enabled f (fire g s) ∧ fire g (fire f s) = fire f (fire g s) :=
  ⟨ind.enabled_after eg, ind.symm.enabled_after ef,
    fire_comm_of_enabled ef eg (ind.enabled_after eg) (ind.symm.enabled_after ef)⟩

/-- **The clause on outputs is necessary**: if `g` is still enabled after `f`,
no output of `f` satisfies `g`'s `absent` predicate. -/
theorem commute_absent_exact {f g : Firing α} {s : Multiset α} (efg : Enabled g (fire f s)) :
    ∀ a ∈ f.outputs, ¬ g.absent a :=
  fun a ha => efg.2.2 a (Multiset.mem_add.mpr (Or.inr ha))

/-- One firing's outputs are not atoms the other reads or takes. -/
def NoFeed (f g : Firing α) : Prop := ∀ a ∈ f.outputs, a ∉ g.takes ∧ a ∉ g.reads

/-- **Independence is exact.**  For two enabled firings neither of which
delivers an atom the other reads or takes, each stays enabled after the other
if and only if they are independent. -/
theorem commute_iff_indep {f g : Firing α} {s : Multiset α} (ef : Enabled f s)
    (eg : Enabled g s) (nf : NoFeed f g) (ng : NoFeed g f) :
    (Enabled g (fire f s) ∧ Enabled f (fire g s)) ↔ Indep f g s := by
  constructor
  · rintro ⟨efg, egf⟩
    have zero : ∀ {p q : Firing α}, NoFeed p q → ∀ a, a ∈ q.takes ∨ a ∈ q.reads →
        p.outputs.count a = 0 := by
      intro p q n a mem
      apply Multiset.count_eq_zero_of_notMem
      intro out
      rcases mem with h | h
      · exact (n a out).1 h
      · exact (n a out).2 h
    have tf := Multiset.le_iff_count.mp ef.1
    have tg := Multiset.le_iff_count.mp eg.1
    have tfg := Multiset.le_iff_count.mp efg.1
    refine ⟨Multiset.le_iff_count.mpr fun a => ?_, fun a har => ?_, fun a har => ?_,
      commute_absent_exact efg, commute_absent_exact egf⟩
    · rw [Multiset.count_add]
      by_cases mem : a ∈ g.takes
      · have h := tfg a
        rw [count_fire, zero nf a (Or.inl mem)] at h
        have := tf a
        omega
      · rw [Multiset.count_eq_zero_of_notMem mem]
        have := tf a
        omega
    · have h := mem_sub_iff.mp (egf.2.1 a har)
      rw [count_fire, zero ng a (Or.inr har)] at h
      rw [mem_sub_iff, Multiset.count_add]
      omega
    · have h := mem_sub_iff.mp (efg.2.1 a har)
      rw [count_fire, zero nf a (Or.inr har)] at h
      rw [mem_sub_iff, Multiset.count_add]
      omega
  · intro ind
    exact ⟨ind.enabled_after eg, ind.symm.enabled_after ef⟩

/-! ## The joint firing and waves -/

/-- Both firings as one. -/
def join (f g : Firing α) : Firing α where
  reads := f.reads + g.reads
  takes := f.takes + g.takes
  absent a := f.absent a ∨ g.absent a
  outputs := f.outputs + g.outputs

/-- The joint firing reaches the store the two reach in sequence. -/
theorem fire_join {f g : Firing α} {s : Multiset α} (ind : Indep f g s) :
    fire (join f g) s = fire g (fire f s) := by
  ext a
  have := Multiset.le_iff_count.mp ind.takes a
  rw [Multiset.count_add] at this
  simp only [count_fire, join, Multiset.count_add]
  omega

/-- The joint firing is enabled exactly when both are and their takes and
reads are available together.  The clause on outputs is not part of it. -/
theorem enabled_join_iff (f g : Firing α) (s : Multiset α) :
    Enabled (join f g) s ↔ Enabled f s ∧ Enabled g s ∧ f.takes + g.takes ≤ s ∧
      (∀ a ∈ f.reads, a ∈ s - (f.takes + g.takes)) ∧
      ∀ a ∈ g.reads, a ∈ s - (f.takes + g.takes) := by
  constructor
  · rintro ⟨ht, hr, ha⟩
    have left : ∀ a ∈ f.reads, a ∈ s - (f.takes + g.takes) :=
      fun a h => hr a (Multiset.mem_add.mpr (Or.inl h))
    have right : ∀ a ∈ g.reads, a ∈ s - (f.takes + g.takes) :=
      fun a h => hr a (Multiset.mem_add.mpr (Or.inr h))
    have weaken : ∀ {t : Multiset α} {a : α}, t ≤ f.takes + g.takes →
        a ∈ s - (f.takes + g.takes) → a ∈ s - t :=
      fun le mem => Multiset.mem_of_le (tsub_le_tsub_left le _) mem
    refine ⟨⟨(Multiset.le_add_right _ _).trans ht,
        fun a h => weaken (Multiset.le_add_right _ _) (left a h),
        fun a h bad => ha a h (Or.inl bad)⟩,
      ⟨(Multiset.le_add_left _ _).trans ht,
        fun a h => weaken (Multiset.le_add_left _ _) (right a h),
        fun a h bad => ha a h (Or.inr bad)⟩, ht, left, right⟩
  · rintro ⟨ef, eg, ht, left, right⟩
    refine ⟨ht, fun a h => ?_, fun a h bad => ?_⟩
    · rcases Multiset.mem_add.mp h with h | h
      · exact left a h
      · exact right a h
    · rcases bad with bad | bad
      · exact ef.2.2 a h bad
      · exact eg.2.2 a h bad

/-- All the takes of a list of firings. -/
def takesAll (fs : List (Firing α)) : Multiset α := (fs.map Firing.takes).sum

/-- All the outputs of a list of firings. -/
def outputsAll (fs : List (Firing α)) : Multiset α := (fs.map Firing.outputs).sum

/-- A wave: the takes are stored together, every read atom is stored apart
from all the takes, no stored atom satisfies any predicate, and the outputs of
any two avoid each other's predicates. -/
structure Wave (fs : List (Firing α)) (s : Multiset α) : Prop where
  takes : takesAll fs ≤ s
  reads : ∀ f ∈ fs, ∀ a ∈ f.reads, a ∈ s - takesAll fs
  absent : ∀ f ∈ fs, ∀ a ∈ s, ¬ f.absent a
  apart : fs.Pairwise fun f g =>
    (∀ a ∈ f.outputs, ¬ g.absent a) ∧ ∀ a ∈ g.outputs, ¬ f.absent a

/-- Firing a list in order: each must be enabled when its turn comes. -/
def Runs : List (Firing α) → Multiset α → Prop
  | [], _ => True
  | f :: fs, s => Enabled f s ∧ Runs fs (fire f s)

/-- The store a list of firings reaches, fired in order. -/
def fireAll (fs : List (Firing α)) (s : Multiset α) : Multiset α :=
  fs.foldl (fun acc f => fire f acc) s

/-- **A wave fires in the order given**, each firing enabled at its turn, and
reaches the store without all the takes and with all the outputs. -/
theorem wave_runs (fs : List (Firing α)) (s : Multiset α) (wave : Wave fs s) :
    Runs fs s ∧ fireAll fs s = s - takesAll fs + outputsAll fs := by
  induction fs generalizing s with
  | nil => simp [Runs, fireAll, takesAll, outputsAll]
  | cons f fs ih =>
    have tk := Multiset.le_iff_count.mp wave.takes
    have split : ∀ a, (takesAll (f :: fs)).count a = f.takes.count a + (takesAll fs).count a := by
      intro a
      simp [takesAll, Multiset.count_add]
    have en : Enabled f s := by
      rw [enabled_iff_count]
      refine ⟨fun a => ?_, fun a har => ?_, wave.absent f (List.mem_cons_self ..)⟩
      · have := tk a
        rw [split] at this
        omega
      · have := mem_sub_iff.mp (wave.reads f (List.mem_cons_self ..) a har)
        rw [split] at this
        omega
    have rest : Wave fs (fire f s) := by
      refine ⟨Multiset.le_iff_count.mpr fun a => ?_, fun g hg a har => ?_, fun g hg a mem => ?_,
        (List.pairwise_cons.mp wave.apart).2⟩
      · have := tk a
        rw [split] at this
        rw [count_fire]
        omega
      · have := mem_sub_iff.mp (wave.reads g (List.mem_cons_of_mem _ hg) a har)
        rw [split] at this
        rw [mem_sub_iff, count_fire]
        omega
      · rcases mem_fire mem with h | h
        · exact wave.absent g (List.mem_cons_of_mem _ hg) a h
        · exact ((List.pairwise_cons.mp wave.apart).1 g hg).1 a h
    obtain ⟨runs, eq⟩ := ih (fire f s) rest
    refine ⟨⟨en, runs⟩, ?_⟩
    change fireAll fs (fire f s) = _
    rw [eq]
    ext a
    have := tk a
    rw [split] at this
    simp only [Multiset.count_add, Multiset.count_sub, count_fire, split, outputsAll,
      List.map_cons, List.sum_cons]
    omega

/-- **A wave is a wave in every order**, and every order reaches the same
store. -/
theorem wave_perm {fs gs : List (Firing α)} {s : Multiset α} (wave : Wave fs s)
    (perm : fs.Perm gs) : Wave gs s ∧ fireAll gs s = fireAll fs s := by
  have tk : takesAll gs = takesAll fs := (perm.map _).sum_eq.symm
  have out : outputsAll gs = outputsAll fs := (perm.map _).sum_eq.symm
  have wave' : Wave gs s := by
    refine ⟨tk ▸ wave.takes, fun f hf => tk ▸ wave.reads f (perm.mem_iff.mpr hf),
      fun f hf => wave.absent f (perm.mem_iff.mpr hf), ?_⟩
    exact perm.pairwise wave.apart fun h => ⟨h.2, h.1⟩
  refine ⟨wave', ?_⟩
  rw [(wave_runs gs s wave').2, (wave_runs fs s wave).2, tk, out]

end Firing

/-- A rule: a firing for each binding of its variables. -/
structure Rule (β α : Type*) where
  inst : β → Firing α

namespace Rule

variable {α β : Type*} [DecidableEq α]

/-- The bindings under which the rule can fire. -/
def answers (r : Rule β α) (s : Multiset α) : Set β := {σ | (r.inst σ).Enabled s}

/-- A rule with no `absent` condition answers in a larger store whatever it
answered in a smaller one. -/
theorem answers_mono (r : Rule β α) (positive : ∀ σ a, ¬ (r.inst σ).absent a)
    {s s' : Multiset α} (le : s ≤ s') : r.answers s ⊆ r.answers s' :=
  fun σ en => Firing.Enabled.mono en le fun a _ => positive σ a

end Rule

namespace Firing.Controls

/-- Read `1`, take `2`, deliver `3`, with `9` required absent. -/
def move : Firing Nat := ⟨{1}, {2}, fun a => a = 9, {3}⟩

theorem move_enabled : move.Enabled {1, 2} := by
  refine ⟨by decide, by decide, fun a ha => ?_⟩
  have : a = 1 ∨ a = 2 := by simpa using ha
  change ¬ a = 9
  omega

/-- Positive: beside an atom `7` the firing fires alike and leaves `7`. -/
theorem frame_example :
    move.Enabled ({1, 2} + {7}) ∧ fire move ({1, 2} + {7}) = fire move {1, 2} + {7} :=
  frame move_enabled {7} fun a ha => by
    have : a = 7 := by simpa using ha
    change ¬ a = 9
    omega

/-- Negative: beside the atom `9` it is not enabled: `absent` is not monotone. -/
theorem absent_not_monotone : move.Enabled {1, 2} ∧ ¬ move.Enabled ({1, 2} + {9}) :=
  ⟨move_enabled, fun h => h.2.2 9 (by decide) rfl⟩

/-- Take `4`, deliver `5`. -/
def other : Firing Nat := ⟨0, {4}, fun _ => False, {5}⟩

theorem other_enabled : other.Enabled {1, 2, 4} :=
  ⟨by decide, by decide, fun _ _ h => h⟩

theorem move_enabled_wide : move.Enabled {1, 2, 4} := by
  refine ⟨by decide, by decide, fun a ha => ?_⟩
  have : a = 1 ∨ a = 2 ∨ a = 4 := by simpa using ha
  change ¬ a = 9
  omega

/-- Positive: the two are independent in `{1, 2, 4}` and commute. -/
theorem commute_example :
    fire other (fire move {1, 2, 4}) = fire move (fire other {1, 2, 4}) := by
  have ind : Indep move other {1, 2, 4} := by
    refine ⟨by decide, by decide, by decide, fun _ _ h => h, fun a ha => ?_⟩
    have : a = 5 := by simpa [other] using ha
    change ¬ a = 9
    omega
  exact (indep_commute move_enabled_wide other_enabled ind).2.2

/-- Deliver `1` unless `2` is stored. -/
def left : Firing Nat := ⟨0, 0, fun a => a = 2, {1}⟩

/-- Deliver `2` unless `1` is stored. -/
def right : Firing Nat := ⟨0, 0, fun a => a = 1, {2}⟩

/-- Negative: in the empty store both are enabled, and so is their joint
firing, whose takes and reads are empty; but after either one the other is
disabled.  A wave validated against one snapshot, without the clause on
outputs, is not a sequence of firings. -/
theorem write_skew :
    left.Enabled 0 ∧ right.Enabled 0 ∧ (join left right).Enabled 0 ∧
      ¬ right.Enabled (fire left 0) ∧ ¬ left.Enabled (fire right 0) := by
  refine ⟨⟨le_rfl, by simp [left], by simp⟩, ⟨le_rfl, by simp [right], by simp⟩,
    ⟨by simp [join, left, right], by simp [join, left, right], by simp⟩, ?_, ?_⟩
  · intro h
    exact h.2.2 1 (by simp [fire, left]) rfl
  · intro h
    exact h.2.2 2 (by simp [fire, right]) rfl

/-- Read `1`. -/
def reader : Firing Nat := ⟨{1}, 0, fun _ => False, 0⟩

/-- Take `1`. -/
def taker : Firing Nat := ⟨0, {1}, fun _ => False, 0⟩

/-- Negative: with one copy of `1` the reader and the taker are both enabled,
and the reader is disabled after the taker: a read conflicts with a take of
the same occurrence. -/
theorem read_take_conflict :
    reader.Enabled {1} ∧ taker.Enabled {1} ∧ ¬ reader.Enabled (fire taker {1}) := by
  refine ⟨⟨by simp [reader], by simp [reader], fun _ _ h => h⟩,
    ⟨le_rfl, by simp [taker], fun _ _ h => h⟩, fun h => ?_⟩
  have := h.2.1 1 (by simp [reader])
  simp [fire, taker, reader] at this

/-- Negative: three takers of `1` over two copies are pairwise independent, and
are no wave: independence of pairs does not give a joint firing. -/
theorem pairwise_is_not_joint :
    Indep taker taker ({1, 1} : Multiset Nat) ∧
      ¬ Wave [taker, taker, taker] ({1, 1} : Multiset Nat) := by
  refine ⟨⟨by decide, by simp [taker], by simp [taker], by simp [taker], by simp [taker]⟩,
    fun wave => ?_⟩
  have := wave.takes
  revert this
  decide

end Firing.Controls

end Mettapedia.Machines.Step
