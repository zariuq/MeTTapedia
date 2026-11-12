import Mettapedia.Machines.Step.Seeker
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Seekers are closed under intersection and dependent sum: the resumable join

A conjunctive query read one variable at a time is built from two operations
on ordered indexes.

* **Intersection** (`Seeker.inter`): the keys two indexes share, found by
  leapfrogging: search the first from the bound, search the second from the key
  found, and repeat from the second's answer until both agree.
* **Dependent sum** (`Seeker.sigma`): for each key `a` of an outer index, the
  keys of an inner index that depends on `a`, as pairs in lexicographic order.
  A search resumes inside the inner index of the bound's first component, and
  moves to the next outer key whose inner index is not empty.

Both produce lawful seekers (`leap_none`, `leap_some`, `sigmaSeek_none`,
`sigmaSeek_some`).  So a join of any number of variables, written as nested
sums of intersections, is itself a seeker, and everything proved of seekers
holds of it: its drain yields exactly the join in lexicographic order
(`Seeker.mem_drain`, `Seeker.drain_pairwise`), and it resumes from its last
answer alone (`Seeker.drain_resume`).  The state of a join that has yielded an
answer is that answer, as a bound.  It keeps no intermediate relation, and no
position in any of the indexes it reads.

The triangle query is the worked instance (`triangle`, `mem_triangle_keys`):
`R(a, b), S(b, c), T(a, c)` as a sum over `a`, a sum over `b`, and an
intersection for `c`.  `triangle_resume` states the resumption for it.

Positive example: `Controls.triangle_drain`, `Controls.triangle_after`.
Negative examples: `Controls.inner_resume_alone_loses` (resuming only the inner
index of the last answer, without moving to the next outer key, loses every
later answer) and `Controls.union_is_not_join` (taking the keys either index
holds is not the intersection).

The answers of a sum are counted from its parts without building a tuple
(`card_sigmaKeys`).

The searches a leapfrog makes are bounded by the keys of its first index still
admitted (`leapSeeks_le`), and a whole drain of an intersection by twice the
keys of its first index (`interDrainSeeks_le`).  Choosing the smaller index as the first one is the
caller's decision; its consequence for the triangle query is the subject of
`TriangleBound`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Step

namespace Seeker

section Intersection

variable {K : Type*} [LinearOrder K]

/-- The keys admitted by `ge y` are fewer than those admitted by a bound that
admits some key below `y`. -/
theorem card_ge_lt (X : Seeker K) {b : Bound K} {x y : K} (hx : X.seek b = some x)
    (lt : x < y) :
    (X.keys.filter (Bound.ge y).admits).card < (X.keys.filter b.admits).card := by
  have h := X.seek_some b x hx
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨fun z hz => ?_, fun eq => ?_⟩
  · have := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨this.1, Bound.admits_mono h.2.1 (le_trans (le_of_lt lt) this.2)⟩
  · have mem : x ∈ X.keys.filter b.admits := Finset.mem_filter.mpr ⟨h.1, h.2.1⟩
    rw [← eq] at mem
    exact not_le_of_gt lt (Finset.mem_filter.mp mem).2

/-- Leapfrog: the least key both indexes hold that the bound admits. -/
def leap (X Y : Seeker K) (b : Bound K) : Option K :=
  match _ : X.seek b with
  | none => none
  | some x =>
    match _ : Y.seek (.ge x) with
    | none => none
    | some y => if _ : y = x then some x else leap X Y (.ge y)
termination_by (X.keys.filter b.admits).card
decreasing_by
  have hy := Y.seek_some (.ge x) y ‹_›
  exact card_ge_lt X ‹_› (lt_of_le_of_ne hy.2.1 (Ne.symm ‹_›))

theorem leap_of_none (X Y : Seeker K) {b : Bound K} (hx : X.seek b = none) :
    leap X Y b = none := by
  rw [leap]
  split
  · rfl
  · rename_i x h; rw [hx] at h; cases h

theorem leap_of_some_none (X Y : Seeker K) {b : Bound K} {x : K} (hx : X.seek b = some x)
    (hy : Y.seek (.ge x) = none) : leap X Y b = none := by
  rw [leap]
  split
  · rfl
  · rename_i x' h
    rw [hx] at h
    cases h
    split
    · rfl
    · rename_i y h'; rw [hy] at h'; cases h'

theorem leap_of_some_some (X Y : Seeker K) {b : Bound K} {x y : K} (hx : X.seek b = some x)
    (hy : Y.seek (.ge x) = some y) :
    leap X Y b = if y = x then some x else leap X Y (.ge y) := by
  rw [leap]
  split
  · rename_i h; rw [hx] at h; cases h
  · rename_i x' h
    rw [hx] at h
    cases h
    split
    · rename_i h'; rw [hy] at h'; cases h'
    · rename_i y' h'
      rw [hy] at h'
      cases h'
      rfl

/-- Strong induction on the keys of `X` a bound still admits. -/
theorem leap_induction (X Y : Seeker K) {motive : Bound K → Prop}
    (step : ∀ b, (∀ x y, X.seek b = some x → Y.seek (.ge x) = some y → y ≠ x →
      motive (.ge y)) → motive b) (b : Bound K) : motive b := by
  induction h : (X.keys.filter b.admits).card using Nat.strong_induction_on generalizing b with
  | _ n ih =>
    apply step
    intro x y hx hy ne
    have hy' := Y.seek_some (.ge x) y hy
    exact ih _ (h ▸ card_ge_lt X hx (lt_of_le_of_ne hy'.2.1 (Ne.symm ne))) _ rfl

/-- The leapfrog answers the least shared key the bound admits, or that there
is none. -/
theorem leap_spec (X Y : Seeker K) (b : Bound K) :
    (leap X Y b = none → ∀ z ∈ X.keys ∩ Y.keys, ¬ b.admits z) ∧
    (∀ z, leap X Y b = some z →
      z ∈ X.keys ∩ Y.keys ∧ b.admits z ∧ ∀ w ∈ X.keys ∩ Y.keys, b.admits w → z ≤ w) := by
  induction b using leap_induction X Y with
  | step b ih =>
    cases hx : X.seek b with
    | none =>
      rw [leap_of_none X Y hx]
      refine ⟨fun _ z hz hb => ?_, fun z h => by cases h⟩
      exact X.seek_none b hx z (Finset.mem_inter.mp hz).1 hb
    | some x =>
      have sx := X.seek_some b x hx
      cases hy : Y.seek (.ge x) with
      | none =>
        rw [leap_of_some_none X Y hx hy]
        refine ⟨fun _ z hz hb => ?_, fun z h => by cases h⟩
        have hz' := Finset.mem_inter.mp hz
        exact Y.seek_none (.ge x) hy z hz'.2 (sx.2.2 z hz'.1 hb)
      | some y =>
        have sy := Y.seek_some (.ge x) y hy
        rw [leap_of_some_some X Y hx hy]
        by_cases same : y = x
        · rw [if_pos same]
          refine ⟨fun h => (by cases h), fun z h => ?_⟩
          cases h
          refine ⟨Finset.mem_inter.mpr ⟨sx.1, same ▸ sy.1⟩, sx.2.1, fun w hw hb => ?_⟩
          exact sx.2.2 w (Finset.mem_inter.mp hw).1 hb
        · rw [if_neg same]
          have onward := ih x y hx hy same
          have below : ∀ w ∈ X.keys ∩ Y.keys, b.admits w → y ≤ w := fun w hw hb =>
            sy.2.2 w (Finset.mem_inter.mp hw).2 (sx.2.2 w (Finset.mem_inter.mp hw).1 hb)
          refine ⟨fun h z hz hb => onward.1 h z hz (below z hz hb), fun z h => ?_⟩
          have hz := onward.2 z h
          exact ⟨hz.1, Bound.admits_mono sx.2.1 (le_trans sy.2.1 hz.2.1),
            fun w hw hb => hz.2.2 w hw (below w hw hb)⟩

/-- **Intersection of two seekers is a seeker.** -/
def inter (X Y : Seeker K) : Seeker K where
  keys := X.keys ∩ Y.keys
  seek := leap X Y
  seek_none b := (leap_spec X Y b).1
  seek_some b := (leap_spec X Y b).2

@[simp] theorem inter_keys (X Y : Seeker K) : (inter X Y).keys = X.keys ∩ Y.keys := rfl

/-- The searches one leapfrog makes, in both indexes together. -/
def leapSeeks (X Y : Seeker K) (b : Bound K) : Nat :=
  match _ : X.seek b with
  | none => 1
  | some x =>
    match _ : Y.seek (.ge x) with
    | none => 2
    | some y => if _ : y = x then 2 else 2 + leapSeeks X Y (.ge y)
termination_by (X.keys.filter b.admits).card
decreasing_by
  have hy := Y.seek_some (.ge x) y ‹_›
  exact card_ge_lt X ‹_› (lt_of_le_of_ne hy.2.1 (Ne.symm ‹_›))

/-- A leapfrog makes at most two searches for each key of its first index that
the bound admits, and one more.  The second index's size does not enter. -/
theorem leapSeeks_le (X Y : Seeker K) (b : Bound K) :
    leapSeeks X Y b ≤ 2 * (X.keys.filter b.admits).card + 1 := by
  induction b using leap_induction X Y with
  | step b ih =>
    rw [leapSeeks]
    split
    · omega
    · rename_i x hx
      have sx := X.seek_some b x hx
      have pos : 0 < (X.keys.filter b.admits).card :=
        Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨sx.1, sx.2.1⟩⟩
      split
      · omega
      · rename_i y hy
        split
        · omega
        · rename_i ne
          have sy := Y.seek_some (.ge x) y hy
          have fewer := card_ge_lt X hx (lt_of_le_of_ne sy.2.1 (Ne.symm ne))
          have := ih x y hx hy ne
          omega

theorem leapSeeks_of_none (X Y : Seeker K) {b : Bound K} (hx : X.seek b = none) :
    leapSeeks X Y b = 1 := by
  rw [leapSeeks]
  split
  · rfl
  · rename_i x h; rw [hx] at h; cases h

theorem leapSeeks_of_some_none (X Y : Seeker K) {b : Bound K} {x : K}
    (hx : X.seek b = some x) (hy : Y.seek (.ge x) = none) : leapSeeks X Y b = 2 := by
  rw [leapSeeks]
  split
  · rename_i h; rw [hx] at h; cases h
  · rename_i x' h
    rw [hx] at h
    cases h
    split
    · rfl
    · rename_i y h'; rw [hy] at h'; cases h'

theorem leapSeeks_of_some_some (X Y : Seeker K) {b : Bound K} {x y : K}
    (hx : X.seek b = some x) (hy : Y.seek (.ge x) = some y) :
    leapSeeks X Y b = if y = x then 2 else 2 + leapSeeks X Y (.ge y) := by
  rw [leapSeeks]
  split
  · rename_i h; rw [hx] at h; cases h
  · rename_i x' h
    rw [hx] at h
    cases h
    split
    · rename_i h'; rw [hy] at h'; cases h'
    · rename_i y' h'
      rw [hy] at h'
      cases h'
      rfl

/-- The account of one leapfrog: when it answers `z` it has spent at most two
searches for each key of its first index between the bound and `z`, `z`
included; those keys are never searched for again by a reader that goes on
past `z`. -/
theorem leapSeeks_account (X Y : Seeker K) (b : Bound K) :
    (leap X Y b = none → leapSeeks X Y b ≤ 2 * (X.keys.filter b.admits).card + 1) ∧
    (∀ z, leap X Y b = some z →
      leapSeeks X Y b + 2 * (X.keys.filter (Bound.gt z).admits).card ≤
        2 * (X.keys.filter b.admits).card) := by
  induction b using leap_induction X Y with
  | step b ih =>
    cases hx : X.seek b with
    | none =>
      rw [leap_of_none X Y hx, leapSeeks_of_none X Y hx]
      exact ⟨fun _ => by omega, fun z h => by cases h⟩
    | some x =>
      have sx := X.seek_some b x hx
      have pos : 0 < (X.keys.filter b.admits).card :=
        Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨sx.1, sx.2.1⟩⟩
      cases hy : Y.seek (.ge x) with
      | none =>
        rw [leap_of_some_none X Y hx hy, leapSeeks_of_some_none X Y hx hy]
        exact ⟨fun _ => by omega, fun z h => by cases h⟩
      | some y =>
        have sy := Y.seek_some (.ge x) y hy
        rw [leap_of_some_some X Y hx hy, leapSeeks_of_some_some X Y hx hy]
        by_cases same : y = x
        · rw [if_pos same, if_pos same]
          refine ⟨fun h => (by cases h), fun z h => ?_⟩
          cases h
          have := card_gt_lt X hx
          omega
        · rw [if_neg same, if_neg same]
          have fewer := card_ge_lt X hx (lt_of_le_of_ne sy.2.1 (Ne.symm same))
          have onward := ih x y hx hy same
          refine ⟨fun h => ?_, fun z h => ?_⟩
          · have := onward.1 h
            omega
          · have := onward.2 z h
            omega

/-- The searches a whole drain of the intersection makes: one leapfrog per
answer and one more that finds the end. -/
def interDrainSeeks (X Y : Seeker K) (b : Bound K) : Nat :=
  match _ : leap X Y b with
  | none => leapSeeks X Y b
  | some z => leapSeeks X Y b + interDrainSeeks X Y (.gt z)
termination_by ((inter X Y).keys.filter b.admits).card
decreasing_by exact card_gt_lt (inter X Y) ‹_›

/-- **Draining an intersection costs at most two searches for each key of its
first index, and one more**, however large the second index is and however many
keys the two share.  Reading the smaller index first therefore costs at most
`2 * min + 1`. -/
theorem interDrainSeeks_le (X Y : Seeker K) (b : Bound K) :
    interDrainSeeks X Y b ≤ 2 * (X.keys.filter b.admits).card + 1 := by
  induction b using bound_induction (inter X Y) with
  | step b ih =>
    rw [interDrainSeeks]
    split
    · rename_i h
      exact (leapSeeks_account X Y b).1 h
    · rename_i z h
      have := (leapSeeks_account X Y b).2 z h
      have := ih z h
      omega

end Intersection

section DependentSum

variable {A B : Type*} [LinearOrder A] [LinearOrder B]

/-- The pairs `(a, b)` with `a` an outer key and `b` a key of `a`'s inner index. -/
def sigmaKeys (X : Seeker A) (Y : A → Seeker B) : Finset (A ×ₗ B) :=
  X.keys.biUnion fun a => (Y a).keys.image fun b => toLex (a, b)

theorem mem_sigmaKeys (X : Seeker A) (Y : A → Seeker B) (a : A) (b : B) :
    toLex (a, b) ∈ sigmaKeys X Y ↔ a ∈ X.keys ∧ b ∈ (Y a).keys := by
  simp only [sigmaKeys, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨a', ha', b', hb', eq⟩
    have := toLex.injective eq
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨ha', hb'⟩
  · rintro ⟨ha, hb⟩
    exact ⟨a, ha, b, hb, rfl⟩

/-- **The answers of a dependent sum are counted from its parts**: the sum,
over the outer keys, of the inner indexes' sizes.  A count, an emptiness test
or any other fold over the answers needs no tuple to be built. -/
theorem card_sigmaKeys (X : Seeker A) (Y : A → Seeker B) :
    (sigmaKeys X Y).card = ∑ a ∈ X.keys, (Y a).keys.card := by
  unfold sigmaKeys
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun a _ => ?_
    exact Finset.card_image_of_injective _ fun b b' h => by
      simpa using toLex.injective h
  · intro a _ a' _ ne
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b', _, eq⟩ := Finset.mem_image.mp hp'
    have := toLex.injective eq
    simp only [Prod.mk.injEq] at this
    exact ne this.1.symm

/-- The first pair whose outer key the bound admits: outer keys with an empty
inner index are passed, one search each. -/
def scan (X : Seeker A) (Y : A → Seeker B) (bA : Bound A) : Option (A ×ₗ B) :=
  match _ : X.seek bA with
  | none => none
  | some a =>
    match (Y a).seek .all with
    | some b => some (toLex (a, b))
    | none => scan X Y (.gt a)
termination_by (X.keys.filter bA.admits).card
decreasing_by exact card_gt_lt X ‹_›

theorem scan_of_none (X : Seeker A) (Y : A → Seeker B) {bA : Bound A} (hx : X.seek bA = none) :
    scan X Y bA = none := by
  rw [scan]
  split
  · rfl
  · rename_i a h; rw [hx] at h; cases h

theorem scan_of_some (X : Seeker A) (Y : A → Seeker B) {bA : Bound A} {a : A}
    (hx : X.seek bA = some a) :
    scan X Y bA =
      match (Y a).seek .all with
      | some b => some (toLex (a, b))
      | none => scan X Y (.gt a) := by
  rw [scan]
  split
  · rename_i h; rw [hx] at h; cases h
  · rename_i a' h
    rw [hx] at h
    cases h
    rfl

theorem scan_spec (X : Seeker A) (Y : A → Seeker B) (bA : Bound A) :
    (scan X Y bA = none → ∀ a b, toLex (a, b) ∈ sigmaKeys X Y → ¬ bA.admits a) ∧
    (∀ p, scan X Y bA = some p →
      p ∈ sigmaKeys X Y ∧ bA.admits (ofLex p).1 ∧
        ∀ a b, toLex (a, b) ∈ sigmaKeys X Y → bA.admits a → p ≤ toLex (a, b)) := by
  induction bA using bound_induction X with
  | step bA ih =>
    cases hx : X.seek bA with
    | none =>
      rw [scan_of_none X Y hx]
      refine ⟨fun _ a b hab hb => ?_, fun p h => by cases h⟩
      exact X.seek_none bA hx a ((mem_sigmaKeys X Y a b).mp hab).1 hb
    | some a =>
      have sa := X.seek_some bA a hx
      rw [scan_of_some X Y hx]
      cases hy : (Y a).seek .all with
      | some b =>
        have sb := (Y a).seek_some .all b hy
        refine ⟨fun h => (by cases h), fun p h => ?_⟩
        cases h
        refine ⟨(mem_sigmaKeys X Y a b).mpr ⟨sa.1, sb.1⟩, sa.2.1, fun a' b' hab hb => ?_⟩
        have mem := (mem_sigmaKeys X Y a' b').mp hab
        rcases lt_or_eq_of_le (sa.2.2 a' mem.1 hb) with lt | rfl
        · exact Prod.Lex.toLex_le_toLex.mpr (Or.inl lt)
        · exact Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨rfl, sb.2.2 b' mem.2 trivial⟩)
      | none =>
        have empty : ∀ b, b ∉ (Y a).keys := fun b hb => (Y a).seek_none .all hy b hb trivial
        have onward := ih a hx
        have past : ∀ a' b', toLex (a', b') ∈ sigmaKeys X Y → bA.admits a' → a < a' := by
          intro a' b' hab hb
          have mem := (mem_sigmaKeys X Y a' b').mp hab
          rcases lt_or_eq_of_le (sa.2.2 a' mem.1 hb) with lt | rfl
          · exact lt
          · exact absurd mem.2 (empty b')
        refine ⟨fun h a' b' hab hb => onward.1 h a' b' hab (past a' b' hab hb), fun p h => ?_⟩
        have hp := onward.2 p h
        exact ⟨hp.1, Bound.admits_mono sa.2.1 (le_of_lt hp.2.1),
          fun a' b' hab hb => hp.2.2 a' b' hab (past a' b' hab hb)⟩

/-- Resume at outer key `a` with an inner bound: the inner index of `a` first,
then the outer keys past `a`. -/
def resume (X : Seeker A) (Y : A → Seeker B) (a : A) (bB : Bound B) : Option (A ×ₗ B) :=
  match X.seek (.ge a) with
  | none => none
  | some a' =>
    if a' = a then
      match (Y a).seek bB with
      | some b => some (toLex (a, b))
      | none => scan X Y (.gt a)
    else scan X Y (.ge a')

theorem resume_spec (X : Seeker A) (Y : A → Seeker B) (a : A) (bB : Bound B) :
    (resume X Y a bB = none → ∀ a' b', toLex (a', b') ∈ sigmaKeys X Y →
      ¬ (a < a' ∨ a = a' ∧ bB.admits b')) ∧
    (∀ p, resume X Y a bB = some p →
      p ∈ sigmaKeys X Y ∧ (a < (ofLex p).1 ∨ a = (ofLex p).1 ∧ bB.admits (ofLex p).2) ∧
        ∀ a' b', toLex (a', b') ∈ sigmaKeys X Y → (a < a' ∨ a = a' ∧ bB.admits b') →
          p ≤ toLex (a', b')) := by
  unfold resume
  cases hx : X.seek (.ge a) with
  | none =>
    refine ⟨fun _ a' b' hab adm => ?_, fun p h => by cases h⟩
    have mem := (mem_sigmaKeys X Y a' b').mp hab
    refine X.seek_none (.ge a) hx a' mem.1 ?_
    rcases adm with lt | ⟨rfl, _⟩
    · exact le_of_lt lt
    · exact le_rfl
  | some a₁ =>
    have sa := X.seek_some (.ge a) a₁ hx
    by_cases same : a₁ = a
    · subst same
      simp only [if_true]
      cases hy : (Y a₁).seek bB with
      | some b =>
        have sb := (Y a₁).seek_some bB b hy
        refine ⟨fun h => (by cases h), fun p h => ?_⟩
        cases h
        refine ⟨(mem_sigmaKeys X Y a₁ b).mpr ⟨sa.1, sb.1⟩, Or.inr ⟨rfl, sb.2.1⟩,
          fun a' b' hab adm => ?_⟩
        have mem := (mem_sigmaKeys X Y a' b').mp hab
        rcases adm with lt | ⟨rfl, hb⟩
        · exact Prod.Lex.toLex_le_toLex.mpr (Or.inl lt)
        · exact Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨rfl, sb.2.2 b' mem.2 hb⟩)
      | none =>
        have onward := scan_spec X Y (.gt a₁)
        have later : ∀ a' b', toLex (a', b') ∈ sigmaKeys X Y →
            (a₁ < a' ∨ a₁ = a' ∧ bB.admits b') → a₁ < a' := by
          intro a' b' hab adm
          rcases adm with lt | ⟨rfl, hb⟩
          · exact lt
          · exact absurd hb ((Y a₁).seek_none bB hy b' ((mem_sigmaKeys X Y a₁ b').mp hab).2)
        refine ⟨fun h a' b' hab adm => onward.1 h a' b' hab (later a' b' hab adm), fun p h => ?_⟩
        have hp := onward.2 p h
        exact ⟨hp.1, Or.inl hp.2.1, fun a' b' hab adm => hp.2.2 a' b' hab (later a' b' hab adm)⟩
    · simp only [if_neg same]
      have lt : a < a₁ := lt_of_le_of_ne sa.2.1 (Ne.symm same)
      have onward := scan_spec X Y (.ge a₁)
      have later : ∀ a' b', toLex (a', b') ∈ sigmaKeys X Y →
          (a < a' ∨ a = a' ∧ bB.admits b') → a₁ ≤ a' := by
        intro a' b' hab adm
        have mem := (mem_sigmaKeys X Y a' b').mp hab
        refine sa.2.2 a' mem.1 ?_
        rcases adm with lt' | ⟨rfl, _⟩
        · exact le_of_lt lt'
        · exact le_rfl
      refine ⟨fun h a' b' hab adm => onward.1 h a' b' hab (later a' b' hab adm), fun p h => ?_⟩
      have hp := onward.2 p h
      exact ⟨hp.1, Or.inl (lt_of_lt_of_le lt hp.2.1),
        fun a' b' hab adm => hp.2.2 a' b' hab (later a' b' hab adm)⟩

/-- One search of the dependent sum. -/
def sigmaSeek (X : Seeker A) (Y : A → Seeker B) : Bound (A ×ₗ B) → Option (A ×ₗ B)
  | .all => scan X Y .all
  | .ge p => resume X Y (ofLex p).1 (.ge (ofLex p).2)
  | .gt p => resume X Y (ofLex p).1 (.gt (ofLex p).2)

theorem sigmaSeek_none (X : Seeker A) (Y : A → Seeker B) (b : Bound (A ×ₗ B))
    (h : sigmaSeek X Y b = none) : ∀ q ∈ sigmaKeys X Y, ¬ b.admits q := by
  intro q hq
  obtain ⟨⟨a', b'⟩, rfl⟩ := toLex.surjective q
  cases b with
  | all => exact fun _ => (scan_spec X Y .all).1 h a' b' hq trivial
  | ge p =>
    obtain ⟨⟨a, b₀⟩, rfl⟩ := toLex.surjective p
    exact fun adm => (resume_spec X Y a (.ge b₀)).1 h a' b' hq (Prod.Lex.toLex_le_toLex.mp adm)
  | gt p =>
    obtain ⟨⟨a, b₀⟩, rfl⟩ := toLex.surjective p
    exact fun adm => (resume_spec X Y a (.gt b₀)).1 h a' b' hq (Prod.Lex.toLex_lt_toLex.mp adm)

theorem sigmaSeek_some (X : Seeker A) (Y : A → Seeker B) (b : Bound (A ×ₗ B)) (p : A ×ₗ B)
    (h : sigmaSeek X Y b = some p) :
    p ∈ sigmaKeys X Y ∧ b.admits p ∧ ∀ q ∈ sigmaKeys X Y, b.admits q → p ≤ q := by
  cases b with
  | all =>
    have hp := (scan_spec X Y .all).2 p h
    refine ⟨hp.1, trivial, fun q hq _ => ?_⟩
    obtain ⟨⟨a', b'⟩, rfl⟩ := toLex.surjective q
    exact hp.2.2 a' b' hq trivial
  | ge p₀ =>
    obtain ⟨⟨a, b₀⟩, rfl⟩ := toLex.surjective p₀
    have hp := (resume_spec X Y a (.ge b₀)).2 p h
    obtain ⟨⟨pa, pb⟩, rfl⟩ := toLex.surjective p
    refine ⟨hp.1, Prod.Lex.toLex_le_toLex.mpr hp.2.1, fun q hq adm => ?_⟩
    obtain ⟨⟨a', b'⟩, rfl⟩ := toLex.surjective q
    exact hp.2.2 a' b' hq (Prod.Lex.toLex_le_toLex.mp adm)
  | gt p₀ =>
    obtain ⟨⟨a, b₀⟩, rfl⟩ := toLex.surjective p₀
    have hp := (resume_spec X Y a (.gt b₀)).2 p h
    obtain ⟨⟨pa, pb⟩, rfl⟩ := toLex.surjective p
    refine ⟨hp.1, Prod.Lex.toLex_lt_toLex.mpr hp.2.1, fun q hq adm => ?_⟩
    obtain ⟨⟨a', b'⟩, rfl⟩ := toLex.surjective q
    exact hp.2.2 a' b' hq (Prod.Lex.toLex_lt_toLex.mp adm)

/-- **The dependent sum of seekers is a seeker**, over pairs in lexicographic
order. -/
def sigma (X : Seeker A) (Y : A → Seeker B) : Seeker (A ×ₗ B) where
  keys := sigmaKeys X Y
  seek := sigmaSeek X Y
  seek_none := sigmaSeek_none X Y
  seek_some := sigmaSeek_some X Y

@[simp] theorem sigma_keys (X : Seeker A) (Y : A → Seeker B) :
    (sigma X Y).keys = sigmaKeys X Y := rfl

end DependentSum

section Triangle

variable {K : Type*} [LinearOrder K]

/-- The second components of the pairs of `R` whose first component is `a`. -/
def row (R : Finset (K × K)) (a : K) : Finset K := (R.filter fun p => p.1 = a).image Prod.snd

theorem mem_row (R : Finset (K × K)) (a b : K) : b ∈ row R a ↔ (a, b) ∈ R := by
  simp only [row, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨a', b'⟩, ⟨mem, rfl⟩, rfl⟩
    exact mem
  · intro mem
    exact ⟨(a, b), ⟨mem, rfl⟩, rfl⟩

/-- The triangle query `R(a, b), S(b, c), T(a, c)` read a variable at a time:
`a` from the first columns of `R` and `T`, then `b` from `R`'s row of `a` and
the first column of `S`, then `c` from `S`'s row of `b` and `T`'s row of `a`.
`index` is any way of building a lawful index from a set of keys. -/
def triangle (index : Finset K → Seeker K) (R S T : Finset (K × K)) :
    Seeker (K ×ₗ K ×ₗ K) :=
  sigma (inter (index (R.image Prod.fst)) (index (T.image Prod.fst))) fun a =>
    sigma (inter (index (row R a)) (index (S.image Prod.fst))) fun b =>
      inter (index (row S b)) (index (row T a))

/-- **The triangle seeker holds exactly the triangles**, whatever lawful index
it reads. -/
theorem mem_triangle_keys (index : Finset K → Seeker K)
    (lawful : ∀ s, (index s).keys = s) (R S T : Finset (K × K)) (a b c : K) :
    toLex (a, toLex (b, c)) ∈ (triangle index R S T).keys ↔
      (a, b) ∈ R ∧ (b, c) ∈ S ∧ (a, c) ∈ T := by
  simp only [triangle, sigma_keys, mem_sigmaKeys, inter_keys, Finset.mem_inter, lawful, mem_row,
    Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨hab, _⟩, hbc, hac⟩
    exact ⟨hab, hbc, hac⟩
  · rintro ⟨hab, hbc, hac⟩
    exact ⟨⟨⟨(a, b), hab, rfl⟩, ⟨(a, c), hac, rfl⟩⟩, ⟨hab, ⟨(b, c), hbc, rfl⟩⟩, hbc, hac⟩

/-- **The join resumes from its last answer.**  A drain of the triangle query
stopped after the answer `t` continues from the bound `gt t`: no intermediate
relation, no binding stack and no position in any index is kept. -/
theorem triangle_resume (index : Finset K → Seeker K) (R S T : Finset (K × K))
    (b : Bound (K ×ₗ K ×ₗ K)) (pre post : List (K ×ₗ K ×ₗ K)) (t : K ×ₗ K ×ₗ K)
    (split : (triangle index R S T).drain b = pre ++ t :: post) :
    (triangle index R S T).drain (.gt t) = post :=
  drain_resume _ b pre post t split

/-- Two lawful indexes over the same relations give the same answers in the
same order. -/
theorem triangle_index_irrelevant (index index' : Finset K → Seeker K)
    (lawful : ∀ s, (index s).keys = s) (lawful' : ∀ s, (index' s).keys = s)
    (R S T : Finset (K × K)) (b : Bound (K ×ₗ K ×ₗ K)) :
    (triangle index R S T).drain b = (triangle index' R S T).drain b := by
  apply drain_eq_of_keys_eq
  ext p
  obtain ⟨⟨a, q⟩, rfl⟩ := toLex.surjective p
  obtain ⟨⟨b', c⟩, rfl⟩ := toLex.surjective q
  rw [mem_triangle_keys index lawful, mem_triangle_keys index' lawful']

end Triangle

namespace Controls

/-- Two triangles: `0, 1, 2` and `0, 1, 3`. -/
def R : Finset (Nat × Nat) := {(0, 1), (4, 5)}
def S : Finset (Nat × Nat) := {(1, 2), (1, 3), (5, 6)}
def T : Finset (Nat × Nat) := {(0, 2), (0, 3), (4, 7)}

theorem triangle_members (t : Nat ×ₗ Nat ×ₗ Nat) :
    t ∈ (triangle ofFinset R S T).keys ↔
      t = toLex (0, toLex (1, 2)) ∨ t = toLex (0, toLex (1, 3)) := by
  obtain ⟨⟨a, q⟩, rfl⟩ := toLex.surjective t
  obtain ⟨⟨b, c⟩, rfl⟩ := toLex.surjective q
  rw [mem_triangle_keys ofFinset (fun _ => rfl)]
  simp only [R, S, T, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
    EmbeddingLike.apply_eq_iff_eq]
  omega

/-- Positive: the answers after the first triangle are the second alone. -/
theorem triangle_after (t : Nat ×ₗ Nat ×ₗ Nat) :
    t ∈ (triangle ofFinset R S T).drain (.gt (toLex (0, toLex (1, 2)))) ↔
      t = toLex (0, toLex (1, 3)) := by
  rw [mem_drain, triangle_members]
  constructor
  · rintro ⟨rfl | rfl, adm⟩
    · exact absurd adm (lt_irrefl _)
    · rfl
  · rintro rfl
    refine ⟨Or.inr rfl, ?_⟩
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr
      (Or.inr ⟨rfl, by decide⟩)⟩)

/-- Positive: the drain's answers are the two triangles. -/
theorem triangle_drain (t : Nat ×ₗ Nat ×ₗ Nat) :
    t ∈ (triangle ofFinset R S T).drain .all ↔
      t = toLex (0, toLex (1, 2)) ∨ t = toLex (0, toLex (1, 3)) := by
  rw [mem_drain, triangle_members]
  exact ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

/-- Negative: a resumption that searches only the inner index of the last
answer's outer key.  After the last pair of outer key `0` it answers nothing,
though the pair `(1, 7)` remains. -/
theorem inner_resume_alone_loses :
    let X : Seeker Nat := ofFinset {0, 1}
    let Y : Nat → Seeker Nat := fun a => ofFinset (if a = 0 then {5} else {7})
    (Y 0).seek (.gt 5) = none ∧ toLex (1, 7) ∈ (sigma X Y).keys ∧
      (Bound.gt (toLex (0, 5))).admits (toLex ((1 : Nat), (7 : Nat))) := by
  refine ⟨by decide, ?_, ?_⟩
  · exact (mem_sigmaKeys _ _ 1 7).mpr ⟨by decide, by decide⟩
  · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by decide))

/-- Negative: the keys either index holds are not the keys both hold. -/
theorem union_is_not_join :
    (3 : Nat) ∈ (ofFinset ({1, 3} : Finset Nat)).keys ∪ (ofFinset ({1, 4} : Finset Nat)).keys ∧
      (3 : Nat) ∉ (inter (ofFinset {1, 3}) (ofFinset {1, 4})).keys := by
  decide

end Controls

end Seeker

end Mettapedia.Machines.Step
