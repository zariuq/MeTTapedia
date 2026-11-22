import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints.SetFootprints
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.DeltaMerge

/-!
# Waves of changes that read a pattern

`Regions.DeltaMerge` merges footprinted deltas, changes certified at a finite set
of reads and a finite set of writes, into one delta when they are independent in
pairs, in every order.  A change that reads every atom of a pattern does not fit:
its reads are not a finite set.

A **pattern delta** (`PatternDelta`) writes finitely many locations and reads the
locations that a Boolean predicate accepts.  Everything a wave needs holds of
them.

* `PatternDelta.seq`, `PatternDelta.seq_comm_of_independent`,
  `PatternDelta.seqAll_perm`: pattern deltas compose; two independent ones commute;
  deltas independent in pairs compose to one delta in every order.
* `PatternDelta.decidableIndependent`: independence is decided, by finitely many
  questions to the two predicates: one for each written location.
* `patternWaveMerge`: the merge of a wave, as an order-free merge of alternatives
  (`GSLT.Dynamics.ContextualDeltaHandlers.AlternativeMerge`), computed.
* `FootprintedDelta.toPatternDelta`, `toPatternDelta_independent_iff`: a
  footprinted delta is a pattern delta, with the same independence: the finite
  case is an instance.

An operation that needs it: `addWhereNoneOf pattern kind` adds an occurrence of a
kind where no kind that the pattern accepts is present.

* It reads the pattern and writes the kind (its certificate is a field).
* `addWhereNoneOf_reads_all`: every certificate of it covers every kind the
  pattern accepts.  So where the pattern accepts infinitely many kinds it has no
  finite footprint (`addWhereNoneOf_not_effectFootprinted`); the test of the whole
  bag of `FootprintedSpaceTransactions` is the case of the pattern that accepts
  everything.
* Over the numbers, with the pattern of the even ones: it is independent of an
  addition of an odd kind and commutes with it (`PatternControls.guard_and_odd`),
  and it is not independent of an addition of an even kind, which disables it
  (`PatternControls.guard_and_even`).

What a pattern delta does not cover: a change that writes a pattern.  Emptying a
whole bag writes every kind that is present, and is the change of no pattern
delta (`PatternControls.clear_is_no_patternDelta`).  Such a change has a
certificate at a set of writes (`SetEffectFootprinted`); a test of independence
between two of them compares two infinite sets, which for patterns is
unification.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
open Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers (AlternativeMerge)

universe u v

/-- **A pattern delta**: a partial change of a located state that writes finitely
many locations and reads the locations a Boolean predicate accepts, such as the
kinds a pattern matches. -/
@[ext] structure PatternDelta (Location : Type u) (Value : Type v) where
  /-- The locations the change reads: those the predicate accepts. -/
  reads : Location → Bool
  /-- The locations the change writes. -/
  writes : Finset Location
  /-- The change; `none` is a refusal. -/
  act : (Location → Value) → Option (Location → Value)
  /-- The change is certified at its footprint. -/
  certified : SetEffectFootprinted (fun source target => act source = some target)
    {location | reads location = true} ↑writes

variable {Location : Type u} {Value : Type v}

namespace PatternDelta

/-- The delta that changes nothing and reads nothing. -/
def empty : PatternDelta Location Value where
  reads _ := false
  writes := ∅
  act := some
  certified :=
    { preserves := fun same _ _ => by cases same; rfl
      frame := fun same framedSource _ => by
        cases same
        exact ⟨framedSource, rfl,
          fun _ inside => absurd (Finset.mem_coe.mp inside) (Finset.notMem_empty _),
          fun _ _ => rfl⟩ }

variable [DecidableEq Location]

/-- One delta after another: it reads what either reads and writes what either
writes. -/
def seq (first second : PatternDelta Location Value) : PatternDelta Location Value where
  reads location := first.reads location || second.reads location
  writes := first.writes ∪ second.writes
  act state := (first.act state).bind second.act
  certified := by
    have composed := first.certified.comp second.certified
    have sameReads : {location | (first.reads location || second.reads location) = true} =
        {location | first.reads location = true} ∪ {location | second.reads location = true} := by
      ext location
      exact Iff.of_eq (Bool.or_eq_true _ _)
    rw [sameReads, Finset.coe_union]
    constructor
    · intro source target fired
      exact composed.preserves (Option.bind_eq_some_iff.mp fired)
    · intro source target fired framedSource agrees
      obtain ⟨framedTarget, framedFired, written, outside⟩ :=
        composed.frame (Option.bind_eq_some_iff.mp fired) framedSource agrees
      exact ⟨framedTarget, Option.bind_eq_some_iff.mpr framedFired, written, outside⟩

theorem seq_assoc (first second third : PatternDelta Location Value) :
    (first.seq second).seq third = first.seq (second.seq third) := by
  apply PatternDelta.ext
  · funext location
    exact Bool.or_assoc _ _ _
  · exact Finset.union_assoc _ _ _
  · funext state
    exact Option.bind_assoc _ _ _

/-- **Independent pattern deltas**: the writes of each meet neither the reads nor
the writes of the other. -/
def Independent (first second : PatternDelta Location Value) : Prop :=
  SetIndependentEffects {location | first.reads location = true} ↑first.writes
    {location | second.reads location = true} ↑second.writes

/-- **Independence is decided**: one question to each predicate for each written
location. -/
instance decidableIndependent (first second : PatternDelta Location Value) :
    Decidable (first.Independent second) :=
  inferInstanceAs (Decidable
    (Disjoint (↑first.writes : Set Location)
        ({location | second.reads location = true} ∪ ↑second.writes) ∧
      Disjoint (↑second.writes : Set Location)
        ({location | first.reads location = true} ∪ ↑first.writes)))

omit [DecidableEq Location] in
theorem Independent.symm {first second : PatternDelta Location Value}
    (independent : first.Independent second) : second.Independent first :=
  SetIndependentEffects.symm independent

/-- **Independent pattern deltas commute**: either order is the same delta. -/
theorem seq_comm_of_independent {first second : PatternDelta Location Value}
    (independent : first.Independent second) : first.seq second = second.seq first := by
  apply PatternDelta.ext
  · funext location
    exact Bool.or_comm _ _
  · exact Finset.union_comm _ _
  · funext state
    exact first.certified.bind_comm second.certified independent state

/-- The deltas of a list, one after another. -/
def seqAll : List (PatternDelta Location Value) → PatternDelta Location Value :=
  List.foldr seq empty

/-- **Pattern deltas that are independent in pairs compose to one delta in every
order.** -/
theorem seqAll_perm {deltas reordered : List (PatternDelta Location Value)}
    (perm : deltas.Perm reordered) (independent : deltas.Pairwise Independent) :
    seqAll deltas = seqAll reordered := by
  induction perm with
  | nil => rfl
  | cons delta _ ih =>
      show delta.seq (seqAll _) = delta.seq (seqAll _)
      rw [ih (List.pairwise_cons.mp independent).2]
  | swap first second rest =>
      show second.seq (first.seq (seqAll rest)) = first.seq (second.seq (seqAll rest))
      rw [← seq_assoc, ← seq_assoc,
        seq_comm_of_independent ((List.pairwise_cons.mp independent).1 first List.mem_cons_self)]
  | trans firstPerm _ ihFirst ihSecond =>
      rw [ihFirst independent,
        ihSecond ((firstPerm.pairwise_iff Independent.symm).mp independent)]

end PatternDelta

variable [DecidableEq Location]

/-- **The merge of a wave of pattern deltas**: deltas that are independent in pairs
are put one after another; any other list is refused.  It does not depend on the
order of the deltas, by their footprints. -/
def patternWaveMerge : AlternativeMerge (PatternDelta Location Value) where
  merge deltas :=
    if deltas.Pairwise PatternDelta.Independent then some (PatternDelta.seqAll deltas) else none
  permutationInvariant := by
    intro first second perm
    by_cases independent : first.Pairwise PatternDelta.Independent
    · rw [if_pos independent,
        if_pos ((perm.pairwise_iff PatternDelta.Independent.symm).mp independent),
        PatternDelta.seqAll_perm perm independent]
    · rw [if_neg independent, if_neg fun reorderedIndependent =>
        independent
          ((perm.pairwise_iff PatternDelta.Independent.symm).mpr reorderedIndependent)]

/-- **A footprinted delta is a pattern delta**: its finite reads, as a predicate. -/
def FootprintedDelta.toPatternDelta (delta : FootprintedDelta Location Value) :
    PatternDelta Location Value where
  reads location := decide (location ∈ delta.reads)
  writes := delta.writes
  act := delta.act
  certified := by
    have sameReads : {location | decide (location ∈ delta.reads) = true} =
        (↑delta.reads : Set Location) := by
      ext location
      exact decide_eq_true_iff
    rw [sameReads]
    exact setEffectFootprinted_coe_iff.mpr delta.certified

/-- With the same independence: the finite case is an instance. -/
theorem toPatternDelta_independent_iff (first second : FootprintedDelta Location Value) :
    (FootprintedDelta.toPatternDelta first).Independent (FootprintedDelta.toPatternDelta second) ↔
      first.Independent second := by
  have sameReads : ∀ delta : FootprintedDelta Location Value,
      {location | decide (location ∈ delta.reads) = true} = (↑delta.reads : Set Location) :=
    fun delta => Set.ext fun _ => decide_eq_true_iff
  show SetIndependentEffects {location | decide (location ∈ first.reads) = true} ↑first.writes
    {location | decide (location ∈ second.reads) = true} ↑second.writes ↔ _
  rw [sameReads first, sameReads second]
  exact setIndependentEffects_coe_iff

/-! ## A guard that asks for the absence of a pattern -/

/-- Add one occurrence at a location: a pattern delta that reads nothing. -/
def addAt (kind : Location) : PatternDelta Location ℕ where
  reads _ := false
  writes := {kind}
  act state := some (state + Pi.single kind 1)
  certified :=
    { preserves := fun fired location outside => by
        cases fired
        have different : location ≠ kind := fun same =>
          outside (Finset.mem_coe.mpr (Finset.mem_singleton.mpr same))
        show _ + (Pi.single kind 1 : Location → ℕ) location = _
        rw [Pi.single_eq_of_ne different, add_zero]
      frame := fun fired framedSource agrees => by
        cases fired
        refine ⟨framedSource + Pi.single kind 1, rfl, fun location inside => ?_,
          fun location outside => ?_⟩
        · show _ + (Pi.single kind 1 : Location → ℕ) location =
            _ + (Pi.single kind 1 : Location → ℕ) location
          rw [agrees (Or.inr inside)]
        · have different : location ≠ kind := fun same =>
            outside (Finset.mem_coe.mpr (Finset.mem_singleton.mpr same))
          show _ + (Pi.single kind 1 : Location → ℕ) location = _
          rw [Pi.single_eq_of_ne different, add_zero] }

open Classical in
/-- **Add one occurrence of a kind where no kind the pattern accepts is present.**
It reads every kind of the pattern.  Whether the condition holds of an arbitrary
state is not computed; whether the delta is independent of another is. -/
noncomputable def addWhereNoneOf (pattern : Location → Bool) (kind : Location) :
    PatternDelta Location ℕ where
  reads := pattern
  writes := {kind}
  act state :=
    if ∀ location, pattern location = true → state location = 0 then
      some (state + Pi.single kind 1)
    else none
  certified :=
    { preserves := fun {source target} fired location outside => by
        split at fired
        · cases fired
          have different : location ≠ kind := fun same =>
            outside (Finset.mem_coe.mpr (Finset.mem_singleton.mpr same))
          show _ + (Pi.single kind 1 : Location → ℕ) location = _
          rw [Pi.single_eq_of_ne different, add_zero]
        · cases fired
      frame := fun {source target} fired framedSource agrees => by
        split at fired
        · next absent =>
          cases fired
          have framedAbsent : ∀ location, pattern location = true → framedSource location = 0 :=
            fun location accepted =>
              (agrees (Or.inl accepted)).symm.trans (absent location accepted)
          refine ⟨framedSource + Pi.single kind 1, if_pos framedAbsent, fun location inside => ?_,
            fun location outside => ?_⟩
          · show _ + (Pi.single kind 1 : Location → ℕ) location =
              _ + (Pi.single kind 1 : Location → ℕ) location
            rw [agrees (Or.inr inside)]
          · have different : location ≠ kind := fun same =>
              outside (Finset.mem_coe.mpr (Finset.mem_singleton.mpr same))
            show _ + (Pi.single kind 1 : Location → ℕ) location = _
            rw [Pi.single_eq_of_ne different, add_zero]
        · cases fired }

/-- It fires exactly where no kind of the pattern is present. -/
theorem addWhereNoneOf_act_eq_some_iff (pattern : Location → Bool) (kind : Location)
    (state target : Location → ℕ) :
    (addWhereNoneOf pattern kind).act state = some target ↔
      (∀ location, pattern location = true → state location = 0) ∧
        target = state + Pi.single kind 1 := by
  classical
  show (if ∀ location, pattern location = true → state location = 0 then
    some (state + Pi.single kind 1) else none) = some target ↔ _
  by_cases absent : ∀ location, pattern location = true → state location = 0
  · rw [if_pos absent]
    exact ⟨fun same => ⟨absent, (Option.some.inj same).symm⟩,
      fun ⟨_, same⟩ => congrArg some same.symm⟩
  · rw [if_neg absent]
    exact ⟨fun fired => (by cases fired), fun ⟨holds, _⟩ => absurd holds absent⟩

/-- **Every certificate of the guard covers every kind the pattern accepts.** -/
theorem addWhereNoneOf_reads_all (pattern : Location → Bool) (kind : Location)
    {reads writes : Set Location}
    (certified : SetEffectFootprinted
      (fun source target => (addWhereNoneOf pattern kind).act source = some target) reads writes) :
    {location | pattern location = true} ⊆ reads ∪ writes := by
  intro accepted isAccepted
  by_contra outside
  have fires : (addWhereNoneOf pattern kind).act 0 = some (0 + Pi.single kind 1) :=
    (addWhereNoneOf_act_eq_some_iff pattern kind 0 _).mpr ⟨fun _ _ => rfl, rfl⟩
  obtain ⟨framedTarget, framedFires, -, -⟩ :=
    certified.frame fires (Pi.single accepted 1) (by
      intro other inside
      have different : other ≠ accepted := fun same => outside (same ▸ inside)
      simp [different])
  have absent :=
    ((addWhereNoneOf_act_eq_some_iff pattern kind _ framedTarget).mp framedFires).1 accepted
      isAccepted
  simp at absent

/-- **Where the pattern accepts infinitely many kinds the guard has no finite
footprint.** -/
theorem addWhereNoneOf_not_effectFootprinted (pattern : Location → Bool) (kind : Location)
    (infinite : {location | pattern location = true}.Infinite) (reads writes : Finset Location) :
    ¬ EffectFootprinted
      (fun source target => (addWhereNoneOf pattern kind).act source = some target) reads
      writes := by
  intro certified
  have covers := addWhereNoneOf_reads_all pattern kind (setEffectFootprinted_coe_iff.mpr certified)
  rw [← Finset.coe_union] at covers
  exact infinite ((reads ∪ writes).finite_toSet.subset covers)

/-! ## Controls -/

namespace PatternControls

/-- The pattern that accepts the even numbers. -/
def evens (number : ℕ) : Bool := number % 2 == 0

/-- It accepts infinitely many kinds. -/
theorem evens_infinite : {number | evens number = true}.Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun number : ℕ => 2 * number)
    (fun first second same => by
      have equal : 2 * first = 2 * second := same
      omega)
    (fun number => by
      show (2 * number % 2 == 0) = true
      rw [Nat.mul_mod_right]
      rfl)

/-- **Positive, a pattern delta**: the addition at a location.  **Negative**: the
guard over the even numbers is the change of no footprinted delta: it has no
finite footprint. -/
theorem guard_has_no_finite_footprint (reads writes : Finset ℕ) :
    ¬ EffectFootprinted
      (fun source target => (addWhereNoneOf evens 1).act source = some target) reads writes :=
  addWhereNoneOf_not_effectFootprinted evens 1 evens_infinite reads writes

/-- So it is a pattern delta that comes from no footprinted delta. -/
theorem guard_is_no_footprintedDelta :
    ¬ ∃ delta : FootprintedDelta ℕ ℕ,
      (FootprintedDelta.toPatternDelta delta).act = (addWhereNoneOf evens 1).act := by
  rintro ⟨delta, same⟩
  have certified := delta.certified
  have sameAct : delta.act = (addWhereNoneOf evens 1).act := same
  rw [sameAct] at certified
  exact guard_has_no_finite_footprint delta.reads delta.writes certified

/-- **Negative, a pattern delta**: emptying the whole bag is the change of no
pattern delta.  It writes every kind that is present, and a pattern delta writes
finitely many locations; only its reads may be a pattern. -/
theorem clear_is_no_patternDelta :
    ¬ ∃ delta : PatternDelta ℕ ℕ, delta.act = fun _ => some 0 := by
  rintro ⟨delta, same⟩
  obtain ⟨outside, notWritten⟩ := Infinite.exists_notMem_finset delta.writes
  have fired : delta.act (Pi.single outside 1) = some 0 := by rw [same]
  have unchanged := delta.certified.preserves fired
    (fun written => notWritten (Finset.mem_coe.mp written))
  simp at unchanged

/-- **Positive, independence**: the guard over the even numbers and an addition
of the odd kind `3`.  The test is computed, and the two commute as deltas. -/
theorem guard_and_odd :
    (addWhereNoneOf evens 1).Independent (addAt 3) ∧
      (addWhereNoneOf evens 1).seq (addAt 3) = (addAt 3).seq (addWhereNoneOf evens 1) := by
  have independent : (addWhereNoneOf evens 1).Independent (addAt 3) := by decide
  exact ⟨independent, PatternDelta.seq_comm_of_independent independent⟩

/-- **Negative, independence**: an addition of the even kind `2`.  The test finds
it, and the addition disables the guard: after it the guard is refused, and
before it the guard fires. -/
theorem guard_and_even :
    ¬ (addWhereNoneOf evens 1).Independent (addAt 2) ∧
      ((addAt 2).act 0).bind (addWhereNoneOf evens 1).act = none ∧
      ((addWhereNoneOf evens 1).act 0).isSome = true := by
  refine ⟨by decide, ?_, ?_⟩
  · show (addWhereNoneOf evens 1).act (0 + Pi.single 2 1) = none
    cases fired : (addWhereNoneOf evens 1).act (0 + Pi.single 2 1) with
    | none => rfl
    | some target =>
        have absent := ((addWhereNoneOf_act_eq_some_iff evens 1 _ target).mp fired).1 2 rfl
        simp at absent
  · rw [(addWhereNoneOf_act_eq_some_iff evens 1 0 _).mpr ⟨fun _ _ => rfl, rfl⟩]
    rfl

/-- **Positive, the empty delta**: it fires on every state and leaves it.
**Negative**: an addition is not the empty delta: it changes the state. -/
theorem empty_instances (state : ℕ → ℕ) :
    (PatternDelta.empty : PatternDelta ℕ ℕ).act state = some state ∧
      (addAt 3).act state ≠ (PatternDelta.empty : PatternDelta ℕ ℕ).act state := by
  refine ⟨rfl, fun same => ?_⟩
  have atThree := congrFun (Option.some.inj same) 3
  simp at atThree

/-- **Positive, the merge of a wave**: the guard and two additions of odd kinds
are merged, in every order to one delta.  **Negative**: with an addition of an
even kind among them the merge is refused. -/
theorem merge_instances :
    (patternWaveMerge.merge [addWhereNoneOf evens 1, addAt 3, addAt 5]).isSome = true ∧
      patternWaveMerge.merge [addWhereNoneOf evens 1, addAt 3, addAt 5] =
        patternWaveMerge.merge [addAt 5, addWhereNoneOf evens 1, addAt 3] ∧
      (patternWaveMerge.merge [addWhereNoneOf evens 1, addAt 2]).isSome = false := by
  refine ⟨by decide, ?_, by decide⟩
  exact patternWaveMerge.permutationInvariant
    (List.perm_append_comm (l₁ := [addWhereNoneOf evens 1, addAt 3]) (l₂ := [addAt 5]))

end PatternControls

#print axioms PatternDelta.seq_assoc
#print axioms PatternDelta.seq_comm_of_independent
#print axioms PatternDelta.seqAll_perm
#print axioms patternWaveMerge
#print axioms toPatternDelta_independent_iff
#print axioms addWhereNoneOf_act_eq_some_iff
#print axioms addWhereNoneOf_reads_all
#print axioms addWhereNoneOf_not_effectFootprinted
#print axioms PatternControls.evens_infinite
#print axioms PatternControls.guard_has_no_finite_footprint
#print axioms PatternControls.guard_is_no_footprintedDelta
#print axioms PatternControls.clear_is_no_patternDelta
#print axioms PatternControls.guard_and_odd
#print axioms PatternControls.guard_and_even
#print axioms PatternControls.empty_instances
#print axioms PatternControls.merge_instances

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints
