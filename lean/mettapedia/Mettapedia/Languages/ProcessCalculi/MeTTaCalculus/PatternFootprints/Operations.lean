import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints.PatternWaves
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints.Patterns
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints.MatcherRows
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints.Compatibility
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints.PolicyTable
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints.Claims

/-!
# The operations of a space at the grain of kinds: one table

A location is a kind of atom in a space; the state gives each kind its
multiplicity; a pattern is the set of kinds it matches.  This module imports the
development and gives, for each operation, its footprint, whether it is monotone,
and with which operations it conflicts when a wave is validated on its writes
only and when it is validated on its reads as well.  It adds what the table needs
about how two operations meet.

A conflict by footprints is a verdict about two sets.  On writes only two
operations conflict when they write a common kind
(`independentEffects_write_write_iff`); on reads as well, also when one writes a
kind the other reads (`independentEffects_read_write_iff`).  A read conflicts
with nothing on writes only (`Proposal.writesApart_of_writes_empty`), and two
reads never conflict (`Proposal.independent_of_no_writes`).  Whether a conflict
by footprints is a real one, an order in which something is lost, is a separate
fact, and the table gives both.  For proposals that only add, the wave of deltas
leaves out the two comparisons that find conflicts that are not real, two
additions of one kind and an addition against a positive read: it compares
guards that are not positive and answers that read, and nothing else
(`Proposal.DeltaCompatible`, `wave_of_deltas_every_order`).  Both tests establish
one property of a pair (`Proposal.Compatible`), so they may be mixed in one wave:
a removal that is independent of the additions by sets, among additions that are
compatible by deltas (`wave_of_compatible_every_order`,
`CompatibilityControls.mixed_wave`).  For proposals that remove, with guards that
no addition disables and answers that read nothing, the test is counting: a world
on which the proposals have claims publishes them in every order
(`HasClaims.publishAll_perm`, `wave_of_claims_every_order`).  At the grain of kinds
the test is computed (`ClaimsAvailable`, `hasClaims_of_claimsAvailable`), and the
wave validated on it is a policy (`Policy.publishWaveOnClaims`).

The verdicts by footprints for every pair of the seven operations at one kind are
computed in `OperationControls.conflicts_on_writes` and
`OperationControls.conflicts_on_reads`.

| Operation | Reads; writes | Monotone | Conflicts on writes only | Conflicts on reads as well |
|---|---|---|---|---|
| add (`addKind`) | nothing; its kind (`addKind_footprint`) | yes (`addKind_monotone`) | with what writes its kind. Not real against an addition: both orders fire to one state (`addKind_comm`). Real against a removal where the kind is absent (`addKind_then_removeKind`, `removeKind_then_addKind_of_absent`), not where it is present (`removeKind_then_addKind_of_present`; by claims `ClaimControls.addition_and_removal`) | also with what reads its kind. Not real against one answer of a match (`oneAnswer_stillHas_add`). Real against the bag of answers of a pattern that matches the kind (`indicator_add_single_eq_iff`, `bagOfAnswers_add_eq_iff`) and against a guard for its absence (`addKind_then_addKindUnless`) |
| remove (`removeKind`) | nothing declared, and it fires only where its kind is (`fire_removeKind_eq_some_iff`); its kind (`removeKind_footprint`) | no (`removeKind_not_monotone`); positive (`removeKind_positive`): where it fires it fires on every larger state (`fire_removeKind_add`) | with what writes its kind. Against a removal, real exactly where there are fewer than two occurrences (`removeKind_twice_isSome_iff`); by claims the two are a wave exactly where there are two (`removals_hasClaims_iff`) | also with what reads its kind. Against one answer of a match, real exactly where there are fewer than two occurrences (`removeKind_then_seeKind_isSome_iff`; by claims `ClaimControls.reader_and_taker`), and never for another kind (`oneAnswer_stillHas_after_removeKind`). Real against the bag of answers of a pattern that matches the kind (`indicator_eq_of_add_single_iff`). Not real against a guard for absence (`addKindUnless_after_removeKind`) |
| consume (`consumeKind`) | what its guard reads; its kind (`consumeKind_footprint`); one step (`fire_consumeKind_eq_some_iff`) | no (`consumeKind_not_monotone`); positive when no addition disables its guard (`consumeKind_positive`) | as a removal, which it is where its guard holds (`fire_consumeKind_eq_some_iff`) | as a removal, and with what writes a kind its guard reads (`KindControls.consumeKind_fires`) |
| one answer of a match (`seeKind`, `oneAnswer`) | its kind; nothing (`seeKind_footprint`, `oneAnswer_footprint`); for a row of the matcher, its witnesses (`cmatchPattern_mem_iff_witnesses`) | yes (`seeKind_monotone`, `oneAnswer_monotone`, `Region.matchKinds_monotone`) | with nothing (`Proposal.writesApart_of_writes_empty`) | with what writes its kind; real only against the removal of the last occurrence (`oneAnswer_stillHas_iff`) |
| the bag of answers of a match (`Set.indicator` of the kinds, `Readout.complete`, `allAnswers`) | exactly the kinds the pattern matches (`dependsOn_indicator_iff`); no finite set if there are infinitely many (`not_dependsOn_indicator_finite`); nothing; as the guard of a rule, `completeRead_guard_setEffectFootprinted` | no (`MonotoneControls.complete_read_leaves_the_fragment`) | with nothing (`allAnswers_footprint`, `Proposal.writesApart_of_writes_empty`) | with what writes a kind the pattern matches, always real (`indicator_add_eq_iff`, `allAnswers_stillHas_iff_readsKept`), and with nothing else (`completeRead_guard_commutes_with_addKind`); against a publication the validation is a finite check on the kinds written (`completeRead_after_publish_iff`); the test is matching against a kind (`singleton_disjoint_kinds_iff`) and unification against a template (`apart_iff_kinds_disjoint`, `bagOfAnswers_stable_under_template`, `bagOfAnswers_changed_by_template`); for the atoms of the computable matcher, a sound test (`atomKinds_disjoint_of_rigidClash`) |
| a guard for absence (`addKindUnless`, `addWhereNoneOf`) | the kind watched; the kind added (`addKindUnless_footprint`); for a pattern, exactly the kinds it accepts (`addWhereNoneOf_reads_all`), so no finite set where there are infinitely many (`addWhereNoneOf_not_effectFootprinted`); for the whole bag, every kind (`emptinessTest_setEffectFootprinted_iff`) | no (`addKindUnless_not_monotone`), and not positive (`addKindUnless_not_positive`) | as the addition it guards; and by installation two such guards publish a state of no serial run (`ValidationControls.write_skew`) | also with what writes a kind watched: real against an addition (`addKind_then_addKindUnless`, `PatternControls.guard_and_even`), not against a removal (`addKindUnless_after_removeKind`); for a pattern the test is computed (`PatternDelta.decidableIndependent`, `PatternControls.guard_and_odd`) |
| a cell write (`replaceKind`) | nothing declared, and it fires only where the old value is (`fire_replaceKind_eq_some_iff`); the old and the new value (`replaceKind_footprint`) | no (`replaceKind_not_monotone`); positive (`replaceKind_positive`) | with what writes the old or the new value; two writers of one cell, real (`replaceKind_twice`) | also with what reads the old or the new value; real against a read of the old value (`replaceKind_then_seeKind_of_once`) |
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Logic.LP

universe u v w

variable {Location : Type u} {Value : Type v} {Answer : Type w}

/-! ## Verdicts by footprints -/

section Verdicts

variable [DecidableEq Location]

/-- **Two writers that read nothing conflict exactly when they write a common
location**, under both validations. -/
theorem independentEffects_write_write_iff (firstWrites secondWrites : Finset Location) :
    IndependentEffects ∅ firstWrites ∅ secondWrites ↔ Disjoint firstWrites secondWrites := by
  unfold IndependentEffects
  rw [Finset.empty_union, Finset.empty_union]
  exact ⟨fun independent => independent.1, fun disjoint => ⟨disjoint, disjoint.symm⟩⟩

/-- **A reader and a writer conflict, when reads are validated, exactly when the
writer writes a location the reader reads.** -/
theorem independentEffects_read_write_iff (reads writes : Finset Location) :
    IndependentEffects reads ∅ ∅ writes ↔ Disjoint writes reads := by
  exact ⟨fun independent => independent.2.mono_right Finset.subset_union_left,
    fun disjoint => ⟨Finset.disjoint_empty_left _, (Finset.union_empty reads).symm ▸ disjoint⟩⟩

variable [Zero Value] [Add Value] [SepAlgebra Value]

/-- **A read conflicts with nothing when only writes are validated.** -/
theorem Proposal.writesApart_of_writes_empty {first : Proposal Location Value Answer}
    (readsOnly : first.writes = ∅) (second : Proposal Location Value Answer) :
    first.WritesApart second := by
  unfold Proposal.WritesApart
  rw [readsOnly]
  exact Finset.disjoint_empty_left _

end Verdicts

/-! ## How two operations meet -/

section Meetings

variable [DecidableEq Location]

/-- Removing a kind that is present leaves one occurrence less. -/
theorem fire_removeKind_of_present (kind : Location) {state : Location → ℕ}
    (present : 0 < state kind) :
    (removeKind kind).fire state = some (state - Pi.single kind 1) := by
  refine (fire_removeKind_eq_some_iff kind state _).mpr (funext fun other => ?_)
  show state other =
    state other - (Pi.single kind 1 : Location → ℕ) other + (Pi.single kind 1 : Location → ℕ) other
  by_cases same : other = kind
  · subst same
    rw [Pi.single_eq_same]
    omega
  · rw [Pi.single_eq_of_ne same]
    rfl

/-- **Two additions commute**, of two kinds or of one: both orders fire, to one
state. -/
theorem addKind_comm (first second : Location) (state : Location → ℕ) :
    ((addKind first).fire state).bind (addKind second).fire =
      ((addKind second).fire state).bind (addKind first).fire := by
  rw [fire_addKind, fire_addKind, Option.bind_some, Option.bind_some, fire_addKind, fire_addKind,
    add_right_comm]

/-- An addition and then the removal of its kind: the state as it was. -/
theorem addKind_then_removeKind (kind : Location) (state : Location → ℕ) :
    ((addKind kind).fire state).bind (removeKind kind).fire = some state := by
  rw [fire_addKind, Option.bind_some]
  exact (fire_removeKind_eq_some_iff kind _ state).mpr rfl

/-- **The removal first, where the kind is absent: refused.**  So an addition and
a removal of one kind are in a real conflict there. -/
theorem removeKind_then_addKind_of_absent (kind : Location) {state : Location → ℕ}
    (absent : state kind = 0) :
    ((removeKind kind).fire state).bind (addKind kind).fire = none := by
  rw [fire_removeKind_eq_none kind absent]
  rfl

/-- Where the kind is present the two orders agree. -/
theorem removeKind_then_addKind_of_present (kind : Location) {state : Location → ℕ}
    (present : 0 < state kind) :
    ((removeKind kind).fire state).bind (addKind kind).fire = some state := by
  rw [fire_removeKind_of_present kind present, Option.bind_some, fire_addKind]
  refine congrArg some (funext fun other => ?_)
  show state other - (Pi.single kind 1 : Location → ℕ) other +
    (Pi.single kind 1 : Location → ℕ) other = state other
  by_cases same : other = kind
  · subst same
    rw [Pi.single_eq_same]
    omega
  · rw [Pi.single_eq_of_ne same]
    rfl

/-- **Two removals of one kind are both published exactly where there are two
occurrences.** -/
theorem removeKind_twice_isSome_iff (kind : Location) (state : Location → ℕ) :
    (((removeKind kind).fire state).bind (removeKind kind).fire).isSome ↔ 2 ≤ state kind := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨final, published⟩
    obtain ⟨middle, first, second⟩ := Option.bind_eq_some_iff.mp published
    have atFirst := congrFun ((fire_removeKind_eq_some_iff kind state middle).mp first) kind
    have atSecond := congrFun ((fire_removeKind_eq_some_iff kind middle final).mp second) kind
    have single : (Pi.single kind 1 : Location → ℕ) kind = 1 := Pi.single_eq_same kind 1
    have firstCount : state kind = middle kind + 1 := by rw [atFirst]; exact congrArg _ single
    have secondCount : middle kind = final kind + 1 := by rw [atSecond]; exact congrArg _ single
    omega
  · intro two
    have present : 0 < state kind := by omega
    have still : 0 < (state - (Pi.single kind 1 : Location → ℕ)) kind := by
      show 0 < state kind - (Pi.single kind 1 : Location → ℕ) kind
      rw [Pi.single_eq_same]
      omega
    exact ⟨_, by rw [fire_removeKind_of_present kind present, Option.bind_some,
      fire_removeKind_of_present kind still]⟩

/-- **A removal and then one answer of a match for its kind: the answer is there
exactly where there were two occurrences.** -/
theorem removeKind_then_seeKind_isSome_iff (kind : Location) (state : Location → ℕ) :
    (((removeKind kind).fire state).bind (seeKind kind).fire).isSome ↔ 2 ≤ state kind := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨final, published⟩
    obtain ⟨middle, first, second⟩ := Option.bind_eq_some_iff.mp published
    have atFirst := congrFun ((fire_removeKind_eq_some_iff kind state middle).mp first) kind
    have present := ((fire_seeKind_eq_some_iff kind middle final).mp second).1
    have single : (Pi.single kind 1 : Location → ℕ) kind = 1 := Pi.single_eq_same kind 1
    have firstCount : state kind = middle kind + 1 := by rw [atFirst]; exact congrArg _ single
    omega
  · intro two
    have present : 0 < state kind := by omega
    have still : 0 < (state - (Pi.single kind 1 : Location → ℕ)) kind := by
      show 0 < state kind - (Pi.single kind 1 : Location → ℕ) kind
      rw [Pi.single_eq_same]
      omega
    exact ⟨_, by rw [fire_removeKind_of_present kind present, Option.bind_some,
      (fire_seeKind_eq_some_iff kind _ _).mpr ⟨still, rfl⟩]⟩

/-- **An addition of the kind watched disables the guard for its absence.** -/
theorem addKind_then_addKindUnless (kind watched : Location) (state : Location → ℕ) :
    ((addKind watched).fire state).bind (addKindUnless kind watched).fire = none := by
  rw [fire_addKind, Option.bind_some]
  cases fired : (addKindUnless kind watched).fire (state + Pi.single watched 1) with
  | none => rfl
  | some target =>
      have absent := ((fire_addKindUnless_eq_some_iff kind watched _ target).mp fired).1
      have single : (Pi.single watched 1 : Location → ℕ) watched = 1 := Pi.single_eq_same watched 1
      have count : (state + (Pi.single watched 1 : Location → ℕ)) watched = state watched + 1 :=
        congrArg (state watched + ·) single
      omega

/-- **A removal does not disable a guard for absence**, of the kind watched or of
another. -/
theorem addKindUnless_after_removeKind (kind watched other : Location)
    {state target next : Location → ℕ}
    (fires : (addKindUnless kind watched).fire state = some target)
    (removed : (removeKind other).fire state = some next) :
    ((addKindUnless kind watched).fire next).isSome := by
  have absent := ((fire_addKindUnless_eq_some_iff kind watched state target).mp fires).1
  have atWatched := congrFun ((fire_removeKind_eq_some_iff other state next).mp removed) watched
  have stillAbsent : next watched = 0 := by
    have sum : state watched = next watched + (Pi.single other 1 : Location → ℕ) watched :=
      atWatched
    omega
  rw [(fire_addKindUnless_eq_some_iff kind watched next _).mpr ⟨stillAbsent, rfl⟩]
  rfl

/-- **A consumption is not monotone**: it consumes its kind. -/
theorem consumeKind_not_monotone (kind : Location) (guard : Readout Location ℕ Prop)
    (decideGuard : DecidablePred guard.value) :
    ¬ (consumeKind kind guard decideGuard).Monotone := by
  intro monotone
  have consumes : marking ({kind} : Multiset Location) = 0 := monotone.isAddition
  have atKind := congrFun consumes kind
  rw [marking_singleton] at atKind
  simp at atKind

/-- **Two writers of one cell**: after the first has replaced the one old value,
the second is refused. -/
theorem replaceKind_twice (old new other : Location) {state : Location → ℕ}
    (once : state old = 1) (differentNew : new ≠ old) :
    ((replaceKind old new).fire state).bind (replaceKind old other).fire = none := by
  cases first : (replaceKind old new).fire state with
  | none => rfl
  | some middle =>
      rw [Option.bind_some]
      cases second : (replaceKind old other).fire middle with
      | none => rfl
      | some final =>
          obtain ⟨frame, stateEq, middleEq⟩ :=
            (fire_replaceKind_eq_some_iff old new state middle).mp first
          obtain ⟨frame', middleEq', -⟩ :=
            (fire_replaceKind_eq_some_iff old other middle final).mp second
          have single : (Pi.single old 1 : Location → ℕ) old = 1 := Pi.single_eq_same old 1
          have none : (Pi.single new 1 : Location → ℕ) old = 0 := Pi.single_eq_of_ne' differentNew 1
          have atState : state old = frame old + (Pi.single old 1 : Location → ℕ) old :=
            congrFun stateEq old
          have atMiddle : middle old = frame old + (Pi.single new 1 : Location → ℕ) old :=
            congrFun middleEq old
          have atMiddle' : middle old = frame' old + (Pi.single old 1 : Location → ℕ) old :=
            congrFun middleEq' old
          omega

/-- **A cell write and then a read of the old value, where the cell held it once:
refused.** -/
theorem replaceKind_then_seeKind_of_once (old new : Location) (different : new ≠ old)
    {state : Location → ℕ} (once : state old = 1) :
    ((replaceKind old new).fire state).bind (seeKind old).fire = none := by
  cases first : (replaceKind old new).fire state with
  | none => rfl
  | some middle =>
      rw [Option.bind_some]
      cases second : (seeKind old).fire middle with
      | none => rfl
      | some final =>
          obtain ⟨frame, stateEq, middleEq⟩ :=
            (fire_replaceKind_eq_some_iff old new state middle).mp first
          have present := ((fire_seeKind_eq_some_iff old middle final).mp second).1
          have single : (Pi.single old 1 : Location → ℕ) old = 1 := Pi.single_eq_same old 1
          have none : (Pi.single new 1 : Location → ℕ) old = 0 := Pi.single_eq_of_ne' different 1
          have atState : state old = frame old + (Pi.single old 1 : Location → ℕ) old :=
            congrFun stateEq old
          have atMiddle : middle old = frame old + (Pi.single new 1 : Location → ℕ) old :=
            congrFun middleEq old
          omega

end Meetings

/-! ## A rule guarded by a complete read -/

section GuardedByCompleteRead

variable [DecidableEq Location]

/-- **A rule that fires only where the whole bag of answers of a pattern is a
captured one is certified with the pattern among its reads.**  The pattern may
match infinitely many kinds. -/
theorem completeRead_guard_setEffectFootprinted (rule : LocalRule Location ℕ)
    (footprint : Set Location) (captured : Location → ℕ) :
    SetEffectFootprinted
      (fun source target => footprint.indicator source = captured ∧ rule.Fires source target)
      (footprint ∪ ↑rule.reads) ↑rule.writes :=
  (LocalRule.setEffectFootprinted rule).guarded fun state other agrees => by
    have same : footprint.indicator state = footprint.indicator other :=
      dependsOn_indicator footprint agrees
    rw [same]

/-- **The diamond for a pattern footprint.**  Such a rule and the addition of a
kind that the pattern does not match, and that the rule neither reads nor writes,
commute: after either the other fires, the captured bag of answers is still the
bag of answers, and the two orders reach one state. -/
theorem completeRead_guard_commutes_with_addKind (rule : LocalRule Location ℕ)
    (footprint : Set Location) (captured : Location → ℕ) {kind : Location}
    (outside : kind ∉ footprint) (unread : kind ∉ rule.reads) (unwritten : kind ∉ rule.writes)
    {source afterRule afterAdd : Location → ℕ}
    (fires : footprint.indicator source = captured ∧ rule.Fires source afterRule)
    (added : (addKind kind).rule.Fires source afterAdd) :
    ∃ joined, (addKind kind).rule.Fires afterRule joined ∧
      (footprint.indicator afterAdd = captured ∧ rule.Fires afterAdd joined) := by
  have addCertified := LocalRule.setEffectFootprinted (addKind kind).rule
  rw [(addKind_footprint kind).1, (addKind_footprint kind).2] at addCertified
  refine (completeRead_guard_setEffectFootprinted rule footprint captured).independent_commute
    addCertified ⟨?_, ?_⟩ fires added
  · refine Set.disjoint_left.mpr fun location written inside => ?_
    rcases inside with empty | isKind
    · exact absurd (Finset.mem_coe.mp empty) (Finset.notMem_empty location)
    · have same : location = kind := Finset.mem_singleton.mp (Finset.mem_coe.mp isKind)
      exact unwritten (same ▸ Finset.mem_coe.mp written)
  · refine Set.disjoint_left.mpr fun location isKind inside => ?_
    have same : location = kind := Finset.mem_singleton.mp (Finset.mem_coe.mp isKind)
    subst same
    rcases inside with (inFootprint | read) | written
    · exact outside inFootprint
    · exact unread (Finset.mem_coe.mp read)
    · exact unwritten (Finset.mem_coe.mp written)

/-- **Validation of a complete read against finitely many writes is a finite
check.**  After a change that leaves everything outside finitely many written
kinds as it was, the bag of answers of a pattern is the same exactly when no
written kind that the pattern matches has changed its multiplicity: one question
to the matcher for each written kind. -/
theorem completeRead_eq_iff_of_preservesOutside {writes : Finset Location}
    (footprint : Set Location) {source target : Location → ℕ}
    (preserves : PreservesOutside writes source target) :
    footprint.indicator source = footprint.indicator target ↔
      ∀ kind ∈ writes, kind ∈ footprint → source kind = target kind :=
  (indicator_eq_iff_eqOn footprint source target).trans (eqOn_iff_of_preservesOutside preserves)

/-- **After a publication** the bag of answers of a pattern is what it was exactly
when no kind that the steps write and the pattern matches has changed its
multiplicity. -/
theorem completeRead_after_publish_iff {steps : List (Step Location ℕ)}
    (footprint : Set Location) {source target : Location → ℕ}
    (published : publish steps source = some target) :
    footprint.indicator source = footprint.indicator target ↔
      ∀ kind ∈ stepsWrites steps, kind ∈ footprint → source kind = target kind :=
  completeRead_eq_iff_of_preservesOutside footprint
    ((publish_effectFootprinted steps).preserves published)

end GuardedByCompleteRead

/-! ## A pattern against an addition, and against a template -/

section Patterns

variable {σ : LPSignature} [DecidableEq (GroundTerm σ)]

/-- **An addition changes the whole bag of answers of a match exactly when the
pattern matches the atom that is added.** -/
theorem bagOfAnswers_add_eq_iff (pattern : Mettapedia.Logic.LP.Term σ) (state : GroundTerm σ → ℕ)
    (kind : GroundTerm σ) :
    (kinds pattern).indicator (state + Pi.single kind 1) = (kinds pattern).indicator state ↔
      ¬ Matches pattern kind :=
  indicator_add_single_eq_iff (kinds pattern) state kind

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- **A rule whose additions are instances of a template leaves the bag of
answers of a pattern as it is, when the test finds the pattern and the template
apart.**  The test is made before any instance is known. -/
theorem bagOfAnswers_stable_under_template {split : VariableSplit σ}
    {pattern template : Mettapedia.Logic.LP.Term σ}
    (found : apart split pattern template = true) {kind : GroundTerm σ}
    (instanceOf : Matches template kind) (state : GroundTerm σ → ℕ) :
    (kinds pattern).indicator (state + Pi.single kind 1) = (kinds pattern).indicator state :=
  (bagOfAnswers_add_eq_iff pattern state kind).mpr fun matched =>
    Set.disjoint_left.mp (kinds_disjoint_of_apart found) matched instanceOf

/-- **And where the test does not find them apart, some instance of the template
changes the bag of answers**, given a term without variables. -/
theorem bagOfAnswers_changed_by_template [Nonempty (GroundTerm σ)] {split : VariableSplit σ}
    {pattern template : Mettapedia.Logic.LP.Term σ}
    (notApart : apart split pattern template = false) (state : GroundTerm σ → ℕ) :
    ∃ kind, Matches template kind ∧
      (kinds pattern).indicator (state + Pi.single kind 1) ≠ (kinds pattern).indicator state := by
  have common : ¬ Disjoint (kinds pattern) (kinds template) := fun disjoint => by
    rw [(apart_iff_kinds_disjoint split pattern template).mpr disjoint] at notApart
    cases notApart
  obtain ⟨kind, matched, instanceOf⟩ := Set.not_disjoint_iff.mp common
  exact ⟨kind, instanceOf, fun same => (bagOfAnswers_add_eq_iff pattern state kind).mp same matched⟩

end Patterns

/-! ## Controls -/

namespace OperationControls

open AddOnly (Kind noKinds)

/-- **Positive, two writers**: additions of two kinds do not conflict.
**Negative**: additions of one kind do, by footprints. -/
theorem write_write_instances :
    IndependentEffects ∅ ({Kind.a} : Finset Kind) ∅ {Kind.b} ∧
      ¬ IndependentEffects ∅ ({Kind.a} : Finset Kind) ∅ {Kind.a} := by
  rw [independentEffects_write_write_iff, independentEffects_write_write_iff]
  decide

/-- **Positive, a reader and a writer**: a read of `a` and a write of `b`.
**Negative**: a read of `a` and a write of `a`. -/
theorem read_write_instances :
    IndependentEffects ({Kind.a} : Finset Kind) ∅ ∅ {Kind.b} ∧
      ¬ IndependentEffects ({Kind.a} : Finset Kind) ∅ ∅ {Kind.a} := by
  rw [independentEffects_read_write_iff, independentEffects_read_write_iff]
  decide

/-- **Two writers of one cell, an instance**: the cell holds `a`; both write `b`
over it; the second is refused. -/
theorem two_writers_of_one_cell :
    (publish [replaceKind Kind.a Kind.b, replaceKind Kind.a Kind.b]
      (Pi.single Kind.a 1)).isSome = false := by
  decide

/-- **Two removals of one kind, instances**: with two occurrences both are
published; with one the second is refused. -/
theorem two_removals :
    (publish [removeKind Kind.a, removeKind Kind.a] (Pi.single Kind.a 2)).isSome = true ∧
      (publish [removeKind Kind.a, removeKind Kind.a] (Pi.single Kind.a 1)).isSome = false := by
  decide

/-- The seven operations as proposals at the kind `a`, in the order of the table:
add an `a`; remove an `a`; consume an `a` when a `b` is there; one answer of a
match for `a`; the bag of answers of the pattern that matches `a`, as its
multiplicity; add a `b` unless an `a` is there; write a cell from `a` to `b`. -/
def operations : List (Proposal Kind ℕ ℕ) :=
  [⟨[addKind .a], Readout.const 0⟩,
    ⟨[removeKind .a], Readout.const 0⟩,
    ⟨[KindControls.consumeAIfB], Readout.const 0⟩,
    oneAnswer Kind.a 0,
    ⟨[], Readout.valueAt Kind.a⟩,
    ⟨[addKindUnless .b .a], Readout.const 0⟩,
    ⟨[replaceKind .a .b], Readout.const 0⟩]

/-- **Conflicts by footprints when only writes are validated**, for every pair of
the seven operations: `true` is a conflict.  Rows and columns are in the order of
`operations`.  The two reads conflict with nothing; two instances of one writer
conflict with each other. -/
theorem conflicts_on_writes :
    operations.map (fun first => operations.map fun second =>
        decide (¬ first.WritesApart second)) =
      [[true, true, true, false, false, false, true],
        [true, true, true, false, false, false, true],
        [true, true, true, false, false, false, true],
        [false, false, false, false, false, false, false],
        [false, false, false, false, false, false, false],
        [false, false, false, false, false, true, true],
        [true, true, true, false, false, true, true]] := by
  decide

/-- **Conflicts by footprints when reads are validated as well**, for every pair
of the seven operations.  A read conflicts with every writer of its kind, and two
reads do not conflict; the guard for the absence of `a` writes `b`, so it conflicts
with the writers of `a` by its read only. -/
theorem conflicts_on_reads :
    operations.map (fun first => operations.map fun second =>
        decide (¬ first.Independent second)) =
      [[true, true, true, true, true, true, true],
        [true, true, true, true, true, true, true],
        [true, true, true, true, true, true, true],
        [true, true, true, false, false, false, true],
        [true, true, true, false, false, false, true],
        [true, true, true, false, false, true, true],
        [true, true, true, true, true, true, true]] := by
  decide

end OperationControls

#print axioms independentEffects_write_write_iff
#print axioms independentEffects_read_write_iff
#print axioms Proposal.writesApart_of_writes_empty
#print axioms fire_removeKind_of_present
#print axioms addKind_comm
#print axioms addKind_then_removeKind
#print axioms removeKind_then_addKind_of_absent
#print axioms removeKind_then_addKind_of_present
#print axioms removeKind_twice_isSome_iff
#print axioms removeKind_then_seeKind_isSome_iff
#print axioms addKind_then_addKindUnless
#print axioms addKindUnless_after_removeKind
#print axioms consumeKind_not_monotone
#print axioms replaceKind_twice
#print axioms replaceKind_then_seeKind_of_once
#print axioms completeRead_guard_setEffectFootprinted
#print axioms completeRead_guard_commutes_with_addKind
#print axioms completeRead_eq_iff_of_preservesOutside
#print axioms completeRead_after_publish_iff
#print axioms bagOfAnswers_add_eq_iff
#print axioms bagOfAnswers_stable_under_template
#print axioms bagOfAnswers_changed_by_template
#print axioms OperationControls.write_write_instances
#print axioms OperationControls.read_write_instances
#print axioms OperationControls.two_writers_of_one_cell
#print axioms OperationControls.two_removals
#print axioms OperationControls.conflicts_on_writes
#print axioms OperationControls.conflicts_on_reads

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
