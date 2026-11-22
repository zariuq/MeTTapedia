import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions

/-!
# Steps: local rule instances that fire as partial functions

A region is a program of local rule instances.  To give it a bag of outcomes, every
instance it uses must fire as a partial function of the state: at most one result,
and the result computed.  A `Step` is an instance of a local rule
(`FootprintedSpaceTransactions.LocalRule`) together with such a function, proved
equal to the rule's firing relation.

* **Publication** (`publish`) fires a finite list of steps in order as one step of
  the state.  Either all of them fire, or the state is refused and nothing has
  changed.
* **Footprint** (`publish_effectFootprinted`).  The read/write certificate of
  `FootprintedSpaceTransactions` is closed under sequential composition
  (`comp_effectFootprinted`), so a publication is certified at the union of the
  read locations and the union of the written locations of its steps
  (`stepsReads`, `stepsWrites`).  A refusal is as local as a success
  (`publish_eq_none_of_agreesOn`).
* **Bags** (`Step.ofBagRule`).  Over a network of occurrence stores every local
  rule with a decidable guard is a step: a bag is cancellative, so the frame of a
  firing is the difference.  The rules used below are adding, removing, seeing and
  replacing one occurrence.

Positive: `Step.fire_addAtom`, `Step.fire_removeAtom_eq_some_iff`.  Negative: over
an algebra in which a resource can be put beside itself and still be itself, the
rule that takes the resource away has two results from one state, so it is the rule
of no step (`Controls.lower_is_no_step`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
open Mettapedia.GSLT.SeparationAlgebra

universe u v

variable {Location : Type u} {Value : Type v}

/-! ## Agreement on a footprint -/

section Agreement

variable [DecidableEq Location]

/-- A state agrees with itself on every footprint. -/
theorem agreesOn_refl (footprint : Finset Location) (state : Location → Value) :
    AgreesOn footprint state state :=
  fun _ _ => rfl

/-- Agreement on a footprint is symmetric. -/
theorem agreesOn_symm {footprint : Finset Location} {left right : Location → Value}
    (agrees : AgreesOn footprint left right) : AgreesOn footprint right left :=
  fun location inside => (agrees location inside).symm

/-- Agreement on a footprint is transitive. -/
theorem agreesOn_trans {footprint : Finset Location} {first second third : Location → Value}
    (firstSecond : AgreesOn footprint first second)
    (secondThird : AgreesOn footprint second third) : AgreesOn footprint first third :=
  fun location inside => (firstSecond location inside).trans (secondThird location inside)

/-- Agreement on a footprint is agreement on every smaller footprint. -/
theorem agreesOn_mono {small large : Finset Location} {left right : Location → Value}
    (subset : small ⊆ large) (agrees : AgreesOn large left right) :
    AgreesOn small left right :=
  fun location inside => agrees location (subset inside)

/-- Agreement on a finite footprint is checked location by location. -/
instance decidableAgreesOn [DecidableEq Value] (footprint : Finset Location)
    (left right : Location → Value) : Decidable (AgreesOn footprint left right) :=
  inferInstanceAs (Decidable (∀ location ∈ footprint, left location = right location))

/-- Independence of two read/write footprints is checked on the finite sets. -/
instance decidableIndependentEffects
    (firstReads firstWrites secondReads secondWrites : Finset Location) :
    Decidable (IndependentEffects firstReads firstWrites secondReads secondWrites) :=
  inferInstanceAs (Decidable (Disjoint firstWrites (secondReads ∪ secondWrites) ∧
    Disjoint secondWrites (firstReads ∪ firstWrites)))

/-- Independence of effects does not depend on which of the two is named first. -/
theorem independentEffects_symm
    {firstReads firstWrites secondReads secondWrites : Finset Location}
    (independent : IndependentEffects firstReads firstWrites secondReads secondWrites) :
    IndependentEffects secondReads secondWrites firstReads firstWrites :=
  ⟨independent.2, independent.1⟩

/-- A transition that preserves everything outside its written locations keeps
every location it does not write: the source and the target agree on any footprint
disjoint from the written one. -/
theorem agreesOn_of_preservesOutside {writes footprint : Finset Location}
    {source target : Location → Value} (disjoint : Disjoint writes footprint)
    (preserves : PreservesOutside writes source target) :
    AgreesOn footprint source target :=
  fun location inside =>
    (preserves location fun written => Finset.disjoint_left.mp disjoint written inside).symm

/-- **The read/write certificate is closed under sequential composition**: one
transition after another reads what either reads and writes what either writes. -/
theorem comp_effectFootprinted
    {first second : (Location → Value) → (Location → Value) → Prop}
    {firstReads firstWrites secondReads secondWrites : Finset Location}
    (firstCertified : EffectFootprinted first firstReads firstWrites)
    (secondCertified : EffectFootprinted second secondReads secondWrites) :
    EffectFootprinted
      (fun source target => ∃ middle, first source middle ∧ second middle target)
      (firstReads ∪ secondReads) (firstWrites ∪ secondWrites) := by
  constructor
  · rintro source target ⟨middle, firstStep, secondStep⟩ location outside
    have notFirst : location ∉ firstWrites :=
      fun written => outside (Finset.mem_union_left _ written)
    have notSecond : location ∉ secondWrites :=
      fun written => outside (Finset.mem_union_right _ written)
    rw [secondCertified.preserves secondStep location notSecond,
      firstCertified.preserves firstStep location notFirst]
  · rintro source target ⟨middle, firstStep, secondStep⟩ framedSource agrees
    obtain ⟨framedMiddle, framedFirst, firstWritten, firstOutside⟩ :=
      firstCertified.frame firstStep framedSource
        (agreesOn_mono
          (Finset.union_subset_union Finset.subset_union_left Finset.subset_union_left) agrees)
    have middleAgrees : AgreesOn (secondReads ∪ secondWrites) middle framedMiddle := by
      intro location inside
      by_cases written : location ∈ firstWrites
      · exact firstWritten location written
      · rw [firstCertified.preserves firstStep location written, firstOutside location written]
        exact agrees location
          (Finset.union_subset_union Finset.subset_union_right Finset.subset_union_right inside)
    obtain ⟨framedTarget, framedSecond, secondWritten, secondOutside⟩ :=
      secondCertified.frame secondStep framedMiddle middleAgrees
    refine ⟨framedTarget, ⟨framedMiddle, framedFirst, framedSecond⟩, ?_, ?_⟩
    · intro location inside
      by_cases written : location ∈ secondWrites
      · exact secondWritten location written
      · have inFirst : location ∈ firstWrites :=
          (Finset.mem_union.mp inside).resolve_right written
        rw [secondCertified.preserves secondStep location written,
          secondOutside location written]
        exact firstWritten location inFirst
    · intro location outside
      have notFirst : location ∉ firstWrites :=
        fun written => outside (Finset.mem_union_left _ written)
      have notSecond : location ∉ secondWrites :=
        fun written => outside (Finset.mem_union_right _ written)
      rw [secondOutside location notSecond, firstOutside location notFirst]

/-- A certificate stays a certificate when more locations are declared read. -/
theorem effectFootprinted_mono_reads
    {relation : (Location → Value) → (Location → Value) → Prop}
    {reads moreReads writes : Finset Location}
    (certified : EffectFootprinted relation reads writes) (subset : reads ⊆ moreReads) :
    EffectFootprinted relation moreReads writes where
  preserves := certified.preserves
  frame step framedSource agrees :=
    certified.frame step framedSource
      (agreesOn_mono (Finset.union_subset_union subset (Finset.Subset.refl _)) agrees)

/-- **A refusal is local**: a certified partial function that refuses a state
refuses every state that agrees with it on what it reads or writes. -/
theorem eq_none_of_agreesOn {act : (Location → Value) → Option (Location → Value)}
    {reads writes : Finset Location}
    (certified : EffectFootprinted (fun source target => act source = some target) reads writes)
    {source framed : Location → Value} (agrees : AgreesOn (reads ∪ writes) source framed)
    (refused : act source = none) : act framed = none := by
  cases fired : act framed with
  | none => rfl
  | some target =>
      obtain ⟨back, backFired, -, -⟩ := certified.frame fired source (agreesOn_symm agrees)
      rw [refused] at backFired
      cases backFired

/-- **Independent certified partial functions commute**: shared reads are
permitted, and the writes of each avoid everything the other reads or writes.
In either order both fire with one result, or both orders are refused. -/
theorem bind_comm_of_independent
    {firstAct secondAct : (Location → Value) → Option (Location → Value)}
    {firstReads firstWrites secondReads secondWrites : Finset Location}
    (firstCertified :
      EffectFootprinted (fun source target => firstAct source = some target) firstReads firstWrites)
    (secondCertified :
      EffectFootprinted (fun source target => secondAct source = some target) secondReads
        secondWrites)
    (independent : IndependentEffects firstReads firstWrites secondReads secondWrites)
    (world : Location → Value) :
    (firstAct world).bind secondAct = (secondAct world).bind firstAct := by
  cases firstFired : firstAct world with
  | none =>
      cases secondFired : secondAct world with
      | none => rfl
      | some afterSecond =>
          exact (eq_none_of_agreesOn firstCertified
            (agreesOn_of_preservesOutside independent.2 (secondCertified.preserves secondFired))
            firstFired).symm
  | some afterFirst =>
      cases secondFired : secondAct world with
      | none =>
          exact eq_none_of_agreesOn secondCertified
            (agreesOn_of_preservesOutside independent.1 (firstCertified.preserves firstFired))
            secondFired
      | some afterSecond =>
          obtain ⟨joined, secondAfterFirst, firstAfterSecond⟩ :=
            EffectFootprinted.independent_commute firstCertified secondCertified independent
              firstFired secondFired
          exact secondAfterFirst.trans firstAfterSecond.symm

end Agreement

/-! ## Steps -/

/-- **A step**: an instance of a local rule whose firing is computed.  `fire` is
the firing as a partial function of the state, and it is exactly the rule's firing
relation; so the instance has at most one result from a state. -/
structure Step (Location : Type u) (Value : Type v) [DecidableEq Location] [Zero Value]
    [Add Value] [SepAlgebra Value] where
  /-- The instance of a local rule. -/
  rule : LocalRule Location Value
  /-- Its firing, as a partial function of the state. -/
  fire : (Location → Value) → Option (Location → Value)
  /-- The function is the firing relation of the rule. -/
  fire_eq_some_iff : ∀ {source target : Location → Value},
    fire source = some target ↔ rule.Fires source target

section Steps

variable [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]

namespace Step

/-- The rule of a step has at most one result from a state. -/
theorem fires_unique (step : Step Location Value) {source first second : Location → Value}
    (firstFires : step.rule.Fires source first) (secondFires : step.rule.Fires source second) :
    first = second :=
  Option.some.inj
    ((step.fire_eq_some_iff.mpr firstFires).symm.trans (step.fire_eq_some_iff.mpr secondFires))

/-- A step is certified at the read and written locations of its rule. -/
theorem effectFootprinted (step : Step Location Value) :
    EffectFootprinted (fun source target => step.fire source = some target)
      step.rule.reads step.rule.writes := by
  have certified := step.rule.effectFootprinted
  constructor
  · intro source target fires
    exact certified.preserves (step.fire_eq_some_iff.mp fires)
  · intro source target fires framedSource agrees
    obtain ⟨framedTarget, framedFires, written, outside⟩ :=
      certified.frame (step.fire_eq_some_iff.mp fires) framedSource agrees
    exact ⟨framedTarget, step.fire_eq_some_iff.mpr framedFires, written, outside⟩

end Step

/-- The locations the guards of a list of steps may read. -/
def stepsReads : List (Step Location Value) → Finset Location
  | [] => ∅
  | step :: rest => step.rule.reads ∪ stepsReads rest

/-- The locations a list of steps may change. -/
def stepsWrites : List (Step Location Value) → Finset Location
  | [] => ∅
  | step :: rest => step.rule.writes ∪ stepsWrites rest

theorem stepsReads_append (first second : List (Step Location Value)) :
    stepsReads (first ++ second) = stepsReads first ∪ stepsReads second := by
  induction first with
  | nil => simp [stepsReads]
  | cons step rest ih => simp [stepsReads, ih, Finset.union_assoc]

theorem stepsWrites_append (first second : List (Step Location Value)) :
    stepsWrites (first ++ second) = stepsWrites first ∪ stepsWrites second := by
  induction first with
  | nil => simp [stepsWrites]
  | cons step rest ih => simp [stepsWrites, ih, Finset.union_assoc]

/-- **Publication**: fire the steps in order, as one step of the state.  All of
them fire, or the state is refused (`none`); a refusal changes nothing, because
nothing but the result is returned. -/
def publish : List (Step Location Value) → (Location → Value) → Option (Location → Value)
  | [], world => some world
  | step :: rest, world => (step.fire world).bind (publish rest)

@[simp] theorem publish_nil (world : Location → Value) :
    publish ([] : List (Step Location Value)) world = some world :=
  rfl

@[simp] theorem publish_cons (step : Step Location Value) (rest : List (Step Location Value))
    (world : Location → Value) :
    publish (step :: rest) world = (step.fire world).bind (publish rest) :=
  rfl

/-- Publishing one list of steps and then another is publishing their
concatenation. -/
theorem publish_append (first second : List (Step Location Value)) (world : Location → Value) :
    publish (first ++ second) world = (publish first world).bind (publish second) := by
  induction first generalizing world with
  | nil => rfl
  | cons step rest ih =>
      cases fired : step.fire world with
      | none => simp [fired]
      | some middle => simp [fired, ih]

/-- **A publication is certified at the footprint of its steps.**  It changes
nothing outside the locations they write, and it can be replayed, with the same
values written, on every state that agrees on the locations they read or write. -/
theorem publish_effectFootprinted (steps : List (Step Location Value)) :
    EffectFootprinted (fun source target => publish steps source = some target)
      (stepsReads steps) (stepsWrites steps) := by
  induction steps with
  | nil =>
      constructor
      · intro source target published location _
        cases published
        rfl
      · intro source target published framedSource _
        cases published
        exact ⟨framedSource, rfl,
          fun location inside => absurd inside (Finset.notMem_empty location), fun _ _ => rfl⟩
  | cons step rest ih =>
      have composed := comp_effectFootprinted step.effectFootprinted ih
      constructor
      · intro source target published
        rw [publish_cons, Option.bind_eq_some_iff] at published
        exact composed.preserves published
      · intro source target published framedSource agrees
        rw [publish_cons, Option.bind_eq_some_iff] at published
        obtain ⟨framedTarget, framedPublished, written, outside⟩ :=
          composed.frame published framedSource agrees
        refine ⟨framedTarget, ?_, written, outside⟩
        rw [publish_cons, Option.bind_eq_some_iff]
        exact framedPublished

/-- **A refusal is local too**: steps that cannot be published on a state cannot
be published on any state that agrees with it on what they read or write. -/
theorem publish_eq_none_of_agreesOn {steps : List (Step Location Value)}
    {source framed : Location → Value}
    (agrees : AgreesOn (stepsReads steps ∪ stepsWrites steps) source framed)
    (refused : publish steps source = none) : publish steps framed = none :=
  eq_none_of_agreesOn (publish_effectFootprinted steps) agrees refused

end Steps

/-! ## Steps over a network of occurrence stores -/

section Bags

variable {Atom : Type v} [DecidableEq Location] [DecidableEq Atom]

/-- **Every local rule over bags with a decidable guard is a step.**  The rule
fires when its guard holds and every written location holds what it consumes; a
bag is cancellative, so the frame is the difference. -/
def Step.ofBagRule (rule : LocalRule Location (Multiset Atom))
    (decideGuard : DecidablePred rule.guard) : Step Location (Multiset Atom) where
  rule := rule
  fire source :=
    if rule.guard source ∧ ∀ location ∈ rule.writes, rule.consumed location ≤ source location then
      some fun location => source location - rule.consumed location + rule.produced location
    else none
  fire_eq_some_iff := by
    intro source target
    constructor
    · intro fires
      split at fires
      · next enabled =>
        cases fires
        refine ⟨enabled.1, fun location => source location - rule.consumed location,
          fun _ => trivial, fun _ => trivial, ?_, ?_⟩
        · funext location
          show source location = rule.consumed location + (source location - rule.consumed location)
          by_cases written : location ∈ rule.writes
          · exact (add_tsub_cancel_of_le (enabled.2 location written)).symm
          · rw [rule.consumed_outside location written, tsub_zero, zero_add]
        · funext location
          show source location - rule.consumed location + rule.produced location =
            rule.produced location + (source location - rule.consumed location)
          exact add_comm _ _
      · cases fires
    · rintro ⟨guarded, frame, -, -, rfl, rfl⟩
      have enabled : rule.guard (rule.consumed + frame) ∧
          ∀ location ∈ rule.writes, rule.consumed location ≤ (rule.consumed + frame) location :=
        ⟨guarded, fun location _ => le_add_right le_rfl⟩
      rw [if_pos enabled]
      congr 1
      funext location
      show rule.consumed location + frame location - rule.consumed location +
          rule.produced location = rule.produced location + frame location
      rw [add_tsub_cancel_left, add_comm]

/-- See one occurrence of `atom` in the space at `location`, and leave it there. -/
def SpaceRules.observeAtom (location : Location) (atom : Atom) :
    LocalRule Location (Multiset Atom) where
  consumed := 0
  produced := 0
  guard state := atom ∈ state location
  reads := {location}
  writes := ∅
  consumed_outside _ _ := rfl
  produced_outside _ _ := rfl
  guard_local agrees holds := by
    rwa [← agrees _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))]

omit [DecidableEq Atom] in
/-- **Seeing an atom is the located observe step.** -/
theorem SpaceRules.observeAtom_fires_iff (location : Location) (atom : Atom)
    (source target : Network Location Atom) :
    (SpaceRules.observeAtom location atom).Fires source target ↔
      LocatedStep .observe location atom source target := by
  rw [LocatedStep.observe_iff]
  constructor
  · rintro ⟨present, frame, -, -, rfl, rfl⟩
    exact ⟨present, rfl⟩
  · rintro ⟨present, rfl⟩
    exact ⟨present, target, fun _ => trivial, fun _ => trivial,
      by simp [SpaceRules.observeAtom], by simp [SpaceRules.observeAtom]⟩

/-- Replace one occurrence of `old` by one of `new` in the store at `location`:
the write of a cell that holds `old`. -/
def SpaceRules.replaceAtom (location : Location) (old new : Atom) :
    LocalRule Location (Multiset Atom) :=
  LocalRule.unguarded (Pi.single location {old}) (Pi.single location {new}) {location}
    (fun other outside => by
      have different : other ≠ location := by simpa using outside
      simp [different])
    (fun other outside => by
      have different : other ≠ location := by simpa using outside
      simp [different])

omit [DecidableEq Atom] in
/-- **Replacing an atom takes one occurrence of the old atom and puts one of the
new atom in its place**, in the store at the location. -/
theorem SpaceRules.replaceAtom_fires_iff (location : Location) (old new : Atom)
    (source target : Network Location Atom) :
    (SpaceRules.replaceAtom location old new).Fires source target ↔
      ∃ rest, source location = old ::ₘ rest ∧
        target = Function.update source location (new ::ₘ rest) := by
  constructor
  · rintro ⟨-, frame, -, -, rfl, rfl⟩
    refine ⟨frame location, by simp [SpaceRules.replaceAtom, LocalRule.unguarded], ?_⟩
    funext other
    by_cases same : other = location
    · subst same
      simp [SpaceRules.replaceAtom, LocalRule.unguarded]
    · simp [SpaceRules.replaceAtom, LocalRule.unguarded, same]
  · rintro ⟨rest, atLocation, rfl⟩
    refine ⟨trivial, Function.update source location rest, fun _ => trivial,
      fun _ => trivial, ?_, ?_⟩
    · funext other
      by_cases same : other = location
      · subst same
        simp [SpaceRules.replaceAtom, LocalRule.unguarded, atLocation, Multiset.singleton_add]
      · simp [SpaceRules.replaceAtom, LocalRule.unguarded, same]
    · funext other
      by_cases same : other = location
      · subst same
        simp [SpaceRules.replaceAtom, LocalRule.unguarded, Multiset.singleton_add]
      · simp [SpaceRules.replaceAtom, LocalRule.unguarded, same]

namespace Step

/-- Add one occurrence of `atom` to the space at `location`. -/
def addAtom (location : Location) (atom : Atom) : Step Location (Multiset Atom) :=
  .ofBagRule (SpaceRules.addAtom location atom) fun _ => isTrue trivial

/-- Remove one occurrence of `atom` from the space at `location`. -/
def removeAtom (location : Location) (atom : Atom) : Step Location (Multiset Atom) :=
  .ofBagRule (SpaceRules.removeAtom location atom) fun _ => isTrue trivial

/-- See one occurrence of `atom` in the space at `location`, and leave it there. -/
def observeAtom (location : Location) (atom : Atom) : Step Location (Multiset Atom) :=
  .ofBagRule (SpaceRules.observeAtom location atom) fun state =>
    inferInstanceAs (Decidable (atom ∈ state location))

/-- Replace one occurrence of `old` by one of `new` in the store at `location`. -/
def replaceAtom (location : Location) (old new : Atom) : Step Location (Multiset Atom) :=
  .ofBagRule (SpaceRules.replaceAtom location old new) fun _ => isTrue trivial

/-- **Positive**: adding an atom fires on every state. -/
theorem fire_addAtom (location : Location) (atom : Atom) (source : Network Location Atom) :
    (addAtom location atom).fire source = some (source + Pi.single location {atom}) :=
  (addAtom location atom).fire_eq_some_iff.mpr
    ((SpaceRules.addAtom_fires_iff location atom source _).mpr rfl)

/-- Removing an atom fires exactly as the located consume step. -/
theorem fire_removeAtom_eq_some_iff (location : Location) (atom : Atom)
    (source target : Network Location Atom) :
    (removeAtom location atom).fire source = some target ↔
      LocatedStep .consume location atom source target :=
  (removeAtom location atom).fire_eq_some_iff.trans
    (SpaceRules.removeAtom_fires_iff location atom source target)

/-- **Negative**: removing an atom that is not there does not fire. -/
theorem fire_removeAtom_eq_none (location : Location) (atom : Atom)
    (source : Network Location Atom) (absent : atom ∉ source location) :
    (removeAtom location atom).fire source = none := by
  cases fired : (removeAtom location atom).fire source with
  | none => rfl
  | some target =>
      obtain ⟨rest, atLocation, -⟩ :=
        LocatedStep.consume_iff.mp
          ((fire_removeAtom_eq_some_iff location atom source target).mp fired)
      exact absurd (by rw [atLocation]; exact Multiset.mem_cons_self atom rest) absent

/-- Seeing an atom fires exactly when the atom is there, and changes nothing. -/
theorem fire_observeAtom_eq_some_iff (location : Location) (atom : Atom)
    (source target : Network Location Atom) :
    (observeAtom location atom).fire source = some target ↔
      atom ∈ source location ∧ target = source :=
  (observeAtom location atom).fire_eq_some_iff.trans
    ((SpaceRules.observeAtom_fires_iff location atom source target).trans LocatedStep.observe_iff)

end Step

end Bags

/-! ## Controls: a rule that is the rule of no step -/

namespace Controls

/-- A flag that is lowered or raised.  Raising a raised flag leaves it raised. -/
inductive Flag where
  | lowered
  | raised
  deriving DecidableEq

instance : Zero Flag := ⟨.lowered⟩

instance : Add Flag :=
  ⟨fun first second => match first with
    | .lowered => second
    | .raised => .raised⟩

/-- Flags under "either is raised", every two of them separate.  The algebra is
not cancellative: a raised flag beside a raised flag is a raised flag. -/
instance : SepAlgebra Flag where
  Separate _ _ := True
  separate_zero _ := trivial
  separate_symm _ := trivial
  add_zero flag := by cases flag <;> rfl
  add_comm := by
    intro first second _
    cases first <;> cases second <;> rfl
  add_assoc := by
    intro first second third _ _ _
    cases first <;> rfl
  separate_of_separate_add _ _ := trivial
  separate_add_of_separate_add _ _ := trivial

/-- Take the raised flag away. -/
def lower : LocalRule Unit Flag :=
  LocalRule.unguarded (fun _ => .raised) 0 {()} (fun location outside => by simp at outside)
    (fun _ _ => rfl)

/-- From the raised flag the rule reaches the lowered flag. -/
theorem lower_fires_lowered : lower.Fires (fun _ => .raised) (fun _ => .lowered) :=
  ⟨trivial, fun _ => .lowered, fun _ => trivial, fun _ => trivial, rfl, rfl⟩

/-- And it reaches the raised flag: the frame may hold a raised flag as well. -/
theorem lower_fires_raised : lower.Fires (fun _ => .raised) (fun _ => .raised) :=
  ⟨trivial, fun _ => .raised, fun _ => trivial, fun _ => trivial, rfl, rfl⟩

/-- **Negative**: a rule with two results from one state is the rule of no step. -/
theorem lower_is_no_step : ¬ ∃ step : Step Unit Flag, step.rule = lower := by
  rintro ⟨step, same⟩
  have equal := step.fires_unique (same ▸ lower_fires_lowered) (same ▸ lower_fires_raised)
  exact Flag.noConfusion (congrFun equal ())

end Controls

#print axioms comp_effectFootprinted
#print axioms eq_none_of_agreesOn
#print axioms bind_comm_of_independent
#print axioms Step.fires_unique
#print axioms Step.effectFootprinted
#print axioms publish_append
#print axioms publish_effectFootprinted
#print axioms publish_eq_none_of_agreesOn
#print axioms SpaceRules.observeAtom_fires_iff
#print axioms SpaceRules.replaceAtom_fires_iff
#print axioms Step.fire_observeAtom_eq_some_iff
#print axioms Step.fire_addAtom
#print axioms Step.fire_removeAtom_eq_some_iff
#print axioms Step.fire_removeAtom_eq_none
#print axioms Controls.lower_fires_lowered
#print axioms Controls.lower_fires_raised
#print axioms Controls.lower_is_no_step

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
