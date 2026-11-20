import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.AskTiming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.AskTiming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Unique
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Plain
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreDisciplines
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Product
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Located

/-!
# The ask-timing law, instantiated across the step web

`StepWeb.AskTiming` states once, for every guarded step with a split of its information, that asking
the guards before the firing's own tells restricts the step, with equality where the ask part entails
the tells. Each section below names a construction by its five choices (store, commit, guards, rules,
knowledge), gives its split, and says what the law gives there. In every section the guards are asked
after the firing's own tells (the construction as the tree has it) or before them (the law's form).

## One match (`oneMatch`)

Store: a bag. Commit: one match. Rules: fixed beside the store, as a set. Knowledge: one store.
The split: the knowledge along the extension with the equations of the takes and reads, then
the opened tells. The law's before-tells step is `Firing.AdmitsBeforeTells` (`oneMatch_admits_iff`).
It recovers `Firing.admits_of_beforeTells` and `Firing.beforeTells_iff_of_no_tells`, and adds equality
where the ask information entails the tells, equality without checks and collect query, and the transitions
(`oneMatch_succ_iff`, `oneMatch_succ_iff_of_no_tells`).

## Bags (`bags`), and `every`, maximal and `unique`

Store: a bag. Commit: bag-joint (`Bag.Admits`; the runtime spells it `bag`), and below `every`,
maximal and `unique`. Rules: fixed beside the store, as a set. Knowledge: one store. The split: the
knowledge with every member's matching,
then every member's tells (`Bag.models_information_iff`). The before-tells step is
`Bag.AdmitsBeforeTells` on bags with a member (`bags_admits_iff`); it recovers
`Bag.admits_of_beforeTells`, `Bag.beforeTells_iff_of_entailed_tells` and `Bag.beforeTells_iff_of_no_tells`.

Commits `every`, maximal and `unique` are restrictions of the bag step (`everyStep`, `maximalStep`,
`uniqueStep`). Since the law commutes with restriction, their before-tells forms are those
restrictions of the before-tells bag step (`every_beforeTells_admits_iff`, ...): the commit asked as it
is, the guards before the tells. This is how the set store's `DisciplinedStep d .beforeTells` reads
them.

Their definitions also quantify over admitted firings: `every` must hold every admitted match, and a
maximal bag no admitted larger bag. Read with those quantifiers at the before-tells timing
(`AdmitsEveryBeforeTells`, `AdmitsMaximalBeforeTells`, `AdmitsUniqueBeforeTells`), the commits are
still restrictions of the before-tells bag step (`beforeTells_of_ownBeforeTells`), but not of the same
commits read after the tells: completeness and maximality ask the none query of a further admitted match,
so they are antitone in the admitted set, and fewer firings are admitted before the tells.
`StepWeb.AskTimingControls` shows that in general neither includes the other. They agree where the ask
parts entail the tells (`everyBeforeTells_iff_of_entailed`, `maximalBeforeTells_iff_of_entailed`), in
particular for programs whose rules tell nothing. The pieces that do transfer: own guards before the
tells are own guards after them and joint guards before them (`admitsOwn_of_ownBeforeTells`,
`beforeTells_of_ownBeforeTells`), and completeness after the tells gives completeness before them
(`completeBeforeTells_of_complete`).

## The set store

Store: a set (`SetStore.Step`). Commit: any bag with a member, and each discipline of
`SetStoreSyntax.DisciplinedStep` (one, round, synchronous, bag-joint, every, maximal, unique). Rules:
fixed beside the store, as a set. Knowledge: one store. The timing parameter
`SetStore.AskTiming` reads the bag step's admission or the law's before-tells form of it
(`setStore_admitted_afterTells_iff`, `setStore_admitted_beforeTells_iff`). The law recovers
`SetStore.before_step_is_after`, and adds equality of the two set steps for programs whose rules tell
nothing (`setStore_step_iff_of_no_tells`), and the same two statements for every discipline
(`disciplined_before_is_after`, `disciplined_iff_of_no_tells`).

## Rules held in the store (`heldRules`)

Store: a bag of rows and a bag of rule occurrences. Commit: one match. Rules: held in the store, read
and kept or taken, beside an ambient set of codes. Knowledge: one store. The split: the knowledge
with the takes, reads and the closure's equations (each parameter with its argument), then the opened
tells. The law gives inclusion (`heldRules_admits_of_beforeTells`), equality where the ask part entails
the tells and for codes that tell nothing, and, for a plain code at a closed state, the before-tells
counterpart of `RFiring.admits_plain` (`heldRules_admits_iff_plain`).

## Worlds (`FiresBeforeTells`)

Store: a bag in each world, and a space of closed rows as a set. Commit: one match per firing move.
Rules: each world's own set and the space. Knowledge: located worlds, one store per world. The moves of
worlds are not
presented as an `Interface.Step`: a state of the interface has one frame and one store of knowledge,
and a bag of worlds has a store per world, each at its own frame. A world's firing is a one-match
firing of its program with the space (`fires_iff_worldFires`),
so the law applies world by world: firing moves before the tells are firing moves, hence moves
(`fires_of_firesBeforeTells`, `move_of_firesBeforeTells`), with equality where every rule of the firing
world and of the space tells nothing or asks nothing (`firesBeforeTells_iff`). A published row asks
nothing (`snapshot_quiet`), so publication never separates the two timings.

## Knowledge located per alternative (`LocatedBeforeTells`)

Store: one bag of rows, each at a location or shared. Commit: one match at one location. Rules: fixed
beside the store, as a set. Knowledge: located, one store per location. A located firing is admitted
when its location is live, its firing is admitted at the location's view, and its made rows and created
locations fit (`Hosting.Alternatives.Located.LFiring.Admits`). Its before-tells form restricts it to the
firings admitted before their tells at the view; it is the same admission with the firing asked before
its tells (`locatedBeforeTells_iff`), it is included in the located admission, equal to it for a firing
that tells nothing, and with one location it is one match before its tells
(`one_location_beforeTells_iff`, the counterpart of `one_location_admits_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb

open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface (Frames)
open _root_.Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.StepSpan
  (Succ)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

universe uO uT uH uE uOcc uR uC uZ uL

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

/-! ## One match -/

section OneMatchSplit

variable (X : Frames Tm Hom) {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

/-- **A one-match firing's information is split** into its ask information (the knowledge along the
extension, the equations of its takes and reads) and its opened tells. -/
theorem firing_splits (s : State Tm O) (f : Firing O E P s.frame) :
    Splits X (f.information X s) (f.askInformation X s) (f.opened X).tell :=
  splits_append X (f.askInformation X s) (f.opened X).tell

/-- A rule that tells nothing opens to no tells. -/
theorem opened_tell_nil {a : Obj} (f : Firing O E P a) (silent : f.rule.body.tell = []) :
    (f.opened X).tell = [] := by
  show f.rule.body.tell.map _ = []
  rw [silent, List.map_nil]

variable (O E P) in
/-- **The split of one match.** -/
def oneMatch [DecidableEq O] : AskSplit (step X O E P).toStep where
  ask {s} f := f.askInformation X s
  tells {_} f := (f.opened X).tell
  splits {s} f := firing_splits X s f

end OneMatchSplit

section OneMatch

variable {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {P : Program Tm}

/-- **Before its tells, one match is `Firing.AdmitsBeforeTells`.** -/
theorem oneMatch_admits_iff {s : State Tm O} (f : Firing O E P s.frame) :
    (beforeTells (step X O E P).toStep (oneMatch X O E P)).Admits f ↔ f.AdmitsBeforeTells X s :=
  (beforeTells_admits_iff (step X O E P).toStep (oneMatch X O E P) f).trans
    ⟨fun ⟨⟨shapes, enabled, solvable⟩, asked⟩ => ⟨shapes, enabled, solvable, asked⟩,
      fun ⟨shapes, enabled, solvable, asked⟩ => ⟨⟨shapes, enabled, solvable⟩, asked⟩⟩

/-- **Recovers `Firing.admits_of_beforeTells`**, through the law. -/
theorem oneMatch_admits_of_beforeTells {s : State Tm O} {f : Firing O E P s.frame}
    (before : f.AdmitsBeforeTells X s) : f.Admits X s :=
  admits_of_beforeTells _ _ ((oneMatch_admits_iff f).mpr before)

/-- **Recovers `Firing.beforeTells_iff_of_no_tells`**, through the law. -/
theorem oneMatch_beforeTells_iff_of_no_tells {s : State Tm O} (f : Firing O E P s.frame)
    (silent : (f.opened X).tell = []) : f.AdmitsBeforeTells X s ↔ f.Admits X s :=
  (oneMatch_admits_iff f).symm.trans (beforeTells_admits_iff_of_no_tells _ (oneMatch X O E P) silent)

/-- **Equality where the ask information entails the tells**, for one match. -/
theorem oneMatch_beforeTells_iff_of_entailed {s : State Tm O} (f : Firing O E P s.frame)
    (entailed : X.Entails (f.askInformation X s) fun _ σ => X.Models σ (f.opened X).tell) :
    f.AdmitsBeforeTells X s ↔ f.Admits X s :=
  (oneMatch_admits_iff f).symm.trans (beforeTells_admits_iff_of_entailed _ (oneMatch X O E P) entailed)

/-- **Equality without checks and collect query**, for one match: nothing is asked. -/
theorem oneMatch_beforeTells_iff_of_no_checks {s : State Tm O} (f : Firing O E P s.frame)
    (noChecks : f.rule.body.checks = []) (noCollect : f.rule.collect = []) :
    f.AdmitsBeforeTells X s ↔ f.Admits X s := by
  refine (oneMatch_admits_iff f).symm.trans (beforeTells_admits_iff_of_unguarded _ _ ?_)
  intro b σ
  have checks : (f.opened X).checks = [] := by
    show f.rule.body.checks.map _ = []
    rw [noChecks, List.map_nil]
  have collect : f.collectOpened X = [] := by
    show f.rule.collect.map _ = []
    rw [noCollect, List.map_nil]
  show f.Holds X s σ
  refine ⟨fun c member => ?_, fun q member => ?_⟩
  · rw [checks] at member
    exact absurd member List.not_mem_nil
  · rw [collect, List.zip_nil_left] at member
    exact absurd member List.not_mem_nil

/-- **One-match transitions before the tells**: a firing admitted before its tells reaches the
state. -/
theorem oneMatch_succ_iff {s t : State Tm O} :
    Succ (beforeTells (step X O E P).toStep (oneMatch X O E P)) s t ↔
      ∃ f : Firing O E P s.frame, f.AdmitsBeforeTells X s ∧ f.result X s = t := by
  constructor
  · rintro ⟨f, admitted, reached⟩
    exact ⟨f, (oneMatch_admits_iff f).mp admitted, reached⟩
  · rintro ⟨f, before, reached⟩
    exact ⟨f, (oneMatch_admits_iff f).mpr before, reached⟩

/-- **For a program whose rules tell nothing, both timings have the same transitions.** -/
theorem oneMatch_succ_iff_of_no_tells (silent : ∀ r ∈ P, r.body.tell = []) {s t : State Tm O} :
    Succ (beforeTells (step X O E P).toStep (oneMatch X O E P)) s t ↔ Succ (step X O E P).toStep s t :=
  succ_beforeTells_iff_of_entailed _ _ fun f =>
    (oneMatch X O E P).entailed_of_no_tells (opened_tell_nil X f (silent f.rule f.member))

end OneMatch

/-! ## Bags -/

section BagSplit

variable (X : Frames Tm Hom) {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

/-- **A bag's joint information is split** into the knowledge with every member's matching, and every
member's tells. -/
theorem bag_splits (s : State Tm O) (f : Bag O E P s.frame) :
    Splits X (f.information X s) (f.askInformation X s) (f.tells X s) :=
  fun _ σ => Bag.models_information_iff X s f σ

/-- **A solution of a bag's ask information solves the ask information of each member.** -/
theorem models_member_ask {s : State Tm O} {f : Bag O E P s.frame} {m : Member O E P f.ext}
    (inside : m ∈ f.members) {b : Obj} {σ : Hom (E.target f.ext) b}
    (solved : X.Models σ (f.askInformation X s)) : X.Models σ (m.firing.askInformation X s) := by
  intro e member
  apply solved e
  rcases List.mem_append.mp member with front | read
  · rcases List.mem_append.mp front with known | taken
    · exact List.mem_append_left _ known
    · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨m, inside, List.mem_append_left _ taken⟩)
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨m, inside, List.mem_append_right _ read⟩)

end BagSplit

section BagSteps

variable (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O] (E : Extensions.{uO, uH, uE} Hom)
  (P : Program Tm)

/-- **The split of a bag.** -/
def bags : AskSplit (bagStep X O E P).toStep where
  ask {s} f := f.askInformation X s
  tells {s} f := f.tells X s
  splits {s} f := bag_splits X s f

/-- **The `every` step over a set of rules**: the bag step restricted to the bags admitted as
`every`. -/
abbrev everyStep (Q : Set (Rule Tm)) :
    Interface.Step X O (State Tm O) (fun s => Bag O E P s.frame) :=
  Spaces.restrict (bagStep X O E P).toStep fun {s} f => f.AdmitsEvery X s Q

/-- **The maximal step**: the bag step restricted to the maximal bags. -/
abbrev maximalStep : Interface.Step X O (State Tm O) (fun s => Bag O E P s.frame) :=
  Spaces.restrict (bagStep X O E P).toStep fun {s} f => f.AdmitsMaximal X s

/-- **The `unique` step over a set of rules**: the bag step restricted to the bags admitted as
`unique`. -/
abbrev uniqueStep (Q : Set (Rule Tm)) :
    Interface.Step X O (State Tm O) (fun s => Bag O E P s.frame) :=
  Spaces.restrict (bagStep X O E P).toStep fun {s} f => f.AdmitsUnique X s Q

end BagSteps

section BagLaw

variable {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {P : Program Tm}

/-- **Before its tells, the bag step is `Bag.AdmitsBeforeTells` on bags with a member.** -/
theorem bags_admits_iff {s : State Tm O} (f : Bag O E P s.frame) :
    (beforeTells (bagStep X O E P).toStep (bags X O E P)).Admits f ↔
      f.members ≠ [] ∧ f.AdmitsBeforeTells X s :=
  (beforeTells_admits_iff (bagStep X O E P).toStep (bags X O E P) f).trans
    ⟨fun ⟨⟨⟨nonempty, fits⟩, enabled, solvable⟩, asked⟩ => ⟨nonempty, fits, enabled, solvable, asked⟩,
      fun ⟨nonempty, fits, enabled, solvable, asked⟩ => ⟨⟨⟨nonempty, fits⟩, enabled, solvable⟩, asked⟩⟩

/-- **Recovers `Bag.admits_of_beforeTells`**, for every bag, from the law's core. -/
theorem bag_admits_of_beforeTells {s : State Tm O} {f : Bag O E P s.frame}
    (before : f.AdmitsBeforeTells X s) : f.Admits X s :=
  ⟨before.1, before.2.1, before.2.2.1, entails_of_splits (bag_splits X s f) before.2.2.2⟩

/-- **Recovers `Bag.beforeTells_iff_of_entailed_tells`**, from the law's core. -/
theorem bag_beforeTells_iff_of_entailed {s : State Tm O} (f : Bag O E P s.frame)
    (entailed : X.Entails (f.askInformation X s) fun _ σ => X.Models σ (f.tells X s)) :
    f.AdmitsBeforeTells X s ↔ f.Admits X s :=
  ⟨bag_admits_of_beforeTells, fun admitted => ⟨admitted.1, admitted.2.1, admitted.2.2.1,
    (entails_iff_of_splits (bag_splits X s f) entailed).mpr admitted.2.2.2⟩⟩

/-- **Recovers `Bag.beforeTells_iff_of_no_tells`**, from the law's core. -/
theorem bag_beforeTells_iff_of_no_tells {s : State Tm O} (f : Bag O E P s.frame)
    (silent : ∀ m ∈ f.members, (m.firing.opened X).tell = []) :
    f.AdmitsBeforeTells X s ↔ f.Admits X s :=
  bag_beforeTells_iff_of_entailed f fun _ σ _ => by
    rw [Bag.tells_nil X s f silent]
    exact Frames.models_nil σ

/-- **`every` before the tells, by the law**: the restriction of the before-tells bag step to the bags
admitted as `every`. -/
theorem every_beforeTells_admits_iff (Q : Set (Rule Tm)) {s : State Tm O} (f : Bag O E P s.frame) :
    (beforeTells (everyStep X O E P Q) ((bags X O E P).restrict _)).Admits f ↔
      f.members ≠ [] ∧ f.AdmitsBeforeTells X s ∧ f.AdmitsEvery X s Q :=
  (beforeTells_restrict_admits_iff (bagStep X O E P).toStep (bags X O E P)
    (fun {s} f => f.AdmitsEvery X s Q) f).trans
    ⟨fun ⟨before, every⟩ =>
      ⟨((bags_admits_iff f).mp before).1, ((bags_admits_iff f).mp before).2, every⟩,
      fun ⟨nonempty, before, every⟩ => ⟨(bags_admits_iff f).mpr ⟨nonempty, before⟩, every⟩⟩

/-- **Maximal before the tells, by the law.** -/
theorem maximal_beforeTells_admits_iff {s : State Tm O} (f : Bag O E P s.frame) :
    (beforeTells (maximalStep X O E P) ((bags X O E P).restrict _)).Admits f ↔
      f.members ≠ [] ∧ f.AdmitsBeforeTells X s ∧ f.AdmitsMaximal X s :=
  (beforeTells_restrict_admits_iff (bagStep X O E P).toStep (bags X O E P)
    (fun {s} f => f.AdmitsMaximal X s) f).trans
    ⟨fun ⟨before, maximal⟩ =>
      ⟨((bags_admits_iff f).mp before).1, ((bags_admits_iff f).mp before).2, maximal⟩,
      fun ⟨nonempty, before, maximal⟩ => ⟨(bags_admits_iff f).mpr ⟨nonempty, before⟩, maximal⟩⟩

/-- **`unique` before the tells, by the law.** -/
theorem unique_beforeTells_admits_iff (Q : Set (Rule Tm)) {s : State Tm O} (f : Bag O E P s.frame) :
    (beforeTells (uniqueStep X O E P Q) ((bags X O E P).restrict _)).Admits f ↔
      f.members ≠ [] ∧ f.AdmitsBeforeTells X s ∧ f.AdmitsUnique X s Q :=
  (beforeTells_restrict_admits_iff (bagStep X O E P).toStep (bags X O E P)
    (fun {s} f => f.AdmitsUnique X s Q) f).trans
    ⟨fun ⟨before, unique⟩ =>
      ⟨((bags_admits_iff f).mp before).1, ((bags_admits_iff f).mp before).2, unique⟩,
      fun ⟨nonempty, before, unique⟩ => ⟨(bags_admits_iff f).mpr ⟨nonempty, before⟩, unique⟩⟩

end BagLaw

/-! ## `every`, maximal and `unique` with their quantifiers read before the tells -/

section Readings

variable (X : Frames Tm Hom) {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {P : Program Tm} (s : State Tm O)

/-- **Own guards before the tells**: the bag fitted, enabled as one commit, its information solvable,
and each member's guards at every solution of the knowledge with its own matching. -/
def AdmitsOwnBeforeTells (f : Bag O E P s.frame) : Prop :=
  f.Fits X s ∧ Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
    X.Solvable (f.information X s) ∧
    ∀ m ∈ f.members, X.Entails (m.firing.askInformation X s) (fun _ σ => m.firing.Holds X s σ)

/-- **Complete before the tells**: the key of every firing of the rules admitted before its tells is
the key of a member. -/
def CompleteBeforeTells (Q : Set (Rule Tm)) (f : Bag O E P s.frame) : Prop :=
  ∀ g : Firing O E P s.frame, g.rule ∈ Q → g.AdmitsBeforeTells X s →
    firingKey g ∈ f.members.map Member.key

/-- **`every` with its guards and its completeness read before the tells.** -/
def AdmitsEveryBeforeTells (Q : Set (Rule Tm)) (f : Bag O E P s.frame) : Prop :=
  AdmitsOwnBeforeTells X s f ∧ f.Within Q ∧ f.Distinct ∧ CompleteBeforeTells X s Q f

/-- **A maximal bag with its admission and its maximality read before the tells.** -/
def AdmitsMaximalBeforeTells (f : Bag O E P s.frame) : Prop :=
  f.AdmitsBeforeTells X s ∧ f.Distinct ∧ ∀ f' : Bag O E P s.frame, f'.AdmitsBeforeTells X s →
    f'.Distinct → (∀ k ∈ f.members.map Member.key, k ∈ f'.members.map Member.key) →
    ∀ k ∈ f'.members.map Member.key, k ∈ f.members.map Member.key

/-- **`unique` read before the tells**: `every` read before the tells, with one member. -/
def AdmitsUniqueBeforeTells (Q : Set (Rule Tm)) (f : Bag O E P s.frame) : Prop :=
  AdmitsEveryBeforeTells X s Q f ∧ f.members.length = 1

variable {X s}

/-- **Own guards before the tells are own guards after them**: the law, member by member. -/
theorem admitsOwn_of_ownBeforeTells {f : Bag O E P s.frame} (before : AdmitsOwnBeforeTells X s f) :
    f.AdmitsOwn X s :=
  ⟨before.1, before.2.1, before.2.2.1, fun m inside =>
    entails_of_splits (firing_splits X s m.firing) (before.2.2.2 m inside)⟩

/-- **Own guards before the tells are joint guards before the tells.** -/
theorem beforeTells_of_ownBeforeTells {f : Bag O E P s.frame} (before : AdmitsOwnBeforeTells X s f) :
    f.AdmitsBeforeTells X s :=
  ⟨before.1, before.2.1, before.2.2.1, fun _ _ solved m inside =>
    before.2.2.2 m inside _ _ (models_member_ask X inside solved)⟩

/-- **Own guards before and after the tells agree where each member's ask information entails its
tells.** -/
theorem ownBeforeTells_iff_of_entailed {f : Bag O E P s.frame}
    (entailed : ∀ m ∈ f.members,
      X.Entails (m.firing.askInformation X s) fun _ σ => X.Models σ (m.firing.opened X).tell) :
    AdmitsOwnBeforeTells X s f ↔ f.AdmitsOwn X s :=
  ⟨admitsOwn_of_ownBeforeTells, fun own => ⟨own.1, own.2.1, own.2.2.1, fun m inside =>
    (entails_iff_of_splits (firing_splits X s m.firing) (entailed m inside)).mpr (own.2.2.2 m inside)⟩⟩

/-- **Completeness after the tells gives completeness before them**: fewer firings are admitted before
the tells. -/
theorem completeBeforeTells_of_complete {Q : Set (Rule Tm)} {f : Bag O E P s.frame}
    (complete : f.Complete X s Q) : CompleteBeforeTells X s Q f :=
  fun g inQ before => complete g inQ (oneMatch_admits_of_beforeTells before)

/-- **The two completenesses agree where the rules' firings have their tells entailed.** -/
theorem completeBeforeTells_iff_of_entailed {Q : Set (Rule Tm)} {f : Bag O E P s.frame}
    (entailed : ∀ g : Firing O E P s.frame, g.rule ∈ Q →
      X.Entails (g.askInformation X s) fun _ σ => X.Models σ (g.opened X).tell) :
    CompleteBeforeTells X s Q f ↔ f.Complete X s Q :=
  ⟨fun before g inQ admitted =>
    before g inQ ((oneMatch_beforeTells_iff_of_entailed g (entailed g inQ)).mpr admitted),
    completeBeforeTells_of_complete⟩

/-- **`every` read before the tells is `every`** where the rules' firings have their tells entailed. -/
theorem everyBeforeTells_iff_of_entailed {Q : Set (Rule Tm)} {f : Bag O E P s.frame}
    (entailed : ∀ g : Firing O E P s.frame, g.rule ∈ Q →
      X.Entails (g.askInformation X s) fun _ σ => X.Models σ (g.opened X).tell) :
    AdmitsEveryBeforeTells X s Q f ↔ f.AdmitsEvery X s Q := by
  constructor
  · rintro ⟨own, within, distinct, complete⟩
    exact ⟨admitsOwn_of_ownBeforeTells own, within, distinct,
      (completeBeforeTells_iff_of_entailed entailed).mp complete⟩
  · rintro ⟨own, within, distinct, complete⟩
    exact ⟨(ownBeforeTells_iff_of_entailed fun m inside => entailed m.firing (within m inside)).mpr own,
      within, distinct, completeBeforeTells_of_complete complete⟩

/-- **A maximal bag read before the tells is a maximal bag** where every bag's ask information entails
its tells. -/
theorem maximalBeforeTells_iff_of_entailed {f : Bag O E P s.frame}
    (entailed : ∀ f' : Bag O E P s.frame,
      X.Entails (f'.askInformation X s) fun _ σ => X.Models σ (f'.tells X s)) :
    AdmitsMaximalBeforeTells X s f ↔ f.AdmitsMaximal X s := by
  have same : ∀ f' : Bag O E P s.frame, f'.AdmitsBeforeTells X s ↔ f'.Admits X s :=
    fun f' => bag_beforeTells_iff_of_entailed f' (entailed f')
  constructor
  · rintro ⟨before, distinct, maximal⟩
    exact ⟨(same f).mp before, distinct, fun f' admitted' distinct' sub =>
      maximal f' ((same f').mpr admitted') distinct' sub⟩
  · rintro ⟨admitted, distinct, maximal⟩
    exact ⟨(same f).mpr admitted, distinct, fun f' before' distinct' sub =>
      maximal f' ((same f').mp before') distinct' sub⟩

/-- **For a program whose rules tell nothing, `every` read before the tells is `every`.** -/
theorem everyBeforeTells_iff_of_no_tells (silent : ∀ r ∈ P, r.body.tell = []) {Q : Set (Rule Tm)}
    {f : Bag O E P s.frame} : AdmitsEveryBeforeTells X s Q f ↔ f.AdmitsEvery X s Q :=
  everyBeforeTells_iff_of_entailed fun g _ _ σ _ => by
    rw [opened_tell_nil X g (silent g.rule g.member)]
    exact Frames.models_nil σ

/-- **For a program whose rules tell nothing, a maximal bag read before the tells is a maximal
bag.** -/
theorem maximalBeforeTells_iff_of_no_tells (silent : ∀ r ∈ P, r.body.tell = [])
    {f : Bag O E P s.frame} : AdmitsMaximalBeforeTells X s f ↔ f.AdmitsMaximal X s :=
  maximalBeforeTells_iff_of_entailed fun f' _ σ _ => by
    rw [Bag.tells_nil X s f' fun m _ => opened_tell_nil X m.firing (silent m.rule m.member)]
    exact Frames.models_nil σ

/-- **For a program whose rules tell nothing, `unique` read before the tells is `unique`.** -/
theorem uniqueBeforeTells_iff_of_no_tells (silent : ∀ r ∈ P, r.body.tell = []) {Q : Set (Rule Tm)}
    {f : Bag O E P s.frame} : AdmitsUniqueBeforeTells X s Q f ↔ f.AdmitsUnique X s Q :=
  and_congr (everyBeforeTells_iff_of_no_tells silent) Iff.rfl

end Readings

/-! ## The set store -/

section SetStore

open _root_.Mettapedia.Logic.LP
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.OneFrame
  (Terms ext)

variable {signature : LPSignature} [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols] {P : Program (Terms (Term signature))}

/-- **After the tells, the set store reads the bag step**: a candidate with a member is admitted
exactly when the bag step admits it. -/
theorem setStore_admitted_afterTells_iff (rows : SetStore.Rows signature) (c : SetStore.Candidate P) :
    (c.members ≠ [] ∧ SetStore.admitted .afterTells rows c) ↔
      (bagStep (SetStore.X (signature := signature)) (Term signature × ℕ)
        (ext (SetStore.A (signature := signature))) P).toStep.Admits (s := SetStore.represent rows) c :=
  Iff.rfl

/-- **Before the tells, the set store reads the law's before-tells form of the bag step.** -/
theorem setStore_admitted_beforeTells_iff (rows : SetStore.Rows signature) (c : SetStore.Candidate P) :
    (c.members ≠ [] ∧ SetStore.admitted .beforeTells rows c) ↔
      (beforeTells (bagStep (SetStore.X (signature := signature)) (Term signature × ℕ)
        (ext (SetStore.A (signature := signature))) P).toStep
        (bags (SetStore.X (signature := signature)) (Term signature × ℕ)
          (ext (SetStore.A (signature := signature))) P)).Admits (s := SetStore.represent rows) c :=
  (bags_admits_iff (s := SetStore.represent rows) c).symm

/-- **Recovers `SetStore.before_step_is_after`**, from the law's inclusion. -/
theorem setStore_before_step_is_after {rows after : SetStore.Rows signature}
    (stepped : SetStore.Step .beforeTells P rows after) : SetStore.Step .afterTells P rows after := by
  obtain ⟨c, nonempty, yes, answer, accepted, result, changed⟩ := stepped
  have law := admits_of_beforeTells _ _ ((setStore_admitted_beforeTells_iff rows c).mp ⟨nonempty, yes⟩)
  exact ⟨c, nonempty, law.2, answer, accepted, result, changed⟩

/-- **For a program whose rules tell nothing, the two set steps are one.** -/
theorem setStore_step_iff_of_no_tells (silent : ∀ r ∈ P, r.body.tell = [])
    {rows after : SetStore.Rows signature} :
    SetStore.Step .beforeTells P rows after ↔ SetStore.Step .afterTells P rows after := by
  refine ⟨setStore_before_step_is_after, ?_⟩
  rintro ⟨c, nonempty, yes, answer, accepted, result, changed⟩
  refine ⟨c, nonempty, ?_, answer, accepted, result, changed⟩
  exact (bag_beforeTells_iff_of_no_tells (X := SetStore.X (signature := signature))
    (s := SetStore.represent rows) c
    fun m _ => opened_tell_nil _ m.firing (silent m.rule m.member)).mpr yes

/-- **Every set-store discipline before the tells is included in it after the tells**: the discipline
is asked as it is, and the admission at the timing. -/
theorem disciplined_before_is_after {d : SetStoreSyntax.Discipline} {rows after : SetStore.Rows signature}
    (stepped : SetStoreSyntax.DisciplinedStep d .beforeTells P rows after) :
    SetStoreSyntax.DisciplinedStep d .afterTells P rows after := by
  obtain ⟨c, nonempty, yes, allowed, answer, accepted, result, changed⟩ := stepped
  have law := admits_of_beforeTells _ _ ((setStore_admitted_beforeTells_iff rows c).mp ⟨nonempty, yes⟩)
  exact ⟨c, nonempty, law.2, allowed, answer, accepted, result, changed⟩

/-- **For a program whose rules tell nothing, every discipline has one step at both timings.** -/
theorem disciplined_iff_of_no_tells (silent : ∀ r ∈ P, r.body.tell = []) {d : SetStoreSyntax.Discipline}
    {rows after : SetStore.Rows signature} :
    SetStoreSyntax.DisciplinedStep d .beforeTells P rows after ↔
      SetStoreSyntax.DisciplinedStep d .afterTells P rows after := by
  refine ⟨disciplined_before_is_after, ?_⟩
  rintro ⟨c, nonempty, yes, allowed, answer, accepted, result, changed⟩
  refine ⟨c, nonempty, ?_, allowed, answer, accepted, result, changed⟩
  exact (bag_beforeTells_iff_of_no_tells (X := SetStore.X (signature := signature))
    (s := SetStore.represent rows) c
    fun m _ => opened_tell_nil _ m.firing (silent m.rule m.member)).mpr yes

end SetStore

/-! ## Rules held in the store -/

section HeldSplit

variable (X : Frames Tm Hom) {O : Type uOcc} {R : Type uR} {C : Type uC} {Z : Type uZ}
  {E : Extensions.{uO, uH, uE} Hom} {codes : RuleOccurrences.Codes Tm C Z}

/-- **The information of a firing of a held rule is split** into its ask part (the knowledge along the
extension, the equations of its takes and reads, and the closure's equations) and its opened tells. -/
theorem held_splits {s : RuleOccurrences.RState Tm O R C Z} (f : RuleOccurrences.RFiring O R E codes s) :
    Splits X (f.information X) (f.base.askInformation X s.toState ++ f.env X) (f.base.opened X).tell := by
  intro b σ
  show X.Models σ (f.base.information X s.toState ++ f.env X) ↔ _
  simp only [Frames.models_append, Firing.information_eq_ask]
  exact ⟨fun ⟨⟨asked, told⟩, closure⟩ => ⟨⟨asked, closure⟩, told⟩,
    fun ⟨⟨asked, closure⟩, told⟩ => ⟨⟨asked, told⟩, closure⟩⟩

variable (O R E codes) in
/-- **The split of a firing of a held rule.** -/
def heldRules [DecidableEq O] [DecidableEq R] (ambient : Set C) :
    AskSplit (RuleOccurrences.rstep X O R E codes ambient).toStep where
  ask {s} f := f.base.askInformation X s.toState ++ f.env X
  tells {_} f := (f.base.opened X).tell
  splits {_} f := held_splits X f

end HeldSplit

section Held

variable {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {R : Type uR} [DecidableEq R] {C : Type uC}
  {Z : Type uZ} {E : Extensions.{uO, uH, uE} Hom} {codes : RuleOccurrences.Codes Tm C Z}
  {ambient : Set C} {s : RuleOccurrences.RState Tm O R C Z}

/-- **Before its tells, a firing of a held rule** is prepared and has its guards at every solution of
its ask part, the closure's equations included. -/
theorem heldRules_admits_iff (f : RuleOccurrences.RFiring O R E codes s) :
    (beforeTells (RuleOccurrences.rstep X O R E codes ambient).toStep
      (heldRules X O R E codes ambient)).Admits f ↔
      f.Shapes X ambient ∧ Enabled (fun _ : O => ()) s.present (f.selection.commit (T := Unit)) ∧
        X.Solvable (f.information X) ∧
        X.Entails (f.base.askInformation X s.toState ++ f.env X) (fun _ σ => f.Holds X σ) :=
  (beforeTells_admits_iff (RuleOccurrences.rstep X O R E codes ambient).toStep
    (heldRules X O R E codes ambient) f).trans
    ⟨fun ⟨⟨shapes, enabled, solvable⟩, asked⟩ => ⟨shapes, enabled, solvable, asked⟩,
      fun ⟨shapes, enabled, solvable, asked⟩ => ⟨⟨shapes, enabled, solvable⟩, asked⟩⟩

/-- **Rules held in the store, inclusion**: a firing of a held rule admitted before its tells is
admitted. -/
theorem heldRules_admits_of_beforeTells {f : RuleOccurrences.RFiring O R E codes s}
    (before : (beforeTells (RuleOccurrences.rstep X O R E codes ambient).toStep
      (heldRules X O R E codes ambient)).Admits f) : f.Admits X ambient :=
  admits_of_beforeTells _ _ before

/-- **Rules held in the store, equality** where the ask part, closure included, entails the tells. -/
theorem heldRules_beforeTells_iff_of_entailed {f : RuleOccurrences.RFiring O R E codes s}
    (entailed : X.Entails (f.base.askInformation X s.toState ++ f.env X)
      fun _ σ => X.Models σ (f.base.opened X).tell) :
    (beforeTells (RuleOccurrences.rstep X O R E codes ambient).toStep
      (heldRules X O R E codes ambient)).Admits f ↔ f.Admits X ambient :=
  beforeTells_admits_iff_of_entailed _ (heldRules X O R E codes ambient) entailed

/-- **Rules held in the store, equality for a code that tells nothing.** -/
theorem heldRules_beforeTells_iff_of_no_tells {f : RuleOccurrences.RFiring O R E codes s}
    (silent : f.spec.body.tell = []) :
    (beforeTells (RuleOccurrences.rstep X O R E codes ambient).toStep
      (heldRules X O R E codes ambient)).Admits f ↔ f.Admits X ambient :=
  beforeTells_admits_iff_of_no_tells _ (heldRules X O R E codes ambient) (opened_tell_nil X f.base silent)

/-- **A plain code at a closed state, before its tells**: its firing of the present step admitted before
its tells, and the shapes of the rule occurrences. The counterpart of `RFiring.admits_plain`. -/
theorem heldRules_admits_iff_plain (f : RuleOccurrences.RFiring O R E codes s) (closed : s.Closed)
    (plain : f.spec.Plain) :
    (beforeTells (RuleOccurrences.rstep X O R E codes ambient).toStep
      (heldRules X O R E codes ambient)).Admits f ↔
      f.base.AdmitsBeforeTells X s.toState ∧ f.RuleShapes ambient := by
  rw [heldRules_admits_iff]
  unfold RuleOccurrences.RFiring.Shapes Firing.AdmitsBeforeTells Firing.Shapes
  rw [f.env_of_plain X plain, List.append_nil, f.information_of_plain X plain,
    f.fresh_iff_base X closed plain]
  constructor
  · rintro ⟨⟨fresh, rows, rules⟩, enabled, solvable, asks⟩
    exact ⟨⟨⟨fresh, rows⟩, enabled, solvable,
      fun b σ solved => (f.holds_iff_base X plain σ).mp (asks b σ solved)⟩, rules⟩
  · rintro ⟨⟨⟨fresh, rows⟩, enabled, solvable, asks⟩, rules⟩
    exact ⟨⟨fresh, rows, rules⟩, enabled, solvable,
      fun b σ solved => (f.holds_iff_base X plain σ).mpr (asks b σ solved)⟩

/-- **Rules held in the store, transitions**: a transition before the tells is a transition. -/
theorem heldRules_succ_of_beforeTells {s t : RuleOccurrences.RState Tm O R C Z}
    (stepped : Succ (beforeTells (RuleOccurrences.rstep X O R E codes ambient).toStep
      (heldRules X O R E codes ambient)) s t) :
    Succ (RuleOccurrences.rstep X O R E codes ambient).toStep s t :=
  succ_of_beforeTells _ _ stepped

end Held

/-! ## Worlds -/

section Worlds

open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence
  (System)

variable {O : Type uOcc}

/-- **The firing moves of a bag of worlds through a transition relation for each program**: one world
moves by the relation of its program with the space, and no other world and not the space changes. -/
def WorldFires (succ : Program Tm → State Tm O → State Tm O → Prop) (W W' : Worlds.Bag Tm O) : Prop :=
  ∃ (rest : Multiset (System Tm O)) (space : Program Tm) (S : System Tm O) (t : State Tm O),
    succ (S.program ∪ space) S.state t ∧ W = ⟨S ::ₘ rest, space⟩ ∧
      W' = ⟨(⟨S.program, t⟩ : System Tm O) ::ₘ rest, space⟩

/-- Firing moves are monotone in the transition relations. -/
theorem worldFires_mono {succ₁ succ₂ : Program Tm → State Tm O → State Tm O → Prop}
    (le : ∀ Q s t, succ₁ Q s t → succ₂ Q s t) {W W' : Worlds.Bag Tm O}
    (fires : WorldFires succ₁ W W') : WorldFires succ₂ W W' := by
  obtain ⟨rest, space, S, t, stepped, rfl, rfl⟩ := fires
  exact ⟨rest, space, S, t, le _ _ _ stepped, rfl, rfl⟩

/-- **A published row asks nothing**: the closed row of a world's atom has no checks and no collect query. -/
theorem snapshot_quiet (s : State Tm O) (atom : Tm s.frame) :
    (Hosting.Alternatives.Worlds.snapshot s atom).body.checks = [] ∧
      (Hosting.Alternatives.Worlds.snapshot s atom).collect = [] :=
  ⟨rfl, rfl⟩

variable [DecidableEq O] (X : Frames Tm Hom) (E : Extensions.{uO, uH, uE} Hom)

/-- **The firing moves of worlds are one-match transitions, world by world.** -/
theorem fires_iff_worldFires (W W' : Worlds.Bag Tm O) :
    Worlds.Fires (Worlds.events X O E) W W' ↔
      WorldFires (fun Q => Succ (step X O E Q).toStep) W W' := by
  constructor
  · rintro ⟨rest, space, S, ⟨f, admitted⟩⟩
    exact ⟨rest, space, S, f.result X S.state, ⟨f, admitted, rfl⟩, rfl, rfl⟩
  · rintro ⟨rest, space, S, t, ⟨f, admitted, rfl⟩, rfl, rfl⟩
    exact Worlds.Fires.fire (family := Worlds.events X O E) rest space S ⟨f, admitted⟩

/-- **The firing moves of worlds with each world's guards asked before its tells.** -/
def FiresBeforeTells (W W' : Worlds.Bag Tm O) : Prop :=
  WorldFires (fun Q => Succ (beforeTells (step X O E Q).toStep (oneMatch X O E Q))) W W'

/-- **Worlds, inclusion**: a firing move before the tells is a firing move. -/
theorem fires_of_firesBeforeTells {W W' : Worlds.Bag Tm O} (fires : FiresBeforeTells X E W W') :
    Worlds.Fires (Worlds.events X O E) W W' :=
  (fires_iff_worldFires X E W W').mpr
    (worldFires_mono (fun _ _ _ stepped => succ_of_beforeTells _ _ stepped) fires)

/-- **Worlds, inclusion in the moves.** -/
theorem move_of_firesBeforeTells (J : Worlds.Joining X O) {W W' : Worlds.Bag Tm O}
    (fires : FiresBeforeTells X E W W') : Worlds.Move X J (Worlds.events X O E) W W' :=
  (fires_of_firesBeforeTells X E fires).move X J

/-- **Worlds, equality**: where every rule of every world's program and of the space tells nothing or
asks nothing, the firing moves before and after the tells are the same. -/
theorem firesBeforeTells_iff {W W' : Worlds.Bag Tm O}
    (quiet : ∀ S ∈ W.worlds, ∀ r ∈ S.program ∪ W.space,
      r.body.tell = [] ∨ (r.body.checks = [] ∧ r.collect = [])) :
    FiresBeforeTells X E W W' ↔ Worlds.Fires (Worlds.events X O E) W W' := by
  refine ⟨fires_of_firesBeforeTells X E, fun fires => ?_⟩
  obtain ⟨rest, space, S, ⟨f, admitted⟩⟩ := fires
  have here := quiet S (Multiset.mem_cons_self S rest) f.rule f.member
  refine ⟨rest, space, S, f.result X S.state, ⟨f, ?_, rfl⟩, rfl, rfl⟩
  rcases here with silent | ⟨noChecks, noCollect⟩
  · exact (beforeTells_admits_iff_of_no_tells _ _ (opened_tell_nil X f silent)).mpr admitted
  · exact (oneMatch_admits_iff f).mpr ((oneMatch_beforeTells_iff_of_no_checks f noChecks noCollect).mpr admitted)

end Worlds

/-! ## Knowledge located per alternative -/

section Located

open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Located
  (LState LFiring embed lift one_location_admits_iff visible_embed)

variable {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {P : Program Tm} {L : Type uL} [DecidableEq L]

variable (X) in
/-- **A located firing with its guards asked before its tells**: admitted, with its firing admitted
before its tells at the view of its location. -/
def LocatedBeforeTells (s : LState Tm O L) (f : LFiring O L E P s.frame) : Prop :=
  f.Admits X s ∧ f.firing.AdmitsBeforeTells X (s.view f.loc)

/-- **The located admission with the firing asked before its tells.** -/
theorem locatedBeforeTells_iff (s : LState Tm O L) (f : LFiring O L E P s.frame) :
    LocatedBeforeTells X s f ↔
      f.loc ∈ s.live ∧ f.firing.AdmitsBeforeTells X (s.view f.loc) ∧
        (∀ o ∈ f.firing.selection.made, o ∉ s.present) ∧ f.born.Nodup ∧ (∀ ℓ ∈ f.born, ℓ ∉ s.live) ∧
        f.places.length = f.firing.selection.made.length ∧
        ∀ p ∈ f.places, p = none ∨ p = some f.loc ∨ ∃ ℓ ∈ f.born, p = some ℓ := by
  constructor
  · rintro ⟨⟨live, -, side⟩, before⟩
    exact ⟨live, before, side⟩
  · rintro ⟨live, before, side⟩
    exact ⟨⟨live, oneMatch_admits_of_beforeTells before, side⟩, before⟩

/-- **Located knowledge, inclusion.** -/
theorem located_admits_of_beforeTells {s : LState Tm O L} {f : LFiring O L E P s.frame}
    (before : LocatedBeforeTells X s f) : f.Admits X s :=
  before.1

/-- **Located knowledge, equality for a firing that tells nothing.** -/
theorem locatedBeforeTells_iff_of_no_tells {s : LState Tm O L} {f : LFiring O L E P s.frame}
    (silent : (f.firing.opened X).tell = []) : LocatedBeforeTells X s f ↔ f.Admits X s :=
  ⟨located_admits_of_beforeTells, fun admitted =>
    ⟨admitted, (oneMatch_beforeTells_iff_of_no_tells (s := s.view f.loc) f.firing silent).mpr
      admitted.2.1⟩⟩

omit [DecidableEq L] in
/-- The view of the one location is the state, for admission before the tells. -/
theorem beforeTells_view_embed (s : State Tm O) (f : Firing O E P s.frame) :
    f.AdmitsBeforeTells X ((embed s).view PUnit.unit) ↔ f.AdmitsBeforeTells X s := by
  obtain ⟨frame, knowledge, present, label⟩ := s
  change f.AdmitsBeforeTells X ⟨frame, knowledge,
    (embed (⟨frame, knowledge, present, label⟩ : State Tm O)).visible PUnit.unit, label⟩ ↔ _
  rw [visible_embed]

omit [DecidableEq L] in
/-- **With one location, the located firing before its tells is one match before its tells.** -/
theorem one_location_beforeTells_iff (s : State Tm O) (f : Firing O E P s.frame) :
    LocatedBeforeTells X (embed s) (lift f) ↔ f.AdmitsBeforeTells X s :=
  ⟨fun before => (beforeTells_view_embed s f).mp before.2,
    fun before => ⟨(one_location_admits_iff X s f).mpr (oneMatch_admits_of_beforeTells before),
      (beforeTells_view_embed s f).mpr before⟩⟩

end Located

#print axioms oneMatch_admits_iff
#print axioms oneMatch_admits_of_beforeTells
#print axioms oneMatch_beforeTells_iff_of_no_tells
#print axioms oneMatch_beforeTells_iff_of_entailed
#print axioms oneMatch_beforeTells_iff_of_no_checks
#print axioms oneMatch_succ_iff
#print axioms oneMatch_succ_iff_of_no_tells
#print axioms bags_admits_iff
#print axioms bag_admits_of_beforeTells
#print axioms bag_beforeTells_iff_of_entailed
#print axioms bag_beforeTells_iff_of_no_tells
#print axioms every_beforeTells_admits_iff
#print axioms maximal_beforeTells_admits_iff
#print axioms unique_beforeTells_admits_iff
#print axioms admitsOwn_of_ownBeforeTells
#print axioms beforeTells_of_ownBeforeTells
#print axioms ownBeforeTells_iff_of_entailed
#print axioms completeBeforeTells_of_complete
#print axioms completeBeforeTells_iff_of_entailed
#print axioms everyBeforeTells_iff_of_entailed
#print axioms maximalBeforeTells_iff_of_entailed
#print axioms everyBeforeTells_iff_of_no_tells
#print axioms maximalBeforeTells_iff_of_no_tells
#print axioms uniqueBeforeTells_iff_of_no_tells
#print axioms setStore_admitted_afterTells_iff
#print axioms setStore_admitted_beforeTells_iff
#print axioms setStore_before_step_is_after
#print axioms setStore_step_iff_of_no_tells
#print axioms disciplined_before_is_after
#print axioms disciplined_iff_of_no_tells
#print axioms held_splits
#print axioms heldRules_admits_iff
#print axioms heldRules_admits_of_beforeTells
#print axioms heldRules_beforeTells_iff_of_entailed
#print axioms heldRules_beforeTells_iff_of_no_tells
#print axioms heldRules_admits_iff_plain
#print axioms heldRules_succ_of_beforeTells
#print axioms fires_iff_worldFires
#print axioms fires_of_firesBeforeTells
#print axioms move_of_firesBeforeTells
#print axioms firesBeforeTells_iff
#print axioms locatedBeforeTells_iff
#print axioms located_admits_of_beforeTells
#print axioms locatedBeforeTells_iff_of_no_tells
#print axioms beforeTells_view_embed
#print axioms one_location_beforeTells_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb
