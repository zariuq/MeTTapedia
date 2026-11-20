import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.AskTimingInstances
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.AskTimingControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples

/-!
# Controls for the ask-timing law across the step web

All controls are at one frame over first-order terms whose constants and unknowns are numerals. The
central rule (`selfRule`, from `JointFirings.AskTimingControls`) tells `x = 5` and checks `x = 5`: it
is admitted after its tells and refused before them, because before the tells nothing binds `x`. A
fresh opening can send `x` anywhere (`firing_refused`, `bag_refused`), so every firing of it, with any
opening, is refused before its tells wherever every assignment solves its ask part, for instance where
the ask part is empty.

## Strictness, construction by construction

* **One match** (bag store, one match, fixed set of rules, one store): `oneMatch_strict`, from the
  tree's `strict_inclusion` through the law.
* **Bags** (bag store, a bag of matches enabled as one commit): `bags_strict`, from the tree's
  `self_bag_after` and `self_bag_before_refused`.
* **The split is data**: with the whole information as the ask part, the same firing is admitted
  before its tells (`split_matters`).
* **Rules held in the store** (bag store with rule occurrences, one match, a persistently held rule,
  one store): `held_strict`. The held code unfolds to the self-telling rule. Where the closure's
  equations go is a real choice (`closure_in_ask`): a held rule whose check `x = 5` is met by its
  argument `5` is admitted before its tells by the split that puts the closure in the ask part, and
  refused by the split that counts it among the tells.
* **Worlds** (a bag of rows per world and a space, one match per move, each world's rules, a store per
  world): from one world holding the self-telling rule, a firing move exists after the tells and none
  before them (`worlds_strict`). Positive control: a world whose rules tell nothing or ask nothing has
  firing moves before the tells (`quiet_world_fires`).
* **Knowledge located per alternative** (one bag of rows at locations, one match at a location, fixed
  rules, a store per location): with one location, the self-telling firing is admitted and refused
  before its tells (`located_strict`).
* **The set store** (a set of rows, any bag with a member, fixed rules, one store): from no rows, a
  rule that tells `x = 5`, checks it and makes `x` has a set step after the tells and none before them
  (`setStore_strict`).

## `every`, maximal and `unique` (bag store, the commits named, fixed set of rules, one store)

The program `pair` holds the self-telling rule and a rule that does nothing (`idleRule`). At the empty
state:

* **`every`** (`every_incomparable`): the bag of both rules is `every` and not `every` read before the
  tells; the bag of the idle rule alone is `every` read before the tells and not `every`.
* **maximal** (`maximal_incomparable`) and **`unique`** (`unique_incomparable`): the same separation.
* **The law's restriction form is strict for `every`** (`every_law_strict`): the bag of both rules is a
  step of the `every` step and not of its before-tells form.

So reading the quantifiers of `every`, maximal and `unique` at the before-tells timing gives commits
that neither include nor are included in the same commits read after the tells: the law's inclusion
does not transfer to them.

## Synchronous and bag-joint commits

The tree includes the bag-joint commit in the synchronous one (`Bag.admitsSnapshot_of_admits`). The
inclusion is strict (`snapshot_not_joint`): a bag that takes a token and reads the same token is
admitted with each member enabled on its own, and refused as one commit.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.AskTimingControls

open _root_.Mettapedia.Logic.LP
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.StepSpan
  (Succ)
open _root_.Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.AskTimingControls
  (Tm X E v c selfRule selfProgram emptyState selfFiring self_after self_before_refused
    strict_inclusion self_bag_after self_bag_before_refused)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence
  (System)

/-! ## A fresh opening of a rule that checks its unknown is refused before its tells -/

section Refusal

variable {O : Type} {P : Program Tm} {s : State Tm O}

/-- **The ask information of a firing** at a state without knowledge, of a rule without take and read
patterns, is empty. -/
theorem askInformation_nil (g : Firing O E P s.frame) (noKnowledge : s.knowledge = [])
    (noTake : g.rule.body.take = []) (noRead : g.rule.body.read = []) : g.askInformation X s = [] := by
  show X.applyStore (E.weaken g.ext) s.knowledge ++
      g.matching X s (g.rule.body.take.map (X.act g.opening)) g.selection.taken ++
      g.matching X s (g.rule.body.read.map (X.act g.opening)) g.selection.read = []
  rw [noKnowledge, noTake, noRead]
  rfl

/-- **The ask information of a bag** at a state without knowledge, whose members' rules have no take
and read patterns, is empty. -/
theorem bag_askInformation_nil (f : Bag O E P s.frame) (noKnowledge : s.knowledge = [])
    (noPatterns : ∀ m ∈ f.members, m.rule.body.take = [] ∧ m.rule.body.read = []) :
    f.askInformation X s = [] := by
  have each : ∀ m ∈ f.members, m.matchingInformation X s = [] := by
    intro m inside
    show m.firing.matching X s (m.rule.body.take.map (X.act m.opening)) m.selection.taken ++
        m.firing.matching X s (m.rule.body.read.map (X.act m.opening)) m.selection.read = []
    rw [(noPatterns m inside).1, (noPatterns m inside).2]
    rfl
  show X.applyStore (E.weaken f.ext) s.knowledge ++ f.members.flatMap (fun m => m.matchingInformation X s) = []
  rw [noKnowledge, List.flatMap_eq_nil_iff.mpr each]
  rfl

variable [DecidableEq O]

/-- **A firing that checks its unknown `x` against `n ≠ 0` is refused before its tells** wherever every
assignment solves its ask information: its fresh opening lets `x` be sent to `0`. -/
theorem firing_refused (g : Firing O E P s.frame) {n : ℕ} (other : n ≠ 0)
    (check : Check.equal (v 0) (c n) ∈ g.rule.body.checks)
    (askFree : ∀ σ : Subst atoms, X.Models (b := PUnit.unit) σ (g.askInformation X s)) :
    ¬ g.AdmitsBeforeTells X s := by
  rintro ⟨⟨fresh, -⟩, -, -, asks⟩
  obtain ⟨u, -, opened⟩ := fresh PUnit.unit (Subst.id atoms) (fun _ => c 0)
  have zero : u.applyTerm (g.opening.applyTerm (v 0)) = c 0 :=
    opened (v 0) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_, check, List.mem_cons_self⟩))))
  have held : u.applyTerm (g.opening.applyTerm (v 0)) = c n :=
    (asks PUnit.unit u (askFree u)).1 _ (List.mem_map_of_mem check)
  exact other (Term.const.inj (zero.symm.trans held)).symm

/-- **A bag with such a member is refused before its tells** wherever every assignment solves its ask
information. -/
theorem bag_refused (f : Bag O E P s.frame) {m : Member O E P f.ext} (inside : m ∈ f.members) {n : ℕ}
    (other : n ≠ 0) (check : Check.equal (v 0) (c n) ∈ m.rule.body.checks)
    (askFree : ∀ σ : Subst atoms, X.Models (b := PUnit.unit) σ (f.askInformation X s)) :
    ¬ f.AdmitsBeforeTells X s := by
  rintro ⟨fits, -, -, asks⟩
  obtain ⟨u, -, opened⟩ := Bag.fresh_member X (fun _ _ => ⟨Subst.id atoms⟩) fits.1 inside
    PUnit.unit (Subst.id atoms) (fun _ => c 0)
  have zero : u.applyTerm (m.opening.applyTerm (v 0)) = c 0 :=
    opened (v 0) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_, check, List.mem_cons_self⟩))))
  have held : u.applyTerm (m.opening.applyTerm (v 0)) = c n :=
    (asks PUnit.unit u (askFree u) m inside).1 _ (List.mem_map_of_mem check)
  exact other (Term.const.inj (zero.symm.trans held)).symm

end Refusal

/-- **Every firing of the self-telling rule is refused before its tells at the empty state.** -/
theorem self_refused {P : Program Tm} (g : Firing ℕ E P PUnit.unit) (isSelf : g.rule = selfRule) :
    ¬ g.AdmitsBeforeTells X emptyState :=
  firing_refused g (n := 5) (by decide) (by rw [isSelf]; exact List.mem_cons_self) fun σ => by
    rw [askInformation_nil (s := emptyState) g rfl (by rw [isSelf]; rfl) (by rw [isSelf]; rfl)]
    exact Interface.Frames.models_nil (X := X) σ

/-! ## One match and bags -/

/-- **One match: admitted after its tells, refused before them, through the law.** -/
theorem oneMatch_strict :
    (step X ℕ E selfProgram).toStep.Admits (s := emptyState) selfFiring ∧
      ¬ (beforeTells (step X ℕ E selfProgram).toStep (oneMatch X ℕ E selfProgram)).Admits
        (s := emptyState) selfFiring :=
  ⟨strict_inclusion.1, fun before => strict_inclusion.2 ((oneMatch_admits_iff selfFiring).mp before)⟩

/-- **Bags: admitted after the tells, refused before them, through the law.** -/
theorem bags_strict :
    (bagStep X ℕ E selfProgram).toStep.Admits (s := emptyState) (Bag.single selfFiring) ∧
      ¬ (beforeTells (bagStep X ℕ E selfProgram).toStep (bags X ℕ E selfProgram)).Admits
        (s := emptyState) (Bag.single selfFiring) :=
  ⟨⟨List.cons_ne_nil _ _, self_bag_after⟩,
    fun before => self_bag_before_refused ((bags_admits_iff (Bag.single selfFiring)).mp before).2⟩

/-- **The split is data**: with the whole information as the ask part, the firing that the split of
one match refuses before its tells is admitted. -/
theorem split_matters :
    (beforeTells (step X ℕ E selfProgram).toStep (AskSplit.whole _)).Admits (s := emptyState)
        selfFiring ∧
      ¬ (beforeTells (step X ℕ E selfProgram).toStep (oneMatch X ℕ E selfProgram)).Admits
        (s := emptyState) selfFiring :=
  ⟨(beforeTells_whole_admits_iff (step X ℕ E selfProgram).toStep selfFiring).mpr self_after,
    oneMatch_strict.2⟩

/-! ## Rules held in the store -/

namespace Held

/-- One code, unfolding to the self-telling rule. -/
def codes : RuleOccurrences.Codes Tm Unit Unit :=
  ⟨fun _ => RuleOccurrences.Spec.ofRule selfRule, fun _ _ _ => False, fun _ _ _ => none⟩

/-- The empty state, holding that code persistently as occurrence `0`, without arguments. -/
def holding : RuleOccurrences.RState Tm ℕ ℕ Unit Unit :=
  { toState := emptyState, rules := {0}, held := fun _ => ⟨(), [], .persistent, ()⟩ }

/-- The firing of the held occurrence. -/
def firing : RuleOccurrences.RFiring ℕ ℕ E codes holding :=
  ⟨.held 0, PUnit.unit, Subst.id atoms, ⟨[], [], []⟩, [], [], [], [], []⟩

theorem closed : holding.Closed := fun _ _ => rfl

theorem plain : firing.spec.Plain := RuleOccurrences.Spec.plain_ofRule selfRule

theorem shapes : firing.RuleShapes (∅ : Set Unit) :=
  ⟨Finset.mem_singleton_self 0, rfl, rfl, List.nodup_nil, rfl,
    fun _ inside => absurd inside List.not_mem_nil, rfl, List.nodup_nil,
    fun _ inside => absurd inside List.not_mem_nil, rfl⟩

/-- **Rules held in the store: admitted after the tells, refused before them.** -/
theorem held_strict :
    (RuleOccurrences.rstep X ℕ ℕ E codes ∅).toStep.Admits firing ∧
      ¬ (beforeTells (RuleOccurrences.rstep X ℕ ℕ E codes ∅).toStep
        (heldRules X ℕ ℕ E codes ∅)).Admits firing :=
  ⟨(RuleOccurrences.RFiring.admits_plain X firing closed plain ∅).mpr ⟨self_after, shapes⟩,
    fun before => self_before_refused ((heldRules_admits_iff_plain firing closed plain).mp before).1⟩

end Held

namespace Closure

/-- A code with one parameter `x` that checks `x = 5` and tells nothing. -/
def spec : RuleOccurrences.Spec Tm Unit Unit :=
  ⟨PUnit.unit, ⟨[], [], [], [.equal (v 0) (c 5)], []⟩, [], [v 0], [], [], [], [], []⟩

def codes : RuleOccurrences.Codes Tm Unit Unit :=
  ⟨fun _ => spec, fun _ _ _ => False, fun _ _ _ => none⟩

/-- The empty state, holding the code persistently as occurrence `0`, with the argument `5`. -/
def holding : RuleOccurrences.RState Tm ℕ ℕ Unit Unit :=
  { toState := emptyState, rules := {0}, held := fun _ => ⟨(), [c 5], .persistent, ()⟩ }

/-- The firing of the held occurrence. -/
def firing : RuleOccurrences.RFiring ℕ ℕ E codes holding :=
  ⟨.held 0, PUnit.unit, Subst.id atoms, ⟨[], [], []⟩, [], [], [], [], []⟩

/-- **The split that counts the closure's equations among the tells.** -/
def closureAsTells : AskSplit (RuleOccurrences.rstep X ℕ ℕ E codes ∅).toStep where
  ask {s} f := f.base.askInformation X s.toState
  tells {_} f := (f.base.opened X).tell ++ f.env X
  splits {s} f := by
    intro b σ
    show X.Models σ (f.base.information X s.toState ++ f.env X) ↔ _
    simp only [Interface.Frames.models_append, Firing.information_eq_ask]
    exact ⟨fun ⟨⟨asked, told⟩, closure⟩ => ⟨asked, told, closure⟩,
      fun ⟨asked, told, closure⟩ => ⟨⟨asked, told⟩, closure⟩⟩

theorem fresh : firing.Fresh X := by
  intro b g h
  refine ⟨h, fun t mentioned => ?_, fun t _ => ?_⟩
  · rcases mentioned with mentioned | ⟨ρ, -, inside⟩
    · change emptyState.Mentions t at mentioned
      simp [State.Mentions, emptyState] at mentioned
    · change t ∈ [c 5] at inside
      obtain rfl := List.mem_singleton.mp inside
      rfl
  · change h.applyTerm ((Subst.id atoms).applyTerm t) = h.applyTerm t
    rw [Subst.applyTerm_id]

theorem shapes : firing.Shapes X (∅ : Set Unit) :=
  ⟨fresh, ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩,
    ⟨Finset.mem_singleton_self 0, rfl, rfl, List.nodup_nil, rfl,
      fun _ inside => absurd inside List.not_mem_nil, rfl, List.nodup_nil,
      fun _ inside => absurd inside List.not_mem_nil, rfl⟩⟩

/-- **By the law's split, the held rule is admitted before its tells**: its argument binds `x`. -/
theorem before :
    (beforeTells (RuleOccurrences.rstep X ℕ ℕ E codes ∅).toStep (heldRules X ℕ ℕ E codes ∅)).Admits
      firing := by
  refine (heldRules_admits_iff firing).mpr ⟨shapes, enabled_nil ∅, ⟨PUnit.unit, fun _ => c 5, ?_⟩, ?_⟩
  · intro e inside
    change e ∈ [(v 0, c 5)] at inside
    obtain rfl := List.mem_singleton.mp inside
    rfl
  · intro b σ asked
    have bound : σ.applyTerm (v 0) = c 5 :=
      asked (v 0, c 5) (List.mem_append_right _ List.mem_cons_self)
    refine ⟨⟨fun check inside => ?_, fun _ inside => (by cases inside)⟩, fun _ inside => (by cases inside),
      fun _ inside => (by cases inside), fun _ inside => (by cases inside), fun _ inside => (by cases inside)⟩
    obtain rfl := List.mem_singleton.mp inside
    exact bound

/-- **Counting the closure's equations among the tells refuses the same firing before its tells.** -/
theorem refused_closureAsTells :
    ¬ (beforeTells (RuleOccurrences.rstep X ℕ ℕ E codes ∅).toStep closureAsTells).Admits firing := by
  intro admitted
  have asks := ((beforeTells_admits_iff _ closureAsTells firing).mp admitted).2
  have zero := (asks PUnit.unit (fun _ => c 0) (fun _ inside => absurd inside List.not_mem_nil)).1.1 _
    List.mem_cons_self
  have impossible : c 0 = c 5 := zero
  simp [c] at impossible

/-- **Where the closure's equations go is a real choice**: the held rule is admitted, admitted before
its tells by the law's split, and refused before its tells by the split that counts the closure among
the tells. -/
theorem closure_in_ask :
    (RuleOccurrences.rstep X ℕ ℕ E codes ∅).toStep.Admits firing ∧
      (beforeTells (RuleOccurrences.rstep X ℕ ℕ E codes ∅).toStep (heldRules X ℕ ℕ E codes ∅)).Admits
        firing ∧
      ¬ (beforeTells (RuleOccurrences.rstep X ℕ ℕ E codes ∅).toStep closureAsTells).Admits firing :=
  ⟨heldRules_admits_of_beforeTells before, before, refused_closureAsTells⟩

end Closure

/-! ## Worlds -/

namespace WorldControls

/-- One world running the self-telling rule at the empty state. -/
def selfWorld : System Tm ℕ := ⟨selfProgram, emptyState⟩

/-- The bag of that one world, with an empty space. -/
def start : Worlds.Bag Tm ℕ := ⟨{selfWorld}, ∅⟩

/-- **Worlds: a firing move after the tells, none before them.** -/
theorem worlds_strict :
    (∃ W', Worlds.Fires (Worlds.events X ℕ E) start W') ∧
      ∀ W', ¬ FiresBeforeTells X E start W' := by
  refine ⟨⟨_, Worlds.Fires.fire (family := Worlds.events X ℕ E) 0 ∅ selfWorld
    ⟨Worlds.widen Set.subset_union_left selfFiring, self_after⟩⟩, ?_⟩
  rintro W' ⟨rest, space, S, t, ⟨g, before, -⟩, same, -⟩
  have worlds : ({selfWorld} : Multiset (System Tm ℕ)) = S ::ₘ rest := congrArg Worlds.Bag.worlds same
  have spaces : (∅ : Program Tm) = space := congrArg Worlds.Bag.space same
  obtain ⟨rfl, -⟩ := (Multiset.singleton_eq_cons_iff rest).mp worlds
  subst spaces
  have isSelf : g.rule = selfRule := by
    rcases g.member with inside | inside
    · exact inside
    · exact absurd inside (Set.notMem_empty _)
  exact self_refused g isSelf ((oneMatch_admits_iff g).mp before)

/-- One world running the example program at a token. -/
def tokenWorld : System Tm ℕ := ⟨Examples.demo, Examples.tokenState⟩

/-- **Positive control**: the example program's rules tell nothing or ask nothing, so its world fires
before the tells exactly as after them; taking the token is such a firing move. -/
theorem quiet_world_fires :
    FiresBeforeTells X E ⟨{tokenWorld}, ∅⟩
      ⟨{(⟨Examples.demo, Examples.consumeFiring.result X Examples.tokenState⟩ : System Tm ℕ)}, ∅⟩ := by
  refine (firesBeforeTells_iff X E ?_).mpr
    (Worlds.Fires.fire (family := Worlds.events X ℕ E) 0 ∅ tokenWorld
      ⟨Worlds.widen Set.subset_union_left Examples.consumeFiring, Examples.consume_admitted⟩)
  intro S inside r member
  obtain rfl := Multiset.mem_singleton.mp inside
  rcases member with member | member
  · change r ∈ Examples.demo at member
    simp only [Examples.demo, Set.mem_insert_iff, Set.mem_singleton_iff] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
  · exact absurd member (Set.notMem_empty _)

/-- **Located knowledge: with one location, admitted after the tells, refused before them.** -/
theorem located_strict :
    (Hosting.Alternatives.Located.lift (s := emptyState) selfFiring).Admits X
        (Hosting.Alternatives.Located.embed emptyState) ∧
      ¬ LocatedBeforeTells X (Hosting.Alternatives.Located.embed emptyState)
        (Hosting.Alternatives.Located.lift (s := emptyState) selfFiring) :=
  ⟨(Hosting.Alternatives.Located.one_location_admits_iff X emptyState selfFiring).mpr self_after,
    fun before => self_before_refused ((one_location_beforeTells_iff emptyState selfFiring).mp before)⟩

end WorldControls

/-! ## The set store -/

namespace SetStoreControl

/-- Tell `x = 5`, check `x = 5`, make `x`. -/
def maker : Rule Tm := ⟨PUnit.unit, ⟨[], [], [(v 0, c 5)], [.equal (v 0) (c 5)], [v 0]⟩, []⟩

def program : Program Tm := {maker}

def makerFiring : Firing (Term atoms × ℕ) E program PUnit.unit :=
  ⟨maker, Set.mem_singleton _, PUnit.unit, Subst.id atoms, ⟨[], [], [(c 0, 1)]⟩, []⟩

theorem maker_admitted : makerFiring.Admits X (SetStore.represent (∅ : Finset (Term atoms))) := by
  refine ⟨⟨?_, List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro b g h
    refine ⟨h, fun t mentioned => ?_, fun t _ => ?_⟩
    · simp [State.Mentions, SetStore.represent] at mentioned
    · change h.applyTerm ((Subst.id atoms).applyTerm t) = h.applyTerm t
      rw [Subst.applyTerm_id]
  · refine ⟨by simp [makerFiring, Selection.commit], by simp [makerFiring, Selection.commit],
      by simp [makerFiring, Selection.commit], ?_, fun query inside => by cases inside⟩
    simp [makerFiring, Selection.commit, SetStore.represent]
  · refine ⟨PUnit.unit, (fun _ => c 5), fun equation inside => ?_⟩
    obtain rfl := List.mem_singleton.mp inside
    rfl
  · intro b σ solved
    refine ⟨fun check member => ?_, fun query member => by cases member⟩
    obtain rfl := List.mem_singleton.mp member
    exact solved (v 0, c 5) List.mem_cons_self

/-- **The set store: from no rows, a set step after the tells, none before them.** -/
theorem setStore_strict :
    (∃ after, SetStore.Step .afterTells program ∅ after) ∧
      ∀ after, ¬ SetStore.Step .beforeTells program ∅ after := by
  constructor
  · let bag := Bag.single makerFiring
    have yes : bag.Admits X (SetStore.represent (∅ : Finset (Term atoms))) :=
      (Bag.single_admits_iff X _ makerFiring).mpr maker_admitted
    obtain ⟨answer, accepted⟩ := (FirstOrder.accepted_iff_consistent [(v 0, c 5)]).mpr
      ⟨(fun _ => c 5), fun equation member => by obtain rfl := List.mem_singleton.mp member; rfl⟩
    refine ⟨_, bag, List.cons_ne_nil _ _, yes, answer, ?_, rfl, ?_⟩
    · change unifyTotal (Bag.information X (SetStore.represent ∅) (Bag.single makerFiring)) = some answer
      simp only [Bag.single, Bag.information_single]
      exact accepted
    · rintro ⟨names, same⟩
      have made : answer.applyTerm (v 0) ∈ SetStore.setResult ∅ bag answer :=
        SetStore.mem_update.mpr (Or.inr (Finset.mem_image.mpr
          ⟨v 0, List.mem_toFinset.mpr List.mem_cons_self, rfl⟩))
      rw [same, Finset.image_empty] at made
      exact Finset.notMem_empty _ made
  · rintro after ⟨bag, nonempty, before, -⟩
    obtain ⟨m, inside⟩ := List.exists_mem_of_ne_nil _ nonempty
    have isMaker : m.rule = maker := m.member
    refine bag_refused bag inside (n := 5) (by decide) (by rw [isMaker]; exact List.mem_cons_self)
      (fun σ => ?_) before
    rw [bag_askInformation_nil bag rfl fun m' _ => by
      have isMaker' : m'.rule = maker := m'.member
      rw [isMaker']
      exact ⟨rfl, rfl⟩]
    exact Interface.Frames.models_nil (X := X) σ

end SetStoreControl

/-! ## `every`, maximal and `unique` -/

namespace Quantifiers

/-- A rule that does nothing. -/
def idleRule : Rule Tm := ⟨PUnit.unit, ⟨[], [], [], [], []⟩, []⟩

/-- The self-telling rule and the idle rule. -/
def pair : Program Tm := {selfRule, idleRule}

def selfIn : Firing ℕ E pair PUnit.unit :=
  ⟨selfRule, Or.inl rfl, PUnit.unit, Subst.id atoms, ⟨[], [], []⟩, []⟩

def idleIn : Firing ℕ E pair PUnit.unit :=
  ⟨idleRule, Or.inr rfl, PUnit.unit, Subst.id atoms, ⟨[], [], []⟩, []⟩

/-- The bag of the idle rule alone. -/
def idleBag : Bag ℕ E pair PUnit.unit := ⟨PUnit.unit, [Member.ofFiring idleIn]⟩

/-- The bag of the self-telling rule alone. -/
def selfBag : Bag ℕ E pair PUnit.unit := ⟨PUnit.unit, [Member.ofFiring selfIn]⟩

/-- The bag of both rules. -/
def bothBag : Bag ℕ E pair PUnit.unit := ⟨PUnit.unit, [Member.ofFiring idleIn, Member.ofFiring selfIn]⟩

theorem self_ne_idle : selfRule ≠ idleRule := fun same => by
  have lengths : selfRule.body.tell.length = idleRule.body.tell.length :=
    congrArg (fun r : Rule Tm => r.body.tell.length) same
  exact absurd lengths (by decide)

theorem pair_cases {r : Rule Tm} (inside : r ∈ pair) : r = selfRule ∨ r = idleRule := by
  simpa only [pair, Set.mem_insert_iff, Set.mem_singleton_iff] using inside

theorem pair_patterns {r : Rule Tm} (inside : r ∈ pair) : r.body.take = [] ∧ r.body.read = [] := by
  rcases pair_cases inside with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- **The key of a firing of `pair` with its shapes** is the self-telling rule's or the idle rule's, with
no rows. -/
theorem pair_key {a : PUnit.{1}} (g : Firing ℕ E pair a)
    (takes : g.rule.body.take.length = g.selection.taken.length)
    (reads : g.rule.body.read.length = g.selection.read.length) :
    firingKey g = (selfRule, [], []) ∨ firingKey g = (idleRule, [], []) := by
  have patterns := pair_patterns g.member
  have taken : g.selection.taken = [] :=
    List.length_eq_zero_iff.mp (by rw [← takes, patterns.1, List.length_nil])
  have read : g.selection.read = [] :=
    List.length_eq_zero_iff.mp (by rw [← reads, patterns.2, List.length_nil])
  show (g.rule, g.selection.taken, g.selection.read) = (selfRule, [], []) ∨
    (g.rule, g.selection.taken, g.selection.read) = (idleRule, [], [])
  rw [taken, read]
  rcases pair_cases g.member with same | same
  · exact Or.inl (by rw [same])
  · exact Or.inr (by rw [same])

theorem firing_askFree (g : Firing ℕ E pair PUnit.unit) (σ : Subst atoms) :
    X.Models (b := PUnit.unit) σ (g.askInformation X emptyState) := by
  rw [askInformation_nil (s := emptyState) g rfl (pair_patterns g.member).1 (pair_patterns g.member).2]
  exact Interface.Frames.models_nil (X := X) σ

theorem bag_askFree (f : Bag ℕ E pair PUnit.unit) (σ : Subst atoms) :
    X.Models (b := PUnit.unit) σ (f.askInformation X emptyState) := by
  rw [bag_askInformation_nil (s := emptyState) f rfl fun m _ => pair_patterns m.member]
  exact Interface.Frames.models_nil (X := X) σ

theorem selfIn_admitted : selfIn.Admits X emptyState := self_after

theorem idleIn_admitted : idleIn.Admits X emptyState := by
  refine ⟨⟨fun b g h => ⟨h, fun t mentioned => ?_, fun t inside => ?_⟩, List.nodup_nil, List.nodup_nil,
    rfl, rfl, rfl, rfl⟩, enabled_nil ∅, ⟨PUnit.unit, Subst.id atoms, Interface.Frames.models_nil _⟩,
    fun b σ _ => ⟨fun c inside => ?_, fun q inside => ?_⟩⟩
  · simp [State.Mentions, emptyState] at mentioned
  · exact absurd inside List.not_mem_nil
  · exact absurd inside List.not_mem_nil
  · exact absurd inside List.not_mem_nil

/-- The self-telling member of a bag makes it refused before the tells. -/
theorem self_member_refused (f : Bag ℕ E pair PUnit.unit) {m : Member ℕ E pair f.ext}
    (inside : m ∈ f.members) (isSelf : m.rule = selfRule) : ¬ f.AdmitsBeforeTells X emptyState :=
  bag_refused f inside (n := 5) (by decide) (by rw [isSelf]; exact List.mem_cons_self) (bag_askFree f)

theorem both_fresh : bothBag.Fresh X emptyState := by
  intro b g h₁ h₂
  refine ⟨h₂, ⟨fun t mentioned => ?_, fun t inside => ?_⟩, fun t _ => ?_⟩
  · simp [State.Mentions, emptyState] at mentioned
  · exact absurd inside List.not_mem_nil
  · change h₂.applyTerm ((Subst.id atoms).applyTerm t) = h₂.applyTerm t
    rw [Subst.applyTerm_id]

theorem both_own : bothBag.AdmitsOwn X emptyState := by
  refine ⟨⟨both_fresh, List.nodup_nil, List.nodup_nil, ?_⟩, enabled_nil ∅, ?_, ?_⟩
  · intro m inside
    change m ∈ [Member.ofFiring idleIn, Member.ofFiring selfIn] at inside
    rcases List.mem_cons.mp inside with rfl | inside
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · obtain rfl := List.mem_singleton.mp inside
      exact ⟨rfl, rfl, rfl, rfl⟩
  · refine ⟨PUnit.unit, (fun _ => c 5), fun equation inside => ?_⟩
    change equation ∈ [(v 0, c 5)] at inside
    obtain rfl := List.mem_singleton.mp inside
    rfl
  · intro m inside
    change m ∈ [Member.ofFiring idleIn, Member.ofFiring selfIn] at inside
    rcases List.mem_cons.mp inside with rfl | inside
    · exact idleIn_admitted.2.2.2
    · obtain rfl := List.mem_singleton.mp inside
      exact selfIn_admitted.2.2.2

theorem both_distinct : bothBag.Distinct := by
  refine List.nodup_cons.mpr ⟨fun inside => ?_, List.nodup_singleton _⟩
  exact self_ne_idle (congrArg Prod.fst (List.mem_singleton.mp inside)).symm

theorem both_complete : bothBag.Complete X emptyState pair := by
  intro g _ admitted
  rcases pair_key g admitted.1.2.2.2.1 admitted.1.2.2.2.2.1 with key | key
  · rw [key]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · rw [key]
    exact List.mem_cons_self

theorem both_every : bothBag.AdmitsEvery X emptyState pair :=
  ⟨both_own, fun m _ => m.member, both_distinct, both_complete⟩

theorem both_not_before : ¬ bothBag.AdmitsBeforeTells X emptyState :=
  self_member_refused bothBag (m := Member.ofFiring selfIn) (List.mem_cons_of_mem _ List.mem_cons_self) rfl

theorem idle_admits : idleBag.Admits X emptyState :=
  (Bag.single_admits_iff X emptyState idleIn).mpr idleIn_admitted

theorem idle_ownBefore : AdmitsOwnBeforeTells X emptyState idleBag :=
  ⟨idle_admits.1, idle_admits.2.1, idle_admits.2.2.1, fun m inside => by
    obtain rfl := List.mem_singleton.mp inside
    exact fun _ _ _ => ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil⟩⟩

theorem self_key_not_idle : (selfRule, ([] : List ℕ), ([] : List ℕ)) ∉ idleBag.members.map Member.key :=
  fun inside => self_ne_idle (congrArg Prod.fst (List.mem_singleton.mp inside))

theorem idle_completeBefore : CompleteBeforeTells X emptyState pair idleBag := by
  intro g _ before
  rcases pair_key g before.1.2.2.2.1 before.1.2.2.2.2.1 with key | key
  · exact absurd before (self_refused g (congrArg Prod.fst key))
  · rw [key]
    exact List.mem_cons_self

theorem idle_everyBefore : AdmitsEveryBeforeTells X emptyState pair idleBag :=
  ⟨idle_ownBefore, fun m _ => m.member, List.nodup_singleton _, idle_completeBefore⟩

theorem idle_not_complete : ¬ idleBag.Complete X emptyState pair :=
  fun complete => self_key_not_idle (complete selfIn (Or.inl rfl) selfIn_admitted)

/-- **`every` and `every` read before the tells are incomparable**, on bags with members. -/
theorem every_incomparable :
    (bothBag.AdmitsEvery X emptyState pair ∧ ¬ AdmitsEveryBeforeTells X emptyState pair bothBag) ∧
      (AdmitsEveryBeforeTells X emptyState pair idleBag ∧ ¬ idleBag.AdmitsEvery X emptyState pair) :=
  ⟨⟨both_every, fun every => both_not_before (beforeTells_of_ownBeforeTells every.1)⟩,
    ⟨idle_everyBefore, fun every => idle_not_complete every.2.2.2⟩⟩

/-- **The law's restriction form of `every` is strict**: the bag of both rules is a step of the
`every` step and not of its before-tells form. -/
theorem every_law_strict :
    (everyStep X ℕ E pair pair).Admits (s := emptyState) bothBag ∧
      ¬ (beforeTells (everyStep X ℕ E pair pair) ((bags X ℕ E pair).restrict _)).Admits
        (s := emptyState) bothBag :=
  ⟨⟨⟨List.cons_ne_nil _ _, Bag.admits_of_admitsOwn X both_own⟩, both_every⟩,
    fun before => both_not_before ((every_beforeTells_admits_iff pair bothBag).mp before).2.1⟩

theorem both_maximal : bothBag.AdmitsMaximal X emptyState := by
  refine ⟨Bag.admits_of_admitsOwn X both_own, both_distinct, fun f' admitted' _ _ k inside => ?_⟩
  obtain ⟨m, inM, rfl⟩ := List.mem_map.mp inside
  obtain ⟨takes, reads, -, -⟩ := admitted'.1.2.2.2 m inM
  rcases pair_key m.firing takes reads with key | key
  · rw [← firingKey_firing, key]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · rw [← firingKey_firing, key]
    exact List.mem_cons_self

theorem idle_beforeTells : idleBag.AdmitsBeforeTells X emptyState :=
  beforeTells_of_ownBeforeTells idle_ownBefore

theorem idle_maximalBefore : AdmitsMaximalBeforeTells X emptyState idleBag := by
  refine ⟨idle_beforeTells, List.nodup_singleton _, fun f' before' _ _ k inside => ?_⟩
  obtain ⟨m, inM, rfl⟩ := List.mem_map.mp inside
  obtain ⟨takes, reads, -, -⟩ := before'.1.2.2.2 m inM
  rcases pair_key m.firing takes reads with key | key
  · exact absurd before' (self_member_refused f' inM (congrArg Prod.fst key))
  · rw [← firingKey_firing, key]
    exact List.mem_cons_self

/-- **A maximal bag and a maximal bag read before the tells are incomparable**, on bags with
members. -/
theorem maximal_incomparable :
    (bothBag.AdmitsMaximal X emptyState ∧ ¬ AdmitsMaximalBeforeTells X emptyState bothBag) ∧
      (AdmitsMaximalBeforeTells X emptyState idleBag ∧ ¬ idleBag.AdmitsMaximal X emptyState) := by
  refine ⟨⟨both_maximal, fun maximal => both_not_before maximal.1⟩, idle_maximalBefore, ?_⟩
  rintro ⟨-, -, maximal⟩
  refine self_key_not_idle (maximal bothBag both_maximal.1 both_distinct (fun k inside => ?_) _
    (List.mem_cons_of_mem _ List.mem_cons_self))
  obtain rfl := List.mem_singleton.mp inside
  exact List.mem_cons_self

theorem self_unique : selfBag.AdmitsUnique X emptyState {selfRule} := by
  refine ⟨⟨(Bag.admitsOwn_single X emptyState (Member.ofFiring selfIn)).mpr selfIn_admitted,
    fun m inside => ?_, List.nodup_singleton _, fun g inQ admitted => ?_⟩, rfl⟩
  · obtain rfl := List.mem_singleton.mp inside
    rfl
  · rcases pair_key g admitted.1.2.2.2.1 admitted.1.2.2.2.2.1 with key | key
    · rw [key]
      exact List.mem_cons_self
    · exact absurd ((congrArg Prod.fst key).symm.trans inQ) self_ne_idle.symm

/-- **`unique` and `unique` read before the tells are incomparable.** -/
theorem unique_incomparable :
    (selfBag.AdmitsUnique X emptyState {selfRule} ∧
        ¬ AdmitsUniqueBeforeTells X emptyState {selfRule} selfBag) ∧
      (AdmitsUniqueBeforeTells X emptyState pair idleBag ∧ ¬ idleBag.AdmitsUnique X emptyState pair) :=
  ⟨⟨self_unique, fun unique => self_member_refused selfBag (m := Member.ofFiring selfIn)
      List.mem_cons_self rfl (beforeTells_of_ownBeforeTells unique.1.1)⟩,
    ⟨⟨idle_everyBefore, rfl⟩, fun unique => idle_not_complete unique.1.2.2.2⟩⟩

end Quantifiers

/-! ## Synchronous and bag-joint commits -/

namespace Synchronous

/-- Read a token `1`. -/
def readOne : Rule Tm := ⟨PUnit.unit, ⟨[], [c 1], [], [], []⟩, []⟩

def program : Program Tm := {Examples.consume, readOne}

/-- Take the token `0` and make `1`. -/
def takeIt : OneMember action ℕ program :=
  ⟨Examples.consume, Or.inl rfl, Subst.id atoms, ⟨[0], [], [1]⟩, []⟩

/-- Read the same token. -/
def readIt : OneMember action ℕ program :=
  ⟨readOne, Or.inr rfl, Subst.id atoms, ⟨[], [0], []⟩, []⟩

/-- Both, at once. -/
def takeAndRead : Bag ℕ E program PUnit.unit := bagOf action [takeIt, readIt]

theorem fresh : takeAndRead.Fresh X Examples.tokenState := by
  intro b g h₁ h₂
  refine ⟨Subst.id atoms, ⟨fun t mentioned => ?_, fun t inside => ?_⟩, fun t inside => ?_⟩
  · rcases mentioned with known | known | ⟨o, -, rfl⟩
    · exact absurd known List.not_mem_nil
    · exact absurd known List.not_mem_nil
    · rfl
  · change t ∈ [Examples.c 1, Examples.c 2] at inside
    rcases List.mem_cons.mp inside with rfl | inside
    · rfl
    · obtain rfl := List.mem_singleton.mp inside
      rfl
  · change t ∈ [c 1] at inside
    obtain rfl := List.mem_singleton.mp inside
    rfl

/-- **A bag that takes a token and reads it is admitted with each member enabled on its own, and
refused as one commit.** -/
theorem snapshot_not_joint :
    takeAndRead.AdmitsSnapshot X Examples.tokenState ∧ ¬ takeAndRead.Admits X Examples.tokenState := by
  refine ⟨⟨⟨fresh, by decide, by decide, fun m inside => ?_⟩, fun m inside => ?_, ?_, ?_⟩,
    fun admitted => absurd admitted.2.1 (by decide)⟩
  · change m ∈ [takeIt, readIt] at inside
    rcases List.mem_cons.mp inside with rfl | inside
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · obtain rfl := List.mem_singleton.mp inside
      exact ⟨rfl, rfl, rfl, rfl⟩
  · change m ∈ [takeIt, readIt] at inside
    rcases List.mem_cons.mp inside with rfl | inside
    · exact ⟨by decide, by decide, by decide, by decide, fun query inside => by cases inside⟩
    · obtain rfl := List.mem_singleton.mp inside
      exact ⟨by decide, by decide, by decide, by decide, fun query inside => by cases inside⟩
  · refine ⟨PUnit.unit, Subst.id atoms, fun equation inside => ?_⟩
    change equation ∈ [(Examples.c 1, Examples.c 1), (c 1, Examples.c 1)] at inside
    rcases List.mem_cons.mp inside with rfl | inside
    · rfl
    · obtain rfl := List.mem_singleton.mp inside
      rfl
  · intro b σ _ m inside
    change m ∈ [takeIt, readIt] at inside
    rcases List.mem_cons.mp inside with rfl | inside
    · exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩
    · obtain rfl := List.mem_singleton.mp inside
      exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

end Synchronous

#print axioms firing_refused
#print axioms bag_refused
#print axioms self_refused
#print axioms oneMatch_strict
#print axioms bags_strict
#print axioms split_matters
#print axioms Held.held_strict
#print axioms Closure.closure_in_ask
#print axioms WorldControls.worlds_strict
#print axioms WorldControls.quiet_world_fires
#print axioms WorldControls.located_strict
#print axioms SetStoreControl.setStore_strict
#print axioms Quantifiers.every_incomparable
#print axioms Quantifiers.every_law_strict
#print axioms Quantifiers.maximal_incomparable
#print axioms Quantifiers.unique_incomparable
#print axioms Synchronous.snapshot_not_joint

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.AskTimingControls
