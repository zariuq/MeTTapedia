import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Independent
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Isolation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderRoundTrace

/-!
# One round, two presentations

A step construction is named by five choices: its store, its commit, its guards, its rules and its
knowledge. This module relates two constructions whose commit is a **round** and which differ in their
layer.

* **A bag of matches of a program admitted with each member's guards at its own information**
  (`JointFirings.Bag.AdmitsOwn`, at the one-frame action of a substitution action with the identity
  extension). Store: a bag of occurrences, labelled by the state, made identities labelled by the made
  rows. Commit: a bag of matches whose openings are jointly fresh, whose selections are enabled as one
  commit, and whose information is jointly solvable. Guards: each member's at every solution of its own
  information, its own tells included. Rules: a fixed set beside the store, opened per use. Knowledge:
  one store.
* **A round of the base layer** (`AnnotatedRuns.Round`). Store: a bag of occurrences with labels fixed
  once for all identities. Commit: a list of rule instances, each admitted at one configuration, with
  jointly consistent equations, pairwise compatible (`AnnotatedRuns.Compatible`: independent selections,
  and checks and predicate queries that ignore each other's writes). Guards: each instance's at every
  solution of its own problem, its own tells included. Rules: instances already opened, no program.
  Knowledge: one store.

The map between them is the tree's map from the one-match step to the base layer, member by member:
states by `OneFrame.embed`, firings by `OneFrame.toFirstOrder` (`baseFiring`, `image`). The base layer
asks that made identities already carry their made rows (`KeepsLabels`), the restriction
`OneFrame.keeping` of the one-match step.

## The two presentations agree

* **`round_image_iff`**: the image of a bag admitted on its own at an embedded state, whose members keep
  labels, is a round exactly when its members ignore each other's writes (`IgnoreEachOther`) at the cut
  of each pair. Equation guards always do; none queries and count checks and collect queries do when what the
  other member takes and makes is apart from their patterns at that cut. No hypothesis on the terms of
  the state.
* **`round_image_of_positive`**: so for positive rules (equation guards, no collect query) the image of such a
  bag is a round.
* **`admitsOwn_of_round`**, conversely: a round whose members are the images of members of the program
  with jointly fresh openings and one seen set per collect pattern is the image of a bag admitted on its
  own, and its members keep labels. Every rule; no hypothesis on the terms of the state. Joint freshness
  cannot be read back from the image, which forgets the openings (`Controls.twins_not_image`).
* **`admitsOwn_iff_round`**: for positive rules, at an embedded state, the two presentations define one
  round: a bag admitted on its own whose members keep labels, and a round of jointly fresh images with one
  seen set per collect pattern.
* **Every state at the one frame** (`round_image_canonical`): one round can be labelled by the labels its
  result carries (`roundLabel`). They agree with the state's on its present rows (`roundLabel_present`),
  so the state relabelled by them is structurally congruent to it (`congruent_relabel`) and admits the
  same bags (`admitsOwn_of_congruent`); under them every member keeps labels (`keepsLabels_roundLabel`).
  So at every state at the one frame the image of a bag admitted on its own is a round exactly when its
  members ignore each other's writes (`round_image_canonical_iff`), and always for positive rules; and for
  positive rules a bag is admitted on its own exactly when its image is a round under the labels of its
  round, its openings are jointly fresh, and it has one seen set per collect pattern
  (`admitsOwn_iff_round_canonical`).
* **Guards at the joint information** (`round_image_of_admits_fixed`): at an embedded state that mentions
  only fixed terms, the image of a bag of positive rules admitted with the guards at the joint
  information, keeping labels, is a round. Fixed terms are used here only, to make joint guards own guards
  (`JointFirings.admitsOwn_of_fixed`); without them it fails (`Controls.jointGuards_need_fixed`).

## What carries over from the base layer's trace theory

* **`orders_equivalent`**, **`orders_run`**: the images of any two orders of the members of a round are
  one contextual trace (`AnnotatedRuns.Round.orders_equivalent`); every order runs in the base layer and
  reaches one class (`Round.executable_perm`, `Round.follow_perm`).
* **`native_traces`**: the base runs of any two orders, as runs of the first-order step, are one trace of
  its transport (`AnnotatedRuns.firstOrderTransport`, by `FirstOrderNativeRuns.native_trace_of_rounds`).
* **`orders_equivalent_of_admitsOwn`**, **`native_traces_of_admitsOwn`**: hence for every bag of positive
  rules admitted on its own, at every state at the one frame, under the labels of its round.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Rounds

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled Independent)
open OneFrame (Terms frames ext embed toFirstOrder)
open JointFirings (OneMember bagOf)
open Scope (Positive Congruent)

universe uT uS uO

/-! ## Lists -/

section Lists

universe uA uB

/-- Two families of lists over a list are disjoint when each item's are and every two items' are. -/
theorem disjoint_flatMap {α : Type uA} {β : Type uB} (f g : α → List β) :
    ∀ (l : List α), (∀ a ∈ l, (f a).Disjoint (g a)) →
      l.Pairwise (fun a b => (f a).Disjoint (g b) ∧ (f b).Disjoint (g a)) →
        (l.flatMap f).Disjoint (l.flatMap g)
  | [], _, _ => by
      intro _ inF
      simp at inF
  | a :: rest, own, pairs => by
      intro o inF inG
      rw [List.flatMap_cons, List.mem_append] at inF inG
      have later := List.pairwise_cons.mp pairs
      rcases inF with here | there <;> rcases inG with here' | there'
      · exact own a List.mem_cons_self here here'
      · obtain ⟨b, inB, member⟩ := List.mem_flatMap.mp there'
        exact (later.1 b inB).1 here member
      · obtain ⟨b, inB, member⟩ := List.mem_flatMap.mp there
        exact (later.1 b inB).2 member here'
      · exact disjoint_flatMap f g rest (fun b inB => own b (List.mem_cons_of_mem a inB)) later.2
          there there'

/-- A list is mapped onto another of its length when every pair of the zip is. -/
theorem map_eq_of_zip {α : Type uA} {β : Type uB} (f : α → β) :
    ∀ (as : List α) (bs : List β), as.length = bs.length → (∀ p ∈ as.zip bs, f p.1 = p.2) →
      as.map f = bs
  | [], [], _, _ => rfl
  | [], _ :: _, lengths, _ => by simp at lengths
  | _ :: _, [], lengths, _ => by simp at lengths
  | a :: as, b :: bs, lengths, pairs => by
      have head : f a = b := pairs (a, b) List.mem_cons_self
      have tail := map_eq_of_zip f as bs (Nat.succ.inj lengths)
        fun p inside => pairs p (List.mem_cons_of_mem _ inside)
      rw [List.map_cons, head, tail]

end Lists

/-! ## The image of members in the base layer -/

section Image

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S) {O : Type uO} [DecidableEq O]
  {P : Program (Terms T)}

/-- **The firing of the base layer that a member stands for**: its rule opened along its opening, its
collect patterns as exact region queries of their seen sets, and its selection. -/
noncomputable abbrev baseFiring (m : OneMember A O P) : AnnotatedRuns.Firing T S O :=
  toFirstOrder A P m.firing

/-- **The image of a list of members in the base layer**, member by member. -/
noncomputable abbrev image (l : List (OneMember A O P)) : List (AnnotatedRuns.Firing T S O) :=
  l.map (baseFiring A)

/-- **A member keeps the labels** of the base layer: its made identities already carry its opened made
rows. -/
def KeepsLabels (label : O → T) (m : OneMember A O P) : Prop :=
  m.selection.made.map label = (m.firing.opened (frames A)).produce

/-- **Two firings of the base layer ignore each other's writes**: at the cut of the pair, the checks and
the predicate queries of each are unchanged by what the other takes and makes. This is
`AnnotatedRuns.Compatible` without its condition on the selections. -/
def IgnoreEachOther (label : O → T) (C : Configuration T O) (f g : AnnotatedRuns.Firing T S O) :
    Prop :=
  (∀ check ∈ f.rule.checks,
      Check.IgnoresWrites A (AnnotatedRuns.pairCut label C f g) label g.selection check) ∧
    (∀ check ∈ g.rule.checks,
      Check.IgnoresWrites A (AnnotatedRuns.pairCut label C f g) label f.selection check) ∧
    (∀ query ∈ f.queries, query.IgnoresWrites A (AnnotatedRuns.pairCut label C f g) label g.selection) ∧
    (∀ query ∈ g.queries, query.IgnoresWrites A (AnnotatedRuns.pairCut label C f g) label f.selection)

/-- **Compatibility is independent selections and ignored writes.** -/
theorem compatible_iff (label : O → T) (C : Configuration T O) (f g : AnnotatedRuns.Firing T S O) :
    AnnotatedRuns.Compatible A label C f g ↔
      Independent label (f.selection.commit (T := T)) (g.selection.commit (T := T)) ∧
        IgnoreEachOther A label C f g := Iff.rfl

omit [DecidableEq O] in
/-- **Positive members ignore each other's writes**: their checks are equations and they have no
collect query. -/
theorem ignoreEachOther_of_positive (label : O → T) (C : Configuration T O) {m m' : OneMember A O P}
    (positive : Positive m.rule) (positive' : Positive m'.rule) :
    IgnoreEachOther A label C (baseFiring A m) (baseFiring A m') := by
  have checks : ∀ n : OneMember A O P, Positive n.rule → ∀ (D : EquationStore T) (writer : Selection O),
      ∀ check ∈ (baseFiring A n).rule.checks, Check.IgnoresWrites A D label writer check := by
    intro n positiveN _ _ check inside
    obtain ⟨_, _, _, _, -, rfl⟩ := Scope.opened_check_equal A positiveN inside
    trivial
  have queries : ∀ n : OneMember A O P, Positive n.rule → (baseFiring A n).queries = [] := by
    intro n positiveN
    simp [OneFrame.toFirstOrder, Firing.collectOpened, positiveN.2]
  refine ⟨checks m positive _ _, checks m' positive' _ _, fun query inside => ?_, fun query inside => ?_⟩
  · rw [queries m positive] at inside
    cases inside
  · rw [queries m' positive'] at inside
    cases inside

omit [DecidableEq O] in
/-- The own equations of a member at an embedded state are the equations its base firing adds. -/
theorem own_embed (label : O → T) (C : Configuration T O) (m : OneMember A O P) :
    JointFirings.Member.own (frames A) (embed label C) m =
      GuardFreeProcessOrders.added label (m.firing.opened (frames A)) m.selection := by
  unfold JointFirings.Member.own Firing.matching GuardFreeProcessOrders.added Selection.equations
  rw [OneFrame.row_eq C m.firing]

omit [DecidableEq O] in
/-- **The joint information of a bag at an embedded state is the joint problem of its image.** -/
theorem information_embed (label : O → T) (C : Configuration T O) (l : List (OneMember A O P)) :
    JointFirings.Bag.information (frames A) (embed label C) (bagOf A l) =
      AnnotatedRuns.jointProblem label C (image A l) := by
  have known : (frames A).applyStore ((frames A).id PUnit.unit) C.equations = C.equations :=
    Frames.applyStore_id (X := frames A) C.equations
  have owns : l.flatMap (fun m => JointFirings.Member.own (frames A) (embed label C) m) =
      l.flatMap (fun m => (baseFiring A m).added label) :=
    List.flatMap_congr fun m _ => own_embed A label C m
  show (frames A).applyStore ((frames A).id PUnit.unit) C.equations ++
      l.flatMap (fun m => JointFirings.Member.own (frames A) (embed label C) m) =
    C.equations ++ (l.map (baseFiring A)).flatMap (AnnotatedRuns.Firing.added label)
  rw [known, owns, List.flatMap_map]

omit [DecidableEq O] in
/-- **Joint solvability is joint consistency of the image.** -/
theorem solvable_iff_joint (label : O → T) (C : Configuration T O) (l : List (OneMember A O P)) :
    (frames A).Solvable (JointFirings.Bag.information (frames A) (embed label C) (bagOf A l)) ↔
      A.Consistent (AnnotatedRuns.jointProblem label C (image A l)) := by
  rw [information_embed A label C l]
  exact Frames.ofSubstitution_solvable_iff A _

/-- **The selections of a bag enabled as one commit, with distinct takes and made identities, are
pairwise independent.** -/
theorem independent_of_enabled (label : O → T) {s : State (Terms T) O} {l : List (OneMember A O P)}
    (taken : (bagOf A l).selection.taken.Nodup) (made : (bagOf A l).selection.made.Nodup)
    (enabled : Enabled (fun _ : O => ()) s.present ((bagOf A l).selection.commit (T := Unit))) :
    l.Pairwise fun m m' =>
      Independent label (m.selection.commit (T := T)) (m'.selection.commit (T := T)) := by
  have spoils : ∀ m ∈ l, ∀ m' ∈ l,
      Disjoint (m.selection.commit (T := T)).taken (m'.selection.commit (T := T)).kept := by
    intro m inM m' inM'
    refine Finset.disjoint_left.mpr fun o isTaken isKept => ?_
    have inTaken : o ∈ ((bagOf A l).selection.commit (T := Unit)).taken :=
      List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨m, inM, List.mem_toFinset.mp isTaken⟩)
    have inKept : o ∈ ((bagOf A l).selection.commit (T := Unit)).kept :=
      List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨m', inM', List.mem_toFinset.mp isKept⟩)
    exact Finset.disjoint_left.mp enabled.apart inTaken inKept
  refine ((List.nodup_flatMap.mp taken).2.and (List.nodup_flatMap.mp made).2).imp_of_mem
    @fun m m' inM inM' apart => ⟨?_, ?_, ?_⟩
  · rintro (overlap | overlap)
    · exact overlap (List.disjoint_toFinset_iff_disjoint.mpr apart.1)
    · exact overlap (List.disjoint_toFinset_iff_disjoint.mpr apart.2)
  · rintro (overlap | ⟨_, inQ, -⟩)
    · exact overlap (spoils m inM m' inM')
    · simp [Selection.commit] at inQ
  · rintro (overlap | ⟨_, inQ, -⟩)
    · exact overlap (spoils m' inM' m inM)
    · simp [Selection.commit] at inQ

/-- **A member of a bag admitted on its own, keeping labels, is valid in the base layer.** -/
theorem valid_of_member {label : O → T} {C : Configuration T O} {l : List (OneMember A O P)}
    (own : JointFirings.Bag.AdmitsOwn (frames A) (embed label C) (bagOf A l))
    {m : OneMember A O P} (inside : m ∈ l) (keeps : KeepsLabels A label m) :
    (baseFiring A m).Valid A label C :=
  ((OneFrame.admits_toFirstOrder_iff (A := A) (label := label) (P := P) C m.firing).mp
    ⟨JointFirings.Bag.admits_member (frames A) (fun _ _ => ⟨A.identity⟩) own inside, keeps⟩).1

/-! ## The image of a bag admitted on its own is a round -/

/-- **The image of a bag admitted on its own, keeping labels, is a round exactly when its members
ignore each other's writes.** No hypothesis on the rules or on the terms of the state. -/
theorem round_image_iff {label : O → T} {C : Configuration T O} {l : List (OneMember A O P)}
    (own : JointFirings.Bag.AdmitsOwn (frames A) (embed label C) (bagOf A l))
    (keeps : ∀ m ∈ l, KeepsLabels A label m) :
    AnnotatedRuns.Round A label C (image A l) ↔ (image A l).Pairwise (IgnoreEachOther A label C) := by
  constructor
  · intro round
    exact round.compatible.imp fun compatible => compatible.2
  · intro ignore
    have independent : (image A l).Pairwise fun f g =>
        Independent label (f.selection.commit (T := T)) (g.selection.commit (T := T)) :=
      List.pairwise_map.mpr (independent_of_enabled A label own.1.2.1 own.1.2.2.1 own.2.1)
    refine ⟨fun f inside => ?_, (solvable_iff_joint A label C l).mp own.2.2.1,
      (independent.and ignore).imp fun both => both⟩
    obtain ⟨m, inM, rfl⟩ := List.mem_map.mp inside
    exact valid_of_member A own inM (keeps m inM)

/-- **For positive rules, the image of a bag admitted on its own, keeping labels, is a round.** -/
theorem round_image_of_positive {label : O → T} {C : Configuration T O} {l : List (OneMember A O P)}
    (own : JointFirings.Bag.AdmitsOwn (frames A) (embed label C) (bagOf A l))
    (keeps : ∀ m ∈ l, KeepsLabels A label m) (positive : ∀ m ∈ l, Positive m.rule) :
    AnnotatedRuns.Round A label C (image A l) :=
  (round_image_iff A own keeps).mpr (List.pairwise_map.mpr (List.pairwise_of_forall_mem_list
    fun m inM m' inM' => ignoreEachOther_of_positive A label C (positive m inM) (positive m' inM')))

/-! ## A round of images is a bag admitted on its own -/

/-- **A round whose members are the images of members with jointly fresh openings, and one seen set per
collect pattern, is the image of a bag admitted on its own; its members keep labels.** Every rule; no
hypothesis on the terms of the state. -/
theorem admitsOwn_of_round {label : O → T} {C : Configuration T O} {l : List (OneMember A O P)}
    (round : AnnotatedRuns.Round A label C (image A l))
    (fresh : JointFirings.Bag.Fresh (frames A) (embed label C) (bagOf A l))
    (collect : ∀ m ∈ l, m.rule.collect.length = m.seen.length) :
    JointFirings.Bag.AdmitsOwn (frames A) (embed label C) (bagOf A l) ∧
      ∀ m ∈ l, KeepsLabels A label m := by
  have member : ∀ m ∈ l, m.firing.Admits (frames A) (embed label C) ∧ KeepsLabels A label m :=
    fun m inside => (OneFrame.admits_toFirstOrder_iff (A := A) (label := label) (P := P) C m.firing).mpr
      ⟨round.valid _ (List.mem_map_of_mem inside),
        JointFirings.Bag.fresh_member (frames A) (fun _ _ => ⟨A.identity⟩) fresh inside, collect m inside⟩
  have pairs : l.Pairwise fun m m' =>
      AnnotatedRuns.Compatible A label C (baseFiring A m) (baseFiring A m') :=
    List.pairwise_map.mp round.compatible
  have each : ∀ m ∈ l, Enabled (fun _ : O => ()) C.present (m.selection.commit (T := Unit)) :=
    fun m inside => (member m inside).1.2.1
  refine ⟨⟨⟨fresh, ?_, ?_, fun m inside => (member m inside).1.1.2.2.2⟩, ?_,
    (solvable_iff_joint A label C l).mpr round.joint, fun m inside => (member m inside).1.2.2.2⟩,
    fun m inside => (member m inside).2⟩
  · refine List.nodup_flatMap.mpr ⟨fun m inside => (member m inside).1.1.2.1,
      pairs.imp fun compatible => ?_⟩
    exact List.disjoint_toFinset_iff_disjoint.mp
      (Classical.byContradiction fun overlap => compatible.1.1 (Or.inl overlap))
  · refine List.nodup_flatMap.mpr ⟨fun m inside => (member m inside).1.1.2.2.1,
      pairs.imp fun compatible => ?_⟩
    exact List.disjoint_toFinset_iff_disjoint.mp
      (Classical.byContradiction fun overlap => compatible.1.1 (Or.inr overlap))
  · refine ⟨fun o inside => ?_, fun o inside => ?_, ?_, ?_, fun _ inside => by
      simp [Selection.commit] at inside⟩
    · obtain ⟨m, inM, taken⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp inside)
      exact (each m inM).taken_subset (List.mem_toFinset.mpr taken)
    · obtain ⟨m, inM, read⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp inside)
      exact (each m inM).kept_subset (List.mem_toFinset.mpr read)
    · refine List.disjoint_toFinset_iff_disjoint.mpr
        (disjoint_flatMap (fun m : OneMember A O P => m.selection.taken)
          (fun m : OneMember A O P => m.selection.read) l
          (fun m inM => List.disjoint_toFinset_iff_disjoint.mp (each m inM).apart)
          (pairs.imp fun compatible => ⟨?_, ?_⟩))
      · exact List.disjoint_toFinset_iff_disjoint.mp
          (Classical.byContradiction fun overlap => compatible.1.2.1 (Or.inl overlap))
      · exact List.disjoint_toFinset_iff_disjoint.mp
          (Classical.byContradiction fun overlap => compatible.1.2.2 (Or.inl overlap))
    · refine Finset.disjoint_left.mpr fun o isMade present => ?_
      obtain ⟨m, inM, made⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp isMade)
      exact Finset.disjoint_left.mp (each m inM).fresh (List.mem_toFinset.mpr made) present

/-- **For positive rules, the two presentations define one round**: a bag admitted on its own whose
members keep labels, and a round of images with jointly fresh openings and one seen set per collect query
pattern. -/
theorem admitsOwn_iff_round {label : O → T} {C : Configuration T O} {l : List (OneMember A O P)}
    (positive : ∀ m ∈ l, Positive m.rule) :
    (JointFirings.Bag.AdmitsOwn (frames A) (embed label C) (bagOf A l) ∧
        ∀ m ∈ l, KeepsLabels A label m) ↔
      AnnotatedRuns.Round A label C (image A l) ∧
        JointFirings.Bag.Fresh (frames A) (embed label C) (bagOf A l) ∧
        ∀ m ∈ l, m.rule.collect.length = m.seen.length := by
  constructor
  · rintro ⟨own, keeps⟩
    exact ⟨round_image_of_positive A own keeps positive, own.1.1,
      fun m inside => (own.1.2.2.2 m inside).2.2.2⟩
  · rintro ⟨round, fresh, collect⟩
    exact admitsOwn_of_round A round fresh collect

/-- **At a state that mentions only fixed terms, the image of a bag of positive rules admitted with the
guards at the joint information, keeping labels, is a round.** -/
theorem round_image_of_admits_fixed {label : O → T} {C : Configuration T O}
    {l : List (OneMember A O P)} (fixed : ∀ t, (embed label C).Mentions t → ∀ σ : S, A.E (A.apply σ t) t)
    (positive : ∀ m ∈ l, Positive m.rule) (keeps : ∀ m ∈ l, KeepsLabels A label m)
    (admitted : JointFirings.Bag.Admits (frames A) (embed label C) (bagOf A l)) :
    AnnotatedRuns.Round A label C (image A l) :=
  round_image_of_positive A (JointFirings.admitsOwn_of_fixed A fixed positive admitted) keeps positive

/-! ## Every state at the one frame: the labels of a round -/

/-- The configuration of a state at the one frame: its knowledge and its present rows. -/
def configurationOf (s : State (Terms T) O) : Configuration T O := ⟨s.knowledge, s.present⟩

/-- **The labels of a round**: the labels the bag's result carries. The state's labels, with each made
identity labelled by its opened made row. -/
def roundLabel (s : State (Terms T) O) (l : List (OneMember A O P)) : O → T :=
  (JointFirings.Bag.result (frames A) s (bagOf A l)).label

/-- **The labels of a round agree with the state's on its present rows.** -/
theorem roundLabel_present {s : State (Terms T) O} {l : List (OneMember A O P)}
    (enabled : Enabled (fun _ : O => ()) s.present ((bagOf A l).selection.commit (T := Unit)))
    {o : O} (present : o ∈ s.present) : roundLabel A s l o = s.label o := by
  have missing : o ∉ (bagOf A l).selection.made := fun made =>
    Finset.disjoint_left.mp enabled.fresh (List.mem_toFinset.mpr made) present
  have step : roundLabel A s l o = A.apply A.identity (s.label o) :=
    Firing.relabel_of_not_mem (Tm := Terms T) (a := PUnit.unit)
      (fun o' => A.apply A.identity (s.label o')) _ _ missing
  rw [step, A.apply_identity]

/-- **Under the labels of a round, every member keeps labels.** -/
theorem keepsLabels_roundLabel {s : State (Terms T) O} {l : List (OneMember A O P)}
    (fits : JointFirings.Bag.Fits (frames A) s (bagOf A l)) {m : OneMember A O P} (inM : m ∈ l) :
    KeepsLabels A (roundLabel A s l) m := by
  have pieces : ∀ n ∈ l,
      n.selection.made.length = (JointFirings.Member.produced (frames A) n).length := by
    intro n inN
    show n.selection.made.length = (n.rule.body.produce.map ((frames A).act n.opening)).length
    rw [List.length_map]
    exact (fits.2.2.2 n inN).2.2.1.symm
  have total : (l.flatMap fun n => n.selection.made).length =
      (l.flatMap (JointFirings.Member.produced (frames A))).length := by
    rw [List.length_flatMap, List.length_flatMap]
    exact congrArg List.sum (List.map_congr_left pieces)
  have zipped := JointFirings.zip_flatMap (fun n : OneMember A O P => n.selection.made)
    (JointFirings.Member.produced (frames A)) l pieces
  refine map_eq_of_zip _ _ _ (pieces m inM) fun p inside => ?_
  have joint : p ∈ (l.flatMap fun n => n.selection.made).zip
      (l.flatMap (JointFirings.Member.produced (frames A))) := by
    rw [zipped]
    exact List.mem_flatMap.mpr ⟨m, inM, inside⟩
  exact Firing.relabel_zip _ _ _ fits.2.2.1 total p joint

omit [DecidableEq O] in
/-- **A state relabelled where it has no present rows is structurally congruent to it.** -/
theorem congruent_relabel {s : State (Terms T) O} {label : O → T}
    (agree : ∀ o ∈ s.present, label o = s.label o) :
    Congruent s (embed label (configurationOf s)) :=
  ⟨fun _ => Iff.rfl, rfl, fun o present => (agree o present).symm⟩

/-- **Structurally congruent states admit the same bags on their own**: the bag form of
`Scope.admits_of_congruent`. -/
theorem admitsOwn_of_congruent {s s' : State (Terms T) O} (same : Congruent s s')
    {l : List (OneMember A O P)} (own : JointFirings.Bag.AdmitsOwn (frames A) s (bagOf A l)) :
    JointFirings.Bag.AdmitsOwn (frames A) s' (bagOf A l) := by
  obtain ⟨⟨fresh, taken, made, lengths⟩, enabled, ⟨_, σ, solved⟩, asks⟩ := own
  have information : ∀ m ∈ l, ∀ e,
      e ∈ m.firing.information (frames A) s ↔ e ∈ m.firing.information (frames A) s' :=
    fun m inside e => Scope.information_congruent (f := m.firing) same
      (JointFirings.Bag.enabled_member enabled inside) e
  refine ⟨⟨fun b g => JointFirings.Realized.mono (frames A) l
      (fun _ holds v mentioned => holds v ((Scope.mentions_congruent same v).mpr mentioned))
      (fresh b g), taken, made, lengths⟩, same.present ▸ enabled,
    ⟨PUnit.unit, σ, fun e inside => solved e ?_⟩, fun m inside b ρ solvedM => ?_⟩
  · rcases List.mem_append.mp inside with known | owned
    · obtain ⟨e₀, inK, rfl⟩ := List.mem_map.mp known
      exact List.mem_append_left _ (List.mem_map.mpr ⟨e₀, (same.knowledge e₀).mpr inK, rfl⟩)
    · obtain ⟨m, inM, ownM⟩ := List.mem_flatMap.mp owned
      have inInformation : e ∈ m.firing.information (frames A) s' := by
        rw [JointFirings.Member.information_eq]
        exact List.mem_append_right _ ownM
      have back := (information m inM e).mpr inInformation
      rw [JointFirings.Member.information_eq] at back
      rcases List.mem_append.mp back with knownS | ownS
      · exact List.mem_append_left _ knownS
      · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨m, inM, ownS⟩)
  · have solvedS : (frames A).Models ρ (m.firing.information (frames A) s) :=
      fun e member => solvedM e ((information m inside e).mp member)
    exact (Scope.holds_congruent same m.firing ρ).mp (asks m inside b ρ solvedS)

/-- **At every state at the one frame, the image of a bag admitted on its own, under the labels of its
round, is a round exactly when its members ignore each other's writes.** Every rule. -/
theorem round_image_canonical_iff {s : State (Terms T) O} {l : List (OneMember A O P)}
    (own : JointFirings.Bag.AdmitsOwn (frames A) s (bagOf A l)) :
    AnnotatedRuns.Round A (roundLabel A s l) (configurationOf s) (image A l) ↔
      (image A l).Pairwise (IgnoreEachOther A (roundLabel A s l) (configurationOf s)) :=
  round_image_iff A
    (admitsOwn_of_congruent A
      (congruent_relabel fun _ present => roundLabel_present A own.2.1 present) own)
    (fun _ inM => keepsLabels_roundLabel A own.1 inM)

/-- **The image of every bag of positive rules admitted on its own, at every state at the one frame,
is a round of the base layer**, under the labels of its round, at the state's configuration. -/
theorem round_image_canonical {s : State (Terms T) O} {l : List (OneMember A O P)}
    (own : JointFirings.Bag.AdmitsOwn (frames A) s (bagOf A l)) (positive : ∀ m ∈ l, Positive m.rule) :
    AnnotatedRuns.Round A (roundLabel A s l) (configurationOf s) (image A l) :=
  round_image_of_positive A
    (admitsOwn_of_congruent A
      (congruent_relabel fun _ present => roundLabel_present A own.2.1 present) own)
    (fun _ inM => keepsLabels_roundLabel A own.1 inM) positive

/-- **For positive rules, at every state at the one frame, the two presentations define one round**: a
bag admitted on its own, and a round of the base layer of its image under the labels of its round, with
jointly fresh openings and one seen set per collect pattern. -/
theorem admitsOwn_iff_round_canonical {s : State (Terms T) O} {l : List (OneMember A O P)}
    (positive : ∀ m ∈ l, Positive m.rule) :
    JointFirings.Bag.AdmitsOwn (frames A) s (bagOf A l) ↔
      AnnotatedRuns.Round A (roundLabel A s l) (configurationOf s) (image A l) ∧
        JointFirings.Bag.Fresh (frames A) s (bagOf A l) ∧
        ∀ m ∈ l, m.rule.collect.length = m.seen.length := by
  constructor
  · intro own
    exact ⟨round_image_canonical A own positive, own.1.1, fun m inside => (own.1.2.2.2 m inside).2.2.2⟩
  · rintro ⟨round, fresh, collect⟩
    have agree : ∀ o ∈ s.present, roundLabel A s l o = s.label o := by
      intro o present
      have missing : o ∉ (bagOf A l).selection.made := by
        intro made
        obtain ⟨m, inM, isMade⟩ := List.mem_flatMap.mp made
        exact Finset.disjoint_left.mp (round.valid _ (List.mem_map_of_mem inM)).firing.occurrences.fresh
          (List.mem_toFinset.mpr isMade) present
      have step : roundLabel A s l o = A.apply A.identity (s.label o) :=
        Firing.relabel_of_not_mem (Tm := Terms T) (a := PUnit.unit)
          (fun o' => A.apply A.identity (s.label o')) _ _ missing
      rw [step, A.apply_identity]
    have same := congruent_relabel agree
    have freshEmbed :
        JointFirings.Bag.Fresh (frames A) (embed (roundLabel A s l) (configurationOf s)) (bagOf A l) :=
      fun b g => JointFirings.Realized.mono (frames A) l
        (fun _ holds v mentioned => holds v ((Scope.mentions_congruent same v).mpr mentioned)) (fresh b g)
    exact admitsOwn_of_congruent A same.symm (admitsOwn_of_round A round freshEmbed collect).1

/-! ## What carries over from the base layer's trace theory -/

/-- **The images of any two orders of the members of a round are one contextual trace.** -/
theorem orders_equivalent {label : O → T} {C : Configuration T O} {l l₁ l₂ : List (OneMember A O P)}
    (round : AnnotatedRuns.Round A label C (image A l)) (first : l₁.Perm l) (second : l₂.Perm l) :
    AnnotatedRuns.RoundEquiv A label C (image A l₁) (image A l₂) :=
  .trans _ _ _ (round.orders_equivalent A label (first.map (baseFiring A)))
    (.symm _ _ (round.orders_equivalent A label (second.map (baseFiring A))))

/-- **Every order of the members of a round runs in the base layer, to one class.** -/
theorem orders_run {label : O → T} {C : Configuration T O} {l l₁ : List (OneMember A O P)}
    (round : AnnotatedRuns.Round A label C (image A l)) (perm : l₁.Perm l) :
    AnnotatedRuns.Executable A label C (image A l₁) ∧
      GuardFreeProcessOrders.SameUpTo A (AnnotatedRuns.follow label C (image A l₁))
        (AnnotatedRuns.follow label C (image A l)) :=
  ⟨round.executable_perm A label (perm.map (baseFiring A)),
    round.follow_perm A label (perm.map (baseFiring A))⟩

/-- **The base runs of any two orders of the members of a round are one trace of the first-order step's
transport.** -/
theorem native_traces {label : O → T} {C : Configuration T O} {l l₁ l₂ : List (OneMember A O P)}
    (round : AnnotatedRuns.Round A label C (image A l)) (first : l₁.Perm l) (second : l₂.Perm l) :
    (AnnotatedRuns.firstOrderTransport A label).TraceEquiv C
      (Interface.FirstOrderNativeRuns.ofExecutable A label C (image A l₁)
        (round.executable_perm A label (first.map (baseFiring A))))
      (Interface.FirstOrderNativeRuns.ofExecutable A label C (image A l₂)
        (round.executable_perm A label (second.map (baseFiring A)))) := by
  apply Interface.FirstOrderNativeRuns.native_trace_of_rounds
  rw [Interface.FirstOrderNativeRuns.sites_ofExecutable,
    Interface.FirstOrderNativeRuns.sites_ofExecutable]
  exact orders_equivalent A round first second

/-- **For every bag of positive rules admitted on its own, at every state at the one frame, the images
of any two orders are one contextual trace**, under the labels of its round. -/
theorem orders_equivalent_of_admitsOwn {s : State (Terms T) O} {l l₁ l₂ : List (OneMember A O P)}
    (own : JointFirings.Bag.AdmitsOwn (frames A) s (bagOf A l)) (positive : ∀ m ∈ l, Positive m.rule)
    (first : l₁.Perm l) (second : l₂.Perm l) :
    AnnotatedRuns.RoundEquiv A (roundLabel A s l) (configurationOf s) (image A l₁) (image A l₂) :=
  orders_equivalent A (round_image_canonical A own positive) first second

/-- **For every bag of positive rules admitted on its own, at every state at the one frame, the base
runs of any two orders are one trace of the first-order step's transport**, under the labels of its
round. -/
theorem native_traces_of_admitsOwn {s : State (Terms T) O} {l l₁ l₂ : List (OneMember A O P)}
    (own : JointFirings.Bag.AdmitsOwn (frames A) s (bagOf A l)) (positive : ∀ m ∈ l, Positive m.rule)
    (first : l₁.Perm l) (second : l₂.Perm l) :
    (AnnotatedRuns.firstOrderTransport A (roundLabel A s l)).TraceEquiv (configurationOf s)
      (Interface.FirstOrderNativeRuns.ofExecutable A (roundLabel A s l) (configurationOf s) (image A l₁)
        ((round_image_canonical A own positive).executable_perm A _ (first.map (baseFiring A))))
      (Interface.FirstOrderNativeRuns.ofExecutable A (roundLabel A s l) (configurationOf s) (image A l₂)
        ((round_image_canonical A own positive).executable_perm A _ (second.map (baseFiring A)))) :=
  native_traces A (round_image_canonical A own positive) first second

end Image

#print axioms disjoint_flatMap
#print axioms map_eq_of_zip
#print axioms compatible_iff
#print axioms ignoreEachOther_of_positive
#print axioms own_embed
#print axioms information_embed
#print axioms solvable_iff_joint
#print axioms independent_of_enabled
#print axioms valid_of_member
#print axioms round_image_iff
#print axioms round_image_of_positive
#print axioms admitsOwn_of_round
#print axioms admitsOwn_iff_round
#print axioms round_image_of_admits_fixed
#print axioms roundLabel_present
#print axioms keepsLabels_roundLabel
#print axioms congruent_relabel
#print axioms admitsOwn_of_congruent
#print axioms round_image_canonical_iff
#print axioms round_image_canonical
#print axioms admitsOwn_iff_round_canonical
#print axioms orders_equivalent
#print axioms orders_run
#print axioms native_traces
#print axioms orders_equivalent_of_admitsOwn
#print axioms native_traces_of_admitsOwn

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Rounds
