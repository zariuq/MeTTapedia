import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.RoundEveryOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.RoundPetriSteps
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Runs

/-!
# Where the two presentations of a round part, and where they do not

Controls for `RoundTwoPresentations` and `RoundEveryOrder`. Each breaks one hypothesis, or keeps all but
one, at the one-frame action on first-order terms over numerals (`RuleSyntax.Controls.action`).

* **Positivity** (`none_separates`): two members whose none checks ask that the row the other makes
  not be present. The bag is admitted on its own; under the labels of its round its image is not a round of the
  base layer; and it is no runtime round, since no run of the one-match step reaches its result.
* **Positivity is not necessary** (`ninePair_round`): two members whose none checks read a pattern apart
  from every row the other makes. The rules are not positive, and the image is a round: the hypothesis of
  `round_image_iff` is the write-ignorance, not positivity.
* **Joint freshness** (`twins_round`, `twins_not_image`): at a state that mentions only fixed terms, two
  copies of one read whose openings share the unknown `x₁` are each admitted, and their images form a round
  of the base layer; and no list of members with these images is admitted on its own. The base layer has
  no freshness to read back.
* **Fixed terms are not needed for rounds** (`unknown_round`): at a state whose row is an unknown, a bag of
  positive rules admitted on its own has a round of the base layer as its image.
* **Fixed terms are needed for the guards at the joint information** (`jointGuards_need_fixed`): at a
  state whose rows are unknowns, the bag of `JointFirings.Knowledge`, of positive rules, is admitted with
  the guards at the joint information, and its image is not a round.
* **Labels** (`labels_of_round`): under the state's own labels the image of a bag admitted on its own is
  not a round, since the state labels the identities the bag makes otherwise than the bag does; under the
  labels of its round it is.
* **A multi-firing step from a bag** (`spends_step`): the same two spends, whose images are statically
  independent (`spends_static`), are one multi-firing step of the base layer (`RoundPetriSteps`).
* **The runtime's round is coarser than the base layer's round for rules with counts**
  (`refresh_separates`): a refresh of a `1` and a count of the `1`s run in either order to one state and
  form a runtime round, and the count does not ignore the refresh's writes, so the image is not a round.
  So for rules that are not positive three notions part: at an embedded state, a round of jointly fresh
  images is a runtime round (`runtimeRound_of_round`), and a runtime round is a bag admitted on its own
  (`admitsOwn_of_runtimeRound`); this control and `none_separates` show both inclusions strict.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Rounds.Controls

open _root_.Mettapedia.Logic.LP
open _root_.Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.OneFrame
  (Terms frames ext embed)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope (Positive)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples
  (Tm X E c x)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-! ## Positivity: none checks where the two presentations part -/

/-- The two members of the synchronous bag: make a `1` unless a `2` is present, make a `2` unless a `1`
is present. -/
abbrev unlessPair : List (OneMember action ℕ Synchronous.program) :=
  [Synchronous.makeOne, Synchronous.makeTwo]

/-- **Without positivity a bag admitted on its own need not be a round.** The bag is admitted on its own at
the empty state; under the labels of its round its image is not a round of the base layer; and it is no
runtime round. -/
theorem none_separates :
    Bag.AdmitsOwn X Synchronous.empty (bagOf action unlessPair) ∧
      ¬ AnnotatedRuns.Round action (roundLabel action Synchronous.empty unlessPair)
          (configurationOf Synchronous.empty) (image action unlessPair) ∧
      ¬ RuntimeRound action Synchronous.empty unlessPair := by
  refine ⟨Synchronous.both_admitted, fun round => ?_, fun runtime => ?_⟩
  · have compatible := List.pairwise_pair.mp round.compatible
    have ignored := compatible.2.1 (Check.predicate .none (c 2)) (List.mem_singleton_self _) 11
      (List.mem_append_right _ (List.mem_singleton_self 11))
    refine ignored ⟨Subst.id atoms, fun e member => ?_⟩
    have store : AnnotatedRuns.pairCut (roundLabel action Synchronous.empty unlessPair)
        (configurationOf Synchronous.empty) (baseFiring action Synchronous.makeOne)
        (baseFiring action Synchronous.makeTwo) ++
        [(c 2, roundLabel action Synchronous.empty unlessPair 11)] = [(c 2, c 2)] := rfl
    rw [store] at member
    obtain rfl := List.mem_singleton.mp member
    rfl
  · have fires := (runtime.2 unlessPair (List.Perm.refl _)).1
    have run := run_of_firesInOrder action Synchronous.empty unlessPair fires
    rw [stateAfter_eq_result action Synchronous.empty unlessPair Synchronous.both_admitted.1
      Synchronous.both_admitted.2.1] at run
    exact Synchronous.no_run_reaches run

/-! ## Positivity is not necessary: none checks apart from what the others make -/

/-- **The program**: make a `1` unless a `9` is present; make a `2` unless a `9` is present. -/
def unlessNine : Program Tm := {Synchronous.addUnless 1 9, Synchronous.addUnless 2 9}

/-- Make a `1` as identity `10`, unless a `9` is present. -/
def oneUnlessNine : OneMember action ℕ unlessNine :=
  ⟨Synchronous.addUnless 1 9, Or.inl rfl, Subst.id atoms, ⟨[], [], [10]⟩, []⟩

/-- Make a `2` as identity `11`, unless a `9` is present. -/
def twoUnlessNine : OneMember action ℕ unlessNine :=
  ⟨Synchronous.addUnless 2 9, Or.inr rfl, Subst.id atoms, ⟨[], [], [11]⟩, []⟩

/-- The two. -/
abbrev ninePair : List (OneMember action ℕ unlessNine) := [oneUnlessNine, twoUnlessNine]

theorem ninePair_members {m : OneMember action ℕ unlessNine} (inside : m ∈ ninePair) :
    m = oneUnlessNine ∨ m = twoUnlessNine := by
  rcases List.mem_cons.mp inside with first | rest
  · exact Or.inl first
  · exact Or.inr (List.mem_singleton.mp rest)

/-- **The bag of the two is admitted on its own at the empty state.** -/
theorem ninePair_admitted : Bag.AdmitsOwn X Synchronous.empty (bagOf action ninePair) := by
  refine ⟨⟨fresh_of_ground_bag action Synchronous.empty _ fun m inside => ?_, by decide, by decide,
      fun m inside => ?_⟩, ⟨by decide, by decide, by decide, by decide,
        fun q member => by simp [Selection.commit] at member⟩,
      ⟨PUnit.unit, Subst.id atoms, fun e inside => ?_⟩, fun m inside b σ _ => ⟨fun check member => ?_,
        fun q member => ?_⟩⟩
  · rcases ninePair_members inside with rfl | rfl
    · exact Synchronous.addUnless_ground 1 9
    · exact Synchronous.addUnless_ground 2 9
  · rcases ninePair_members inside with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · have none : Bag.information X Synchronous.empty (bagOf action ninePair) = [] := rfl
    rw [none] at inside
    exact absurd inside List.not_mem_nil
  · rcases ninePair_members inside with rfl | rfl <;>
    · rw [List.mem_singleton.mp member]
      intro o present
      exact absurd present (Finset.notMem_empty o)
  · rcases ninePair_members inside with rfl | rfl <;> exact absurd member List.not_mem_nil

/-- **The rules are not positive, and the image of the bag, under the labels of its round, is a round of
the base layer**: each none check reads `9`, apart from the row the other member makes. -/
theorem ninePair_round :
    ¬ (∀ m ∈ ninePair, Positive m.rule) ∧
      AnnotatedRuns.Round action (roundLabel action Synchronous.empty ninePair)
        (configurationOf Synchronous.empty) (image action ninePair) := by
  refine ⟨fun positive => ?_, (round_image_canonical_iff action ninePair_admitted).mpr
    (List.pairwise_pair.mpr ⟨?_, ?_, ?_, ?_⟩)⟩
  · obtain ⟨_, _, equal⟩ := (positive oneUnlessNine List.mem_cons_self).1 (Check.predicate .none (c 9))
      List.mem_cons_self
    cases equal
  · intro check member
    rw [List.mem_singleton.mp member]
    intro o written consistent
    have eleven : o ∈ ([] ++ [11] : List ℕ) := written
    obtain rfl : o = 11 := by simpa using eleven
    obtain ⟨σ, solved⟩ := consistent
    have same : (c 9 : Term atoms) = c 2 :=
      solved _ (List.mem_append_right _ (List.mem_singleton_self _))
    exact absurd (Term.const.inj same) (by decide)
  · intro check member
    rw [List.mem_singleton.mp member]
    intro o written consistent
    have ten : o ∈ ([] ++ [10] : List ℕ) := written
    obtain rfl : o = 10 := by simpa using ten
    obtain ⟨σ, solved⟩ := consistent
    have same : (c 9 : Term atoms) = c 1 :=
      solved _ (List.mem_append_right _ (List.mem_singleton_self _))
    exact absurd (Term.const.inj same) (by decide)
  · intro query member
    exact absurd member List.not_mem_nil
  · intro query member
    exact absurd member List.not_mem_nil

/-! ## Joint freshness: a round of images that is the image of no bag admitted on its own -/

/-- Read any row. -/
def readAny : Rule Tm := ⟨PUnit.unit, ⟨[], [x], [], [], []⟩, []⟩

/-- **The program**: read any row. -/
def readers : Program Tm := {readAny}

/-- Read the row `0`, the rule's unknown opened as `x₁`. -/
def twin : OneMember action ℕ readers := ⟨readAny, rfl, Examples.shift, ⟨[], [0], []⟩, []⟩

/-- Every row is the constant `1`. -/
abbrev onesLabel : ℕ → Term atoms := fun _ => c 1

/-- **The state of one token mentions only fixed terms.** -/
theorem tokenState_fixed : FixedState action Examples.tokenState := by
  rintro t (known | known | ⟨o, -, rfl⟩) σ
  · simp [Examples.tokenState] at known
  · simp [Examples.tokenState] at known
  · rfl

/-- The twin's opening is fresh at the state of one token. -/
theorem twin_fresh : twin.firing.Fresh X Examples.tokenState := by
  intro b g h
  refine ⟨fun v => if v = 1 then h 0 else g v, ?_, ?_⟩
  · rintro t (member | member | ⟨o, -, rfl⟩)
    · simp [Examples.tokenState] at member
    · simp [Examples.tokenState] at member
    · rfl
  · intro t member
    have listed : t ∈ [x] := member
    obtain rfl := List.mem_singleton.mp listed
    rfl

/-- **The twin is admitted alone.** -/
theorem twin_admitted : twin.firing.Admits X Examples.tokenState := by
  refine ⟨⟨twin_fresh, List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩,
    ⟨by decide, by decide, by decide, by decide, fun q member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, Examples.everywhere 1, fun e member => ?_⟩, fun b σ _ =>
      ⟨fun check member => absurd member List.not_mem_nil, fun q member => absurd member List.not_mem_nil⟩⟩
  have info : twin.firing.information X Examples.tokenState = [(.var 1, c 1)] := rfl
  rw [info] at member
  obtain rfl := List.mem_singleton.mp member
  rfl

theorem twin_valid :
    (baseFiring action twin).Valid action onesLabel (configurationOf Examples.tokenState) :=
  ((OneFrame.admits_toFirstOrder_iff (A := action) (label := onesLabel) (P := readers)
    (configurationOf Examples.tokenState) twin.firing).mp ⟨twin_admitted, rfl⟩).1

/-- **Two copies of the twin are a round of the base layer**: each is valid, their equations are jointly
consistent, they take and make nothing, and they have no checks. -/
theorem twins_round :
    AnnotatedRuns.Round action onesLabel (configurationOf Examples.tokenState)
      (image action [twin, twin]) := by
  refine ⟨fun f inside => ?_, ⟨Examples.everywhere 1, fun e member => ?_⟩,
    List.pairwise_pair.mpr ⟨?_, fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil⟩⟩
  · rcases List.mem_cons.mp inside with rfl | rest
    · exact twin_valid
    · rw [List.mem_singleton.mp rest]
      exact twin_valid
  · have joint : AnnotatedRuns.jointProblem onesLabel (configurationOf Examples.tokenState)
        (image action [twin, twin]) = [(.var 1, c 1), (.var 1, c 1)] := rfl
    rw [joint] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    subst member
    rfl
  · unfold MeTTaCalculus.OccurrenceCommits.Independent MeTTaCalculus.OccurrenceCommits.Clash
      MeTTaCalculus.OccurrenceCommits.Spoils MeTTaCalculus.OccurrenceCommits.WritesInto
    decide

/-- **Every member whose image is the twin's opens the rule's unknown as `x₁`.** -/
theorem opens_as_twin (m : OneMember action ℕ readers)
    (same : baseFiring action m = baseFiring action twin) : m.opening 0 = .var 1 := by
  obtain ⟨rule, member, opening, selection, seen⟩ := m
  have isRead : rule = readAny := member
  subst isRead
  have reads : [Subst.applyTerm opening x] = [(Term.var 1 : Term atoms)] :=
    congrArg (fun f : AnnotatedRuns.Firing (Term atoms) (Subst atoms) ℕ => f.rule.read) same
  exact (List.cons.inj reads).1

/-- **The round of the two twins is the image of no bag admitted on its own**: two members with these
images open the rule's unknown as one `x₁`, so they are not jointly fresh. The state mentions only fixed
terms (`tokenState_fixed`), and each member is admitted alone (`twin_admitted`). -/
theorem twins_not_image (l : List (OneMember action ℕ readers))
    (same : image action l = image action [twin, twin]) :
    ¬ Bag.AdmitsOwn X Examples.tokenState (bagOf action l) := by
  intro own
  obtain ⟨m₁, rest, rfl, first, tail⟩ := List.map_eq_cons_iff.mp same
  obtain ⟨m₂, rest', rfl, second, -⟩ := List.map_eq_cons_iff.mp tail
  have realized := own.1.1 PUnit.unit (Subst.id atoms)
  have afterOne := (realized_cons X m₁ (m₂ :: rest') _).mp realized (fun _ => c 1)
  have afterTwo := (realized_cons X m₂ rest' _).mp afterOne (fun _ => c 2)
  obtain ⟨u, ⟨-, atOne⟩, atTwo⟩ := Realized.exists X (fun _ => ⟨Subst.id atoms⟩) rest' afterTwo
  have rule₁ : m₁.rule = readAny := m₁.member
  have rule₂ : m₂.rule = readAny := m₂.member
  have term₁ : x ∈ m₁.rule.terms := by
    rw [rule₁]
    exact List.mem_singleton_self x
  have term₂ : x ∈ m₂.rule.terms := by
    rw [rule₂]
    exact List.mem_singleton_self x
  have u₁ : Subst.applyTerm u (m₁.opening 0) = c 1 := atOne x term₁
  have u₂ : Subst.applyTerm u (m₂.opening 0) = c 2 := atTwo x term₂
  rw [opens_as_twin m₁ first] at u₁
  rw [opens_as_twin m₂ second] at u₂
  exact absurd (Term.const.inj (u₁.symm.trans u₂)) (by decide)

/-! ## Fixed terms are not needed for rounds -/

/-- Read the row and tell it is `5`, the rule's unknown opened as `x₂`. -/
def fiveAgain : OneMember action ℕ SharedUnknown.program :=
  ⟨Examples.answer, Or.inl rfl, SharedUnknown.shiftBy 2, ⟨[], [0], []⟩, []⟩

/-- Two matches that tell the row is `5`. -/
abbrev fives : List (OneMember action ℕ SharedUnknown.program) := [SharedUnknown.five, fiveAgain]

/-- **The state whose row is the unknown `x` does not mention only fixed terms.** -/
theorem openRequest_not_fixed : ¬ FixedState action Examples.openRequest := by
  intro fixed
  have moved : c 6 = x :=
    fixed x (Or.inr (Or.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩)) (Examples.everywhere 6)
  cases moved

theorem fives_admitted : Bag.AdmitsOwn X Examples.openRequest (bagOf action fives) := by
  refine ⟨⟨fun b g => ?_, by decide, by decide, fun m inside => ?_⟩,
    ⟨by decide, by decide, by decide, by decide, fun q member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, Examples.everywhere 5, fun e member => ?_⟩, fun m inside => ?_⟩
  · refine (realized_cons X SharedUnknown.five [fiveAgain] _).mpr fun h₁ =>
      (realized_cons X fiveAgain [] _).mpr fun h₂ =>
        (realized_nil X _).mpr ⟨fun v => if v = 1 then h₁ 0 else if v = 2 then h₂ 0 else g v,
          ⟨⟨?_, ?_⟩, ?_⟩⟩
    · rintro t (member | member | ⟨o, -, rfl⟩)
      · exact absurd member List.not_mem_nil
      · exact absurd member List.not_mem_nil
      · rfl
    · intro t member
      have listed : t ∈ [x, x, c 5] := member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
      rcases listed with rfl | rfl | rfl <;> rfl
    · intro t member
      have listed : t ∈ [x, x, c 5] := member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
      rcases listed with rfl | rfl | rfl <;> rfl
  · rcases List.mem_cons.mp inside with rfl | rest
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · obtain rfl := List.mem_singleton.mp rest
      exact ⟨rfl, rfl, rfl, rfl⟩
  · have info : Bag.information X Examples.openRequest (bagOf action fives) =
        [(.var 1, x), (.var 1, c 5), (.var 2, x), (.var 2, c 5)] := rfl
    rw [info] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl
  · rcases List.mem_cons.mp inside with rfl | rest
    · exact fun _ _ _ => ⟨fun check member => absurd member List.not_mem_nil,
        fun q member => absurd member List.not_mem_nil⟩
    · obtain rfl := List.mem_singleton.mp rest
      exact fun _ _ _ => ⟨fun check member => absurd member List.not_mem_nil,
        fun q member => absurd member List.not_mem_nil⟩

/-- **At a state whose row is an unknown, a bag of positive rules admitted on its own has a round of the
base layer as its image.** -/
theorem unknown_round :
    ¬ FixedState action Examples.openRequest ∧
      Bag.AdmitsOwn X Examples.openRequest (bagOf action fives) ∧
      AnnotatedRuns.Round action Examples.openRequest.label (configurationOf Examples.openRequest)
        (image action fives) := by
  refine ⟨openRequest_not_fixed, fives_admitted, round_image_of_positive action fives_admitted ?_ ?_⟩
  · intro m inside
    rcases List.mem_cons.mp inside with rfl | rest
    · rfl
    · obtain rfl := List.mem_singleton.mp rest
      rfl
  · intro m inside
    rcases List.mem_cons.mp inside with rfl | rest
    · exact ⟨fun check member => absurd member List.not_mem_nil, rfl⟩
    · obtain rfl := List.mem_singleton.mp rest
      exact ⟨fun check member => absurd member List.not_mem_nil, rfl⟩

/-! ## Fixed terms are needed for the guards at the joint information -/

/-- **At a state whose rows are unknowns, a bag of positive rules admitted with the guards at the joint
information has an image that is not a round**: each member's guard asks what the other tells. With fixed
terms this cannot happen (`round_image_of_admits_fixed`). -/
theorem jointGuards_need_fixed :
    ¬ FixedState action Knowledge.start ∧
      Bag.Admits X Knowledge.start (bagOf action [Knowledge.first, Knowledge.second]) ∧
      (∀ m ∈ [Knowledge.first, Knowledge.second], Positive m.rule) ∧
      ¬ AnnotatedRuns.Round action Knowledge.start.label (configurationOf Knowledge.start)
          (image action [Knowledge.first, Knowledge.second]) := by
  refine ⟨fun fixed => ?_, Knowledge.both_admitted, fun m inside => ?_, fun round => ?_⟩
  · have moved : c 6 = Knowledge.v 0 :=
      fixed (Knowledge.v 0) (Or.inr (Or.inr ⟨0, by decide, rfl⟩)) (Examples.everywhere 6)
    cases moved
  · rcases List.mem_cons.mp inside with rfl | rest
    · exact ⟨fun check member => ⟨_, _, List.mem_singleton.mp member⟩, rfl⟩
    · obtain rfl := List.mem_singleton.mp rest
      exact ⟨fun check member => ⟨_, _, List.mem_singleton.mp member⟩, rfl⟩
  · refine Knowledge.both_refused_own (admitsOwn_of_round action round Knowledge.both_fresh ?_).1
    intro m inside
    rcases List.mem_cons.mp inside with rfl | rest
    · rfl
    · obtain rfl := List.mem_singleton.mp rest
      rfl

/-! ## The labels of a round -/

/-- The two spends of `JointFirings.Between`: take the token at `0` making `10`, take the token at `1`
making `11`. -/
abbrev spends : List (OneMember action ℕ Between.watched) :=
  [Between.spendAt 0 10, Between.spendAt 1 11]

/-- **Under the state's own labels the image of a bag admitted on its own is not a round**: the base layer
labels each identity once, and the state labels the identities the bag makes as tokens, not as the rows
the bag makes. **Under the labels of its round the image is a round.** -/
theorem labels_of_round :
    Bag.AdmitsOwn X EveryControls.twoTokens (bagOf action spends) ∧
      ¬ AnnotatedRuns.Round action EveryControls.twoTokens.label
          (configurationOf EveryControls.twoTokens) (image action spends) ∧
      AnnotatedRuns.Round action (roundLabel action EveryControls.twoTokens spends)
        (configurationOf EveryControls.twoTokens) (image action spends) := by
  refine ⟨Between.spend_admitted, fun round => ?_,
    round_image_canonical action Between.spend_admitted fun m inside => ?_⟩
  · have wrong : [c 1] = [c 2] := (round.valid _ List.mem_cons_self).firing.outputs
    exact absurd (Term.const.inj (List.cons.inj wrong).1) (by decide)
  · rcases List.mem_cons.mp inside with rfl | rest
    · exact ⟨fun check member => absurd member List.not_mem_nil, rfl⟩
    · obtain rfl := List.mem_singleton.mp rest
      exact ⟨fun check member => absurd member List.not_mem_nil, rfl⟩

/-- The two spends are positive: their rule has no checks and no collect query. -/
theorem spends_positive : ∀ m ∈ spends, Positive m.rule := by
  intro m inside
  rcases List.mem_cons.mp inside with rfl | rest
  · exact ⟨fun check member => absurd member List.not_mem_nil, rfl⟩
  · obtain rfl := List.mem_singleton.mp rest
    exact ⟨fun check member => absurd member List.not_mem_nil, rfl⟩

/-- **The images of the two spends are statically independent**: no checks, no predicate queries, and
footprints that take and make different identities. -/
theorem spends_static :
    (image action spends).Pairwise
      (AnnotatedRuns.StaticIndependent (roundLabel action EveryControls.twoTokens spends)) := by
  refine List.pairwise_pair.mpr ⟨⟨rfl, fun _ member => absurd member List.not_mem_nil⟩,
    ⟨rfl, fun _ member => absurd member List.not_mem_nil⟩, fun _ _ => ?_⟩
  show MeTTaCalculus.OccurrenceCommits.TraceIndependent _
    ((Between.spendAt 0 10).selection.commit (T := Term atoms))
    ((Between.spendAt 1 11).selection.commit (T := Term atoms))
  unfold MeTTaCalculus.OccurrenceCommits.TraceIndependent MeTTaCalculus.OccurrenceCommits.Independent
    MeTTaCalculus.OccurrenceCommits.Clash MeTTaCalculus.OccurrenceCommits.Spoils
    MeTTaCalculus.OccurrenceCommits.WritesInto MeTTaCalculus.OccurrenceCommits.Commit.uses
  decide

/-- **A multi-firing step of the base layer from a bag admitted on its own**: the two spends, under the
labels of their round, are one step of the base layer's Petri-net semantics (offered by every offer). -/
theorem spends_step :
    Race.StepMoves action (roundLabel action EveryControls.twoTokens spends) (fun (_ : Unit) _ => True)
      (configurationOf EveryControls.twoTokens) (↑(spends.map fun _ => ()) : Multiset Unit)
      (AnnotatedRuns.follow (roundLabel action EveryControls.twoTokens spends)
        (configurationOf EveryControls.twoTokens) (image action spends)) :=
  stepMoves_of_admitsOwn action (fun _ => ())
    (admitsOwn_of_congruent action
      (congruent_relabel fun _ present => roundLabel_present action Between.spend_admitted.2.1 present)
      Between.spend_admitted)
    (fun _ inM => keepsLabels_roundLabel action Between.spend_admitted.1 inM) spends_positive
    (List.cons_ne_nil _ _) (fun _ _ => trivial) spends_static

/-! ## A runtime round that is not a round of the base layer -/

/-- A list is a reordering of two items exactly when it is one of their two orders. -/
theorem perm_two {α : Type*} {a b : α} {l : List α} (perm : l.Perm [a, b]) :
    l = [a, b] ∨ l = [b, a] := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem (perm.symm.subset List.mem_cons_self)
  have rest : (s ++ t).Perm [b] := (List.perm_middle.symm.trans perm).cons_inv
  rcases List.append_eq_singleton_iff.mp (List.perm_singleton.mp rest) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Take a `1`, make a `1`. -/
def refresh : Rule Tm := ⟨PUnit.unit, ⟨[c 1], [], [], [], [c 1]⟩, []⟩

/-- Make a `2` when exactly one `1` is present. -/
def countOne : Rule Tm := ⟨PUnit.unit, ⟨[], [], [], [.count (c 1) 1], [c 2]⟩, []⟩

/-- **The program**: refresh a `1`; make a `2` when exactly one `1` is present. -/
def refreshing : Program Tm := {refresh, countOne}

/-- Refresh the `1` at `0`, making `10`. -/
def refreshAt : OneMember action ℕ refreshing :=
  ⟨refresh, Or.inl rfl, Subst.id atoms, ⟨[0], [], [10]⟩, []⟩

/-- Count the `1`s, making `11`. -/
def countAt : OneMember action ℕ refreshing :=
  ⟨countOne, Or.inr rfl, Subst.id atoms, ⟨[], [], [11]⟩, []⟩

/-- The two. -/
abbrev refreshPair : List (OneMember action ℕ refreshing) := [refreshAt, countAt]

/-- The labels: `11` is a `2`, every other identity a `1`. -/
def refreshLabel : ℕ → Term atoms := fun o => if o = 11 then c 2 else c 1

/-- One `1`, at `0`. -/
def oneToken : State Tm ℕ := ⟨PUnit.unit, [], {0}, refreshLabel⟩

theorem refreshPair_members {m : OneMember action ℕ refreshing} (inside : m ∈ refreshPair) :
    m = refreshAt ∨ m = countAt := by
  rcases List.mem_cons.mp inside with first | rest
  · exact Or.inl first
  · exact Or.inr (List.mem_singleton.mp rest)

theorem refresh_ground : ∀ t ∈ refresh.terms, ∀ σ : Subst atoms, action.apply σ t = t := by
  intro t member σ
  have listed : t ∈ [c 1, c 1] := member
  rcases List.mem_cons.mp listed with rfl | rest
  · rfl
  · rw [List.mem_singleton.mp rest]
    rfl

theorem countOne_ground : ∀ t ∈ countOne.terms, ∀ σ : Subst atoms, action.apply σ t = t := by
  intro t member σ
  have listed : t ∈ [c 1, c 2] := member
  rcases List.mem_cons.mp listed with rfl | rest
  · rfl
  · rw [List.mem_singleton.mp rest]
    rfl

/-- **Exactly one `1` is present** at a state with one present row, labelled `1`. -/
theorem count_one {s : State Tm ℕ} {p : ℕ} (present : s.present = {p}) (labelled : s.label p = c 1)
    (g : Firing ℕ E refreshing PUnit.unit) (σ : Subst atoms) :
    (matchesAt X (a := PUnit.unit) (b := PUnit.unit) σ (g.row X s) s.present (c 1)).card = 1 := by
  have only : matchesAt X (a := PUnit.unit) (b := PUnit.unit) σ (g.row X s) s.present (c 1) = {p} := by
    ext o
    rw [mem_matchesAt, present, Finset.mem_singleton]
    constructor
    · exact fun both => both.1
    · intro same
      refine ⟨same, ?_⟩
      rw [same]
      show Subst.applyTerm σ (c 1) = Subst.applyTerm σ (Subst.applyTerm (Subst.id atoms) (s.label p))
      rw [labelled]
      rfl
  rw [only, Finset.card_singleton]

/-- **The bag of the refresh and the count is admitted on its own at the state of one `1`.** -/
theorem refreshPair_admitted : Bag.AdmitsOwn X oneToken (bagOf action refreshPair) := by
  refine ⟨⟨fresh_of_ground_bag action oneToken _ fun m inside => ?_, by decide, by decide,
      fun m inside => ?_⟩, ⟨by decide, by decide, by decide, by decide,
        fun q member => by simp [Selection.commit] at member⟩,
      ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩, fun m inside b σ _ => ?_⟩
  · rcases refreshPair_members inside with rfl | rfl
    · exact refresh_ground
    · exact countOne_ground
  · rcases refreshPair_members inside with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · have info : Bag.information X oneToken (bagOf action refreshPair) = [(c 1, c 1)] := rfl
    rw [info] at member
    obtain rfl := List.mem_singleton.mp member
    rfl
  · rcases refreshPair_members inside with rfl | rfl
    · exact ⟨fun check member => absurd member List.not_mem_nil,
        fun q member => absurd member List.not_mem_nil⟩
    · refine ⟨fun check member => ?_, fun q member => absurd member List.not_mem_nil⟩
      rw [List.mem_singleton.mp member]
      exact count_one (s := oneToken) (p := 0) rfl rfl countAt.firing σ

/-- After the refresh, the count is admitted: the new `1` is the one `1`. -/
theorem count_after_refresh : countAt.firing.Admits X (refreshAt.firing.result X oneToken) := by
  refine ⟨⟨Examples.fresh_of_ground action _ countAt.firing countOne_ground, List.nodup_nil,
      List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, rfl, rfl, rfl, rfl⟩,
    ⟨by decide, by decide, by decide, by decide, fun q member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩, fun b σ _ => ⟨fun check member => ?_,
      fun q member => absurd member List.not_mem_nil⟩⟩
  · have info : countAt.firing.information X (refreshAt.firing.result X oneToken) = [(c 1, c 1)] := rfl
    rw [info] at member
    obtain rfl := List.mem_singleton.mp member
    rfl
  · rw [List.mem_singleton.mp member]
    exact count_one (s := refreshAt.firing.result X oneToken) (p := 10) (by decide) rfl countAt.firing σ

/-- After the count, the refresh is admitted: the `1` at `0` is still present. -/
theorem refresh_after_count : refreshAt.firing.Admits X (countAt.firing.result X oneToken) := by
  refine ⟨⟨Examples.fresh_of_ground action _ refreshAt.firing refresh_ground,
      List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
      List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, rfl, rfl, rfl, rfl⟩,
    ⟨by decide, by decide, by decide, by decide, fun q member => by simp [Selection.commit] at member⟩,
    ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩, fun b σ _ =>
      ⟨fun check member => absurd member List.not_mem_nil, fun q member => absurd member List.not_mem_nil⟩⟩
  have info : refreshAt.firing.information X (countAt.firing.result X oneToken) = [(c 1, c 1)] := rfl
  rw [info] at member
  obtain rfl := List.mem_singleton.mp member
  rfl

/-- **A runtime round need not be a round of the base layer.** One member takes a `1` and makes a `1`;
the other makes a `2` when exactly one `1` is present. The count check is not positive. Fired one after
another in either order the two are admitted and reach states congruent to the bag's result, so the bag
is a runtime round; but the count check does not ignore the refresh's writes, so its image is not a
round. The write-ignorance of the base layer is sufficient for running in every order, not necessary. -/
theorem refresh_separates :
    ¬ (∀ m ∈ refreshPair, Positive m.rule) ∧ RuntimeRound action oneToken refreshPair ∧
      ¬ AnnotatedRuns.Round action refreshLabel (configurationOf oneToken) (image action refreshPair) := by
  refine ⟨fun positive => ?_, runtimeRound_of_fires action refreshPair_admitted fun l perm => ?_,
    fun round => ?_⟩
  · obtain ⟨_, _, equal⟩ := (positive countAt (List.mem_cons_of_mem _ List.mem_cons_self)).1
      (Check.count (c 1) 1) List.mem_cons_self
    cases equal
  · rcases perm_two perm with rfl | rfl
    · exact ⟨Bag.admits_member X (fun _ _ => ⟨Subst.id atoms⟩) refreshPair_admitted List.mem_cons_self,
        count_after_refresh, trivial⟩
    · exact ⟨Bag.admits_member X (fun _ _ => ⟨Subst.id atoms⟩) refreshPair_admitted
        (List.mem_cons_of_mem _ List.mem_cons_self), refresh_after_count, trivial⟩
  · have compatible := List.pairwise_pair.mp round.compatible
    have ignored := compatible.2.2.1 (Check.count (c 1) 1) (List.mem_singleton_self _) 0
      (List.mem_append_left _ (List.mem_singleton_self 0))
    refine ignored ⟨Subst.id atoms, fun e member => ?_⟩
    have listed : e ∈ [(c 1, c 1), (c 1, c 1)] := member
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at listed
    subst listed
    rfl

#print axioms none_separates
#print axioms ninePair_admitted
#print axioms ninePair_round
#print axioms tokenState_fixed
#print axioms twin_admitted
#print axioms twins_round
#print axioms opens_as_twin
#print axioms twins_not_image
#print axioms openRequest_not_fixed
#print axioms fives_admitted
#print axioms unknown_round
#print axioms jointGuards_need_fixed
#print axioms labels_of_round
#print axioms spends_positive
#print axioms spends_static
#print axioms spends_step
#print axioms perm_two
#print axioms count_one
#print axioms refreshPair_admitted
#print axioms count_after_refresh
#print axioms refresh_after_count
#print axioms refresh_separates

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Rounds.Controls
