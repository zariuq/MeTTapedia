import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy
import Mettapedia.GSLT.Logic.ImageFinitenessNecessary

/-!
# Finite behavioral covers with infinitely many literal successors

The authored equations remain equality. Each branch has infinitely many
distinct terminal successors in two observed parity classes. Alarm and parity
observations still distinguish genuinely different states. Thus behavioral-cover
adequacy is not obtained by changing equations or discarding observations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HennessyMilner.BehavioralCoverControls

inductive State where
  | branch (identity : Bool)
  | terminal (identity : Nat)
  | alarm
  deriving DecidableEq

inductive Kind where
  | branch
  | terminal (parity : Nat)
  | alarm
  deriving DecidableEq

def kind : State → Kind
  | .branch _ => .branch
  | .terminal identity => .terminal (identity % 2)
  | .alarm => .alarm

inductive Step : State → State → Prop
  | branch (identity : Bool) (next : Nat) : Step (.branch identity) (.terminal next)

inductive Observation where
  | odd
  | alarm
  deriving DecidableEq

def observes : Observation → State → Prop
  | .odd, .terminal identity => identity % 2 = 1
  | .odd, _ => False
  | .alarm, state => state = .alarm

def theory : GSLT where
  Term := State
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := Step
  rewrites_resp_left := by
    rintro source _ target rfl step
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    rintro source target _ step rfl
    exact step

def system : HennessyMilner.System theory where
  Atom := Observation
  observes := observes
  observes_resp := by
    rintro atom left _ rfl
    exact Iff.rfl
  Label := Unit
  act _ := Step
  act_resp_left := by
    rintro label source _ target rfl step
    exact ⟨target, step, rfl⟩
  act_resp_right := by
    rintro label source target _ step rfl
    exact step

private theorem match_of_kind_eq {left right : State} (same : kind left = kind right)
    {next : State} (step : Step left next) :
    ∃ matched, Step right matched ∧ kind next = kind matched := by
  cases step with
  | branch identity next =>
    cases right with
    | branch other => exact ⟨.terminal next, .branch other next, rfl⟩
    | terminal other => cases same
    | alarm => cases same

/-- Actual stepping and observation preservation justify the classifier relation. -/
theorem bisimilar_of_kind_eq {left right : State} (same : kind left = kind right) :
    system.Bisimilar left right := by
  refine ⟨fun left right => kind left = kind right, ⟨?_, ?_, ?_⟩, same⟩
  · intro left right pair label next step
    exact match_of_kind_eq pair step
  · intro left right pair label next step
    obtain ⟨matched, actual, hKind⟩ := match_of_kind_eq pair.symm step
    exact ⟨matched, actual, hKind.symm⟩
  · intro left right pair atom
    change observes atom left ↔ observes atom right
    cases atom <;> cases left <;> cases right <;> simp_all [kind, observes]

theorem behavioral_successors_have_two_class_cover : system.ImageFiniteBisimilar := by
  intro label term
  refine ⟨{State.terminal 0, State.terminal 1},
    Set.Finite.insert _ (Set.finite_singleton _), ?_⟩
  intro target step
  cases step with
  | branch identity next =>
    have hParity : next % 2 = 0 ∨ next % 2 = 1 := Nat.mod_two_eq_zero_or_one next
    refine ⟨.terminal (next % 2), ?_, bisimilar_of_kind_eq (by simp [kind])⟩
    change State.terminal (next % 2) = State.terminal 0 ∨
      State.terminal (next % 2) = State.terminal 1
    rcases hParity with hZero | hOne
    · exact Or.inl (congrArg State.terminal hZero)
    · exact Or.inr (congrArg State.terminal hOne)

theorem literal_successors_are_infinite :
    Set.Infinite {target | system.act () (.branch false) target} := by
  have injective : Function.Injective State.terminal := fun _ _ same => State.terminal.inj same
  refine (Set.infinite_range_of_injective injective).mono ?_
  rintro target ⟨next, rfl⟩
  exact Step.branch false next

theorem not_image_finite_modulo_authored_equations : ¬system.ImageFiniteModulo := by
  intro finite
  obtain ⟨representatives, hFinite, covered⟩ := finite () (.branch false)
  have subset : {target | system.act () (.branch false) target} ⊆ representatives := by
    intro target step
    obtain ⟨representative, hMember, equivalent⟩ := covered step
    have equal : target = representative := equivalent
    exact equal.symm ▸ hMember
  exact literal_successors_are_infinite (hFinite.subset subset)

theorem behavioral_cover_is_strictly_weaker_here :
    system.ImageFiniteBisimilar ∧ ¬system.ImageFiniteModulo :=
  ⟨behavioral_successors_have_two_class_cover, not_image_finite_modulo_authored_equations⟩

theorem actual_behavioral_cover_adequacy (left right : State) :
    system.LogicallyEquivalent left right ↔ system.Bisimilar left right :=
  system.logicallyEquivalent_iff_bisimilar_of_imageFiniteBisimilar
    behavioral_successors_have_two_class_cover left right

theorem distinct_literal_branches_are_logically_equivalent :
    State.branch false ≠ .branch true ∧
      system.LogicallyEquivalent (.branch false) (.branch true) := by
  refine ⟨by decide, ?_⟩
  exact system.logicallyEquivalent_of_bisimilar (bisimilar_of_kind_eq rfl)

theorem alarm_is_behaviorally_distinct : ¬system.Bisimilar .alarm (.terminal 0) := by
  intro related
  have observed := system.logicallyEquivalent_of_bisimilar related (.atom .alarm)
  have impossible := observed.mp rfl
  cases impossible

/-- The two representatives really inhabit different behavioral classes. -/
theorem parity_representatives_are_behaviorally_distinct :
    ¬system.Bisimilar (.terminal 0) (.terminal 1) := by
  intro related
  have observed := system.logicallyEquivalent_of_bisimilar related (.atom .odd)
  have impossible : system.sat (.atom .odd) (.terminal 0) := observed.mpr rfl
  exact Nat.zero_ne_one impossible

theorem branch_and_terminal_are_behaviorally_distinct :
    ¬system.Bisimilar (.branch false) (.terminal 0) := by
  rintro ⟨relation, bisimulation, pair⟩
  obtain ⟨matched, impossible, _⟩ := bisimulation.1 pair () (Step.branch false 0)
  cases impossible

/-- The existing generic failure of unrestricted HML adequacy also fails the
new hypothesis; finite behavioral coverage has not been silently dropped. -/
theorem unrestricted_counterexample_has_no_finite_behavioral_cover :
    ¬ImageFinitenessNecessary.hm.ImageFiniteBisimilar := by
  intro finite
  exact ImageFinitenessNecessary.not_bisimilar
    (ImageFinitenessNecessary.hm.bisimilar_of_logicallyEquivalent_of_imageFiniteBisimilar
      finite ImageFinitenessNecessary.logically_equivalent)

/-- The same genuinely infinite literal system is a client of positive
adequacy; no second state space or cover is introduced. -/
theorem actual_positive_behavioral_cover_adequacy (left right : State) :
    system.LogicalPreorder left right ↔ system.Similar left right :=
  system.logicalPreorder_iff_similar_of_imageFiniteBisimilar
    behavioral_successors_have_two_class_cover left right

theorem terminal_zero_similar_terminal_one :
    system.Similar (.terminal 0) (.terminal 1) := by
  refine ⟨fun left right => left = .terminal 0 ∧ right = .terminal 1, ⟨?_, ?_⟩,
    rfl, rfl⟩
  · rintro left right ⟨rfl, rfl⟩ label next step
    cases step
  · rintro left right ⟨rfl, rfl⟩ atom holds
    cases atom with
    | odd => exact False.elim (Nat.zero_ne_one holds)
    | alarm => cases holds

theorem terminal_one_not_similar_terminal_zero :
    ¬system.Similar (.terminal 1) (.terminal 0) := by
  intro related
  have impossible := system.logicalPreorder_of_similar related (.atom .odd) rfl
  exact Nat.zero_ne_one impossible

/-- Positive logical preorder is directional and is not bisimilarity. -/
theorem positive_order_is_strict_without_bisimilarity :
    system.LogicalPreorder (.terminal 0) (.terminal 1) ∧
      ¬system.LogicalPreorder (.terminal 1) (.terminal 0) ∧
      ¬system.Bisimilar (.terminal 0) (.terminal 1) := by
  refine ⟨(actual_positive_behavioral_cover_adequacy _ _).mpr terminal_zero_similar_terminal_one,
    ?_, parity_representatives_are_behaviorally_distinct⟩
  intro ordered
  exact terminal_one_not_similar_terminal_zero
    ((actual_positive_behavioral_cover_adequacy _ _).mp ordered)

theorem distinct_literal_branches_are_positively_equivalent :
    State.branch false ≠ .branch true ∧
      system.LogicalPreorder (.branch false) (.branch true) ∧
      system.LogicalPreorder (.branch true) (.branch false) := by
  refine ⟨by decide, ?_, ?_⟩
  · exact (actual_positive_behavioral_cover_adequacy _ _).mpr
      (system.similar_of_bisimilar (bisimilar_of_kind_eq rfl))
  · exact (actual_positive_behavioral_cover_adequacy _ _).mpr
      (system.similar_of_bisimilar (bisimilar_of_kind_eq rfl))

theorem branch_not_similar_terminal : ¬system.Similar (.branch false) (.terminal 0) := by
  rintro ⟨relation, simulation, pair⟩
  obtain ⟨matched, impossible, _⟩ := simulation.1 pair () (Step.branch false 0)
  cases impossible

theorem alarm_not_similar_terminal : ¬system.Similar .alarm (.terminal 0) := by
  intro related
  have impossible := system.logicalPreorder_of_similar related (.atom .alarm) rfl
  cases impossible

end Mettapedia.GSLT.HennessyMilner.BehavioralCoverControls
