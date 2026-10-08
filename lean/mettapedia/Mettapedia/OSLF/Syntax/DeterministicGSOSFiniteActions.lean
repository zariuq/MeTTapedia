import Mettapedia.OSLF.Syntax.DeterministicGSOSObservation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range

/-!
# Image-finite rule presentations and finite-action recovery

A finite set of rules for one operator and output action has one uniform
finite observation bound, including unsuccessful guards. Conversely such
a bound yields a finite rule presentation. Finite action carriers supply
this bound for every complete guarded schema. Arbitrarily many finite
premise rules have the weaker successful-observation characterization.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS

open CategoryTheory Mettapedia.TypeTheory

universe u

variable {S : Signature.{u}} (Actions : S.Srt → Type u)

/-- Each operator and output action has only finitely many authored rules. -/
def ImageFinite (presentation : FinitePresentation Actions) : Prop :=
  ∀ sort (operator : S.Operator sort) action, (presentation sort operator action).Finite

/-- One finite observation bound determines successes and failures alike. -/
def UniformFiniteObservation (rules : GuardedSchemas Actions) : Prop :=
  ∀ sort (operator : S.Operator sort) action,
    ∃ observed : Finset (Address Actions operator),
      ∀ first second, (∀ address ∈ observed, second address = first address) →
        universalReadout Actions rules operator second action =
          universalReadout Actions rules operator first action

theorem ImageFinite.uniformObservation {presentation : FinitePresentation Actions}
    {rules : GuardedSchemas Actions} (imageFinite : ImageFinite Actions presentation)
    (denotes : Denotes Actions presentation rules) : UniformFiniteObservation Actions rules := by
  classical
  intro sort operator action
  let authored := (imageFinite sort operator action).toFinset
  let observed := authored.biUnion FiniteRule.observed
  refine ⟨observed, ?_⟩
  intro first second agrees
  have transfer : ∀ rule ∈ presentation sort operator action,
      rule.Matches first ↔ rule.Matches second := by
    intro rule member
    have contained : ∀ address ∈ rule.observed, address ∈ observed := by
      intro address present
      apply Finset.mem_biUnion.mpr
      exact ⟨rule, (Set.Finite.mem_toFinset _).mpr member, present⟩
    constructor
    · intro matching address present
      exact (agrees address (contained address present)).trans (matching address present)
    · intro matching address present
      exact (agrees address (contained address present)).symm.trans (matching address present)
  cases firstRead : universalReadout Actions rules operator first action with
  | none =>
      cases secondRead : universalReadout Actions rules operator second action with
      | none => rfl
      | some target =>
          obtain ⟨rule, member, matching, readout⟩ :=
            (denotes sort operator action second target).mp secondRead
          have impossible := (denotes sort operator action first target).mpr
            ⟨rule, member, (transfer rule member).mpr matching, readout⟩
          rw [firstRead] at impossible
          cases impossible
  | some target =>
      obtain ⟨rule, member, matching, readout⟩ :=
        (denotes sort operator action first target).mp firstRead
      exact (denotes sort operator action second target).mpr
        ⟨rule, member, (transfer rule member).mp matching, readout⟩

/-- One finite rule for a supplied finite positive/negative observation pattern. -/
noncomputable def ruleAtPattern (rules : GuardedSchemas Actions)
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort)
    (observed : Finset (Address Actions operator))
    (pattern : {address // address ∈ observed} → Bool) :
    Option (FiniteRule Actions operator) :=
  (rules sort operator (observedGuard Actions observed pattern) action).map
    (fun target => ⟨observed, pattern, target⟩)

/-- The finite collection of conclusions over all patterns on a fixed bound. -/
noncomputable def boundedPresentation (rules : GuardedSchemas Actions)
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort)
    (observed : Finset (Address Actions operator)) : Set (FiniteRule Actions operator) :=
  {rule | ∃ pattern, ruleAtPattern Actions rules operator action observed pattern = some rule}

theorem boundedPresentation_finite (rules : GuardedSchemas Actions)
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort)
    (observed : Finset (Address Actions operator)) :
    (boundedPresentation Actions rules operator action observed).Finite := by
  classical
  apply Set.Finite.of_injOn (f := some)
    (t := Set.range (ruleAtPattern Actions rules operator action observed))
  · rintro rule ⟨pattern, computed⟩
    exact ⟨pattern, computed⟩
  · intro first _ second _ equal
    exact Option.some.inj equal
  · exact Set.finite_range _

theorem boundedPresentation_denotes (rules : GuardedSchemas Actions)
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort)
    (observed : Finset (Address Actions operator))
    (determines : ∀ first second, (∀ address ∈ observed, second address = first address) →
      universalReadout Actions rules operator second action =
        universalReadout Actions rules operator first action)
    (guard : Guard Actions operator) (target : S.Term (universalVariables Actions operator) sort) :
    universalReadout Actions rules operator guard action = some target ↔
      ∃ rule ∈ boundedPresentation Actions rules operator action observed,
        rule.Matches guard ∧ rule.readout = target := by
  classical
  constructor
  · intro success
    let pattern : {address // address ∈ observed} → Bool := fun address => guard address.1
    let truncated := observedGuard Actions observed pattern
    have agrees : ∀ address ∈ observed, truncated address = guard address := by
      intro address present
      simp [truncated, observedGuard, present, pattern]
    have truncatedRead := (determines guard truncated agrees).trans success
    cases sourceRead : rules sort operator truncated action with
    | none => simp [universalReadout, sourceRead] at truncatedRead
    | some body =>
        let rule : FiniteRule Actions operator := ⟨observed, pattern, body⟩
        refine ⟨rule, ⟨pattern, ?_⟩, ?_, ?_⟩
        · simp only [ruleAtPattern, sourceRead, Option.map_some, rule, truncated]
        · intro address present
          rfl
        · simpa only [FiniteRule.readout, rule, truncated, universalReadout,
            sourceRead, Option.map_some, Option.some.injEq]
            using truncatedRead
  · rintro ⟨rule, ⟨pattern, computed⟩, matching, readout⟩
    cases sourceRead : rules sort operator (observedGuard Actions observed pattern) action with
    | none => simp [ruleAtPattern, sourceRead] at computed
    | some body =>
        have identified : (⟨observed, pattern, body⟩ : FiniteRule Actions operator) = rule := by
          simpa only [ruleAtPattern, sourceRead, Option.map_some, Option.some.injEq] using computed
        subst rule
        have agrees : ∀ address ∈ observed,
            guard address = observedGuard Actions observed pattern address := by
          intro address present
          exact (matching address present).trans (by simp [observedGuard, present])
        rw [determines _ guard agrees]
        simpa only [FiniteRule.readout, universalReadout, sourceRead, Option.map_some]
          using congrArg some readout

/-- Uniform finite observations characterize image-finite ordinary GSOS presentations. -/
theorem imageFinite_iff_uniformFiniteObservation (rules : GuardedSchemas Actions) :
    (∃ presentation : FinitePresentation Actions,
      ImageFinite Actions presentation ∧ Denotes Actions presentation rules) ↔
      UniformFiniteObservation Actions rules := by
  classical
  constructor
  · rintro ⟨presentation, finite, denotes⟩
    exact finite.uniformObservation Actions denotes
  · intro uniform
    let observed := fun sort (operator : S.Operator sort) action =>
      (uniform sort operator action).choose
    let presentation : FinitePresentation Actions := fun sort operator action =>
      boundedPresentation Actions rules operator action (observed sort operator action)
    refine ⟨presentation, ?_, ?_⟩
    · intro sort operator action
      exact boundedPresentation_finite Actions rules operator action _
    · intro sort operator action guard target
      exact boundedPresentation_denotes Actions rules operator action _
        (uniform sort operator action).choose_spec guard target

/-- Finite action carriers make the full availability pattern finitely observable. -/
theorem finiteActions_uniform (rules : GuardedSchemas Actions)
    [∀ sort, Finite (Actions sort)] : UniformFiniteObservation Actions rules := by
  classical
  intro sort operator action
  let : Finite (S.Position operator) := S.finite operator
  let : Fintype (Address Actions operator) := Fintype.ofFinite _
  refine ⟨Finset.univ, ?_⟩
  intro first second agrees
  have equal : second = first := funext (fun address => agrees address (Finset.mem_univ address))
  rw [equal]

/-- The complete correspondence recovers ordinary image-finite GSOS under finite actions. -/
theorem finiteActions_imageFinite (rules : GuardedSchemas Actions)
    [∀ sort, Finite (Actions sort)] :
    ∃ presentation : FinitePresentation Actions,
      ImageFinite Actions presentation ∧ Denotes Actions presentation rules :=
  (imageFinite_iff_uniformFiniteObservation Actions rules).mpr (finiteActions_uniform Actions rules)

end Mettapedia.OSLF.DeterministicGSOS
