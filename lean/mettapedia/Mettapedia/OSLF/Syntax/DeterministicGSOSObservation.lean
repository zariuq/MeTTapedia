import Mettapedia.OSLF.Syntax.DeterministicGSOSCorrespondence
import Mathlib.Data.Finset.Basic

/-!
# Finite-premise presentations and finite successful observations

Finite rules carry a finite set of tested input actions, their positive or
negative premises, and a finite target term over the corresponding names.
Their semantic characterization is finite-cylinder openness of successful
readouts in a fixed universal variable family. The characterization permits
arbitrary action carriers and arbitrarily many finite rules.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS

open CategoryTheory Mettapedia.TypeTheory

universe u

variable {S : Signature.{u}} (Actions : S.Srt → Type u)

/-- Universal names contain every original argument and every derivative. -/
abbrev universalVariables {sort : S.Srt} (operator : S.Operator sort) : S.Families :=
  ruleVariables Actions operator (fun _ => true)

/-- The actual inclusion of available names into the universal variable family. -/
def universalInclusion {sort : S.Srt} (operator : S.Operator sort)
    (guard : Guard Actions operator) :
    ruleVariables Actions operator guard ⟶ universalVariables Actions operator :=
  variableInclusion Actions (fun _ _ => rfl)

/-- Successful conclusions read in one fixed family, independently of the guard. -/
noncomputable def universalReadout (rules : GuardedSchemas Actions)
    {sort : S.Srt} (operator : S.Operator sort) (guard : Guard Actions operator)
    (action : Actions sort) : Option (S.Term (universalVariables Actions operator) sort) :=
  (rules sort operator guard action).map (S.rename (universalInclusion Actions operator guard))

/-- The complete guard retaining exactly a supplied finite list of premises. -/
noncomputable def observedGuard {sort : S.Srt} {operator : S.Operator sort}
    (observed : Finset (Address Actions operator))
    (pattern : {address // address ∈ observed} → Bool) : Guard Actions operator := by
  classical
  exact fun address => if present : address ∈ observed then pattern ⟨address, present⟩ else false

/-- An independently authored ordinary finite-premise rule. -/
structure FiniteRule {sort : S.Srt} (operator : S.Operator sort) where
  observed : Finset (Address Actions operator)
  pattern : {address // address ∈ observed} → Bool
  target : S.Term (ruleVariables Actions operator (observedGuard Actions observed pattern)) sort

namespace FiniteRule

variable {Actions}

/-- Every positive and negative premise of the finite rule holds. -/
def Matches {sort : S.Srt} {operator : S.Operator sort}
    (rule : FiniteRule Actions operator) (guard : Guard Actions operator) : Prop :=
  ∀ address (present : address ∈ rule.observed), guard address = rule.pattern ⟨address, present⟩

/-- Read the independently authored finite conclusion in universal variables. -/
noncomputable def readout {sort : S.Srt} {operator : S.Operator sort}
    (rule : FiniteRule Actions operator) : S.Term (universalVariables Actions operator) sort :=
  S.rename (universalInclusion Actions operator
    (observedGuard Actions rule.observed rule.pattern)) rule.target

theorem observed_matches {sort : S.Srt} {operator : S.Operator sort}
    (rule : FiniteRule Actions operator) :
    rule.Matches (observedGuard Actions rule.observed rule.pattern) := by
  classical
  intro address present
  simp [observedGuard, present]

end FiniteRule

/-- A finite-premise specification may contain arbitrarily many authored rules. -/
abbrev FinitePresentation :=
  (sort : S.Srt) → (operator : S.Operator sort) → Actions sort →
    Set (FiniteRule Actions operator)

/-- Its exact successful readouts, including the complete typed target term. -/
def Denotes (presentation : FinitePresentation Actions) (rules : GuardedSchemas Actions) : Prop :=
  ∀ sort (operator : S.Operator sort) action guard target,
    universalReadout Actions rules operator guard action = some target ↔
      ∃ rule ∈ presentation sort operator action, rule.Matches guard ∧ rule.readout = target

/-- Every successful readout is determined on a finite cylinder of input guards. -/
def FiniteSuccessfulObservation (rules : GuardedSchemas Actions) : Prop :=
  ∀ sort (operator : S.Operator sort) action guard target,
    universalReadout Actions rules operator guard action = some target →
      ∃ observed : Finset (Address Actions operator),
        ∀ other, (∀ address ∈ observed, other address = guard address) →
          universalReadout Actions rules operator other action = some target

theorem Denotes.finiteSuccessfulObservation
    {presentation : FinitePresentation Actions} {rules : GuardedSchemas Actions}
    (denotes : Denotes Actions presentation rules) :
    FiniteSuccessfulObservation Actions rules := by
  intro sort operator action guard target success
  obtain ⟨rule, member, matching, readout⟩ := (denotes sort operator action guard target).mp success
  refine ⟨rule.observed, ?_⟩
  intro other agrees
  apply (denotes sort operator action other target).mpr
  refine ⟨rule, member, ?_, readout⟩
  intro address present
  exact (agrees address present).trans (matching address present)

/-- The set of finite rules whose conclusions are sound on their own premise cylinders. -/
noncomputable def soundFinitePresentation (rules : GuardedSchemas Actions) :
    FinitePresentation Actions :=
  fun _ operator action => {rule | ∀ guard, rule.Matches guard →
    universalReadout Actions rules operator guard action = some rule.readout}

theorem finiteSuccessfulObservation_denotes {rules : GuardedSchemas Actions}
    (finite : FiniteSuccessfulObservation Actions rules) :
    Denotes Actions (soundFinitePresentation Actions rules) rules := by
  classical
  intro sort operator action guard target
  constructor
  · intro success
    obtain ⟨observed, determines⟩ := finite sort operator action guard target success
    let pattern : {address // address ∈ observed} → Bool := fun address => guard address.1
    let truncated := observedGuard Actions observed pattern
    have agrees : ∀ address ∈ observed, truncated address = guard address := by
      intro address present
      simp [truncated, observedGuard, present, pattern]
    have truncatedRead := determines truncated agrees
    cases sourceRead : rules sort operator truncated action with
    | none => simp [universalReadout, sourceRead] at truncatedRead
    | some body =>
        have bodyRead : S.rename (universalInclusion Actions operator truncated) body = target := by
          simpa only [universalReadout, sourceRead, Option.map_some, Option.some.injEq]
            using truncatedRead
        let rule : FiniteRule Actions operator := ⟨observed, pattern, body⟩
        have conclusion : rule.readout = target := bodyRead
        refine ⟨rule, ?_, ?_, conclusion⟩
        · intro other matching
          rw [conclusion]
          apply determines other
          exact matching
        · intro address present
          rfl
  · rintro ⟨rule, sound, matching, readout⟩
    exact (sound guard matching).trans (congrArg some readout)

/-- Exactly the finitely observed successes admit ordinary finite-premise rules. -/
theorem finitePremise_iff_finiteSuccessfulObservation (rules : GuardedSchemas Actions) :
    (∃ presentation : FinitePresentation Actions, Denotes Actions presentation rules) ↔
      FiniteSuccessfulObservation Actions rules := by
  constructor
  · rintro ⟨presentation, denotes⟩
    exact denotes.finiteSuccessfulObservation Actions
  · intro finite
    exact ⟨soundFinitePresentation Actions rules, finiteSuccessfulObservation_denotes Actions finite⟩

end Mettapedia.OSLF.DeterministicGSOS
