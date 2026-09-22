import Mettapedia.GSLT.LanguageDef.MatchDecisionContract

/-!
An observed expression arity does not determine its head identity. Lift a
concrete candidate policy over the remaining identity completions. This models
the C selector's policy adapter; it does not verify the C implementation.
-/

namespace Mettapedia.GSLT.LanguageDef.MatchDecisionPartialIdentity

inductive Outcome where
  | fallback
  | keep
  | refute
  deriving DecidableEq

/-- Uncertainty retains a candidate unless both completions refute it. -/
def joinOutcome : Outcome → Outcome → Outcome
  | .fallback, _ | _, .fallback => .fallback
  | .keep, _ | _, .keep => .keep
  | .refute, .refute => .refute

theorem joinOutcome_refute_iff (left right : Outcome) :
    joinOutcome left right = .refute ↔ left = .refute ∧ right = .refute := by
  cases left <;> cases right <;> simp [joinOutcome]

theorem joinOutcome_assoc (a b c : Outcome) :
    joinOutcome (joinOutcome a b) c = joinOutcome a (joinOutcome b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem joinOutcome_comm (a b : Outcome) : joinOutcome a b = joinOutcome b a := by
  cases a <;> cases b <;> rfl

/-- `none` admits either equality result; a known observation admits one. -/
def Completes (observation : Option Bool) (identity : Bool) : Prop :=
  observation = none ∨ observation = some identity

def liftPolicy (policy : Bool → Outcome) : Option Bool → Outcome
  | none => joinOutcome (policy false) (policy true)
  | some identity => policy identity

theorem liftPolicy_refute_iff (policy : Bool → Outcome) (observation : Option Bool) :
    liftPolicy policy observation = .refute ↔
      ∀ identity, Completes observation identity → policy identity = .refute := by
  cases observation with
  | none =>
    simp only [liftPolicy, joinOutcome_refute_iff, Completes, true_or,
      forall_const]
    constructor
    · rintro ⟨hf, ht⟩ identity
      cases identity <;> assumption
    · intro h
      exact ⟨h false, h true⟩
  | some observed =>
    simp [liftPolicy, Completes]

/-- A realizable retained candidate cannot be lost by forgetting identity. -/
theorem liftPolicy_preserves_completion (policy : Bool → Outcome)
    (observation : Option Bool) (identity : Bool)
    (completion : Completes observation identity)
    (retained : policy identity ≠ .refute) :
    liftPolicy policy observation ≠ .refute := by
  intro refuted
  exact retained ((liftPolicy_refute_iff policy observation).mp refuted identity completion)

/-- Known shape incompatibility still refutes when identity is unavailable. -/
example : liftPolicy (fun _ => .refute) none = .refute := rfl

/-- Unknown identity is not the negative identity observation. -/
example : liftPolicy (fun equal => if equal then .keep else .refute) none = .keep := rfl

example : liftPolicy (fun equal => if equal then .keep else .refute) (some false) =
    .refute := rfl

end Mettapedia.GSLT.LanguageDef.MatchDecisionPartialIdentity
