import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedProjection

/-!
# Request, premise and output locations on existing rule instances

Location tags are supplied by source operation metadata: request consumption,
protected premise reads, condition data and protected outputs may occupy
different physical spaces. Projection reconstructs every original field.

Equality asks retain their payload meaning. No claim projects absence/count
observations away from their physical regions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedRequest

universe uT uS uN uO
variable {T : Type uT} {S : Type uS} {N : Type uN} {O : Type uO}

def lift (requests premises conditions outputs : N) (source : RuleInstance T) : RuleInstance (N × T) where
  take := source.take.map (requests, ·)
  read := source.read.map (premises, ·)
  tell := source.tell.map fun pair => ((conditions, pair.1), (conditions, pair.2))
  checks := source.checks.map (Check.map (conditions, ·))
  produce := source.produce.map (outputs, ·)

theorem projection (requests premises conditions outputs : N) (source : RuleInstance T) :
    LocatedProjection.rule (lift requests premises conditions outputs source) = source := by
  have restore : ∀ check : Check T, Check.map Prod.snd (Check.map (conditions, ·) check) = check := by
    intro check
    cases check <;> rfl
  cases source
  simp [lift, LocatedProjection.rule, RuleInstance.map, List.map_map, Function.comp_def, restore]

def EqualityChecks (source : RuleInstance T) : Prop :=
  ∀ check ∈ source.checks, ∃ left right, check = .equal left right

theorem equality_checks (requests premises conditions outputs : N) {source : RuleInstance T}
    (equalities : EqualityChecks source) :
    LocatedProjection.EqualityChecks (lift requests premises conditions outputs source) := by
  intro check member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨left, right, rfl⟩ := equalities original present
  exact ⟨(conditions, left), (conditions, right), rfl⟩

section Selections

variable [DecidableEq O]

theorem take_space (base : SubstitutionAction T S) (location : O → N) (payload : O → T)
    (requests premises conditions outputs : N) {source : RuleInstance T}
    {before : Configuration (N × T) O} {picked : Selection O}
    (qualified : picked.Valid (LocatedSubstitution.action base) (fun occurrence => (location occurrence, payload occurrence))
      (lift requests premises conditions outputs source) before) :
    List.Forall₂ (fun _ occurrence => requests = location occurrence) source.take picked.taken := by
  have places := LocatedSubstitution.take_locations base location payload qualified
  exact List.forall₂_map_left_iff.mp places

theorem read_space (base : SubstitutionAction T S) (location : O → N) (payload : O → T)
    (requests premises conditions outputs : N) {source : RuleInstance T}
    {before : Configuration (N × T) O} {picked : Selection O}
    (qualified : picked.Valid (LocatedSubstitution.action base) (fun occurrence => (location occurrence, payload occurrence))
      (lift requests premises conditions outputs source) before) :
    ∀ occurrence ∈ picked.read, location occurrence = premises := by
  apply LocatedSubstitution.declared_read_space base location payload qualified premises
  intro expected member
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
  rfl

theorem output_space (base : SubstitutionAction T S) (location : O → N) (payload : O → T)
    (requests premises conditions outputs : N) {source : RuleInstance T}
    {before : Configuration (N × T) O} {picked : Selection O}
    (qualified : picked.Valid (LocatedSubstitution.action base) (fun occurrence => (location occurrence, payload occurrence))
      (lift requests premises conditions outputs source) before) :
    ∀ occurrence ∈ picked.made, location occurrence = outputs := by
  apply LocatedSubstitution.declared_output_space base location payload qualified outputs
  intro expected member
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
  rfl

theorem project_valid (base : SubstitutionAction T S) (label : O → N × T)
    (requests premises conditions outputs : N) {source : RuleInstance T}
    {before : Configuration (N × T) O} {picked : Selection O}
    (equalities : EqualityChecks source)
    (qualified : picked.Valid (LocatedSubstitution.action base) label
      (lift requests premises conditions outputs source) before) :
    picked.Valid base (fun occurrence => (label occurrence).2) source (LocatedProjection.configuration before) := by
  have projected := LocatedProjection.valid base label (equality_checks requests premises conditions outputs equalities) qualified
  simpa only [projection] using projected

theorem project_models (base : SubstitutionAction T S) (label : O → N × T)
    (requests premises conditions outputs : N) {source : RuleInstance T}
    {before : Configuration (N × T) O} {picked : Selection O}
    (qualified : picked.Valid (LocatedSubstitution.action base) label
      (lift requests premises conditions outputs source) before)
    (assignment : S)
    (solved : (LocatedSubstitution.action base).Models assignment
      (picked.problem label (lift requests premises conditions outputs source) before)) :
    base.Models assignment (picked.problem (fun occurrence => (label occurrence).2) source
      (LocatedProjection.configuration before)) := by
  have projected := (LocatedProjection.models_iff base qualified.consistent assignment).mp solved
  rw [LocatedProjection.problem, projection] at projected
  exact projected

end Selections

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedRequest
