import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedSubstitution

/-!
# Projecting located ordinary firings with equality asks

Locations are rigid. Consistency of a located equation store therefore
establishes all its location equations, and projection preserves exactly its
payload models. Ordinary firings whose asks are equalities project with the
same physical selection and complete payload equation store.

Absence and count are deliberately outside this projection theorem: their
observed regions depend on physical locations. No such guard is discarded or
silently interpreted over a larger unlocated world.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedProjection

universe uT uS uN uO
variable {T : Type uT} {S : Type uS} {N : Type uN} {O : Type uO}

def equation (value : Equation (N × T)) : Equation T := (value.1.2, value.2.2)

def equations (store : EquationStore (N × T)) : EquationStore T := store.map equation

def configuration (state : Configuration (N × T) O) : Configuration T O := ⟨equations state.equations, state.present⟩

def rule (source : RuleInstance (N × T)) : RuleInstance T := source.map Prod.snd

theorem models_iff (base : SubstitutionAction T S) {store : EquationStore (N × T)}
    (consistent : (LocatedSubstitution.action base).Consistent store) (assignment : S) :
    (LocatedSubstitution.action base).Models assignment store ↔ base.Models assignment (equations store) := by
  constructor
  · intro solved value member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact (solved original present).2
  · intro solved
    obtain ⟨witness, locationEvidence⟩ := consistent
    intro value member
    exact ⟨(locationEvidence value member).1, solved (equation value) (List.mem_map.mpr ⟨value, member, rfl⟩)⟩

theorem consistent_projected (base : SubstitutionAction T S) {store : EquationStore (N × T)}
    (consistent : (LocatedSubstitution.action base).Consistent store) : base.Consistent (equations store) := by
  obtain ⟨assignment, solved⟩ := consistent
  exact ⟨assignment, (models_iff base ⟨assignment, solved⟩ assignment).mp solved⟩

section Selections

variable [DecidableEq O]

omit [DecidableEq O] in
theorem selected_equations (label : O → N × T) (patterns : List (N × T)) (picked : List O) :
    equations (Selection.equations label patterns picked) =
      Selection.equations (fun occurrence => (label occurrence).2) (patterns.map Prod.snd) picked := by
  simp only [equations, Selection.equations, List.map_zipWith, List.zipWith_map_left]
  rfl

omit [DecidableEq O] in
theorem problem (label : O → N × T) (source : RuleInstance (N × T)) (picked : Selection O)
    (before : Configuration (N × T) O) :
    equations (picked.problem label source before) =
      picked.problem (fun occurrence => (label occurrence).2) (rule source) (configuration before) := by
  simp only [Selection.problem, equations, List.map_append, rule, RuleInstance.map, configuration]
  change _ ++ equations (Selection.equations label source.take picked.taken) ++
    equations (Selection.equations label source.read picked.read) ++ _ = _
  rw [selected_equations, selected_equations]
  rfl

theorem result (label : O → N × T) (source : RuleInstance (N × T)) (picked : Selection O)
    (before : Configuration (N × T) O) :
    configuration (picked.result label source before) =
      picked.result (fun occurrence => (label occurrence).2) (rule source) (configuration before) := by
  apply congrArg₂ Configuration.mk
  · exact problem label source picked before
  · rfl

def EqualityChecks (source : RuleInstance (N × T)) : Prop :=
  ∀ check ∈ source.checks, ∃ left right, check = .equal left right

theorem valid (base : SubstitutionAction T S) (label : O → N × T)
    {source : RuleInstance (N × T)} {picked : Selection O} {before : Configuration (N × T) O}
    (equalities : EqualityChecks source)
    (qualified : picked.Valid (LocatedSubstitution.action base) label source before) :
    picked.Valid base (fun occurrence => (label occurrence).2) (rule source) (configuration before) := by
  refine ⟨qualified.take_distinct, qualified.output_distinct, ?_, ?_, ?_,
    ⟨qualified.occurrences.taken_subset, qualified.occurrences.kept_subset, qualified.occurrences.apart,
      qualified.occurrences.fresh, by simp [Selection.commit]⟩, ?_, ?_⟩
  · simpa [rule, RuleInstance.map] using qualified.take_length
  · simpa [rule, RuleInstance.map] using qualified.read_length
  · have shapes := congrArg (List.map Prod.snd) qualified.outputs
    simpa only [rule, RuleInstance.map, List.map_map, Function.comp_def] using shapes
  · rw [← problem]
    exact consistent_projected base qualified.consistent
  · intro check member assignment solved
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨left, right, rfl⟩ := equalities original present
    have locatedModels : (LocatedSubstitution.action base).Models assignment (picked.problem label source before) :=
      (models_iff base qualified.consistent assignment).mpr (by rwa [problem])
    exact (qualified.checks (.equal left right) present assignment locatedModels).2

theorem step (base : SubstitutionAction T S) (label : O → N × T)
    {source : RuleInstance (N × T)} {before after : Configuration (N × T) O}
    (equalities : EqualityChecks source)
    (stepped : Step (LocatedSubstitution.action base) label source before after) :
    Step base (fun occurrence => (label occurrence).2) (rule source) (configuration before) (configuration after) := by
  obtain ⟨picked, qualified, rfl⟩ := stepped
  exact ⟨picked, valid base label equalities qualified, result label source picked before⟩

end Selections

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedProjection
