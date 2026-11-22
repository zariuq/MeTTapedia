import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedRequest

/-!
# Reverse physical lifting of ordinary request firings

The payload firing supplies its own full consistency and equality asks.
Explicit metadata routes the actual selected take/read/output occurrences.
The existing physical locations and complete equation store are retained;
payload resemblance never supplies a location premise.

This converse is deliberately restricted to equality checks. Absence and
count need their own region-sensitive observation correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedRequestLifting

universe uT uS uN uO
variable {T : Type uT} {S : Type uS} {N : Type uN} {O : Type uO}

def Coherent (store : EquationStore (N × T)) : Prop :=
  ∀ equation ∈ store, equation.1.1 = equation.2.1

theorem models_iff (base : SubstitutionAction T S) {store : EquationStore (N × T)}
    (coherent : Coherent store) (assignment : S) :
    (LocatedSubstitution.action base).Models assignment store ↔
      base.Models assignment (LocatedProjection.equations store) := by
  constructor
  · intro solved equation member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact (solved original present).2
  · intro solved equation member
    exact ⟨coherent equation member,
      solved _ (List.mem_map.mpr ⟨equation, member, rfl⟩)⟩

theorem selected_coherent (location : O → N) (payload : O → T) (space : N)
    (patterns : List T) (selected : List O)
    (routed : ∀ occurrence ∈ selected, location occurrence = space) :
    Coherent (Selection.equations (fun occurrence => (location occurrence, payload occurrence))
      (patterns.map (space, ·)) selected) := by
  induction patterns generalizing selected with
  | nil => intro equation member; cases member
  | cons pattern patterns earlier =>
      cases selected with
      | nil => intro equation member; cases member
      | cons occurrence selected =>
          intro equation member
          have alternatives : equation = ((space, pattern), (location occurrence, payload occurrence)) ∨
              equation ∈ Selection.equations (fun next => (location next, payload next))
                (patterns.map (space, ·)) selected := by simpa [Selection.equations] using member
          rcases alternatives with rfl | member
          · exact (routed occurrence (by simp)).symm
          · exact earlier selected (fun next member => routed next (List.mem_cons_of_mem _ member)) equation member

variable [DecidableEq O]

omit [DecidableEq O] in
theorem problem_coherent (location : O → N) (payload : O → T)
    (requests premises conditions outputs : N) (rule : RuleInstance T)
    (picked : Selection O) (before : Configuration (N × T) O)
    (background : Coherent before.equations)
    (takes : ∀ occurrence ∈ picked.taken, location occurrence = requests)
    (reads : ∀ occurrence ∈ picked.read, location occurrence = premises) :
    Coherent (picked.problem (fun occurrence => (location occurrence, payload occurrence))
      (LocatedRequest.lift requests premises conditions outputs rule) before) := by
  intro equation member
  simp only [Selection.problem, LocatedRequest.lift, List.mem_append] at member
  rcases member with ((old | taken) | read) | told
  · exact background equation old
  · exact selected_coherent location payload requests rule.take picked.taken takes equation taken
  · exact selected_coherent location payload premises rule.read picked.read reads equation read
  · obtain ⟨original, _, rfl⟩ := List.mem_map.mp told
    rfl

theorem valid (base : SubstitutionAction T S) (location : O → N) (payload : O → T)
    (requests premises conditions outputs : N) {rule : RuleInstance T}
    {picked : Selection O} {before : Configuration (N × T) O}
    (equalities : LocatedRequest.EqualityChecks rule)
    (background : Coherent before.equations)
    (takes : ∀ occurrence ∈ picked.taken, location occurrence = requests)
    (reads : ∀ occurrence ∈ picked.read, location occurrence = premises)
    (makes : ∀ occurrence ∈ picked.made, location occurrence = outputs)
    (qualified : picked.Valid base payload rule (LocatedProjection.configuration before)) :
    picked.Valid (LocatedSubstitution.action base) (fun occurrence => (location occurrence, payload occurrence))
      (LocatedRequest.lift requests premises conditions outputs rule) before := by
  have projected : LocatedProjection.equations
      (picked.problem (fun occurrence => (location occurrence, payload occurrence))
        (LocatedRequest.lift requests premises conditions outputs rule) before) =
      picked.problem payload rule (LocatedProjection.configuration before) := by
    rw [LocatedProjection.problem, LocatedRequest.projection]
  have coherent := problem_coherent location payload requests premises conditions outputs rule picked before background takes reads
  refine ⟨qualified.take_distinct, qualified.output_distinct, ?_, ?_, ?_,
    ⟨qualified.occurrences.taken_subset, qualified.occurrences.kept_subset,
      qualified.occurrences.apart, qualified.occurrences.fresh, by simp [Selection.commit]⟩, ?_, ?_⟩
  · simpa [LocatedRequest.lift] using qualified.take_length
  · simpa [LocatedRequest.lift] using qualified.read_length
  · change picked.made.map (fun occurrence => (location occurrence, payload occurrence)) = rule.produce.map (outputs, ·)
    have same : picked.made.map (fun occurrence => (location occurrence, payload occurrence)) =
        (picked.made.map payload).map (outputs, ·) := by
      rw [List.map_map]
      exact List.map_congr_left (fun occurrence member => by simp [makes occurrence member])
    rw [same, qualified.outputs]
  · obtain ⟨assignment, solved⟩ := qualified.consistent
    refine ⟨assignment, (models_iff base coherent assignment).mpr ?_⟩
    rwa [projected]
  · intro check member assignment solved
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨left, right, rfl⟩ := equalities original present
    have rawModels : base.Models assignment (picked.problem payload rule (LocatedProjection.configuration before)) := by
      rw [← projected]
      exact (models_iff base coherent assignment).mp solved
    exact ⟨rfl, qualified.checks (.equal left right) present assignment rawModels⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedRequestLifting
