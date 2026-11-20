import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationCandidateModels

/-!
# Admission is derived for every compatible application

Premise readings supply well-formed captured interfaces and an information
model. The namespace theorem supplies actual joint freshness. Only the fresh
output occurrence remains a resource requirement; no solver verdict, admission
predicate or completeness conclusion is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSyntax
open MeTTaCalculus.OccurrenceCommits (Enabled)

universe uOcc
variable {O : Type uOcc}

theorem candidate_shapes (judgmentTag arrowTag : Nat) (s : Store O) (major minor made : O)
    (majorWellFormed : (s.label major).WellFormed) (minorWellFormed : (s.label minor).WellFormed) :
    (candidate judgmentTag arrowTag (sourceBound s) s major minor made).Shapes X := by
  refine ⟨candidate_fresh judgmentTag arrowTag s major minor made,
    List.nodup_nil, List.nodup_singleton made, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro selected inside
    rw [candidate_uses] at inside
    rcases List.mem_cons.mp inside with rfl | tail
    · exact majorWellFormed
    · obtain rfl := List.mem_singleton.mp tail
      exact minorWellFormed
  · intro output inside
    cases inside

variable [DecidableEq O]

theorem candidate_enabled (judgmentTag arrowTag : Nat) (s : Store O) (major minor made : O)
    (majorPresent : major ∈ s.present) (minorPresent : minor ∈ s.present) (madeFresh : made ∉ s.present) :
    Enabled (fun _ : O => ()) s.present
      ((candidate judgmentTag arrowTag (sourceBound s) s major minor made).selection.commit (T := Unit)) := by
  refine ⟨Finset.empty_subset _, ?_, Finset.disjoint_empty_left _, ?_, ?_⟩
  · intro o inside
    change o ∈ ([major, minor] : List O).toFinset at inside
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl
    · exact majorPresent
    · exact minorPresent
  · change Disjoint ({made} : Finset O) s.present
    apply Finset.disjoint_left.mpr
    intro o fresh present
    have same := Finset.mem_singleton.mp fresh
    exact madeFresh (same ▸ present)
  · intro query inside
    cases inside

theorem candidate_admitted (judgmentTag arrowTag : Nat) (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge)
    (major minor made : O) (majorPresent : major ∈ s.present) (minorPresent : minor ∈ s.present)
    (madeFresh : made ∉ s.present) (function argument domain codomain : Tm)
    (majorReading : (s.label major).ReadsAt X (b := PUnit.unit) caller
      (judgment judgmentTag function (arrow arrowTag domain codomain)))
    (minorReading : (s.label minor).ReadsAt X (b := PUnit.unit) caller
      (judgment judgmentTag argument domain)) :
    (candidate judgmentTag arrowTag (sourceBound s) s major minor made).Admits X := by
  obtain ⟨assignment, solved, _, _⟩ := candidate_model judgmentTag arrowTag s caller known
    major minor made majorPresent minorPresent function argument domain codomain majorReading minorReading
  refine ⟨candidate_shapes judgmentTag arrowTag s major minor made
      (reading_wellFormed _ caller _ majorReading) (reading_wellFormed _ caller _ minorReading),
    candidate_enabled judgmentTag arrowTag s major minor made majorPresent minorPresent madeFresh,
    ⟨PUnit.unit, assignment, solved⟩, ?_⟩
  intro b model _
  constructor
  · intro check inside
    cases inside
  · intro query inside
    cases inside

#print axioms candidate_shapes
#print axioms candidate_enabled
#print axioms candidate_admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
