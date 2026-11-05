import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardSemantics

/-!
# Nonbinding guards account for each row's latent equations

Presence, absence and counts use conditional matching, rather than matching
the displayed value while ignoring its obligations. Admission asks quantify
over all future solutions at their original joint information cut.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalGuards

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows

variable {S : Signature} {Local Shared Next Later O : Type}
    (locals : Local → MetaArity S) {captures : Shared → MetaArity S}
    {next : Next → MetaArity S} {later : Later → MetaArity S}

noncomputable def region (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → Row locals captures Γ sort) (world : Finset O)
    (pattern : Term (signature S captures) Γ sort) : Finset O := by
  classical
  exact world.filter fun occurrence => Matches locals captures candidate (instantiate candidate pattern) (rows occurrence)

def Holds (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → Row locals captures Γ sort) (world : Finset O) : Check (Term (signature S captures) Γ sort) → Prop
  | .equal first second => instantiate candidate first = instantiate candidate second
  | .absent pattern => ∀ occurrence ∈ world, ¬ Matches locals captures candidate (instantiate candidate pattern) (rows occurrence)
  | .count pattern cardinality => (region locals candidate rows world pattern).card = cardinality

theorem mem_region (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → Row locals captures Γ sort) (world : Finset O)
    (pattern : Term (signature S captures) Γ sort) (occurrence : O) :
    occurrence ∈ region locals candidate rows world pattern ↔ occurrence ∈ world ∧
      Matches locals captures candidate (instantiate candidate pattern) (rows occurrence) := by
  classical
  exact Finset.mem_filter

theorem region_ofStored (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (pattern : Term (signature S captures) Γ sort) :
    region locals candidate (fun occurrence => ofStored locals captures (rows occurrence)) world pattern =
      ContextualGuardSemantics.region locals candidate rows world pattern := by
  classical
  ext occurrence
  simp only [mem_region, ContextualGuardSemantics.mem_region, ofStored_matches_iff]

theorem holds_ofStored (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (check : Check (Term (signature S captures) Γ sort)) :
    Holds locals candidate (fun occurrence => ofStored locals captures (rows occurrence)) world check ↔
      ContextualGuardSemantics.Holds locals candidate rows world check := by
  cases check with
  | equal _ _ => rfl
  | absent pattern => simp only [Holds, ContextualGuardSemantics.Holds, ofStored_matches_iff]
  | count pattern cardinality => rw [Holds, ContextualGuardSemantics.Holds, region_ofStored]

theorem region_transport (change : Assignment captures later) (candidate : Assignment later next)
    {Γ : Ctx S} {sort : S.Srt} (rows : O → Row locals captures Γ sort) (world : Finset O)
    (pattern : Term (signature S captures) Γ sort) :
    region locals candidate (fun occurrence => (rows occurrence).map locals captures change) world
      (instantiate change pattern) = region locals (Assignment.compose candidate change) rows world pattern := by
  classical
  ext occurrence
  simp only [mem_region, matches_map_iff, Assignment.instantiate_compose]

theorem holds_transport (change : Assignment captures later) (candidate : Assignment later next)
    {Γ : Ctx S} {sort : S.Srt} (rows : O → Row locals captures Γ sort) (world : Finset O)
    (check : Check (Term (signature S captures) Γ sort)) :
    Holds locals candidate (fun occurrence => (rows occurrence).map locals captures change) world
      (check.map (instantiate change)) ↔ Holds locals (Assignment.compose candidate change) rows world check := by
  cases check with
  | equal _ _ => simp only [Check.map, Holds, Assignment.instantiate_compose]
  | absent _ => simp only [Check.map, Holds, matches_map_iff, Assignment.instantiate_compose]
  | count pattern cardinality => rw [Check.map, Holds, Holds, region_transport]

def Ask {Γ : Ctx S} {sort : S.Srt} (problem : ContextualResidual.Problem captures)
    (rows : O → Row locals captures Γ sort) (world : Finset O) (check : Check (Term (signature S captures) Γ sort)) : Prop :=
  ∀ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment captures future),
    ContextualResidual.Models candidate problem → Holds locals candidate rows world check

theorem ask_transport {Γ : Ctx S} {sort : S.Srt} (change : Assignment captures later)
    {problem : ContextualResidual.Problem captures} {rows : O → Row locals captures Γ sort} {world : Finset O}
    {check : Check (Term (signature S captures) Γ sort)} (asked : Ask locals problem rows world check) :
    Ask locals (ContextualResidual.mapProblem change problem)
      (fun occurrence => (rows occurrence).map locals captures change) world (check.map (instantiate change)) := by
  intro Future future candidate model
  exact (holds_transport locals change candidate rows world check).mpr
    (asked Future future (Assignment.compose candidate change) ((ContextualResidual.models_mapProblem _ _ _).mp model))

theorem ask_ofStored {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (check : Check (Term (signature S captures) Γ sort)) :
    Ask locals (ContextualResidual.observeProblem problem) (fun occurrence => ofStored locals captures (rows occurrence)) world check ↔
      ContextualGuardSemantics.Ask locals problem rows world check := by
  constructor <;> intro asked Future future candidate model
  · exact (holds_ofStored locals candidate rows world check).mp
      (asked Future future candidate ((ContextualResidual.models_observeProblem _ _).mpr model))
  · exact (holds_ofStored locals candidate rows world check).mpr
      (asked Future future candidate ((ContextualResidual.models_observeProblem _ _).mp model))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalGuards
