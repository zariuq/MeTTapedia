import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPublicationScope

/-!
# Scope coverage travels with conditional stored values

Latent equations are roots of the same stored binding unit as its value.
Opening a selected row allocates their private names at that row's actual
port scope. Publication preserves the old scopes, the new activation scopes
and the returned declarations without requiring the solver queue to finish.

These finite support laws concern scope formation. They do not infer a
source-language ownership policy or authority from physical presence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalScopes

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ContextualScopeSupport ContextualConditionalRows ContextualConditionalExecution

variable {S : Signature} {V W Local Added Shared O : Type}
    {source : V → MetaArity S} {next : W → MetaArity S}
    (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

def ConditionsCovered (scopes : V → Finset Nat) (occupied : Finset Nat)
    (problem : ContextualResidual.Problem source) : Prop :=
  ∀ equation ∈ problem, Covered scopes occupied equation.1.2.2 ∧ Covered scopes occupied equation.2.2.2

theorem ConditionsCovered.mono {scopes : V → Finset Nat} {first second : Finset Nat}
    {problem : ContextualResidual.Problem source} (covered : ConditionsCovered scopes first problem)
    (subset : first ⊆ second) : ConditionsCovered scopes second problem :=
  fun equation member => ⟨(covered equation member).1.mono subset, (covered equation member).2.mono subset⟩

theorem conditions_append (scopes : V → Finset Nat) (occupied : Finset Nat)
    (first second : ContextualResidual.Problem source) :
    ConditionsCovered scopes occupied (first ++ second) ↔
      ConditionsCovered scopes occupied first ∧ ConditionsCovered scopes occupied second := by
  simp only [ConditionsCovered, List.forall_mem_append]

theorem conditions_map (inScopes : V → Finset Nat) (outScopes : W → Finset Nat) (occupied : Finset Nat)
    (assignment : Assignment source next) (respects : Respects inScopes outScopes assignment)
    {problem : ContextualResidual.Problem source} (covered : ConditionsCovered inScopes occupied problem) :
    ConditionsCovered outScopes occupied (ContextualResidual.mapProblem assignment problem) := by
  intro equation member
  obtain ⟨⟨⟨leftContext, leftSort, left⟩, ⟨rightContext, rightSort, right⟩⟩, present, rfl⟩ := List.mem_map.mp member
  exact ⟨covered_instantiate_of_respects _ _ _ assignment respects (covered _ present).1,
    covered_instantiate_of_respects _ _ _ assignment respects (covered _ present).2⟩

theorem conditions_observe_iff (scopes : V → Finset Nat) (occupied : Finset Nat)
    {Γ : Ctx S} {sort : S.Srt} (problem : EquationStore (Term (signature S source) Γ sort)) :
    ConditionsCovered scopes occupied (ContextualResidual.observeProblem problem) ↔
      ContextualWorldScopeLedger.equationScopes scopes problem ⊆ occupied := by
  rw [ContextualWorldScopeLedger.equationScopes_subset_iff]
  constructor
  · intro covered equation member
    exact covered (observe equation.1, observe equation.2) (List.mem_map.mpr ⟨equation, member, rfl⟩)
  · intro covered equation member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact covered original present

def RowCovered (scopes : Shared → Finset Nat) (occupied : Finset Nat)
    {Γ : Ctx S} {sort : S.Srt} (row : Row locals captures Γ sort) : Prop :=
  ContextualScopeSupport.row locals captures scopes row.value ⊆ occupied ∧
    ConditionsCovered (privateScopes (Local := Local) scopes) occupied row.obligations

theorem RowCovered.mono {scopes : Shared → Finset Nat} {first second : Finset Nat}
    {Γ : Ctx S} {sort : S.Srt} {row : Row locals captures Γ sort}
    (covered : RowCovered locals captures scopes first row) (subset : first ⊆ second) :
    RowCovered locals captures scopes second row :=
  ⟨Finset.Subset.trans covered.1 subset, covered.2.mono subset⟩

theorem row_ofStored (scopes : Shared → Finset Nat) (occupied : Finset Nat)
    {Γ : Ctx S} {sort : S.Srt} (row : ContextualStoredRows.Row locals captures Γ sort)
    (covered : ContextualScopeSupport.row locals captures scopes row ⊆ occupied) :
    RowCovered locals captures scopes occupied (ofStored locals captures row) :=
  ⟨covered, by intro equation member; cases member⟩

theorem row_map (inScopes : Shared → Finset Nat) (outScopes : W → Finset Nat) (occupied : Finset Nat)
    (assignment : Assignment captures next) (respects : Respects inScopes outScopes assignment)
    {Γ : Ctx S} {sort : S.Srt} {row : Row locals captures Γ sort}
    (covered : RowCovered locals captures inScopes occupied row) :
    RowCovered locals next outScopes occupied (row.map locals captures assignment) := by
  refine ⟨ContextualScopeSupport.row_map locals inScopes outScopes assignment respects row.value covered.1, ?_⟩
  exact conditions_map _ _ _ _ (respects_liftCaptures locals inScopes outScopes assignment respects) covered.2

theorem opened_conditions (scopes : Shared → Finset Nat) (occupied : Finset Nat) (scope : Nat)
    (allocated : scope ∈ occupied) {Γ : Ctx S} {sort : S.Srt} {row : Row locals captures Γ sort}
    (covered : RowCovered locals captures scopes occupied row) :
    ConditionsCovered (activeScopes (Local := Local) scopes) occupied (row.obligationsAt locals captures scope) := by
  intro equation member
  obtain ⟨⟨⟨leftContext, leftSort, left⟩, ⟨rightContext, rightSort, right⟩⟩, present, rfl⟩ := List.mem_map.mp member
  exact ⟨covered_termAt locals captures scopes allocated (covered.2 _ present).1,
    covered_termAt locals captures scopes allocated (covered.2 _ present).2⟩

theorem row_extendPrivate (added : Added → MetaArity S) (scopes : Shared → Finset Nat) (occupied : Finset Nat)
    {Γ : Ctx S} {sort : S.Srt} {row : Row locals captures Γ sort}
    (covered : RowCovered locals captures scopes occupied row) :
    RowCovered (ContextualPublication.privateFamily locals added) captures scopes occupied
      (ContextualConditionalPublication.extendPrivate locals added captures row) := by
  refine ⟨ContextualPublication.row_extendPrivate_covered locals added captures scopes row.value covered.1, ?_⟩
  exact conditions_map _ _ _ _ (ContextualPublication.includePrivate_respects locals added captures scopes) covered.2

theorem row_ordinary (added : Added → MetaArity S) (scopes : Shared → Finset Nat)
    {Γ : Ctx S} {sort : S.Srt} (answer : ContextualConditionalAnswers.Answer added Γ sort) :
    RowCovered (ContextualPublication.privateFamily locals added) captures scopes ∅
      (ContextualConditionalPublication.ordinary locals added captures answer) := by
  refine ⟨ContextualPublication.ordinary_covered locals added captures scopes answer.value, ?_⟩
  intro equation member
  obtain ⟨⟨⟨leftContext, leftSort, left⟩, ⟨rightContext, rightSort, right⟩⟩, present, rfl⟩ := List.mem_map.mp member
  have images : ∀ name,
      Covered (privateScopes (Local := Local ⊕ Added) scopes) ∅
        ((Assignment.compose (ContextualStoredRows.privateSource (ContextualPublication.privateFamily locals added) captures)
          (ContextualPublication.newPrivate locals added)) name) := by
    intro name
    change term (privateScopes scopes)
      (instantiate (ContextualStoredRows.privateSource (ContextualPublication.privateFamily locals added) captures)
        (generator (ContextualPublication.privateFamily locals added) (.inr name))) ⊆ ∅
    rw [instantiate_generator]
    change term (privateScopes scopes)
      (generator (ContextualSelectionViews.source (ContextualPublication.privateFamily locals added) captures)
        (.inl (.inr name))) ⊆ ∅
    rw [term_generator]
    exact Finset.Subset.refl _
  exact ⟨covered_instantiate _ _ _ left (fun name _ => images name),
    covered_instantiate _ _ _ right (fun name _ => images name)⟩

structure Formed {Γ : Ctx S} {sort : S.Srt} (before : State locals O Γ sort)
    (scopes : before.Names → Finset Nat) : Prop where
  equations : ConditionsCovered scopes before.occupied before.equations
  rows : ∀ occurrence ∈ before.present, RowCovered locals before.declarations scopes before.occupied (before.rows occurrence)

/-- Reserving additional scopes retains coverage of all existing values
and latent equations; it does not reclassify captured names as fresh. -/
theorem Formed.mono {Γ : Ctx S} {sort : S.Srt} {before : State locals O Γ sort}
    {scopes : before.Names → Finset Nat} (formed : Formed locals before scopes)
    (occupied : Finset Nat) (retained : before.occupied ⊆ occupied) :
    Formed locals {before with occupied := occupied} scopes :=
  ⟨formed.equations.mono retained,
    fun occurrence member => (formed.rows occurrence member).mono locals before.declarations retained⟩

theorem of_endpoint_formed {Γ : Ctx S} {sort : S.Srt} (before : ContextualExecution.Endpoint locals O Γ sort) :
    Formed locals (ofEndpoint locals before) before.scopes := by
  refine ⟨(conditions_observe_iff _ _ _).mpr before.covered.equations, ?_⟩
  intro occurrence present
  exact row_ofStored locals before.declarations before.scopes before.occupied _ (before.covered.rows occurrence present)

def valueInventory {Γ : Ctx S} {sort : S.Srt} (before : State locals O Γ sort) :
    ContextualWorldScopeLedger.Inventory locals before.declarations (O := O) Γ sort :=
  ⟨⟨[], before.present⟩, (fun occurrence => (before.rows occurrence).value), [], []⟩

theorem value_inventory_covered {Γ : Ctx S} {sort : S.Srt} {before : State locals O Γ sort}
    {scopes : before.Names → Finset Nat} (formed : Formed locals before scopes) :
    ContextualWorldScopeLedger.CoveredWorld locals before.declarations scopes before.occupied
      (valueInventory locals before) := by
  refine ⟨by simp [valueInventory, ContextualWorldScopeLedger.equationScopes, names], ?_,
    by simp [valueInventory, observations, names], by simp [valueInventory, observations, names]⟩
  intro occurrence present
  exact (formed.rows occurrence present).1

section Execution

variable [DecidableEq O] {Γ : Ctx S} {sort : S.Srt} {before : State locals O Γ sort}
    {scopes : before.Names → Finset Nat}
    {rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals before.declarations)) Γ sort)}
    {selection : Selection O}
    {outputs : O → Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort}

theorem admitted_enabled (admitted : Admitted locals before rule selection outputs) :
    Enabled outputs before.present
      (selection.commit (T := Term (signature S (ContextualActivatedStep.target locals before.declarations)) Γ sort)) :=
  ⟨admitted.taken_present, admitted.read_present, admitted.apart, admitted.fresh,
    by intro query member; cases member⟩

theorem information_covered (formed : Formed locals before scopes)
    (ruleCovered : ContextualWorldScopeLedger.RuleCovered (privateScopes (Local := Local) scopes) before.occupied rule)
    (admitted : Admitted locals before rule selection outputs) :
    ConditionsCovered (activeScopes (Local := Local) scopes) (ContextualActivationScopes.after before.occupied selection)
      (information locals before.declarations before.occupied selection rule before.rows before.equations) := by
  have oldSubset := ContextualActivationScopes.old_scopes_retained before.occupied selection
  have values := ContextualWorldScopeLedger.problem_covered locals before.declarations scopes before.occupied selection rule
    (valueInventory locals before) outputs (value_inventory_covered locals formed) ruleCovered (admitted_enabled locals admitted)
  apply (conditions_append _ _ _ _).mpr
  refine ⟨(conditions_append _ _ _ _).mpr ⟨?_, ?_⟩, ?_⟩
  · exact conditions_map _ _ _ _ (respects_capturedTarget locals before.declarations scopes) (formed.equations.mono oldSubset)
  · apply (conditions_observe_iff _ _ _).mpr
    apply (ContextualWorldScopeLedger.equationScopes_subset_iff _ _ _).mpr
    intro equation member
    apply (ContextualWorldScopeLedger.equationScopes_subset_iff _ _ _).mp values equation
    rw [ContextualActivatedStep.problem_eq_frame_append]
    exact List.mem_append_right _ member
  · apply (conditions_append _ _ _ _).mpr
    constructor
    · intro equation member
      obtain ⟨rowProblem, selected, inside⟩ := List.mem_flatten.mp member
      obtain ⟨port, rfl⟩ := List.mem_ofFn.mp selected
      exact opened_conditions locals before.declarations scopes _ _
        (ContextualActivationScopes.allocated_scopes_retained before.occupied selection
          (ContextualActivationScopes.at_mem_reserved before.occupied selection _))
        ((formed.rows _ (admitted.taken_present (List.mem_toFinset.mpr (selection.taken.get_mem port)))).mono
          locals before.declarations oldSubset) equation inside
    · intro equation member
      obtain ⟨rowProblem, selected, inside⟩ := List.mem_flatten.mp member
      obtain ⟨port, rfl⟩ := List.mem_ofFn.mp selected
      exact opened_conditions locals before.declarations scopes _ _
        (ContextualActivationScopes.allocated_scopes_retained before.occupied selection
          (ContextualActivationScopes.at_mem_reserved before.occupied selection _))
        ((formed.rows _ (admitted.read_present (List.mem_toFinset.mpr (selection.read.get_mem port)))).mono
          locals before.declarations oldSubset) equation inside

end Execution

section Publication

variable [DecidableEq Local] [DecidableEq O] [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    {Γ : Ctx S} {sort : S.Srt} {before : State locals O Γ sort}

def targetScopes (firing : Firing locals before) (scopes : before.Names → Finset Nat) :
    firing.target.Names → Finset Nat :=
  ContextualFreshFrameScopeLedger.frameScopes (activeScopes scopes)
    (ContextualFreshFrameScopeLedger.helperScope (ContextualActivationScopes.after before.occupied firing.selection))

/-- An actual partial publication retains coverage of every present value
and every equation, including the conditions private to a reusable row. -/
theorem firing_preserves_formation (firing : Firing locals before) (scopes : before.Names → Finset Nat)
    (formed : Formed locals before scopes)
    (ruleCovered : ContextualWorldScopeLedger.RuleCovered (privateScopes (Local := Local) scopes)
      before.occupied firing.rule) :
    Formed (ContextualPublication.privateFamily locals firing.update.declaration) firing.target
      (targetScopes locals firing scopes) := by
  have oldSubset := ContextualActivationScopes.old_scopes_retained before.occupied firing.selection
  have extraSubset := ContextualFreshFrameScopeLedger.old_scopes_retained
    (ContextualActivationScopes.after before.occupied firing.selection)
  have inclusion := ContextualFreshFrameScopeLedger.includeSource_respects firing.update (activeScopes scopes)
    (ContextualFreshFrameScopeLedger.helperScope (ContextualActivationScopes.after before.occupied firing.selection))
  have captureInclusion := respects_capturedTarget locals before.declarations scopes
  have composed : Respects scopes (targetScopes locals firing scopes)
      (Assignment.compose (ContextualComputedFreshFrame.includeSource firing.update)
        (ContextualSelectionViews.capturedTarget locals before.declarations)) := by
    intro name
    exact covered_instantiate_of_respects _ _ _ _ inclusion (captureInclusion name)
  refine ⟨conditions_map _ _ _ _ inclusion
    ((information_covered locals formed ruleCovered firing.admitted).mono extraSubset), ?_⟩
  intro occurrence present
  by_cases made : occurrence ∈ firing.selection.made
  · by_cases reusable : firing.reusable occurrence = true
    · change RowCovered _ _ _ _ (if _ then (if _ then _ else _) else _)
      rw [if_pos made, if_pos reusable]
      exact (row_ordinary locals firing.target.declarations firing.update.declaration
        (targetScopes locals firing scopes) (ContextualConditionalAnswers.ofUpdate firing.update (firing.outputs occurrence))).mono
          _ _ (Finset.empty_subset _)
    · have isShared : firing.reusable occurrence = false := Bool.eq_false_iff.mpr reusable
      rw [firing.shared_row occurrence made isShared]
      apply row_ofStored
      apply row_shared
      have ruleSafe := ContextualWorldScopeLedger.prepared_rule_covered locals before.declarations scopes
        before.occupied firing.selection firing.rule (fun index => (before.rows index).value) ruleCovered
      have outputSafe : Covered (activeScopes (Local := Local) scopes)
          (ContextualActivationScopes.after before.occupied firing.selection) (firing.outputs occurrence) := by
        apply ruleSafe.produce
        rw [← firing.admitted.outputs]
        exact List.mem_map.mpr ⟨occurrence, made, rfl⟩
      exact covered_instantiate_of_respects _ _ _ _ inclusion (outputSafe.mono extraSubset)
  · have old : occurrence ∈ before.present := by
      change occurrence ∈ fire before.present (firing.selection.commit (T := Unit)) at present
      rcases Finset.mem_union.mp present with retained | added
      · exact (Finset.mem_sdiff.mp retained).1
      · exact False.elim (made (List.mem_toFinset.mp added))
    change RowCovered _ _ _ _ (if _ then _ else _)
    rw [if_neg made]
    apply row_extendPrivate
    exact row_map locals before.declarations scopes (targetScopes locals firing scopes) _ _ composed
      ((formed.rows occurrence old).mono locals before.declarations (Finset.Subset.trans oldSubset extraSubset))

end Publication

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalScopes
