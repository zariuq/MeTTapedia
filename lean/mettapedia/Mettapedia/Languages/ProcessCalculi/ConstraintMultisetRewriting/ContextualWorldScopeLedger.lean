import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScopeSupport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedStep

/-!
# Occupied scopes cover the complete finite root inventory

The inventory retains shared rows, both sides of configuration equations,
heterogeneous continuation roots and stored template captures. Its footprint
is computed from actual binding-term support. Template locals contribute no
live scope until a selected use opens them.

An activation transports the old roots through the actual capture inclusion,
retains every activated rule position, and installs its computed rows and
equations. The reserved ledger covers that result. Schema publication adds
its actual capture footprint; it does not establish logical admission or
authority. Enumeration of a native engine's roots remains a refinement task.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldScopeLedger

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ContextualScopeSupport
open ContextualActivatedStep

universe u
variable {S : Signature} {Local Shared : Type} {O : Type u}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

def equationScopes {V : Type} {declaration : V → MetaArity S}
    (scopes : V → Finset Nat) {Γ : Ctx S} {sort : S.Srt}
    (equations : EquationStore (Term (signature S declaration) Γ sort)) : Finset Nat :=
  names (fun equation => term scopes equation.1 ∪ term scopes equation.2) equations

theorem equationScopes_subset_iff {V : Type} {declaration : V → MetaArity S}
    (scopes : V → Finset Nat) {Γ : Ctx S} {sort : S.Srt}
    (equations : EquationStore (Term (signature S declaration) Γ sort)) (occupied : Finset Nat) :
    equationScopes scopes equations ⊆ occupied ↔
      ∀ equation ∈ equations, Covered scopes occupied equation.1 ∧ Covered scopes occupied equation.2 := by
  simp only [equationScopes, names_subset_iff, Finset.union_subset_iff, Covered]

def checkTerms {T : Type} : Check T → List T
  | .equal left right => [left, right]
  | .absent pattern | .count pattern _ => [pattern]

def ruleTerms {T : Type} (rule : RuleInstance T) : List T :=
  rule.take ++ rule.read ++ rule.tell.flatMap (fun pair => [pair.1, pair.2]) ++
    rule.checks.flatMap checkTerms ++ rule.produce

theorem checkTerms_map {T U : Type} (function : T → U) (check : Check T) :
    checkTerms (check.map function) = (checkTerms check).map function := by
  cases check <;> rfl

theorem ruleTerms_map {T U : Type} (function : T → U) (rule : RuleInstance T) :
    ruleTerms (rule.map function) = (ruleTerms rule).map function := by
  simp only [ruleTerms, RuleInstance.map, List.map_append, List.map_flatMap,
    List.flatMap_map, checkTerms_map, List.map_cons, List.map_nil]

def ruleRoots {V : Type} {declaration : V → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S declaration) Γ sort)) : List (Observation S declaration) :=
  (ruleTerms rule).map observe

def RuleCovered {V : Type} {declaration : V → MetaArity S}
    (scopes : V → Finset Nat) (occupied : Finset Nat) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S declaration) Γ sort)) : Prop :=
  ∀ value ∈ ruleTerms rule, Covered scopes occupied value

theorem ruleRoots_covered {V : Type} {declaration : V → MetaArity S}
    {scopes : V → Finset Nat} {occupied : Finset Nat} {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S declaration) Γ sort)}
    (covered : RuleCovered scopes occupied rule) : observations scopes (ruleRoots rule) ⊆ occupied := by
  apply (observations_subset_iff _ _ _).mpr
  intro value member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact covered original present

theorem ruleRoots_covered_iff {V : Type} {declaration : V → MetaArity S}
    (scopes : V → Finset Nat) (occupied : Finset Nat) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S declaration) Γ sort)) :
    observations scopes (ruleRoots rule) ⊆ occupied ↔ RuleCovered scopes occupied rule := by
  constructor
  · intro covered value member
    exact (observations_subset_iff _ _ _).mp covered (observe value)
      (List.mem_map.mpr ⟨value, member, rfl⟩)
  · exact ruleRoots_covered

theorem RuleCovered.mono {V : Type} {declaration : V → MetaArity S}
    {scopes : V → Finset Nat} {first second : Finset Nat} {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S declaration) Γ sort)}
    (covered : RuleCovered scopes first rule) (subset : first ⊆ second) :
    RuleCovered scopes second rule := fun value member => (covered value member).mono subset

/-- Capture transport preserves coverage when each transported declaration
uses only its original scopes. The same law covers guards and outputs. -/
theorem RuleCovered.map {V W : Type} {source : V → MetaArity S} {target : W → MetaArity S}
    {inScopes : V → Finset Nat} {outScopes : W → Finset Nat} {occupied : Finset Nat}
    {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S source) Γ sort)}
    (covered : RuleCovered inScopes occupied rule) (assignment : Assignment source target)
    (respects : Respects inScopes outScopes assignment) :
    RuleCovered outScopes occupied (rule.map (instantiate assignment)) := by
  intro value member
  rw [ruleTerms_map] at member
  obtain ⟨original, selected, rfl⟩ := List.mem_map.mp member
  exact covered_instantiate_of_respects inScopes outScopes occupied assignment respects (covered original selected)

theorem RuleCovered.take {V : Type} {declaration : V → MetaArity S}
    {scopes : V → Finset Nat} {occupied : Finset Nat} {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S declaration) Γ sort)}
    (covered : RuleCovered scopes occupied rule) :
    ∀ value ∈ rule.take, Covered scopes occupied value := by
  intro value member
  apply covered value
  simp only [ruleTerms, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl member)))

theorem RuleCovered.read {V : Type} {declaration : V → MetaArity S}
    {scopes : V → Finset Nat} {occupied : Finset Nat} {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S declaration) Γ sort)}
    (covered : RuleCovered scopes occupied rule) :
    ∀ value ∈ rule.read, Covered scopes occupied value := by
  intro value member
  apply covered value
  simp only [ruleTerms, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr member)))

theorem RuleCovered.tell {V : Type} {declaration : V → MetaArity S}
    {scopes : V → Finset Nat} {occupied : Finset Nat} {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S declaration) Γ sort)}
    (covered : RuleCovered scopes occupied rule) : equationScopes scopes rule.tell ⊆ occupied := by
  apply (equationScopes_subset_iff _ _ _).mpr
  intro pair member
  have position : ∀ value ∈ [pair.1, pair.2], value ∈ ruleTerms rule := by
    intro value inside
    simp only [ruleTerms, List.mem_append]
    exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.mpr ⟨pair, member, inside⟩)))
  exact ⟨covered pair.1 (position _ (by simp)), covered pair.2 (position _ (by simp))⟩

theorem RuleCovered.produce {V : Type} {declaration : V → MetaArity S}
    {scopes : V → Finset Nat} {occupied : Finset Nat} {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S declaration) Γ sort)}
    (covered : RuleCovered scopes occupied rule) :
    ∀ value ∈ rule.produce, Covered scopes occupied value := by
  intro value member
  exact covered value (List.mem_append_right _ member)

structure Inventory (context : Ctx S) (sort : S.Srt) where
  configuration : Configuration (Term (signature S captures) context sort) O
  rows : O → ContextualStoredRows.Row locals captures context sort
  retained : List (Observation S captures)
  templates : List (Observation S (source locals captures))

def footprint [DecidableEq O] (scopes : Shared → Finset Nat) {Γ : Ctx S} {sort : S.Srt}
    (inventory : Inventory locals captures (O := O) Γ sort) : Finset Nat :=
  equationScopes scopes inventory.configuration.equations ∪
    inventory.configuration.present.biUnion (fun occurrence => row locals captures scopes (inventory.rows occurrence)) ∪
      observations scopes inventory.retained ∪ observations (privateScopes scopes) inventory.templates

structure CoveredWorld (scopes : Shared → Finset Nat) (occupied : Finset Nat)
    {Γ : Ctx S} {sort : S.Srt} (inventory : Inventory locals captures (O := O) Γ sort) : Prop where
  equations : equationScopes scopes inventory.configuration.equations ⊆ occupied
  rows : ∀ occurrence ∈ inventory.configuration.present,
    row locals captures scopes (inventory.rows occurrence) ⊆ occupied
  retained : observations scopes inventory.retained ⊆ occupied
  templates : observations (privateScopes scopes) inventory.templates ⊆ occupied

theorem coveredWorld_iff [DecidableEq O] (scopes : Shared → Finset Nat) (occupied : Finset Nat)
    {Γ : Ctx S} {sort : S.Srt} (inventory : Inventory locals captures (O := O) Γ sort) :
    CoveredWorld locals captures scopes occupied inventory ↔ footprint locals captures scopes inventory ⊆ occupied := by
  simp only [footprint, Finset.union_subset_iff, Finset.biUnion_subset_iff_forall_subset]
  constructor
  · intro covered
    exact ⟨⟨⟨covered.equations, covered.rows⟩, covered.retained⟩, covered.templates⟩
  · rintro ⟨⟨⟨equations, rows⟩, retained⟩, templates⟩
    exact ⟨equations, rows, retained, templates⟩

theorem rule_covered_from_templates (scopes : Shared → Finset Nat) {occupied : Finset Nat}
    {Γ : Ctx S} {sort : S.Srt} {inventory : Inventory locals captures (O := O) Γ sort}
    (covered : CoveredWorld locals captures scopes occupied inventory)
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (installed : ∀ root ∈ ruleRoots rule, root ∈ inventory.templates) :
    RuleCovered (privateScopes scopes) occupied rule := by
  intro value member
  exact (observations_subset_iff _ _ _).mp covered.templates (observe value)
    (installed _ (List.mem_map.mpr ⟨value, member, rfl⟩))

theorem CoveredWorld.mono {scopes : Shared → Finset Nat} {first second : Finset Nat}
    {Γ : Ctx S} {sort : S.Srt} {inventory : Inventory locals captures (O := O) Γ sort}
    (covered : CoveredWorld locals captures scopes first inventory) (subset : first ⊆ second) :
    CoveredWorld locals captures scopes second inventory := by
  exact ⟨Finset.Subset.trans covered.equations subset,
    fun occurrence member => Finset.Subset.trans (covered.rows occurrence member) subset,
    Finset.Subset.trans covered.retained subset, Finset.Subset.trans covered.templates subset⟩

def mapInventory {Next : Type} {next : Next → MetaArity S}
    (change : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (inventory : Inventory locals captures (O := O) Γ sort) : Inventory locals next (O := O) Γ sort where
  configuration := ⟨ContextualFrameUnifier.mapProblem change inventory.configuration.equations,
    inventory.configuration.present⟩
  rows occurrence := (inventory.rows occurrence).map locals change
  retained := inventory.retained.map (instantiateObservation change)
  templates := inventory.templates.map (instantiateObservation (ContextualStoredRows.liftCaptures locals change))

theorem mapInventory_covered {Next : Type} {next : Next → MetaArity S}
    (inScopes : Shared → Finset Nat) (outScopes : Next → Finset Nat) {occupied : Finset Nat}
    (change : Assignment captures next) (respects : Respects inScopes outScopes change)
    {Γ : Ctx S} {sort : S.Srt} (inventory : Inventory locals captures (O := O) Γ sort)
    (covered : CoveredWorld locals captures inScopes occupied inventory) :
    CoveredWorld locals next outScopes occupied (mapInventory locals captures change inventory) := by
  refine ⟨?_, ?_, observations_map _ _ _ _ respects _ covered.retained,
    observations_map _ _ _ _ (respects_liftCaptures locals _ _ change respects) _ covered.templates⟩
  · apply (equationScopes_subset_iff _ _ _).mpr
    intro pair member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    have both := (equationScopes_subset_iff _ _ _).mp covered.equations original present
    exact ⟨covered_instantiate_of_respects _ _ _ _ respects both.1,
      covered_instantiate_of_respects _ _ _ _ respects both.2⟩
  · intro occurrence member
    exact row_map locals _ _ _ respects _ (covered.rows occurrence member)

def afterInventory [DecidableEq O] (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (inventory : Inventory locals captures (O := O) Γ sort)
    (outputs : O → Term (signature S (target locals captures)) Γ sort) :
    Inventory locals (target locals captures) (O := O) Γ sort where
  configuration := result locals captures occupied selection rule inventory.rows inventory.configuration
  rows := resultRows locals captures selection outputs inventory.rows
  retained := inventory.retained.map (instantiateObservation (ContextualSelectionViews.capturedTarget locals captures)) ++
    ruleRoots (prepared locals captures occupied selection rule inventory.rows).rule
  templates := inventory.templates.map (instantiateObservation
    (ContextualStoredRows.liftCaptures locals (ContextualSelectionViews.capturedTarget locals captures)))

theorem prepared_rule_covered (scopes : Shared → Finset Nat) (occupied : Finset Nat)
    (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (covered : RuleCovered (privateScopes scopes) occupied rule) :
    RuleCovered (activeScopes scopes) (ContextualActivationScopes.after occupied selection)
      (prepared locals captures occupied selection rule rows).rule := by
  intro value member
  change value ∈ ruleTerms (rule.map (ContextualFreshening.termAt locals captures
    (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort selection)))) at member
  rw [ruleTerms_map] at member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact covered_termAt locals captures scopes
    (ContextualActivationScopes.allocated_scopes_retained occupied selection
      (ContextualActivationScopes.at_mem_reserved occupied selection (ContextualActivationScopes.rulePort selection)))
    ((covered original present).mono (ContextualActivationScopes.old_scopes_retained occupied selection))

theorem selected_view_covered (scopes : Shared → Finset Nat) (occupied : Finset Nat)
    (selection : Selection O) (port : ContextualActivationScopes.Port selection)
    {Γ : Ctx S} {sort : S.Srt} (value : ContextualStoredRows.Row locals captures Γ sort)
    (covered : row locals captures scopes value ⊆ occupied) :
    Covered (activeScopes scopes) (ContextualActivationScopes.after occupied selection)
      (ContextualStoredRows.viewAt locals captures (ContextualActivationScopes.scopeAt occupied port) value) := by
  rw [ContextualStoredRows.viewAt_eq_freshening]
  exact covered_termAt locals captures scopes
    (ContextualActivationScopes.allocated_scopes_retained occupied selection
      (ContextualActivationScopes.at_mem_reserved occupied selection port))
    (Covered.mono covered (ContextualActivationScopes.old_scopes_retained occupied selection))

theorem useEquations_covered {V : Type} {declaration : V → MetaArity S}
    (scopes : V → Finset Nat) (occupied : Finset Nat) {Γ : Ctx S} {sort : S.Srt}
    (patterns values : List (Term (signature S declaration) Γ sort))
    (patternCovered : ∀ value ∈ patterns, Covered scopes occupied value)
    (valueCovered : ∀ value ∈ values, Covered scopes occupied value) :
    equationScopes scopes (useEquations patterns values) ⊆ occupied := by
  induction patterns generalizing values with
  | nil => exact Finset.empty_subset _
  | cons pattern rest ih =>
      cases values with
      | nil => exact Finset.empty_subset _
      | cons value tail =>
          change (term scopes pattern ∪ term scopes value) ∪
            equationScopes scopes (useEquations rest tail) ⊆ occupied
          refine Finset.union_subset (Finset.union_subset
            (patternCovered pattern List.mem_cons_self) (valueCovered value List.mem_cons_self)) ?_
          exact ih tail
            (fun item member => patternCovered item (List.mem_cons_of_mem _ member))
            (fun item member => valueCovered item (List.mem_cons_of_mem _ member))

theorem problem_covered [DecidableEq O] (scopes : Shared → Finset Nat) (occupied : Finset Nat)
    (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (inventory : Inventory locals captures (O := O) Γ sort)
    (outputs : O → Term (signature S (target locals captures)) Γ sort)
    (worldCovered : CoveredWorld locals captures scopes occupied inventory)
    (ruleCovered : RuleCovered (privateScopes scopes) occupied rule)
    (enabled : Enabled outputs inventory.configuration.present
      (selection.commit (T := Term (signature S (target locals captures)) Γ sort))) :
    equationScopes (activeScopes scopes)
      (problem locals captures occupied selection rule inventory.rows inventory.configuration) ⊆
      ContextualActivationScopes.after occupied selection := by
  have oldSubset := ContextualActivationScopes.old_scopes_retained occupied selection
  have ruleSafe := prepared_rule_covered locals captures scopes occupied selection rule inventory.rows ruleCovered
  have oldSafe : equationScopes (activeScopes scopes) (frame locals captures inventory.configuration).equations ⊆
      ContextualActivationScopes.after occupied selection := by
    apply (equationScopes_subset_iff _ _ _).mpr
    intro pair member
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    have both := (equationScopes_subset_iff _ _ _).mp worldCovered.equations old present
    exact ⟨covered_instantiate_of_respects scopes _ _ _ (respects_capturedTarget locals captures scopes)
        (both.1.mono oldSubset),
      covered_instantiate_of_respects scopes _ _ _ (respects_capturedTarget locals captures scopes)
        (both.2.mono oldSubset)⟩
  have takeSafe : ∀ value ∈ List.ofFn (prepared locals captures occupied selection rule inventory.rows).taken,
      Covered (activeScopes scopes) (ContextualActivationScopes.after occupied selection) value := by
    intro value member
    obtain ⟨position, rfl⟩ := List.mem_ofFn.mp member
    rw [prepared_taken_view]
    exact selected_view_covered locals captures scopes occupied selection _ _
      (worldCovered.rows _ (enabled.taken_subset (by
        simpa only [Selection.commit, List.mem_toFinset] using selection.taken.get_mem position)))
  have readSafe : ∀ value ∈ List.ofFn (prepared locals captures occupied selection rule inventory.rows).read,
      Covered (activeScopes scopes) (ContextualActivationScopes.after occupied selection) value := by
    intro value member
    obtain ⟨position, rfl⟩ := List.mem_ofFn.mp member
    rw [prepared_read_view]
    exact selected_view_covered locals captures scopes occupied selection _ _
      (worldCovered.rows _ (enabled.kept_subset (by
        simpa only [Selection.commit, List.mem_toFinset] using selection.read.get_mem position)))
  simp only [problem, equationScopes, names_append, Finset.union_subset_iff]
  exact ⟨⟨⟨oldSafe, useEquations_covered _ _ _ _ ruleSafe.take takeSafe⟩,
    useEquations_covered _ _ _ _ ruleSafe.read readSafe⟩, ruleSafe.tell⟩

theorem afterInventory_covered [DecidableEq O] (scopes : Shared → Finset Nat) (occupied : Finset Nat)
    (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (inventory : Inventory locals captures (O := O) Γ sort)
    (outputs : O → Term (signature S (target locals captures)) Γ sort)
    (worldCovered : CoveredWorld locals captures scopes occupied inventory)
    (ruleCovered : RuleCovered (privateScopes scopes) occupied rule)
    (enabled : Enabled outputs inventory.configuration.present
      (selection.commit (T := Term (signature S (target locals captures)) Γ sort)))
    (outputsShape : selection.made.map outputs =
      (prepared locals captures occupied selection rule inventory.rows).rule.produce) :
    CoveredWorld locals (target locals captures) (activeScopes scopes)
      (ContextualActivationScopes.after occupied selection)
      (afterInventory locals captures occupied selection rule inventory outputs) := by
  have oldSubset := ContextualActivationScopes.old_scopes_retained occupied selection
  have ruleSafe := prepared_rule_covered locals captures scopes occupied selection rule inventory.rows ruleCovered
  refine ⟨problem_covered locals captures scopes occupied selection rule inventory outputs worldCovered ruleCovered enabled,
    ?_, ?_, ?_⟩
  · intro occurrence member
    change occurrence ∈ fire inventory.configuration.present selection.commit at member
    by_cases made : occurrence ∈ selection.made
    · change row locals _ _ (resultRows locals captures selection outputs inventory.rows occurrence) ⊆ _
      rw [produced_row_is_shared locals captures selection outputs inventory.rows made]
      apply row_shared
      apply ruleSafe.produce (outputs occurrence)
      rw [← outputsShape]
      exact List.mem_map.mpr ⟨occurrence, made, rfl⟩
    · have old : occurrence ∈ inventory.configuration.present := by
        rcases Finset.mem_union.mp member with retained | added
        · exact (Finset.mem_sdiff.mp retained).1
        · exact False.elim (made (by simpa only [Selection.commit, List.mem_toFinset] using added))
      change row locals _ _ (if occurrence ∈ selection.made then _ else _) ⊆ _
      rw [if_neg made]
      exact Finset.Subset.trans (row_map locals scopes _ _ (respects_capturedTarget locals captures scopes)
        (inventory.rows occurrence) (worldCovered.rows occurrence old)) oldSubset
  · change observations (activeScopes scopes)
      (inventory.retained.map _ ++ ruleRoots _) ⊆ _
    rw [observations, names_append, Finset.union_subset_iff]
    exact ⟨Finset.Subset.trans
      (observations_map scopes _ occupied _ (respects_capturedTarget locals captures scopes) _ worldCovered.retained)
      oldSubset, ruleRoots_covered ruleSafe⟩
  · exact Finset.Subset.trans
      (observations_map _ _ occupied _
        (respects_liftCaptures locals scopes _ _ (respects_capturedTarget locals captures scopes))
        inventory.templates worldCovered.templates) oldSubset

theorem guarded_step_preserves_ledger [DecidableEq O] (scopes : Shared → Finset Nat)
    {occupied : Finset Nat} {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S (source locals captures)) Γ sort)}
    (inventory : Inventory locals captures (O := O) Γ sort)
    {outputs : O → Term (signature S (target locals captures)) Γ sort}
    {after : Configuration (Term (signature S (target locals captures)) Γ sort) O}
    {afterRows : O → ContextualStoredRows.Row locals (target locals captures) Γ sort}
    {afterOccupied : Finset Nat}
    (covered : CoveredWorld locals captures scopes occupied inventory)
    (ruleCovered : RuleCovered (privateScopes scopes) occupied rule)
    (step : ContextualGuardedStep.Step locals captures occupied rule inventory.rows inventory.configuration
      outputs after afterRows afterOccupied) :
    ∃ selection, afterOccupied = ContextualActivationScopes.after occupied selection ∧
      CoveredWorld locals (target locals captures) (activeScopes scopes) afterOccupied
        ⟨after, afterRows,
          inventory.retained.map (instantiateObservation (ContextualSelectionViews.capturedTarget locals captures)) ++
            ruleRoots (prepared locals captures occupied selection rule inventory.rows).rule,
          inventory.templates.map (instantiateObservation
            (ContextualStoredRows.liftCaptures locals (ContextualSelectionViews.capturedTarget locals captures)))⟩ := by
  obtain ⟨selection, valid, rfl, rfl, rfl⟩ := step
  exact ⟨selection, rfl, afterInventory_covered locals captures scopes occupied selection rule inventory outputs
    covered ruleCovered
    ((ContextualInteractionFactors.resources_iff outputs _ _).mp valid.resources).2.2
    valid.formation.outputs⟩

def publish {Γ : Ctx S} {sort : S.Srt}
    (inventory : Inventory locals captures (O := O) Γ sort)
    (newTemplates : List (Observation S (source locals captures))) : Inventory locals captures (O := O) Γ sort :=
  {inventory with templates := inventory.templates ++ newTemplates}

def publicationLedger (scopes : Shared → Finset Nat) (occupied : Finset Nat)
    (newTemplates : List (Observation S (source locals captures))) : Finset Nat :=
  occupied ∪ observations (privateScopes scopes) newTemplates

theorem publish_covered (scopes : Shared → Finset Nat) {occupied : Finset Nat}
    {Γ : Ctx S} {sort : S.Srt} (inventory : Inventory locals captures (O := O) Γ sort)
    (covered : CoveredWorld locals captures scopes occupied inventory)
    (newTemplates : List (Observation S (source locals captures))) :
    CoveredWorld locals captures scopes (publicationLedger locals captures scopes occupied newTemplates)
      (publish locals captures inventory newTemplates) := by
  have oldSubset : occupied ⊆ publicationLedger locals captures scopes occupied newTemplates := Finset.subset_union_left
  have old := covered.mono locals captures oldSubset
  refine ⟨old.equations, old.rows, old.retained, ?_⟩
  change observations (privateScopes scopes) (inventory.templates ++ newTemplates) ⊆ _
  rw [observations, names_append, Finset.union_subset_iff]
  exact ⟨old.templates, Finset.subset_union_right⟩

theorem subsequent_reservation_avoids_every_root [DecidableEq O]
    (scopes : Shared → Finset Nat) {occupied : Finset Nat} {Γ : Ctx S} {sort : S.Srt}
    {inventory : Inventory locals captures (O := O) Γ sort}
    (covered : CoveredWorld locals captures scopes occupied inventory)
    (selection : Selection O) (port : ContextualActivationScopes.Port selection) :
    ContextualActivationScopes.scopeAt occupied port ∉ footprint locals captures scopes inventory := by
  intro member
  exact ContextualActivationScopes.at_fresh occupied port
    ((coveredWorld_iff locals captures scopes occupied inventory).mp covered member)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldScopeLedger
