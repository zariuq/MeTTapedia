import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadProtected
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSyntax
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

/-! # Open captured-row and protected-execution controls -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericControls

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationMachine (RowTerms X E)
open ApplicationSyntax (symbol)
open RuleOccurrences HeldReadGenericSources HeldReadGenericFirings

def ordinary : RuleSyntax.State RowTerms Nat := ⟨PUnit.unit, [], {0}, fun _ => .var 0⟩
def rows : Finset Nat := {0}
def captured : Closure RowTerms PUnit.unit := ⟨⟨PUnit.unit, [], [(.var 0)], .var 0⟩, [(.var 0)]⟩
def closures (_ : Nat) : Closure RowTerms PUnit.unit := captured
def ruleOpening : Subst rowSig := Subst.single 0 (.var 1)
def datumOpening : Subst rowSig := Subst.single 0 (.var 2)
def request := direct (E := E) ordinary rows closures 0 PUnit.unit ruleOpening datumOpening 1
def helper : HeldReadEncoding.Code RowTerms := .inr (consumeRule captured.schema)
def ambient : Set (HeldReadEncoding.Code RowTerms) := {helper}
def allocate (_ : RuleSyntax.State RowTerms Nat) (_ : Nat) : Nat := 2

theorem mentioned_only_source_variable (term : Tm)
    (mentioned : (mixed ordinary rows closures).scope.Mentions term) : term = .var 0 := by
  have actual := (HeldReadGenericSources.scope_mentions_iff ordinary rows closures term).mp mentioned
  rcases actual with (left | right | ⟨o, _, labelled⟩) | ⟨r, _, argument⟩
  · cases left
  · cases right
  · exact labelled.symm
  · exact List.mem_singleton.mp argument

theorem request_fresh : request.Fresh X := by
  intro target caller ruleAssignment datumAssignment
  cases target
  let combined : Subst rowSig := fun name =>
    if name = 0 then caller 0 else if name = 1 then ruleAssignment 0 else
      if name = 2 then datumAssignment 0 else caller name
  refine ⟨combined, ⟨?_, ?_⟩, ?_⟩
  · intro term mentioned
    have same := mentioned_only_source_variable term mentioned
    subst term
    change combined.applyTerm ((Subst.id rowSig).applyTerm (.var 0)) = caller.applyTerm (.var 0)
    rw [Subst.applyTerm_id]
    change combined 0 = caller 0
    exact if_pos rfl
  · intro term member
    change term ∈ [(.var 0 : Tm), .var 0] at member
    have same : term = .var 0 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using member
    subst term
    change combined.applyTerm (ruleOpening.applyTerm (.var 0)) = ruleAssignment.applyTerm (.var 0)
    simp [combined, ruleOpening, Subst.single, Subst.applyTerm]
  · intro term member
    change term ∈ [(.var 0 : Tm), .var 0] at member
    have same : term = .var 0 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using member
    subst term
    change combined.applyTerm (datumOpening.applyTerm (.var 0)) = datumAssignment.applyTerm (.var 0)
    simp [combined, datumOpening, Subst.single, Subst.applyTerm]

theorem request_information : request.information X =
    [((.var 2 : Tm), .var 0), (.var 1, .var 2)] := rfl

theorem request_admitted : request.Admits X := by
  let point : Subst rowSig := fun _ => symbol 20
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) point (request.information X) := by
    intro equation member
    rw [request_information] at member
    rcases List.mem_cons.mp member with rfl | member
    · rfl
    · obtain rfl := List.mem_singleton.mp member
      rfl
  refine ⟨direct_shapes (E := E) X ordinary rows closures 0 PUnit.unit ruleOpening datumOpening 1 request_fresh rfl,
    direct_enabled (E := E) ordinary rows closures 0 PUnit.unit ruleOpening datumOpening 1 (by decide) (by decide),
    ⟨PUnit.unit, point, solved⟩, ?_⟩
  intro target assignment _
  exact direct_holds (E := E) X ordinary rows closures 0 PUnit.unit ruleOpening datumOpening 1 assignment

theorem actual_two_stage_read :
    ∃ run : (protocolMachine (E := E) (O := Nat) (R := Nat) X ambient).Run (hosted ordinary rows closures),
      run.word.length = 2 ∧ run.last.present = {0, 1} ∧ run.last.rules = {0} ∧ 2 ∉ run.last.present := by
  obtain ⟨run, length, _, present, held, absent⟩ := execution_of_direct (E := E) X ordinary rows closures 0 PUnit.unit
    ruleOpening datumOpening 2 1 ambient (Set.mem_singleton helper) (by decide) (by decide) request_admitted
  exact ⟨run, length, by simpa [ordinary] using present, held, absent⟩

theorem colliding_temporary_refuses_completion :
    ¬ (consumer (E := E) ordinary rows closures 0 PUnit.unit ruleOpening datumOpening X 1 1).Admits X ambient := by
  intro admitted
  have present : 1 ∈ ((datum (E := E) ordinary rows closures 0 PUnit.unit datumOpening 1).result X).present :=
    (datum_present (E := E) X ordinary rows closures 0 PUnit.unit datumOpening 1).symm ▸
      Finset.mem_union_right _ (Finset.mem_singleton_self _)
  exact Finset.disjoint_left.mp admitted.2.1.fresh
    (List.mem_toFinset.mpr (List.mem_singleton_self _)) present

theorem missing_helper_refuses_completion :
    ¬ (consumer (E := E) ordinary rows closures 0 PUnit.unit ruleOpening datumOpening X 2 1).Admits X ∅ := by
  intro admitted
  exact Set.notMem_empty _ admitted.1.2.2.available

def badRequest := direct (E := E) ordinary rows closures 0 PUnit.unit (Subst.id rowSig) datumOpening 1

theorem source_capture_is_not_fresh : ¬ badRequest.Fresh X := by
  intro fresh
  let caller : Subst rowSig := fun _ => symbol 20
  let ruleAssignment : Subst rowSig := fun _ => symbol 21
  obtain ⟨combined, ⟨kept, ruleTerms⟩, _⟩ := fresh PUnit.unit caller ruleAssignment caller
  have sourceMention : (mixed ordinary rows closures).scope.Mentions (.var 0 : Tm) := by
    apply (State.scope_mentions_iff _ _).mpr
    exact Or.inr (Or.inr ⟨.inl 0, by decide, List.mem_singleton_self _⟩)
  have old := kept (.var 0) sourceMention
  have localImage := ruleTerms (.var 0) (by change (.var 0 : Tm) ∈ [(.var 0 : Tm), .var 0]; simp)
  change combined 0 = symbol 20 at old
  change combined 0 = symbol 21 at localImage
  have impossible := old.symm.trans localImage
  cases impossible

noncomputable def readPlan : HeldReadProtected.Plan X E ambient allocate (hosted ordinary rows closures) :=
  .read ordinary rows closures 0 PUnit.unit ruleOpening datumOpening 1 (Set.mem_singleton helper)
    (by decide) (by decide) request_admitted

noncomputable def configuration := HeldReadProtected.configuration (O := Nat) (R := Nat) X E ambient allocate
  (∅ : Set (HeldReadEncoding.Code RowTerms)) (fun {_} _ => false) (fun {_} _ => true)

noncomputable def logicalRead : ProtectedTwoStage.MacroTrace configuration
    (hosted ordinary rows closures) [true] (configuration.realize readPlan).finishState :=
  .cons (.protocol readPlan) (.nil _)

theorem logical_read_has_two_actual_events :
    (ProtectedTwoStage.underlying configuration (ProtectedTwoStage.expand configuration logicalRead)).word.length = 2 := rfl

theorem logical_read_round_trip :
    ProtectedTwoStage.collapse configuration (ProtectedTwoStage.expand configuration logicalRead) = logicalRead :=
  ProtectedTwoStage.collapse_expand configuration logicalRead

theorem no_public_action_during_pending {target}
    (move : ProtectedTwoStage.MicroMove configuration (.pending readPlan) (some false) target) : False := by
  cases move

theorem completion_is_private :
    ¬ configuration.publicAllowed (configuration.realize readPlan).second :=
  HeldReadProtected.completion_not_public X E ambient allocate ∅ readPlan

theorem first_can_be_public : configuration.publicAllowed (configuration.realize readPlan).first := by
  exact ⟨⟨PUnit.unit, rfl⟩, trivial⟩

noncomputable def logicalPublic : ProtectedTwoStage.MacroTrace configuration
    (hosted ordinary rows closures) [false] (configuration.realize readPlan).middle :=
  .cons (.external (configuration.realize readPlan).first
    (configuration.realize readPlan).firstAdmitted first_can_be_public) (.nil _)

theorem public_action_has_one_actual_event :
    (ProtectedTwoStage.underlying configuration (ProtectedTwoStage.expand configuration logicalPublic)).word.length = 1 := rfl

theorem output_keeps_capture (point : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) point
      ((consumer (E := E) ordinary rows closures 0 PUnit.unit ruleOpening datumOpening X 2 1).result X).knowledge) :
    point.applyTerm
        (((consumer (E := E) ordinary rows closures 0 PUnit.unit ruleOpening datumOpening X 2 1).result X).label 1) =
      point.applyTerm (.var 0) := by
  have information := HeldReadGenericFirings.information_eq (E := E) X ordinary rows closures 0 PUnit.unit
    ruleOpening datumOpening 2 1
  have solved : X.Models (a := PUnit.unit) (b := PUnit.unit) point (request.information X) := information ▸ known
  rw [request_information] at solved
  have captured := solved ((.var 2 : Tm), .var 0) List.mem_cons_self
  have matched := solved ((.var 1 : Tm), .var 2) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  exact matched.trans captured

#print axioms request_fresh
#print axioms actual_two_stage_read
#print axioms colliding_temporary_refuses_completion
#print axioms missing_helper_refuses_completion
#print axioms source_capture_is_not_fresh
#print axioms logical_read_round_trip
#print axioms no_public_action_during_pending
#print axioms completion_is_private
#print axioms first_can_be_public
#print axioms output_keeps_capture

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericControls
