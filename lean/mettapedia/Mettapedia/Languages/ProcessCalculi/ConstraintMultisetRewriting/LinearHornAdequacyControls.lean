import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LinearHornAdequacy
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PositiveResourceProjectionControls

/-!
# Linear proof controls: genuine generation, no contraction and physical lifting

A two-rule diagram consumes and produces the exact declared multiplicities
beside a residual frame. In the absence of declarations, cardinality rejects
both copying and dropping context atoms. A genuine ordinary CMR receipt then
passes through the independent logical proof type and back to a fresh actual
schedule under the same shared substitution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LinearHornAdequacyControls

open Mettapedia.Logic
open Mettapedia.GSLT.Causality
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open PositiveResourceProjection
open LinearHornAdequacy

def exampleSystem : ResourceInteraction.System Nat where
  Site := Bool
  Instance _ := Unit
  consume := fun {declaration} _ => if declaration then {1, 1} else {0}
  read _ := 0
  produce := fun {declaration} _ => if declaration then {2} else {1, 1}

def entry (which : Bool) : exampleSystem.Entry := ⟨which, ()⟩

def diagram : exampleSystem.HornProof ({9} + {0}) ({9} + {2}) :=
  .tensor (.identity {9}) (.cut (.rule (entry false)) (.rule (entry true)))

theorem the_independent_diagram_uses_both_declarations : diagram.uses = [entry false, entry true] := rfl

theorem independent_tensor_cut_proof_sequentializes_to_actual_firings :
    exampleSystem.Fires [entry false, entry true] ({9} + {0}) ({9} + {2}) :=
  exampleSystem.horn_proof_fires (fun _ => rfl) diagram

theorem the_intermediate_two_copies_are_real_resources :
    exampleSystem.fire ({9} + {0}) (entry false).2 = ({9, 1, 1} : Multiset Nat) := by decide

def readSystem : ResourceInteraction.System Nat where
  Site := Unit
  Instance _ := Unit
  consume _ := {0}
  read _ := {9}
  produce _ := {1}

def readEntry : readSystem.Entry := ⟨(), ()⟩

/-- Forgetting a source read would make its logical rule usable without the
resource actually required by the source. The no-read hypothesis matters. -/
theorem a_logical_rule_without_its_read_is_not_a_source_firing :
    Nonempty (readSystem.HornProof ({0} : Multiset Nat) {1}) ∧
      ¬ readSystem.Fires [readEntry] ({0} : Multiset Nat) {1} := by
  refine ⟨⟨.rule readEntry⟩, ?_⟩
  intro fired
  have absent : ¬ readSystem.Enables ({0} : Multiset Nat) readEntry.2 := by
    change ¬ (({0} : Multiset Nat) + {9} ≤ {0})
    decide
  exact absent fired.1

def noRules (_ : Empty) : Multiset Nat := 0

def cardinality : Multiset Nat →+ Nat where
  toFun := Multiset.card
  map_zero' := rfl
  map_add' := Multiset.card_add

theorem identity_tensor_and_cut_cannot_copy_a_resource :
    ¬ Nonempty (LinearHorn.Derivation noRules noRules ({0} : Multiset Nat) {0, 0}) := by
  rintro ⟨proof⟩
  have same := proof.preserves_valuation cardinality (fun declaration => nomatch declaration)
  change (1 : Nat) = 2 at same
  cases same

theorem identity_tensor_and_cut_cannot_drop_a_residual_resource :
    ¬ Nonempty (LinearHorn.Derivation noRules noRules ({0, 9} : Multiset Nat) {0}) := by
  rintro ⟨proof⟩
  have same := proof.preserves_valuation cardinality (fun declaration => nomatch declaration)
  change (2 : Nat) = 1 at same
  cases same

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls
open PositiveResourceProjection.Controls

noncomputable section

local instance : DecidableEq (Term signature) := Classical.decEq _

def declaredProgram : Set (RuleInstance (Term signature)) := {duplicateOutputs}

def termCardinality : Multiset (Term signature) →+ Nat where
  toFun := Multiset.card
  map_zero' := rfl
  map_add' := Multiset.card_add

theorem the_declared_program_cannot_forge_a_resource_from_nothing :
    ¬ Nonempty (Proof A declaredProgram both 0 ({Term.const (σ := signature) 42} : Multiset (Term signature))) := by
  rintro ⟨proof⟩
  have balanced : ∀ declaration : (system A declaredProgram both).Entry,
      termCardinality ((system A declaredProgram both).consume declaration.2) =
        termCardinality ((system A declaredProgram both).produce declaration.2) := by
    intro declaration
    have present := declaration.1.property.1
    have same : declaration.1.val = duplicateOutputs := Set.mem_singleton_iff.mp present
    change (declaration.1.val.take.map (A.apply both)).length =
      (declaration.1.val.produce.map (A.apply both)).length
    rw [same]
    rfl
  have impossible := proof.preserves_valuation termCardinality balanced
  change (0 : Nat) = 1 at impossible
  cases impossible

theorem actual_receipt_logical_proof_and_fresh_receipt_agree :
    ∃ schedule : List (ConditionalSchedule.Firing (Term signature) Id),
      ConditionalSchedule.Executable A indexedLabel indexedBefore schedule ∧ Pure schedule ∧
      Declared declaredProgram schedule ∧
      A.Models both (ConditionalSchedule.follow indexedLabel indexedBefore schedule).equations ∧
      labels (realized A both indexedLabel)
        (ConditionalSchedule.follow indexedLabel indexedBefore schedule).present =
          ({Term.const (σ := signature) 1, Term.const (σ := signature) 1, Term.const (σ := signature) 1} : Multiset (Term signature)) ∧
      schedule.map Prod.fst = [duplicateOutputs] := by
  obtain ⟨selection, valid, solved, _, _, _, observed⟩ := an_actual_selection_realizes_the_bag_frame
  let original : List (ConditionalSchedule.Firing (Term signature) Id) := [(duplicateOutputs, selection)]
  have executable : ConditionalSchedule.Executable A indexedLabel indexedBefore original :=
    ⟨valid, both, solved⟩
  have pure : Pure original := by
    intro firing member
    have same : firing = (duplicateOutputs, selection) := List.mem_singleton.mp member
    subst firing
    exact ⟨rfl, rfl⟩
  have declared : Declared declaredProgram original := by
    intro firing member
    have same : firing = (duplicateOutputs, selection) := List.mem_singleton.mp member
    subst firing
    exact Set.mem_singleton _
  obtain ⟨proof, uses⟩ := proof_of_constraint_schedule A declaredProgram both indexedLabel rfl original indexedBefore executable pure declared solved
  have supply : ∀ (world : Finset Id) (value : Term signature),
      ∃ occurrence, occurrence ∉ world ∧ indexedLabel occurrence = value := IndexedOccurrences.supply
  obtain ⟨schedule, executes, isPure, isDeclared, finalModel, finalBag, rawRules⟩ :=
    constraint_schedule_of_proof A declaredProgram both indexedLabel rfl supply indexedBefore (A.models_nil both) _ proof
  refine ⟨schedule, executes, isPure, isDeclared, finalModel, finalBag.trans observed, ?_⟩
  exact rawRules.trans uses

end

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LinearHornAdequacyControls
