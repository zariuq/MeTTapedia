import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunication
import Mettapedia.OSLF.Syntax.ContextualRigidTerms

/-!
# Closed rho communication as an ordinary occurrence step

The same closed channel, payload and open continuation determine both the
existing source rho reduction and an ordinary two-sided occurrence firing.
The binding signature and plugging operation are unchanged. This comparison
concerns one closed source instance; it does not erase the occurrence order
or assert a converse for arbitrary contextual or guarded rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationGround

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ContextualCommunication

variable {V : Type} (declaration : V → MetaArity base)
  (channel : Term base [] .nm) (payload : Term base [] .pr) (body : Term base [.nm] .pr)

def receiver := Rigid.includeTerm declaration (RhoSchema.ClosedCommunication.input channel body)
def sender := Rigid.includeTerm declaration (RhoSchema.ClosedCommunication.output channel payload)
def destination := Rigid.includeTerm declaration (inst body (RhoSchema.ClosedCommunication.quote payload))

def instanceRule : RuleInstance (Term (signature base declaration) [] .pr) where
  take := [receiver declaration channel body, sender declaration channel payload]
  read := []
  tell := []
  checks := []
  produce := [destination declaration payload body]

def supply : Assignment (ContextualCommunication.source declaration) declaration
  | .inl .channel => Rigid.includeTerm declaration channel
  | .inl .payload => Rigid.includeTerm declaration payload
  | .inl .continuation => Rigid.includeTerm declaration body
  | .inr name => generator declaration name

theorem the_contextual_schema_instantiates_to_this_closed_rule :
    (rule declaration).map (instantiate (supply declaration channel payload body)) =
      instanceRule declaration channel payload body := by
  let assignment := supply declaration channel payload body
  have channelImage : instantiate assignment (ContextualCommunication.channel declaration (Γ := [])) =
      Rigid.includeTerm declaration channel := instantiate_generator assignment (.inl .channel)
  have payloadImage : instantiate assignment (ContextualCommunication.payload declaration (Γ := [])) =
      Rigid.includeTerm declaration payload := instantiate_generator assignment (.inl .payload)
  have continuationImage : instantiate assignment (continuation declaration (.var .zero)) =
      Rigid.includeTerm declaration body := instantiate_generator assignment (.inl .continuation)
  have inputImage : instantiate assignment
      (input (ContextualCommunication.channel declaration) (continuation declaration (.var .zero))) =
      receiver declaration channel body := congrArg₂ input channelImage continuationImage
  have outputImage : instantiate assignment
      (output (ContextualCommunication.channel declaration) (ContextualCommunication.payload declaration)) =
      sender declaration channel payload := congrArg₂ output channelImage payloadImage
  have resultImage : instantiate assignment
      (continuation declaration (quote (ContextualCommunication.payload declaration))) =
      destination declaration payload body := by
    exact (instantiate_result declaration assignment).trans
      (Rigid.include_inst declaration body (RhoSchema.ClosedCommunication.quote payload)).symm
  have takes : (rule declaration).take.map (instantiate assignment) =
      (instanceRule declaration channel payload body).take :=
    congrArg₂ List.cons inputImage (congrArg₂ List.cons outputImage rfl)
  have produces : (rule declaration).produce.map (instantiate assignment) =
      (instanceRule declaration channel payload body).produce := congrArg₂ List.cons resultImage rfl
  exact congrArg₂ (fun taken made : List (Term (signature base declaration) [] .pr) =>
    (⟨taken, [], [], [], made⟩ : RuleInstance (Term (signature base declaration) [] .pr))) takes produces

def selection : Selection Nat := ⟨[0, 1], [], [2]⟩
def before : Configuration (Term (signature base declaration) [] .pr) Nat := ⟨[], {0, 1}⟩
def label (occurrence : Nat) : Term (signature base declaration) [] .pr :=
  if occurrence = 0 then receiver declaration channel body
  else if occurrence = 1 then sender declaration channel payload else destination declaration payload body

theorem every_selected_value_is_fixed (assignment : Assignment declaration declaration)
    (occurrence : Nat) :
    instantiate assignment (label declaration channel payload body occurrence) =
      label declaration channel payload body occurrence := by
  unfold label
  split
  · exact Rigid.instantiate_include assignment _
  · split <;> exact Rigid.instantiate_include assignment _

theorem one_way_iff_two_way (assignment : Assignment declaration declaration)
    (pattern : Term (signature base declaration) [] .pr) (occurrence : Nat) :
    (ContextualFamilies.action declaration [] .pr).Solves assignment
      (pattern, label declaration channel payload body occurrence) ↔
      instantiate assignment pattern = label declaration channel payload body occurrence :=
  ContextualCommunication.one_way_of_fixed assignment pattern _
    (every_selected_value_is_fixed declaration channel payload body assignment occurrence)

theorem selected_step_is_valid :
    selection.Valid (ContextualFamilies.action declaration [] .pr)
      (label declaration channel payload body) (instanceRule declaration channel payload body) (before declaration) := by
  refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change ({0, 1} : Finset Nat) ⊆ {0, 1}
      exact Finset.Subset.refl _
    · change (∅ : Finset Nat) ⊆ {0, 1}
      exact Finset.empty_subset _
    · change Disjoint ({0, 1} : Finset Nat) ∅
      exact Finset.disjoint_empty_right _
    · change Disjoint ({2} : Finset Nat) {0, 1}
      decide +kernel
    · intro query member
      cases member
  · refine ⟨generator declaration, ?_⟩
    intro equation member
    change equation ∈ [(_, _), (_, _)] at member
    rcases List.mem_cons.mp member with same | tail
    · subst equation
      rfl
    · have same := List.mem_singleton.mp tail
      subst equation
      rfl
  · intro check member
    exact False.elim (List.not_mem_nil member)

theorem ordinary_step :
    Step (ContextualFamilies.action declaration [] .pr) (label declaration channel payload body)
      (instanceRule declaration channel payload body) (before declaration)
      (selection.result (label declaration channel payload body) (instanceRule declaration channel payload body) (before declaration)) :=
  ⟨selection, selected_step_is_valid declaration channel payload body, rfl⟩

theorem exact_occurrence_result :
    (selection.result (label declaration channel payload body) (instanceRule declaration channel payload body) (before declaration)).present = {2} := by
  change (({0, 1} \ ({0, 1} : Finset Nat)) ∪ {2}) = {2}
  decide +kernel

theorem destination_is_capture_avoiding_plugging :
    destination declaration payload body =
      inst (Rigid.includeTerm declaration body)
        (Rigid.includeTerm declaration (RhoSchema.ClosedCommunication.quote payload)) :=
  Rigid.include_inst declaration body (RhoSchema.ClosedCommunication.quote payload)

theorem the_same_inputs_have_the_source_rho_reduction :
    RhoSchema.rho.StepModE
      (RhoSchema.parT (RhoSchema.ClosedCommunication.input channel body)
        (RhoSchema.ClosedCommunication.output channel payload))
      (inst body (RhoSchema.ClosedCommunication.quote payload)) :=
  RhoSchema.ClosedCommunication.source_order_comm channel payload body

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationGround
