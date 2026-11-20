import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunication
import Mettapedia.OSLF.Syntax.ContextualRigidTerms
import Mettapedia.OSLF.Syntax.RhoPayloadTranslation

/-!
# Closed rho communication as an ordinary occurrence step

The same closed channel, payload and open continuation determine both a source
communication and an occurrence firing. The name-binding profile uses an
instantiated ordinary rule. The payload-binding profile opens the schematic
rule in a fresh scope, establishes actual activation admission, and reads its
result under every solution of the generated equations. Each profile retains
its existing binding signature and plugging operation. These are closed
communication results, not whole-language correspondences.
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

namespace Payload

abbrev base := ContextualCommunication.Payload.base
abbrev locals := ContextualCommunication.Payload.locals

variable {V W : Type} (captures : V → MetaArity base)
  (channel : Term base [] .nm) (payload : Term base [] .pr) (body : Term base [.pr] .pr)

abbrev raw := ContextualCommunication.Payload.source captures
abbrev active := ContextualCommunication.Payload.target captures

def selection : Selection Nat := ⟨[0, 1], [], [2]⟩
def before : Configuration (Term (signature base captures) [] .pr) Nat := ⟨[], {0, 1}⟩

/-- Stored values retain the source's intrinsic binding, not a serialized name. -/
def rows (occurrence : Nat) : ContextualStoredRows.Row locals captures [] .pr :=
  .shared (Rigid.includeTerm captures
    (if occurrence = 0 then RhoPayloadPresentation.inpT channel body
    else if occurrence = 1 then RhoPayloadPresentation.outT channel payload
    else RhoPayloadPresentation.nilT))

def ruleScope (occupied : Finset Nat) :=
  ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort selection)

def outputs (occupied : Finset Nat) (_ : Nat) : Term (signature base (active captures)) [] .pr :=
  ContextualFreshening.termAt locals captures (ruleScope occupied)
    (continuationFor (S := base) .nm .pr .pr captures (payloadFor (S := base) .nm .pr .pr captures))

def problem (occupied : Finset Nat) :=
  ContextualActivatedStep.problem locals captures occupied selection
    (ContextualCommunication.Payload.rule captures) (rows captures channel payload body) (before captures)

theorem problem_equations (occupied : Finset Nat) :
    problem captures channel payload body occupied =
      [(ContextualFreshening.termAt locals captures (ruleScope occupied)
          ((ContextualCommunication.Payload.rule captures).take[0]'(by change 0 < 2; decide)),
        Rigid.includeTerm (active captures) (RhoPayloadPresentation.inpT channel body)),
       (ContextualFreshening.termAt locals captures (ruleScope occupied)
          ((ContextualCommunication.Payload.rule captures).take[1]'(by change 1 < 2; decide)),
        Rigid.includeTerm (active captures) (RhoPayloadPresentation.outT channel payload))] := by
  change [( _, instantiate _ (instantiate _ (Rigid.includeTerm captures _))),
      (_, instantiate _ (instantiate _ (Rigid.includeTerm captures _)))] = _
  simp only [Rigid.instantiate_include]
  rfl

def supply : Assignment (raw captures) captures
  | .inl .channel => Rigid.includeTerm captures channel
  | .inl .payload => Rigid.includeTerm captures payload
  | .inl .continuation => Rigid.includeTerm captures body
  | .inr identity => generator captures identity

def witness : Assignment (active captures) captures
  | .inl ⟨_, .channel⟩ => Rigid.includeTerm captures channel
  | .inl ⟨_, .payload⟩ => Rigid.includeTerm captures payload
  | .inl ⟨_, .continuation⟩ => Rigid.includeTerm captures body
  | .inr identity => generator captures identity

theorem instantiate_fresh (scope : Nat) {Γ : Ctx base} {sort : base.Srt}
    (term : Term (signature base (raw captures)) Γ sort) :
    instantiate (witness captures channel payload body)
      (ContextualFreshening.termAt locals captures scope term) =
        instantiate (supply captures channel payload body) term := by
  rw [ContextualFreshening.termAt, instantiate_comp]
  congr 1
  funext identity
  cases identity with
  | inl port =>
      change instantiate (witness captures channel payload body)
        (generator (active captures) (.inl ⟨scope, port⟩)) = _
      rw [instantiate_generator]
      cases port <;> rfl
  | inr identity =>
      exact instantiate_generator (witness captures channel payload body) (.inr identity)

theorem witness_models (occupied : Finset Nat) :
    ContextualFrameUnifier.Models (witness captures channel payload body)
      (problem captures channel payload body occupied) := by
  intro equation member
  rw [problem_equations] at member
  rcases List.mem_cons.mp member with same | tail
  · subst equation
    rw [instantiate_fresh, Rigid.instantiate_include]
    change ContextualCommunication.Payload.input
      (instantiate (supply captures channel payload body) (generator (raw captures) (.inl .channel)))
      (instantiate (supply captures channel payload body) (generator (raw captures) (.inl .continuation))) = _
    erw [instantiate_generator, instantiate_generator]
    rfl
  · have same := List.mem_singleton.mp tail
    subst equation
    rw [instantiate_fresh, Rigid.instantiate_include]
    change ContextualCommunication.Payload.output
      (instantiate (supply captures channel payload body) (generator (raw captures) (.inl .channel)))
      (instantiate (supply captures channel payload body) (generator (raw captures) (.inl .payload))) = _
    erw [instantiate_generator, instantiate_generator]
    rfl

/-- Freshening and matching the actual schematic rule admits the communication;
the rule is not replaced by a precomputed input/output instance. -/
theorem activation_valid (occupied : Finset Nat) :
    ContextualActivatedStep.Valid locals captures occupied selection
      (ContextualCommunication.Payload.rule captures) (rows captures channel payload body)
      (before captures) (outputs captures occupied) := by
  refine ⟨rfl, by decide, by decide, rfl, rfl, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change ({0, 1} : Finset Nat) ⊆ {0, 1}
      exact Finset.Subset.refl _
    · exact Finset.empty_subset _
    · exact Finset.disjoint_empty_right _
    · change Disjoint ({2} : Finset Nat) {0, 1}
      decide +kernel
    · intro query member
      cases member
  · exact ⟨V, captures, witness captures channel payload body,
      witness_models captures channel payload body occupied⟩

theorem activated_step (occupied : Finset Nat) :
    ContextualActivatedStep.Step locals captures occupied
      (ContextualCommunication.Payload.rule captures) (rows captures channel payload body)
      (before captures) (outputs captures occupied)
      (ContextualActivatedStep.result locals captures occupied selection
        (ContextualCommunication.Payload.rule captures) (rows captures channel payload body) (before captures))
      (ContextualActivatedStep.resultRows locals captures selection (outputs captures occupied)
        (rows captures channel payload body))
      (ContextualActivationScopes.after occupied selection) :=
  ⟨selection, activation_valid captures channel payload body occupied, rfl, rfl, rfl⟩

theorem exact_occurrence_result (occupied : Finset Nat) :
    (ContextualActivatedStep.result locals captures occupied selection
      (ContextualCommunication.Payload.rule captures) (rows captures channel payload body) (before captures)).present = {2} := by
  change (({0, 1} \ ({0, 1} : Finset Nat)) ∪ {2}) = {2}
  decide +kernel

/-- Every solution of the admitted equations reads the same source result.
The statement ranges over further declaration families, not only the witness
used to establish consistency. -/
theorem result_in_every_solution (occupied : Finset Nat) (next : W → MetaArity base)
    (assignment : Assignment (active captures) next)
    (solved : ContextualFrameUnifier.Models assignment (problem captures channel payload body occupied)) :
    instantiate assignment (outputs captures occupied 2) =
      Rigid.includeTerm next (inst body payload) := by
  have equations := problem_equations captures channel payload body occupied
  have first := solved _ (equations ▸ List.mem_cons_self)
  have second := solved _ (equations ▸ List.mem_cons_of_mem _ List.mem_cons_self)
  rw [Rigid.instantiate_include] at first second
  change ContextualCommunication.Payload.input
    (instantiate assignment (generator (active captures) (.inl ⟨ruleScope occupied, .channel⟩)))
    (instantiate assignment (generator (active captures) (.inl ⟨ruleScope occupied, .continuation⟩))) = _ at first
  change ContextualCommunication.Payload.output
    (instantiate assignment (generator (active captures) (.inl ⟨ruleScope occupied, .channel⟩)))
    (instantiate assignment (generator (active captures) (.inl ⟨ruleScope occupied, .payload⟩))) = _ at second
  erw [instantiate_generator, instantiate_generator] at first second
  have continuationImage := (ContextualCommunication.Payload.input_fields first).2
  have payloadImage := (ContextualCommunication.Payload.output_fields second).2
  rw [outputs, ContextualFreshening.termAt, instantiate_comp,
    ContextualCommunication.Payload.instantiate_result]
  dsimp only [ContextualFreshening.assignment]
  erw [instantiate_generator, instantiate_generator]
  erw [continuationImage, payloadImage]
  exact (Rigid.include_inst next body payload).symm

theorem source_communication :
    RhoPayloadPresentation.Steps RhoPayloadPresentation.strictRules
      (RhoPayloadPresentation.parT (RhoPayloadPresentation.outT channel payload)
        (RhoPayloadPresentation.inpT channel body)) (inst body payload) :=
  RhoPayloadPresentation.steps_comm [] channel payload body

/-- The same result agrees with the semantic COMM operation on the authored
rho syntax whenever its continuation and payload have the stated translation.
Agreement is at source equation classes, not raw quotation syntax. -/
theorem semantic_comm_readback
    {sourceBody sourcePayload : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (bodyTranslation : RhoPayloadPresentation.tProc (RhoPayloadPresentation.Env.empty []).up
      sourceBody = some body)
    (payloadTranslation : RhoPayloadPresentation.tProc (RhoPayloadPresentation.Env.empty [])
      sourcePayload = some payload)
    (occupied : Finset Nat) (next : W → MetaArity base)
    (assignment : Assignment (active captures) next)
    (solved : ContextualFrameUnifier.Models assignment (problem captures channel payload body occupied)) :
    ∃ translated, RhoPayloadPresentation.tProc (RhoPayloadPresentation.Env.empty [])
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.semanticCommSubst sourceBody sourcePayload) = some translated ∧
      ∃ result, instantiate assignment (outputs captures occupied 2) = Rigid.includeTerm next result ∧
        EqClosure RhoPayloadPresentation.equations result translated := by
  obtain ⟨translated, translation, agreement⟩ :=
    RhoPayloadPresentation.translate_semanticCommSubst bodyTranslation payloadTranslation
  exact ⟨translated, translation, inst body payload,
    result_in_every_solution captures channel payload body occupied next assignment solved, agreement.symm⟩

end Payload

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCommunicationGround
