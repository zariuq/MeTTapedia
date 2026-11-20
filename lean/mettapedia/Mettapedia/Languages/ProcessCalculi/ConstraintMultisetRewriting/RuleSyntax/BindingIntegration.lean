import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegrationSyntax
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegrationAdmission
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegrationRows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegrationWorlds

/-!
# Binding application, schematic activation and a counted world event

The term computed by the common physical graft is the same term stored in the
selected schema and observed at the actual firing's output. A model of the
source knowledge, a compatible local schema instantiation and its capture
equations construct the firing and event; target admission is not a premise.
The output is read back at its intrinsic context and sort.

Certified contextual solving may subsequently factor this witness through a
fresh target declaration frame. The compared store is the held firing's full
information, including capture equations, rather than only its base rule.
The construction does not choose a universal store or firing discipline.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT.LanguageDef
open Interface (Frames)
open Interface.Frames (Frame)
open RuleOccurrences SchematicRows
open SchematicRows.HeldReadGenericSources

namespace Pipeline

variable {S : Signature} [DecidableEq S.Srt]

/-- Read the existing intrinsic term carried by an observation through its
selected head presentation. The context and sort are checked by the reader. -/
def observationTree {Variables : Type} {declaration : Variables → MetaArity S}
    (code : Presentation.Intrinsic.HeadPresentation (signature S declaration)) :
    Observation S declaration → Presentation.Payloads.Term
  | ⟨_, _, term⟩ => Presentation.Intrinsic.lower code term

variable {O R : Type} [DecidableEq O] [DecidableEq R]
  (catalogue : R → Schema (Contextual.Terms S))
  (captures : (state : State (Contextual.Terms S) O) → R → List (Contextual.Terms S state.frame))
  (rows : Finset R) (program : Program (Contextual.Terms S))
  (state : State (Contextual.Terms S) O) (selected : R) (output : O)
  {parameters context : Ctx S} {sort : S.Srt}
  (body : Term (signature S (catalogue selected).locals.arity) parameters sort)
  (arguments : Args (signature S (catalogue selected).locals.arity)
    (parameters.map (fun parameter => ([], parameter))) context)

/-- Actual execution and its named readout share the physically applied term.
The source layout identifies the schema's authored value; it supplies no
target firing, target model or execution correspondence. -/
theorem application_materializes
    (sourceCode : Presentation.Intrinsic.HeadPresentation
      (signature S (catalogue selected).locals.arity))
    (layout : (catalogue selected).value = observe (bind (argsToSub arguments) body))
    (visible : (catalogue selected).toRule ∈ program)
    (present : selected ∈ rows) (fresh : output ∉ state.present)
    {target : Frame S} (caller : Assignment state.frame.arity target.arity)
    (known : (Frames.contextual S).Models caller state.knowledge)
    (localPoint : Assignment (catalogue selected).locals.arity target.arity)
    (localKnown : (Frames.contextual S).Models localPoint (catalogue selected).knowledge)
    (captureModel : List.Forall₂ (fun parameter argument =>
      instantiateObservation localPoint parameter = instantiateObservation caller argument)
      (catalogue selected).params (captures state selected))
    (targetCode : Presentation.Intrinsic.HeadPresentation (signature S target.arity)) :
    Syntax.graftAndRead? sourceCode context sort parameters.length
        ((CommonABT.lowerSpine arguments).map (SignatureIndexedABT.mapHeads (sourceCode.view (sort := ()))))
        (Presentation.Intrinsic.lower sourceCode body) = some (bind (argsToSub arguments) body) ∧
      ∃ choice : Worlds.Choice catalogue captures rows program state,
        choice.selected = selected ∧ choice.output = output ∧
        (Worlds.activationEvents catalogue captures rows program).next state choice =
          ((Rows.activation state rows (Worlds.closures catalogue captures state) selected output).result
            (Frames.contextual S)).toState ∧
        ∃ point : Assignment
            (Contextual.extend S state.frame (catalogue selected).locals).arity target.arity,
          (Frames.contextual S).Models point
            ((Rows.activation state rows (Worlds.closures catalogue captures state) selected output).result
              (Frames.contextual S)).knowledge ∧
          (∀ term, (hosted state rows (Worlds.closures catalogue captures state)).Mentions term →
            instantiateObservation point
                (instantiateObservation (Contextual.weakenNames S state.frame (catalogue selected).locals) term) =
              instantiateObservation caller term) ∧
          instantiateObservation point
              (((Rows.activation state rows (Worlds.closures catalogue captures state) selected output).result
                (Frames.contextual S)).label output) =
            observe (instantiate localPoint (bind (argsToSub arguments) body)) ∧
          Presentation.Intrinsic.read? targetCode context sort
              (observationTree targetCode (instantiateObservation point
                (((Rows.activation state rows (Worlds.closures catalogue captures state) selected output).result
                  (Frames.contextual S)).label output))) =
            some (instantiate localPoint (bind (argsToSub arguments) body)) := by
  have reading : (Worlds.closures catalogue captures state selected).ReadsAt
      (Frames.contextual S) caller (observe (instantiate localPoint (bind (argsToSub arguments) body))) := by
    refine ⟨localPoint, localKnown, captureModel, ?_⟩
    change instantiateObservation localPoint (catalogue selected).value = _
    rw [layout]
    rfl
  have wellFormed := Closure.wellFormed_of_readsAt (Frames.contextual S)
    (Worlds.closures catalogue captures state selected) caller reading
  obtain ⟨admitted, point, model, agrees, named⟩ := Rows.activation_realizes_reading
    state rows (Worlds.closures catalogue captures state) selected output present fresh wellFormed
    caller known (observe (instantiate localPoint (bind (argsToSub arguments) body))) reading
  refine ⟨Syntax.intrinsic_application_readback sourceCode body arguments,
    ⟨selected, output, visible, admitted⟩, rfl, rfl, rfl, point, model, agrees, named, ?_⟩
  have represented := congrArg (fun value : Observation S target.arity =>
    Presentation.Intrinsic.read? targetCode context sort (observationTree targetCode value)) named
  exact represented.trans (Presentation.Intrinsic.read_lower targetCode _)

/-- The source-derived output witness factors through the certified solver
answer on the entire held firing store. Capture equations are included in
that store, so they cannot disappear through the base-rule projection. -/
theorem application_materializes_with_solver
    (sourceCode : Presentation.Intrinsic.HeadPresentation
      (signature S (catalogue selected).locals.arity))
    (layout : (catalogue selected).value = observe (bind (argsToSub arguments) body))
    (visible : (catalogue selected).toRule ∈ program)
    (present : selected ∈ rows) (fresh : output ∉ state.present)
    {target : Frame S} (caller : Assignment state.frame.arity target.arity)
    (known : (Frames.contextual S).Models caller state.knowledge)
    (localPoint : Assignment (catalogue selected).locals.arity target.arity)
    (localKnown : (Frames.contextual S).Models localPoint (catalogue selected).knowledge)
    (captureModel : List.Forall₂ (fun parameter argument =>
      instantiateObservation localPoint parameter = instantiateObservation caller argument)
      (catalogue selected).params (captures state selected))
    (targetCode : Presentation.Intrinsic.HeadPresentation (signature S target.arity))
    {SolverVariables : Type} {solverDeclarations : SolverVariables → MetaArity S}
    {solverContext : Ctx S} {solverSort : S.Srt}
    (problem : EquationStore (Term (signature S
      (Contextual.extend S state.frame (catalogue selected).locals).arity) solverContext solverSort))
    (answer : Assignment (Contextual.extend S state.frame (catalogue selected).locals).arity solverDeclarations)
    (principal : ContextualFrameUnifier.Principal problem answer)
    (included : ∀ equation ∈ Admission.Frames.observedProblem problem,
      equation ∈ (Rows.activation state rows (Worlds.closures catalogue captures state) selected output).information
        (Frames.contextual S)) :
    Syntax.graftAndRead? sourceCode context sort parameters.length
        ((CommonABT.lowerSpine arguments).map (SignatureIndexedABT.mapHeads (sourceCode.view (sort := ()))))
        (Presentation.Intrinsic.lower sourceCode body) = some (bind (argsToSub arguments) body) ∧
      ∃ choice : Worlds.Choice catalogue captures rows program state,
        choice.selected = selected ∧ choice.output = output ∧
        (Worlds.activationEvents catalogue captures rows program).next state choice =
          ((Rows.activation state rows (Worlds.closures catalogue captures state) selected output).result
            (Frames.contextual S)).toState ∧
        ∃ point : Assignment
            (Contextual.extend S state.frame (catalogue selected).locals).arity target.arity,
          (∀ term, (hosted state rows (Worlds.closures catalogue captures state)).Mentions term →
            instantiateObservation point
                (instantiateObservation (Contextual.weakenNames S state.frame (catalogue selected).locals) term) =
              instantiateObservation caller term) ∧
          instantiateObservation point
              (((Rows.activation state rows (Worlds.closures catalogue captures state) selected output).result
                (Frames.contextual S)).label output) =
            observe (instantiate localPoint (bind (argsToSub arguments) body)) ∧
          Presentation.Intrinsic.read? targetCode context sort
              (observationTree targetCode (instantiateObservation point
                (((Rows.activation state rows (Worlds.closures catalogue captures state) selected output).result
                  (Frames.contextual S)).label output))) =
            some (instantiate localPoint (bind (argsToSub arguments) body)) ∧
          ∃ residual : Assignment solverDeclarations target.arity,
            (Frames.contextual S).Models (a := ⟨SolverVariables, solverDeclarations⟩) (b := target) residual
              ((Frames.contextual S).applyStore
                (a := Contextual.extend S state.frame (catalogue selected).locals)
                (b := ⟨SolverVariables, solverDeclarations⟩) answer
                ((Rows.activation state rows (Worlds.closures catalogue captures state) selected output).information
                  (Frames.contextual S))) ∧
            point = Assignment.compose residual answer := by
  obtain ⟨physical, choice, selectedSame, outputSame, nextSame, point, model, agrees, named, readback⟩ :=
    application_materializes catalogue captures rows program state selected output body arguments
      sourceCode layout visible present fresh caller known localPoint localKnown captureModel targetCode
  have fullModel : (Frames.contextual S).Models point
      ((Rows.activation state rows (Worlds.closures catalogue captures state) selected output).information
        (Frames.contextual S)) := model
  obtain ⟨residual, residualModel, factor⟩ :=
    (Admission.Frames.observed_residual_models_iff principal _ included point).mp fullModel
  exact ⟨physical, choice, selectedSame, outputSame, nextSame,
    point, agrees, named, readback, residual, residualModel, factor⟩

end Pipeline

namespace PipelineExample

open Rows.Example (signature nullary ambient locals target atom body closedBody initial caller localPoint)

private instance : DecidableEq signature.Srt := inferInstanceAs (DecidableEq Unit)

private def encodeHead {Names : Type} [Encodable Names] :
    CommonABT.Head (ContextualFamily.signature signature (nullary Names)) → Presentation.Payloads.Head
  | ⟨(), .inl .pair⟩ => .symbol 0
  | ⟨(), .inl .lam⟩ => .symbol 1
  | ⟨(), .inl (.atom value)⟩ => .symbol (value + 2)
  | ⟨(), .inr (.mk name)⟩ => .hole (Encodable.encode name)

private def decodeHead {Names : Type} [Encodable Names] :
    Presentation.Payloads.Head → Option
      (CommonABT.Head (ContextualFamily.signature signature (nullary Names)))
  | .symbol 0 => some ⟨(), .inl .pair⟩
  | .symbol 1 => some ⟨(), .inl .lam⟩
  | .symbol (value + 2) => some ⟨(), .inl (.atom value)⟩
  | .hole code => (Encodable.decode code).map fun name => ⟨(), .inr (.mk name)⟩
  | _ => none

private theorem decode_encode {Names : Type} [Encodable Names] :
    ∀ head : CommonABT.Head (ContextualFamily.signature signature (nullary Names)),
      decodeHead (encodeHead head) = some head
  | ⟨(), .inl .pair⟩ => rfl
  | ⟨(), .inl .lam⟩ => rfl
  | ⟨(), .inl (.atom value)⟩ => rfl
  | ⟨(), .inr (.mk name)⟩ => by simp [encodeHead, decodeHead]

/-- Concrete injective codes for the sample signature, with separate keys
for the source declaration family and the closed output interpretation. -/
def headPresentation (Names : Type) [Encodable Names] (name : String) :
    Presentation.Intrinsic.HeadPresentation (ContextualFamily.signature signature (nullary Names)) where
  key := ⟨name, 1⟩
  view := encodeHead
  expand := decodeHead
  expand_view := decode_encode

def sourceCode := headPresentation Bool "binding-integration.locals"
def targetCode := headPresentation Empty "binding-integration.closed"

/-- A real one-parameter application duplicates a nested binding term. -/
def template : Term (ContextualFamily.signature signature locals.arity) [()] () :=
  .op (.inl .pair) (.cons (.var .zero) (.cons (.var .zero) .nil))

def arguments : Args (ContextualFamily.signature signature locals.arity) [([], ())] [] :=
  .cons body .nil

def applied : Term (ContextualFamily.signature signature locals.arity) [] () :=
  .op (.inl .pair) (.cons body (.cons body .nil))

theorem applied_value : bind (argsToSub arguments) template = applied := rfl

def observedResult (n : Nat) : Term (ContextualFamily.signature signature target.arity) [] () :=
  .op (.inl .pair) (.cons (closedBody 7 n) (.cons (closedBody 7 n) .nil))

def schema : Schema (Contextual.Terms signature) :=
  ⟨locals, [], [observe (generator locals.arity false)], observe applied⟩

def catalogue (_ : Bool) : Schema (Contextual.Terms signature) := schema
def captures := Worlds.anchoredArguments (S := signature) (O := Nat) (fun _ : Bool => [2])
def stored := Worlds.closures catalogue captures initial
def firing := Rows.activation initial ({false, true} : Finset Bool) stored false 0
def result := firing.result (Frames.contextual signature)


theorem physical_application_changes_the_tree :
    Presentation.Intrinsic.lower sourceCode template ≠
      Presentation.Intrinsic.lower sourceCode applied := by decide

theorem physical_application :
    Syntax.graftAndRead? sourceCode [] () 1
      ((CommonABT.lowerSpine (parameters := [()]) (Γ := []) arguments).map (SignatureIndexedABT.mapHeads (sourceCode.view (sort := ()))))
      (Presentation.Intrinsic.lower sourceCode template) = some applied :=
  Syntax.intrinsic_application_readback sourceCode template arguments

/-- The nonidentity physical application is the selected schema value, the
actual world event's output, and the term recovered by typed readback. -/
theorem compiled_application_executes (n : Nat) :
    Syntax.graftAndRead? sourceCode [] () 1
        ((CommonABT.lowerSpine (parameters := [()]) (Γ := []) arguments).map (SignatureIndexedABT.mapHeads (sourceCode.view (sort := ()))))
        (Presentation.Intrinsic.lower sourceCode template) = some applied ∧
      ∃ choice : Worlds.Choice catalogue captures ({false, true} : Finset Bool) {schema.toRule} initial,
        choice.selected = false ∧ choice.output = 0 ∧
        (Worlds.activationEvents catalogue captures {false, true} {schema.toRule}).next initial choice =
          result.toState ∧
        ∃ point : Assignment result.frame.arity target.arity,
          (Frames.contextual signature).Models point result.knowledge ∧
          (∀ term, (hosted initial {false, true} stored).Mentions term →
            instantiateObservation point
              (instantiateObservation (Contextual.weakenNames signature ambient locals) term) =
                instantiateObservation caller term) ∧
          instantiateObservation point (result.label 0) = observe (observedResult n) ∧
          Presentation.Intrinsic.read? targetCode [] ()
              (Pipeline.observationTree targetCode (instantiateObservation point (result.label 0))) =
            some (observedResult n) := by
  have known : (Frames.contextual signature).Models (localPoint n) schema.knowledge := by
    intro equation missing
    cases missing
  have captureModel : List.Forall₂ (fun parameter argument =>
      instantiateObservation (localPoint n) parameter = instantiateObservation caller argument)
      schema.params (captures initial false) := .cons rfl .nil
  exact Pipeline.application_materializes catalogue captures {false, true} {schema.toRule} initial false 0
    template arguments sourceCode rfl (Set.mem_singleton _) (by decide) (by decide)
    caller Rows.Example.initial_known (localPoint n) known captureModel targetCode

def capturedParameter : Term (ContextualFamily.signature signature result.frame.arity) [] () :=
  generator result.frame.arity (Sum.inr false)

def capturedSource : Term (ContextualFamily.signature signature result.frame.arity) [] () :=
  generator result.frame.arity (Sum.inl ())

def captureProblem := [(capturedParameter, capturedSource)]
def captureAnswer : Assignment result.frame.arity result.frame.arity :=
  @ContextualBinding.answer signature (Unit ⊕ Bool) (inferInstance) result.frame.arity
    (Sum.inr false) capturedSource

theorem capture_principal : ContextualFrameUnifier.Principal captureProblem captureAnswer := by
  apply @ContextualUnifierProfiles.binding signature (Unit ⊕ Bool) (inferInstance)
    result.frame.arity (Sum.inr false) capturedSource
  change (Sum.inr false : Unit ⊕ Bool) ∉ [Sum.inl ()]
  intro member
  have impossible := List.mem_singleton.mp member
  cases impossible

theorem capture_is_in_full_information :
    ∀ equation ∈ Admission.Frames.observedProblem captureProblem,
      equation ∈ firing.information (Frames.contextual signature) := by
  intro equation member
  change equation ∈ [(observe capturedParameter, observe capturedSource)] at member
  obtain rfl := List.mem_singleton.mp member
  exact List.mem_singleton_self _

/-- The capture equation really is additional information. Comparing only
the base firing would omit the very equation certified by this solver case. -/
theorem capture_does_not_occur_in_base_information :
    (observe capturedParameter, observe capturedSource) ∉
      firing.base.information (Frames.contextual signature) initial := by
  change (observe capturedParameter, observe capturedSource) ∉ ([] : List _)
  intro impossible
  cases impossible

theorem uncaptured_local_remains_unresolved :
    captureAnswer (Sum.inr true) = generator result.frame.arity (Sum.inr true) :=
  @ContextualBinding.answer_other signature (Unit ⊕ Bool) (inferInstance) result.frame.arity
    (Sum.inr false) (Sum.inr true) (by decide) capturedSource

/-- The actual pipeline's source-derived model factors through elimination
of its capture equation, retaining its same typed, binder-bearing output. -/
theorem compiled_application_with_capture_solver (n : Nat) :
    ∃ residual : Assignment result.frame.arity target.arity,
      (Frames.contextual signature).Models (a := result.frame) (b := target) residual
        ((Frames.contextual signature).applyStore (a := result.frame) (b := result.frame)
          captureAnswer (firing.information (Frames.contextual signature))) ∧
      instantiateObservation (Assignment.compose residual captureAnswer) (result.label 0) =
        observe (observedResult n) ∧
      Presentation.Intrinsic.read? targetCode [] ()
          (Pipeline.observationTree targetCode
            (instantiateObservation (Assignment.compose residual captureAnswer) (result.label 0))) =
        some (observedResult n) := by
  have known : (Frames.contextual signature).Models (localPoint n) schema.knowledge := by
    intro equation missing
    cases missing
  have captureModel : List.Forall₂ (fun parameter argument =>
      instantiateObservation (localPoint n) parameter = instantiateObservation caller argument)
      schema.params (captures initial false) := .cons rfl .nil
  obtain ⟨_, _, _, _, _, point, _, named, readback, residual, model, factor⟩ :=
    Pipeline.application_materializes_with_solver catalogue captures {false, true} {schema.toRule}
      initial false 0 template arguments sourceCode rfl (Set.mem_singleton _) (by decide) (by decide)
      caller Rows.Example.initial_known (localPoint n) known captureModel targetCode
      captureProblem captureAnswer capture_principal capture_is_in_full_information
  refine ⟨residual, model, ?_, ?_⟩
  · have sameOutput := congrArg (fun assignment : Assignment result.frame.arity target.arity =>
        instantiateObservation assignment (result.label 0)) factor
    exact sameOutput.symm.trans named
  · have sameReadback := congrArg (fun assignment : Assignment result.frame.arity target.arity =>
        Presentation.Intrinsic.read? targetCode [] ()
          (Pipeline.observationTree targetCode (instantiateObservation assignment (result.label 0)))) factor
    exact sameReadback.symm.trans readback

end PipelineExample

#print axioms Pipeline.application_materializes
#print axioms Pipeline.application_materializes_with_solver
#print axioms PipelineExample.physical_application_changes_the_tree
#print axioms PipelineExample.compiled_application_executes
#print axioms PipelineExample.capture_does_not_occur_in_base_information
#print axioms PipelineExample.compiled_application_with_capture_solver

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration
