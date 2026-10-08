import Mettapedia.GSLT.LanguageDef.NativeOpsLowering
import Mettapedia.GSLT.LanguageDef.NativeOpsRunComposition
import Mettapedia.GSLT.LanguageDef.NativeOpsScalarObservation
import Mettapedia.GSLT.LanguageDef.NativeOpsSourceComposition

/-!
# Control boundaries of authored native expressions

Successful expression, address and argument lowering produces no outward
label transfer. These syntactic facts connect the actual lowering definitions
to finite target-run composition, including short-circuit branches and array
initialization loops. They do not replace expression or function adequacy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction)
open NativeLowering (Expression Arguments)

/-- The actual argument emitter concatenates the head computation before
the tail, retaining its result atom and the tail's final supply. -/
theorem arguments_lowering_cons_exact (interface : Interface) (scope : Scope)
    (first : Expr) (rest : List Expr) (supply : NativeIR.Supply) (output : Arguments) :
    NativeLowering.arguments? interface scope (first :: rest) supply = some output ↔
      ∃ head tail,
        NativeLowering.expression? interface scope first supply = some head ∧
        NativeLowering.arguments? interface scope rest head.supply = some tail ∧
        output = ⟨head.code ++ tail.code, head.result :: tail.results, tail.supply⟩ := by
  rw [NativeLowering.arguments?]
  constructor
  · intro compiled
    obtain ⟨head, headCompiled, compiled⟩ := Option.bind_eq_some_iff.mp compiled
    obtain ⟨tail, tailCompiled, compiled⟩ := Option.bind_eq_some_iff.mp compiled
    exact ⟨head, tail, headCompiled, tailCompiled, (Option.some.inj compiled).symm⟩
  · rintro ⟨head, tail, headCompiled, tailCompiled, same⟩
    exact Option.bind_eq_some_iff.mpr ⟨head, headCompiled,
      Option.bind_eq_some_iff.mpr ⟨tail, tailCompiled, congrArg some same.symm⟩⟩


theorem jump_free_append (first second : List Instruction) :
    jumpFreeCode (first ++ second) = (jumpFreeCode first && jumpFreeCode second) := by
  induction first with
  | nil => simp only [List.nil_append, jumpFreeCode, Bool.true_and]
  | cons head tail ih =>
      simp only [List.cons_append, jumpFreeCode, ih, Bool.and_assoc]

theorem pure_temporary_jump_free (supply : NativeIR.Supply) (type : NativeType)
    (operation : NativeIR.PureOperation) :
    jumpFreeCode (NativeLowering.pureTemporary supply type operation).code = true := by
  simp only [NativeLowering.pureTemporary, jumpFreeCode, jumpFreeInstruction, Bool.true_and]

theorem reference_checks_jump_free (value : NativeIR.Atom) :
    jumpFreeCode (NativeLowering.checkReference value) = true := by
  simp only [NativeLowering.checkReference, jumpFreeCode, jumpFreeInstruction, Bool.true_and]

theorem numeric_guard_jump_free (operation : Binary) (right : NativeIR.Atom) :
    jumpFreeCode (NativeLowering.numericGuard operation right) = true := by
  cases operation with
  | word operation => cases operation <;> simp only [NativeLowering.numericGuard, jumpFreeCode, jumpFreeInstruction, Bool.true_and]
  | compare operation => simp only [NativeLowering.numericGuard, jumpFreeCode]
  | and => simp only [NativeLowering.numericGuard, jumpFreeCode]
  | or => simp only [NativeLowering.numericGuard, jumpFreeCode]

local macro "finish_leaf_lowering" compiled:ident : tactic => `(tactic| (
  rcases Option.bind_eq_some_iff.mp $compiled with ⟨type, inferred, lowered⟩
  cases Option.some.inj lowered
  simp only [NativeLowering.pureTemporary, jumpFreeCode, jumpFreeInstruction, Bool.true_and]))

mutual
  theorem expression_lowering_jump_free (interface : Interface) (scope : Scope)
      (expression : Expr) (supply : NativeIR.Supply) (output : Expression)
      (compiled : NativeLowering.expression? interface scope expression supply = some output) :
      jumpFreeCode output.code = true := by
    cases expression with
    | word value => rw [NativeLowering.expression?] at compiled; finish_leaf_lowering compiled
    | byte value => rw [NativeLowering.expression?] at compiled; finish_leaf_lowering compiled
    | bool value => rw [NativeLowering.expression?] at compiled; finish_leaf_lowering compiled
    | «variable» name => rw [NativeLowering.expression?] at compiled; finish_leaf_lowering compiled
    | zero type => rw [NativeLowering.expression?] at compiled; finish_leaf_lowering compiled
    | null type => rw [NativeLowering.expression?] at compiled; finish_leaf_lowering compiled
    | new type => rw [NativeLowering.expression?] at compiled; finish_leaf_lowering compiled
    | newArray element count =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨countOutput, countCompiled, compiled⟩
        cases Option.some.inj compiled
        simp only [jump_free_append,
          expression_lowering_jump_free interface scope count supply countOutput countCompiled,
          pure_temporary_jump_free, jumpFreeCode, jumpFreeInstruction, Bool.true_and]
    | field base name =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨baseType, baseInferred, compiled⟩
        cases baseType with
        | named record =>
            rcases Option.bind_eq_some_iff.mp compiled with ⟨baseOutput, baseCompiled, compiled⟩
            rcases Option.bind_eq_some_iff.mp compiled with ⟨index, layout, compiled⟩
            cases Option.some.inj compiled
            simp only [NativeLowering.prependCode, jump_free_append,
              expression_lowering_jump_free interface scope base supply baseOutput baseCompiled,
              pure_temporary_jump_free, Bool.true_and]
        | ref element =>
            cases element with
            | named record =>
                rcases Option.bind_eq_some_iff.mp compiled with ⟨locationOutput, located, compiled⟩
                cases Option.some.inj compiled
                simp only [NativeLowering.prependCode, jump_free_append,
                  location_lowering_jump_free interface scope (.field base name) supply locationOutput located,
                  pure_temporary_jump_free, Bool.true_and]
            | _ => cases compiled
        | _ => cases compiled
    | index array index =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨locationOutput, located, compiled⟩
        cases Option.some.inj compiled
        simp only [NativeLowering.prependCode, jump_free_append,
          location_lowering_jump_free interface scope (.index array index) supply locationOutput located,
          pure_temporary_jump_free, Bool.true_and]
    | load reference =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨locationOutput, located, compiled⟩
        cases Option.some.inj compiled
        simp only [NativeLowering.prependCode, jump_free_append,
          location_lowering_jump_free interface scope (.load reference) supply locationOutput located,
          pure_temporary_jump_free, Bool.true_and]
    | address location =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨locationOutput, located, compiled⟩
        cases Option.some.inj compiled
        simp only [NativeLowering.prependCode, jump_free_append,
          location_lowering_jump_free interface scope location supply locationOutput located,
          pure_temporary_jump_free, Bool.true_and]
    | length array =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨arrayOutput, arrayCompiled, compiled⟩
        cases Option.some.inj compiled
        simp only [NativeLowering.prependCode, jump_free_append,
          expression_lowering_jump_free interface scope array supply arrayOutput arrayCompiled,
          pure_temporary_jump_free, Bool.true_and]
    | slice array start count =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨arrayOutput, arrayCompiled, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨startOutput, startCompiled, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨countOutput, countCompiled, compiled⟩
        cases type with
        | array element =>
            cases Option.some.inj compiled
            simp only [jump_free_append,
              expression_lowering_jump_free interface scope array supply arrayOutput arrayCompiled,
              expression_lowering_jump_free interface scope start arrayOutput.supply startOutput startCompiled,
              expression_lowering_jump_free interface scope count startOutput.supply countOutput countCompiled,
              pure_temporary_jump_free, jumpFreeCode, jumpFreeInstruction, Bool.true_and]
        | _ => cases compiled
    | call name arguments =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨argumentOutput, argumentsCompiled, compiled⟩
        repeat' (first | dsimp only at compiled | split at compiled)
        all_goals cases Option.some.inj compiled
        all_goals simp only [jump_free_append,
            arguments_lowering_jump_free interface scope arguments supply argumentOutput argumentsCompiled,
            jumpFreeCode, jumpFreeInstruction, Bool.true_and]
    | unary operation operand =>
        rw [NativeLowering.expression?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨operandOutput, operandCompiled, compiled⟩
        cases Option.some.inj compiled
        simp only [NativeLowering.prependCode, jump_free_append,
          expression_lowering_jump_free interface scope operand supply operandOutput operandCompiled,
          pure_temporary_jump_free, Bool.true_and]
    | binary operation left right =>
        cases operation with
        | and | or =>
            rw [NativeLowering.expression?] at compiled
            rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
            rcases Option.bind_eq_some_iff.mp compiled with ⟨leftOutput, leftCompiled, compiled⟩
            rcases Option.bind_eq_some_iff.mp compiled with ⟨rightOutput, rightCompiled, compiled⟩
            cases Option.some.inj compiled
            simp only [shortCircuitOutput, jump_free_append,
              expression_lowering_jump_free interface scope left supply leftOutput leftCompiled,
              pure_temporary_jump_free, jumpFreeCode, jumpFreeInstruction,
              expression_lowering_jump_free interface scope right
                (NativeLowering.pureTemporary leftOutput.supply .bool (.copy leftOutput.result)).supply
                rightOutput rightCompiled, Bool.true_and]
        | word operation | compare operation =>
            rw [NativeLowering.expression?] at compiled
            rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
            rcases Option.bind_eq_some_iff.mp compiled with ⟨leftOutput, leftCompiled, compiled⟩
            rcases Option.bind_eq_some_iff.mp compiled with ⟨rightOutput, rightCompiled, compiled⟩
            cases Option.some.inj compiled
            simp only [NativeLowering.prependCode, jump_free_append,
              expression_lowering_jump_free interface scope left supply leftOutput leftCompiled,
              expression_lowering_jump_free interface scope right leftOutput.supply rightOutput rightCompiled,
              numeric_guard_jump_free, pure_temporary_jump_free, Bool.true_and]
  termination_by 2 * sizeOf expression + 1
  decreasing_by
    all_goals subst_vars
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega

  theorem location_lowering_jump_free (interface : Interface) (scope : Scope)
      (location : Expr) (supply : NativeIR.Supply) (output : Expression)
      (compiled : NativeLowering.location? interface scope location supply = some output) :
      jumpFreeCode output.code = true := by
    cases location with
    | «variable» name => rw [NativeLowering.location?] at compiled; finish_leaf_lowering compiled
    | field base name =>
        rw [NativeLowering.location?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨baseType, baseInferred, compiled⟩
        cases baseType with
        | named record =>
            rcases Option.bind_eq_some_iff.mp compiled with ⟨baseOutput, baseCompiled, compiled⟩
            rcases Option.bind_eq_some_iff.mp compiled with ⟨index, layout, compiled⟩
            cases Option.some.inj compiled
            simp only [NativeLowering.prependCode, jump_free_append,
              location_lowering_jump_free interface scope base supply baseOutput baseCompiled,
              pure_temporary_jump_free, Bool.true_and]
        | ref element =>
            cases element with
            | named record =>
                rcases Option.bind_eq_some_iff.mp compiled with ⟨baseOutput, baseCompiled, compiled⟩
                rcases Option.bind_eq_some_iff.mp compiled with ⟨index, layout, compiled⟩
                cases Option.some.inj compiled
                simp only [NativeLowering.prependCode, jump_free_append,
                  expression_lowering_jump_free interface scope base supply baseOutput baseCompiled,
                  reference_checks_jump_free, pure_temporary_jump_free, Bool.true_and]
            | _ => cases compiled
        | _ => cases compiled
    | index array index =>
        rw [NativeLowering.location?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨arrayOutput, arrayCompiled, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨indexOutput, indexCompiled, compiled⟩
        cases Option.some.inj compiled
        simp only [jump_free_append,
          expression_lowering_jump_free interface scope array supply arrayOutput arrayCompiled,
          expression_lowering_jump_free interface scope index arrayOutput.supply indexOutput indexCompiled,
          jumpFreeCode, jumpFreeInstruction, Bool.true_and]
    | load reference =>
        rw [NativeLowering.location?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨referenceOutput, referenceCompiled, compiled⟩
        cases Option.some.inj compiled
        simp only [jump_free_append,
          expression_lowering_jump_free interface scope reference supply referenceOutput referenceCompiled,
          reference_checks_jump_free, Bool.true_and]
    | _ =>
        rw [NativeLowering.location?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, inferred, compiled⟩
        cases compiled
  termination_by 2 * sizeOf location
  decreasing_by
    all_goals subst_vars
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega

  theorem arguments_lowering_jump_free (interface : Interface) (scope : Scope)
      (arguments : List Expr) (supply : NativeIR.Supply) (output : Arguments)
      (compiled : NativeLowering.arguments? interface scope arguments supply = some output) :
      jumpFreeCode output.code = true := by
    cases arguments with
    | nil =>
        rw [NativeLowering.arguments?] at compiled
        cases Option.some.inj compiled
        simp only [jumpFreeCode]
    | cons first rest =>
        rw [NativeLowering.arguments?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨firstOutput, firstCompiled, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨restOutput, restCompiled, compiled⟩
        cases Option.some.inj compiled
        simp only [jump_free_append,
          expression_lowering_jump_free interface scope first supply firstOutput firstCompiled,
          arguments_lowering_jump_free interface scope rest firstOutput.supply restOutput restCompiled,
          Bool.true_and]
  termination_by 2 * sizeOf arguments
  decreasing_by
    all_goals subst_vars
    all_goals simp +unfoldPartialApp +zetaDelta -failIfUnchanged [-Nat.mul_lt_mul_left]
    all_goals omega
end

/-- Argument compilation extends its supply monotonically. An earlier
result remains within the final supply, including unit children that create
no result temporary. This statement concerns the actual recursive emitter. -/
theorem stateful_arguments_bounds (interface : Interface) (scope : Scope)
    (arguments : List Expr)
    (bounds : ∀ expression ∈ arguments, ∀ supply output,
      NativeLowering.expression? interface scope expression supply = some output →
      supply.next ≤ output.supply.next ∧ atomWithin output.supply.next output.result)
    (supply : NativeIR.Supply) (output : NativeLowering.Arguments)
    (compiled : NativeLowering.arguments? interface scope arguments supply = some output) :
    supply.next ≤ output.supply.next ∧
      ∀ atom ∈ output.results, atomWithin output.supply.next atom := by
  induction arguments generalizing supply output with
  | nil =>
      rw [NativeLowering.arguments?] at compiled
      cases Option.some.inj compiled
      exact ⟨Nat.le_refl _, fun _ member => False.elim (List.not_mem_nil member)⟩
  | cons expression rest ih =>
      obtain ⟨head, tail, headCompiled, tailCompiled, same⟩ :=
        (arguments_lowering_cons_exact interface scope expression rest supply output).mp compiled
      subst output
      have headBounds := bounds expression (by simp) supply head headCompiled
      have tailBounds := ih (fun child member => bounds child (by simp [member]))
        head.supply tail tailCompiled
      refine ⟨headBounds.1.trans tailBounds.1, ?_⟩
      intro atom member
      rcases List.mem_cons.mp member with same | member
      · subst atom
        exact atom_within_weaken tailBounds.1 head.result headBounds.2
      · exact tailBounds.2 atom member

/-- Ordered argument evaluation composes complete child post-states. Its
private atom results retain earlier values even when later arguments mutate
memory or the external world. A checked fault skips the remaining suffix. -/
theorem stateful_arguments_forward {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (result : NativeType) (default : TargetValue)
    (arguments : List Expr)
    (children : ∀ expression ∈ arguments, ∀ source, source.fault = none →
      StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
        sourceFrame source result default expression)
    (root : List Instruction) {source : SourceState SourceWorld} (clear : source.fault = none)
    {supply : NativeIR.Supply} {output : NativeLowering.Arguments}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.arguments? interface (sourceFrameScope sourceFrame)
      arguments supply = some output)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {sourceOut : SourceArgumentsOutcome SourceWorld}
    (ran : SourceArgumentsEval interface sourceHeap sourceCalls sourceFrame arguments source sourceOut) :
    ∃ out,
      TargetRun interface targetHeap targetCalls result root output.code targetFrame target out ∧
      CheckedArgumentsRelated worldRelated interface default output.results sourceOut out ∧
      TemporaryProtection supply.next targetFrame out.frame ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame := by
  induction arguments generalizing source supply output targetFrame target sourceOut with
  | nil =>
      rw [NativeLowering.arguments?] at compiled
      cases Option.some.inj compiled
      cases (source_arguments_nil_exact source sourceOut).mp ran
      exact ⟨⟨.normal, targetFrame, target⟩, .nil _ _ _,
        ⟨states, clear, rfl, .nil⟩, temporary_protection_refl _ _, bounded, hscope⟩
  | cons expression rest ih =>
      obtain ⟨head, tail, headCompiled, tailCompiled, same⟩ :=
        (arguments_lowering_cons_exact interface (sourceFrameScope sourceFrame)
          expression rest supply output).mp compiled
      subst output
      have laws := children expression (by simp) source clear
      have tailChildren := fun child (member : child ∈ rest) =>
        children child (List.mem_cons_of_mem expression member)
      have headBounds := laws.bounds headCompiled
      have tailBounds := stateful_arguments_bounds interface (sourceFrameScope sourceFrame)
        rest (fun child member _ _ emitted =>
          (tailChildren child member source clear).bounds emitted)
        head.supply tail tailCompiled
      have jumpFree := expression_lowering_jump_free interface (sourceFrameScope sourceFrame)
        expression supply head headCompiled
      cases ran with
      | @cons _ _ value _ sourceMiddle tailOut firstRun restRun =>
          obtain ⟨middle, firstTarget, related, headProtection, headBounded, headScoped⟩ :=
            laws.forward root headCompiled frames states bounded hscope firstRun
          rcases middle with ⟨flow, middleFrame, middleState⟩
          rcases related with ⟨middleRelated, middleClear, normal, firstRead⟩
          change flow = .normal at normal
          subst flow
          obtain ⟨out, restTarget, restRelated, tailProtection, finalBounded, finalScoped⟩ :=
            ih tailChildren middleClear tailCompiled
              (temporary_protection_preserves_source_frame frames headProtection)
              middleRelated headBounded headScoped restRun
          refine ⟨out, target_append_normal root head.code tail.code jumpFree firstTarget restTarget,
            ?_, temporary_protection_trans headProtection (temporary_protection_weaken headBounds.1 tailProtection),
            finalBounded, finalScoped⟩
          rcases restRelated with ⟨finalRelated, restRelated⟩
          rcases tailOut with ⟨answer, post⟩
          cases answer with
          | ok values =>
              rcases restRelated with ⟨finalClear, finalNormal, restRead⟩
              refine ⟨finalRelated, ?_, finalNormal, ?_⟩
              · exact finalClear
              · exact .cons
                  ((protection_atom_evaluation tailProtection head.result headBounds.2
                    middleState out.state _).mp firstRead) restRead
          | error fault =>
              exact ⟨finalRelated, restRelated⟩
      | consFault firstRun =>
          obtain ⟨out, firstTarget, related, protection, headBounded, finalScoped⟩ :=
            laws.forward root headCompiled frames states bounded hscope firstRun
          rcases related with ⟨postRelated, fault, returned⟩
          refine ⟨out, ?_, ⟨postRelated, fault, returned⟩, protection,
            temporary_names_bound_weaken tailBounds.1 headBounded, finalScoped⟩
          cases out with
          | mk flow frame state =>
              change flow = .returned default at returned
              subst flow
              exact target_append_returned root head.code tail.code jumpFree firstTarget

/-- Reflection retains every target argument effect and every checked early
return. No target suffix execution is admitted after a reflected first fault. -/
theorem stateful_arguments_reflection {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (result : NativeType) (default : TargetValue)
    (arguments : List Expr)
    (children : ∀ expression ∈ arguments, ∀ source, source.fault = none →
      StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
        sourceFrame source result default expression)
    (root : List Instruction) {source : SourceState SourceWorld} (clear : source.fault = none)
    {supply : NativeIR.Supply} {output : NativeLowering.Arguments}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (compiled : NativeLowering.arguments? interface (sourceFrameScope sourceFrame)
      arguments supply = some output)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {out : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result root output.code targetFrame target out) :
    ∃ sourceOut,
      SourceArgumentsEval interface sourceHeap sourceCalls sourceFrame arguments source sourceOut ∧
      CheckedArgumentsRelated worldRelated interface default output.results sourceOut out ∧
      TemporaryProtection supply.next targetFrame out.frame ∧
      TemporaryNamesBound out.frame output.supply.next ∧ TemporariesScoped out.frame := by
  induction arguments generalizing source supply output targetFrame target out with
  | nil =>
      rw [NativeLowering.arguments?] at compiled
      cases Option.some.inj compiled
      cases ran
      exact ⟨⟨.ok [], source⟩, .nil _, ⟨states, clear, rfl, .nil⟩,
        temporary_protection_refl _ _, bounded, hscope⟩
  | cons expression rest ih =>
      obtain ⟨head, tail, headCompiled, tailCompiled, same⟩ :=
        (arguments_lowering_cons_exact interface (sourceFrameScope sourceFrame)
          expression rest supply output).mp compiled
      subst output
      have laws := children expression (by simp) source clear
      have tailChildren := fun child (member : child ∈ rest) =>
        children child (List.mem_cons_of_mem expression member)
      have headBounds := laws.bounds headCompiled
      have tailBounds := stateful_arguments_bounds interface (sourceFrameScope sourceFrame)
        rest (fun child member _ _ emitted => (tailChildren child member source clear).bounds emitted)
        head.supply tail tailCompiled
      have jumpFree := expression_lowering_jump_free interface (sourceFrameScope sourceFrame)
        expression supply head headCompiled
      rcases (target_run_append_exact interface targetHeap targetCalls result root head.code tail.code
        jumpFree targetFrame target out).mp ran with
        ⟨middleFrame, middleState, firstTarget, restTarget⟩ |
        ⟨returnedValue, finalFrame, finalState, firstTarget, same⟩
      · obtain ⟨firstSource, firstRun, related, headProtection, headBounded, headScoped⟩ :=
          laws.backward root headCompiled frames states bounded hscope firstTarget
        rcases firstSource with ⟨answer, middleSource⟩
        obtain ⟨value, success, middleClear, middleRelated, firstRead⟩ :=
          checked_result_normal related rfl
        cases success
        obtain ⟨restSource, restRun, restRelated, tailProtection, finalBounded, finalScoped⟩ :=
          ih tailChildren middleClear tailCompiled
            (temporary_protection_preserves_source_frame frames headProtection)
            middleRelated headBounded headScoped restTarget
        refine ⟨⟨restSource.result.map (value :: ·), restSource.state⟩,
          .cons firstRun restRun, ?_,
          temporary_protection_trans headProtection (temporary_protection_weaken headBounds.1 tailProtection),
          finalBounded, finalScoped⟩
        rcases restRelated with ⟨finalRelated, restRelated⟩
        rcases restSource with ⟨answer, post⟩
        cases answer with
        | ok values =>
            rcases restRelated with ⟨finalClear, finalNormal, restRead⟩
            exact ⟨finalRelated, finalClear, finalNormal, .cons
              ((protection_atom_evaluation tailProtection head.result headBounds.2
                middleState out.state _).mp firstRead) restRead⟩
        | error fault => exact ⟨finalRelated, restRelated⟩
      · subst out
        obtain ⟨firstSource, firstRun, related, protection, headBounded, finalScoped⟩ :=
          laws.backward root headCompiled frames states bounded hscope firstTarget
        rcases firstSource with ⟨answer, post⟩
        obtain ⟨fault, failure, failed, finalRelated, defaultValue⟩ :=
          checked_result_returned related rfl
        cases failure
        cases defaultValue
        exact ⟨⟨.error fault, post⟩, .consFault firstRun, ⟨finalRelated, failed, rfl⟩,
          protection, temporary_names_bound_weaken tailBounds.1 headBounded, finalScoped⟩

theorem arguments_lowering_pair (interface : Interface) (scope : Scope) (left right : Expr)
    {supply : NativeIR.Supply} {first second : NativeLowering.Expression}
    (firstCompiled : NativeLowering.expression? interface scope left supply = some first)
    (secondCompiled : NativeLowering.expression? interface scope right first.supply = some second) :
    NativeLowering.arguments? interface scope [left, right] supply =
      some ⟨first.code ++ second.code, [first.result, second.result], second.supply⟩ := by
  apply (arguments_lowering_cons_exact interface (scope) left [right] supply _).mpr
  refine ⟨first, ⟨second.code, [second.result], second.supply⟩, firstCompiled, ?_, rfl⟩
  apply (arguments_lowering_cons_exact interface (scope) right [] first.supply _).mpr
  exact ⟨second, ⟨[], [], second.supply⟩, secondCompiled, (by rw [NativeLowering.arguments?]), by simp only [List.append_nil]⟩

theorem target_two_encoded_arguments {World : Type} {interface : Interface} {frame : TargetFrame} {state : TargetState World}
    {a b : NativeIR.Atom} {values : List SourceValue}
    (read : TargetAtomsEval interface frame state [a, b] (encodeValues values)) :
    ∃ first second, values = [first, second] ∧
      TargetAtomEval interface frame state a (encodeValue first) ∧
      TargetAtomEval interface frame state b (encodeValue second) := by
  cases values with
  | nil => cases read
  | cons first rest =>
      cases rest with
      | nil => cases read with | cons _ impossible => cases impossible
      | cons second tail =>
          cases tail with
          | nil =>
              cases read with
              | cons readLeft remaining =>
                  cases remaining with
                  | cons readRight _ => exact ⟨first, second, rfl, readLeft, readRight⟩
          | cons third tail =>
              cases read with
              | cons _ remaining =>
                  cases remaining with
                  | cons _ impossible => cases impossible

/-- The actual recursive argument emitter and a checked primitive suffix
compose in both directions. Effects remain ordered, earlier private values
remain protected, and the first argument fault skips the primitive. -/
theorem stateful_strict_child_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (sourceFrame : SourceFrame) (source : SourceState SourceWorld) (clear : source.fault = none)
    (result : NativeType) (default : TargetValue) (expression : Expr) (arguments : List Expr)
    (operands : sourceStrictOperands? expression = some arguments)
    (children : ∀ child ∈ arguments, ∀ before, before.fault = none →
      StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
        sourceFrame before result default child)
    (emitted : ∀ {supply : NativeIR.Supply} {output : NativeLowering.Expression},
      NativeLowering.expression? interface (sourceFrameScope sourceFrame) expression supply = some output →
      ∃ argumentOutput suffix,
        NativeLowering.arguments? interface (sourceFrameScope sourceFrame) arguments supply = some argumentOutput ∧
        output = NativeLowering.prependCode argumentOutput.code suffix ∧
        StatefulPrimitiveLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
          sourceFrame source result default expression arguments argumentOutput suffix) :
    StatefulChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default expression := by
  have argumentBounds (supply : NativeIR.Supply) (argumentOutput : NativeLowering.Arguments)
      (compiled : NativeLowering.arguments? interface (sourceFrameScope sourceFrame)
        arguments supply = some argumentOutput) : supply.next ≤ argumentOutput.supply.next :=
    (stateful_arguments_bounds interface (sourceFrameScope sourceFrame) arguments
      (fun child member _ _ compiled => (children child member source clear).bounds compiled)
      supply argumentOutput compiled).1
  refine ⟨?_, ?_, ?_⟩
  · intro supply output compiled
    obtain ⟨argumentOutput, suffix, argsCompiled, same, primitive⟩ := emitted compiled
    subst output
    exact ⟨(argumentBounds supply argumentOutput argsCompiled).trans primitive.bounds.1, primitive.bounds.2⟩
  · intro root supply output frame target compiled frames states bounded hscope sourceOut ran
    obtain ⟨argumentOutput, suffix, argsCompiled, same, primitive⟩ := emitted compiled
    subst output
    have grew := argumentBounds supply argumentOutput argsCompiled
    have jumpFree := arguments_lowering_jump_free interface (sourceFrameScope sourceFrame)
      arguments supply argumentOutput argsCompiled
    rcases (source_strict_expression_exact expression arguments operands source sourceOut).mp ran with
      ⟨values, middle, argsRan, primitiveRan⟩ | ⟨fault, post, argsRan, same⟩
    · obtain ⟨⟨flow, middleFrame, middleState⟩, targetArgs, related, protection, middleBounded, middleScoped⟩ :=
        stateful_arguments_forward worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
          sourceFrame result default arguments children root clear argsCompiled frames states bounded hscope argsRan
      rcases related with ⟨postRelated, middleClear, normal, reads⟩
      change flow = .normal at normal
      subst flow
      obtain ⟨out, targetPrimitive, checked, tailProtection, finalBounded, finalScoped⟩ :=
        primitive.forward root argsRan middleClear
          (temporary_protection_preserves_source_frame frames protection) postRelated
          middleBounded middleScoped reads primitiveRan
      exact ⟨out, target_append_normal root argumentOutput.code suffix.code jumpFree targetArgs targetPrimitive,
        checked, temporary_protection_trans protection (temporary_protection_weaken grew tailProtection),
        finalBounded, finalScoped⟩
    · subst sourceOut
      obtain ⟨⟨flow, postFrame, postState⟩, targetArgs, related, protection, postBounded, postScoped⟩ :=
        stateful_arguments_forward worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
          sourceFrame result default arguments children root clear argsCompiled frames states bounded hscope argsRan
      rcases related with ⟨postRelated, failed, returned⟩
      change flow = .returned default at returned
      subst flow
      exact ⟨⟨.returned default, postFrame, postState⟩,
        target_append_returned root argumentOutput.code suffix.code jumpFree targetArgs,
        ⟨postRelated, failed, rfl⟩, protection,
        temporary_names_bound_weaken primitive.bounds.1 postBounded, postScoped⟩
  · intro root supply output frame target compiled frames states bounded hscope out ran
    obtain ⟨argumentOutput, suffix, argsCompiled, same, primitive⟩ := emitted compiled
    subst output
    have grew := argumentBounds supply argumentOutput argsCompiled
    have jumpFree := arguments_lowering_jump_free interface (sourceFrameScope sourceFrame)
      arguments supply argumentOutput argsCompiled
    rcases (target_run_append_exact interface targetHeap targetCalls result root argumentOutput.code suffix.code
      jumpFree frame target out).mp ran with
      ⟨middleFrame, middleState, targetArgs, targetPrimitive⟩ |
      ⟨returnedValue, postFrame, postState, targetArgs, same⟩
    · obtain ⟨sourceArgs, argsRan, related, protection, middleBounded, middleScoped⟩ :=
        stateful_arguments_reflection worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
          sourceFrame result default arguments children root clear argsCompiled frames states bounded hscope targetArgs
      obtain ⟨values, success, middleClear, postRelated, reads⟩ := checked_result_normal related rfl
      rcases sourceArgs with ⟨answer, middle⟩
      cases success
      obtain ⟨sourceOut, primitiveRan, checked, tailProtection, finalBounded, finalScoped⟩ :=
        primitive.backward root argsRan middleClear
          (temporary_protection_preserves_source_frame frames protection) postRelated
          middleBounded middleScoped reads targetPrimitive
      exact ⟨sourceOut, .strict operands argsRan primitiveRan, checked,
        temporary_protection_trans protection (temporary_protection_weaken grew tailProtection),
        finalBounded, finalScoped⟩
    · subst out
      obtain ⟨sourceArgs, argsRan, related, protection, postBounded, postScoped⟩ :=
        stateful_arguments_reflection worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
          sourceFrame result default arguments children root clear argsCompiled frames states bounded hscope targetArgs
      obtain ⟨fault, failed, faulted, postRelated, returned⟩ := checked_result_returned related rfl
      rcases sourceArgs with ⟨answer, post⟩
      cases failed
      cases returned
      exact ⟨⟨.error fault, post⟩, .strictFault operands argsRan,
        ⟨postRelated, faulted, rfl⟩, protection,
        temporary_names_bound_weaken primitive.bounds.1 postBounded, postScoped⟩

theorem arguments_lowering_single (interface : Interface) (scope : Scope) (argument : Expr)
    {supply : NativeIR.Supply} {child : NativeLowering.Expression}
    (compiled : NativeLowering.expression? interface scope argument supply = some child) :
    NativeLowering.arguments? interface scope [argument] supply =
      some ⟨child.code, [child.result], child.supply⟩ := by
  apply (arguments_lowering_cons_exact interface scope argument [] supply _).mpr
  exact ⟨child, ⟨[], [], child.supply⟩, compiled, (by rw [NativeLowering.arguments?]),
    by simp only [List.append_nil]⟩

theorem target_one_encoded_argument {World : Type} {interface : Interface} {frame : TargetFrame}
    {state : TargetState World} {atom : NativeIR.Atom} {values : List SourceValue}
    (read : TargetAtomsEval interface frame state [atom] (encodeValues values)) :
    ∃ value, values = [value] ∧ TargetAtomEval interface frame state atom (encodeValue value) := by
  cases values with
  | nil => cases read
  | cons first rest =>
      cases rest with
      | nil => cases read with | cons firstRead _ => exact ⟨first, rfl, firstRead⟩
      | cons second rest => cases read with | cons _ impossible => cases impossible

theorem arguments_lowering_triple (interface : Interface) (scope : Scope) (a b c : Expr)
    {supply : NativeIR.Supply} {first second third : NativeLowering.Expression}
    (firstCompiled : NativeLowering.expression? interface scope a supply = some first)
    (secondCompiled : NativeLowering.expression? interface scope b first.supply = some second)
    (thirdCompiled : NativeLowering.expression? interface scope c second.supply = some third) :
    NativeLowering.arguments? interface scope [a, b, c] supply =
      some ⟨first.code ++ second.code ++ third.code, [first.result, second.result, third.result], third.supply⟩ := by
  apply (arguments_lowering_cons_exact interface scope a [b, c] supply _).mpr
  exact ⟨first, ⟨second.code ++ third.code, [second.result, third.result], third.supply⟩,
    firstCompiled, arguments_lowering_pair interface scope b c secondCompiled thirdCompiled,
    by simp only [List.append_assoc]⟩

theorem target_three_encoded_arguments {World : Type} {interface : Interface}
    {frame : TargetFrame} {state : TargetState World} {a b c : NativeIR.Atom} {values : List SourceValue}
    (read : TargetAtomsEval interface frame state [a, b, c] (encodeValues values)) :
    ∃ first second third, values = [first, second, third] ∧
      TargetAtomEval interface frame state a (encodeValue first) ∧
      TargetAtomEval interface frame state b (encodeValue second) ∧
      TargetAtomEval interface frame state c (encodeValue third) := by
  cases values with
  | nil => cases read
  | cons first rest =>
      cases read with
      | cons head tail =>
          obtain ⟨second, third, same, readSecond, readThird⟩ := target_two_encoded_arguments tail
          subst rest
          exact ⟨first, second, third, rfl, head, readSecond, readThird⟩

end Mettapedia.GSLT.LanguageDef.NativeOps
