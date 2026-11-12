import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AnnotatedRunsFormedFrame
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormedAppend

/-!
# The joined theorem: a formed source program, compiled, executed, and certified by its own run

## The theorem (`formed_certified_execution`)

Its hypotheses are actual objects:

* a **compiled program** for the theory (`CompiledProgram`): callables, operations, and compiled
  rules each carrying a certificate checked on its schema;
* the **compilation of the source** (`compile`): the compiler reads the source term and gives the
  compiled term;
* the **compiled start**: one occurrence labelled with the compiled term, to be told to the result
  variable, and no equations;
* a **run of compiled steps** (`CompiledStep`): every firing is an instance of a compiled rule,
  separated from a client run in the sense of R26's partial tensor (the client may be empty,
  `separated_alone`);
* an accepted **result check** (`checkResult`) under the theory's value discipline: the unifier's
  answer for the result variable reads back as the target, a value, and leaves the context
  unbound;
* the **run's certificate** exists (`runCertificate`): it is produced from the run's firings and
  the unifier's answer, with no search;
* the target's **formation**: a formed type, the target typed at it, and the source's type
  converted to it.

Its conclusions are derived:

* **formed evidence whose term certificate is produced by the run**: the compiler's entry
  certificate (the telescope's beta steps of the call) followed by the run's certificate, checked
  by the Flower's checker through per-rule soundness (`certify_sound`);
* the target is a **value**, a normal form of the theory (`IsValue.no_step`);
* everything result checking gives (`checked_result_joined`): the run's and the tensor's final
  stores observe an answer reading back as the target; the source is retyped at the target's
  formed type; source and target are one `QTerm` class; the run's history carries the evidence in
  R28's evidence fibration.

## Result checking, kept apart

`checked_result_joined` is the earlier statement: an accepted check and any formed evidence for
the checked target. Nothing in it relates the run to the source. Probes C and E
(`CompilationControls`) meet its hypotheses with a run that does not execute the program, and probe
C's conclusion is derived; both violate the certifying theorem's hypotheses. Probes A and B
(`ValueControls`), an eliminator redex and an unevaluated declared call, are refused by readback.

## Consumers

* `projection_joined`, `projection_joined_with_client`: the Sigma/wire projection, alone and beside
  an unrelated copy.
* `append_joined`: dependent vector append, three compiled steps.
* For every wire, the projection is certified in `AnnotatedRunsFormedWires`
  (`projection_joined_every_wire`); the substitution square is in `AnnotatedRunsFormedSquare`.

## What descends, and what does not

* Formation and the semantic value descend (`projection_descends`).
* Witness identity and cost stay in the richer fibre (`two_evidence_objects_one_history`,
  `cost_not_a_function_of_class`, `Append.append_source_steps`).
* The extension by the declared append adds a name (`extension_adds_name`); the name unfolds to a
  base term by a checked delta step, so this does not show that interpretation is one-way.

## Readout and fuel

The readout of a history (`unifierReadout`) runs the unifier with a stated fuel. Below the
unifier's need the store has no answer: the projection's store has none at fuel 7 and is checked
at fuel 8 (`incomplete_checking_grants_no_authority`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed

open _root_.CategoryTheory
open Mettapedia.Logic.LP
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation (Tm StepCore)
open Presentation.FormationSensitiveContextual (Context TypeOver Term TotalTerm QTerm empty)
open Presentation.StructuralConversionCode (RootDecoder Certificate Code)
open AnnotatedRuns
open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath)

/-! ## The readout of histories -/

/-- **The unifier's readout of a history**: solve the store the history leaves with the stated
fuel and read the result variable through the answer. It depends on the fuel. -/
def unifierReadout {Head : Type} {n : Nat} (canonical : Presentation.DeclName → Bool)
    (label : Nat → Pattern) (start : Configuration Pattern Nat) (fuel result : Nat) :
    ∀ {x : Runs action label}, (runObject action label start ⟶ x) → Option (Tm Head n) :=
  fun h =>
    match unifyFuel fuel (follow label start (OccurrencePath.sites h)).equations with
    | some θ => readback canonical (θ result)
    | none => none

theorem readout_of_check {Head : Type} [DecidableEq Head] {n : Nat}
    {canonical : Presentation.DeclName → Bool} {fuel result : Nat}
    {store : EquationStore Pattern} {target : Tm Head n}
    (checked : checkResult canonical fuel store result target = true) :
    (match unifyFuel fuel store with
      | some θ => readback canonical (θ result)
      | none => none) = some target := by
  obtain ⟨θ, accepted, read, _⟩ := checkResult_answer checked
  rw [accepted]
  exact read

/-- A run alone is separated from the empty client. -/
theorem separated_alone {label : Nat → Pattern} {start : Configuration Pattern Nat}
    {run : List (Firing Pattern (Subst signature) Nat)} (executes : Executable action label start run) :
    Separated action label start run unitConfiguration [] where
  left := executes
  right := ⟨Subst.id signature, fun _ member => (List.not_mem_nil member).elim⟩
  apart := by simp [space, madeBy, unitConfiguration]
  leftBlind _ _ := ⟨fun _ _ _ _ _ _ member => by simp [space, madeBy, unitConfiguration] at member,
    fun _ _ _ _ member => by simp [space, madeBy, unitConfiguration] at member⟩
  rightBlind _ member := (List.not_mem_nil member).elim
  joint := by
    obtain ⟨σ, solved⟩ := Executable.joint action label executes
    exact ⟨σ, by simpa [jointStore, jointProblem, unitConfiguration] using solved⟩

/-! ## Result checking -/

section Joined

variable {Head : Type} [DecidableEq Head] {R : Presentation.Rules Head} [DecidableRel R.headEq]

/-- The conclusion of result checking. -/
def JoinedConclusion (decoder : RootDecoder R.computation) (canonical : Presentation.DeclName → Bool)
    (context : Context R) (source : TotalTerm context) (label : Nat → Pattern)
    (start clientStart : Configuration Pattern Nat)
    (run client : List (Firing Pattern (Subst signature) Nat)) (fuel result : Nat)
    (target : Tm Head context.arity) (evidence : FormedEvidence decoder context source target) : Prop :=
  (∃ answer, readback canonical answer = some target ∧
    Observes action (follow label start run).equations (.var result) answer ∧
    Observes action (follow label (tensor start clientStart) (run ++ client)).equations (.var result) answer) ∧
    Executable action label (tensor start clientStart) (run ++ client) ∧
    action.Consistent (follow label (tensor start clientStart) (run ++ client)).equations ∧
    Presentation.FormationSensitive.Judgment R context.raw source.2.code evidence.targetType.code ∧
    Presentation.FormationSensitive.Judgment R context.raw target evidence.targetType.code ∧
    QTerm.mk source.2 = QTerm.mk evidence.targetTerm ∧
    ∃ history : runObject action label start ⟶ classOf action label (follow label start run),
      OccurrencePath.sites history = run ∧
      Nonempty (formedFiber (runObject action label start) decoder context source
        (unifierReadout canonical label start fuel result)
        (classOf action label (follow label start run)) history)

/-- **Result checking.** From a run separated from a client, an accepted result check and formed
evidence for the checked target: the run and the tensor run observe an answer reading back as the
target; the source is retyped at the target's formed type and is in the target's `QTerm` class;
and the run's history carries the evidence. Nothing relates the run to the source except the
shared target: see `formed_certified_execution` for the certifying statement. -/
theorem checked_result_joined (decoder : RootDecoder R.computation)
    (canonical : Presentation.DeclName → Bool) {context : Context R} {source : TotalTerm context}
    {label : Nat → Pattern} {start clientStart : Configuration Pattern Nat}
    {run client : List (Firing Pattern (Subst signature) Nat)}
    (separated : Separated action label start run clientStart client)
    {fuel result : Nat} {target : Tm Head context.arity}
    (certified : checkResult canonical fuel (follow label start run).equations result target = true)
    (evidence : FormedEvidence decoder context source target) :
    JoinedConclusion decoder canonical context source label start clientStart run client fuel result
      target evidence := by
  obtain ⟨_, answer, readout, observed⟩ := checkResult_sound certified
  obtain ⟨executes, consistent, tensorObserved⟩ := observes_tensor action label separated observed
  obtain ⟨history, sites⟩ := exists_path action label start run separated.left _ rfl
  refine ⟨⟨answer, readout, observed, tensorObserved⟩, executes, consistent, evidence.retyped,
    evidence.targetJudgment, evidence.class_eq, history, sites, ⟨⟨⟨target, ?_⟩, evidence⟩⟩⟩
  change (match unifyFuel fuel (follow label start (OccurrencePath.sites history)).equations with
    | some θ => readback canonical (θ result)
    | none => none) = some target
  rw [sites]
  exact readout_of_check certified

/-! ## The certifying theorem -/

/-- **The run's certificate**: the certificate the run produces for its program occurrence, at
the unifier's answer for the run's final store. -/
def runCertificate {decoder : RootDecoder R.computation} (program : CompiledProgram R decoder)
    (rootAction : RootAction decoder) {n : Nat} (fuel : Nat) (label : Nat → Pattern)
    (start : Configuration Pattern Nat) (steps : List (CompiledStep program)) (o : Nat) :
    Option (Code Head decoder.Code n) :=
  match unifyFuel fuel (follow label start (steps.map CompiledStep.firing)).equations with
  | some θ => certify program rootAction θ steps o
  | none => none

/-- The conclusion of certifying execution: the run's certificate, formed evidence whose term
certificate is the compiler's entry followed by the run's certificate, the target a value and a
normal form, and everything result checking gives. -/
def CertifiedConclusion (decoder : RootDecoder R.computation) (discipline : ValueDiscipline R)
    (program : CompiledProgram R decoder) (rootAction : RootAction decoder) (context : Context R)
    (source : TotalTerm context) (label : Nat → Pattern) (o : Nat)
    (clientStart : Configuration Pattern Nat) (steps : List (CompiledStep program))
    (client : List (Firing Pattern (Subst signature) Nat)) (fuel result : Nat)
    (target : Tm Head context.arity) : Prop :=
  ∃ code, runCertificate program rootAction fuel label (compiledStart o) steps o = some code ∧
    ∃ evidence : FormedEvidence decoder context source target,
      (∃ entry, evidence.termCertificate.code = Code.trans entry code) ∧
      IsValue discipline.canonical target ∧
      (∀ next, ¬ StepCore R.computation R.headEq target next) ∧
      JoinedConclusion decoder discipline.canonical context source label (compiledStart o)
        clientStart (steps.map CompiledStep.firing) client fuel result target evidence

/-- **The joined theorem: a formed source program, compiled, executed as compiled rules, gives a
value whose certificate the run itself produces.** The compiler reads the source; the run starts
from the compiled start and fires only compiled rules; its final store is checked under the
theory's value discipline; and the run's certificate, built from its firings through per-rule
soundness, converts the source to the result. -/
theorem formed_certified_execution {decoder : RootDecoder R.computation}
    (discipline : ValueDiscipline R) (program : CompiledProgram R decoder)
    (rootAction : RootAction decoder) {context : Context R} {source : TotalTerm context}
    {compiledTerm : Pattern}
    (compiled : compile discipline.canonical program.callables source.2.code = some compiledTerm)
    {label : Nat → Pattern} {o r : Nat} (labelled : label o = evaluate compiledTerm (.var r))
    {steps : List (CompiledStep program)} {clientStart : Configuration Pattern Nat}
    {client : List (Firing Pattern (Subst signature) Nat)}
    (separated : Separated action label (compiledStart o) (steps.map CompiledStep.firing)
      clientStart client)
    {fuel : Nat} {target : Tm Head context.arity}
    (checked : checkResult discipline.canonical fuel
      (follow label (compiledStart o) (steps.map CompiledStep.firing)).equations r target = true)
    (produced : (runCertificate program rootAction fuel label (compiledStart o) steps o :
      Option (Code Head decoder.Code context.arity)).isSome = true)
    (targetType : TypeOver context) (targetTerm : Term context targetType)
    (target_code : targetTerm.code = target)
    (typeCertificate : Certificate R.headEq decoder.decode source.1.code targetType.code) :
    CertifiedConclusion decoder discipline program rootAction context source label o clientStart
      steps client fuel r target := by
  obtain ⟨code, producedCode⟩ := Option.isSome_iff_exists.mp produced
  obtain ⟨θ, accepted, read, fixes⟩ := checkResult_answer checked
  have certifiedCode : certify program rootAction θ steps o = some code := by
    unfold runCertificate at producedCode
    rw [accepted] at producedCode
    exact producedCode
  have solvesStore : action.Models θ
      (follow label (compiledStart o) (steps.map CompiledStep.firing)).equations :=
    unifyFuel_sound fuel _ θ accepted
  have solves : ∀ step ∈ steps, action.Models θ (step.firing.added label) := by
    intro step member equation inside
    apply solvesStore
    rw [follow_equations]
    exact List.mem_append_right _
      (List.mem_flatMap.mpr ⟨step.firing, List.mem_map_of_mem member, inside⟩)
  have made : ∀ step ∈ steps, step.made.map label = (step.rule.instantiate step.rename).produce := by
    intro step member
    obtain ⟨_, valid⟩ := Executable.valid_of_mem action label separated.left step.firing
      (List.mem_map_of_mem member)
    exact valid.firing.outputs
  obtain ⟨term, result, left, right, labelledθ, denotedTerm, denotedResult, codeChecked⟩ :=
    certify_sound θ label steps solves made o code certifiedCode
  rw [labelled, applyTerm_evaluate, compile_fixed compiled θ fixes] at labelledθ
  obtain ⟨termSame, resultSame⟩ := evaluate_injective labelledθ
  obtain ⟨sourceDenoted, entry, denotedCompiled, entryChecked⟩ :=
    compile_sound program.operations program.callables_denoted R.headEq decoder.decode compiled
  have leftSame : left = sourceDenoted := by
    rw [← termSame, denotedCompiled] at denotedTerm
    exact (Option.some.inj denotedTerm).symm
  have rightSame : right = target := by
    rw [← resultSame] at denotedResult
    have fromReadback := denote_of_readback program.operations discipline.canonical _ read
    change denote program.operations (θ r) = some right at denotedResult
    rw [fromReadback] at denotedResult
    exact (Option.some.inj denotedResult).symm
  subst leftSame rightSame
  have termChecked : (Code.trans entry code).check R.headEq decoder.decode source.2.code
      targetTerm.code = true := by
    rw [target_code]
    exact Presentation.StructuralConversionCode.Code.check_trans R.headEq decoder.decode
      entryChecked codeChecked
  let evidence : FormedEvidence decoder context source right :=
    ⟨targetType, targetTerm, target_code, typeCertificate, ⟨Code.trans entry code, termChecked⟩⟩
  have value := readback_isValue discipline.canonical _ read
  exact ⟨code, producedCode, evidence, ⟨entry, rfl⟩, value,
    fun next => IsValue.no_step discipline value,
    checked_result_joined decoder discipline.canonical separated checked evidence⟩

end Joined

/-! ## The consumers -/

namespace Consumers

open Projection

/-- The projection's compiled run, as compiled steps. -/
theorem projection_run :
    [projectionStep 1 2 3 0].map CompiledStep.firing = [projectionFiring] := by
  rw [List.map_singleton, projectionFiringAt_compiled]

/-- **The certifying joined theorem for the formed Sigma/wire projection.** -/
theorem projection_joined :
    CertifiedConclusion holDecoder holDiscipline projectionProgram holRootAction (empty rules)
      (projectionSource exampleWire) (programLabel (program exampleWire)) 0 unitConfiguration
      [projectionStep 1 2 3 0] [] 16 0 (NativeWireData.encode exampleWire) := by
  have executes := (projection_square exampleWire).2.1
  refine formed_certified_execution holDiscipline projectionProgram holRootAction
    (compile_source exampleWire) rfl (separated_alone executes) ?_ ?_ dataTypeOver
    (valueTerm exampleWire) rfl (Certificate.refl _)
  · rw [projection_run]
    exact example_certified
  · decide +kernel

/-- The result check of the projection under the shared label of the frame controls. -/
theorem frame_certified :
    checkResult holCanonical 16 (follow FrameControls.frameLabel (startAt 0) FrameControls.certified).equations 0
      (NativeWireData.encode (n := 0) exampleWire) = true := by
  decide +kernel

/-- **The certifying joined theorem for the projection beside an unrelated client.** -/
theorem projection_joined_with_client :
    CertifiedConclusion holDecoder holDiscipline projectionProgram holRootAction (empty rules)
      (projectionSource exampleWire) FrameControls.frameLabel 0 (startAt 5)
      [projectionStep 1 2 3 0] FrameControls.copy 16 0 (NativeWireData.encode exampleWire) := by
  refine formed_certified_execution holDiscipline projectionProgram holRootAction
    (compile_source exampleWire) rfl ?_ ?_ ?_ dataTypeOver (valueTerm exampleWire) rfl
    (Certificate.refl _)
  · rw [projection_run]
    exact FrameControls.separated
  · rw [projection_run]
    exact frame_certified
  · decide +kernel

/-- **The certifying joined theorem for dependent vector append.** The run's certificate replaces
the Flower's search for the term; the target's formation at `Vec Nat 2` and the index conversion
are the target's own judgments. -/
theorem append_joined :
    CertifiedConclusion NativeNaturalVectorFamilies.Programs.decoder Append.vectorDiscipline
      Append.appendProgram Append.vectorRootAction Append.context Append.appendSource Append.label 0
      unitConfiguration Append.steps [] 64 Append.resultVar Append.value := by
  refine formed_certified_execution Append.vectorDiscipline Append.appendProgram
    Append.vectorRootAction (source := Append.appendSource) Append.compile_source rfl ?_ ?_ ?_
    Append.valueTypeOver
    Append.valueTerm rfl Append.typeCertificate
  · rw [Append.steps_firing]
    exact separated_alone Append.append_executes
  · rw [Append.steps_firing]
    exact Append.append_certified
  · decide +kernel

end Consumers

/-! ## Negative controls for the compilation hypotheses -/

namespace CompilationControls

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed.Append

/-- The quoted value `[a, b]`. -/
def valuePattern : Pattern := vconsP natP (succP zeroP) (.var 1) (vconsP natP zeroP (.var 0) (vnilP natP))

def anyLabel : Nat → Pattern := fun _ => .const .anonymous

/-- Probe C's start: the store already holds the answer, and nothing is pending. -/
def oracleStart : Configuration Pattern Nat := ⟨[(.var resultVar, valuePattern)], ∅⟩

theorem oracle_start_executes : Executable action anyLabel oracleStart [] :=
  consistent_of_unified (fuel := 8) (by decide +kernel)

/-- **Negative control (probe C): a run with no firings.** Result checking accepts the start whose
store already holds the answer. That start is not compiled; from the compiled start the empty run
has no checked result and no certificate. -/
theorem no_firing_refused :
    JoinedConclusion NativeNaturalVectorFamilies.Programs.decoder vectorCanonical context appendSource anyLabel oracleStart
        unitConfiguration [] [] 8 resultVar value appendEvidence ∧
      (∀ o, oracleStart ≠ compiledStart o) ∧
      checkResult vectorCanonical 64
        (follow label start ([] : List (Firing Pattern (Subst signature) Nat))).equations resultVar value =
          false ∧
      (runCertificate appendProgram vectorRootAction 64 label start [] 0 :
        Option (Code Presentation.Tower.Head NativeNaturalVectorFamilies.Programs.decoder.Code 2)) = none := by
  refine ⟨checked_result_joined NativeNaturalVectorFamilies.Programs.decoder vectorCanonical
    (separated_alone oracle_start_executes)
    (by decide +kernel) appendEvidence, fun o same => ?_, by decide +kernel, ?_⟩
  · have stores := congrArg Configuration.equations same
    simp [oracleStart, compiledStart] at stores
  · unfold runCertificate
    split <;> rfl

/-- Probe E's firing: it takes nothing and tells the answer. -/
def oracleFiring : Firing Pattern (Subst signature) Nat :=
  ⟨⟨[], [], [(.var resultVar, valuePattern)], [], []⟩, [], ⟨[], [], []⟩⟩

theorem oracle_runs : Executable action label start [oracleFiring] := by
  refine ⟨⟨⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, FrameControls.empty_enabled _ _, ?_,
    by simp [oracleFiring]⟩, by simp [oracleFiring]⟩, ?_⟩
  · exact consistent_of_unified (fuel := 8) (by decide +kernel)
  · exact consistent_of_unified (fuel := 8) (by decide +kernel)

/-- **Negative control (probe E): a one-firing oracle from the compiled start.** It runs, and its
result is accepted while the compiled program is still pending; but it is the firing of no
compiled step, since a compiled step takes exactly one occurrence. -/
theorem oracle_refused :
    Executable action label start [oracleFiring] ∧
      checkResult vectorCanonical 8 (follow label start [oracleFiring]).equations resultVar value = true ∧
      0 ∈ (follow label start [oracleFiring]).present ∧
      ∀ step : CompiledStep appendProgram, step.firing ≠ oracleFiring := by
  refine ⟨oracle_runs, by decide +kernel, by decide +kernel, fun step same => ?_⟩
  have taken := congrArg (fun f : Firing Pattern (Subst signature) Nat => f.selection.taken) same
  simp [CompiledStep.firing, oracleFiring] at taken

end CompilationControls

/-! ## Negative controls for the value discipline -/

namespace ValueControls

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed.Append
open NativeNaturalVectorFamilies

/-- **The vector table is a value discipline of the extension by the declared append**: there the
declared name is the head of a delta root, and it is not canonical. -/
def extensionDiscipline : ValueDiscipline AppendDefinitionCompletion.rules where
  canonical := vectorCanonical
  root_head := by
    intro n left right step
    cases step with
    | inherited inherited => exact vectorDiscipline.root_head inherited
    | @delta name value lookup =>
        by_cases same : name = AppendDefinitionCompletion.name
        · subst same
          exact ⟨_, rfl, by decide +kernel⟩
        · have absent : AppendDefinitionCompletion.library.valueOf? name = none := by
            simp [AppendDefinitionCompletion.library, AppendDefinitionCompletion.entries,
              Presentation.Declaration.Signature.ofList, Presentation.Declaration.Signature.insert,
              Presentation.Declaration.Signature.valueOf?, Presentation.Declaration.Signature.empty,
              same]
          rw [absent] at lookup
          cases lookup
    | declared declared =>
        change (Presentation.Declaration.Signature.ofList AppendDefinitionCompletion.entries).computation.step
          left right at declared
        rw [Presentation.Declaration.Signature.computation_ofList] at declared
        exact False.elim declared

/-- Probe A's pattern: the eliminator application `natElim P z s zero`. -/
def redexPattern : Pattern :=
  ap (ap (ap (ap (.const natEliminateName) (.var 2)) (.var 1)) (.var 0)) zeroP

/-- **Negative control (probe A): an eliminator redex is not a value.** Readback refuses it, so the
result check refuses a store that binds the result to it; the compiler refuses it as a source;
and it is a redex, with an iota step to its zero case. -/
theorem redex_refused :
    (readback vectorCanonical redexPattern : Option (Tm Presentation.Tower.Head 3)) = none ∧
      checkResult vectorCanonical 8 [(.var 3, redexPattern)] 3 natZeroIotaLeft = false ∧
      compile vectorCanonical appendProgram.callables natZeroIotaLeft = none ∧
      ¬ IsValue vectorCanonical natZeroIotaLeft ∧
      StepCore Append.rules.computation Append.rules.headEq natZeroIotaLeft natZeroIotaRight := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, fun value => ?_, ?_⟩
  · have isCanonical : vectorCanonical natEliminateName = true := value.1.1.1.1
    revert isCanonical
    decide +kernel
  · exact .root (Presentation.Declaration.RootStep.declared
      (Nonempty.intro (IotaEvidence.natZero _ _ _)))

/-- Probe B's pattern: the unevaluated call of the declared append. -/
def callPattern : Pattern :=
  ap (ap (ap (ap (ap (.const AppendDefinitionCompletion.name) natP) (succP zeroP)) (succP zeroP))
    (vconsP natP zeroP (.var 1) (vnilP natP))) (vconsP natP zeroP (.var 0) (vnilP natP))

def callTerm : Presentation.Tower.Tm 2 :=
  AppendDefinitionCompletion.call natTm one one xs ys

/-- **Negative control (probe B): an unevaluated call of the declared append is not a value.**
Readback refuses it under the extension's value discipline, so the result check refuses it; its
head is a delta redex of the extension. -/
theorem call_refused :
    (readback extensionDiscipline.canonical callPattern : Option (Tm Presentation.Tower.Head 2)) = none ∧
      checkResult extensionDiscipline.canonical 8 [(.var resultVar, callPattern)] resultVar callTerm =
        false ∧
      ¬ IsValue extensionDiscipline.canonical callTerm ∧
      StepCore AppendDefinitionCompletion.rules.computation AppendDefinitionCompletion.rules.headEq
        (.const AppendDefinitionCompletion.name : Presentation.Tower.Tm 2)
        (Presentation.liftClosed Programs.appendTerm) := by
  refine ⟨by decide +kernel, by decide +kernel, fun value => ?_, ?_⟩
  · have isCanonical : vectorCanonical AppendDefinitionCompletion.name = true :=
      value.1.1.1.1.1
    revert isCanonical
    decide +kernel
  · exact .root (Presentation.Declaration.RootStep.delta AppendDefinitionCompletion.selected_entry.2)

end ValueControls

/-- **Negative control: a residual expression is not a value.** After the cons firing alone, the
unifier answers, and its answer for the result variable is a cons with a pending length and a
pending tail; that has no readback, and the formed fibre at the history is empty. -/
theorem residual_not_value :
    (unifyFuel 64 (follow Append.label Append.start [Append.consFiring]).equations).map
        (fun θ => θ Append.resultVar) =
      some (Append.vconsP Append.natP (.var 10) (.var 1) (.var 11)) ∧
    ∃ history : runObject action Append.label Append.start ⟶
        classOf action Append.label (follow Append.label Append.start [Append.consFiring]),
      OccurrencePath.sites history = [Append.consFiring] ∧
        unifierReadout (Head := Presentation.Tower.Head) (n := 2) Append.vectorCanonical
          Append.label Append.start 64 Append.resultVar history = none ∧
        IsEmpty (formedFiber (runObject action Append.label Append.start)
          NativeNaturalVectorFamilies.Programs.decoder Append.context Append.appendSource
          (unifierReadout Append.vectorCanonical Append.label Append.start 64 Append.resultVar) _
          history) := by
  have prefixRuns : Executable action Append.label Append.start [Append.consFiring] :=
    executable_append_left action Append.label Append.start [Append.consFiring]
      [Append.addFiring, Append.nilFiring] Append.append_executes
  obtain ⟨history, sites⟩ := exists_path action Append.label Append.start [Append.consFiring]
    prefixRuns _ rfl
  have readout : unifierReadout (Head := Presentation.Tower.Head) (n := 2) Append.vectorCanonical
      Append.label Append.start 64 Append.resultVar history = none := by
    change (match unifyFuel 64 (follow Append.label Append.start (OccurrencePath.sites history)).equations with
      | some θ => readback (Head := Presentation.Tower.Head) (n := 2) Append.vectorCanonical
          (θ Append.resultVar)
      | none => none) = none
    rw [sites]
    decide +kernel
  refine ⟨by decide +kernel, history, sites, readout, ⟨fun element => ?_⟩⟩
  have defined : unifierReadout (Head := Presentation.Tower.Head) (n := 2) Append.vectorCanonical
      Append.label Append.start 64 Append.resultVar history = some element.1.1 := element.1.2
  rw [readout] at defined
  cases defined

/-! ## What descends -/

namespace Descent

open Projection

abbrev historyObject := classOf action (programLabel (program exampleWire))
  (follow (programLabel (program exampleWire)) start [projectionFiring])

abbrev projectionFibre :=
  formedFiber (runObject action (programLabel (program exampleWire)) start) holDecoder (empty rules)
    (projectionSource exampleWire)
    (unifierReadout holCanonical (programLabel (program exampleWire)) start 16 0) historyObject

/-- **Formation and the semantic value descend**: at every history, formed evidence exists exactly
when the history's readout is a formed term in the source's `QTerm` class. -/
theorem projection_descends
    (h : runObject action (programLabel (program exampleWire)) start ⟶ historyObject) :
    h ∈ trunc projectionFibre ↔
      ∃ target, unifierReadout holCanonical (programLabel (program exampleWire)) start 16 0 h =
          some target ∧
        ∃ (type : TypeOver (empty rules)) (term : Term (empty rules) type),
          term.code = target ∧ QTerm.mk (projectionSource exampleWire).2 = QTerm.mk term :=
  trunc_formedFiber _ h

/-- **Two pieces of evidence for one history, with distinct costs.** The projection's history has
the direct evidence and the detour; both lie in the formed fibre, have one class, and cost one and
three steps. The cost separates the fibre. -/
theorem two_evidence_objects_one_history :
    ∃ (history : runObject action (programLabel (program exampleWire)) start ⟶ historyObject)
      (direct detour : projectionFibre history),
      direct.2.stepCount = 1 ∧ detour.2.stepCount = 3 ∧
        QTerm.mk direct.2.targetTerm = QTerm.mk detour.2.targetTerm ∧
        Separates (E := projectionFibre) (fun _ evidence => evidence.2.stepCount) := by
  have executes : Executable action (programLabel (program exampleWire)) start [projectionFiring] := by
    have compiled := (projection_square exampleWire).2.1
    rw [projectionFiringAt_compiled] at compiled
    exact compiled
  obtain ⟨history, sites⟩ := exists_path action (programLabel (program exampleWire)) start
    [projectionFiring] executes _ rfl
  have readout : unifierReadout (Head := Presentation.Tower.Head) (n := 0) holCanonical
      (programLabel (program exampleWire)) start 16 0 history =
      some (NativeWireData.encode (n := 0) exampleWire) := by
    change (match unifyFuel 16 (follow (programLabel (program exampleWire)) start
        (OccurrencePath.sites history)).equations with
      | some θ => readback holCanonical (θ 0)
      | none => none) = some (NativeWireData.encode (n := 0) exampleWire)
    rw [sites]
    exact readout_of_check example_certified
  let direct : projectionFibre history := ⟨⟨_, readout⟩, projectionEvidence exampleWire⟩
  let detour : projectionFibre history := ⟨⟨_, readout⟩, projectionDetour exampleWire⟩
  refine ⟨history, direct, detour, projectionEvidence_stepCount exampleWire,
    projectionDetour_stepCount exampleWire, rfl, formedFiber_separates _ direct detour ?_⟩
  change (projectionEvidence exampleWire).stepCount ≠ (projectionDetour exampleWire).stepCount
  rw [projectionEvidence_stepCount, projectionDetour_stepCount]
  decide

/-- **The cost is not a function of the class.** -/
theorem cost_not_a_function_of_class :
    ¬ ∃ cost : QTerm (empty rules) → Nat,
      ∀ e : FormedEvidence holDecoder (empty rules) (projectionSource exampleWire)
          (NativeWireData.encode exampleWire),
        e.stepCount = cost (QTerm.mk e.targetTerm) := by
  rintro ⟨cost, reads⟩
  have direct := reads (projectionEvidence exampleWire)
  have detour := reads (projectionDetour exampleWire)
  rw [projectionEvidence_stepCount] at direct
  rw [projectionDetour_stepCount] at detour
  have same : QTerm.mk (projectionEvidence exampleWire).targetTerm =
      QTerm.mk (projectionDetour exampleWire).targetTerm := rfl
  rw [same] at direct
  omega

/-- **The extension by the declared append adds a name.** Append's retyped judgment moves into
the theory with the declared append; the declared name is typed there and not in the base. The
name unfolds to a base term by a checked delta step, so this does not show that interpretation
is one-way. -/
theorem extension_adds_name :
    Presentation.FormationSensitive.Judgment AppendDefinitionCompletion.rules Append.ctx
        Append.sourceCode Append.valueType ∧
      (∃ type, Presentation.FormationSensitive.Typing AppendDefinitionCompletion.rules .nil
        (.const AppendDefinitionCompletion.name) type) ∧
      ¬ ∃ type, Presentation.FormationSensitive.Typing Append.rules .nil
        (.const AppendDefinitionCompletion.name) type := by
  refine ⟨Append.appendEvidence.retyped.includeSignature AppendDefinitionCompletion.library, ?_, ?_⟩
  · have universes : Presentation.FormationSensitive.UniverseRegularity
        NativeNaturalVectorFamilies.Programs.rules :=
      Presentation.FormationSensitive.towerUniverseRegularity.includeSignature
        NativeNaturalVectorFamilies.Programs.signature
    obtain ⟨u, isUniverse, formed⟩ :=
      NativeNaturalVectorFamilies.Programs.append_typed.typing.regularity universes .nil
    exact ⟨_, .const AppendDefinitionCompletion.selected_entry.1
      (formed.includeSignature AppendDefinitionCompletion.library) isUniverse⟩
  · rintro ⟨type, typed⟩
    obtain ⟨declared, _, known, _, _⟩ := typed.constFormation
    have absent : Append.rules.constantType AppendDefinitionCompletion.name = none := by decide
    rw [absent] at known
    cases known

end Descent

/-! ## Negative controls of the source side and the checker -/

namespace JoinedControls

open Projection
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

section Inversion

variable {Head : Type} {R : Presentation.Rules Head}

theorem pair_first_typed {n : Nat} {Γ : Presentation.Ctx Head n} {term type : Tm Head n}
    (typing : Presentation.FormationSensitive.Typing R Γ term type) :
    ∀ {first second : Tm Head n}, term = .pair first second →
      ∃ firstType, Presentation.FormationSensitive.Typing R Γ first firstType := by
  induction typing with
  | pairIntro _ _ firstTyped _ _ _ _ =>
      intro first second equality
      cases equality
      exact ⟨_, firstTyped⟩
  | cumul _ _ ih =>
      intro first second equality
      exact ih equality
  | conv _ _ _ _ ih _ =>
      intro first second equality
      exact ih equality
  | _ =>
      intro first second equality
      cases equality

theorem snd_pair_first_typed {n : Nat} {Γ : Presentation.Ctx Head n} {term type : Tm Head n}
    (typing : Presentation.FormationSensitive.Typing R Γ term type) :
    ∀ {first second : Tm Head n}, term = .snd (.pair first second) →
      ∃ firstType, Presentation.FormationSensitive.Typing R Γ first firstType := by
  induction typing with
  | sndElim pairTyped _ =>
      intro first second equality
      cases equality
      exact pair_first_typed pairTyped rfl
  | cumul _ _ ih =>
      intro first second equality
      exact ih equality
  | conv _ _ _ _ ih _ =>
      intro first second equality
      exact ih equality
  | _ =>
      intro first second equality
      cases equality

end Inversion

abbrev missingName := FormationSensitiveCompletedConversion.Controls.missingName

/-- A target convertible to the projection's value, containing an undeclared constant. -/
def unformedTarget (wire : NativeWireData.Wire) : Tm Presentation.Tower.Head 0 :=
  .snd (.pair (.const missingName) (NativeWireData.encode wire))

theorem unformed_not_typed (wire : NativeWireData.Wire) (type : Tm Presentation.Tower.Head 0) :
    ¬ Presentation.FormationSensitive.Typing rules .nil (unformedTarget wire) type := by
  intro typed
  obtain ⟨_, constantTyped⟩ := snd_pair_first_typed typed rfl
  obtain ⟨declared, _, known, _, _⟩ := constantTyped.constFormation
  have absent : rules.constantType missingName = none := by decide
  rw [absent] at known
  cases known

/-- The checked Sigma beta step from the unformed target to the value. -/
def unformedStep (wire : NativeWireData.Wire) :
    Certificate rules.headEq holDecoder.decode (unformedTarget wire) (NativeWireData.encode wire) :=
  ⟨.single (.betaSigmaSnd (.const missingName) (NativeWireData.encode wire)), by
    simp [Presentation.StructuralConversionCode.Code.check, Presentation.StructuralConversionCode.Code.decode,
      Presentation.StructuralConversionCode.StepCode.decode, unformedTarget]⟩

/-- **Negative control: an unformed target.** The checker relates the source to a convertible
target, and there is no formed evidence for that target: it has no formation at any type. -/
theorem unformed_target (wire : NativeWireData.Wire) :
    Nonempty (Certificate rules.headEq holDecoder.decode (projectionSource wire).2.code
      (unformedTarget wire)) ∧
      IsEmpty (FormedEvidence holDecoder (empty rules) (projectionSource wire) (unformedTarget wire)) :=
  ⟨⟨(betaCertificate wire).trans (unformedStep wire).symm⟩,
    ⟨fun e => unformed_not_typed wire _ e.targetJudgment.typing⟩⟩

/-- **Negative control: an undeclared opaque constant despite raw reflexive conversion.** The
reflexive conversion of an undeclared constant has an accepted code; no formed source program has
that code, so the adapter has no source to start from. -/
theorem undeclared_constant_no_source :
    (∃ code, NativeRelatorConversionChecking.check code (.const missingName : Tm Presentation.Tower.Head 0)
        (.const missingName) = true) ∧
      IsEmpty {source : TotalTerm (empty rules) // source.2.code = .const missingName} := by
  obtain ⟨checked, notAdmitted⟩ :=
    FormationSensitiveCompletedConversion.Controls.checked_conversion_does_not_supply_admission
  refine ⟨checked, ⟨fun ⟨source, code⟩ => notAdmitted ⟨source.1.code, ?_⟩⟩⟩
  have judgment := source.2.judgment
  rw [code] at judgment
  exact judgment

abbrev projectionStore : EquationStore Pattern :=
  (follow (programLabel (program exampleWire)) start [projectionFiring]).equations

open Mettapedia.Languages.Lean.LeanCheckerAuthorityFlower in
/-- **Negative control: incomplete checking grants no theorem authority, at the real
thresholds.** The projection's store needs eight unifier steps: at fuel seven the unifier gives no
answer and the service declines, though the store observes the answer; at fuel eight the check
accepts. The Flower's search finds append's conversion at budget nine, not at eight, though the
conversion holds. -/
theorem incomplete_checking_grants_no_authority :
    (unifyFuel 7 projectionStore).isNone = true ∧
      (resultService (Head := Presentation.Tower.Head) (n := 0) holCanonical 7).run
        (projectionStore, 0, NativeWireData.encode exampleWire) = .declined ∧
      checkResult (Head := Presentation.Tower.Head) (n := 0) holCanonical 8 projectionStore 0
        (NativeWireData.encode exampleWire) = true ∧
      Observes action projectionStore (.var 0) (payloadPattern exampleWire) ∧
      Presentation.StructuralConversionSearch.compare NativeNaturalVectorFamilies.Programs.decoder
          NativeNaturalVectorFamilies.Programs.searchRoot (headEq := Append.rules.headEq) 8
          Append.sourceCode Append.value = none ∧
      (Presentation.StructuralConversionSearch.compare NativeNaturalVectorFamilies.Programs.decoder
          NativeNaturalVectorFamilies.Programs.searchRoot (headEq := Append.rules.headEq) 9
          Append.sourceCode Append.value).isSome = true ∧
      Presentation.Conv Append.rules.headEq Append.sourceCode Append.value Append.rules.computation :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, (projection_square exampleWire).2.2.1,
    by decide +kernel, by decide +kernel, Append.appendEvidence.termConversion⟩

/-- **Negative control: model existence is not an observation.** The empty store has a model where
the result variable has the payload's value, and it does not observe the payload. -/
theorem model_existence_is_not_observation :
    (∃ σ : Subst signature, action.Models σ [] ∧ σ 0 = payloadPattern exampleWire) ∧
      ¬ Observes action ([] : EquationStore Pattern) (.var 0) (payloadPattern exampleWire) := by
  refine ⟨⟨fun _ => payloadPattern exampleWire, fun _ member => (List.not_mem_nil member).elim, rfl⟩,
    fun observed => ?_⟩
  have identity := observed (Subst.id signature) (fun _ member => (List.not_mem_nil member).elim)
  change (Subst.id signature).applyTerm (.var 0) = (Subst.id signature).applyTerm (payloadPattern exampleWire)
    at identity
  rw [Subst.applyTerm_id, Subst.applyTerm_id] at identity
  have readbacks := congrArg (readback (Head := Presentation.Tower.Head) (n := 0) holCanonical) identity
  rw [readback_internal holCanonical (Nat.le_refl 0), payload_readback] at readbacks
  cases readbacks

end JoinedControls

#print axioms readout_of_check
#print axioms separated_alone
#print axioms checked_result_joined
#print axioms formed_certified_execution
#print axioms Consumers.projection_run
#print axioms Consumers.projection_joined
#print axioms Consumers.frame_certified
#print axioms Consumers.projection_joined_with_client
#print axioms Consumers.append_joined
#print axioms CompilationControls.no_firing_refused
#print axioms CompilationControls.oracle_refused
#print axioms ValueControls.extensionDiscipline
#print axioms ValueControls.redex_refused
#print axioms ValueControls.call_refused
#print axioms residual_not_value
#print axioms Descent.projection_descends
#print axioms Descent.two_evidence_objects_one_history
#print axioms Descent.cost_not_a_function_of_class
#print axioms Descent.extension_adds_name
#print axioms JoinedControls.unformed_target
#print axioms JoinedControls.undeclared_constant_no_source
#print axioms JoinedControls.incomplete_checking_grants_no_authority
#print axioms JoinedControls.model_existence_is_not_observation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsFormed
