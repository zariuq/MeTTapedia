import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeNamedGeneralization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeFieldPacking

/-!
# Checked proof-only accumulation for the actual native products

The accumulator retains the actual registered commands, context and ordered
cache. One signature-instance finder is used throughout the proof-only suffix.
Product readings are constructed only by the exact reader in the final state.
No semantic model is computed or independently selected by this executable layer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeProductClosure

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution NativeClauseData

structure ProofRun (before : Registered.State) where
  after : Registered.State
  instances : SignatureFormation.InstanceWitnesses
  nodes : List Receipt
  replayed : Registered.replayFrom SourceProfileModels.policy before
    (RegisteredProofBlocks.commands instances nodes) = some after
  context_eq : after.context = before.context
  inferenceOnly : InferenceOnlyReplay.inferenceOnly nodes = true
  old_lookup : ∀ (index : Nat) (fact : Theorem), before.cache[index]? = some fact →
    after.cache[index]? = some fact

namespace ProofRun

def suffix {before : Registered.State} (run : ProofRun before) : List Registered.Command :=
  RegisteredProofBlocks.commands run.instances run.nodes

def start (before : Registered.State) : ProofRun before where
  after := before
  instances := ExportReplay.instanceCertificates before.context.signature
  nodes := []
  replayed := rfl
  context_eq := rfl
  inferenceOnly := rfl
  old_lookup := fun _ _ found => found

theorem no_requested_axiom {before : Registered.State} (run : ProofRun before)
    (command : Registered.Command) (member : command ∈ run.suffix) :
    command.requestedAxiom = none := by
  obtain ⟨node, present, rfl⟩ := List.mem_map.mp member
  have inference := (List.all_eq_true.mp run.inferenceOnly) node present
  cases witness : node.witness with
  | inference request =>
      simp only [Registered.Command.requestedAxiom, witness, RuleRequest.requestedAxiom]
  | «axiom» sequent =>
      simp only [InferenceOnlyReplay.isInference, witness] at inference
      cases inference

end ProofRun

def formedB (state : Registered.State) (instances : SignatureFormation.InstanceWitnesses)
    (nodes : List Receipt) : Bool :=
  nodes.all fun node => Registered.requestFormedB state.context.signature instances node.witness &&
    DefinitionAdapters.theoremFormedB state.context.signature instances node.conclusion

theorem formedB_eq_true (state : Registered.State) (instances : SignatureFormation.InstanceWitnesses)
    (nodes : List Receipt) : formedB state instances nodes = true ↔
      RegisteredProofBlocks.Formed state instances nodes := by
  simp only [formedB, List.all_eq_true, Bool.and_eq_true, RegisteredProofBlocks.Formed]

theorem relocated_inferenceOnly (roots : List Nat) (offset : Nat) (block : ProofSystem.Certificate) :
    InferenceOnlyReplay.inferenceOnly (GraphExpansion.expandBlock roots offset block).1 =
      InferenceOnlyReplay.inferenceOnly block.1 := by
  simp only [GraphExpansion.expandBlock, InferenceOnlyReplay.inferenceOnly, List.all_map,
    Function.comp_def, DerivationGraph.Node.relocate, InferenceOnlyReplay.isInference]
  rfl

/-- Append only a compact block that passes the existing primitive checker,
the actual premise lookup and the actual registered signature checks. -/
def appendBlock? {before : Registered.State} (run : ProofRun before)
    (roots : List Nat) {premises : List Theorem}
    (block : NativeNamedGeneralization.CheckedBlock SourceProfileModels.policy premises) :
    Option (ProofRun before × Nat) := do
  match selected : DerivationGraph.lookupPremises run.after.cache roots with
  | none => none
  | some actual =>
      if same : actual = premises then
        if formed : formedB run.after run.instances block.certificate.1 = true then
          if only : InferenceOnlyReplay.inferenceOnly block.certificate.1 = true then
            let expanded := GraphExpansion.expandBlock roots run.after.cache.size block.certificate
            let checked := RegisteredProofBlocks.relocated_replay SourceProfileModels.policy
              run.after run.instances roots premises block.result block.certificate
              (selected.trans (congrArg some same)) block.checked
              ((formedB_eq_true _ _ _).mp formed)
            let final := RegisteredProofBlocks.finish run.after run.instances expanded.1
            let replayed : Registered.replayFrom SourceProfileModels.policy before
                (RegisteredProofBlocks.commands run.instances (run.nodes ++ expanded.1)) = some final := by
              rw [RegisteredProofBlocks.commands, List.map_append]
              exact Registered.replayFrom_append_accepted SourceProfileModels.policy run.replayed checked
            have expandedOnly : InferenceOnlyReplay.inferenceOnly expanded.1 = true :=
              (relocated_inferenceOnly roots run.after.cache.size block.certificate).trans only
            return (⟨final, run.instances, run.nodes ++ expanded.1, replayed,
              run.context_eq,
              by simpa only [InferenceOnlyReplay.inferenceOnly, List.all_append,
                Bool.and_eq_true] using And.intro run.inferenceOnly expandedOnly,
              fun index fact found => Registered.replayFrom_preserves_lookup SourceProfileModels.policy
                before _ final replayed found⟩, expanded.2)
          else none
        else none
      else none

structure Result (before : Registered.State) (ops : Operations) extends ProofRun before where
  readings : NativeFieldPacking.Readings ops after

/-- A finite exact-reading bundle, not a supplied semantic product law. -/
def readAll? (ops : Operations) (state : Registered.State)
    (indices : Fin 9 → NativeFieldPacking.Indices) : Option (NativeFieldPacking.Readings ops state) :=
  if available : ∀ index : Fin 9,
      (NativeFieldPacking.readProduct? (NativeFieldPacking.products ops index) state (indices index)).isSome = true then
    some ⟨fun index =>
      (NativeFieldPacking.readProduct? (NativeFieldPacking.products ops index) state (indices index)).get
        (available index)⟩
  else none

def finishReadings? {before : Registered.State} (run : ProofRun before) (ops : Operations)
    (indices : Fin 9 → NativeFieldPacking.Indices) : Option (Result before ops) := do
  let readings ← readAll? ops run.after indices
  return { toProofRun := run, readings := readings }

def emitRequest? {before : Registered.State} (run : ProofRun before) (roots : List Nat)
    (request : RuleRequest) (origin : Origin) : Option (ProofRun before × Nat) := do
  let conclusion ← request.check SourceProfileModels.policy
  let block ← NativeNamedGeneralization.checkBlock? SourceProfileModels.policy request.premises
    (GraphExpansion.primitiveBlock request conclusion origin)
  appendBlock? run roots block

def instantiateAt? {before : Registered.State} (run : ProofRun before) (root : Nat)
    (entries : List (Ty × Ty)) (origin : Origin) : Option (ProofRun before × Nat) := do
  let input ← run.after.cache[root]?
  emitRequest? run [root] (.inference (.instType entries input)) origin

def functionConversionAt? {before : Registered.State} (run : ProofRun before)
    (domain : Ty) (universalRoot truthRoot : Nat) (origin : Origin) :
    Option (ProofRun before × Nat) := do
  let universal ← run.after.cache[universalRoot]?
  let truth ← run.after.cache[truthRoot]?
  let initial := GraphExpansion.start [universal, truth]
  let (converted, root) ← NativeNamedGeneralization.functionConversion? domain.toHOL initial 0 1 origin
  let block ← NativeNamedGeneralization.checkBlock? SourceProfileModels.policy [universal, truth]
    (GraphExpansion.finish converted root)
  appendBlock? run [universalRoot, truthRoot] block

def generalizeAt? {before : Registered.State} (run : ProofRun before)
    (root conversionRoot : Nat) (binder : SourceVar) (origin : Origin) :
    Option (ProofRun before × Nat) := do
  let input ← run.after.cache[root]?
  let conversion ← run.after.cache[conversionRoot]?
  let named ← NativeNamedGeneralization.namedGenBlock? SourceProfileModels.policy input conversion binder origin
  appendBlock? run [root, conversionRoot] named.block

def rawProducts (ops : Operations) : Fin 9 → Ty × Ty × Ty :=
  ![(t1 ops, t21 ops, t22 ops), (t4 ops, t20 ops, t21 ops),
    (t8 ops, t19 ops, t20 ops), (t11 ops, t18 ops, t19 ops),
    (t8 ops, t17 ops, t18 ops), (t12 ops, t16 ops, t17 ops),
    (t13 ops, t15 ops, t16 ops), (t13 ops, t14 ops, t15 ops),
    (t12 ops, t5 ops, t14 ops)]

def projectionSeed (ops : Operations) (first second pair : Ty) (left : Bool) :
    HOL.ClosedFormula Symbol :=
  let product := NativeFieldPacking.productSignature ops first second pair
  let x : HOL.ClosedTerm Symbol first.toHOL := .const (.variable ⟨.global "x", first⟩ rfl)
  let y : HOL.ClosedTerm Symbol second.toHOL := .const (.variable ⟨.global "y", second⟩ rfl)
  let packed := HOL.Term.app (HOL.Term.app product.constructor x) y
  if left then .eq (.app product.left packed) x else .eq (.app product.right packed) y

structure Inputs where
  truth : Nat
  universalSchema : Nat
  universalParameter : Name
  pairSchema : Nat
  pairFirstParameter : Name
  pairSecondParameter : Name
  firstSeed : Fin 9 → Nat
  secondSeed : Fin 9 → Nat

/-- The complete constructor earns every reading through actual existing
checks. It does not accept an assumed product interpretation or final model. -/
def closeProducts? (before : Registered.State) (ops : Operations) (inputs : Inputs)
    (origin : String) : Option (Result before ops) := do
  let genericFirst := Ty.var inputs.pairFirstParameter
  let genericSecond := Ty.var inputs.pairSecondParameter
  let genericPair := Ty.op ops.o4 [genericFirst, genericSecond]
  let generic := NativeFieldPacking.productSignature ops genericFirst genericSecond genericPair
  let _ ← ExactFormulaReadback.read? before inputs.pairSchema generic.pairLaw
  let mut run := ProofRun.start before
  let mut collected : Array NativeFieldPacking.Indices := #[]
  for index in List.finRange 9 do
    let types := rawProducts ops index
    let first := types.1
    let second := types.2.1
    let pair := types.2.2
    let _ ← ExactFormulaReadback.read? run.after (inputs.firstSeed index)
      (projectionSeed ops first second pair true)
    let _ ← ExactFormulaReadback.read? run.after (inputs.secondSeed index)
      (projectionSeed ops first second pair false)
    let base := 20 * index.val
    let (next, firstDefinition) ← instantiateAt? run inputs.universalSchema
      [(first, .var inputs.universalParameter)] (origin, base)
    run := next
    let (next, firstConversion) ← functionConversionAt? run first firstDefinition inputs.truth (origin, base+1)
    run := next
    let (next, secondDefinition) ← instantiateAt? run inputs.universalSchema
      [(second, .var inputs.universalParameter)] (origin, base+2)
    run := next
    let (next, secondConversion) ← functionConversionAt? run second secondDefinition inputs.truth (origin, base+3)
    run := next
    let (next, firstInner) ← generalizeAt? run (inputs.firstSeed index) secondConversion
      ⟨.global "y", second⟩ (origin, base+4)
    run := next
    let (next, firstRoot) ← generalizeAt? run firstInner firstConversion
      ⟨.global "x", first⟩ (origin, base+5)
    run := next
    let (next, secondInner) ← generalizeAt? run (inputs.secondSeed index) secondConversion
      ⟨.global "y", second⟩ (origin, base+6)
    run := next
    let (next, secondRoot) ← generalizeAt? run secondInner firstConversion
      ⟨.global "x", first⟩ (origin, base+7)
    run := next
    let (next, pairRoot) ← instantiateAt? run inputs.pairSchema
      [(first, .var inputs.pairFirstParameter), (second, .var inputs.pairSecondParameter)]
      (origin, base+8)
    run := next
    collected := collected.push ⟨firstRoot, secondRoot, pairRoot⟩
  if complete : collected.size = 9 then
    finishReadings? run ops (fun index => collected[index.val]'(by omega))
  else none

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeProductClosure
