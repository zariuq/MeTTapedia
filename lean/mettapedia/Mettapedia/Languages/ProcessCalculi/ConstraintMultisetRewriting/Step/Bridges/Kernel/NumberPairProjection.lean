import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeProductClosure
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeTheoremRowSource

/-!
# Checked receipt production for the actual numeric pair projection

Only prod, num, comma, FST and SND are required. The producer reads the real
pointwise seed, instantiates its two type parameters, constructs the named
universal conversion from actual definition facts, and generalizes y then x.
Exact final readback and dependency checks gate the returned receipt.

The suffix retains the original registered context, cache and receipts. It is
a separate derived proof suffix, not replacement input or a new source law.
Numeric syntax, HD/EL, carrier categoricity and native admission are separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberPairProjection

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution TypeFamilySemantics NativeProductClosure

universe w

structure Operations where
  number : TypeOp
  product : TypeOp
  comma : Const
  first : Const
  second : Const

def operations? (symbols : ExportCodec.Symbols) : Option Operations := do
  return ⟨← List.lookup "num" symbols.operators,← List.lookup "prod" symbols.operators,
    ← List.lookup "," symbols.constants,← List.lookup "FST" symbols.constants,← List.lookup "SND" symbols.constants⟩

def Operations.numberType (ops : Operations) : Ty := .op ops.number []
def Operations.pairType (ops : Operations) (first second : Ty) : Ty := .op ops.product [first,second]

def Operations.productSignature (ops : Operations) (first second : Ty) : SourceProducts.Signature where
  first := first.toHOL
  second := second.toHOL
  pair := (ops.pairType first second).toHOL
  constructor := .const (.constant ops.comma (.function first (.function second (ops.pairType first second)))
    (by simp only [Ty.toHOL_function]))
  left := .const (.constant ops.first (.function (ops.pairType first second) first) (Ty.toHOL_function _ _))
  right := .const (.constant ops.second (.function (ops.pairType first second) second) (Ty.toHOL_function _ _))

def Operations.signature (ops : Operations) : SourceProducts.Signature :=
  ops.productSignature ops.numberType ops.numberType

def pointwiseSecond (signature : SourceProducts.Signature) (first second : Ty)
    (firstTyped : first.toHOL = signature.first) (secondTyped : second.toHOL = signature.second) :
    HOL.ClosedFormula Symbol :=
  let x : HOL.ClosedTerm Symbol signature.first := .const (.variable ⟨.global "x",first⟩ firstTyped)
  let y : HOL.ClosedTerm Symbol signature.second := .const (.variable ⟨.global "y",second⟩ secondTyped)
  .eq (.app signature.right (.app (.app signature.constructor x) y)) y

def genericSeed (ops : Operations) : HOL.ClosedFormula Symbol :=
  pointwiseSecond (ops.productSignature (.var (.global "A")) (.var (.global "B")))
    (.var (.global "A")) (.var (.global "B")) rfl rfl

def numericSeed (ops : Operations) : HOL.ClosedFormula Symbol :=
  pointwiseSecond ops.signature ops.numberType ops.numberType rfl rfl

structure Inputs where
  seed : Nat
  universalDefinition : Nat
  truthDefinition : Nat

structure Prepared (before : Registered.State) (ops : Operations) extends ProofRun before where
  seed : ExactFormulaReadback.ReadFact before (genericSeed ops)
  numericRoot : Nat
  numeric : ExactFormulaReadback.ReadFact after (numericSeed ops)
  conversionRoot : Nat

/-- No source theorem or conversion is supplied: actual cache entries are read. -/
def prepare? (before : Registered.State) (ops : Operations) (inputs : Inputs)
    (origin : String) : Option (Prepared before ops) := do
  let seed ← ExactFormulaReadback.read? before inputs.seed (genericSeed ops)
  let truth ← before.cache[inputs.truthDefinition]?
  let universal ← before.cache[inputs.universalDefinition]?
  if truth.axioms = ∅ ∧ universal.axioms = ∅ then
    let (run, numericRoot) ← instantiateAt? (ProofRun.start before) inputs.seed
      [(ops.numberType,.var (.global "A")),(ops.numberType,.var (.global "B"))] (origin,0)
    let _ ← ExactFormulaReadback.read? run.after numericRoot (numericSeed ops)
    let (run, universalRoot) ← instantiateAt? run inputs.universalDefinition
      [(ops.numberType,.var (.global "A"))] (origin,1)
    let (run, conversionRoot) ← functionConversionAt? run ops.numberType universalRoot inputs.truthDefinition (origin,2)
    let numeric ← ExactFormulaReadback.read? run.after numericRoot (numericSeed ops)
    return ⟨run,seed,numericRoot,numeric,conversionRoot⟩
  else none

private theorem read_lookup {state : Registered.State} {index : Nat} {formula : HOL.ClosedFormula Symbol}
    {reading : ExactFormulaReadback.ReadFact state formula}
    (read : ExactFormulaReadback.read? state index formula = some reading) : state.cache[index]? = some reading.fact := by
  unfold ExactFormulaReadback.read? at read
  split at read
  · cases read
  · rename_i fact found
    split at read
    · have same := Option.some.inj read
      have value : fact = reading.fact := congrArg (fun item : ExactFormulaReadback.ReadFact state formula => item.fact) same
      simpa only [found] using congrArg some value
    · cases read

structure Result (before : Registered.State) (ops : Operations) extends ProofRun before where
  seed : ExactFormulaReadback.ReadFact before (genericSeed ops)
  root : Nat
  second : ExactFormulaReadback.ReadFact after ops.signature.secondLaw
  read : ExactFormulaReadback.read? after root ops.signature.secondLaw = some second
  found : after.cache[root]? = some second.fact
  axioms_eq : second.fact.axioms = seed.fact.axioms

/-- Alternative orders are checked against the same exact target; they do not
change the named operator or infer a semantic binder-exchange rule. -/
def finish? {before : Registered.State} {ops : Operations} (prepared : Prepared before ops)
    (binders : List SourceVar) (origin : String) : Option (Result before ops) := do
  let mut run := prepared.toProofRun
  let mut root := prepared.numericRoot
  let mut serial := 3
  for binder in binders do
    let (next, nextRoot) ← generalizeAt? run root prepared.conversionRoot binder (origin,serial)
    run := next
    root := nextRoot
    serial := serial+1
  match read : ExactFormulaReadback.read? run.after root ops.signature.secondLaw with
  | none => none
  | some second =>
      if tags : second.fact.axioms = prepared.seed.fact.axioms then
        return ⟨run,prepared.seed,root,second,read,read_lookup read,tags⟩
      else none

def produce? (before : Registered.State) (ops : Operations) (inputs : Inputs)
    (origin : String) : Option (Result before ops) := do
  let prepared ← prepare? before ops inputs origin
  finish? prepared [⟨.global "y",ops.numberType⟩,⟨.global "x",ops.numberType⟩] origin

/-- A compact primitive block on three external theorems. No source frame is
chosen for this local compiler state; installation binds its premises to the
actual prefix cache. -/
structure Compiled (ops : Operations) (seed universal truth : Theorem) where
  block : NativeNamedGeneralization.CheckedBlock SourceProfileModels.policy [seed,universal,truth]
  seedMatches : ExactFormulaReadback.matchesB seed (genericSeed ops) = true
  finalMatches : ExactFormulaReadback.matchesB block.result ops.signature.secondLaw = true
  inferenceOnly : InferenceOnlyReplay.inferenceOnly block.certificate.1 = true
  axioms_eq : block.result.axioms = seed.axioms

/-- Explicit finite construction choices are checked against the same target.
Incorrect substitutions or binder order cannot bypass final exact reading. -/
def compileWith? (ops : Operations) (seed universal truth : Theorem)
    (entries : List (Ty × Ty)) (binders : List SourceVar) (origin : String) :
    Option (Compiled ops seed universal truth) := do
  if base : ExactFormulaReadback.matchesB seed (genericSeed ops) = true ∧
      universal.axioms = ∅ ∧ truth.axioms = ∅ then
    let initial := GraphExpansion.start [seed,universal,truth]
    let (state, root) ← GraphExpansion.emit SourceProfileModels.policy
      (.inference (.instType entries seed)) [0] (origin,0) initial
    let numeric ← state.cache[root]?
    if ExactFormulaReadback.matchesB numeric (numericSeed ops) = true then
      let (state, universalRoot) ← GraphExpansion.emit SourceProfileModels.policy
        (.inference (.instType [(ops.numberType,.var (.global "A"))] universal)) [1] (origin,1) state
      let (state, conversionRoot) ← NativeNamedGeneralization.functionConversion?
        ops.numberType.toHOL state universalRoot 2 (origin,2)
      let mut current := state
      let mut currentRoot := root
      let mut serial := 3
      for binder in binders do
        let input ← current.cache[currentRoot]?
        let conversion ← current.cache[conversionRoot]?
        let named ← NativeNamedGeneralization.namedGenBlock? SourceProfileModels.policy input conversion binder (origin,serial)
        let (next, nextRoot) ← GraphExpansion.emitBlock SourceProfileModels.policy
          [currentRoot,conversionRoot] named.block.certificate current
        current := next
        currentRoot := nextRoot
        serial := serial+1
      let block ← NativeNamedGeneralization.checkBlock? SourceProfileModels.policy
        [seed,universal,truth] (GraphExpansion.finish current currentRoot)
      if matched : ExactFormulaReadback.matchesB block.result ops.signature.secondLaw = true then
        if only : InferenceOnlyReplay.inferenceOnly block.certificate.1 = true then
          if tags : block.result.axioms = seed.axioms then
            return ⟨block,base.1,matched,only,tags⟩
          else none
        else none
      else none
    else none
  else none

def compile? (ops : Operations) (seed universal truth : Theorem) (origin : String) :
    Option (Compiled ops seed universal truth) :=
  compileWith? ops seed universal truth
    [(ops.numberType,.var (.global "A")),(ops.numberType,.var (.global "B"))]
    [⟨.global "y",ops.numberType⟩,⟨.global "x",ops.numberType⟩] origin

private def readFrom (state : Registered.State) (index : Nat) (formula : HOL.ClosedFormula Symbol)
    (fact : Theorem) (found : state.cache[index]? = some fact)
    (matched : ExactFormulaReadback.matchesB fact formula = true) : ExactFormulaReadback.ReadFact state formula :=
  ⟨fact,Array.mem_of_getElem? found,(ExactFormulaReadback.matches_sound matched).1,
    (ExactFormulaReadback.matches_sound matched).2⟩

private theorem readFrom_eq (state : Registered.State) (index : Nat) (formula : HOL.ClosedFormula Symbol)
    (fact : Theorem) (found : state.cache[index]? = some fact)
    (matched : ExactFormulaReadback.matchesB fact formula = true) :
    ExactFormulaReadback.read? state index formula = some (readFrom state index formula fact found matched) := by
  unfold ExactFormulaReadback.read?
  split
  · rename_i missing
    rw [found] at missing
    cases missing
  · rename_i value present
    have same : value = fact := Option.some.inj (present.symm.trans found)
    subst value
    simp only [dif_pos matched]
    rfl

/-- Install only after actual prefix lookups and actual signature formation
are certified. Full cache/receipt prefixes remain in the returned state. -/
def install (before : Registered.State) (ops : Operations) (inputs : Inputs)
    (seed universal truth : Theorem) (compiled : Compiled ops seed universal truth)
    (instances : SignatureFormation.InstanceWitnesses)
    (selected : DerivationGraph.lookupPremises before.cache
      [inputs.seed,inputs.universalDefinition,inputs.truthDefinition] = some [seed,universal,truth])
    (seedFound : before.cache[inputs.seed]? = some seed)
    (formed : RegisteredProofBlocks.Formed before instances compiled.block.certificate.1) : Result before ops := by
  let roots := [inputs.seed,inputs.universalDefinition,inputs.truthDefinition]
  let expanded := GraphExpansion.expandBlock roots before.cache.size compiled.block.certificate
  let after := RegisteredProofBlocks.finish before instances expanded.1
  have replayed : Registered.replayFrom SourceProfileModels.policy before
      (RegisteredProofBlocks.commands instances expanded.1) = some after :=
    RegisteredProofBlocks.relocated_replay SourceProfileModels.policy before instances roots
      [seed,universal,truth] compiled.block.result compiled.block.certificate selected compiled.block.checked formed
  have found : after.cache[expanded.2]? = some compiled.block.result :=
    RegisteredProofBlocks.relocated_root SourceProfileModels.policy before instances roots
      [seed,universal,truth] compiled.block.result compiled.block.certificate selected compiled.block.checked
  let reading := readFrom after expanded.2 ops.signature.secondLaw compiled.block.result found compiled.finalMatches
  exact {
    after := after
    instances := instances
    nodes := expanded.1
    replayed := replayed
    context_eq := rfl
    inferenceOnly := (NativeProductClosure.relocated_inferenceOnly roots before.cache.size compiled.block.certificate).trans compiled.inferenceOnly
    old_lookup := fun _ _ old => Registered.replayFrom_preserves_lookup SourceProfileModels.policy before _ after replayed old
    seed := readFrom before inputs.seed (genericSeed ops) seed seedFound compiled.seedMatches
    root := expanded.2
    second := reading
    read := readFrom_eq after expanded.2 ops.signature.secondLaw compiled.block.result found compiled.finalMatches
    found := found
    axioms_eq := compiled.axioms_eq }

section Installation

variable (before : Registered.State) (ops : Operations) (inputs : Inputs)
  (seed universal truth : Theorem) (compiled : Compiled ops seed universal truth)
  (instances : SignatureFormation.InstanceWitnesses)
  (selected : DerivationGraph.lookupPremises before.cache
    [inputs.seed,inputs.universalDefinition,inputs.truthDefinition] = some [seed,universal,truth])
  (seedFound : before.cache[inputs.seed]? = some seed)
  (formed : RegisteredProofBlocks.Formed before instances compiled.block.certificate.1)

theorem install_nodes :
    (install before ops inputs seed universal truth compiled instances selected seedFound formed).nodes =
      (GraphExpansion.expandBlock [inputs.seed,inputs.universalDefinition,inputs.truthDefinition]
        before.cache.size compiled.block.certificate).1 := rfl

theorem install_root :
    (install before ops inputs seed universal truth compiled instances selected seedFound formed).root =
      (GraphExpansion.expandBlock [inputs.seed,inputs.universalDefinition,inputs.truthDefinition]
        before.cache.size compiled.block.certificate).2 := rfl

theorem install_after :
    (install before ops inputs seed universal truth compiled instances selected seedFound formed).after =
      RegisteredProofBlocks.finish before instances
        (GraphExpansion.expandBlock [inputs.seed,inputs.universalDefinition,inputs.truthDefinition]
          before.cache.size compiled.block.certificate).1 := rfl

end Installation

theorem Result.cache_eq {before : Registered.State} {ops : Operations} (result : Result before ops) :
    result.after.cache = before.cache ++ (result.nodes.map (·.conclusion)).toArray := by
  have checked := (Registered.replayProofs_primitive SourceProfileModels.policy before result.nodes
    result.instances result.replayed).2.1
  exact (DerivationGraph.replayFrom_eq_materialize (ruleWitness SourceProfileModels.policy) checked).trans
    (RegisteredProofBlocks.materialize_eq_append before.cache result.nodes)

theorem Result.receipts_eq {before : Registered.State} {ops : Operations} (result : Result before ops) :
    result.after.receipts = before.receipts ++ (RegisteredProofBlocks.receipts result.instances result.nodes).toArray :=
  RegisteredProofBlocks.replay_proof_receipts SourceProfileModels.policy before result.instances result.nodes result.replayed

noncomputable def Result.frame {before : Registered.State} {ops : Operations} (result : Result before ops)
    (profile : SourceProfileModels.ProfileFrame.{w} before) : SourceProfileModels.ProfileFrame.{w} result.after :=
  SourceProofSuffix.carry profile result.instances result.nodes result.replayed

theorem Result.frame_model {before : Registered.State} {ops : Operations} (result : Result before ops)
    (profile : SourceProfileModels.ProfileFrame.{w} before) (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (result.frame profile).frame.model other assignment = profile.frame.model other assignment :=
  SourceProofSuffix.carry_model profile result.instances result.nodes result.replayed other assignment

theorem Result.in_prefix_model {before : Registered.State} {ops : Operations} (result : Result before ops)
    (profile : SourceProfileModels.ProfileFrame.{w} before) (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (profile.frame.model other assignment).models ops.signature.secondLaw :=
  SourceProofSuffix.read_in_prefix_model profile result.instances result.nodes result.replayed other assignment _ result.second

/-- Later actual declarations may change interpretation. The retained syntax
certificate is transported by actual cache growth, without equating models. -/
def Result.retain {before later : Registered.State} {ops : Operations} (result : Result before ops)
    (commands : List Registered.Command)
    (replayed : Registered.replayFrom SourceProfileModels.policy result.after commands = some later) :
    ExactFormulaReadback.ReadFact later ops.signature.secondLaw where
  fact := result.second.fact
  known := Array.mem_of_getElem? (Registered.replayFrom_preserves_lookup SourceProfileModels.policy
    result.after commands later replayed result.found)
  closed := result.second.closed
  translated := result.second.translated

def ofNative (ops : NativeClauseData.Operations) : Operations :=
  ⟨ops.o3,ops.o4,ops.c4,ops.c51,ops.c52⟩

theorem ofNative_signature (ops : NativeClauseData.Operations) :
    (ofNative ops).signature = NativeTheoremRowSource.pairSignature ops := rfl

/-- Consumption in a later full source frame needs actual declaration identity,
not matching printed names. No HD fact or full native table is manufactured. -/
def asNativeSecond {state : Registered.State} (ops : Operations) (native : NativeClauseData.Operations)
    (same : ops = ofNative native) (reading : ExactFormulaReadback.ReadFact state ops.signature.secondLaw) :
    ExactFormulaReadback.ReadFact state (NativeTheoremRowSource.pairSignature native).secondLaw := by
  subst ops
  exact reading

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberPairProjection
