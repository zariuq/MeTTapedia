import Mettapedia.GSLT.LanguageDef.OptimizedFirstOrderFramePipeline

/-!
# Physical refinement for the generic two-phase frame machine

The native machine stores binder and matching instructions in separate arrays.
Each instruction retains its coordinate in the original stack suffix, so
interleaved source roles remain observable without reconstructing an ordered
instruction list.  Binder slots are dense finite indices, optional apartness
obligations are supplied as data, and the conclusion uses the same compact
literal-head carrier as matching hypotheses.

This module models that physical layout independently of any guest language.
The main theorem proves that split-array execution has the same complete
partial result as the already-certified optimized frame pipeline.  Admission
additionally recognizes the native invariant that every dense slot is bound
exactly once.
-/

namespace Mettapedia.GSLT.LanguageDef.TwoPhaseFrameMachinePhysicalRefinement

open FirstOrderFrameCompilation
open OptimizedFirstOrderFramePipeline

universe uToken

abbrev Formula (Token : Type uToken) := List Token
abbrev DenseSubstitution (width : Nat) (Token : Type uToken) :=
  Substitution (Fin width) Token
abbrev ApartCheck (Token : Type uToken) :=
  Formula Token -> Formula Token -> Option Unit

structure PhysicalBind (Token : Type uToken) (width : Nat) where
  stackOffset : Nat
  slot : Fin width
  typeHead : Token
deriving DecidableEq, Repr

structure PhysicalMatch (Token : Type uToken) (width : Nat) where
  stackOffset : Nat
  pattern : CompiledTemplate Token (Fin width)
deriving DecidableEq, Repr

structure PhysicalFrame (Token : Type uToken) (width : Nat) where
  binds : List (PhysicalBind Token width)
  checks : List (PhysicalMatch Token width)
  apart : List (Fin width × Fin width)
  conclusion : CompiledTemplate Token (Fin width)
  stackArity : Nat
deriving DecidableEq, Repr

structure SourceProgram (Token : Type uToken) (width : Nat) where
  frame : Frame Token (Fin width)
  apart : List (Fin width × Fin width)
deriving DecidableEq, Repr

def compileBindsFrom (offset : Nat) :
    List (Instruction Token (Fin width)) ->
      List (PhysicalBind Token width)
  | [] => []
  | .bind specification :: instructions =>
      { stackOffset := offset
        slot := specification.holeId
        typeHead := specification.head } ::
        compileBindsFrom (offset + 1) instructions
  | .check _ :: instructions =>
      compileBindsFrom (offset + 1) instructions

def compileMatchesFrom (offset : Nat) :
    List (Instruction Token (Fin width)) ->
      List (PhysicalMatch Token width)
  | [] => []
  | .bind _ :: instructions =>
      compileMatchesFrom (offset + 1) instructions
  | .check pattern :: instructions =>
      { stackOffset := offset, pattern } ::
        compileMatchesFrom (offset + 1) instructions

def compile (source : SourceProgram Token width) :
    PhysicalFrame Token width where
  binds := compileBindsFrom 0 source.frame.instructions
  checks := compileMatchesFrom 0 source.frame.instructions
  apart := source.apart
  conclusion := source.frame.conclusion
  stackArity := source.frame.instructions.length

def binderSlots : List (Instruction Token (Fin width)) -> List (Fin width)
  | [] => []
  | .bind specification :: instructions =>
      specification.holeId :: binderSlots instructions
  | .check _ :: instructions => binderSlots instructions

/-- The same finite, decidable binder-layout condition checked by the native
admission boundary: one unique binder for every dense slot.  Apartness is an
ordered obligation list: repeated obligations remain admissible and execute
repeatedly unless a separately certified idempotence pass removes them. -/
def admits (source : SourceProgram Token width) : Bool :=
  decide ((binderSlots source.frame.instructions).Nodup) &&
    decide ((binderSlots source.frame.instructions).length = width) &&
    source.apart.all (fun pair => decide (pair.1 ≠ pair.2))

structure AdmittedSource (Token : Type uToken) (width : Nat) where
  source : SourceProgram Token width
  accepted : admits source = true

def admit? (source : SourceProgram Token width) :
    Option (AdmittedSource Token width) :=
  if accepted : admits source = true then
    some { source, accepted }
  else none

def physicalOffsets (frame : PhysicalFrame Token width) : List Nat :=
  frame.binds.map PhysicalBind.stackOffset ++
    frame.checks.map PhysicalMatch.stackOffset

theorem compileBindsFrom_map_slot
    (offset : Nat) (instructions : List (Instruction Token (Fin width))) :
    (compileBindsFrom offset instructions).map PhysicalBind.slot =
      binderSlots instructions := by
  induction instructions generalizing offset with
  | nil => rfl
  | cons instruction instructions inductionHypothesis =>
      cases instruction <;> simp [compileBindsFrom, binderSlots,
        inductionHypothesis]

theorem compileBindsFrom_length
    (offset : Nat) (instructions : List (Instruction Token (Fin width))) :
    (compileBindsFrom offset instructions).length =
      (binderSlots instructions).length := by
  simpa using congrArg List.length
    (compileBindsFrom_map_slot offset instructions)

theorem compileOffsetsFrom_perm_range'
    (offset : Nat) (instructions : List (Instruction Token (Fin width))) :
    ((compileBindsFrom offset instructions).map PhysicalBind.stackOffset ++
      (compileMatchesFrom offset instructions).map
        PhysicalMatch.stackOffset).Perm
      (List.range' offset instructions.length) := by
  induction instructions generalizing offset with
  | nil => simp [compileBindsFrom, compileMatchesFrom]
  | cons instruction instructions inductionHypothesis =>
      cases instruction with
      | bind specification =>
          simpa [compileBindsFrom, compileMatchesFrom, List.range'_succ]
            using
              (inductionHypothesis (offset + 1)).cons offset
      | check pattern =>
          have moved :
              ((compileBindsFrom (offset + 1) instructions).map
                    PhysicalBind.stackOffset ++
                  offset ::
                    (compileMatchesFrom (offset + 1) instructions).map
                      PhysicalMatch.stackOffset).Perm
                (offset ::
                  ((compileBindsFrom (offset + 1) instructions).map
                      PhysicalBind.stackOffset ++
                    (compileMatchesFrom (offset + 1) instructions).map
                      PhysicalMatch.stackOffset)) :=
            List.perm_middle
          exact moved.trans <| by
            simpa [List.range'_succ] using
              (inductionHypothesis (offset + 1)).cons offset

structure NativeShapeValid (frame : PhysicalFrame Token width) : Prop where
  bindCount : frame.binds.length = width
  instructionCount :
    frame.binds.length + frame.checks.length = frame.stackArity
  offsetsNodup : (physicalOffsets frame).Nodup
  offsetsBounded : ∀ offset ∈ physicalOffsets frame,
    offset < frame.stackArity
  slotsNodup : (frame.binds.map PhysicalBind.slot).Nodup
  apartIrreflexive : ∀ pair ∈ frame.apart, pair.1 ≠ pair.2

theorem compile_nativeShapeValid
    (admitted : AdmittedSource Token width) :
    NativeShapeValid (compile admitted.source) := by
  have accepted := admitted.accepted
  simp only [admits, Bool.and_eq_true] at accepted
  rcases accepted with
    ⟨⟨slotsNodup, bindCount⟩, apartIrreflexive⟩
  have offsetsPerm := compileOffsetsFrom_perm_range'
    0 admitted.source.frame.instructions
  refine
    { bindCount := by
        simpa [compile, compileBindsFrom_length] using bindCount
      instructionCount := ?_
      offsetsNodup := ?_
      offsetsBounded := ?_
      slotsNodup := ?_
      apartIrreflexive := ?_ }
  · have lengths := offsetsPerm.length_eq
    simpa [compile, physicalOffsets] using lengths
  · exact (offsetsPerm.nodup_iff).2 List.nodup_range'
  · intro offset member
    have rangeMember :
        offset ∈ List.range' 0 admitted.source.frame.instructions.length :=
      offsetsPerm.mem_iff.mp member
    obtain ⟨relative, relativeBound, equal⟩ :=
      List.mem_range'.mp rangeMember
    simp only [compile]
    omega
  · simpa [compile, compileBindsFrom_map_slot] using slotsNodup
  · simpa [compile, List.all_eq_true] using apartIrreflexive

def runPhysicalBinders [DecidableEq Token] :
    List (PhysicalBind Token width) -> List (Formula Token) ->
      DenseSubstitution width Token ->
        Option (DenseSubstitution width Token)
  | [], _, substitution => some substitution
  | instruction :: instructions, stack, substitution => do
      let input <- stack[instruction.stackOffset]?
      let next <- bindOne substitution
        { head := instruction.typeHead, holeId := instruction.slot } input
      runPhysicalBinders instructions stack next

def runPhysicalMatches [DecidableEq Token]
    (substitution : DenseSubstitution width Token) :
    List (PhysicalMatch Token width) -> List (Formula Token) -> Option Unit
  | [], _ => some ()
  | instruction :: instructions, stack => do
      let input <- stack[instruction.stackOffset]?
      let _ <- LiteralHeadSeparationCompilation.matchRepresentation
        substitution instruction.pattern input
      runPhysicalMatches substitution instructions stack

def runApart (apartCheck : ApartCheck Token)
    (substitution : DenseSubstitution width Token) :
    List (Fin width × Fin width) -> Option Unit
  | [] => some ()
  | pair :: pairs => do
      let left <- substitution pair.1
      let right <- substitution pair.2
      let _ <- apartCheck left right
      runApart apartCheck substitution pairs

def runPhysical [DecidableEq Token]
    (apartCheck : ApartCheck Token) (frame : PhysicalFrame Token width)
    (stack : List (Formula Token)) : Option (Formula Token) :=
  if frame.stackArity = stack.length then do
    let substitution <- runPhysicalBinders frame.binds stack emptySubstitution
    let _ <- runPhysicalMatches substitution frame.checks stack
    let _ <- runApart apartCheck substitution frame.apart
    LiteralHeadSeparationCompilation.instantiateRepresentation
      substitution frame.conclusion
  else none

def runSource [DecidableEq Token]
    (apartCheck : ApartCheck Token) (source : SourceProgram Token width)
    (stack : List (Formula Token)) : Option (Formula Token) := do
  let substitution <- OptimizedFirstOrderFramePipeline.runBinders
    source.frame.instructions stack emptySubstitution
  let _ <- runMatches substitution source.frame.instructions stack
  let _ <- runApart apartCheck substitution source.apart
  LiteralHeadSeparationCompilation.instantiateRepresentation
    substitution source.frame.conclusion

theorem runPhysicalBinders_compileBindsFrom
    [DecidableEq Token]
    (prelude : List (Formula Token))
    (instructions : List (Instruction Token (Fin width)))
    (stack : List (Formula Token))
    (substitution : DenseSubstitution width Token)
    (aligned : instructions.length = stack.length) :
    runPhysicalBinders (compileBindsFrom prelude.length instructions)
        (prelude ++ stack) substitution =
      OptimizedFirstOrderFramePipeline.runBinders
        instructions stack substitution := by
  induction instructions generalizing prelude stack substitution with
  | nil =>
      simp only [List.length_nil] at aligned
      cases stack <;> simp_all [compileBindsFrom, runPhysicalBinders,
        OptimizedFirstOrderFramePipeline.runBinders]
  | cons instruction instructions inductionHypothesis =>
      cases stack with
      | nil => simp at aligned
      | cons input stack =>
          have tailAligned : instructions.length = stack.length := by
            simpa using aligned
          cases instruction with
          | bind specification =>
              simp only [compileBindsFrom, runPhysicalBinders]
              rw [show (prelude ++ input :: stack)[prelude.length]? =
                  some input by simp]
              have sameBinder :
                  (Binder.mk specification.head specification.holeId) =
                    specification := by
                cases specification
                rfl
              rw [sameBinder]
              simp only [OptimizedFirstOrderFramePipeline.runBinders]
              change
                (bindOne substitution specification input).bind
                    (fun next =>
                      runPhysicalBinders
                        (compileBindsFrom (prelude.length + 1) instructions)
                        (prelude ++ input :: stack) next) =
                  (bindOne substitution specification input).bind
                    (fun next =>
                      OptimizedFirstOrderFramePipeline.runBinders
                        instructions stack next)
              cases bound : bindOne substitution specification input with
              | none => simp
              | some next =>
                  simpa [List.append_assoc] using
                    inductionHypothesis (prelude ++ [input]) stack next
                      tailAligned
          | check pattern =>
              simp only [compileBindsFrom,
                OptimizedFirstOrderFramePipeline.runBinders]
              simpa [List.append_assoc] using
                inductionHypothesis (prelude ++ [input]) stack substitution
                  tailAligned

theorem runPhysicalMatches_compileMatchesFrom
    [DecidableEq Token]
    (prelude : List (Formula Token))
    (instructions : List (Instruction Token (Fin width)))
    (stack : List (Formula Token))
    (substitution : DenseSubstitution width Token)
    (aligned : instructions.length = stack.length) :
    runPhysicalMatches substitution
        (compileMatchesFrom prelude.length instructions) (prelude ++ stack) =
      runMatches substitution instructions stack := by
  induction instructions generalizing prelude stack with
  | nil =>
      simp only [List.length_nil] at aligned
      cases stack <;> simp_all [compileMatchesFrom, runPhysicalMatches,
        runMatches]
  | cons instruction instructions inductionHypothesis =>
      cases stack with
      | nil => simp at aligned
      | cons input stack =>
          have tailAligned : instructions.length = stack.length := by
            simpa using aligned
          cases instruction with
          | bind specification =>
              simp only [compileMatchesFrom, runMatches]
              simpa [List.append_assoc] using
                inductionHypothesis (prelude ++ [input]) stack tailAligned
          | check pattern =>
              simp only [compileMatchesFrom, runPhysicalMatches]
              rw [show (prelude ++ input :: stack)[prelude.length]? =
                  some input by simp]
              simp only [runMatches]
              change
                (LiteralHeadSeparationCompilation.matchRepresentation
                    substitution pattern input).bind
                    (fun _ =>
                      runPhysicalMatches substitution
                        (compileMatchesFrom (prelude.length + 1) instructions)
                        (prelude ++ input :: stack)) =
                  (LiteralHeadSeparationCompilation.matchRepresentation
                    substitution pattern input).bind
                    (fun _ => runMatches substitution instructions stack)
              cases matched :
                  LiteralHeadSeparationCompilation.matchRepresentation
                    substitution pattern input with
              | none => simp
              | some value =>
                  cases value
                  simpa [List.append_assoc] using
                    inductionHypothesis (prelude ++ [input]) stack tailAligned

theorem runBinders_eq_none_of_length_ne [DecidableEq Token]
    (instructions : List (Instruction Token (Fin width)))
    (stack : List (Formula Token))
    (substitution : DenseSubstitution width Token)
    (unaligned : instructions.length ≠ stack.length) :
    OptimizedFirstOrderFramePipeline.runBinders
        instructions stack substitution = none := by
  induction instructions generalizing stack substitution with
  | nil =>
      cases stack with
      | nil => contradiction
      | cons input stack => rfl
  | cons instruction instructions inductionHypothesis =>
      cases stack with
      | nil => rfl
      | cons input stack =>
          have tailUnaligned : instructions.length ≠ stack.length := by
            intro tailAligned
            apply unaligned
            simp [tailAligned]
          cases instruction with
          | bind specification =>
              simp only [OptimizedFirstOrderFramePipeline.runBinders]
              cases bound : bindOne substitution specification input with
              | none => rfl
              | some next =>
                  simpa using
                    inductionHypothesis stack next tailUnaligned
          | check pattern =>
              exact inductionHypothesis stack substitution tailUnaligned

/-- Split physical arrays preserve the complete optimized frame observation,
including stack-length rejection, matching failure, apartness failure, and
conclusion instantiation. -/
theorem runPhysical_compile [DecidableEq Token]
    (apartCheck : ApartCheck Token) (source : SourceProgram Token width)
    (stack : List (Formula Token)) :
    runPhysical apartCheck (compile source) stack =
      runSource apartCheck source stack := by
  by_cases aligned : source.frame.instructions.length = stack.length
  · unfold runPhysical runSource compile
    rw [if_pos aligned]
    have bindersRefinement :
        runPhysicalBinders
            (compileBindsFrom 0 source.frame.instructions) stack
            emptySubstitution =
          OptimizedFirstOrderFramePipeline.runBinders
            source.frame.instructions stack emptySubstitution := by
      simpa using runPhysicalBinders_compileBindsFrom
        ([] : List (Formula Token)) source.frame.instructions stack
        emptySubstitution aligned
    rw [bindersRefinement]
    cases bindersEq : OptimizedFirstOrderFramePipeline.runBinders
        source.frame.instructions stack emptySubstitution with
    | none => simp
    | some substitution =>
        have matchesRefinement :
            runPhysicalMatches substitution
                (compileMatchesFrom 0 source.frame.instructions) stack =
              runMatches substitution source.frame.instructions stack := by
          simpa using runPhysicalMatches_compileMatchesFrom
            ([] : List (Formula Token)) source.frame.instructions stack
            substitution aligned
        change
          (runPhysicalMatches substitution
              (compileMatchesFrom 0 source.frame.instructions) stack).bind
                (fun _ =>
                  (runApart apartCheck substitution source.apart).bind fun _ =>
                    LiteralHeadSeparationCompilation.instantiateRepresentation
                      substitution source.frame.conclusion) =
            (runMatches substitution source.frame.instructions stack).bind
                (fun _ =>
                  (runApart apartCheck substitution source.apart).bind fun _ =>
                    LiteralHeadSeparationCompilation.instantiateRepresentation
                      substitution source.frame.conclusion)
        exact congrArg
          (fun matched => matched.bind fun _ =>
            (runApart apartCheck substitution source.apart).bind fun _ =>
              LiteralHeadSeparationCompilation.instantiateRepresentation
                substitution source.frame.conclusion)
          matchesRefinement
  · have sourceRejected :
        OptimizedFirstOrderFramePipeline.runBinders
            source.frame.instructions stack emptySubstitution = none :=
      runBinders_eq_none_of_length_ne
        source.frame.instructions stack emptySubstitution aligned
    unfold runPhysical runSource compile
    rw [if_neg aligned]
    simp [sourceRejected]

def physicalFrameRealization [DecidableEq Token]
    (apartCheck : ApartCheck Token) :
    Mettapedia.GSLT.SimpleRealization
      (AdmittedSource Token width) (PhysicalFrame Token width)
      (List (Formula Token) -> Option (Formula Token)) where
  compile := fun _ source => compile source.source
  observeSource := fun _ source => runSource apartCheck source.source
  observeArtifact := fun _ frame => runPhysical apartCheck frame
  adequate := by
    intro _ source
    funext stack
    exact runPhysical_compile apartCheck source.source stack

/-! ## Generated symbolic plan and exact native admission -/

/-- The ten payload fields emitted for one two-phase frame call site. -/
structure GeneratedFramePlanRecord where
  operation : String
  actionIndex : UInt32
  machine : String
  carrier : String
  templateCarrier : String
  literalHeadPolicy : String
  slotCarrier : String
  binderValidation : String
  stackDiscipline : String
  region : String
  deriving DecidableEq, Repr

structure FramePlanRequest where
  operation : String
  actionIndex : UInt32
  machine : String
  templateCarrier : String
  region : String
  deriving DecidableEq, Repr

structure AdmittedFramePlan where
  operation : String
  actionIndex : UInt32
  machine : String
  templateCarrier : String
  region : String
  deriving DecidableEq, Repr

def genericFrameCarrier : String := "two-phase-frame-machine-v1"
def genericLiteralHeadPolicy : String := "literal-head-optional-v1"
def genericSlotCarrier : String := "epoch-stamped-dense-slots-v1"
def genericBinderValidation : String := "unique-dense-binders-v1"
def genericStackDiscipline : String := "exact-stack-suffix-v1"

/-- Decode only the closed, language-neutral carrier vocabulary.  Operation,
machine, template, and region identities remain generated data. -/
def decodeGeneratedFramePlan? (record : GeneratedFramePlanRecord) :
    Option AdmittedFramePlan :=
  if record.carrier != genericFrameCarrier then none
  else if record.literalHeadPolicy != genericLiteralHeadPolicy then none
  else if record.slotCarrier != genericSlotCarrier then none
  else if record.binderValidation != genericBinderValidation then none
  else if record.stackDiscipline != genericStackDiscipline then none
  else some
    { operation := record.operation
      actionIndex := record.actionIndex
      machine := record.machine
      templateCarrier := record.templateCarrier
      region := record.region }

def frameRequestMatches
    (plan : AdmittedFramePlan) (request : FramePlanRequest) : Bool :=
  plan.operation == request.operation &&
    plan.actionIndex == request.actionIndex &&
    plan.machine == request.machine &&
    plan.templateCarrier == request.templateCarrier &&
    plan.region == request.region

def admitGeneratedFramePlan? (record : GeneratedFramePlanRecord)
    (request : FramePlanRequest) : Option AdmittedFramePlan := do
  let plan <- decodeGeneratedFramePlan? record
  if frameRequestMatches plan request then some plan else none

theorem decodeGeneratedFramePlan?_eq_some_iff
    (record : GeneratedFramePlanRecord) (plan : AdmittedFramePlan) :
    decodeGeneratedFramePlan? record = some plan ↔
      record.carrier = genericFrameCarrier ∧
      record.literalHeadPolicy = genericLiteralHeadPolicy ∧
      record.slotCarrier = genericSlotCarrier ∧
      record.binderValidation = genericBinderValidation ∧
      record.stackDiscipline = genericStackDiscipline ∧
      plan =
        { operation := record.operation
          actionIndex := record.actionIndex
          machine := record.machine
          templateCarrier := record.templateCarrier
          region := record.region } := by
  simp only [decodeGeneratedFramePlan?]
  by_cases carrier : record.carrier = genericFrameCarrier
  · simp [carrier]
    by_cases literalHead :
        record.literalHeadPolicy = genericLiteralHeadPolicy
    · simp [literalHead]
      by_cases slots : record.slotCarrier = genericSlotCarrier
      · simp [slots]
        by_cases binders :
            record.binderValidation = genericBinderValidation
        · simp [binders]
          by_cases stack : record.stackDiscipline = genericStackDiscipline
          · simp [stack, eq_comm]
          · simp [stack]
        · simp [binders]
      · simp [slots]
    · simp [literalHead]
  · simp [carrier]

theorem admitGeneratedFramePlan?_request
    (record : GeneratedFramePlanRecord) (request : FramePlanRequest)
    (plan : AdmittedFramePlan)
    (admitted : admitGeneratedFramePlan? record request = some plan) :
    frameRequestMatches plan request = true := by
  simp only [admitGeneratedFramePlan?] at admitted
  cases decoded : decodeGeneratedFramePlan? record with
  | none => simp [decoded] at admitted
  | some accepted =>
      by_cases acceptedRequest : frameRequestMatches accepted request = true
      · have same : accepted = plan := by
          simpa [admitGeneratedFramePlan?, decoded, acceptedRequest] using
            admitted
        simpa [same] using acceptedRequest
      · simp [decoded, acceptedRequest] at admitted

/-! ## Structurally distinct witnesses and rejection boundaries -/

private def equalityApart {Token : Type} [DecidableEq Token] :
    ApartCheck Token := fun left right =>
  if left = right then none else some ()

private def proofProgram : SourceProgram Nat 2 where
  frame :=
    { instructions :=
        [ .bind { head := 10, holeId := 0 }
        , .check
            (LiteralHeadSeparationCompilation.lower
              [.literal 20, .hole 0, .literal 21, .hole 1])
        , .bind { head := 11, holeId := 1 } ]
      conclusion := LiteralHeadSeparationCompilation.lower
        [.literal 30, .hole 1, .hole 0] }
  apart := [(0, 1)]

example : admits proofProgram = true := by decide

private def repeatedApartProgram : SourceProgram Nat 2 :=
  { proofProgram with apart := [(0, 1), (0, 1)] }

example : admits repeatedApartProgram = true := by decide

example : runPhysical equalityApart (compile repeatedApartProgram)
    [[10, 7], [20, 7, 21, 9], [11, 9]] = some [30, 9, 7] := by
  decide

private def reflexiveApartProgram : SourceProgram Nat 2 :=
  { proofProgram with apart := [(0, 0)] }

example : admits reflexiveApartProgram = false := by decide

example : runPhysical equalityApart (compile proofProgram)
    [[10, 7], [20, 7, 21, 9], [11, 9]] = some [30, 9, 7] := by
  decide

private def parserProgram : SourceProgram String 1 where
  frame :=
    { instructions :=
        [ .bind { head := "value", holeId := 0 }
        , .check
            (LiteralHeadSeparationCompilation.lower
              [.literal "node", .hole 0]) ]
      conclusion := LiteralHeadSeparationCompilation.lower
        [.literal "accepted", .hole 0] }
  apart := []

example : admits parserProgram = true := by decide

example : runPhysical equalityApart (compile parserProgram)
    [["value", "x"], ["node", "x"]] = some ["accepted", "x"] := by
  decide

private def parserFrameRecord : GeneratedFramePlanRecord :=
  { operation := "parser-reduce"
    actionIndex := 3
    machine := "parser-frame"
    carrier := genericFrameCarrier
    templateCarrier := "parser-literal-hole-program"
    literalHeadPolicy := genericLiteralHeadPolicy
    slotCarrier := genericSlotCarrier
    binderValidation := genericBinderValidation
    stackDiscipline := genericStackDiscipline
    region := "parser-transaction" }

private def parserFrameRequest : FramePlanRequest :=
  { operation := "parser-reduce"
    actionIndex := 3
    machine := "parser-frame"
    templateCarrier := "parser-literal-hole-program"
    region := "parser-transaction" }

example : (admitGeneratedFramePlan? parserFrameRecord parserFrameRequest).isSome := by
  decide

example : decodeGeneratedFramePlan?
    { parserFrameRecord with stackDiscipline := "prefix-stack" } = none := by
  decide

example : admitGeneratedFramePlan? parserFrameRecord
    { parserFrameRequest with machine := "other-machine" } = none := by
  decide

private def missingBinderProgram : SourceProgram Nat 2 where
  frame :=
    { instructions := [.bind { head := 10, holeId := 0 }]
      conclusion := LiteralHeadSeparationCompilation.lower [.hole 0] }
  apart := []

example : admits missingBinderProgram = false := by decide

private def duplicateBinderProgram : SourceProgram Nat 2 where
  frame :=
    { instructions :=
        [ .bind { head := 10, holeId := 0 }
        , .bind { head := 10, holeId := 0 } ]
      conclusion := LiteralHeadSeparationCompilation.lower [.hole 0] }
  apart := []

example : admits duplicateBinderProgram = false := by decide

example : runPhysical equalityApart (compile proofProgram)
    [[10, 7], [20, 7, 21, 7], [11, 7]] = none := by
  decide

end Mettapedia.GSLT.LanguageDef.TwoPhaseFrameMachinePhysicalRefinement
