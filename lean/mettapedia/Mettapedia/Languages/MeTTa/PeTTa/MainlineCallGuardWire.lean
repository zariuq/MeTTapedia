import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan

/-!
# Revision-bound structural wire for mainline PeTTa call guards

The dynamic guard artifact is distinct from the five-field `LanguageDef` wire.
It carries the complete cache key and either an ordered compiled plan family or
an explicit outside-fragment result.  Plans contain occurrence provenance and
compiled modes, but never duplicate complete arrow declarations.

Decoding is relative to an authoritative resolved snapshot.  Declaration
occurrences are looked up there, and the reconstructed artifact is accepted
only when it is exactly produced by the G2 compiler at the current owner and
revision.  Structurally plausible, stale, reordered, omitted, duplicated, or
forged inputs therefore fail closed.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardWire

open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan

set_option autoImplicit false

/-! ## Self-contained compilation artifact -/

structure GuardArtifact where
  owner : SpaceOwner
  revision : Nat
  head : String
  arity : Nat
  result : CompilationResult
deriving DecidableEq, Repr

namespace GuardArtifact

def ResultCoordinatesAgree (artifact : GuardArtifact) : Prop :=
  match artifact.result with
  | .outsideFragment => True
  | .compiled family =>
      family.owner = artifact.owner ∧
        family.revision = artifact.revision ∧
          family.head = artifact.head ∧
            family.arity = artifact.arity

instance (artifact : GuardArtifact) :
    Decidable artifact.ResultCoordinatesAgree := by
  unfold ResultCoordinatesAgree
  split <;> infer_instance

/- Semantic admission for either a compiled family or a cached decline. -/
def ValidFor (artifact : GuardArtifact) (owned : OwnedSnapshot) : Prop :=
  owned.snapshot.WellFormed ∧
    artifact.owner = owned.owner ∧
      artifact.revision = owned.snapshot.revision ∧
        compileGuards owned artifact.head artifact.arity = artifact.result ∧
          artifact.ResultCoordinatesAgree

instance (artifact : GuardArtifact) (owned : OwnedSnapshot) :
    Decidable (artifact.ValidFor owned) := by
  unfold ValidFor
  infer_instance

def compile (owned : OwnedSnapshot) (head : String) (arity : Nat) :
    GuardArtifact :=
  { owner := owned.owner
    revision := owned.snapshot.revision
    head := head
    arity := arity
    result := compileGuards owned head arity }

theorem compile_validFor (owned : OwnedSnapshot) (head : String) (arity : Nat)
    (wellFormed : owned.snapshot.WellFormed) :
    (compile owned head arity).ValidFor owned := by
  constructor
  · exact wellFormed
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  unfold ResultCoordinatesAgree compile
  cases result : compileGuards owned head arity with
  | outsideFragment => trivial
  | compiled family =>
      exact compileGuards_coordinates result

theorem compiled_family_validFor
    {artifact : GuardArtifact} {owned : OwnedSnapshot}
    {family : CompiledGuardFamily}
    (valid : artifact.ValidFor owned)
    (compiled : artifact.result = .compiled family) :
    family.ValidFor owned := by
  rcases valid with
    ⟨wellFormed, ownerExact, revisionExact, produced, coordinates⟩
  rw [compiled] at produced
  simp only [ResultCoordinatesAgree, compiled] at coordinates
  refine ⟨wellFormed, ?_, ?_⟩
  · exact ⟨coordinates.1.trans ownerExact,
      coordinates.2.1.trans revisionExact⟩
  · simpa [coordinates.2.2.1, coordinates.2.2.2] using produced

end GuardArtifact

/-! ## Dedicated structural schema -/

def rootTag : String := "PeTTaMainlineCallGuardArtifactV1"
def schemaVersion : Nat := 1

inductive WireArgMode where
  | rawAtom
  | evalUnchecked
  | evalSoftcutType (expected : Term)
deriving DecidableEq, Repr

inductive WireResultMode where
  | resultUnchecked
  | resultSoftcutType (expected : Term)
deriving DecidableEq, Repr

structure WireGuardPlan where
  occurrence : Nat
  argumentModes : List WireArgMode
  resultMode : WireResultMode
deriving DecidableEq, Repr

inductive WireCompilationResult where
  | compiled (plans : List WireGuardPlan)
  | outsideFragment
deriving DecidableEq, Repr

structure StructuralWire where
  root : String
  version : Nat
  ownerToken : Nat
  revision : Nat
  head : String
  arity : Nat
  result : WireCompilationResult
  trailingFields : List String := []
deriving DecidableEq, Repr

def WireArgMode.encode : ArgMode → WireArgMode
  | .rawAtom => .rawAtom
  | .evalUnchecked => .evalUnchecked
  | .evalSoftcutType expected => .evalSoftcutType expected

def WireArgMode.decode : WireArgMode → ArgMode
  | .rawAtom => .rawAtom
  | .evalUnchecked => .evalUnchecked
  | .evalSoftcutType expected => .evalSoftcutType expected

@[simp] theorem WireArgMode.decode_encode (mode : ArgMode) :
    (WireArgMode.encode mode).decode = mode := by
  cases mode <;> rfl

@[simp] theorem WireArgMode.encode_decode (mode : WireArgMode) :
    WireArgMode.encode (WireArgMode.decode mode) = mode := by
  cases mode <;> rfl

def WireResultMode.encode : ResultMode → WireResultMode
  | .resultUnchecked => .resultUnchecked
  | .resultSoftcutType expected => .resultSoftcutType expected

def WireResultMode.decode : WireResultMode → ResultMode
  | .resultUnchecked => .resultUnchecked
  | .resultSoftcutType expected => .resultSoftcutType expected

@[simp] theorem WireResultMode.decode_encode (mode : ResultMode) :
    (WireResultMode.encode mode).decode = mode := by
  cases mode <;> rfl

@[simp] theorem WireResultMode.encode_decode (mode : WireResultMode) :
    WireResultMode.encode (WireResultMode.decode mode) = mode := by
  cases mode <;> rfl

def WireGuardPlan.encode (plan : GuardPlan) : WireGuardPlan :=
  { occurrence := plan.declarationOccurrence
    argumentModes := plan.argumentModes.map WireArgMode.encode
    resultMode := WireResultMode.encode plan.resultMode }

def lookupDeclaration? (occurrence : Nat) :
    List ArrowDeclaration → Option ArrowDeclaration
  | [] => none
  | declaration :: declarations =>
      if declaration.occurrence = occurrence then
        some declaration
      else
        lookupDeclaration? occurrence declarations

theorem lookupDeclaration?_exact
    {declarations : List ArrowDeclaration} {declaration : ArrowDeclaration}
    (occurrencesUnique :
      (declarations.map ArrowDeclaration.occurrence).Nodup)
    (member : declaration ∈ declarations) :
    lookupDeclaration? declaration.occurrence declarations = some declaration := by
  induction declarations with
  | nil => simp at member
  | cons first rest inductionHypothesis =>
      simp only [List.map_cons, List.nodup_cons] at occurrencesUnique
      rcases occurrencesUnique with ⟨firstFresh, restUnique⟩
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp [lookupDeclaration?]
      · have different : first.occurrence ≠ declaration.occurrence := by
          intro equal
          apply firstFresh
          rw [equal]
          exact List.mem_map.2 ⟨declaration, member, rfl⟩
        simp [lookupDeclaration?, different,
          inductionHypothesis restUnique member]

def WireGuardPlan.decode? (snapshot : Snapshot)
    (wirePlan : WireGuardPlan) : Option GuardPlan := do
  let declaration ← lookupDeclaration? wirePlan.occurrence snapshot.declarations
  pure
    { declarationOccurrence := wirePlan.occurrence
      argumentModes := wirePlan.argumentModes.map WireArgMode.decode
      resultMode := wirePlan.resultMode.decode
      declaration := declaration }

def decodePlans? (snapshot : Snapshot) :
    List WireGuardPlan → Option (List GuardPlan)
  | [] => some []
  | wirePlan :: wirePlans => do
      let plan ← wirePlan.decode? snapshot
      let plans ← decodePlans? snapshot wirePlans
      pure (plan :: plans)

def encodeResult : CompilationResult → WireCompilationResult
  | .outsideFragment => .outsideFragment
  | .compiled family => .compiled (family.plans.map WireGuardPlan.encode)

def decodeResult? (owned : OwnedSnapshot) (head : String) (arity : Nat) :
    WireCompilationResult → Option CompilationResult
  | .outsideFragment => some .outsideFragment
  | .compiled wirePlans => do
      let plans ← decodePlans? owned.snapshot wirePlans
      pure (.compiled
        { owner := owned.owner
          revision := owned.snapshot.revision
          head := head
          arity := arity
          plans := plans })

def encode (artifact : GuardArtifact) : StructuralWire :=
  { root := rootTag
    version := schemaVersion
    ownerToken := artifact.owner.token
    revision := artifact.revision
    head := artifact.head
    arity := artifact.arity
    result := encodeResult artifact.result
    trailingFields := [] }

/- Authoritative structural decoding. -/
def decode? (owned : OwnedSnapshot) (wire : StructuralWire) :
    Option GuardArtifact :=
  if wire.root = rootTag then
    if wire.version = schemaVersion then
      if wire.trailingFields = [] then
        if wire.ownerToken = owned.owner.token then
          if wire.revision = owned.snapshot.revision then
            match decodeResult? owned wire.head wire.arity wire.result with
            | none => none
            | some result =>
                let artifact : GuardArtifact :=
                  { owner := ⟨wire.ownerToken⟩
                    revision := wire.revision
                    head := wire.head
                    arity := wire.arity
                    result := result }
                if artifact.ValidFor owned then some artifact else none
          else none
        else none
      else none
    else none
  else none

/-! ## Structural soundness and round trips -/

theorem decode_sound_validFor
    {owned : OwnedSnapshot} {wire : StructuralWire}
    {artifact : GuardArtifact}
    (decoded : decode? owned wire = some artifact) :
    artifact.ValidFor owned := by
  unfold decode? at decoded
  split at decoded <;> simp_all
  split at decoded <;> simp_all
  rename_i result resultDecoded
  rcases decoded with ⟨_, _, _, _, candidateValid, rfl⟩
  exact candidateValid

theorem lookupDeclaration?_occurrence_exact
    {occurrence : Nat} {declarations : List ArrowDeclaration}
    {declaration : ArrowDeclaration}
    (lookup : lookupDeclaration? occurrence declarations = some declaration) :
    declaration.occurrence = occurrence := by
  induction declarations with
  | nil => simp [lookupDeclaration?] at lookup
  | cons first rest inductionHypothesis =>
      by_cases equal : first.occurrence = occurrence
      · simp [lookupDeclaration?, equal] at lookup
        subst declaration
        exact equal
      · simp [lookupDeclaration?, equal] at lookup
        exact inductionHypothesis lookup

theorem decode_encode_plan_of_valid
    {snapshot : Snapshot} {plan : GuardPlan}
    (valid : plan.ValidIn snapshot) :
    WireGuardPlan.decode? snapshot (WireGuardPlan.encode plan) = some plan := by
  have coordinates := compileGuard_coordinateConsistent valid.2.2
  have lookup := lookupDeclaration?_exact valid.1.1 valid.2.1
  unfold WireGuardPlan.decode? WireGuardPlan.encode
  rw [coordinates.1]
  simp [lookup, List.map_map, Function.comp_def]
  cases plan
  congr
  exact coordinates.1.symm

theorem encode_decode_plan
    {snapshot : Snapshot} {wirePlan : WireGuardPlan} {plan : GuardPlan}
    (decoded : wirePlan.decode? snapshot = some plan) :
    WireGuardPlan.encode plan = wirePlan := by
  cases lookup : lookupDeclaration? wirePlan.occurrence
      snapshot.declarations with
  | none => simp [WireGuardPlan.decode?, lookup] at decoded
  | some declaration =>
    simp [WireGuardPlan.decode?, lookup] at decoded
    subst plan
    cases wirePlan
    simp [WireGuardPlan.encode, List.map_map, Function.comp_def]

private theorem decode_encode_plans_of_all_valid
    {snapshot : Snapshot} {plans : List GuardPlan}
    (allValid : ∀ plan ∈ plans, plan.ValidIn snapshot) :
    decodePlans? snapshot (plans.map WireGuardPlan.encode) = some plans := by
  induction plans with
  | nil => rfl
  | cons plan plans inductionHypothesis =>
      have planValid := allValid plan (by simp)
      have tailValid : ∀ candidate ∈ plans,
          candidate.ValidIn snapshot := by
        intro candidate member
        exact allValid candidate (by simp [member])
      simp [decodePlans?, decode_encode_plan_of_valid planValid,
        inductionHypothesis tailValid]

theorem encode_decode_plans
    {snapshot : Snapshot} {wirePlans : List WireGuardPlan}
    {plans : List GuardPlan}
    (decoded : decodePlans? snapshot wirePlans = some plans) :
    plans.map WireGuardPlan.encode = wirePlans := by
  induction wirePlans generalizing plans with
  | nil => simp [decodePlans?] at decoded; subst plans; rfl
  | cons wirePlan wirePlans inductionHypothesis =>
      cases planResult : wirePlan.decode? snapshot with
      | none => simp [decodePlans?, planResult] at decoded
      | some plan =>
          cases tailResult : decodePlans? snapshot wirePlans with
          | none => simp [decodePlans?, planResult, tailResult] at decoded
          | some plansTail =>
              simp [decodePlans?, planResult, tailResult] at decoded
              subst plans
              simp [encode_decode_plan planResult,
                inductionHypothesis tailResult]

theorem decode_encode_plans_of_family_valid
    {owned : OwnedSnapshot} {family : CompiledGuardFamily}
    (valid : family.ValidFor owned) :
    decodePlans? owned.snapshot (family.plans.map WireGuardPlan.encode) =
      some family.plans := by
  apply decode_encode_plans_of_all_valid
  intro plan member
  exact (family.validFor_plan_valid valid member).1

theorem encode_decode_result
    {owned : OwnedSnapshot} {head : String} {arity : Nat}
    {wireResult : WireCompilationResult} {result : CompilationResult}
    (decoded : decodeResult? owned head arity wireResult = some result) :
    encodeResult result = wireResult := by
  cases wireResult with
  | outsideFragment =>
      simp [decodeResult?] at decoded
      subst result
      rfl
  | compiled wirePlans =>
      cases plansResult : decodePlans? owned.snapshot wirePlans with
      | none => simp [decodeResult?, plansResult] at decoded
      | some plans =>
        simp [decodeResult?, plansResult] at decoded
        subst result
        simp [encodeResult, encode_decode_plans plansResult]

theorem decode_encode_of_valid
    {owned : OwnedSnapshot} {artifact : GuardArtifact}
    (valid : artifact.ValidFor owned) :
    decode? owned (encode artifact) = some artifact := by
  rcases artifact with ⟨owner, revision, head, arity, result⟩
  simp only [GuardArtifact.ValidFor] at valid
  rcases valid with
    ⟨wellFormed, ownerExact, revisionExact, produced, coordinates⟩
  subst owner
  subst revision
  cases result with
  | outsideFragment =>
      simp [encode, decode?, decodeResult?, encodeResult,
        rootTag, schemaVersion, GuardArtifact.ValidFor,
        GuardArtifact.ResultCoordinatesAgree, wellFormed, produced]
  | compiled family =>
      have artifactValid :
          (GuardArtifact.mk owned.owner owned.snapshot.revision head arity
            (.compiled family)).ValidFor owned :=
        ⟨wellFormed, rfl, rfl, produced, coordinates⟩
      have familyValid := GuardArtifact.compiled_family_validFor
        artifactValid rfl
      have plansDecoded := decode_encode_plans_of_family_valid familyValid
      have familyExact :
          (CompiledGuardFamily.mk owned.owner owned.snapshot.revision
            head arity family.plans) = family := by
        rcases coordinates with
          ⟨ownerCoordinate, revisionCoordinate, headCoordinate,
            arityCoordinate⟩
        cases family
        simp_all
      simp [encode, decode?, decodeResult?, encodeResult, plansDecoded,
        rootTag, schemaVersion, artifactValid, familyExact]

theorem encode_decode_canonical
    {owned : OwnedSnapshot} {wire : StructuralWire}
    {artifact : GuardArtifact}
    (decoded : decode? owned wire = some artifact) :
    encode artifact = wire := by
  unfold decode? at decoded
  split at decoded <;> simp_all
  split at decoded <;> simp_all
  rename_i result resultDecoded
  rcases decoded with
    ⟨versionExact, trailingExact, ownerExact, revisionExact,
      candidateValid, candidateExact⟩
  subst artifact
  have resultExact := encode_decode_result resultDecoded
  cases wire
  simp_all [encode]

theorem decoded_owner_revision_head_arity_exact
    {owned : OwnedSnapshot} {wire : StructuralWire}
    {artifact : GuardArtifact}
    (decoded : decode? owned wire = some artifact) :
    artifact.owner = owned.owner ∧
      artifact.revision = owned.snapshot.revision ∧
        artifact.head = wire.head ∧ artifact.arity = wire.arity := by
  have valid := decode_sound_validFor decoded
  have canonical := encode_decode_canonical decoded
  exact ⟨valid.2.1, valid.2.2.1,
    by simpa [encode] using congrArg StructuralWire.head canonical,
    by simpa [encode] using congrArg StructuralWire.arity canonical⟩

theorem decoded_plan_occurrences_order_exact
    {owned : OwnedSnapshot} {wire : StructuralWire}
    {artifact : GuardArtifact} {family : CompiledGuardFamily}
    (decoded : decode? owned wire = some artifact)
    (compiled : artifact.result = .compiled family) :
    wire.result = .compiled
      (family.plans.map WireGuardPlan.encode) := by
  have canonical := encode_decode_canonical decoded
  simpa [encode, encodeResult, compiled] using
    congrArg StructuralWire.result canonical.symm

theorem decoded_plan_modes_exact
    {owned : OwnedSnapshot} {wire : StructuralWire}
    {artifact : GuardArtifact} {family : CompiledGuardFamily}
    (decoded : decode? owned wire = some artifact)
    (compiled : artifact.result = .compiled family) :
    wire.result = .compiled
      (family.plans.map fun plan =>
        { occurrence := plan.declarationOccurrence
          argumentModes := plan.argumentModes.map WireArgMode.encode
          resultMode := WireResultMode.encode plan.resultMode }) := by
  change wire.result = .compiled
    (family.plans.map WireGuardPlan.encode)
  exact decoded_plan_occurrences_order_exact decoded compiled

theorem decoded_artifact_no_invention
    {owned : OwnedSnapshot} {wire : StructuralWire}
    {artifact : GuardArtifact} {family : CompiledGuardFamily}
    {plan : GuardPlan}
    (decoded : decode? owned wire = some artifact)
    (compiled : artifact.result = .compiled family)
    (member : plan ∈ family.plans) :
    plan.declaration ∈ owned.snapshot.declarations := by
  have valid := decode_sound_validFor decoded
  have familyValid := GuardArtifact.compiled_family_validFor valid compiled
  exact (family.validFor_plan_valid familyValid member).1.2.1

theorem decoded_outsideFragment_ne_compiled_empty :
    WireCompilationResult.outsideFragment ≠ .compiled [] := by
  decide

theorem decoded_execution_exact
    {owned : OwnedSnapshot} {wire : StructuralWire}
    {artifact : GuardArtifact} {family : CompiledGuardFamily}
    (decoded : decode? owned wire = some artifact)
    (compiled : artifact.result = .compiled family)
    (call : Call) (requestMatches : family.MatchesCall call) :
    executeCompilation owned call artifact.result =
      .executed (successfulDeclarations ⟨owned.snapshot, call⟩) := by
  rw [compiled]
  have valid := decode_sound_validFor decoded
  exact executeCompilation_eq_successfulDeclarations owned call family
    (GuardArtifact.compiled_family_validFor valid compiled) requestMatches

/-! ## Canonical text rendering -/

private def quote (text : String) : String :=
  "\"" ++ (text.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

private def renderList (entries : List String) : String :=
  entries.foldr (fun entry rest => s!"(LCons {entry} {rest})") "LNil"

private def renderTerm : Term → String
  | .variable name => s!"(Variable {quote name})"
  | .number lexeme => s!"(Number {quote lexeme})"
  | .string value => s!"(String {quote value})"
  | .atom name => s!"(Atom {quote name})"
  | .list elements => s!"(List {renderList (elements.map renderTerm)})"

private def renderArgMode : WireArgMode → String
  | .rawAtom => "RawAtom"
  | .evalUnchecked => "EvalUnchecked"
  | .evalSoftcutType expected =>
      s!"(EvalSoftcutType {renderTerm expected})"

private def renderResultMode : WireResultMode → String
  | .resultUnchecked => "ResultUnchecked"
  | .resultSoftcutType expected =>
      s!"(ResultSoftcutType {renderTerm expected})"

private def renderPlan (plan : WireGuardPlan) : String :=
  s!"(Plan {plan.occurrence} " ++
    s!"{renderList (plan.argumentModes.map renderArgMode)} " ++
    s!"{renderResultMode plan.resultMode})"

private def renderResult : WireCompilationResult → String
  | .outsideFragment => "OutsideFragment"
  | .compiled plans => s!"(Compiled {renderList (plans.map renderPlan)})"

def render (wire : StructuralWire) : Option String :=
  if wire.root = rootTag ∧ wire.version = schemaVersion ∧
      wire.trailingFields = [] then
    some (s!"({rootTag} {wire.ownerToken} {wire.revision} " ++
      s!"{quote wire.head} {wire.arity} {renderResult wire.result})")
  else
    none

/-! ## Positive and adversarial canaries -/

namespace Canary

open Mettapedia.Languages.MeTTa.PeTTa.CallGuardNativeKernel
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan.Canary

def emptyArtifact : GuardArtifact :=
  GuardArtifact.compile
    (owned CallGuardNativeKernel.Canary.snapshot) "absent" 3

def overloadArtifact : GuardArtifact :=
  GuardArtifact.compile
    (owned CallGuardNativeKernel.Canary.overloadedClaim.snapshot) "f" 1

def duplicateArtifact : GuardArtifact :=
  GuardArtifact.compile duplicateSource.resolve "f" 1

def checkedArtifact : GuardArtifact :=
  GuardArtifact.compile (owned exactTypeSnapshot) "n" 1

def outsideArtifact : GuardArtifact :=
  GuardArtifact.compile (owned mixedSupportedAndOpenSnapshot) "f" 1

theorem current_empty_compiled_roundtrip :
    decode? (owned CallGuardNativeKernel.Canary.snapshot)
        (encode emptyArtifact) = some emptyArtifact ∧
      (encode emptyArtifact).result = .compiled [] := by
  decide

theorem overload_occurrence_order_roundtrip :
    decode? (owned CallGuardNativeKernel.Canary.overloadedClaim.snapshot)
        (encode overloadArtifact) = some overloadArtifact ∧
      (encode overloadArtifact).result = .compiled
        [{ occurrence := 10
           argumentModes := [.rawAtom]
           resultMode := .resultSoftcutType numberType },
         { occurrence := 13
           argumentModes := [.evalUnchecked]
           resultMode := .resultUnchecked }] := by
  decide

theorem duplicate_source_retains_first_occurrence :
    decode? duplicateSource.resolve (encode duplicateArtifact) =
        some duplicateArtifact ∧
      (encode duplicateArtifact).result = .compiled
        [{ occurrence := 10
           argumentModes := [.rawAtom]
           resultMode := .resultSoftcutType numberType }] := by
  decide

theorem checked_modes_roundtrip :
    decode? (owned exactTypeSnapshot) (encode checkedArtifact) =
        some checkedArtifact ∧
      (encode checkedArtifact).result = .compiled
        [{ occurrence := 21
           argumentModes := [.evalSoftcutType numberType]
           resultMode := .resultSoftcutType numberType }] := by
  decide

theorem outside_fragment_roundtrip :
    decode? (owned mixedSupportedAndOpenSnapshot) (encode outsideArtifact) =
        some outsideArtifact ∧
      (encode outsideArtifact).result = .outsideFragment := by
  decide

def rawWire : StructuralWire := encode checkedArtifact

theorem wrong_root_version_and_trailing_rejected :
    decode? (owned exactTypeSnapshot) { rawWire with root := "wrong" } = none ∧
      decode? (owned exactTypeSnapshot) { rawWire with version := 2 } = none ∧
      decode? (owned exactTypeSnapshot)
        { rawWire with trailingFields := ["extra"] } = none := by
  decide

theorem foreign_owner_and_stale_revision_rejected :
    decode? (owned exactTypeSnapshot)
        { rawWire with ownerToken := foreignOwner.token } = none ∧
      decode? (owned exactTypeSnapshot)
        { rawWire with revision := exactTypeSnapshot.revision + 1 } = none := by
  decide

theorem wrong_head_arity_and_unknown_occurrence_rejected :
    decode? (owned exactTypeSnapshot) { rawWire with head := "other" } = none ∧
      decode? (owned exactTypeSnapshot) { rawWire with arity := 2 } = none ∧
      decode? (owned exactTypeSnapshot)
        { rawWire with result := .compiled ([
            { occurrence := 999
              argumentModes := [.evalSoftcutType numberType]
              resultMode := .resultSoftcutType numberType }] :
            List WireGuardPlan) } = none := by
  decide

def exactWirePlan : WireGuardPlan :=
  { occurrence := 21
    argumentModes := [.evalSoftcutType numberType]
    resultMode := .resultSoftcutType numberType }

def reversedOverloadWirePlans : List WireGuardPlan :=
  [{ occurrence := 13
     argumentModes := [.evalUnchecked]
     resultMode := .resultUnchecked },
   { occurrence := 10
     argumentModes := [.rawAtom]
     resultMode := .resultSoftcutType numberType }]

def forgedModeWirePlan : WireGuardPlan :=
  { exactWirePlan with argumentModes := [.evalUnchecked] }

def forgedExpectedWirePlan : WireGuardPlan :=
  { exactWirePlan with
    argumentModes := [.evalSoftcutType stringType] }

theorem reordered_omitted_duplicated_and_forged_rejected :
    decode? (owned CallGuardNativeKernel.Canary.overloadedClaim.snapshot)
        { encode overloadArtifact with
          result := .compiled reversedOverloadWirePlans } = none ∧
      decode? (owned exactTypeSnapshot)
        { rawWire with result := .compiled [] } = none ∧
      decode? (owned exactTypeSnapshot)
        { rawWire with result := .compiled [exactWirePlan, exactWirePlan] } = none ∧
      decode? (owned exactTypeSnapshot)
        { rawWire with result := .compiled [forgedModeWirePlan] } = none ∧
      decode? (owned exactTypeSnapshot)
        { rawWire with result := .compiled [forgedExpectedWirePlan] } = none := by
  decide

theorem unsupported_is_not_compiled_empty :
    decode? (owned mixedSupportedAndOpenSnapshot)
        { encode outsideArtifact with result := .compiled [] } = none := by
  decide

theorem ill_formed_snapshot_rejected :
    decode? (owned illFormedSnapshot)
      (encode (GuardArtifact.compile (owned illFormedSnapshot) "n" 1)) = none := by
  decide

end Canary

#print axioms GuardArtifact.compile_validFor
#print axioms GuardArtifact.compiled_family_validFor
#print axioms lookupDeclaration?_exact
#print axioms decode_sound_validFor
#print axioms decode_encode_of_valid
#print axioms encode_decode_canonical
#print axioms decoded_owner_revision_head_arity_exact
#print axioms decoded_plan_occurrences_order_exact
#print axioms decoded_plan_modes_exact
#print axioms decoded_artifact_no_invention
#print axioms decoded_execution_exact
#print axioms Canary.current_empty_compiled_roundtrip
#print axioms Canary.overload_occurrence_order_roundtrip
#print axioms Canary.duplicate_source_retains_first_occurrence
#print axioms Canary.checked_modes_roundtrip
#print axioms Canary.outside_fragment_roundtrip
#print axioms Canary.wrong_root_version_and_trailing_rejected
#print axioms Canary.foreign_owner_and_stale_revision_rejected
#print axioms Canary.wrong_head_arity_and_unknown_occurrence_rejected
#print axioms Canary.reordered_omitted_duplicated_and_forged_rejected
#print axioms Canary.unsupported_is_not_compiled_empty
#print axioms Canary.ill_formed_snapshot_rejected

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardWire
