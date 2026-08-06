import Mettapedia.Languages.Metamath.SourceGSLTLexicalClosure
import Mettapedia.Languages.Metamath.SourceGSLTRuntimeCoEvolution
import Mettapedia.Languages.Metamath.SourceGSLTCheckerAlignment
import Mettapedia.Languages.Metamath.SourceGSLTLifecycleComposition
import Mettapedia.Languages.Metamath.SourceGSLTCompressedParserComposition

/-!
# Parallel acceptance certificates at the Metamath composition boundary

The composed source pipeline (`runSource`, parametric in the ratified
include policies) already certifies its own syntax: an accepted run
derives the outer database sort in the lexicalized language of its own
classified stream, with byte-charset provenance (item 1).  This module
adds the runtime leg: every accepted run's state evolution is realized
by the shipped mm-lean4 database operations, growing from the default
database in lock-step with the source fold from the initial state
(item 2's whole-fold declaration-state theorem, entered through the
statement dispatcher).

The independently checked parser/checker certificate supplies a second
family of results over a byte array.  These two families are useful in
parallel, but they do not form a joined equivalence until the checked classified
stream is identified with the stream produced by `runSource`, proof
discharges are constructed for every `$p`, and the production checker DB
is proved to agree with the final source state.  Multi-file inputs also
require a refinement of the shipped include-aware driver.  The declarations
below therefore distinguish the universally proved parallel certificate
from the remaining flattened and include-aware joints.

In particular, declaration-state co-evolution inserts a `$p` conclusion
through the same assertion-insertion operation used after a successful
proof.  It does not itself execute the proof.  Proof execution belongs to
`LifecycleRun` and ultimately to the prefix-wise mm-lean4/source
bisimulation required by the parent goal.
-/

namespace Mettapedia.Languages.Metamath.SourceGSLTParallelAcceptance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives
open Mettapedia.Languages.Metamath.SourceGSLT
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLTDerivationCorrespondence
open Mettapedia.Languages.Metamath.SourceGSLTLexicalClosure
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceGSLTRuntimeCoEvolution
open Mettapedia.Languages.Metamath.SourceGSLTRuntimeStateAgreement
open Mettapedia.Languages.Metamath.SourceGSLTCompressedParserMMLean4
open Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG
open Mettapedia.GSLT.LanguageDef.GrammarInferenceExtraction
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.SourceGSLTLifecycleComposition
open Mettapedia.Languages.Metamath.SourceGSLTCompressedParserComposition

/-! ## From statements to payloads

`applyStatement` already dispatches every raw statement through
`applyLocalPayload?`; a successful application is therefore realized by
one or two accepted payloads. -/

/-- One accepted statement is an accepted payload sequence. -/
theorem applyStatement_payloads {state next : SourceState}
    {stmt : RawStatement}
    {obligations : List TheoremObligation}
    (h : applyStatement state stmt = .ok (next, obligations)) :
    ∃ payloads : List LocalPayload,
      applyLocalPayloads? payloads state = some next := by
  cases stmt with
  | openScope site =>
      simp only [applyStatement] at h
      split at h
      · rename_i mid heq
        cases h
        exact ⟨[.openScope], by simp [applyLocalPayloads?, heq]⟩
      · exact nomatch h
  | closeScope site =>
      simp only [applyStatement] at h
      split at h
      · exact nomatch h
      · rename_i mid heq
        split at h
        · exact nomatch h
        · rename_i fin heq₂
          cases h
          exact ⟨[.closeScope, .completeBlock], by
            simp [applyLocalPayloads?, heq, heq₂]⟩
  | constDecl site names terminator =>
      simp only [applyStatement] at h
      split at h
      · rename_i mid heq
        cases h
        exact ⟨[.declareConstants (names.map (·.name))], by
          simp [applyLocalPayloads?, heq]⟩
      · exact nomatch h
  | varDecl site names terminator =>
      simp only [applyStatement] at h
      split at h
      · rename_i mid heq
        cases h
        exact ⟨[.declareVariables (names.map (·.name))], by
          simp [applyLocalPayloads?, heq]⟩
      · exact nomatch h
  | djDecl site names terminator =>
      simp only [applyStatement] at h
      split at h
      · rename_i mid heq
        cases h
        exact ⟨[.declareDisjoint (names.map (·.name))], by
          simp [applyLocalPayloads?, heq]⟩
      · exact nomatch h
  | floating site label typecode variableName terminator =>
      simp only [applyStatement] at h
      split at h
      · rename_i mid heq
        cases h
        exact ⟨[.declareFloating label.name typecode.name
          variableName.name], by
          simp [applyLocalPayloads?, heq]⟩
      · exact nomatch h
  | essential site label typecode body terminator =>
      simp only [applyStatement] at h
      split at h
      · exact nomatch h
      · rename_i syms htag
        split at h
        · rename_i mid heq
          cases h
          exact ⟨[.declareEssential label.name
            ⟨typecode.name, syms⟩], by
            simp [applyLocalPayloads?, heq]⟩
        · exact nomatch h
  | axiomatic site label typecode body terminator =>
      simp only [applyStatement] at h
      split at h
      · exact nomatch h
      · rename_i syms htag
        split at h
        · rename_i mid heq
          cases h
          exact ⟨[.declareAxiom label.name
            ⟨typecode.name, syms⟩], by
            simp [applyLocalPayloads?, heq]⟩
        · exact nomatch h
  | provable site label typecode body proof separator terminator =>
      simp only [applyStatement] at h
      split at h
      · exact nomatch h
      · rename_i syms htag
        split at h
        · exact nomatch h
        · rename_i mid heq
          cases h
          refine ⟨[.declareAxiom label.name
            ⟨typecode.name, syms⟩], ?_⟩
          rw [show applyLocalPayloads?
              [.declareAxiom label.name ⟨typecode.name, syms⟩]
              state =
            (do
              let m ← applyLocalPayload?
                (.declareAxiom label.name ⟨typecode.name, syms⟩)
                state
              applyLocalPayloads? [] m) from rfl]
          rw [show applyLocalPayload?
              (.declareAxiom label.name ⟨typecode.name, syms⟩)
              state =
            declareAxiom? state label.name ⟨typecode.name, syms⟩
            from rfl]
          rw [show declareAxiom? state label.name
              ⟨typecode.name, syms⟩ =
            insertAssertion? state label.name ⟨typecode.name, syms⟩
            from rfl, heq]
          rfl

/-- An accepted statement fold is an accepted payload sequence. -/
theorem foldStatements_payloads :
    ∀ {statements : List RawStatement} {state final : SourceState}
      {obligations : List TheoremObligation},
      foldStatements state statements = .ok (final, obligations) →
      ∃ payloads : List LocalPayload,
        applyLocalPayloads? payloads state = some final
  | [], state, final, obligations, h => by
      unfold foldStatements at h
      cases h
      exact ⟨[], rfl⟩
  | stmt :: rest, state, final, obligations, h => by
      unfold foldStatements at h
      split at h
      · exact nomatch h
      · rename_i next obls₀ happ
        split at h
        · exact nomatch h
        · rename_i fin obls₁ hrest
          cases h
          obtain ⟨ps₀, hps₀⟩ := applyStatement_payloads happ
          obtain ⟨ps, hps⟩ := foldStatements_payloads hrest
          exact ⟨ps₀ ++ ps, applyLocalPayloads?_append hps₀ hps⟩

/-! ## The runtime leg of an accepted composed run

Every accepted `runSource` (either ratified include policy) has a
declaration-state realization using shipped mm-lean4 database operations
growing from the default database: the composed pipeline's state fold is
an accepted payload sequence, and the payload co-evolution theorem applies.
This is not yet the actual parser/checker trace. -/

open Mettapedia.Languages.Metamath.VerifiedCheckerSemantics
open Mettapedia.Languages.Metamath.SourceGSLTCheckerAlignment

/-- **Declaration-state co-evolution for the composed pipeline.**

This theorem does not execute `$p` proofs: `applyStatement_payloads`
projects an accepted `$p` statement to the assertion insertion that follows
successful checking, while the proof remains a `TheoremObligation`. -/
theorem runSource_declarationState_coevolution {files : FileMap}
    {policy : IncludePolicy} {root : String} {fuel : Nat}
    {state : SourceState} {obligations : List TheoremObligation}
    (h : runSource files policy root fuel = .ok state obligations)
    (pos : Metamath.Verify.Pos) :
    ∃ payloads : List LocalPayload,
      applyLocalPayloads? payloads initialState = some state ∧
      RuntimeDBAgrees
        (payloads.foldl
          (fun d payload => runtimeApplyPayload pos payload d)
          (default : RuntimeDB))
        state := by
  obtain ⟨spans, tokens, statements, hexp, hres, hseg, hfold,
    hcomplete⟩ := runSource_ok_inv h
  obtain ⟨payloads, hps⟩ := foldStatements_payloads hfold
  exact ⟨payloads, hps, default_initial_applyPayloads pos hps⟩

/-! ## The parallel certificate and the flattened-source joint

For each ratified include policy, the theorem below records two proved
worlds without claiming that their inputs have already been joined:

* the authored composed GSLT accepts the source, with exact include
  provenance and a proof-occurrence derivation of the outer database
  sort in the lexicalized language of its own classified stream;
* mm-lean4's declaration operations grow a database in proven agreement
  with the accepted source state from the ground states;
* the independently checked byte presentation has its own exact syntax
  derivation and typed token lowering to the verified reader;
* the verified reader accepts its byte presentation, and for
  every theorem, implementation acceptance is equivalent to
  `Metamath.Spec` provability.

The checked byte presentation is deliberately not called "the same
source" here: that requires the explicit classified-stream binding and
runtime/lifecycle fields in `FlattenedFinalStateEvidence` below. -/

/-- Facts proved in parallel from one accepted source run and one checked
byte presentation.  This proposition intentionally does not mention a
`CheckedParserOutput`: the theorem constructing it uses such an output,
but the proposition itself makes no false same-source claim. -/
def ParallelAcceptanceCertificate (bytes : ByteArray) (files : FileMap)
    (policy : IncludePolicy) (root : String) (fuel : Nat)
    (state : SourceState) (obligations : List TheoremObligation)
    (pos : Metamath.Verify.Pos) : Prop :=
  (∃ (spans : List
      Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan)
    (tokens : List LocatedToken) (statements : List RawStatement),
    expandDatabase files policy root fuel = .ok spans ∧
    resolveTokens files spans = some tokens ∧
    segmentStatements tokens = .ok statements ∧
    foldStatements initialState statements = .ok (state, obligations) ∧
    (∃ tree,
      Derives
        (lexicalizedLanguage sourceGrammar lexicalDeclarations
          (pipelineSource statements)) outerDatabaseSort
        (statements.flatMap RawStatement.tokenStrings) tree) ∧
    (∀ ob ∈ obligations,
      ∀ (openParen closeParen :
          Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan)
        (header : List LocatedName) (words : List LocatedToken),
        ob.proof = .compressed openParen header closeParen words →
        Nonempty (CompressedProofLocatedTokens
          (header.map (·.name)) (words.map (·.bytes))))) ∧
  (∃ payloads : List LocalPayload,
    applyLocalPayloads? payloads initialState = some state ∧
    RuntimeDBAgrees
      (payloads.foldl
        (fun d payload => runtimeApplyPayload pos payload d)
        (default : RuntimeDB))
      state) ∧
  (∃ (source : ClassifiedSource) (tree : Pattern),
    source.isValid = true ∧
      lexicallyValidSource source = true ∧
      TypedLoweringCertificate bytes source ∧
      Derives
        (lexicalizedLanguage sourceGrammar lexicalDeclarations source)
        outerDatabaseSort source.ledger.tokens tree) ∧
  ((Metamath.Verify.checkBytes bytes).error? = none ∧
    ∀ (label : String) (formula : Metamath.Verify.Formula),
      ImplementationAccepts bytes label formula ↔
        DeclarativeAccepts bytes formula)

/-- Policy-parametric construction of the parallel certificate.  The
source run and checked byte presentation may still be different inputs;
`FlattenedFinalStateEvidence` states the missing binding explicitly. -/
theorem parallelAcceptanceCertificate {bytes : ByteArray} {files : FileMap}
    {policy : IncludePolicy} {root : String} {fuel : Nat}
    {state : SourceState} {obligations : List TheoremObligation}
    (accepted : runSource files policy root fuel =
      .ok state obligations)
    (output : CheckedParserOutput bytes)
    (pos : Metamath.Verify.Pos) :
    ParallelAcceptanceCertificate bytes files policy root fuel state
      obligations pos := by
  obtain ⟨spans, tokens, statements, hexp, hres, hseg, hfold,
    hcomplete⟩ := runSource_ok_inv accepted
  refine ⟨⟨spans, tokens, statements, hexp, hres, hseg, hfold,
    ?_, ?_⟩,
    runSource_declarationState_coevolution accepted pos, ?_, ?_, ?_⟩
  · exact statements_derive_outerDatabase
      (fun r hr => baseRule_mem_lexicalized sourceGrammar
        lexicalDeclarations (pipelineSource statements) hr)
      hfold rfl (sourceStateComplete_scopes_length hcomplete)
      (segmentStatements_normalSteps hseg)
      (segmentStatements_compressedWords hseg)
      (pipelineSource_statementLeaves statements)
  · intro ob hob openParen closeParen header words hproof
    exact runSource_compressedProofLocatedTokens accepted hob hproof
  · obtain ⟨proof, derivation, tree, hexpand, herase, htree⟩ :=
      output.syntaxExact
    exact ⟨output.source, tree, output.sourceValid, output.lexicalValid,
      output.typedLoweringExact, htree⟩
  · exact output.readerAccepted
  · intro label formula
    exact output.implementationAcceptance_iff_specProvability
      label formula

/-- The parallel certificate at the book include policy. -/
theorem parallelAcceptanceCertificate_bookSpec
    {bytes : ByteArray} {files : FileMap}
    {root : String} {fuel : Nat} {state : SourceState}
    {obligations : List TheoremObligation}
    (accepted : runSource files bookSpecPolicy root fuel =
      .ok state obligations)
    (output : CheckedParserOutput bytes)
    (pos : Metamath.Verify.Pos) :
    ParallelAcceptanceCertificate bytes files bookSpecPolicy root fuel state
      obligations pos :=
  parallelAcceptanceCertificate accepted output pos

/-- The parallel certificate at the mm-lean4-compatible include policy. -/
theorem parallelAcceptanceCertificate_mmLean4Compat
    {bytes : ByteArray}
    {files : FileMap} {root : String} {fuel : Nat}
    {state : SourceState} {obligations : List TheoremObligation}
    (accepted : runSource files mmLean4CompatPolicy root fuel =
      .ok state obligations)
    (output : CheckedParserOutput bytes)
    (pos : Metamath.Verify.Pos) :
    ParallelAcceptanceCertificate bytes files mmLean4CompatPolicy root fuel
      state obligations pos :=
  parallelAcceptanceCertificate accepted output pos

/-! ### Exact requirements for the still-open flattened composition

The following structures are not accompanied by a universal constructor
theorem in this module.  They expose, without placeholders, the two
load-bearing joints that the parallel certificate does not prove.  They
describe a single checked byte buffer whose classified tokens equal the
source-DAG expansion.  Consequently they are adequate for monolithic input
or an independently justified flattening, but not yet for the shipped
include-aware file driver. -/

/-- An independently checked parser output and an accepted `runSource`
execution describe token-equivalent resolved streams.  Equality is on the
full classified tokens, not merely their serialized spellings.  The
`runSource` side retains file/span provenance, but `CheckedParserOutput`
observes one byte buffer and therefore cannot by itself certify that
multi-file provenance. -/
structure FlattenedRunBinding {bytes : ByteArray} (files : FileMap)
    (policy : IncludePolicy) (root : String) (fuel : Nat)
    (state : SourceState) (obligations : List TheoremObligation)
    (output : CheckedParserOutput bytes) : Type where
  spans : List
    Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan
  tokens : List LocatedToken
  statements : List RawStatement
  expanded : expandDatabase files policy root fuel = .ok spans
  resolved : resolveTokens files spans = some tokens
  segmented : segmentStatements tokens = .ok statements
  folded : foldStatements initialState statements =
    .ok (state, obligations)
  complete : sourceStateComplete state = true
  classifiedStream : output.source.tokens =
    (pipelineSource statements).tokens

/-- A resolved-run binding reconstructs the accepted source execution it
records. -/
theorem FlattenedRunBinding.accepted
    {bytes : ByteArray} {files : FileMap} {policy : IncludePolicy}
    {root : String} {fuel : Nat} {state : SourceState}
    {obligations : List TheoremObligation}
    {output : CheckedParserOutput bytes}
    (binding : FlattenedRunBinding files policy root fuel state obligations
      output) :
    runSource files policy root fuel = .ok state obligations := by
  simp only [runSource, binding.expanded, binding.resolved,
    binding.segmented, binding.folded, binding.complete, if_true]

/-- Minimum token-equivalent final-state evidence still required above the
parallel certificate: every proof obligation has a source-native lifecycle
witness, and the actual production checker database for the flattened byte
presentation agrees with the final source state.  A complete implementation
refinement additionally proves this agreement prefix-by-prefix; final-state
agreement must not be mistaken for that stronger bisimulation. -/
structure FlattenedFinalStateEvidence {bytes : ByteArray} (files : FileMap)
    (policy : IncludePolicy) (root : String) (fuel : Nat)
    (state : SourceState) (obligations : List TheoremObligation)
    (output : CheckedParserOutput bytes) : Type where
  binding : FlattenedRunBinding files policy root fuel state obligations
    output
  lifecycle : Nonempty
    (LifecycleRun initialState binding.statements state)
  checkerState : RuntimeDBAgrees (Metamath.Verify.checkBytes bytes) state

/-- Flattened final-state evidence entails the proved parallel certificate,
while retaining the stronger token-equivalence and proof-discharge fields. -/
theorem FlattenedFinalStateEvidence.parallelCertificate
    {bytes : ByteArray} {files : FileMap} {policy : IncludePolicy}
    {root : String} {fuel : Nat} {state : SourceState}
    {obligations : List TheoremObligation}
    {output : CheckedParserOutput bytes}
    (evidence : FlattenedFinalStateEvidence files policy root fuel state
      obligations output)
    (pos : Metamath.Verify.Pos) :
    ParallelAcceptanceCertificate bytes files policy root fuel state obligations
      pos :=
  parallelAcceptanceCertificate evidence.binding.accepted output pos

/-! ### Include-aware boundary

The universal two-policy composition theorem is stronger than
`FlattenedFinalStateEvidence`.  It must relate `FileMap`, located expansion,
and each include-policy decision to mm-lean4's shipped
`processFileSinglePassWithIO` / `checkSinglePass` driver, including file
identity, path normalization, cycle/seen state, and exact rejection sites.
No theorem in this module claims that still-open driver refinement. -/

/-! ## Kernel fixtures for the new joints -/

set_option maxRecDepth 100000

/-- One complete declaration-only database:
`$c wff |- $. $v x $. vx $f wff x $. ax $a |- x $.` -/
def declarationFixtureFiles : FileMap := fun n =>
  if n = "root" then
    some (ByteArray.mk #[36, 99, 32, 119, 102, 102, 32, 124, 45, 32,
      36, 46, 32, 36, 118, 32, 120, 32, 36, 46, 32, 118, 120, 32, 36,
      102, 32, 119, 102, 102, 32, 120, 32, 36, 46, 32, 97, 120, 32,
      36, 97, 32, 124, 45, 32, 120, 32, 36, 46])
  else none

/-- Positive: the composed pipeline accepts the fixture database at
the book include policy. -/
example : (match runSource declarationFixtureFiles bookSpecPolicy "root" 100 with
    | .ok _ _ => true
    | .error _ => false) = true := by rfl

/-- Positive: the same acceptance at the mm-lean4-compatible policy. -/
example : (match runSource declarationFixtureFiles mmLean4CompatPolicy "root" 100
    with
    | .ok _ _ => true
    | .error _ => false) = true := by rfl

/-- Positive declaration-state fixture: the accepted source run is
realized by the shipped declaration operations. -/
example (pos : Metamath.Verify.Pos) :
    ∃ state obligations,
      runSource declarationFixtureFiles bookSpecPolicy "root" 100 =
        .ok state obligations ∧
      ∃ payloads : List LocalPayload,
        applyLocalPayloads? payloads initialState = some state ∧
        RuntimeDBAgrees
          (payloads.foldl
            (fun d payload => runtimeApplyPayload pos payload d)
            (default : RuntimeDB))
          state := by
  match h : runSource declarationFixtureFiles bookSpecPolicy "root" 100 with
  | .ok state obligations =>
      exact ⟨state, obligations, rfl,
        runSource_declarationState_coevolution h pos⟩
  | .error e =>
      exact absurd h (by
        intro hcontra
        have : (match runSource declarationFixtureFiles bookSpecPolicy "root" 100
            with
            | .ok _ _ => true
            | .error _ => false) = false := by
          rw [hcontra]
        rw [show (match runSource declarationFixtureFiles bookSpecPolicy "root" 100
            with
            | .ok _ _ => true
            | .error _ => false) = true from rfl] at this
        exact nomatch this)

/-- Positive fixture for the parallel certificate, indexed by an
independently checked parser certificate.  This deliberately makes no
same-source claim. -/
example {bytes : ByteArray} (output : CheckedParserOutput bytes)
    (pos : Metamath.Verify.Pos) :
    ∃ state obligations,
      runSource declarationFixtureFiles mmLean4CompatPolicy "root" 100 =
        .ok state obligations ∧
      ParallelAcceptanceCertificate bytes declarationFixtureFiles
        mmLean4CompatPolicy "root" 100 state obligations pos := by
  match h : runSource declarationFixtureFiles mmLean4CompatPolicy "root" 100 with
  | .ok state obligations =>
      exact ⟨state, obligations, rfl,
        parallelAcceptanceCertificate_mmLean4Compat h output pos⟩
  | .error e =>
      exact absurd h (by
        intro hcontra
        have : (match runSource declarationFixtureFiles mmLean4CompatPolicy
            "root" 100 with
            | .ok _ _ => true
            | .error _ => false) = false := by
          rw [hcontra]
        rw [show (match runSource declarationFixtureFiles mmLean4CompatPolicy
            "root" 100 with
            | .ok _ _ => true
            | .error _ => false) = true from rfl] at this
        exact nomatch this)

/-- Negative: a missing include target is rejected with include
provenance retained. -/
example : (match runSource (fun _ => none) bookSpecPolicy "root" 100
    with
    | .ok _ _ => false
    | .error (.include _) => true
    | .error _ => false) = true := by rfl

/-- Negative: a database whose axiom variable has no floating
hypothesis is rejected at the fold with statement provenance.
(`$c wff $. $v x $. ax $a wff x $.`) -/
def missingFloatFiles : FileMap := fun n =>
  if n = "root" then
    some (ByteArray.mk #[36, 99, 32, 119, 102, 102, 32, 36, 46, 32,
      36, 118, 32, 120, 32, 36, 46, 32, 97, 120, 32, 36, 97, 32, 119,
      102, 102, 32, 120, 32, 36, 46])
  else none

example : (match runSource missingFloatFiles bookSpecPolicy "root" 100
    with
    | .ok _ _ => false
    | .error (.fold _) => true
    | .error _ => false) = true := by rfl

/-- A structurally valid `$p` whose proof names an unknown label.  The
source fold must accept it and retain one obligation: proof validation is
the separate lifecycle/checker joint, not part of declaration-state
co-evolution. -/
def uncheckedProofFiles : FileMap := fun n =>
  if n = "root" then
    some (ByteArray.mk #[36, 99, 32, 119, 102, 102, 32, 124, 45, 32,
      36, 46, 32, 36, 118, 32, 120, 32, 36, 46, 32, 118, 120, 32, 36,
      102, 32, 119, 102, 102, 32, 120, 32, 36, 46, 32, 97, 120, 32,
      36, 97, 32, 124, 45, 32, 120, 32, 36, 46, 32, 116, 104, 32, 36,
      112, 32, 124, 45, 32, 120, 32, 36, 61, 32, 110, 111, 112, 101,
      32, 36, 46])
  else none

example : (match runSource uncheckedProofFiles mmLean4CompatPolicy
    "root" 100 with
    | .ok _ obligations => obligations.length == 1
    | .error _ => false) = true := by rfl

end Mettapedia.Languages.Metamath.SourceGSLTParallelAcceptance
