import Mettapedia.TypeTheory.Calculi.StagedScopedReflective.Presentation
import Mettapedia.Languages.MeTTa.RuntimeSpec
import Mettapedia.GSLT.LanguageDef.NIKMetalogic
import Mettapedia.GSLT.LanguageDef.LF.PureCorrespondence
import Mettapedia.GSLT.Dynamics.WeightCost
import Mettapedia.PLN.Evidence.BinEvNat
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystem
import Mettapedia.GSLT.Dynamics.RevisionedOccurrenceProofFlow
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing
import Mettapedia.TypeTheory.ModalCwF

/-!
# A staged-reflective type-theory candidate for the MeTTa family

## Purpose

This module develops one staged-reflective type-theory candidate, informed by
working MeTTa-family observation profiles and explicit target commitments.
The profiles extend the structured property collections of
`RuntimeSpec`/`DialectProfile`; they do not determine this architecture.

The construction separates its inputs, selected policies, and proved laws:

1. working profiles list selected observations about operational behaviour
   and intended candidate capabilities (§1);
2. two authored policies classify observations and commitments by requirement
   labels (§2); their finite-table proofs do not establish that any
   observation semantically necessitates its assigned requirement;
3. the candidate interface assumes a contextual multimodal CwF with a universe
   à la Tarski, parameterized by a mode theory (§3–§4), rather than deriving
   that interface as the unique suitable architecture;
4. explicit witness structures specify laws and noncollapse conditions for
   the selected capabilities (§5–§8);
5. the assembly interface couples these witnesses and exact checker parity
   for its stated direct-typing fragment (§9–§10).  Selected-language
   instances and their concrete assembly are supplied downstream.

The intended semantic reading is **types as spaces**: a closed type denotes a
space of patterns, membership is matching, subtyping is inclusion (§6).  The
universe is a space of type codes with `el` as decoding — the same
codes-plus-decoding pattern already used by the reflection layer.

## Honesty contract

The classification theorems establish table injectivity, exact list contents,
and disjoint policy images.  They contain no satisfaction relation connecting
dialect semantics to requirement labels, and are not necessity implications.
The later semantic, syntactic, and parity theorems establish their own stated
properties independently of those tables.

This candidate uses an intensional kernel equality; stronger observational or
cubical relations remain explicitly named profiles.  That is a scoped
architecture choice, not a determination of the MeTTa family's type theory or
of Prime.  Same-stage quotation carries a nonzero quotation-depth witness and
has distinct positive and negative models.

`openObligations` (§11) records five named theorem boundaries of this
development.  Its pinned count audits that list, not overall completion or
exhaustiveness of the design obligations.  The witness assembly does not
claim a completed language specification or a full executable modal checker.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
namespace Mettapedia.Languages.MeTTa.Experimental.StagedReflective

universe uNativeClaim uNativeCertificate uNativeProof uRaw uRawTarget

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.GSLT.LanguageDef.KernelAuthority (Checker)
open Mettapedia.TypeTheory

/-! ## §1 Observations: the dialect property bags

Each constructor labels an operational property to investigate.  The bags
below are working observation profiles, not proofs that a dialect satisfies
those properties.  Changing a bag changes its assigned requirement list
mechanically.  These profiles are neither complete dialect specifications nor
a determination of a candidate's eventual type theory. -/

/-- Operational-property labels used by the candidate's requirement policy. -/
inductive Observation where
  /-- Evaluation yields collections of results (superposition). -/
  | collectionResults
  /-- The core operation is pattern matching with metavariables. -/
  | metavariablePatterns
  /-- Programs are data: quotation and evaluation are internal. -/
  | nativeReflection
  /-- Atomspaces are first-class values. -/
  | spacesFirstClass
  /-- Unknown symbols remain uninterpreted; they never signal errors. -/
  | unknownsInert
  /-- Reduction carries cost/resource accounting. -/
  | costAccounted
  /-- Claims may carry graded evidence (world-model layer). -/
  | evidenceAnnotated
  /-- Interpreter levels are distinguished (staged tower). -/
  | stagedTower
  deriving DecidableEq, Repr

/-- A dialect's observation bag.  `observed` is deliberately a bare list:
multiplicity is irrelevant, order is not load-bearing, and membership is the
only operation used downstream. -/
structure ObservationBag where
  dialectName : String
  observed : List Observation
  deriving Repr

/-- Working observation profile for the staged-reflective candidate.  Its
eight labels are inputs to a selected policy, not semantic evidence that this
candidate is fixed, realized, or exhaustively specified here. -/
def candidateBag : ObservationBag where
  dialectName := "staged-reflective-candidate"
  observed :=
    [.collectionResults, .metavariablePatterns, .nativeReflection,
     .spacesFirstClass, .unknownsInert, .costAccounted,
     .evidenceAnnotated, .stagedTower]

/-- Working HE observation profile used by this native-typing candidate. -/
def heBag : ObservationBag where
  dialectName := "he"
  observed :=
    [.collectionResults, .metavariablePatterns, .nativeReflection,
     .spacesFirstClass, .unknownsInert]

/-- Working PeTTa observation profile used by this typing candidate.  Equality
with the HE list records only this selected fragment; it does not identify the
two dialects or their complete observable interfaces. -/
def pettaBag : ObservationBag where
  dialectName := "petta"
  observed :=
    [.collectionResults, .metavariablePatterns, .nativeReflection,
     .spacesFirstClass, .unknownsInert]

/-- Zero: the minimal work-closure fragment — collections, metavariables,
inert unknowns. -/
def zeroBag : ObservationBag where
  dialectName := "zero"
  observed := [.collectionResults, .metavariablePatterns, .unknownsInert]

/-- Working family profiles under comparison.  Membership here does not make
one profile a specification or one candidate theory authoritative. -/
def familyBags : List ObservationBag := [candidateBag, heBag, pettaBag, zeroBag]

/-! ## §2 Requirements and the selected classification policies -/

/-- Requirement labels for the selected candidate interface.  The witness
structures of §5–§8 give these labels their intended capability contracts;
this enumeration alone defines no semantic satisfaction relation. -/
inductive Requirement where
  /-- Semantic types classify collections (types-as-spaces). -/
  | typesAsCollections
  /-- Open terms are typed relative to contexts; metavariables first-class. -/
  | contextualJudgment
  /-- An internal code/quotation modality. -/
  | quotationModality
  /-- Types for spaces as values (the universe supports space codes). -/
  | spaceTypes
  /-- A interface mode that never rejects unknown-only programs. -/
  | successInterface
  /-- Cost grading in the mode theory. -/
  | gradedModality
  /-- Evidence decorations fibred over the kernel, never inside it. -/
  | evidenceFibration
  /-- Staging levels in the mode theory. -/
  | levelModalities
  /-- Genuinely dependent type families (full DTT/MTT-tier reasoning). -/
  | dependentFamilies
  /-- Propositional identity with a reflexivity witness. -/
  | identityTypes
  /-- Language presentations as first-class typed values. -/
  | languageCodes
  /-- Native proof objects remain first-class and proof relevant. -/
  | nativeProofObjects
  /-- Universes and meta-authorities are strictly level stratified. -/
  | stratifiedMetalogic
  /-- Production typing computes directly on Pattern claims and carries no
  certificate language through the interior fast path. -/
  | directTypingPath
  deriving DecidableEq, Repr

/-- Authored observation-to-requirement policy.  Its one-label-per-observation
classification is a design input, not a semantic necessity theorem. -/
def observationRequirementPolicy : Observation → Requirement
  | .collectionResults => .typesAsCollections
  | .metavariablePatterns => .contextualJudgment
  | .nativeReflection => .quotationModality
  | .spacesFirstClass => .spaceTypes
  | .unknownsInert => .successInterface
  | .costAccounted => .gradedModality
  | .evidenceAnnotated => .evidenceFibration
  | .stagedTower => .levelModalities

/-- The selected table assigns distinct labels to distinct observations.
Injectivity is a property of this table, not evidence that the assigned
capabilities are necessary or sufficient for the observed behaviour. -/
theorem observationRequirementPolicy_injective :
    Function.Injective observationRequirementPolicy := by
  intro a b h
  cases a <;> cases b <;> simp_all [observationRequirementPolicy]

/-- The requirements assigned by the selected observation policy. -/
def ObservationBag.assignedRequirements (bag : ObservationBag) : List Requirement :=
  bag.observed.map observationRequirementPolicy

/-- Exact table expansion for the staged-reflective candidate's working
profile, in order.  This is neither a completeness result for dialect
observations nor a semantic derivation of requirements. -/
theorem candidate_assignedRequirements_eq :
    candidateBag.assignedRequirements =
      [.typesAsCollections, .contextualJudgment, .quotationModality,
       .spaceTypes, .successInterface, .gradedModality,
       .evidenceFibration, .levelModalities] := rfl

/-- Under this policy, every label assigned to the working Zero profile also
occurs in the staged-reflective candidate's list.  List inclusion alone does
not prove that a common spine models either dialect. -/
theorem zero_assignedRequirements_subset_candidate :
    ∀ r ∈ zeroBag.assignedRequirements,
      r ∈ candidateBag.assignedRequirements := by decide

/-! ### Target commitments: the normative channel

Observation profiles record selected operational-property labels.
Commitments declare capabilities sought in this candidate.  Both channels use
authored classification policies; neither table establishes semantic
necessity.  `commitmentRequirementPolicy_disjoint_candidate` checks only that
the commitment table's image is disjoint from the candidate's assigned
observation labels.  This bookkeeping separation does not prove that any
actual dialect lacks the committed capabilities or gains them from a label. -/

/-- Capabilities explicitly requested of this candidate. -/
inductive TargetCommitment where
  /-- Full dependent-family reasoning (DTT/MTT tier). -/
  | dttReasoning
  /-- Propositional identity and its elimination. -/
  | identityReasoning
  /-- Native, typed manipulation of language presentations
  (the intermediate-language capacity). -/
  | languageManipulation
  /-- Proof objects are native data closed under admitted operations. -/
  | proofObjectProgramming
  /-- A non-self-certifying tower of universes and meta-authorities. -/
  | stratifiedBootstrap
  /-- The native typing authority is a direct decision kernel over MeTTa
  Patterns; proof-carrying replay remains an optional boundary mode. -/
  | directTypingPath
  deriving DecidableEq, Repr

/-- Authored classification of target commitments by requirement label. -/
def commitmentRequirementPolicy : TargetCommitment → Requirement
  | .dttReasoning => .dependentFamilies
  | .identityReasoning => .identityTypes
  | .languageManipulation => .languageCodes
  | .proofObjectProgramming => .nativeProofObjects
  | .stratifiedBootstrap => .stratifiedMetalogic
  | .directTypingPath => .directTypingPath

/-- Distinct commitments receive distinct labels in this selected table. -/
theorem commitmentRequirementPolicy_injective :
    Function.Injective commitmentRequirementPolicy := by
  intro a b h
  cases a <;> cases b <;> simp_all [commitmentRequirementPolicy]

/-- The explicit target commitments of the staged-reflective candidate. -/
def candidateCommitments : List TargetCommitment :=
  [.dttReasoning, .identityReasoning, .languageManipulation,
   .proofObjectProgramming, .stratifiedBootstrap, .directTypingPath]

/-- No commitment-table label occurs in the candidate's assigned observation
list.  This proves disjointness of selected classifications, not independence
or absence of semantic capabilities in any dialect. -/
theorem commitmentRequirementPolicy_disjoint_candidate :
    ∀ c : TargetCommitment,
      commitmentRequirementPolicy c ∉ candidateBag.assignedRequirements := by
  intro c
  cases c <;> decide

/-! ### Live HE and PeTTa success interfaces

These instances expose the pass-through fragments of the two executable
language specifications.  They are intentionally smaller than complete
typing algorithms: the policy assigns `successInterface` to `unknownsInert`,
and these witnesses prove a valid operational continuation for their stated
unknown-only fragments.  Soundness lands in each dialect's own evaluation
relation, while a concrete non-pass-through claim is rejected.  This does not
derive the interface contract from the observation label alone. -/

/-- The HE pass-through checker only needs the subject and expected type;
space, grounded dispatch, and bindings are universally quantified in its
native judgment. -/
structure HESuccessClaim where
  atom : Mettapedia.Languages.MeTTa.OSLFCore.Atom
  expected : Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-- The exact guard of HE's `EvalAtom.type_pass` constructor. -/
def hePasses (claim : HESuccessClaim) : Prop :=
  Mettapedia.Languages.MeTTa.HE.isEmptyOrError claim.atom = false ∧
    (claim.expected = Mettapedia.Languages.MeTTa.OSLFCore.Atom.atomType ∨
      claim.expected = Mettapedia.Languages.MeTTa.HE.getMetaType claim.atom ∨
      Mettapedia.Languages.MeTTa.HE.getMetaType claim.atom =
        Mettapedia.Languages.MeTTa.OSLFCore.Atom.variableType)

/-- Boolean presentation of the HE pass-through guard. -/
def hePassesBool (claim : HESuccessClaim) : Bool :=
  (Mettapedia.Languages.MeTTa.HE.isEmptyOrError claim.atom == false) &&
    ((claim.expected == Mettapedia.Languages.MeTTa.OSLFCore.Atom.atomType) ||
      (claim.expected == Mettapedia.Languages.MeTTa.HE.getMetaType claim.atom) ||
      (Mettapedia.Languages.MeTTa.HE.getMetaType claim.atom ==
        Mettapedia.Languages.MeTTa.OSLFCore.Atom.variableType))

theorem hePassesBool_eq_true (claim : HESuccessClaim) :
    hePassesBool claim = true ↔ hePasses claim := by
  simp [hePassesBool, hePasses, Bool.or_eq_true]
  tauto

/-- HE's direct executable success-fragment decision. -/
def heSuccessDecide : HESuccessClaim → Bool :=
  hePassesBool

/-- The native HE judgment selected by the success interface. -/
def HEPassesJudgment (claim : HESuccessClaim) : Prop :=
  ∀ (space : Mettapedia.Languages.MeTTa.HE.Space)
    (dispatch : Mettapedia.Languages.MeTTa.HE.GroundedDispatch)
    (bindings : Mettapedia.Languages.MeTTa.HE.Bindings),
    Mettapedia.Languages.MeTTa.HE.EvalAtom space dispatch
      claim.atom claim.expected bindings (claim.atom, bindings)

/-- Executable acceptance enters HE's authored evaluation relation. -/
theorem heSuccessDecide_sound (claim : HESuccessClaim)
    (accepted : heSuccessDecide claim = true) :
    HEPassesJudgment claim := by
  have passes : hePasses claim :=
    (hePassesBool_eq_true claim).mp accepted
  intro space dispatch bindings
  exact Mettapedia.Languages.MeTTa.HE.EvalAtom.type_pass
    claim.atom claim.expected bindings passes.1 passes.2

/-- Unknown HE symbols are the unknown-only fragment. -/
def HEUnknownOnly (claim : HESuccessClaim) : Prop :=
  ∃ name : String,
    claim.atom = .symbol name ∧
      name ≠ "Empty" ∧
      claim.expected = Mettapedia.Languages.MeTTa.OSLFCore.Atom.atomType

/-- A deliberately unsupported HE expected type. -/
def heRejectedClaim : HESuccessClaim where
  atom := .symbol "native-success-subject"
  expected := .symbol "NativeSuccessUnsupportedType"

/-- HE's unknown-preserving pass-through fragment is a nondegenerate success
interface over the live `EvalAtom` relation. -/
def heSuccessInterface : SuccessInterface HESuccessClaim where
  decide := heSuccessDecide
  Judges := HEPassesJudgment
  sound := heSuccessDecide_sound
  UnknownOnly := HEUnknownOnly
  witness := by
    refine ⟨⟨.symbol "native-unknown",
      Mettapedia.Languages.MeTTa.OSLFCore.Atom.atomType⟩, ?_⟩
    exact ⟨"native-unknown", rfl, by decide, rfl⟩
  never_rejects := by
    intro claim unknown
    rcases claim with ⟨atom, expected⟩
    rcases unknown with ⟨name, atomEq, notEmpty, expectedEq⟩
    dsimp at atomEq expectedEq
    subst atom
    subst expected
    apply (hePassesBool_eq_true _).mpr
    constructor
    · simp [Mettapedia.Languages.MeTTa.HE.isEmptyOrError,
        Mettapedia.Languages.MeTTa.HE.isEmptyAtom,
        Mettapedia.Languages.MeTTa.HE.isErrorAtom,
        Mettapedia.Languages.MeTTa.OSLFCore.Atom.empty, notEmpty]
    · exact Or.inl rfl
  rejects := by
    exact ⟨heRejectedClaim, rfl⟩

/-- The PeTTa pass-through interface names a nullary symbol and its expected
type. -/
structure PeTTaSuccessClaim where
  symbol : String
  expected : Pattern

/-- PeTTa's direct executable pass-through-type decision. -/
def pettaSuccessDecide (claim : PeTTaSuccessClaim) : Bool :=
    (claim.expected == Mettapedia.Languages.MeTTa.PeTTa.atomType) ||
    (claim.expected == Mettapedia.Languages.MeTTa.PeTTa.expressionType) ||
    (claim.expected == Mettapedia.Languages.MeTTa.PeTTa.undefinedType) ||
    (claim.expected == Mettapedia.Languages.MeTTa.PeTTa.groundedType)

theorem pettaSuccessDecide_eq_true (claim : PeTTaSuccessClaim) :
    pettaSuccessDecide claim = true ↔
      Mettapedia.Languages.MeTTa.PeTTa.isPassThroughType claim.expected := by
  simp [pettaSuccessDecide,
    Mettapedia.Languages.MeTTa.PeTTa.isPassThroughType, Bool.or_eq_true]
  tauto

/-- The native PeTTa evaluation judgment selected by the success interface. -/
def PeTTaPassesJudgment (claim : PeTTaSuccessClaim) : Prop :=
  ∀ (space : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace)
    (bindings : Mettapedia.OSLF.MeTTaIL.Match.Bindings),
    Mettapedia.Languages.MeTTa.PeTTa.MeTTaEval space
      (.apply claim.symbol []) claim.expected bindings
      [(.apply claim.symbol [], bindings)]

/-- Executable acceptance enters PeTTa's authored evaluation relation. -/
theorem pettaSuccessDecide_sound (claim : PeTTaSuccessClaim)
    (accepted : pettaSuccessDecide claim = true) :
    PeTTaPassesJudgment claim := by
  have passes : Mettapedia.Languages.MeTTa.PeTTa.isPassThroughType
      claim.expected := (pettaSuccessDecide_eq_true claim).mp accepted
  intro space bindings
  exact Mettapedia.Languages.MeTTa.PeTTa.meTTaEval_ground_passThrough passes

/-- PeTTa's undefined expected type is its unknown-only fragment. -/
def PeTTaUnknownOnly (claim : PeTTaSuccessClaim) : Prop :=
  claim.expected = Mettapedia.Languages.MeTTa.PeTTa.undefinedType

/-- A deliberately unsupported PeTTa expected type. -/
def pettaRejectedClaim : PeTTaSuccessClaim where
  symbol := "native-success-subject"
  expected := .apply "NativeSuccessUnsupportedType" []

/-- PeTTa's undefined-type pass-through is a nondegenerate success interface
over the live `MeTTaEval` relation. -/
def pettaSuccessInterface : SuccessInterface PeTTaSuccessClaim where
  decide := pettaSuccessDecide
  Judges := PeTTaPassesJudgment
  sound := pettaSuccessDecide_sound
  UnknownOnly := PeTTaUnknownOnly
  witness := ⟨⟨"native-unknown",
    Mettapedia.Languages.MeTTa.PeTTa.undefinedType⟩, rfl⟩
  never_rejects := by
    intro claim unknown
    rcases claim with ⟨symbol, expected⟩
    unfold PeTTaUnknownOnly at unknown
    dsimp at unknown
    subst expected
    rfl
  rejects := by
    exact ⟨pettaRejectedClaim, rfl⟩

/-- Positive HE witness: some unknown-only claim is operationally accepted. -/
theorem heSuccessInterface_positive :
    ∃ claim, heSuccessInterface.UnknownOnly claim ∧
      heSuccessInterface.decide claim = true := by
  rcases heSuccessInterface.witness with ⟨claim, unknown⟩
  exact ⟨claim, unknown, heSuccessInterface.never_rejects claim unknown⟩

/-- Negative HE witness: success typing still rejects an unsupported type. -/
theorem heSuccessInterface_negative :
    ∃ claim, heSuccessInterface.decide claim = false :=
  heSuccessInterface.rejects

/-- Positive PeTTa witness: some unknown-only claim is operationally accepted. -/
theorem pettaSuccessInterface_positive :
    ∃ claim, pettaSuccessInterface.UnknownOnly claim ∧
      pettaSuccessInterface.decide claim = true := by
  rcases pettaSuccessInterface.witness with ⟨claim, unknown⟩
  exact ⟨claim, unknown, pettaSuccessInterface.never_rejects claim unknown⟩

/-- Negative PeTTa witness: success typing still rejects an unsupported type. -/
theorem pettaSuccessInterface_negative :
    ∃ claim, pettaSuccessInterface.decide claim = false :=
  pettaSuccessInterface.rejects

/-! ### Fast correct-by-construction Pattern typing

This is the named composite between a native MeTTa typing calculus and the
certificate-free NIK decision interface.  Its scope is deliberately exact:
direct annotations, the unknown top type, bare-symbol typing, and structural
expression typing from PeTTa's live `MeTTaType` calculus.  It is not presented
as a decision procedure for the recursive arrow fragment.

Inside the trusted path, values carry an inductive `FastPatternTyping`
derivation and operations construct new derivations directly.  The Boolean
decision is used at an external publication boundary; its `Unit` certificate
has no choices and cannot contain a replay trace. -/

/-- A native typing query over Pattern terms and Pattern types. -/
structure PatternTypingClaim where
  space : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace
  term : Pattern
  type : Pattern

/-- The decidable, correct-by-construction fragment of PeTTa's native Pattern
typing calculus.  Every constructor is an actual `MeTTaType` rule. -/
inductive FastPatternTyping : PatternTypingClaim → Prop where
  | annotation {space term type}
      (member : Mettapedia.Languages.MeTTa.PeTTa.typeAnnotationPat term type ∈
        space.facts) :
      FastPatternTyping ⟨space, term, type⟩
  | undefined {space term} :
      FastPatternTyping ⟨space, term,
        Mettapedia.Languages.MeTTa.PeTTa.undefinedType⟩
  | symbol {space name} :
      FastPatternTyping ⟨space, .apply name [],
        Mettapedia.Languages.MeTTa.PeTTa.atomType⟩
  | application {space name arguments} (nonempty : arguments ≠ []) :
      FastPatternTyping ⟨space, .apply name arguments,
        Mettapedia.Languages.MeTTa.PeTTa.expressionType⟩

/-- The structural half of the executable fragment decision. -/
def fastIntrinsicTypeBool (term type : Pattern) : Bool :=
  match term with
  | .apply _ [] => type == Mettapedia.Languages.MeTTa.PeTTa.atomType
  | .apply _ (_ :: _) =>
      type == Mettapedia.Languages.MeTTa.PeTTa.expressionType
  | _ => false

/-- Executable native typing decision for the stated fragment. -/
def fastPatternTypingBool (claim : PatternTypingClaim) : Bool :=
  claim.space.facts.contains
      (Mettapedia.Languages.MeTTa.PeTTa.typeAnnotationPat claim.term claim.type) ||
    ((claim.type == Mettapedia.Languages.MeTTa.PeTTa.undefinedType) ||
      fastIntrinsicTypeBool claim.term claim.type)

/-- The executable decision is exact for the independently presented
inductive fragment, not merely sound. -/
theorem fastPatternTypingBool_correct (claim : PatternTypingClaim) :
    fastPatternTypingBool claim = true ↔ FastPatternTyping claim := by
  rcases claim with ⟨space, term, type⟩
  constructor
  · intro accepted
    simp only [fastPatternTypingBool, Bool.or_eq_true] at accepted
    rcases accepted with annotated | unknown | intrinsic
    · exact .annotation (List.contains_iff_mem.mp annotated)
    · have typeEq : type = Mettapedia.Languages.MeTTa.PeTTa.undefinedType :=
        beq_iff_eq.mp unknown
      subst type
      exact .undefined
    · cases term with
      | bvar index => simp [fastIntrinsicTypeBool] at intrinsic
      | fvar name => simp [fastIntrinsicTypeBool] at intrinsic
      | lambda binder body => simp [fastIntrinsicTypeBool] at intrinsic
      | multiLambda count binders body => simp [fastIntrinsicTypeBool] at intrinsic
      | subst body replacement => simp [fastIntrinsicTypeBool] at intrinsic
      | collection kind elements rest => simp [fastIntrinsicTypeBool] at intrinsic
      | apply name arguments =>
          cases arguments with
          | nil =>
              have typeEq : type = Mettapedia.Languages.MeTTa.PeTTa.atomType :=
                beq_iff_eq.mp intrinsic
              subst type
              exact .symbol
          | cons first rest =>
              have typeEq : type =
                  Mettapedia.Languages.MeTTa.PeTTa.expressionType :=
                beq_iff_eq.mp intrinsic
              subst type
              exact .application (List.cons_ne_nil first rest)
  · intro derivation
    cases derivation with
    | annotation member =>
        simp only [fastPatternTypingBool, Bool.or_eq_true]
        exact Or.inl (List.contains_iff_mem.mpr member)
    | undefined => simp [fastPatternTypingBool]
    | symbol => simp [fastPatternTypingBool, fastIntrinsicTypeBool]
    | application nonempty =>
        rename_i arguments
        cases arguments with
        | nil => exact (nonempty rfl).elim
        | cons first rest =>
            simp [fastPatternTypingBool, fastIntrinsicTypeBool]

/-- The native Pattern typing fragment as a certificate-free decision
kernel. -/
def fastPatternTypingKernel :
    Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker.DecisionKernel
      PatternTypingClaim FastPatternTyping where
  decide := fastPatternTypingBool
  correct := fastPatternTypingBool_correct

/-- Calculus soundness: every fast derivation is a derivation in PeTTa's
authored Pattern typing relation. -/
theorem FastPatternTyping.language_sound {claim : PatternTypingClaim}
    (derivation : FastPatternTyping claim) :
    Mettapedia.Languages.MeTTa.PeTTa.MeTTaType
      claim.space claim.term claim.type := by
  cases derivation with
  | annotation member => exact .typeAnnotation _ _ member
  | undefined => exact .undefinedIsTop _
  | symbol => exact .symbolIsAtom _
  | application nonempty => exact .appIsExpression _ _ nonempty

/-- An interior fast-path value carries its derivation as its type; no replay
certificate or checker call is stored in it. -/
structure FastTypedPattern (claim : PatternTypingClaim) where
  derivation : FastPatternTyping claim

/-- Correct-by-construction weakening to the native unknown type. -/
theorem FastTypedPattern.toUnknown {claim : PatternTypingClaim}
    (_typed : FastTypedPattern claim) :
    FastTypedPattern ⟨claim.space, claim.term,
      Mettapedia.Languages.MeTTa.PeTTa.undefinedType⟩ :=
  ⟨FastPatternTyping.undefined⟩

/-- Publication through NIK is available from the carried derivation, while
the language judgment follows directly from calculus soundness. -/
theorem fast_pattern_typing_correct_by_construction
    {claim : PatternTypingClaim} (typed : FastTypedPattern claim) :
    Mettapedia.Languages.MeTTa.PeTTa.MeTTaType
        claim.space claim.term claim.type ∧
      fastPatternTypingKernel.toChecker.check claim () = true :=
  ⟨typed.derivation.language_sound,
    (fastPatternTypingKernel.correct claim).mpr typed.derivation⟩

/-- The NIK publication boundary is exact for the native fragment. -/
theorem fastPatternTyping_authority :
    fastPatternTypingKernel.toChecker.Authority FastPatternTyping :=
  fastPatternTypingKernel.authority

/-- There is no certificate choice and therefore no certificate-level
micro-trace in the fast Pattern typing authority. -/
theorem fastPatternTyping_certificate_irrelevant
    (claim : PatternTypingClaim) (left right : Unit) :
    fastPatternTypingKernel.toChecker.check claim left =
      fastPatternTypingKernel.toChecker.check claim right := by
  cases left
  cases right
  rfl

/-- Positive witness for the correct-by-construction fast path. -/
theorem fastPatternTyping_unknown_positive
    (space : Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace) (term : Pattern) :
    fastPatternTypingKernel.toChecker.check
      ⟨space, term, Mettapedia.Languages.MeTTa.PeTTa.undefinedType⟩ () = true :=
  (fastPatternTypingKernel.correct _).mpr .undefined

/-- A concrete unsupported claim is rejected: the composite is not an
always-accepting typing facade. -/
def fastPatternTypingRejected : PatternTypingClaim where
  space := Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace.empty
  term := .bvar 0
  type := .apply "NativeFastUnsupportedType" []

theorem fastPatternTyping_unsupported_negative :
    fastPatternTypingKernel.toChecker.check fastPatternTypingRejected () = false := by
  rfl

/-- Witness for the normative `directTypingPath` commitment.  Exact decision
and soundness into the guest calculus are both required, along with positive
and negative points; a constant decision facade cannot inhabit it. -/
structure DirectPatternTypingWitness where
  Meaning : PatternTypingClaim → Prop
  kernel : Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker.DecisionKernel
    PatternTypingClaim Meaning
  calculusSound : ∀ {claim}, Meaning claim →
    Mettapedia.Languages.MeTTa.PeTTa.MeTTaType
      claim.space claim.term claim.type
  positive : ∃ claim, Meaning claim
  negative : ∃ claim, ¬ Meaning claim

namespace DirectPatternTypingWitness

/-- The deliberately too-rich two-tag format for the selected direct
judgment.  It is used only as a negative exact-parity canary. -/
def taggedProofSystem (direct : DirectPatternTypingWitness) :
    Mettapedia.GSLT.LanguageDef.NIKMetalogic.NativeProofSystem
      PatternTypingClaim where
  ProofObject := Bool
  Judges := fun _ claim => direct.Meaning claim

end DirectPatternTypingWitness

/-- The live fast Pattern fragment discharges the direct-typing commitment. -/
def fastDirectPatternTypingWitness : DirectPatternTypingWitness where
  Meaning := FastPatternTyping
  kernel := fastPatternTypingKernel
  calculusSound := FastPatternTyping.language_sound
  positive := by
    exact ⟨⟨Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace.empty,
      .bvar 0, Mettapedia.Languages.MeTTa.PeTTa.undefinedType⟩,
      .undefined⟩
  negative := by
    refine ⟨fastPatternTypingRejected, ?_⟩
    intro derivation
    have accepted :=
      (fastPatternTypingKernel.correct fastPatternTypingRejected).mpr derivation
    have rejected :
        fastPatternTypingKernel.decide fastPatternTypingRejected = false := by
      rfl
    rw [rejected] at accepted
    contradiction

/-! ### Exact parity for the direct typing judgment

Direct decision and proof-relevant publication are different authority tiers.
The fast typing judgment is proposition-valued, so its canonical native proof
object is `Unit`: the kernel computes theoremhood directly and retains no
micro-trace.  staged-reflective candidate Need's proof-relevant boundary is constructed separately
below. -/

namespace FastPatternParity

open Mettapedia.GSLT.LanguageDef.NIKMetalogic

/-- The canonical native proof system for the proposition-valued fast typing
judgment.  It deliberately retains no proof tag. -/
def proofSystem : NativeProofSystem PatternTypingClaim where
  ProofObject := Unit
  Judges := fun _ claim => FastPatternTyping claim

/-- The native proof kernel performs the same direct computation as the
production typing decision; the `Unit` object contributes no work. -/
def nativeKernel : NativeProofKernel proofSystem where
  decide claim _ := fastPatternTypingBool claim
  correct claim _ := fastPatternTypingBool_correct claim

/-- Exact accepted/native fibre parity for the direct Pattern typing path. -/
def certificateEquivalence :
    CertificateEquivalence fastPatternTypingKernel.toChecker proofSystem :=
  nativeKernel.certificateEquivalence

/-- The direct typing checker is therefore an exact authority for inhabitation
of its canonical native judgment fibre. -/
theorem authority :
    fastPatternTypingKernel.toChecker.Authority
      (fun claim => Nonempty (proofSystem.ProofFibre claim)) :=
  certificateEquivalence.authority

/-- The native proof kernel adds no second typing pass: with its unique proof
object erased, its decision is definitionally the production decision. -/
theorem computes_directly (claim : PatternTypingClaim)
    (proof : proofSystem.ProofObject) :
    nativeKernel.decide claim proof = fastPatternTypingKernel.decide claim := by
  cases proof
  rfl

/-- The canonical typing proof fibre is proposition-like: every two judged
native objects in one fibre are equal. -/
theorem proofFibre_subsingleton (claim : PatternTypingClaim) :
    Subsingleton (proofSystem.ProofFibre claim) :=
  ⟨fun left right => by
    apply Subtype.ext
    cases left.1
    cases right.1
    rfl⟩

/-- A two-tag proof guest has the same theoremhood but strictly more proof
identity than the direct decision checker can preserve. -/
def taggedProofSystem : NativeProofSystem PatternTypingClaim where
  ProofObject := Bool
  Judges := fun _ claim => FastPatternTyping claim

/-- Negative parity witness: theoremhood parity cannot be silently promoted
to parity with an independently proof-relevant certificate format. -/
theorem no_tagged_certificateEquivalence :
    ¬ Nonempty
      (CertificateEquivalence fastPatternTypingKernel.toChecker
        taggedProofSystem) := by
  rintro ⟨boundary⟩
  let claim : PatternTypingClaim :=
    ⟨Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace.empty, .bvar 0,
      Mettapedia.Languages.MeTTa.PeTTa.undefinedType⟩
  have typed : FastPatternTyping claim := .undefined
  let falseProof : taggedProofSystem.ProofFibre claim := ⟨false, typed⟩
  let trueProof : taggedProofSystem.ProofFibre claim := ⟨true, typed⟩
  have sameAccepted :
      (boundary.fibreEquiv claim).symm falseProof =
        (boundary.fibreEquiv claim).symm trueProof := by
    apply Subtype.ext
    exact Subsingleton.elim _ _
  have sameProof : falseProof = trueProof :=
    (boundary.fibreEquiv claim).symm.injective sameAccepted
  have false_eq_true := congrArg (fun proof => proof.1) sameProof
  exact Bool.false_ne_true false_eq_true

end FastPatternParity

/-- Audit package for O8.  Exact theoremhood parity, a computing native
kernel, positive and negative claims, and the proof-tag counterexample are all
required together. -/
structure NativeAuthorityParityWitness
    (direct : DirectPatternTypingWitness) where
  guest : Mettapedia.GSLT.LanguageDef.NIKMetalogic.NativeProofSystem
    PatternTypingClaim
  nativeKernel : Mettapedia.GSLT.LanguageDef.NIKMetalogic.NativeProofKernel
    guest
  parity : Mettapedia.GSLT.LanguageDef.NIKMetalogic.CertificateEquivalence
    direct.kernel.toChecker guest
  computes_directly : ∀ claim proof,
    nativeKernel.decide claim proof = direct.kernel.decide claim
  positive : ∃ claim,
    direct.kernel.toChecker.check claim () = true
  negative : ∃ claim,
    direct.kernel.toChecker.check claim () = false
  fibres_subsingleton : ∀ claim, Subsingleton (guest.ProofFibre claim)
  tagged_format_not_exact :
    ¬ Nonempty
      (Mettapedia.GSLT.LanguageDef.NIKMetalogic.CertificateEquivalence
        direct.kernel.toChecker direct.taggedProofSystem)

/-- Concrete authority-from-birth witness for the direct Pattern fragment. -/
def fastNativeAuthorityParityWitness :
    NativeAuthorityParityWitness fastDirectPatternTypingWitness where
  guest := FastPatternParity.proofSystem
  nativeKernel := FastPatternParity.nativeKernel
  parity := FastPatternParity.certificateEquivalence
  computes_directly := FastPatternParity.computes_directly
  positive := by
    exact ⟨⟨Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace.empty,
      .bvar 0, Mettapedia.Languages.MeTTa.PeTTa.undefinedType⟩,
      fastPatternTyping_unknown_positive _ _⟩
  negative := ⟨fastPatternTypingRejected,
    fastPatternTyping_unsupported_negative⟩
  fibres_subsingleton := FastPatternParity.proofFibre_subsingleton
  tagged_format_not_exact :=
    FastPatternParity.no_tagged_certificateEquivalence

/-- The witness assembly for this candidate interface.  Its fields specify
concrete capability contracts and checker parity; it is not indexed by the
requirement tables and does not itself prove dialect-wide satisfaction or
semantic necessity of their classifications. -/
structure NativeTheoryAudit (cand : TypeTheoryCandidate) where
  equality : NativeEqualityArchitecture
  spaceModel : SpaceModel cand.modes cand.spine
  spaceCode : SpaceCodeWitness cand.modes cand.spine spaceModel
  quotation : QuotationWitness cand.modes cand.spine
  contextualBox : ContextualBoxWitness cand.modes cand.spine quotation
  levels : LevelWitness cand.modes
  grading : GradingWitness cand.modes
  evidence : EvidenceFibration cand.modes cand.spine
  InterfaceClaim : Type
  interface : SuccessInterface InterfaceClaim
  dependentFamilies : DependentFamilyWitness cand.modes cand.spine
  identityTypes : IdentityTypeWitness cand.modes cand.spine
  inductiveFamilies : BinaryInductiveFamilyWitness cand.modes cand.spine
  languageCodes : LanguageCodeWitness cand.modes cand.spine spaceModel
  universeTower : StratifiedUniverseWitness cand.modes cand.spine
  directTyping : DirectPatternTypingWitness
  authorityParity : NativeAuthorityParityWitness directTyping
  proofFlow : ∀ {Space Request Answer : Type} [DecidableEq Answer]
    (occurrences : Mettapedia.GSLT.Dynamics.OccurrenceSemantics.OccurrenceSource
      Space Request Answer)
    (keying : Mettapedia.GSLT.Dynamics.ProofRelevantNeed.RevisionKeying.{0, 0, 0}
      Space Request),
    Mettapedia.GSLT.Dynamics.RevisionedOccurrenceProofFlow.Witness occurrences keying


/-! ## §9 Parity for the declared checker boundary

The candidate's checker is compared with an independently given judgment —
the same square every hosted guest owes.  The generic interface below states
the proof-fibre contract; each realization establishes parity only for its
own declared judgment and fragment. -/

/-- The guest proof system is the generic NIK proof-object boundary, not a
second native-theory-specific definition. -/
abbrev GuestKernelSpec (Claim : Type uNativeClaim) :=
  Mettapedia.GSLT.LanguageDef.NIKMetalogic.NativeProofSystem.{
    uNativeClaim, uNativeProof} Claim

/-- Primary parity preserves the entire accepted/native proof fibre.  This is
strictly stronger than decode-only parity and rules out ignored proof tags. -/
abbrev KernelParity {Claim : Type uNativeClaim}
    {Certificate : Type uNativeCertificate}
    (checker : Checker Claim Certificate) (guest : GuestKernelSpec Claim) :=
  Mettapedia.GSLT.LanguageDef.NIKMetalogic.CertificateEquivalence checker guest

/-- A computing realization checks native proof objects directly. -/
abbrev ComputingRealization {Claim : Type uNativeClaim}
    (guest : GuestKernelSpec Claim) :=
  Mettapedia.GSLT.LanguageDef.NIKMetalogic.NativeProofKernel guest

/-- A decided relation is shared with the generic NIK metalogic.  The native
theory's conversion relation owes an instance of this exact interface. -/
abbrev DecidedRelation {α : Type} (R : α → α → Prop) :=
  Mettapedia.GSLT.LanguageDef.NIKMetalogic.DecidedRelation α R

/-! ## §10 The assembled candidate -/

/-- The assembled witness target, not a semantic derivation from observation
labels.  The direct operational typing judgment
and its exact parity square are already dependently coupled inside `audit`;
there is no second unconstrained checker field that could describe a different
logic.  The full proof-relevant modal judgment remains available separately as
`nativeTypingEvidenceDoctrine`, without pretending that its entire calculus
has acquired an executable decision procedure. -/
structure AssembledNativeTheory where
  candidate : TypeTheoryCandidate
  audit : NativeTheoryAudit candidate

namespace AssembledNativeTheory

/-- The primary checker is an exact authority for inhabitation of the native
proof judgment. -/
theorem primaryAuthority (theory : AssembledNativeTheory) :
    theory.audit.directTyping.kernel.toChecker.Authority
      (fun claim =>
        Nonempty (theory.audit.authorityParity.guest.ProofFibre claim)) :=
  theory.audit.authorityParity.parity.authority

/-- The primary certificate fibre and the direct computing kernel's accepted
fibre are equivalent through the native proof fibre.  This is the precise
parity square; it does not identify the two certificate languages. -/
def primaryToNativeKernel
    (theory : AssembledNativeTheory) (claim : PatternTypingClaim) :
    Mettapedia.GSLT.LanguageDef.NIKMetalogic.AcceptedCertificateFibre
        theory.audit.directTyping.kernel.toChecker claim ≃
      Mettapedia.GSLT.LanguageDef.NIKMetalogic.AcceptedCertificateFibre
        theory.audit.authorityParity.nativeKernel.toChecker claim :=
  (theory.audit.authorityParity.parity.fibreEquiv claim).trans
    (theory.audit.authorityParity.nativeKernel.certificateEquivalence.fibreEquiv
      claim).symm

/-- The proof-relevant native modal judgment is part of every assembled
theory as the fixed contextual evidence doctrine over `NativeTypingClaim`.
This exposes proofs as native data without conflating that tier with the
decidable Pattern fragment above. -/
def proofDoctrine (_theory : AssembledNativeTheory) :=
  nativeTypingEvidenceDoctrine

end AssembledNativeTheory


/-! ## §11 Open obligations

The typed ledger names theorem-level gaps that are not discharged by the
families-model witness bundle or by rule-algebra initiality.  The count and
duplicate check make accidental emptying or repeated bookkeeping visible.
An entry may be removed only in the same change that supplies its theorem and
connects that theorem to the assembled theory. -/

/-- Unresolved theorem boundaries in the native theory and its GSLT-IL
interpretation. -/
inductive OpenObligation where
  /-- Authored typing needs initiality/adequacy in semantic modal CwFs, not
  merely in rule algebras carrying the same operations. -/
  | semanticCwFInitiality
  /-- Interpretation kernels now derive raw congruence and renaming from
  substitution naturality.  The remaining typed rule regularity must likewise
  be forced by the semantic CwF model rather than supplied through a duplicate
  `TypingAlgebra`. -/
  | modelForcedRegularity
  /-- Generated operational judgments need a two-way adequacy theorem with the
  independently authored typing judgment on their stated fragment. -/
  | operationalTypingAdequacy
  /-- The exact returned-fibre theorem must be extended to full command syntax
  only after typed transport, substitution, cell coherence, and the universal
  factorization premises have been supplied. -/
  | fullCommandInternalLanguage
  /-- Beyond the finite eight-row conformance authority, the complete native
  judgment needs a sound, evidence-bearing executable authority over encoded
  syntax that is complete on a named fragment and abstains outside it. -/
  | executableNativeAuthority
deriving DecidableEq, Repr

/-- Human-readable statement of each machine-visible obligation. -/
def OpenObligation.description : OpenObligation → String
  | .semanticCwFInitiality =>
      "authored typing is initial and adequate in semantic modal CwFs"
  | .modelForcedRegularity =>
      "semantic CwF structure forces the remaining typed rule regularity"
  | .operationalTypingAdequacy =>
      "generated operational judgments agree with authored typing"
  | .fullCommandInternalLanguage =>
      "the internal-language theorem extends from the returned image to full commands"
  | .executableNativeAuthority =>
      "encoded native syntax has an evidence-bearing checker beyond the finite conformance image"

def openObligations : List OpenObligation :=
  [.semanticCwFInitiality,
    .modelForcedRegularity,
    .operationalTypingAdequacy,
    .fullCommandInternalLanguage,
    .executableNativeAuthority]

/-- Pinned obligation count: update together with the typed ledger. -/
theorem openObligations_count : openObligations.length = 5 := rfl

/-- Each open boundary occurs exactly once in the ledger. -/
theorem openObligations_nodup : openObligations.Nodup := by decide

/-- The assembled witness bundle is not the completed native theory. -/
theorem openObligations_nonempty : openObligations ≠ [] := by decide

/-! ## Axiom audit -/

#print axioms observationRequirementPolicy_injective
#print axioms candidate_assignedRequirements_eq
#print axioms zero_assignedRequirements_subset_candidate
#print axioms commitmentRequirementPolicy_injective
#print axioms commitmentRequirementPolicy_disjoint_candidate
#print axioms Space.sub_trans
#print axioms openObligations_count
#print axioms openObligations_nodup
#print axioms openObligations_nonempty
#print axioms AssembledNativeTheory.primaryAuthority
#print axioms StratifiedUniverseWitness.no_constant_mode
#print axioms FamiliesCwF.app_lam
#print axioms FamiliesCwF.lam_app
#print axioms familiesPiStructure
#print axioms familiesCwFLaws
#print axioms familiesCwFCoherence
#print axioms familiesCwF_sext_unique
#print axioms nonterminal_empty_substitutions_distinct
#print axioms basic_modal_cwf_laws_do_not_force_coherence
#print axioms familiesPatternOutside_ne_marker
#print axioms familiesRuntimePatternCode_decodes
#print axioms LanguageCodeWitness.isLanguagePattern_iff_decode_ne_none
#print axioms LanguageCodeWitness.image_proper
#print axioms familiesValidatedLanguageCode_decodes
#print axioms lambdaPiToLF_injective
#print axioms lambdaPiToLF_subst
#print axioms lambdaPiDecidedConversion
#print axioms lambdaPi_conversion_commutes
#print axioms lambdaPi_decision_sound
#print axioms lambdaPi_beta_positive
#print axioms lambdaPi_eta_positive
#print axioms lambdaPi_unrelated_negative
#print axioms nativeDecidedConversion
#print axioms nativeConversion_lambdaPi_agrees
#print axioms nativeConversion_beta_positive
#print axioms nativeConversion_code_pattern_negative
#print axioms nativeGradingWitness
#print axioms nativeEvidenceFibration
#print axioms nativeEvidence_reindex_separates
#print axioms heSuccessDecide_sound
#print axioms heSuccessInterface_positive
#print axioms heSuccessInterface_negative
#print axioms pettaSuccessDecide_sound
#print axioms pettaSuccessInterface_positive
#print axioms pettaSuccessInterface_negative
#print axioms fastPatternTypingBool_correct
#print axioms FastPatternTyping.language_sound
#print axioms fast_pattern_typing_correct_by_construction
#print axioms fastPatternTyping_authority
#print axioms fastPatternTyping_certificate_irrelevant
#print axioms fastPatternTyping_unknown_positive
#print axioms fastPatternTyping_unsupported_negative
#print axioms fastDirectPatternTypingWitness
#print axioms FastPatternParity.nativeKernel
#print axioms FastPatternParity.certificateEquivalence
#print axioms FastPatternParity.authority
#print axioms FastPatternParity.computes_directly
#print axioms FastPatternParity.proofFibre_subsingleton
#print axioms FastPatternParity.no_tagged_certificateEquivalence
#print axioms fastNativeAuthorityParityWitness
#print axioms familiesIdentityFormation
#print axioms familiesIdentityTypes
#print axioms familiesIdentityTypes_beta
#print axioms familiesIdentity_false_true_empty
#print axioms familiesBooleanInductive
#print axioms familiesBooleanInductive_beta_left
#print axioms familiesBooleanInductive_not_collapsed
#print axioms familiesUniverseLowerContract_target
#print axioms firstUniverseLowerContracts_distinct
#print axioms reflectiveCodeIter_add
#print axioms familiesQuotationWitness
#print axioms familiesQuotation_code_inhabited
#print axioms familiesQuotation_object_empty
#print axioms stageLevelWitness
#print axioms familiesContextualBoxWitness
#print axioms familiesQuotationTerms
#print axioms familiesQuotationTermsSome
#print axioms familiesQuotationTerms_unit_depth_one
#print axioms bare_modal_cwf_does_not_determine_quotation
#print axioms TwoSortRawHom.ext
#print axioms TwoSortRawHom.id_comp
#print axioms TwoSortRawHom.comp_id
#print axioms TwoSortRawHom.comp_assoc
#print axioms twoSortRawFold_unique_pointwise
#print axioms twoSortRawFold_unique
#print axioms twoSortNodeCount_betaShape_positive
#print axioms no_unit_to_twoSort_syntax_hom
#print axioms TwoSortEqualityProfile.rename_closed
#print axioms TwoSortRawHom.kernelProfile
#print axioms syntacticEqualityProfile_rel_iff
#print axioms substitutionUnstableTwoSortHom_has_no_substitution_action
#print axioms TwoSortEqualityProfile.rename_mk
#print axioms TwoSortEqualityProfile.substRaw_mk
#print axioms TwoSortEqualityProfile.substRaw_ids
#print axioms TwoSortEqualityProfile.substRaw_comp
#print axioms TwoSortEqualityProfile.quotientMap_mk
#print axioms twoSortProfileQuotientHom_respects
#print axioms twoSortPiSigmaIdConv_map
#print axioms twoSortPiSigmaIdConv_congr_pi
#print axioms twoSortPiSigmaIdConv_congr_sigma
#print axioms twoSortPiSigmaIdConv_congr_id
#print axioms twoSortPiSigmaIdConv_congr_lam
#print axioms twoSortPiSigmaIdConv_congr_app
#print axioms twoSortPiSigmaIdConv_congr_pair
#print axioms twoSortPiSigmaIdConv_congr_fst
#print axioms twoSortPiSigmaIdConv_congr_snd
#print axioms twoSortPiSigmaIdConv_congr_refl
#print axioms twoSortPiSigmaIdConv_subst_pointwise
#print axioms twoSortPiSigmaIdConv_subst_congr
#print axioms twoSortPiSigmaIdConversionProfile_beta
#print axioms twoSortPiSigmaIdProfile_beta_quotient
#print axioms syntacticProfile_u0_ne_u1
#print axioms syntacticEqualityProfile_finer
#print axioms twoSortPiSigmaIdProfile_not_finer_than_syntactic
#print axioms profile_equating_universes_blocks_identity
#print axioms profile_equating_universes_not_finer_than_syntactic
#print axioms TwoSortRawHom.factorThroughProfile_comp_projection
#print axioms TwoSortRawHom.factorThroughProfile_unique
#print axioms nativeRawFold_unique_pointwise
#print axioms NativeRawHom.ext
#print axioms nativeRawFold_unique
#print axioms twoSortProjection_embedTwoSort
#print axioms embedTwoSort_injective
#print axioms embedTwoSort_eq_iff
#print axioms quotedTwoSortUniverse_not_in_twoSort_image
#print axioms mixedNativeApplication_not_in_twoSort_image
#print axioms twoSortProjection_none_not_in_twoSort_image
#print axioms nativeRuntimePattern_not_in_twoSort_image
#print axioms nativeUniverseSuperposition_not_in_twoSort_image
#print axioms TwoSortPiSigmaIdRefinement.ctxMor_ids
#print axioms TwoSortPiSigmaIdRefinement.ctxMor_comp
#print axioms TwoSortPiSigmaIdRefinement.embedTwoSortSub_comp
#print axioms TwoSortPiSigmaIdRefinement.toNativeSupport_map_injective
#print axioms TwoSortPiSigmaIdRefinement.typingAt_embed_iff
#print axioms TwoSortPiSigmaIdRefinement.TypingAt.subst
#print axioms TwoSortPiSigmaIdRefinement.TypingAt.contextConv
#print axioms TwoSortPiSigmaIdRefinement.oneUniverseContext_identity_maps_to_native_identity
#print axioms TwoSortPiSigmaIdRefinement.stageSensitiveEndSub_has_no_typedTwoSort_preimage
#print axioms TwoSortPiSigmaIdRefinement.quotedTwoSortUniverse_has_no_intrinsic_typing
#print axioms NativeModalTyping.Context.lookup_lock
#print axioms NativeModalTyping.Context.lock_ne_unlocked
#print axioms NativeModalTyping.subst0_rename_wk
#print axioms NativeModalTyping.subst_inst0
#print axioms NativeModalTyping.rename_inst0
#print axioms NativeModalTyping.ContextRen.snoc
#print axioms NativeModalTyping.ContextRen.lock
#print axioms NativeModalTyping.primitiveLet_has_native_modal_type
#print axioms NativeModalTyping.primitiveLet_typable_but_not_syntactically_inlined
#print axioms NativeModalTyping.typing_rename
#print axioms NativeModalTyping.weakening
#print axioms NativeModalTyping.ContextMor.lift
#print axioms NativeModalTyping.ContextMor.lock
#print axioms NativeModalTyping.typing_subst
#print axioms NativeModalTyping.ContextMor.ids
#print axioms NativeModalTyping.ContextMor.comp
#print axioms NativeModalTyping.TypedSub.ext
#print axioms NativeModalTyping.toNativeSupport_map_injective
#print axioms NativeModalTyping.lookup_embedTwoSortContext
#print axioms NativeModalTyping.subst0_embedTwoSort
#print axioms NativeModalTyping.inst0_embedTwoSort
#print axioms NativeModalTyping.inst0_fst_embedTwoSort
#print axioms NativeModalTyping.typing_embedTwoSort
#print axioms NativeModalTyping.syntacticConversion_does_not_extend_twoSortPiSigmaId
#print axioms NativeModalTyping.quotedTwoSortUniverse_has_native_modal_type
#print axioms NativeModalTyping.quotation_typing_separates_native_from_intrinsic
#print axioms NativeModalTyping.ConversionPolicy.extends_syntactic
#print axioms NativeModalTyping.HasType.of_conversion_extension
#print axioms NativeModalTyping.HasType.of_syntactic
#print axioms NativeTypedInitiality.fold_typing
#print axioms NativeTypedInitiality.contextMap_unique
#print axioms NativeTypedInitiality.interpretations_agree
#print axioms NativeTypedInitiality.Interpretation.ext
#print axioms NativeTypedInitiality.initiality
#print axioms NativeTypedInitiality.interpretation_unique
#print axioms NativeTypedInitiality.universe_has_image
#print axioms NativeTypedInitiality.no_empty_judgment_model
#print axioms NativeTypedInitiality.quoted_universe_has_image
#print axioms runtimePattern?_embedRuntimePattern
#print axioms embedRuntimePattern_injective
#print axioms runtimePattern_image_iff
#print axioms quotedTwoSortUniverse_not_runtimePattern_image
#print axioms oneToZeroQuotation_cost_nonzero
#print axioms cost_decoration_is_external_and_nondegenerate
#print axioms evidence_decoration_is_external_and_nondegenerate
#print axioms mixedNativeApplication_node_count
#print axioms nativeNodeCount_positive
#print axioms NativeTypedInitiality.nodeCount_primitiveLet_image
#print axioms NativeTypedInitiality.nodeCount_model_separates_let_from_inlining
#print axioms NativeTypedInitiality.nodeCount_interpretation_exists
#print axioms familiesDependentFamilyWitness
#print axioms no_unit_to_native_syntax_hom
#print axioms nativeRawFold_embedTwoSort
#print axioms nativeSyntax_compatible_syntactic
#print axioms nativeSyntax_incompatible_with_universe_collapse
#print axioms nativeLiftRen_id
#print axioms nativeLiftRen_eq_twoSortLiftRen
#print axioms nativeLiftRen_comp_apply
#print axioms nativeRename_ext
#print axioms nativeRename_id
#print axioms nativeRename_comp
#print axioms nativeLiftSub_ext
#print axioms nativeSubst_ext
#print axioms nativeLiftSub_ids
#print axioms nativeSubst_ids
#print axioms nativeLiftSubOfRen
#print axioms nativeSubst_ofRen
#print axioms nativeSubst_quote
#print axioms nativeRename_liftSub
#print axioms nativeRename_subst
#print axioms nativeLiftSub_liftRen_apply
#print axioms nativeSubst_rename
#print axioms nativeSubst_liftSub_wk
#print axioms nativeLiftSubComp_apply
#print axioms nativeSubst_comp
#print axioms nativeSubComp_left_id
#print axioms nativeSubComp_right_id
#print axioms nativeSubComp_assoc
#print axioms nativeConsSub_zero
#print axioms nativeConsSub_succ
#print axioms nativeInlineLet_var_zero
#print axioms nativeLet_is_primitive_before_inlining
#print axioms nativeRename_embedTwoSort
#print axioms nativeLiftSub_embedTwoSortSub
#print axioms nativeSubst_embedTwoSort
#print axioms stageSensitiveSub_zero_component
#print axioms stageSensitiveSub_one_component
#print axioms stageSensitiveSub_unquoted
#print axioms stageSensitiveSub_quoted
#print axioms stageSensitiveSub_not_projection_constant
#print axioms NativeDecoratedTm.reindex_term
#print axioms NativeDecoratedTm.reindex_account
#print axioms NativeDecoratedTm.reindex_evidence
#print axioms NativeDecoratedTm.reindex_ids
#print axioms NativeDecoratedTm.reindex_comp
#print axioms nativeBoolObservation_rename
#print axioms nativeBoolObservation_rename_wk
#print axioms nativeBoolObservation_subst
#print axioms nativeBooleanEqualityProfile_validates_letInlining
#print axioms nativeBooleanEqualityProfile_separates_universes
#print axioms nativeSyntacticEqualityProfile_rejects_letInlining
#print axioms nativeBooleanConversion_extends_syntactic
#print axioms syntacticConversion_does_not_extend_nativeBoolean
#print axioms primitiveLet_typing_enters_nativeBoolean
#print axioms nativeBoolean_is_strict_nondegenerate_typing_extension
#print axioms NativeModalTyping.ConversionPolicy.extends_refl
#print axioms NativeModalTyping.ConversionPolicy.extends_trans
#print axioms NativeEqualityArchitecture.transport
#print axioms NativeEqualityArchitecture.strictExtension_ne_core
#print axioms selectedEquality_calibration_does_not_alias_core
#print axioms selectedEquality_has_no_stronger_production_profile
#print axioms selectedEquality_core_is_initial
#print axioms selectedEquality_transports_primitiveLet
#print axioms nativeLiftCostEnvironment_rename
#print axioms nativeGradedCost_rename
#print axioms nativeLiftCostEnvironment_subst
#print axioms nativeGradedCost_subst
#print axioms nativeLet_structural_cost
#print axioms nativeInlineLet_structural_cost
#print axioms graded_cost_not_profile_invariant
#print axioms nativeBoolean_cost_does_not_factor
#print axioms NativeDerivationCountBag.truthSet_galois
#print axioms NativeDerivationCountBag.truthSet_ofTruthSet
#print axioms NativeDerivationCountBag.ofTruthSet_truthSet_le
#print axioms NativeDerivationBag.truthSet_eq_count_truthSet
#print axioms NativeDerivationBag.singleton_at
#print axioms nativeTypingProofErasureAdjunction
#print axioms nativeTypingEvidence_not_subsingleton
#print axioms primitiveLetTypingClaim_in_erased_consequence
#print axioms nativeTyping_toThinReflection_not_injective
#print axioms primitiveLetEvidenceBags_same_truth
#print axioms primitiveLetEvidenceBagOne_strength
#print axioms primitiveLetEvidenceBagTwo_strength
#print axioms primitiveLetEvidenceBags_distinct
#print axioms nativeEvidence_strength_does_not_factor_through_truth
#print axioms no_reverse_adjacent_stage
#print axioms StagedReflectiveTm.reflectiveDepth_quote
#print axioms StagedReflectiveTm.quote_strictly_raises_reflectiveDepth
#print axioms nativeQuoteNext_reflectiveDepth
#print axioms nativeQuoteNext_strictly_raises
#print axioms quotedLanguage?_nativeQuotedLanguage
#print axioms nativeQuotedLanguage_has_type
#print axioms quotedTwoSortUniverse_not_quotedLanguage
#print axioms nativeQuoteCodeUnificationWitness

end Mettapedia.Languages.MeTTa.Experimental.StagedReflective
