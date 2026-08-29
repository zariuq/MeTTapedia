import Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyConstruction

/-!
# NIK capability selection for constructional indexed-family kernels

An authored indexed family supports two distinct native-calculus faces.

* A typed canonical schema and a typed substitution construct both endpoint
  judgments.  This face is available from a `TypedNativePresentation` alone.
* A raw authored equation with only its source judgment may be promoted
  without replay only when the declaration world additionally proves uniform
  preservation.

Both faces implement one gradual contract.  Inputs carrying a construction
witness are realized by either face.  The constructional face retains a raw
request unchanged for ordinary fallback, while the preservation face realizes
it natively.  Thus uniform raw preservation is a genuine strict capability,
not a dispatcher priority or an unchecked assertion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime
namespace NativeIndexedFamilyConstructionNIKSelection

open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
open Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredDeclarationSignature
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyConstruction
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyPresentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyTypedConversion
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.Declaration
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.Declaration.ComputationAuthority
open Mettapedia.TypeTheory

noncomputable section

/-! ## One shared gradual request contract -/

/-- An authored equation whose source endpoint is already typed.  Target
typing is deliberately absent: constructing it from this carrier is precisely
the additional uniform-preservation capability. -/
structure RawSourceRequest (presented : PresentedCandidate) where
  arity : Nat
  context : Tower.Ctx arity
  left : Tower.Tm arity
  right : Tower.Tm arity
  type : Tower.Tm arity
  authored : EquationOccurrence
    (equationSchemas (elaborate presented.source)) left right
  sourceTyping :
    HasType (extendRules Tower.rules presented.candidate.signature)
      context left type

namespace RawSourceRequest

/-- Forget only the construction witness and target typing of an intrinsically
constructed step. -/
def ofConstructed {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    {index : TypingIndex Tower.Head}
    {source target : NativeIndexedState presented index}
    (step : TypedNativePresentation.ConstructedStep typed source target) :
    RawSourceRequest presented where
  arity := index.arity
  context := index.context
  left := source.1
  right := target.1
  type := index.type
  authored := step.toTypedOccurrence.authored
  sourceTyping := step.toTypedOccurrence.sourceTyping

end RawSourceRequest

/-- The common request language distinguishes evidence already constructed by
the typed source generator from raw boundary evidence. -/
inductive Input {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented) where
  | constructed {index : TypingIndex Tower.Head}
      {source target : NativeIndexedState presented index}
      (step : TypedNativePresentation.ConstructedStep typed source target)
  | raw (request : RawSourceRequest presented)

namespace Input

def request {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented} :
    Input typed → RawSourceRequest presented
  | .constructed step => RawSourceRequest.ofConstructed step
  | .raw request => request

/-- Source meaning is exact authored/native receipt recovery.  It is not a
typing surrogate: source typing is already retained by the carrier. -/
def Valid {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented} (input : Input typed) : Prop :=
  presented.receiptEquiv.symm
      (presented.receiptEquiv input.request.authored) =
    input.request.authored

theorem valid {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented} (input : Input typed) :
    input.Valid :=
  presented.receiptEquiv.symm_apply_apply input.request.authored

end Input

/-- Native-calculus faces comparable inside the shared gradual contract. -/
inductive Face where
  | constructedImage
  | uniformRawPreservation
  deriving DecidableEq, Repr

def Face.le : Face → Face → Prop
  | .constructedImage, _ => True
  | .uniformRawPreservation, .uniformRawPreservation => True
  | .uniformRawPreservation, .constructedImage => False

instance : PartialOrder Face where
  le := Face.le
  le_refl := by intro face; cases face <;> trivial
  le_trans := by
    intro first middle last firstMiddle middleLast
    cases first <;> cases middle <;> cases last <;>
      simp_all [Face.le]
  le_antisymm := by
    intro first second firstSecond secondFirst
    cases first <;> cases second <;> simp_all [Face.le]

/-- Capabilities visible to this exact request fibre. -/
inductive Capability where
  | exactTypedImage
  | certificateFree
  | retainsRawFallback
  | uniformRawPreservation
  deriving DecidableEq, Repr

def supports : Face → Capability → Prop
  | _, .exactTypedImage => True
  | _, .certificateFree => True
  | _, .retainsRawFallback => True
  | .uniformRawPreservation, .uniformRawPreservation => True
  | .constructedImage, .uniformRawPreservation => False

/-- A successful result retains target typing, native proof evidence, and exact
authored provenance.  Fallback retains the complete raw request. -/
inductive Outcome {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented} (input : Input typed) where
  | realized
      (targetTyping :
        HasType (extendRules Tower.rules presented.candidate.signature)
          input.request.context input.request.right input.request.type)
      (evidence : presented.candidate.computation.Evidence
        input.request.left input.request.right)
      (exact : presented.receiptEquiv.symm evidence =
        input.request.authored)
  | fallback (retained : RawSourceRequest presented)
      (exact : retained = input.request)

namespace Outcome

/-- The target invariant is read from proof-carrying result constructors. -/
def Valid {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented} {input : Input typed} :
    Outcome input → Prop
  | .realized _ evidence _ =>
      presented.receiptEquiv.symm evidence = input.request.authored
  | .fallback retained _ => retained = input.request

theorem valid {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented} {input : Input typed}
    (outcome : Outcome input) : outcome.Valid := by
  cases outcome with
  | realized targetTyping evidence exact => exact exact
  | fallback retained exact => exact exact

/-- Positive observation of the realized branch without erasing its payload. -/
inductive IsRealized {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented} {input : Input typed} :
    Outcome input → Prop where
  | intro targetTyping evidence exact :
      IsRealized (.realized targetTyping evidence exact)

/-- Positive observation of the fallback branch and its retained source. -/
inductive IsFallback {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented} {input : Input typed} :
    Outcome input → Prop where
  | intro retained exact : IsFallback (.fallback retained exact)

end Outcome

/-- Operational provenance remains observable in every result. -/
structure Receipt {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented) where
  face : Face
  source : Input typed
  outcome : Outcome source

namespace Receipt

def Valid {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented} (receipt : Receipt typed) :
    Prop :=
  receipt.outcome.Valid

theorem valid {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented} (receipt : Receipt typed) :
    receipt.Valid :=
  receipt.outcome.valid

end Receipt

def sourceObject {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented) : AdmissionObject where
  Carrier := Input typed
  Meaning := Input.Valid

def targetObject {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented) : AdmissionObject where
  Carrier := Receipt typed
  Meaning := Receipt.Valid

/-! ## The two native operations -/

def constructedOutcome {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    {index : TypingIndex Tower.Head}
    {source target : NativeIndexedState presented index}
    (step : TypedNativePresentation.ConstructedStep typed source target) :
    Outcome (Input.constructed step) :=
  .realized step.toTypedOccurrence.targetTyping
    step.toTypedOccurrence.nativeEvidence
    (TypedOccurrence.authored_of_nativeEvidence _)

def fallbackOutcome {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    (request : RawSourceRequest presented) :
    Outcome (Input.raw request : Input typed) :=
  .fallback ((Input.raw request : Input typed).request) rfl

/-- The constructional face realizes exactly the typed source image.  A raw
request is retained unchanged rather than guessed, rejected, or rechecked. -/
def constructionalReceipt {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented) :
    Input typed → Receipt typed
  | .constructed step =>
      { face := .constructedImage
        source := .constructed step
        outcome := constructedOutcome step }
  | .raw request =>
      { face := .constructedImage
        source := .raw request
        outcome := fallbackOutcome request }

def constructionalOperation {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented) :
    sourceObject typed ⟶ targetObject typed where
  run := constructionalReceipt typed
  preserves := fun input _ => (constructionalReceipt typed input).valid

theorem constructional_constructed_is_realized
    {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    {index : TypingIndex Tower.Head}
    {source target : NativeIndexedState presented index}
    (step : TypedNativePresentation.ConstructedStep typed source target) :
    Outcome.IsRealized
      ((constructionalOperation typed).run (.constructed step)).outcome := by
  change Outcome.IsRealized
    (constructedOutcome step)
  exact .intro _ _ _

theorem constructional_raw_is_fallback
    {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    (request : RawSourceRequest presented) :
    Outcome.IsFallback
      ((constructionalOperation typed).run (.raw request)).outcome := by
  change Outcome.IsFallback
    (fallbackOutcome request)
  exact .intro _ _

/-- Uniform declaration preservation upgrades every source-typed raw request
to a complete typed native occurrence. -/
def preservingReceipt {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented)
    (preserves :
      presented.candidate.signature.DeclaredPreserves Tower.rules)
    (input : Input typed) : Receipt typed :=
  let authorized : PreservingPresentedCandidate :=
    { presented := presented, preserves := preserves }
  let occurrence := authorized.typedOccurrence input.request.authored
    input.request.sourceTyping
  { face := .uniformRawPreservation
    source := input
    outcome := .realized occurrence.targetTyping occurrence.nativeEvidence
      (TypedOccurrence.authored_of_nativeEvidence _) }

def preservingOperation {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented)
    (preserves :
      presented.candidate.signature.DeclaredPreserves Tower.rules) :
    sourceObject typed ⟶ targetObject typed where
  run := preservingReceipt typed preserves
  preserves := fun input _ => (preservingReceipt typed preserves input).valid

/-! ## The preservation-licensed NIK family -/

/-- The stronger family is constructible only from the actual declaration
preservation theorem. -/
def family {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented)
    (preserves :
      presented.candidate.signature.DeclaredPreserves Tower.rules) :
    RecognizedFamily Face (sourceObject typed) (targetObject typed) where
  package
    | .constructedImage => constructionalOperation typed
    | .uniformRawPreservation => preservingOperation typed preserves
  Capability := Capability
  supports := supports
  supports_mono := by
    intro weaker stronger related capability supported
    cases weaker with
    | constructedImage =>
        cases stronger with
        | constructedImage => exact supported
        | uniformRawPreservation => cases capability <;> trivial
    | uniformRawPreservation =>
        cases stronger with
        | constructedImage =>
            change False at related
            exact related.elim
        | uniformRawPreservation => exact supported
  strict_support_gain := by
    intro weaker stronger strict
    cases weaker with
    | constructedImage =>
        cases stronger with
        | constructedImage => exact (lt_irrefl _ strict).elim
        | uniformRawPreservation =>
            exact ⟨.uniformRawPreservation, by trivial, by
              simp [supports]⟩
    | uniformRawPreservation =>
        cases stronger with
        | constructedImage =>
            have impossible := strict.le
            change False at impossible
            exact impossible.elim
        | uniformRawPreservation => exact (lt_irrefl _ strict).elim
  recognized := {.constructedImage, .uniformRawPreservation}
  licensed := {.constructedImage, .uniformRawPreservation}
  licensed_subset_recognized := Finset.Subset.rfl
  licensed_nonempty := ⟨.constructedImage, by simp⟩

theorem order_iff_capability_inclusion {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented)
    (preserves :
      presented.candidate.signature.DeclaredPreserves Tower.rules)
    (first second : Face) :
    first ≤ second ↔
      ∀ capability,
        (family typed preserves).supports first capability →
          (family typed preserves).supports second capability := by
  constructor
  · exact fun related capability supported =>
      (family typed preserves).supports_mono related capability supported
  · intro included
    cases first <;> cases second
    · trivial
    · trivial
    · have impossible := included .uniformRawPreservation
      simp [family, supports] at impossible
    · trivial

theorem family_directed {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented)
    (preserves :
      presented.candidate.signature.DeclaredPreserves Tower.rules) :
    (family typed preserves).LicensedDirected := by
  intro first _ second _
  refine ⟨.uniformRawPreservation, by simp [family], ?_, ?_⟩
  · cases first <;> trivial
  · cases second <;> trivial

def uniformRequest {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented)
    (preserves :
      presented.candidate.signature.DeclaredPreserves Tower.rules) :
    (family typed preserves).CapabilityRequest where
  required := { .uniformRawPreservation }
  candidates := { .uniformRawPreservation }
  candidates_exact := by
    intro candidate
    cases candidate with
    | constructedImage =>
        constructor
        · intro impossible
          simp at impossible
        · rintro ⟨_, supportsRequired⟩
          have impossible := supportsRequired .uniformRawPreservation (by simp)
          change False at impossible
          exact impossible.elim
    | uniformRawPreservation =>
        constructor
        · intro _
          refine ⟨by simp [family], ?_⟩
          intro capability required
          have capabilityEqual : capability = .uniformRawPreservation := by
            simpa using required
          subst capability
          trivial
        · intro _
          simp
  candidates_nonempty := by simp

def uniformSelection {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented)
    (preserves :
      presented.candidate.signature.DeclaredPreserves Tower.rules) :
    (uniformRequest typed preserves).StrongestNativeCalculusPrinciple where
  val := .uniformRawPreservation
  property := by
    constructor
    · simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
        uniformRequest]
    · intro candidate candidateMember
      have candidateEqual : candidate = .uniformRawPreservation := by
        simpa [RecognizedFamily.CapabilityRequest.restrictedFamily,
          uniformRequest] using candidateMember
      subst candidate
      exact le_rfl

theorem uniformRequest_uniqueStrongest {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented)
    (preserves :
      presented.candidate.signature.DeclaredPreserves Tower.rules) :
    ∃! chosen,
      (uniformRequest typed preserves).restrictedFamily
        |>.IsGreatestLicensed chosen :=
  (uniformRequest typed preserves).existsUnique_strongest
    (family_directed typed preserves)

/-- The selected strongest operation realizes a raw source-typed request; it
cannot silently take the fallback branch. -/
theorem selected_raw_is_realized {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented)
    (preserves :
      presented.candidate.signature.DeclaredPreserves Tower.rules)
    (request : RawSourceRequest presented) :
    Outcome.IsRealized
      (((uniformRequest typed preserves).strongestOperation
        (uniformSelection typed preserves)).run (.raw request)).outcome := by
  change Outcome.IsRealized
    (preservingReceipt typed preserves (.raw request)).outcome
  exact .intro _ _ _

/-- Store the genuinely strongest raw-preserving family kernel at one exact
dependency revision. -/
def admitUniformAt {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented)
    (preserves :
      presented.candidate.signature.DeclaredPreserves Tower.rules)
    (dependencies : DependencySystem) (revision : dependencies.Revision) :=
  admitStrongestAt (family typed preserves) (uniformRequest typed preserves)
    (uniformSelection typed preserves) dependencies revision

/-! ## Native List construction and refusing controls -/

namespace Canary

open AuthoredIndexedFamilyConstruction.NativeList
open NativeIndexedFamilies.Intrinsic
open NativeIndexedFamilySource

noncomputable def nilConstructedInput : Input typedNativePresentation :=
  .constructed canonicalNilConstructedStep

/-- The typed List schema runs directly through the constructional face. -/
theorem nil_constructed_image_is_realized :
    Outcome.IsRealized
      ((constructionalOperation typedNativePresentation).run
        nilConstructedInput).outcome := by
  exact constructional_constructed_is_realized canonicalNilConstructedStep

/-- The same source information, when presented without its construction
witness, is retained for fallback by the weaker face.  It is not rechecked or
silently promoted. -/
noncomputable def nilRawRequest :
    RawSourceRequest nativeListPresentedCandidate :=
  RawSourceRequest.ofConstructed canonicalNilConstructedStep

theorem raw_nil_without_construction_witness_is_fallback :
    Outcome.IsFallback
      ((constructionalOperation typedNativePresentation).run
        (.raw nilRawRequest)).outcome := by
  exact constructional_raw_is_fallback nilRawRequest

/-- The lower raw layer still contains an ill-typed authored equation, while
the constructional source fibre has no state at that term. -/
theorem raw_untyped_nil_remains_outside_constructional_kernel
    (type : Tower.Tm 0) :
    Nonempty
        (EquationOccurrence
          nativeSchemas untypedNilLeft undeclaredElement) ∧
      ¬ ∃ source : NativeIndexedState nativeListPresentedCandidate
          ⟨0, (.nil : Tower.Ctx 0), type⟩,
        source.1 = untypedNilLeft :=
  raw_untyped_nil_has_no_constructional_source type

end Canary

/-! ## Axiom audit -/

#print axioms RawSourceRequest.ofConstructed
#print axioms Input.valid
#print axioms constructionalOperation
#print axioms constructional_constructed_is_realized
#print axioms constructional_raw_is_fallback
#print axioms preservingOperation
#print axioms order_iff_capability_inclusion
#print axioms uniformRequest_uniqueStrongest
#print axioms selected_raw_is_realized
#print axioms admitUniformAt
#print axioms Canary.nil_constructed_image_is_realized
#print axioms Canary.raw_nil_without_construction_witness_is_fallback
#print axioms Canary.raw_untyped_nil_remains_outside_constructional_kernel

end

end NativeIndexedFamilyConstructionNIKSelection
end Mettapedia.Languages.MeTTa.Prime
