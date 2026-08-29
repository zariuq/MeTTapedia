import Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission
import Mettapedia.Languages.MeTTa.Prime.DataFibration
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyReceiptEquipment
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyConversionPath

/-!
# NIK admitted flow for authored native indexed-family computation

An authored indexed-family presentation already supplies an exact,
substitution-natural equivalence between raw equation occurrences and native
computation evidence.  Typing both endpoints strengthens that comparison to an
equivalence between complete typed occurrences and complete proof-relevant
native receipts.

This module installs the forward direction as NIK's correct-by-construction
`admittedFlow` mode.  Admission is revision-indexed; current execution applies
only the retained occurrence-to-receipt map.  It does not replay the authored
presentation or invoke a conversion checker.  The inverse map and the two
round-trip theorems show that occurrence identity is not collapsed.

The construction is intentionally not a universal native-family checker.
Raw equation occurrences remain available below the typed boundary, and an
ill-typed occurrence cannot inhabit the admitted source fibre at all.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime
namespace NativeIndexedFamilyNIKAdmittedFlow

open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredDeclarationSignature
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyPresentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyReceiptEquipment
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyReceiptNaturality
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyTypedConversion
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyConversionPath
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyConversionPath.Canary
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.Declaration
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.Declaration.ComputationAuthority
open Mettapedia.Languages.MeTTa.Prime.DataFibration

noncomputable section

/-! ## Exact typed occurrence/native receipt equivalence -/

/-- The full native receipt type at one exact judgment index. -/
abbrev NativeReceipt (presented : PresentedCandidate) {n : Nat}
    (context : Tower.Ctx n) (left right type : Tower.Tm n) :=
  ProofRelevantStepReceipt Tower.rules presented.candidate.signature
    presented.candidate.computation context left right type

/-- Recover the typed authored occurrence from a complete native receipt.
Both endpoint derivations are retained, and the authored witness is recovered
through the already-proved exact receipt-fibre equivalence. -/
def typedOccurrenceOfNativeReceipt
    {presented : PresentedCandidate} {n : Nat}
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    (receipt : NativeReceipt presented context left right type) :
    TypedOccurrence presented context left right type where
  authored := presented.receiptEquiv.symm receipt.evidence
  sourceTyping := receipt.sourceTyping
  targetTyping := receipt.targetTyping

/-- Complete typed authored occurrences and complete native receipts carry
exactly the same proof-relevant information. -/
def typedOccurrenceNativeReceiptEquiv
    (presented : PresentedCandidate) {n : Nat}
    (context : Tower.Ctx n) (left right type : Tower.Tm n) :
    TypedOccurrence presented context left right type ≃
      NativeReceipt presented context left right type where
  toFun := TypedOccurrence.toProofRelevantReceipt
  invFun := typedOccurrenceOfNativeReceipt
  left_inv := by
    intro occurrence
    cases occurrence with
    | mk authored sourceTyping targetTyping =>
        simp [typedOccurrenceOfNativeReceipt,
          TypedOccurrence.toProofRelevantReceipt,
          TypedOccurrence.nativeEvidence]
  right_inv := by
    intro receipt
    cases receipt with
    | mk sourceTyping targetTyping evidence =>
        simp [typedOccurrenceOfNativeReceipt,
          TypedOccurrence.toProofRelevantReceipt,
          TypedOccurrence.nativeEvidence]

@[simp] theorem typedOccurrenceNativeReceiptEquiv_apply
    {presented : PresentedCandidate} {n : Nat}
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    (occurrence : TypedOccurrence presented context left right type) :
    typedOccurrenceNativeReceiptEquiv presented context left right type
        occurrence = occurrence.toProofRelevantReceipt :=
  rfl

@[simp] theorem nativeReceipt_roundtrip
    {presented : PresentedCandidate} {n : Nat}
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    (receipt : NativeReceipt presented context left right type) :
    (typedOccurrenceNativeReceiptEquiv presented context left right type)
        (typedOccurrenceOfNativeReceipt receipt) = receipt :=
  (typedOccurrenceNativeReceiptEquiv presented context left right type)
    |>.apply_symm_apply receipt

@[simp] theorem typedOccurrence_roundtrip
    {presented : PresentedCandidate} {n : Nat}
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    (occurrence : TypedOccurrence presented context left right type) :
    typedOccurrenceOfNativeReceipt occurrence.toProofRelevantReceipt =
      occurrence :=
  (typedOccurrenceNativeReceiptEquiv presented context left right type)
    |>.symm_apply_apply occurrence

/-! ## Common NIK admission arrow -/

/-- The source meaning records exact recoverability of the authored witness.
Typing itself is intrinsic in the carrier. -/
def typedOccurrenceAdmissionObject
    (presented : PresentedCandidate) {n : Nat}
    (context : Tower.Ctx n) (left right type : Tower.Tm n) :
    AdmissionObject where
  Carrier := TypedOccurrence presented context left right type
  Meaning := fun occurrence =>
    presented.receiptEquiv.symm occurrence.nativeEvidence =
      occurrence.authored

/-- The target meaning records exact recovery of the native evidence after
passing through the authored receipt fibre. -/
def nativeReceiptAdmissionObject
    (presented : PresentedCandidate) {n : Nat}
    (context : Tower.Ctx n) (left right type : Tower.Tm n) :
    AdmissionObject where
  Carrier := NativeReceipt presented context left right type
  Meaning := fun receipt =>
    presented.receiptEquiv
        (presented.receiptEquiv.symm receipt.evidence) = receipt.evidence

/-- Correct-by-construction authored-to-native flow.  Its executable map is
only receipt construction; the semantic proof was discharged once here. -/
def typedOccurrenceToNativeReceipt
    (presented : PresentedCandidate) {n : Nat}
    (context : Tower.Ctx n) (left right type : Tower.Tm n) :
    typedOccurrenceAdmissionObject presented context left right type ⟶
      nativeReceiptAdmissionObject presented context left right type where
  run := TypedOccurrence.toProofRelevantReceipt
  preserves := by
    intro occurrence _
    exact presented.receiptEquiv.apply_symm_apply occurrence.nativeEvidence

/-- The inverse receipt-to-authored flow retains the same exact witness. -/
def nativeReceiptToTypedOccurrence
    (presented : PresentedCandidate) {n : Nat}
    (context : Tower.Ctx n) (left right type : Tower.Tm n) :
    nativeReceiptAdmissionObject presented context left right type ⟶
      typedOccurrenceAdmissionObject presented context left right type where
  run := typedOccurrenceOfNativeReceipt
  preserves := by
    intro receipt _
    exact presented.receiptEquiv.symm_apply_apply
      (presented.receiptEquiv.symm receipt.evidence)

theorem typed_native_admission_roundtrip
    (presented : PresentedCandidate) {n : Nat}
    (context : Tower.Ctx n) (left right type : Tower.Tm n) :
    AdmissionHom.comp
        (typedOccurrenceToNativeReceipt presented context left right type)
        (nativeReceiptToTypedOccurrence presented context left right type) =
      AdmissionHom.id
        (typedOccurrenceAdmissionObject presented context left right type) := by
  apply AdmissionHom.ext
  funext occurrence
  exact typedOccurrence_roundtrip occurrence

theorem native_typed_admission_roundtrip
    (presented : PresentedCandidate) {n : Nat}
    (context : Tower.Ctx n) (left right type : Tower.Tm n) :
    AdmissionHom.comp
        (nativeReceiptToTypedOccurrence presented context left right type)
        (typedOccurrenceToNativeReceipt presented context left right type) =
      AdmissionHom.id
        (nativeReceiptAdmissionObject presented context left right type) := by
  apply AdmissionHom.ext
  funext receipt
  exact nativeReceipt_roundtrip receipt

/-! ## Revision-current admitted flow and Data entry mode -/

/-- Store the constructional occurrence-to-receipt realization at a selected
dependency revision. -/
def admitTypedOccurrenceFlowAt
    (presented : PresentedCandidate) {n : Nat}
    (context : Tower.Ctx n) (left right type : Tower.Tm n)
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    AdmittedAt dependencies revision
      (discreteOperationalObject
        (typedOccurrenceAdmissionObject presented context left right type))
      (discreteOperationalObject
        (nativeReceiptAdmissionObject presented context left right type)) where
  refinement := refinementOfAdmission
    (typedOccurrenceToNativeReceipt presented context left right type)

/-- A current admitted family flow is exposed at the common Data boundary as
the established certificate-free `admittedFlow` mode. -/
def activeEntryMode
    {presented : PresentedCandidate} {n : Nat}
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    (active :
      (admitTypedOccurrenceFlowAt presented context left right type
        dependencies admittedRevision).Active currentRevision) :
    EntryMode (NativeReceipt presented context left right type) :=
  .admittedFlow
    (typedOccurrenceAdmissionObject presented context left right type)
    (nativeReceiptAdmissionObject presented context left right type).Meaning
    active.toAdmissionHom

@[simp] theorem active_run_is_native_receipt_construction
    {presented : PresentedCandidate} {n : Nat}
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    (active :
      (admitTypedOccurrenceFlowAt presented context left right type
        dependencies admittedRevision).Active currentRevision)
    (occurrence : TypedOccurrence presented context left right type) :
    active.run occurrence = occurrence.toProofRelevantReceipt :=
  rfl

@[simp] theorem active_entry_requires_no_certificate
    {presented : PresentedCandidate} {n : Nat}
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    (active :
      (admitTypedOccurrenceFlowAt presented context left right type
        dependencies admittedRevision).Active currentRevision) :
    EntryMode.requiresCertificate (activeEntryMode active) = false :=
  rfl

/-- The current Data entry accepts the constructed native receipt using the
proof retained by admission.  No decision procedure appears in the theorem or
in the active runner. -/
theorem active_entry_accepts_constructed_receipt
    {presented : PresentedCandidate} {n : Nat}
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    (active :
      (admitTypedOccurrenceFlowAt presented context left right type
        dependencies admittedRevision).Active currentRevision)
    (occurrence : TypedOccurrence presented context left right type) :
    EntryMode.Accepted (activeEntryMode active) (active.run occurrence) := by
  exact active.toAdmissionHom.preserves occurrence
    (presented.receiptEquiv.symm_apply_apply occurrence.authored)

/-! ## Compatibility with the GSLT-IL equipment cell -/

/-- NIK's admitted execution is exactly the forward authored/native equipment
cell on the retained raw occurrence. -/
theorem active_run_evidence_is_receiptCell
    {presented : PresentedCandidate} {n : Nat}
    {context : Tower.Ctx n} {left right type : Tower.Tm n}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    (active :
      (admitTypedOccurrenceFlowAt presented context left right type
        dependencies admittedRevision).Active currentRevision)
    (occurrence : TypedOccurrence presented context left right type) :
    (active.run occurrence).evidence =
      (receiptCell presented n).map occurrence.authored :=
  rfl

/-- If the receipt comparison is natural, admitted construction commutes with
typed substitution on the whole receipt, not only after support erasure. -/
theorem admittedFlow_substitution_naturality
    {presented : PresentedCandidate}
    (naturality : ReceiptNaturality presented)
    {n m : Nat}
    {sourceContext : Tower.Ctx n} {targetContext : Tower.Ctx m}
    {left right type : Tower.Tm n}
    (occurrence : TypedOccurrence presented sourceContext left right type)
    (substitution : Sub Tower.Head n m)
    (typed : CtxMor
      (extendRules Tower.rules presented.candidate.signature)
      sourceContext targetContext substitution) :
    (typedOccurrenceToNativeReceipt presented targetContext
      (Presentation.subst substitution left)
      (Presentation.subst substitution right)
      (Presentation.subst substitution type)).run
        (occurrence.substitute substitution typed) =
      occurrence.toProofRelevantReceipt.substitute substitution typed :=
  occurrence.toProofRelevantReceipt_substitute naturality substitution typed

/-! ## Complete conversion-path admission -/

/-- Authored path meaning is exact recoverability after native realization.
The carrier already fixes the common typing fibre and retains every
intermediate typed state. -/
def authoredPathAdmissionObject
    (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    (source target : (authoredIndexedComputation presented).State index) :
    AdmissionObject where
  Carrier := AuthoredConversion presented source target
  Meaning := fun path =>
    nativeToAuthoredPath presented (authoredToNativePath presented path) = path

/-- Native path meaning is exact recovery after returning through the authored
presentation. -/
def nativePathAdmissionObject
    (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    (source target : (nativeIndexedComputation presented).State index) :
    AdmissionObject where
  Carrier := NativeConversion presented source target
  Meaning := fun path =>
    authoredToNativePath presented (nativeToAuthoredPath presented path) = path

/-- Constructional realization of a whole conversion derivation.  The runner
recurses structurally over the retained path and maps only its step evidence. -/
def authoredPathToNative
    (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    (source target : (authoredIndexedComputation presented).State index) :
    authoredPathAdmissionObject presented source target ⟶
      nativePathAdmissionObject presented source target where
  run := authoredToNativePath presented
  preserves := by
    intro path _
    exact native_authored_path_roundtrip presented
      (authoredToNativePath presented path)

/-- Exact inverse of complete native path realization. -/
def nativePathToAuthored
    (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    (source target : (nativeIndexedComputation presented).State index) :
    nativePathAdmissionObject presented source target ⟶
      authoredPathAdmissionObject presented source target where
  run := nativeToAuthoredPath presented
  preserves := by
    intro path _
    exact authored_native_path_roundtrip presented
      (nativeToAuthoredPath presented path)

theorem authored_native_path_admission_roundtrip
    (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    (source target : (authoredIndexedComputation presented).State index) :
    AdmissionHom.comp
        (authoredPathToNative presented source target)
        (nativePathToAuthored presented source target) =
      AdmissionHom.id (authoredPathAdmissionObject presented source target) := by
  apply AdmissionHom.ext
  funext path
  exact authored_native_path_roundtrip presented path

theorem native_authored_path_admission_roundtrip
    (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    (source target : (nativeIndexedComputation presented).State index) :
    AdmissionHom.comp
        (nativePathToAuthored presented source target)
        (authoredPathToNative presented source target) =
      AdmissionHom.id (nativePathAdmissionObject presented source target) := by
  apply AdmissionHom.ext
  funext path
  exact native_authored_path_roundtrip presented path

/-- Store the complete authored-to-native path realization at one dependency
revision. -/
def admitAuthoredPathFlowAt
    (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    (source target : (authoredIndexedComputation presented).State index)
    (dependencies : DependencySystem) (revision : dependencies.Revision) :
    AdmittedAt dependencies revision
      (discreteOperationalObject
        (authoredPathAdmissionObject presented source target))
      (discreteOperationalObject
        (nativePathAdmissionObject presented source target)) where
  refinement := refinementOfAdmission
    (authoredPathToNative presented source target)

/-- A current path admission is exposed through the common certificate-free
Data entry mode. -/
def activePathEntryMode
    {presented : PresentedCandidate}
    {index : TypingIndex Tower.Head}
    {source target : (authoredIndexedComputation presented).State index}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    (active :
      (admitAuthoredPathFlowAt presented source target dependencies
        admittedRevision).Active currentRevision) :
    EntryMode (NativeConversion presented source target) :=
  .admittedFlow
    (authoredPathAdmissionObject presented source target)
    (nativePathAdmissionObject presented source target).Meaning
    active.toAdmissionHom

@[simp] theorem active_path_run_is_structural_realization
    {presented : PresentedCandidate}
    {index : TypingIndex Tower.Head}
    {source target : (authoredIndexedComputation presented).State index}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    (active :
      (admitAuthoredPathFlowAt presented source target dependencies
        admittedRevision).Active currentRevision)
    (path : AuthoredConversion presented source target) :
    active.run path = authoredToNativePath presented path :=
  rfl

/-- The active NIK runner is the universal path lift induced by the exact
equivalence of authored and native primitive-step fibres. -/
@[simp] theorem active_path_run_is_free_conversion_lift
    {presented : PresentedCandidate}
    {index : TypingIndex Tower.Head}
    {source target : (authoredIndexedComputation presented).State index}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    (active :
      (admitAuthoredPathFlowAt presented source target dependencies
        admittedRevision).Active currentRevision)
    (path : AuthoredConversion presented source target) :
    active.run path =
      (authoredNativePathEquiv presented source target).toFun path :=
  rfl

@[simp] theorem active_path_requires_no_certificate
    {presented : PresentedCandidate}
    {index : TypingIndex Tower.Head}
    {source target : (authoredIndexedComputation presented).State index}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    (active :
      (admitAuthoredPathFlowAt presented source target dependencies
        admittedRevision).Active currentRevision) :
    EntryMode.requiresCertificate (activePathEntryMode active) = false :=
  rfl

theorem active_path_accepts_structural_realization
    {presented : PresentedCandidate}
    {index : TypingIndex Tower.Head}
    {source target : (authoredIndexedComputation presented).State index}
    {dependencies : DependencySystem}
    {admittedRevision currentRevision : dependencies.Revision}
    (active :
      (admitAuthoredPathFlowAt presented source target dependencies
        admittedRevision).Active currentRevision)
    (path : AuthoredConversion presented source target) :
    EntryMode.Accepted (activePathEntryMode active) (active.run path) := by
  exact active.toAdmissionHom.preserves path
    (authored_native_path_roundtrip presented path)

/-- Complete-path NIK realization commutes with typed substitution whenever
the authored/native step comparison does. -/
theorem admittedPathFlow_substitution_naturality
    {presented : PresentedCandidate}
    (naturality : ReceiptNaturality presented)
    {n m : Nat}
    {sourceContext : Tower.Ctx n} {targetContext : Tower.Ctx m}
    {type : Tower.Tm n}
    (substitution : Sub Tower.Head n m)
    (typed : CtxMor
      (extendRules Tower.rules presented.candidate.signature)
      sourceContext targetContext substitution)
    {source target : (authoredIndexedComputation presented).State
      ⟨n, sourceContext, type⟩}
    (path : AuthoredConversion presented source target) :
    (authoredPathToNative presented
      (substituteState presented substitution typed source)
      (substituteState presented substitution typed target)).run
        (substituteAuthoredPath presented substitution typed path) =
      substituteNativePath presented substitution typed
        ((authoredPathToNative presented source target).run path) :=
  authoredToNativePath_substitute naturality substitution typed path

/-! ## Concrete positives and adversarial negatives -/

namespace Canary

open AuthoredIndexedFamilyReceiptNaturality.NativeList
open AuthoredIndexedFamilyReceiptNaturality.NativeNatVec
open NativeIndexedFamilies.Intrinsic
open NativeIndexedFamilySource
open NativeNaturalVectorFamilies
open NativeNaturalVectorFamilySource

def dependencies : DependencySystem where
  Revision := Bool
  Dependency := Unit
  Value := Bool
  read revision _ := revision

noncomputable def nilAdmission :=
  admitTypedOccurrenceFlowAt nativeListPresentedCandidate contextAPZS
    nilIotaLeft nilIotaRight nilIotaResultType dependencies false

noncomputable def activeNil : nilAdmission.Active false :=
  nilAdmission.activate (dependencies.sameDependencies_refl false)

/-- The canonical List eliminator computation runs through the current
admitted flow and retains its exact native iota witness. -/
theorem current_nil_constructs_exact_receipt :
    (activeNil.run canonicalNilTypedOccurrence).evidence =
      nilIotaReceipt.evidence := by
  exact canonicalNilTypedOccurrence_nativeEvidence

noncomputable def natZeroAdmission :=
  admitTypedOccurrenceFlowAt natPresentedCandidate natContextPZS
    natZeroIotaLeft natZeroIotaRight natZeroIotaType dependencies false

noncomputable def activeNatZero : natZeroAdmission.Active false :=
  natZeroAdmission.activate (dependencies.sameDependencies_refl false)

/-- An independent Nat view of the shared Nat/Vec declaration source uses the
same generic NIK flow and retains its exact native witness. -/
theorem current_nat_zero_constructs_exact_receipt :
    (activeNatZero.run canonicalNatZeroTypedOccurrence).evidence =
      natZeroIotaReceipt.evidence := by
  exact canonicalNatZeroTypedOccurrence_nativeEvidence

/-- The Vec view of the same authored Nat/Vec source is a third, independently
indexed positive inhabitant of the generic flow. -/
noncomputable def canonicalVecNilTypedOccurrence :
    TypedOccurrence vecPresentedCandidate vecContextAPZS
      vecNilIotaLeft vecNilIotaRight vecNilIotaType where
  authored := vecPresentedCandidate.receiptEquiv.symm
    vecNilIotaReceipt.evidence
  sourceTyping := vecNilIotaReceipt.sourceTyping
  targetTyping := vecNilIotaReceipt.targetTyping

noncomputable def vecNilAdmission :=
  admitTypedOccurrenceFlowAt vecPresentedCandidate vecContextAPZS
    vecNilIotaLeft vecNilIotaRight vecNilIotaType dependencies false

noncomputable def activeVecNil : vecNilAdmission.Active false :=
  vecNilAdmission.activate (dependencies.sameDependencies_refl false)

theorem current_vec_nil_constructs_exact_receipt :
    (activeVecNil.run canonicalVecNilTypedOccurrence).evidence =
      vecNilIotaReceipt.evidence := by
  exact vecPresentedCandidate.receiptEquiv.apply_symm_apply
    vecNilIotaReceipt.evidence

/-- A changed selected dependency disables reuse of the admitted family
realization. -/
theorem stale_nil_has_no_active_flow :
    ¬ Nonempty (nilAdmission.Active true) := by
  rintro ⟨active⟩
  have changed := active.current ()
  simp [dependencies] at changed

/-- Staleness disables the realization but cannot erase the complete typed
source retained for fallback or later readmission. -/
theorem stale_nil_preserves_typed_fallback :
    (¬ Nonempty (nilAdmission.Active true)) ∧
      typedOccurrenceOfNativeReceipt
          canonicalNilTypedOccurrence.toProofRelevantReceipt =
        canonicalNilTypedOccurrence :=
  ⟨stale_nil_has_no_active_flow, typedOccurrence_roundtrip _⟩

noncomputable def nilPathAdmission :=
  admitAuthoredPathFlowAt nativeListPresentedCandidate
    canonicalNilTypedOccurrence.sourceState
    canonicalNilTypedOccurrence.targetState dependencies false

noncomputable def activeNilPath : nilPathAdmission.Active false :=
  nilPathAdmission.activate (dependencies.sameDependencies_refl false)

/-- A current NIK path realization retains the exact association tree of a
three-legged conversion, not merely its endpoints. -/
theorem current_nil_path_preserves_association_tree :
    activeNilPath.run authoredNilLeftAssociated =
      .trans
        (.trans canonicalNilTypedOccurrence.toNativeConversion
          (.symm canonicalNilTypedOccurrence.toNativeConversion))
        canonicalNilTypedOccurrence.toNativeConversion := by
  change
    authoredToNativePath nativeListPresentedCandidate
        authoredNilLeftAssociated =
      .trans
        (.trans canonicalNilTypedOccurrence.toNativeConversion
          (.symm canonicalNilTypedOccurrence.toNativeConversion))
        canonicalNilTypedOccurrence.toNativeConversion
  exact authored_nil_left_association_maps_structurally

/-- Two authored conversion histories with the same endpoints remain distinct
after current native realization. -/
theorem current_nil_path_does_not_collapse_association :
    activeNilPath.run authoredNilLeftAssociated ≠
      activeNilPath.run authoredNilRightAssociated := by
  intro equality
  exact
    authored_nil_association_trees_are_distinct
      ((authoredNativePathEquiv nativeListPresentedCandidate
        canonicalNilTypedOccurrence.sourceState
        canonicalNilTypedOccurrence.targetState).injective equality)

/-- A relevant revision change disables the complete path realization. -/
theorem stale_nil_path_has_no_active_flow :
    ¬ Nonempty (nilPathAdmission.Active true) := by
  rintro ⟨active⟩
  have changed := active.current ()
  simp [dependencies] at changed

/-- Staleness disables execution but leaves the complete authored conversion
history available for fallback or readmission. -/
theorem stale_nil_path_preserves_complete_fallback :
    (¬ Nonempty (nilPathAdmission.Active true)) ∧
      nativeToAuthoredPath nativeListPresentedCandidate
          (authoredToNativePath nativeListPresentedCandidate
            authoredNilLeftAssociated) =
        authoredNilLeftAssociated :=
  ⟨stale_nil_path_has_no_active_flow,
    authored_native_path_roundtrip _ _⟩

/-- The raw ill-typed nil equation still exists, but no value of the admitted
source carrier can be constructed at any proposed result type. -/
theorem raw_untyped_nil_cannot_enter_admitted_flow (type : Tower.Tm 0) :
    Nonempty
        (EquationOccurrence nativeSchemas untypedNilLeft undeclaredElement) ∧
      IsEmpty
        (typedOccurrenceAdmissionObject nativeListPresentedCandidate
          (.nil : Tower.Ctx 0) untypedNilLeft undeclaredElement type).Carrier :=
  ⟨⟨untypedNilOccurrence⟩, untypedNil_has_no_typedOccurrence type⟩

end Canary

/-! ## Axiom audit -/

#print axioms typedOccurrenceNativeReceiptEquiv
#print axioms typed_native_admission_roundtrip
#print axioms native_typed_admission_roundtrip
#print axioms active_run_is_native_receipt_construction
#print axioms active_entry_requires_no_certificate
#print axioms active_entry_accepts_constructed_receipt
#print axioms active_run_evidence_is_receiptCell
#print axioms admittedFlow_substitution_naturality
#print axioms authored_native_path_admission_roundtrip
#print axioms native_authored_path_admission_roundtrip
#print axioms active_path_run_is_structural_realization
#print axioms active_path_run_is_free_conversion_lift
#print axioms active_path_requires_no_certificate
#print axioms active_path_accepts_structural_realization
#print axioms admittedPathFlow_substitution_naturality
#print axioms Canary.current_nil_constructs_exact_receipt
#print axioms Canary.current_nat_zero_constructs_exact_receipt
#print axioms Canary.current_vec_nil_constructs_exact_receipt
#print axioms Canary.stale_nil_has_no_active_flow
#print axioms Canary.stale_nil_preserves_typed_fallback
#print axioms Canary.current_nil_path_preserves_association_tree
#print axioms Canary.current_nil_path_does_not_collapse_association
#print axioms Canary.stale_nil_path_has_no_active_flow
#print axioms Canary.stale_nil_path_preserves_complete_fallback
#print axioms Canary.raw_untyped_nil_cannot_enter_admitted_flow

end

end NativeIndexedFamilyNIKAdmittedFlow
end Mettapedia.Languages.MeTTa.Prime
