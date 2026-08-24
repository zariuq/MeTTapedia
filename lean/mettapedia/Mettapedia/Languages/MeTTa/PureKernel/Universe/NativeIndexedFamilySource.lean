import Mettapedia.Languages.MeTTa.PureKernel.Universe.AuthoredIndexedFamilyTypedConversion
import Mettapedia.Languages.MeTTa.PureKernel.Universe.NativeIndexedFamilies

/-!
# Authored source for Prime's native indexed-family kernel

The intrinsic List and identity declarations previously had a formed semantic
signature and proof-relevant iota receipts, but no source-faithful declaration
document connected them to the declaration-authoring GSLT.  This module supplies
that direction of the bridge.

The source document is primary.  Exact elaboration yields the existing native
signature, including the same logical root-computation support.  Equation
occurrences retain their authored schema index and substitution, while the
existing native iota evidence remains the computation-oriented realization.
No inverse reconstruction of source from an extensional signature is claimed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe
namespace NativeIndexedFamilySource

open AuthoredDeclarationSignature
open AuthoredIndexedFamilyPresentation
open AuthoredIndexedFamilyTypedConversion
open DeclarationHostedJudgments
open NativeIndexedFamilies.Intrinsic
open Presentation
open Presentation.Declaration
open Presentation.Declaration.IndexedFamily

/-! ## The exact authored inventory -/

def nilEquation : EquationSchema where
  label := `Prime.List.iota.nil
  arity := 4
  context := contextAPZS
  left := nilIotaLeft
  right := nilIotaRight
  type := nilIotaResultType

def consEquation : EquationSchema where
  label := `Prime.List.iota.cons
  arity := 6
  context := contextAPZSHeadTail
  left := consIotaLeft
  right := consIotaRight
  type := consIotaResultType

def identityEquation : EquationSchema where
  label := `Prime.Id.iota.refl
  arity := 4
  context := contextAXPD
  left := identityIotaLeft
  right := identityIotaRight
  type := identityIotaResultType

def nativeSchemas : List EquationSchema :=
  [nilEquation, consEquation, identityEquation]

def authoredDeclarations : List SourceDeclaration :=
  [.constant listName { type := listType },
   .constant nilName { type := nilType },
   .constant consName { type := consType },
   .constant eliminateName { type := eliminateType },
   .constant identityEliminateName { type := identityEliminateType },
   .equation nilEquation,
   .equation consEquation,
   .equation identityEquation]

def source : SourceDocument := sourceCodec.quote authoredDeclarations

@[simp] theorem source_elaborates_exactly :
    elaborate source = authoredDeclarations := by
  simp [source]

@[simp] theorem source_constant_declarations :
    constantDeclarations authoredDeclarations = declarations := by
  rfl

@[simp] theorem source_equation_schemas :
    equationSchemas authoredDeclarations = nativeSchemas := by
  rfl

/-! ## Authored occurrences and native computation evidence -/

def occurrenceToIotaEvidence {n : Nat} {left right : Tower.Tm n}
    (occurrence : EquationOccurrence nativeSchemas left right) :
    IotaEvidence n left right := by
  rcases occurrence with
    ⟨index, substitution, sourceEquation, targetEquation⟩
  revert substitution sourceEquation targetEquation
  refine Fin.cases ?_ (fun later => ?_) index
  · intro substitution sourceEquation targetEquation
    change Sub Tower.Head 4 n at substitution
    change Presentation.subst substitution nilIotaLeft = left at sourceEquation
    change Presentation.subst substitution nilIotaRight = right at targetEquation
    have evidence := IotaEvidence.substitute nilIotaReceipt.evidence substitution
    simpa only [sourceEquation, targetEquation] using evidence
  · refine Fin.cases ?_ (fun latest => ?_) later
    · intro substitution sourceEquation targetEquation
      change Sub Tower.Head 6 n at substitution
      change Presentation.subst substitution consIotaLeft = left at sourceEquation
      change Presentation.subst substitution consIotaRight = right at targetEquation
      have evidence :=
        IotaEvidence.substitute consIotaReceipt.evidence substitution
      simpa only [sourceEquation, targetEquation] using evidence
    · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) latest
      intro substitution sourceEquation targetEquation
      change Sub Tower.Head 4 n at substitution
      change (Presentation.subst substitution identityIotaLeft = left) at sourceEquation
      change (Presentation.subst substitution identityIotaRight = right) at targetEquation
      have evidence :=
        IotaEvidence.substitute identityIotaReceipt.evidence substitution
      simpa only [sourceEquation, targetEquation] using evidence

noncomputable def iotaEvidenceToOccurrence {n : Nat} {left right : Tower.Tm n}
    (evidence : IotaEvidence n left right) :
    EquationOccurrence nativeSchemas left right :=
  IotaEvidence.rec
    (motive := fun left right _ =>
      EquationOccurrence nativeSchemas left right)
    (fun element motive nilCase consCase =>
        { index := ⟨0, by decide⟩
          substitution :=
            nilSchemaSubstitution element motive nilCase consCase
          sourceEquation := by rfl
          targetEquation := by rfl })
    (fun element motive nilCase consCase head tail =>
        { index := ⟨1, by decide⟩
          substitution :=
            consSchemaSubstitution element motive nilCase consCase head tail
          sourceEquation := by rfl
          targetEquation := by rfl })
    (fun element point motive reflCase =>
        { index := ⟨2, by decide⟩
          substitution :=
            identitySchemaSubstitution element point motive reflCase
          sourceEquation := by rfl
          targetEquation := by rfl })
    evidence

theorem occurrence_support_iff_iota
    {n : Nat} {left right : Tower.Tm n} :
    Nonempty (EquationOccurrence nativeSchemas left right) ↔
      Nonempty (IotaEvidence n left right) := by
  constructor
  · rintro ⟨occurrence⟩
    exact ⟨occurrenceToIotaEvidence occurrence⟩
  · rintro ⟨evidence⟩
    exact ⟨iotaEvidenceToOccurrence evidence⟩

private theorem nilSchemaSubstitution_eta
    {n : Nat} (substitution : Sub Tower.Head 4 n) :
    nilSchemaSubstitution
        (substitution 3) (substitution 2) (substitution 1) (substitution 0) =
      substitution := by
  funext index
  fin_cases index <;> rfl

private theorem consSchemaSubstitution_eta
    {n : Nat} (substitution : Sub Tower.Head 6 n) :
    consSchemaSubstitution
        (substitution 5) (substitution 4) (substitution 3)
        (substitution 2) (substitution 1) (substitution 0) =
      substitution := by
  funext index
  fin_cases index <;> rfl

private theorem identitySchemaSubstitution_eta
    {n : Nat} (substitution : Sub Tower.Head 4 n) :
    identitySchemaSubstitution
        (substitution 3) (substitution 2) (substitution 1) (substitution 0) =
      substitution := by
  funext index
  fin_cases index <;> rfl

/-- Authored equation occurrences and native iota receipts retain exactly the
same proof fibre at each pair of endpoints.  This is stronger than equality of
logical support: the schema occurrence, its complete substitution, and every
constructor parameter survive translation in both directions. -/
noncomputable def occurrenceIotaEquiv
    {n : Nat} {left right : Tower.Tm n} :
    EquationOccurrence nativeSchemas left right ≃
      IotaEvidence n left right where
  toFun := occurrenceToIotaEvidence
  invFun := iotaEvidenceToOccurrence
  left_inv := by
    rintro ⟨index, substitution, sourceEquation, targetEquation⟩
    revert substitution sourceEquation targetEquation
    refine Fin.cases ?_ (fun later => ?_) index
    · intro substitution sourceEquation targetEquation
      subst left
      subst right
      apply EquationOccurrence.ext
      · rfl
      · exact heq_of_eq (nilSchemaSubstitution_eta substitution)
    · refine Fin.cases ?_ (fun latest => ?_) later
      · intro substitution sourceEquation targetEquation
        subst left
        subst right
        apply EquationOccurrence.ext
        · rfl
        · exact heq_of_eq (consSchemaSubstitution_eta substitution)
      · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) latest
        intro substitution sourceEquation targetEquation
        subst left
        subst right
        apply EquationOccurrence.ext
        · rfl
        · exact heq_of_eq (identitySchemaSubstitution_eta substitution)
  right_inv := by
    intro evidence
    cases evidence <;> rfl

private theorem rootComputation_eq_of_step_eq
    (first second : RootComputation Tower.Head)
    (stepEquation :
      @RootComputation.step Tower.Head first =
        @RootComputation.step Tower.Head second) : first = second := by
  cases first with
  | mk firstStep firstRename firstSubstitute =>
      cases second with
      | mk secondStep secondRename secondSubstitute =>
          dsimp at stepEquation
          cases stepEquation
          rfl

theorem authored_computation_support_eq_iota :
    (equationComputation nativeSchemas).support = iotaComputation := by
  apply rootComputation_eq_of_step_eq
  funext n left right
  exact propext occurrence_support_iff_iota

/-! ## Generic finite inventory instance -/

/-- The hand-authored List/identity inventory discharges the generic finite
source interface.  Its extensional interpretation is derived below; it is no
longer supplied as an independent equality field. -/
noncomputable def nativeListInventory : AuthoredCandidateInventory where
  declarations := authoredDeclarations
  candidate := listCandidate
  entries := by rfl
  receiptEquiv := by
    intro n left right
    change EquationOccurrence nativeSchemas left right ≃
      IotaEvidence n left right
    exact occurrenceIotaEquiv

/-! ## Source-to-host adequacy -/

theorem interpret_source_eq_rawSignature :
    interpret source = rawSignature := by
  exact nativeListInventory.interpretation

noncomputable def nativeListPresentedCandidate :
    PresentedCandidate := nativeListInventory.toPresentedCandidate

noncomputable def nativeFormationHost : FormationHost :=
  nativeListPresentedCandidate.toFormationHost

theorem native_host_signature_eq_rawSignature :
    nativeFormationHost.signature = rawSignature := by
  exact interpret_source_eq_rawSignature

/-- Any proof of native iota preservation promotes the same authored package
from a formation host to a computational host; no second source or checker is
introduced. -/
noncomputable def nativeComputationalHostOfIotaPreservation
    (preserves : IotaPreservation) : ComputationalHost :=
  nativeListPresentedCandidate.toComputationalHost
    (Presentation.Declaration.ComputationAuthority.declaredPreservesOfFamily
      preserves)

/-! ## Authored raw-support negative control -/

noncomputable def untypedNilOccurrence :
    EquationOccurrence nativeSchemas untypedNilLeft undeclaredElement :=
  occurrenceIotaEquiv.symm untypedNilEvidence

/-- An authored occurrence can denote a raw native reduction while its
parameter remains untypable.  Receipt equivalence therefore preserves the
gradual/raw layer; it does not silently grant computational authority. -/
theorem authored_raw_iota_does_not_imply_typed_parameters :
    Nonempty
        (EquationOccurrence nativeSchemas untypedNilLeft undeclaredElement) ∧
      ¬ HasType (.nil : Tower.Ctx 0) undeclaredElement
        (sortTm elementLevel) :=
  ⟨⟨untypedNilOccurrence⟩, undeclaredElement_not_hasType _⟩

/-! ## Constructional typed-conversion instance -/

/-- The canonical nil equation as its exact authored occurrence. -/
noncomputable def canonicalNilAuthoredOccurrence :
    EquationOccurrence nativeSchemas nilIotaLeft nilIotaRight :=
  occurrenceIotaEquiv.symm nilIotaReceipt.evidence

/-- Canonical nil computation enters the generic judgment-indexed native
conversion with the actual authored occurrence and both endpoint typings. -/
noncomputable def canonicalNilTypedOccurrence :
    TypedOccurrence nativeListPresentedCandidate contextAPZS
      nilIotaLeft nilIotaRight nilIotaResultType where
  authored := nativeListPresentedCandidate.receiptEquiv.symm
    nilIotaReceipt.evidence
  sourceTyping := nilIotaReceipt.sourceTyping
  targetTyping := nilIotaReceipt.targetTyping

/-- The generic bridge retains exactly the native nil receipt. -/
@[simp] theorem canonicalNilTypedOccurrence_nativeEvidence :
    canonicalNilTypedOccurrence.nativeEvidence = nilIotaReceipt.evidence := by
  exact nativeListPresentedCandidate.receiptEquiv.apply_symm_apply
    nilIotaReceipt.evidence

/-- Native conversion is constructed directly from the typed authored
occurrence; no checked derivation is replayed. -/
noncomputable def canonicalNilNativeConversion :=
  canonicalNilTypedOccurrence.toNativeConversion

/-- The raw ill-typed nil occurrence cannot enter any typed conversion fibre,
regardless of which result type is proposed. -/
theorem untypedNil_has_no_typedOccurrence (type : Tower.Tm 0) :
    IsEmpty
      (TypedOccurrence nativeListPresentedCandidate (.nil : Tower.Ctx 0)
        untypedNilLeft undeclaredElement type) := by
  constructor
  intro occurrence
  exact untypedNilLeft_not_hasType type occurrence.sourceTyping

/-! ## Negative source boundary -/

/-- Extensional interpretation cannot be used as a source decoder.  Native
families therefore retain their authored `PresentedCandidate` package even
after installing its faster semantic signature. -/
theorem no_signature_only_source_reconstruction :
    ¬ Function.Injective semanticSignature :=
  semanticSignature_not_injective

#print axioms source_elaborates_exactly
#print axioms occurrence_support_iff_iota
#print axioms occurrenceIotaEquiv
#print axioms authored_computation_support_eq_iota
#print axioms interpret_source_eq_rawSignature
#print axioms nativeListPresentedCandidate
#print axioms PresentedCandidate.computation_support_eq
#print axioms authored_raw_iota_does_not_imply_typed_parameters
#print axioms canonicalNilTypedOccurrence
#print axioms canonicalNilTypedOccurrence_nativeEvidence
#print axioms canonicalNilNativeConversion
#print axioms untypedNil_has_no_typedOccurrence
#print axioms no_signature_only_source_reconstruction

end NativeIndexedFamilySource
end Mettapedia.Languages.MeTTa.PureKernel.Universe
