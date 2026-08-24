import Mettapedia.Languages.MeTTa.PureKernel.Universe.NativeIndexedFamilySource
import Mettapedia.Languages.MeTTa.PureKernel.Universe.NativeNaturalVectorFamilySource

/-!
# Substitution-natural authored/native indexed-family receipts

A pointwise equivalence between authored equation occurrences and native
computation receipts preserves the evidence in each endpoint fibre.  Dependent
computation needs one further capability: that comparison must commute with
renaming and simultaneous substitution.

This module records that capability separately.  A source-directed family can
therefore be quoted and interpreted before it has earned a natural native
realization.  Once naturality is available, typed occurrences transport along
typed context morphisms and their native receipts agree exactly with direct
transport in the native computation.  No checker or global conversion
algorithm is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe
namespace AuthoredIndexedFamilyReceiptNaturality

open AuthoredDeclarationSignature
open AuthoredIndexedFamilyPresentation
open AuthoredIndexedFamilyTypedConversion
open Presentation
open Presentation.Declaration
open Presentation.Declaration.ComputationAuthority

/-! ## The additional naturality capability -/

/-- The existing authored/native receipt equivalence is natural in the open
term context.  This is stronger than fibrewise equivalence and weaker than a
claim that the family has a total conversion checker. -/
structure ReceiptNaturality (presented : PresentedCandidate) : Prop where
  rename :
    ∀ {n m : Nat} {left right : Tower.Tm n}
      (occurrence : EquationOccurrence
        (equationSchemas (elaborate presented.source)) left right)
      (renameMap : Ren n m),
      presented.receiptEquiv (occurrence.rename renameMap) =
        presented.candidate.computation.rename renameMap
          (presented.receiptEquiv occurrence)
  substitute :
    ∀ {n m : Nat} {left right : Tower.Tm n}
      (occurrence : EquationOccurrence
        (equationSchemas (elaborate presented.source)) left right)
      (substitution : Sub Tower.Head n m),
      presented.receiptEquiv (occurrence.substitute substitution) =
        presented.candidate.computation.substitute substitution
          (presented.receiptEquiv occurrence)

/-- Naturality can be proved directly on the finite authored inventory before
the inventory is quoted into a source document. -/
structure InventoryReceiptNaturality
    (inventory : AuthoredCandidateInventory) : Prop where
  rename :
    ∀ {n m : Nat} {left right : Tower.Tm n}
      (occurrence : EquationOccurrence
        (equationSchemas inventory.declarations) left right)
      (renameMap : Ren n m),
      inventory.receiptEquiv (occurrence.rename renameMap) =
        inventory.candidate.computation.rename renameMap
          (inventory.receiptEquiv occurrence)
  substitute :
    ∀ {n m : Nat} {left right : Tower.Tm n}
      (occurrence : EquationOccurrence
        (equationSchemas inventory.declarations) left right)
      (substitution : Sub Tower.Head n m),
      inventory.receiptEquiv (occurrence.substitute substitution) =
        inventory.candidate.computation.substitute substitution
          (inventory.receiptEquiv occurrence)

namespace InventoryReceiptNaturality

/-- Exact quotation transports inventory naturality to the corresponding
source-directed presentation.  The named schema transport prevents this law
from being hidden inside an opaque dependent cast. -/
noncomputable def toPresented
    {inventory : AuthoredCandidateInventory}
    (naturality : InventoryReceiptNaturality inventory) :
    ReceiptNaturality inventory.toPresentedCandidate where
  rename := by
    intro n m left right occurrence renameMap
    change EquationOccurrence
      (equationSchemas (elaborate inventory.source)) left right at occurrence
    change inventory.receiptEquiv
        (EquationOccurrence.schemaEquiv
          (congrArg equationSchemas inventory.elaborate_source)
          (occurrence.rename renameMap)) =
      inventory.candidate.computation.rename renameMap
        (inventory.receiptEquiv
          (EquationOccurrence.schemaEquiv
            (congrArg equationSchemas inventory.elaborate_source)
            occurrence))
    rw [EquationOccurrence.schemaEquiv_rename]
    exact naturality.rename _ renameMap
  substitute := by
    intro n m left right occurrence substitution
    change EquationOccurrence
      (equationSchemas (elaborate inventory.source)) left right at occurrence
    change inventory.receiptEquiv
        (EquationOccurrence.schemaEquiv
          (congrArg equationSchemas inventory.elaborate_source)
          (occurrence.substitute substitution)) =
      inventory.candidate.computation.substitute substitution
        (inventory.receiptEquiv
          (EquationOccurrence.schemaEquiv
            (congrArg equationSchemas inventory.elaborate_source)
            occurrence))
    rw [EquationOccurrence.schemaEquiv_substitute]
    exact naturality.substitute _ substitution

end InventoryReceiptNaturality

end AuthoredIndexedFamilyReceiptNaturality

namespace AuthoredIndexedFamilyTypedConversion.TypedOccurrence

open AuthoredIndexedFamilyReceiptNaturality
open AuthoredIndexedFamilyPresentation
open Presentation
open Presentation.Declaration
open Presentation.Declaration.ComputationAuthority

variable {n m : Nat} {presented : PresentedCandidate}
    {sourceContext : Tower.Ctx n} {targetContext : Tower.Ctx m}
    {left right type : Tower.Tm n}

/-- Typed simultaneous substitution transports the authored occurrence and
both endpoint derivations together.  The target is constructed directly in the
new typing fibre. -/
def substitute
    (occurrence : TypedOccurrence presented sourceContext left right type)
    (substitution : Sub Tower.Head n m)
    (typed : CtxMor
      (extendRules Tower.rules presented.candidate.signature)
      sourceContext targetContext substitution) :
    TypedOccurrence presented targetContext
      (Presentation.subst substitution left)
      (Presentation.subst substitution right)
      (Presentation.subst substitution type) where
  authored := occurrence.authored.substitute substitution
  sourceTyping := occurrence.sourceTyping.substitute typed
  targetTyping := occurrence.targetTyping.substitute typed

/-- Under a natural receipt comparison, transporting the authored occurrence
and then realizing it natively is exactly native receipt substitution. -/
theorem nativeEvidence_substitute
    (naturality : ReceiptNaturality presented)
    (occurrence : TypedOccurrence presented sourceContext left right type)
    (substitution : Sub Tower.Head n m)
    (typed : CtxMor
      (extendRules Tower.rules presented.candidate.signature)
      sourceContext targetContext substitution) :
    (occurrence.substitute substitution typed).nativeEvidence =
      presented.candidate.computation.substitute substitution
        occurrence.nativeEvidence := by
  exact naturality.substitute occurrence.authored substitution

/-- The whole proof-relevant typed receipt commutes with typed substitution.
This includes both typing derivations and the exact native computation
witness, not merely its propositional support. -/
theorem toProofRelevantReceipt_substitute
    (naturality : ReceiptNaturality presented)
    (occurrence : TypedOccurrence presented sourceContext left right type)
    (substitution : Sub Tower.Head n m)
    (typed : CtxMor
      (extendRules Tower.rules presented.candidate.signature)
      sourceContext targetContext substitution) :
    (occurrence.substitute substitution typed).toProofRelevantReceipt =
      occurrence.toProofRelevantReceipt.substitute substitution typed := by
  cases occurrence with
  | mk authored sourceTyping targetTyping =>
      dsimp [substitute,
        AuthoredIndexedFamilyTypedConversion.TypedOccurrence.nativeEvidence,
        AuthoredIndexedFamilyTypedConversion.TypedOccurrence.toProofRelevantReceipt,
        ProofRelevantStepReceipt.substitute]
      rw [naturality.substitute]

end AuthoredIndexedFamilyTypedConversion.TypedOccurrence

namespace AuthoredIndexedFamilyReceiptNaturality

open AuthoredDeclarationSignature
open AuthoredIndexedFamilyPresentation
open AuthoredIndexedFamilyTypedConversion
open Presentation
open Presentation.Declaration
open Presentation.Declaration.ComputationAuthority

/-! ## Native List and identity realization -/

namespace NativeList

open NativeIndexedFamilies.Intrinsic
open NativeIndexedFamilySource

/-- The exact List/identity occurrence-to-iota translation commutes with
renaming. -/
theorem occurrenceIotaEquiv_rename
    {n m : Nat} {left right : Tower.Tm n}
    (occurrence : EquationOccurrence nativeSchemas left right)
    (renameMap : Ren n m) :
    occurrenceIotaEquiv (occurrence.rename renameMap) =
      IotaEvidence.rename (occurrenceIotaEquiv occurrence) renameMap := by
  rcases occurrence with
    ⟨index, substitution, sourceEquation, targetEquation⟩
  revert substitution sourceEquation targetEquation
  refine Fin.cases ?_ (fun later => ?_) index
  · intro substitution sourceEquation targetEquation
    subst left
    subst right
    rfl
  · refine Fin.cases ?_ (fun latest => ?_) later
    · intro substitution sourceEquation targetEquation
      subst left
      subst right
      rfl
    · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) latest
      intro substitution sourceEquation targetEquation
      subst left
      subst right
      rfl

/-- The exact List/identity occurrence-to-iota translation commutes with
arbitrary simultaneous substitution. -/
theorem occurrenceIotaEquiv_substitute
    {n m : Nat} {left right : Tower.Tm n}
    (occurrence : EquationOccurrence nativeSchemas left right)
    (substitution : Sub Tower.Head n m) :
    occurrenceIotaEquiv (occurrence.substitute substitution) =
      IotaEvidence.substitute (occurrenceIotaEquiv occurrence) substitution := by
  rcases occurrence with
    ⟨index, authoredSubstitution, sourceEquation, targetEquation⟩
  revert authoredSubstitution sourceEquation targetEquation
  refine Fin.cases ?_ (fun later => ?_) index
  · intro authoredSubstitution sourceEquation targetEquation
    subst left
    subst right
    rfl
  · refine Fin.cases ?_ (fun latest => ?_) later
    · intro authoredSubstitution sourceEquation targetEquation
      subst left
      subst right
      rfl
    · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) latest
      intro authoredSubstitution sourceEquation targetEquation
      subst left
      subst right
      rfl

/-- The finite authored List/identity inventory is natural before quotation. -/
noncomputable def nativeListInventoryReceiptNaturality :
    InventoryReceiptNaturality nativeListInventory where
  rename := by
    intro n m left right occurrence renameMap
    change occurrenceIotaEquiv (occurrence.rename renameMap) =
      IotaEvidence.rename (occurrenceIotaEquiv occurrence) renameMap
    exact occurrenceIotaEquiv_rename occurrence renameMap
  substitute := by
    intro n m left right occurrence substitution
    change occurrenceIotaEquiv (occurrence.substitute substitution) =
      IotaEvidence.substitute (occurrenceIotaEquiv occurrence) substitution
    exact occurrenceIotaEquiv_substitute occurrence substitution

/-- The authored List/identity package has a substitution-natural native
receipt realization after exact quotation. -/
noncomputable def nativeListReceiptNaturality :
    ReceiptNaturality nativeListPresentedCandidate :=
  nativeListInventoryReceiptNaturality.toPresented

/-- Every typed substitution instance of the canonical nil rule carries the
same native receipt as direct substitution in the native computation. -/
theorem canonicalNil_nativeEvidence_substitutes
    {m : Nat} {targetContext : Tower.Ctx m}
    (substitution : Sub Tower.Head 4 m)
    (typed : CtxMor
      (extendRules Tower.rules
        nativeListPresentedCandidate.candidate.signature)
      contextAPZS targetContext substitution) :
    (canonicalNilTypedOccurrence.substitute substitution typed).nativeEvidence =
      nativeListPresentedCandidate.candidate.computation.substitute substitution
        canonicalNilTypedOccurrence.nativeEvidence := by
  exact TypedOccurrence.nativeEvidence_substitute
    nativeListReceiptNaturality canonicalNilTypedOccurrence substitution typed

/-- Naturality does not turn an untyped raw equation occurrence into an
intrinsic typed conversion. -/
theorem receipt_naturality_does_not_type_untyped_nil
    (type : Tower.Tm 0) :
    IsEmpty
      (TypedOccurrence nativeListPresentedCandidate (.nil : Tower.Ctx 0)
        untypedNilLeft undeclaredElement type) :=
  untypedNil_has_no_typedOccurrence type

end NativeList

/-! ## Shared Nat/Vec realization -/

namespace NativeNatVec

open NativeNaturalVectorFamilies
open NativeNaturalVectorFamilySource

/-- The shared Nat/Vec occurrence translation commutes with renaming. -/
theorem occurrenceIotaEquiv_rename
    {n m : Nat} {left right : Tower.Tm n}
    (occurrence : EquationOccurrence schemas left right)
    (renameMap : Ren n m) :
    occurrenceIotaEquiv (occurrence.rename renameMap) =
      IotaEvidence.rename (occurrenceIotaEquiv occurrence) renameMap := by
  rcases occurrence with
    ⟨index, substitution, sourceEquation, targetEquation⟩
  revert substitution sourceEquation targetEquation
  refine Fin.cases ?_ (fun later => ?_) index
  · intro substitution sourceEquation targetEquation
    subst left
    subst right
    rfl
  · refine Fin.cases ?_ (fun later => ?_) later
    · intro substitution sourceEquation targetEquation
      subst left
      subst right
      rfl
    · refine Fin.cases ?_ (fun latest => ?_) later
      · intro substitution sourceEquation targetEquation
        subst left
        subst right
        rfl
      · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) latest
        intro substitution sourceEquation targetEquation
        subst left
        subst right
        rfl

/-- The shared Nat/Vec occurrence translation commutes with arbitrary
simultaneous substitution. -/
theorem occurrenceIotaEquiv_substitute
    {n m : Nat} {left right : Tower.Tm n}
    (occurrence : EquationOccurrence schemas left right)
    (substitution : Sub Tower.Head n m) :
    occurrenceIotaEquiv (occurrence.substitute substitution) =
      IotaEvidence.substitute (occurrenceIotaEquiv occurrence) substitution := by
  rcases occurrence with
    ⟨index, authoredSubstitution, sourceEquation, targetEquation⟩
  revert authoredSubstitution sourceEquation targetEquation
  refine Fin.cases ?_ (fun later => ?_) index
  · intro authoredSubstitution sourceEquation targetEquation
    subst left
    subst right
    rfl
  · refine Fin.cases ?_ (fun later => ?_) later
    · intro authoredSubstitution sourceEquation targetEquation
      subst left
      subst right
      rfl
    · refine Fin.cases ?_ (fun latest => ?_) later
      · intro authoredSubstitution sourceEquation targetEquation
        subst left
        subst right
        rfl
      · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) latest
        intro authoredSubstitution sourceEquation targetEquation
        subst left
        subst right
        rfl

/-- Both candidate views of the shared source inherit the same natural
proof-relevant receipt translation. -/
noncomputable def natInventoryReceiptNaturality :
    InventoryReceiptNaturality natInventory where
  rename := by
    intro n m left right occurrence renameMap
    change occurrenceIotaEquiv (occurrence.rename renameMap) =
      IotaEvidence.rename (occurrenceIotaEquiv occurrence) renameMap
    exact occurrenceIotaEquiv_rename occurrence renameMap
  substitute := by
    intro n m left right occurrence substitution
    change occurrenceIotaEquiv (occurrence.substitute substitution) =
      IotaEvidence.substitute (occurrenceIotaEquiv occurrence) substitution
    exact occurrenceIotaEquiv_substitute occurrence substitution

noncomputable def vecInventoryReceiptNaturality :
    InventoryReceiptNaturality vecInventory where
  rename := by
    intro n m left right occurrence renameMap
    change occurrenceIotaEquiv (occurrence.rename renameMap) =
      IotaEvidence.rename (occurrenceIotaEquiv occurrence) renameMap
    exact occurrenceIotaEquiv_rename occurrence renameMap
  substitute := by
    intro n m left right occurrence substitution
    change occurrenceIotaEquiv (occurrence.substitute substitution) =
      IotaEvidence.substitute (occurrenceIotaEquiv occurrence) substitution
    exact occurrenceIotaEquiv_substitute occurrence substitution

noncomputable def natReceiptNaturality :
    ReceiptNaturality natPresentedCandidate :=
  natInventoryReceiptNaturality.toPresented

noncomputable def vecReceiptNaturality :
    ReceiptNaturality vecPresentedCandidate :=
  vecInventoryReceiptNaturality.toPresented

/-- Canonical Nat elimination is stable under every typed substitution in the
shared Nat/Vec declaration world. -/
theorem canonicalNatZero_nativeEvidence_substitutes
    {m : Nat} {targetContext : Tower.Ctx m}
    (substitution : Sub Tower.Head 3 m)
    (typed : CtxMor
      (extendRules Tower.rules natPresentedCandidate.candidate.signature)
      natContextPZS targetContext substitution) :
    (canonicalNatZeroTypedOccurrence.substitute substitution typed).nativeEvidence =
      natPresentedCandidate.candidate.computation.substitute substitution
        canonicalNatZeroTypedOccurrence.nativeEvidence := by
  exact TypedOccurrence.nativeEvidence_substitute
    natReceiptNaturality canonicalNatZeroTypedOccurrence substitution typed

/-- Shared-source naturality still cannot promote the raw ill-typed Nat
equation into an intrinsic conversion fibre. -/
theorem receipt_naturality_does_not_type_untyped_nat
    (type : Tower.Tm 0) :
    IsEmpty
      (TypedOccurrence natPresentedCandidate (.nil : Tower.Ctx 0)
        untypedNatZeroLeft zeroTm type) :=
  untypedNatZero_has_no_typedOccurrence type

end NativeNatVec

/-! ## Axiom audit -/

#print axioms AuthoredIndexedFamilyTypedConversion.TypedOccurrence.nativeEvidence_substitute
#print axioms AuthoredIndexedFamilyTypedConversion.TypedOccurrence.toProofRelevantReceipt_substitute
#print axioms NativeList.occurrenceIotaEquiv_rename
#print axioms NativeList.occurrenceIotaEquiv_substitute
#print axioms NativeList.nativeListInventoryReceiptNaturality
#print axioms NativeList.nativeListReceiptNaturality
#print axioms NativeList.canonicalNil_nativeEvidence_substitutes
#print axioms NativeList.receipt_naturality_does_not_type_untyped_nil
#print axioms NativeNatVec.occurrenceIotaEquiv_rename
#print axioms NativeNatVec.occurrenceIotaEquiv_substitute
#print axioms NativeNatVec.natReceiptNaturality
#print axioms NativeNatVec.vecReceiptNaturality
#print axioms NativeNatVec.canonicalNatZero_nativeEvidence_substitutes
#print axioms NativeNatVec.receipt_naturality_does_not_type_untyped_nat

end AuthoredIndexedFamilyReceiptNaturality
end Mettapedia.Languages.MeTTa.PureKernel.Universe
