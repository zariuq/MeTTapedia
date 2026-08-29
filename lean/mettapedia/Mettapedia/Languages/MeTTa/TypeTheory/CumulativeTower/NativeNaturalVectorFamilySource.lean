import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyTypedConversion
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeNaturalVectorFamilies

/-!
# Authored source for native natural numbers and indexed vectors

The Nat/Vec signature contains two strictly-positive family candidates and one
shared four-rule computation carrier.  This module instantiates the generic
authored-family inventory with that genuinely indexed, multi-family source.

The source is authored once.  Nat and Vec are two formed candidate views of the
same declaration world, and each view retains the complete equation-occurrence
fibre through an exact equivalence with native iota evidence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace NativeNaturalVectorFamilySource

open AuthoredDeclarationSignature
open AuthoredIndexedFamilyPresentation
open AuthoredIndexedFamilyTypedConversion
open DeclarationHostedJudgments
open NativeNaturalVectorFamilies
open Presentation
open Presentation.Declaration
open Presentation.Declaration.IndexedFamily

/-! ## Exact authored inventory -/

def natZeroEquation : EquationSchema where
  label := `Prime.Nat.iota.zero
  arity := 3
  context := natContextPZS
  left := natZeroIotaLeft
  right := natZeroIotaRight
  type := natZeroIotaType

def natSuccEquation : EquationSchema where
  label := `Prime.Nat.iota.succ
  arity := 4
  context := natContextPZSN
  left := natSuccIotaLeft
  right := natSuccIotaRight
  type := natSuccIotaType

def vecNilEquation : EquationSchema where
  label := `Prime.Vec.iota.nil
  arity := 4
  context := vecContextAPZS
  left := vecNilIotaLeft
  right := vecNilIotaRight
  type := vecNilIotaType

def vecConsEquation : EquationSchema where
  label := `Prime.Vec.iota.cons
  arity := 7
  context := vecContextAPZSNHeadTail
  left := vecConsIotaLeft
  right := vecConsIotaRight
  type := vecConsIotaType

def schemas : List EquationSchema :=
  [natZeroEquation, natSuccEquation, vecNilEquation, vecConsEquation]

def authoredDeclarations : List SourceDeclaration :=
  [.constant natName { type := natType },
   .constant zeroName { type := zeroType },
   .constant succName { type := succType },
   .constant natEliminateName { type := natEliminateType },
   .constant vecName { type := vecType },
   .constant vnilName { type := vnilType },
   .constant vconsName { type := vconsType },
   .constant vecEliminateName { type := vecEliminateType },
   .equation natZeroEquation,
   .equation natSuccEquation,
   .equation vecNilEquation,
   .equation vecConsEquation]

def source : SourceDocument := sourceCodec.quote authoredDeclarations

@[simp] theorem source_elaborates_exactly :
    elaborate source = authoredDeclarations := by
  simp [source]

@[simp] theorem source_constant_declarations :
    constantDeclarations authoredDeclarations = declarations := by
  rfl

@[simp] theorem source_equation_schemas :
    equationSchemas authoredDeclarations = schemas := by
  rfl

/-! ## Substitution tuples -/

def emptySubstitution {n : Nat} : Sub Tower.Head 0 n :=
  fun index => Fin.elim0 index

def substitution3 {n : Nat} (first second third : Tower.Tm n) :
    Sub Tower.Head 3 n :=
  consSub third (consSub second (consSub first emptySubstitution))

def substitution4 {n : Nat} (first second third fourth : Tower.Tm n) :
    Sub Tower.Head 4 n :=
  consSub fourth
    (consSub third (consSub second (consSub first emptySubstitution)))

def substitution7
    {n : Nat}
    (first second third fourth fifth sixth seventh : Tower.Tm n) :
    Sub Tower.Head 7 n :=
  consSub seventh
    (consSub sixth
      (consSub fifth
        (consSub fourth
          (consSub third
            (consSub second (consSub first emptySubstitution))))))

private theorem substitution3_eta {n : Nat}
    (substitution : Sub Tower.Head 3 n) :
    substitution3 (substitution 2) (substitution 1) (substitution 0) =
      substitution := by
  funext index
  fin_cases index <;> rfl

private theorem substitution4_eta {n : Nat}
    (substitution : Sub Tower.Head 4 n) :
    substitution4
        (substitution 3) (substitution 2) (substitution 1) (substitution 0) =
      substitution := by
  funext index
  fin_cases index <;> rfl

private theorem substitution7_eta {n : Nat}
    (substitution : Sub Tower.Head 7 n) :
    substitution7
        (substitution 6) (substitution 5) (substitution 4)
        (substitution 3) (substitution 2) (substitution 1)
        (substitution 0) = substitution := by
  funext index
  fin_cases index <;> rfl

/-! ## Proof-fibre adequacy -/

def occurrenceToIotaEvidence {n : Nat} {left right : Tower.Tm n}
    (occurrence : EquationOccurrence schemas left right) :
    IotaEvidence n left right := by
  rcases occurrence with
    ⟨index, substitution, sourceEquation, targetEquation⟩
  revert substitution sourceEquation targetEquation
  refine Fin.cases ?_ (fun later => ?_) index
  · intro substitution sourceEquation targetEquation
    change Sub Tower.Head 3 n at substitution
    change Presentation.subst substitution natZeroIotaLeft = left at sourceEquation
    change Presentation.subst substitution natZeroIotaRight = right at targetEquation
    have evidence := IotaEvidence.substitute natZeroIotaReceipt.evidence substitution
    simpa only [sourceEquation, targetEquation] using evidence
  · refine Fin.cases ?_ (fun later => ?_) later
    · intro substitution sourceEquation targetEquation
      change Sub Tower.Head 4 n at substitution
      change Presentation.subst substitution natSuccIotaLeft = left at sourceEquation
      change Presentation.subst substitution natSuccIotaRight = right at targetEquation
      have evidence := IotaEvidence.substitute natSuccIotaReceipt.evidence substitution
      simpa only [sourceEquation, targetEquation] using evidence
    · refine Fin.cases ?_ (fun latest => ?_) later
      · intro substitution sourceEquation targetEquation
        change Sub Tower.Head 4 n at substitution
        change Presentation.subst substitution vecNilIotaLeft = left at sourceEquation
        change Presentation.subst substitution vecNilIotaRight = right at targetEquation
        have evidence := IotaEvidence.substitute vecNilIotaReceipt.evidence substitution
        simpa only [sourceEquation, targetEquation] using evidence
      · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) latest
        intro substitution sourceEquation targetEquation
        change Sub Tower.Head 7 n at substitution
        change Presentation.subst substitution vecConsIotaLeft = left at sourceEquation
        change Presentation.subst substitution vecConsIotaRight = right at targetEquation
        have evidence := IotaEvidence.substitute vecConsIotaReceipt.evidence substitution
        simpa only [sourceEquation, targetEquation] using evidence

noncomputable def iotaEvidenceToOccurrence
    {n : Nat} {left right : Tower.Tm n}
    (evidence : IotaEvidence n left right) :
    EquationOccurrence schemas left right :=
  IotaEvidence.rec
    (motive := fun left right _ => EquationOccurrence schemas left right)
    (fun motive zeroCase succCase =>
        { index := ⟨0, by decide⟩
          substitution := substitution3 motive zeroCase succCase
          sourceEquation := by rfl
          targetEquation := by rfl })
    (fun motive zeroCase succCase number =>
        { index := ⟨1, by decide⟩
          substitution := substitution4 motive zeroCase succCase number
          sourceEquation := by rfl
          targetEquation := by rfl })
    (fun element motive nilCase consCase =>
        { index := ⟨2, by decide⟩
          substitution := substitution4 element motive nilCase consCase
          sourceEquation := by rfl
          targetEquation := by rfl })
    (fun element motive nilCase consCase length head tail =>
        { index := ⟨3, by decide⟩
          substitution :=
            substitution7 element motive nilCase consCase length head tail
          sourceEquation := by rfl
          targetEquation := by rfl })
    evidence

noncomputable def occurrenceIotaEquiv
    {n : Nat} {left right : Tower.Tm n} :
    EquationOccurrence schemas left right ≃ IotaEvidence n left right where
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
      · exact heq_of_eq (substitution3_eta substitution)
    · refine Fin.cases ?_ (fun later => ?_) later
      · intro substitution sourceEquation targetEquation
        subst left
        subst right
        apply EquationOccurrence.ext
        · rfl
        · exact heq_of_eq (substitution4_eta substitution)
      · refine Fin.cases ?_ (fun latest => ?_) later
        · intro substitution sourceEquation targetEquation
          subst left
          subst right
          apply EquationOccurrence.ext
          · rfl
          · exact heq_of_eq (substitution4_eta substitution)
        · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) latest
          intro substitution sourceEquation targetEquation
          subst left
          subst right
          apply EquationOccurrence.ext
          · rfl
          · exact heq_of_eq (substitution7_eta substitution)
  right_inv := by
    intro evidence
    cases evidence <;> rfl

/-! ## Two candidate views of one authored source -/

noncomputable def natInventory : AuthoredCandidateInventory where
  declarations := authoredDeclarations
  candidate := natCandidate
  entries := by rfl
  receiptEquiv := by
    intro n left right
    change EquationOccurrence schemas left right ≃ IotaEvidence n left right
    exact occurrenceIotaEquiv

noncomputable def vecInventory : AuthoredCandidateInventory where
  declarations := authoredDeclarations
  candidate := vecCandidate
  entries := by rfl
  receiptEquiv := by
    intro n left right
    change EquationOccurrence schemas left right ≃ IotaEvidence n left right
    exact occurrenceIotaEquiv

noncomputable def natPresentedCandidate : PresentedCandidate :=
  natInventory.toPresentedCandidate

noncomputable def vecPresentedCandidate : PresentedCandidate :=
  vecInventory.toPresentedCandidate

theorem interpret_source_eq_rawSignature :
    interpret source = rawSignature := by
  exact natInventory.interpretation

@[simp] theorem candidate_views_share_source :
    natPresentedCandidate.source = vecPresentedCandidate.source := rfl

theorem candidate_views_share_signature :
    natPresentedCandidate.candidate.signature =
      vecPresentedCandidate.candidate.signature := rfl

noncomputable def natFormationHost : FormationHost :=
  natPresentedCandidate.toFormationHost

noncomputable def vecFormationHost : FormationHost :=
  vecPresentedCandidate.toFormationHost

theorem formation_hosts_share_source :
    natFormationHost.source = vecFormationHost.source := rfl

/-! ## Negative typed-authority boundary -/

noncomputable def untypedNatZeroOccurrence :
    EquationOccurrence schemas untypedNatZeroLeft zeroTm :=
  occurrenceIotaEquiv.symm untypedNatZeroEvidence

theorem authored_raw_nat_step_does_not_imply_typed_instance :
    Nonempty (EquationOccurrence schemas untypedNatZeroLeft zeroTm) ∧
      ∀ type : Tower.Tm 0,
        TypedIotaInstance (.nil : Tower.Ctx 0)
          untypedNatZeroLeft zeroTm type → False :=
  ⟨⟨untypedNatZeroOccurrence⟩, untypedNatZero_not_typedInstance⟩

/-! ## Independent constructional typed-conversion instance -/

/-- The canonical Nat-zero computation as an occurrence of the shared
authored Nat/Vec declaration world. -/
noncomputable def canonicalNatZeroAuthoredOccurrence :
    EquationOccurrence schemas natZeroIotaLeft natZeroIotaRight :=
  occurrenceIotaEquiv.symm natZeroIotaReceipt.evidence

/-- The Nat candidate independently instantiates the generic typed-conversion
bridge over the same declaration world used by the Vec candidate. -/
noncomputable def canonicalNatZeroTypedOccurrence :
    TypedOccurrence natPresentedCandidate natContextPZS
      natZeroIotaLeft natZeroIotaRight natZeroIotaType where
  authored := natPresentedCandidate.receiptEquiv.symm
    natZeroIotaReceipt.evidence
  sourceTyping := natZeroIotaReceipt.sourceTyping
  targetTyping := natZeroIotaReceipt.targetTyping

@[simp] theorem canonicalNatZeroTypedOccurrence_nativeEvidence :
    canonicalNatZeroTypedOccurrence.nativeEvidence =
      natZeroIotaReceipt.evidence := by
  exact natPresentedCandidate.receiptEquiv.apply_symm_apply
    natZeroIotaReceipt.evidence

noncomputable def canonicalNatZeroNativeConversion :=
  canonicalNatZeroTypedOccurrence.toNativeConversion

/-- A shared authored declaration world still refuses an ill-typed Nat
equation before either native candidate view can construct conversion. -/
theorem untypedNatZero_has_no_typedOccurrence (type : Tower.Tm 0) :
    IsEmpty
      (TypedOccurrence natPresentedCandidate (.nil : Tower.Ctx 0)
        untypedNatZeroLeft zeroTm type) := by
  constructor
  intro occurrence
  exact untypedNatZeroLeft_not_hasType type occurrence.sourceTyping

#print axioms source_elaborates_exactly
#print axioms occurrenceIotaEquiv
#print axioms natInventory
#print axioms vecInventory
#print axioms interpret_source_eq_rawSignature
#print axioms candidate_views_share_source
#print axioms authored_raw_nat_step_does_not_imply_typed_instance
#print axioms canonicalNatZeroTypedOccurrence
#print axioms canonicalNatZeroTypedOccurrence_nativeEvidence
#print axioms canonicalNatZeroNativeConversion
#print axioms untypedNatZero_has_no_typedOccurrence

end NativeNaturalVectorFamilySource
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
