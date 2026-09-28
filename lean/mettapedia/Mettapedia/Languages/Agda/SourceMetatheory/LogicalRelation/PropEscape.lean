import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropRelation
import Mettapedia.Languages.Agda.SourceEvidence.ProofRecovery

/-!
Escape is proved from the concrete clauses. Source derivations remain
Type-valued; the proposition-level conclusion can be reconstructed through
the checked codec. Weak-head normalization here is conditional on actual
logical-relation evidence, not on arbitrary source typing.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.StaticMetatheory
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

structure Escapes (Γ : RawContext n) (A : Ty n) (P : Pack n) : Prop where
  formation : Nonempty (FormTy Γ A)
  typeEquality : ∀ {B}, P.eqTy B → Nonempty (TypeEq Γ A B)
  typing : ∀ {t}, P.redTm t → Nonempty (Typing Γ t A)
  termEquality : ∀ {t u}, P.eqTm t u → Nonempty (TermEq Γ t u A)

private def expandEquality {Γ : RawContext n} {A B : Ty n} {t u nf ng : Term n}
    (left : TypedRed Γ t nf B) (right : TypedRed Γ u ng B)
    (equal : TermEq Γ nf ng B) (typeEqual : TypeEq Γ B A) : TermEq Γ t u A :=
  .conv (.trans left.equal (.trans equal (.symm right.equal))) typeEqual

theorem LR.escape {bound : Nat} {lower : Nat → Relation} {Γ : RawContext n}
    {A : Ty n} {P : Pack n} (related : LR bound lower Γ A P) : Escapes Γ A P := by
  cases related with
  | «universe» _ red =>
      obtain ⟨red⟩ := red
      refine ⟨⟨(typeEndpoints red.equal).left⟩, ?_, ?_, ?_⟩
      · rintro B ⟨right⟩
        exact ⟨red.equal.trans right.equal.symm⟩
      · rintro t ⟨_, ⟨path⟩, _, _⟩
        exact ⟨.conv path.endpoints.left red.equal.symm⟩
      · rintro t u ⟨_, _, ⟨left⟩, ⟨right⟩, _, _, ⟨equal⟩, _, _⟩
        exact ⟨expandEquality left right equal red.equal.symm⟩
  | neutral red _ =>
      obtain ⟨red⟩ := red
      refine ⟨⟨(typeEndpoints red.equal).left⟩, ?_, ?_, ?_⟩
      · rintro B ⟨_, ⟨right⟩, _, ⟨equal⟩⟩
        exact ⟨red.equal.trans (equal.trans right.equal.symm)⟩
      · rintro t ⟨_, ⟨path⟩, _⟩
        exact ⟨.conv path.endpoints.left red.equal.symm⟩
      · rintro t u ⟨_, _, ⟨left⟩, ⟨right⟩, _, _, ⟨equal⟩⟩
        exact ⟨expandEquality left right equal red.equal.symm⟩
  | pi red _ _ _ _ _ =>
      obtain ⟨red⟩ := red
      refine ⟨⟨(typeEndpoints red.equal).left⟩, ?_, ?_, ?_⟩
      · rintro B ⟨_, _, ⟨right⟩, ⟨equal⟩, _, _⟩
        exact ⟨red.equal.trans (equal.trans right.equal.symm)⟩
      · rintro t ⟨_, ⟨path⟩, _, _, _⟩
        exact ⟨.conv path.endpoints.left red.equal.symm⟩
      · rintro t u ⟨_, _, _, _, ⟨left⟩, ⟨right⟩, ⟨equal⟩, _⟩
        exact ⟨expandEquality left right equal red.equal.symm⟩

theorem LR.typeWeakHead {bound : Nat} {lower : Nat → Relation} {Γ : RawContext n}
    {A : Ty n} {P : Pack n} (related : LR bound lower Γ A P) :
    ∃ B, Nonempty (TypeRed Γ A B) ∧ Nonempty (TypeHead B.term) := by
  cases related with
  | «universe» _ red => exact ⟨_, red, ⟨.sort _⟩⟩
  | neutral red normal =>
      obtain ⟨normal⟩ := normal
      exact ⟨_, red, ⟨.neutral normal⟩⟩
  | pi red _ _ _ _ _ => exact ⟨_, red, ⟨.pi _ _⟩⟩

theorem LR.termWeakHead {bound : Nat} {lower : Nat → Relation} {Γ : RawContext n}
    {A : Ty n} {P : Pack n} (related : LR bound lower Γ A P)
    {t : Term n} (member : P.redTm t) :
    ∃ nf, Nonempty (TypedRed Γ t nf A) ∧ Nonempty (Whnf nf) := by
  cases related with
  | «universe» _ red =>
      obtain ⟨red⟩ := red
      obtain ⟨nf, ⟨path⟩, ⟨head⟩, _⟩ := member
      exact ⟨nf, ⟨typedRedConvert path red.equal.symm⟩, ⟨head.whnf⟩⟩
  | neutral red _ =>
      obtain ⟨red⟩ := red
      obtain ⟨nf, ⟨path⟩, ⟨head⟩⟩ := member
      exact ⟨nf, ⟨typedRedConvert path red.equal.symm⟩, ⟨.neutral head⟩⟩
  | pi red _ _ _ _ _ =>
      obtain ⟨red⟩ := red
      obtain ⟨nf, ⟨path⟩, ⟨head⟩, _, _⟩ := member
      exact ⟨nf, ⟨typedRedConvert path red.equal.symm⟩, ⟨head.whnf⟩⟩

/-- This data-valued escape uses the separately audited decoder and search. -/
def LR.typingEvidence {bound : Nat} {lower : Nat → Relation} {Γ : RawContext n}
    {A : Ty n} {P : Pack n} (related : LR bound lower Γ A P)
    {t : Term n} (member : P.redTm t) : Typing Γ t A :=
  Mettapedia.Languages.Agda.SourceEvidence.Codec.recoverTyping (related.escape.typing member)

def LR.typeEqualityEvidence {bound : Nat} {lower : Nat → Relation} {Γ : RawContext n}
    {A B : Ty n} {P : Pack n} (related : LR bound lower Γ A P)
    (equal : P.eqTy B) : TypeEq Γ A B :=
  Mettapedia.Languages.Agda.SourceEvidence.Codec.recoverTypeEquality (related.escape.typeEquality equal)

def LR.termEqualityEvidence {bound : Nat} {lower : Nat → Relation} {Γ : RawContext n}
    {A : Ty n} {P : Pack n} (related : LR bound lower Γ A P)
    {t u : Term n} (equal : P.eqTm t u) : TermEq Γ t u A :=
  Mettapedia.Languages.Agda.SourceEvidence.Codec.recoverTermEquality (related.escape.termEquality equal)

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
