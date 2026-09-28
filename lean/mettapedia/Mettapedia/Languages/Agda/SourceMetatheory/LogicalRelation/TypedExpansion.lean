import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.AnnotationBound

/-!
Closure under explicitly typed weak-head prefixes. These theorems use real
source reduction/equality evidence; they do not turn an arbitrary raw step
and a typing assumption into preservation.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

theorem LR.expandType {bound : Nat} {lower : Nat → Relation} {Γ : RawContext n}
    {A B : Ty n} {P : Pack n} (initial : TypeRed Γ A B)
    (related : LR bound lower Γ B P) : LR bound lower Γ A P := by
  cases related with
  | «universe» less red =>
      rename_i k
      obtain ⟨red⟩ := red
      exact .universe less ⟨initial.trans red⟩
  | neutral red normal =>
      obtain ⟨red⟩ := red
      exact .neutral ⟨initial.trans red⟩ normal
  | pi red domain codomain family domains codomains =>
      obtain ⟨red⟩ := red
      exact .pi ⟨initial.trans red⟩ domain codomain family domains codomains

theorem LR.expandTypeEquality {bound : Nat} {lower : Nat → Relation} {Γ : RawContext n}
    {A B C : Ty n} {P : Pack n} (related : LR bound lower Γ A P)
    (initial : TypeRed Γ B C) (equal : P.eqTy C) : P.eqTy B := by
  cases related with
  | «universe» _ _ =>
      obtain ⟨red⟩ := equal
      exact ⟨initial.trans red⟩
  | neutral _ _ =>
      obtain ⟨D, ⟨red⟩, normal, equal⟩ := equal
      exact ⟨D, ⟨initial.trans red⟩, normal, equal⟩
  | pi _ _ _ _ _ _ =>
      obtain ⟨D, E, ⟨red⟩, equal, domains, codomains⟩ := equal
      exact ⟨D, E, ⟨initial.trans red⟩, equal, domains, codomains⟩

theorem LogRel.expandTerm {bound : Nat} {Γ : RawContext n} {A : Ty n} {P : Pack n}
    (related : LogRel bound Γ A P) {t u : Term n} (initial : TypedRed Γ t u A)
    (member : P.redTm u) : P.redTm t := by
  cases related with
  | «universe» less red =>
      rename_i k
      obtain ⟨red⟩ := red
      obtain ⟨nf, ⟨path⟩, normal, Q, typeRelated⟩ := member
      have atUniverse := typedRedConvert initial red.equal
      have codePath : TypeRed Γ (.el k t) (.el k u) := ⟨rfl, atUniverse⟩
      have newType := LR.expandType codePath ((below_iff less).mp typeRelated)
      exact ⟨nf, ⟨typedRedTrans atUniverse path⟩, normal, Q, (below_iff less).mpr newType⟩
  | neutral red _ =>
      obtain ⟨red⟩ := red
      obtain ⟨nf, ⟨path⟩, normal⟩ := member
      exact ⟨nf, ⟨typedRedTrans (typedRedConvert initial red.equal) path⟩, normal⟩
  | pi red _ _ _ _ _ =>
      obtain ⟨red⟩ := red
      obtain ⟨nf, ⟨path⟩, normal, applications, extension⟩ := member
      exact ⟨nf, ⟨typedRedTrans (typedRedConvert initial red.equal) path⟩,
        normal, applications, extension⟩

theorem LogRel.expandTermEquality {bound : Nat} {Γ : RawContext n} {A : Ty n} {P : Pack n}
    (related : LogRel bound Γ A P) {t t' u u' : Term n}
    (leftPrefix : TypedRed Γ t t' A) (rightPrefix : TypedRed Γ u u' A)
    (equal : P.eqTm t' u') : P.eqTm t u := by
  cases related with
  | «universe» less red =>
      rename_i k
      obtain ⟨red⟩ := red
      obtain ⟨nf, ng, ⟨left⟩, ⟨right⟩, leftNormal, rightNormal, comparison,
        ⟨Q, rightType⟩, P, leftType, typeEqual⟩ := equal
      have leftAtUniverse := typedRedConvert leftPrefix red.equal
      have rightAtUniverse := typedRedConvert rightPrefix red.equal
      have leftRelated := (below_iff less).mp leftType
      have leftCode : TypeRed Γ (.el k t) (.el k t') := ⟨rfl, leftAtUniverse⟩
      have rightCode : TypeRed Γ (.el k u) (.el k u') := ⟨rfl, rightAtUniverse⟩
      have newLeft := LR.expandType leftCode leftRelated
      have newRight := LR.expandType rightCode ((below_iff less).mp rightType)
      exact ⟨nf, ng, ⟨typedRedTrans leftAtUniverse left⟩,
        ⟨typedRedTrans rightAtUniverse right⟩, leftNormal, rightNormal, comparison,
        ⟨Q, (below_iff less).mpr newRight⟩, P, (below_iff less).mpr newLeft,
        leftRelated.expandTypeEquality rightCode typeEqual⟩
  | neutral red _ =>
      obtain ⟨red⟩ := red
      obtain ⟨nf, ng, ⟨left⟩, ⟨right⟩, leftNormal, rightNormal, comparison⟩ := equal
      exact ⟨nf, ng, ⟨typedRedTrans (typedRedConvert leftPrefix red.equal) left⟩,
        ⟨typedRedTrans (typedRedConvert rightPrefix red.equal) right⟩,
        leftNormal, rightNormal, comparison⟩
  | pi red domain codomain family domains codomains =>
      obtain ⟨leftMember, rightMember, nf, ng, ⟨left⟩, ⟨right⟩, comparison, applications⟩ := equal
      have related := LR.pi red domain codomain family domains codomains
      have newLeft := LogRel.expandTerm related leftPrefix leftMember
      have newRight := LogRel.expandTerm related rightPrefix rightMember
      obtain ⟨red⟩ := red
      exact ⟨newLeft, newRight, nf, ng,
        ⟨typedRedTrans (typedRedConvert leftPrefix red.equal) left⟩,
        ⟨typedRedTrans (typedRedConvert rightPrefix red.equal) right⟩,
        comparison, applications⟩

private def applyRed {Γ : RawContext n} {A C : Ty n} {B : TyAbs n}
    {f g a : Term n} (path : TypedRed Γ f g C) (same : C = Ty.pi A B)
    (argument : Typing Γ a A) : TypedRed Γ (f.app a) (g.app a) (B.instantiate a) :=
  match path with
  | .refl typed => .refl (.app (same ▸ typed) argument)
  | .step first rest => .step (.head (same ▸ first) argument) (applyRed rest same argument)

def typedRedApplication {Γ : RawContext n} {A : Ty n} {B : TyAbs n}
    {f g a : Term n} (path : TypedRed Γ f g (Ty.pi A B)) (argument : Typing Γ a A) :
    TypedRed Γ (f.app a) (g.app a) (B.instantiate a) := applyRed path rfl argument

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
