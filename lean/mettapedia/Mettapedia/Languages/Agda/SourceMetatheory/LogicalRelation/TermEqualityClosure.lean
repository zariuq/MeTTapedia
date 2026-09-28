import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.TypeEqualityClosure

/-!
Semantic term equality has reducible endpoints and is symmetric/transitive.
Pi comparisons can be transferred to the original function terms by typed
head expansion. No normality is presumed for the intermediate paths stored
in the Pi equality clause.
-/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.StaticMetatheory
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.Kripke Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

theorem LR.equalityMembers {bound : Nat} {lower : Nat → Relation} {Γ : RawContext n}
    {A : Ty n} {P : Pack n} (related : LR bound lower Γ A P) {t u : Term n}
    (equal : P.eqTm t u) : P.redTm t ∧ P.redTm u := by
  cases related with
  | «universe» _ _ =>
      obtain ⟨nf, ng, left, right, leftNormal, rightNormal, _, ⟨Q, rightType⟩, P, leftType, _⟩ := equal
      exact ⟨⟨nf, left, leftNormal, P, leftType⟩, ⟨ng, right, rightNormal, Q, rightType⟩⟩
  | neutral _ _ =>
      obtain ⟨nf, ng, left, right, leftNormal, rightNormal, _⟩ := equal
      exact ⟨⟨nf, left, leftNormal⟩, ⟨ng, right, rightNormal⟩⟩
  | pi _ _ _ _ _ _ => exact ⟨equal.1, equal.2.1⟩

theorem LogRel.symmetricTermEquality {bound : Nat} {Γ : RawContext n}
    {A : Ty n} {P : Pack n} (related : LogRel bound Γ A P) {t u : Term n}
    (equal : P.eqTm t u) : P.eqTm u t := by
  induction related with
  | «universe» less _ =>
      obtain ⟨nf, ng, left, right, leftNormal, rightNormal, ⟨comparison⟩,
        ⟨Q, rightType⟩, P, leftType, typeEqual⟩ := equal
      have reverse := LogRel.symmetricTypeEquality ((below_iff less).mp leftType)
        ((below_iff less).mp rightType) typeEqual
      exact ⟨ng, nf, right, left, rightNormal, leftNormal, ⟨.symm comparison⟩,
        ⟨P, leftType⟩, Q, rightType, reverse⟩
  | neutral _ _ =>
      obtain ⟨nf, ng, left, right, leftNormal, rightNormal, ⟨comparison⟩⟩ := equal
      exact ⟨ng, nf, right, left, rightNormal, leftNormal, ⟨.symm comparison⟩⟩
  | pi _ _ _ _ _ _ _ codomainsIH =>
      obtain ⟨leftMember, rightMember, nf, ng, left, right, ⟨comparison⟩, applications⟩ := equal
      exact ⟨rightMember, leftMember, ng, nf, right, left, ⟨.symm comparison⟩,
        fun {_m} {_Δ} {_ρ} world {_a} argument => codomainsIH world argument (applications world argument)⟩

theorem piEquality_source {Γ : RawContext n} {A : Ty n} {B : TyAbs n}
    {family : PiFamily Γ A B} {t u : Term n}
    (equal : (piPack Γ A B family).eqTm t u) : Nonempty (TermEq Γ t u (Ty.pi A B)) := by
  obtain ⟨_, _, _, _, ⟨left⟩, ⟨right⟩, ⟨comparison⟩, _⟩ := equal
  exact ⟨.trans left.equal (.trans comparison (.symm right.equal))⟩

theorem piEquality_pointwise {bound : Nat} {Γ : RawContext n} {A : Ty n} {B : TyAbs n}
    {family : PiFamily Γ A B}
    (domains : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ),
      LogRel bound Δ (A.rename ρ) (family.domain world))
    (codomains : ∀ {m : Nat} {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ)
      {a : Term m} (argument : (family.domain world).redTm a),
      LogRel bound Δ ((B.rename ρ).instantiate a) (family.codomain world argument))
    {t u : Term n} (equal : (piPack Γ A B family).eqTm t u)
    {Δ : RawContext m} {ρ : Renaming n m} (world : World Γ Δ ρ)
    {a : Term m} (argument : (family.domain world).redTm a) :
    (family.codomain world argument).eqTm ((t.rename ρ).app a) ((u.rename ρ).app a) := by
  obtain ⟨_, _, nf, ng, ⟨left⟩, ⟨right⟩, _, applications⟩ := equal
  obtain ⟨typedArgument⟩ := (domains world).escape.typing argument
  have leftRenamed : TypedRed Δ (t.rename ρ) (nf.rename ρ) (Ty.pi (A.rename ρ) (B.rename ρ)) := by
    simpa only [Ty.pi_rename] using world.reduction left
  have rightRenamed : TypedRed Δ (u.rename ρ) (ng.rename ρ) (Ty.pi (A.rename ρ) (B.rename ρ)) := by
    simpa only [Ty.pi_rename] using world.reduction right
  exact (codomains world argument).expandTermEquality
    (typedRedApplication leftRenamed typedArgument) (typedRedApplication rightRenamed typedArgument)
    (applications world argument)

theorem LogRel.transitiveTermEquality {bound : Nat} {Γ : RawContext n}
    {A : Ty n} {P : Pack n} (related : LogRel bound Γ A P) {t u v : Term n}
    (first : P.eqTm t u) (second : P.eqTm u v) : P.eqTm t v := by
  induction related with
  | «universe» less _ =>
      obtain ⟨nf, nm, left, ⟨middleLeft⟩, leftNormal, ⟨middleNormal⟩, ⟨leftEqual⟩,
        _, P, leftType, leftComparison⟩ := first
      obtain ⟨nm', ng, ⟨middleRight⟩, right, ⟨middleNormal'⟩, rightNormal, ⟨rightEqual⟩,
        rightType, Q, middleType, rightComparison⟩ := second
      have same := middleLeft.raw.normal_unique middleRight.raw middleNormal.whnf middleNormal'.whnf
      cases same
      have combined := LogRel.transitiveTypeEquality ((below_iff less).mp leftType)
        ((below_iff less).mp middleType) leftComparison rightComparison
      exact ⟨nf, ng, left, right, leftNormal, rightNormal, ⟨.trans leftEqual rightEqual⟩,
        rightType, P, leftType, combined⟩
  | neutral _ _ =>
      obtain ⟨nf, nm, left, ⟨middleLeft⟩, leftNormal, ⟨middleNormal⟩, ⟨leftEqual⟩⟩ := first
      obtain ⟨nm', ng, ⟨middleRight⟩, right, ⟨middleNormal'⟩, rightNormal, ⟨rightEqual⟩⟩ := second
      have same := middleLeft.raw.normal_unique middleRight.raw (.neutral middleNormal) (.neutral middleNormal')
      cases same
      exact ⟨nf, ng, left, right, leftNormal, rightNormal, ⟨.trans leftEqual rightEqual⟩⟩
  | pi _ _ _ _ domains codomains _ codomainsIH =>
      obtain ⟨leftSource⟩ := piEquality_source first
      obtain ⟨rightSource⟩ := piEquality_source second
      refine ⟨first.1, second.2.1, _, _,
        ⟨.refl (termEndpoints leftSource).left⟩, ⟨.refl (termEndpoints rightSource).right⟩,
        ⟨.trans leftSource rightSource⟩, ?_⟩
      intro m Δ ρ world a argument
      exact codomainsIH world argument
        (piEquality_pointwise domains codomains first world argument)
        (piEquality_pointwise domains codomains second world argument)

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
