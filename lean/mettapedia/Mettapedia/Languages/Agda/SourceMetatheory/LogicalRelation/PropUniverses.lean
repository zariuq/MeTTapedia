import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.PropPiParts

/-! Actual finite-universe formation and decoding/encoding closure lemmas. -/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead Mettapedia.Languages.Agda.SourceMetatheory.TypedHeadData

theorem universeReducible (bound k : Nat) (less : k < bound) {Γ : RawContext n}
    (formed : FormCtx Γ) :
    LogRel bound Γ (Ty.universe k) (universePack (below bound) Γ k) :=
  LR.universe less ⟨TypeRed.refl (.universe formed k)⟩

/-- A reducible type code at stratum k is a reducible member of Set k. -/
theorem universeMember {bound k : Nat} (less : k < bound) {Γ : RawContext n}
    {t : Term n} {P : Pack n} (related : LogRel k Γ (.el k t) P) :
    (universePack (below bound) Γ k).redTm t := by
  obtain ⟨B, ⟨red⟩, shape⟩ := related.typeWeakHead
  exact ⟨B.term, ⟨red.steps⟩, shape, P, (below_iff less).mpr related⟩

/-- Semantic type comparison yields the corresponding universe term comparison;
the right type's reducibility is retained explicitly, not inferred by a rule. -/
theorem universeEquality {bound k : Nat} (less : k < bound) {Γ : RawContext n}
    {t u : Term n} {P Q : Pack n} (left : LogRel k Γ (.el k t) P)
    (right : LogRel k Γ (.el k u) Q) (equal : P.eqTy (.el k u)) :
    (universePack (below bound) Γ k).eqTm t u := by
  obtain ⟨B, ⟨leftRed⟩, leftShape⟩ := left.typeWeakHead
  obtain ⟨C, ⟨rightRed⟩, rightShape⟩ := right.typeWeakHead
  obtain ⟨sourceEqual⟩ := left.escape.typeEquality equal
  cases sourceEqual with
  | atSort sourceEqual =>
      exact ⟨B.term, C.term, ⟨leftRed.steps⟩, ⟨rightRed.steps⟩, leftShape, rightShape,
        ⟨.trans (.symm leftRed.steps.equal) (.trans sourceEqual rightRed.steps.equal)⟩,
        ⟨Q, (below_iff less).mpr right⟩, P, (below_iff less).mpr left, equal⟩

/-- The ordinary sort constructor is semantically inhabited at every finite level. -/
theorem sortMember (k : Nat) {Γ : RawContext n} (formed : FormCtx Γ) :
    (universePack (below (k + 2)) Γ (k + 1)).redTm (.sort k) :=
  universeMember (by omega) (universeReducible (k + 1) k (by omega) formed)

/-- No universe head can occur in the zeroth semantic stratum. Neutral types
still occur there, so this is a genuine universe separation control. -/
theorem zeroHasNoUniverse {Γ : RawContext n} {P : Pack n} (k : Nat) :
    ¬ LogRel 0 Γ (Ty.universe k) P := by
  intro related
  cases related with
  | «universe» less _ => omega
  | neutral red neutral =>
      obtain ⟨red⟩ := red
      obtain ⟨neutral⟩ := neutral
      have fixed := red.steps.raw.sort_fixed
      have atSort : Neutral (.sort k) := fixed ▸ neutral
      cases atSort
  | pi red _ _ _ _ _ =>
      obtain ⟨red⟩ := red
      have impossible := red.steps.raw.sort_fixed
      cases impossible

/-- The source hierarchy remains noncumulative in the semantic clauses. -/
theorem sortNotSelfMember {lower : Nat → Relation} {Γ : RawContext n} (k : Nat) :
    ¬ (universePack lower Γ k).redTm (.sort k) := by
  rintro ⟨_, ⟨red⟩, _⟩
  have levels := red.endpoints.left.sort_level
  change k + 1 = k + 2 at levels
  omega

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
