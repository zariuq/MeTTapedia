import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.ContextConversion
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.Normalization

/-!
# Canonical regular dependent telescopes

The existing term normalizer computes a normal form for each telescope entry.
Subject reduction and context conversion prove formation in the already
normalized prefix. Equality of these computed telescopes decides entrywise
conversion between regular contexts; it does not erase the original contexts.
-/

namespace Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular

open Syntax Context

/-- Every entry is normal, including entries dependent on earlier variables. -/
inductive ContextNormal : {n : Nat} → Ctx n → Prop where
  | nil : ContextNormal .nil
  | snoc {Γ : Ctx n} {A : ScopedTerm n} :
      ContextNormal Γ → RedNormal A → ContextNormal (.snoc Γ A)

/-- The computed telescope retains its typed conversion from the source. -/
structure NormalizedContext (Γ : Ctx n) where
  context : Ctx n
  conversion : RegularCtxConversion Γ context
  normal : ContextNormal context

/-- Normalize actual entries using the shared executable normalizer.
Formation of each new head is transported through the normalized prefix. -/
def normalizeContext : {n : Nat} → (Γ : Ctx n) → RegularCtx Γ → NormalizedContext Γ
  | _, .nil, _ => ⟨.nil, .nil, .nil⟩
  | _, .snoc Γ A, regular =>
      let earlier := normalizeContext Γ regular.prefix
      let covered := regularNormalizationSpecification.covers_subject
        ⟨regular.prefix, regular.head_formed⟩
      let head := regularNormalizationSpecification.normalize A covered
      let steps := regularNormalizationSpecification.reduces A covered
      let formed := regular.head_formed.subject_reduction_star regular.prefix steps
      ⟨.snoc earlier.context head,
        .snoc earlier.conversion regular.head_formed (earlier.conversion.transport formed)
          (((regular.head_formed.constantFree_both regular.prefix.constantFreeCtx).1.redStar
            steps).1),
        .snoc earlier.normal (regularNormalizationSpecification.irreducible A covered)⟩

/-- Convertible normal telescopes coincide entry by entry, by term confluence. -/
theorem RegularCtxConversion.eq_of_normal {Γ Δ : Ctx n}
    (conversion : RegularCtxConversion Γ Δ)
    (left : ContextNormal Γ) (right : ContextNormal Δ) : Γ = Δ := by
  induction conversion with
  | nil => rfl
  | snoc earlier _ _ equal ih =>
      cases left with
      | snoc prefixLeft headLeft =>
          cases right with
          | snoc prefixRight headRight =>
              have prefixEqual := ih prefixLeft prefixRight
              have headEqual := normalForms_eq_of_conv
                (.refl _) (.refl _) headLeft headRight equal.toConv
              cases prefixEqual
              cases headEqual
              rfl

/-- The normalizer is complete and sound for formed telescope conversion. -/
theorem normalizeContext_eq_iff {Γ Δ : Ctx n}
    (left : RegularCtx Γ) (right : RegularCtx Δ) :
    (normalizeContext Γ left).context = (normalizeContext Δ right).context ↔
      RegularCtxConversion Γ Δ := by
  constructor
  · intro equal
    have back := (normalizeContext Δ right).conversion.symm
    rw [← equal] at back
    exact (normalizeContext Γ left).conversion.trans back
  · intro conversion
    exact ((normalizeContext Γ left).conversion.symm.trans
      (conversion.trans (normalizeContext Δ right).conversion)).eq_of_normal
        (normalizeContext Γ left).normal (normalizeContext Δ right).normal

theorem normalizeContext_of_normal {Γ : Ctx n} (regular : RegularCtx Γ)
    (normal : ContextNormal Γ) : (normalizeContext Γ regular).context = Γ :=
  (normalizeContext Γ regular).conversion.symm.eq_of_normal
    (normalizeContext Γ regular).normal normal

theorem normalizeContext_idempotent {Γ : Ctx n} (regular : RegularCtx Γ) :
    (normalizeContext (normalizeContext Γ regular).context
      (normalizeContext Γ regular).conversion.target_regular).context =
        (normalizeContext Γ regular).context :=
  normalizeContext_of_normal _ (normalizeContext Γ regular).normal

/-- Direct comparison of computed normal telescopes. Formation proofs supply
termination evidence, not conversion certificates, and are erased at runtime. -/
def decideContextConversion {Γ Δ : Ctx n} (left : RegularCtx Γ) (right : RegularCtx Δ) : Bool :=
  decide ((normalizeContext Γ left).context = (normalizeContext Δ right).context)

theorem decideContextConversion_correct {Γ Δ : Ctx n}
    (left : RegularCtx Γ) (right : RegularCtx Δ) :
    decideContextConversion left right = true ↔ RegularCtxConversion Γ Δ := by
  simp only [decideContextConversion, decide_eq_true_eq]
  exact normalizeContext_eq_iff left right

#print axioms normalizeContext
#print axioms normalizeContext_eq_iff
#print axioms normalizeContext_idempotent
#print axioms decideContextConversion_correct

end Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular
