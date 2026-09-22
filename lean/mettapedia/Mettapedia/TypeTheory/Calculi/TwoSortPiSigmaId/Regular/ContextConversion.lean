import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.SubjectReduction

/-!
# Conversion of regular dependent telescopes

Each converted context entry is independently formed in its preceding
telescope. The resulting identity-on-syntax context maps transport all
regular judgments, including later dependent entries, in both directions.
Neither context formation nor target type formation is inferred merely
from convertibility.
-/

namespace Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular

open Syntax Substitution Renaming Context

/-- Entrywise conversion between formed telescopes of the same length.
Dependencies on all preceding entries remain part of the formation premises. -/
inductive RegularCtxConversion : {n : Nat} → Ctx n → Ctx n → Prop where
  | nil : RegularCtxConversion .nil .nil
  | snoc {Γ Δ : Ctx n} {A B : ScopedTerm n} :
      RegularCtxConversion Γ Δ →
      RegularHasType Γ A .u1 → RegularHasType Δ B .u1 →
      ConstantFreeConv A B → RegularCtxConversion (.snoc Γ A) (.snoc Δ B)

namespace RegularCtxConversion

theorem source_regular {Γ Δ : Ctx n} (conversion : RegularCtxConversion Γ Δ) :
    RegularCtx Γ := by
  induction conversion with
  | nil => exact .nil
  | snoc _ formed _ _ ih => exact .snoc ih formed

theorem target_regular {Γ Δ : Ctx n} (conversion : RegularCtxConversion Γ Δ) :
    RegularCtx Δ := by
  induction conversion with
  | nil => exact .nil
  | snoc _ _ formed _ ih => exact .snoc ih formed

theorem refl {Γ : Ctx n} (regular : RegularCtx Γ) : RegularCtxConversion Γ Γ := by
  induction regular with
  | nil => exact .nil
  | snoc context formed ih =>
      exact .snoc ih formed formed
        (.refl _ (formed.constantFree_both context.constantFreeCtx).1)

theorem symm {Γ Δ : Ctx n} (conversion : RegularCtxConversion Γ Δ) :
    RegularCtxConversion Δ Γ := by
  induction conversion with
  | nil => exact .nil
  | snoc _ first last equal ih => exact .snoc ih last first equal.symm

theorem trans {Γ Δ Θ : Ctx n} (first : RegularCtxConversion Γ Δ)
    (second : RegularCtxConversion Δ Θ) : RegularCtxConversion Γ Θ := by
  induction first with
  | nil => exact second
  | snoc _ formed _ equal ih =>
      cases second with
      | snoc earlier _ last next => exact .snoc (ih earlier) formed last (equal.trans next)

/-- An entrywise telescope conversion gives a typed identity substitution.
The head formation is transported through the earlier entries before the
existing head-conversion construction is used. -/
theorem identityMorphism {Γ Δ : Ctx n} (conversion : RegularCtxConversion Γ Δ) :
    RegularCtxMor Γ Δ ids := by
  induction conversion with
  | nil => exact RegularCtxMor.identity .nil
  | @snoc n Γ Δ A B earlier formed _ equal ih =>
      have formedInTarget : RegularHasType Δ A .u1 := by
        simpa only [subst_ids] using formed.subst ih
      refine ⟨?_, fun i => .var i⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (RegularCtxMor.convertHead formedInTarget equal).typing 0
      · simpa [lookup_snoc_succ, subst_ids, ids, rename, wk] using
          (ih.typing j).weaken (U := B)

/-- All regular judgments survive telescope conversion with their term and
type syntax unchanged. -/
theorem transport {Γ Δ : Ctx n} (conversion : RegularCtxConversion Γ Δ)
    {term type : ScopedTerm n} (typing : RegularHasType Γ term type) :
    RegularHasType Δ term type := by
  simpa only [subst_ids] using typing.subst conversion.identityMorphism

theorem typing_iff {Γ Δ : Ctx n} (conversion : RegularCtxConversion Γ Δ)
    (term type : ScopedTerm n) : RegularHasType Γ term type ↔ RegularHasType Δ term type :=
  ⟨conversion.transport, conversion.symm.transport⟩

/-- Extend a converted prefix by the same genuinely dependent type code.
Its target formation is proved by transport through the prefix. -/
theorem extend_same {Γ Δ : Ctx n} (conversion : RegularCtxConversion Γ Δ)
    {A : ScopedTerm n} (formed : RegularHasType Γ A .u1) :
    RegularCtxConversion (.snoc Γ A) (.snoc Δ A) :=
  .snoc conversion formed (conversion.transport formed)
    (.refl A (formed.constantFree_both conversion.source_regular.constantFreeCtx).1)

/-- Context conversion carries substitutions across both endpoints without
changing a single image term. -/
theorem transportMorphism {Γ Γ' : Ctx n} {Δ Δ' : Ctx m}
    (source : RegularCtxConversion Γ Γ') (target : RegularCtxConversion Δ Δ')
    {σ : Sub n m} (morphism : RegularCtxMor Γ Δ σ) : RegularCtxMor Γ' Δ' σ := by
  have composed := (source.symm.identityMorphism.comp morphism).comp target.identityMorphism
  simpa only [ids, subst_var, subst_ids] using composed

#print axioms identityMorphism
#print axioms typing_iff
#print axioms extend_same
#print axioms transportMorphism

end RegularCtxConversion
end Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular
