import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.SubjectReduction
import Mettapedia.Languages.MeTTa.OSLFCore.SubjectReduction

/-!
# Typed language-definition assembly for the two-sort experiment

Bundles the two-sort experiment's kernel, typing, reduction, and subject reduction
into a single `TypedLangDef` object, and contrasts it with MeTTa's
current type system.

## Scope

This bundles one concrete Pattern typing relation and its preservation
theorem. It proves neither initiality nor that HE/PeTTa are conservative
extensions of the calculus, and it selects no Prime foundation.
The ground head and formation marker do not provide a cumulative hierarchy.

`metta_not_subject_reduction` is a counterexample for the separately authored
annotation-lookup relation. The contrast with `TwoSortHasType` is about these
two stated judgments, not an adequacy theorem for a runtime dialect.

## Summary

- `TypedLangDef` — structure bundling language + typing + reduction + SR
- `twoSortDependentTyped` — the two-sort experiment as a `TypedLangDef`
- Contrast theorem: documents the SR gap between two-sort and Current
- `twoSortDependent_architecture_properties` — key architectural properties

## File Inventory (Milestone 1)

| File | Sorries | Axioms | Key Definitions |
|------|---------|--------|-----------------|
| `Core.lean` | 0 | 0 | `twoSortDependent : LanguageDef`, OSLF pipeline |
| `Typing.lean` | 0 | 0 | `TwoSortHasType`, `TwoSortConv` (cofinite) |
| `Reduction.lean` | 0 | 0 | `TwoSortReduces`, `TwoSortReducesStar` |
| `SubjectReduction.lean` | 0 | 0 | `typing_subst`, `twoSortDependent_subject_reduction` |
| `TypedLangDef.lean` | 0 | 0 | `TypedLangDef`, `twoSortDependentTyped` |
-/

namespace Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Assembly

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Fragment
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Typing
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Reduction
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.SubjectReduction
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.FVarSubst (TwoSortReducesStar_implies_TwoSortConv)
open Mettapedia.OSLF.MeTTaIL.Substitution (lc_at)

/-! ## TypedLangDef Structure -/

/-- A typed language definition: bundles a MeTTa-IL language, typing
    judgment, reduction relation, and subject reduction proof. -/
structure TypedLangDef where
  /-- The operational language (a `LanguageDef` instance). -/
  lang : LanguageDef
  /-- Context type for typing judgments. -/
  Ctx : Type
  /-- Typing judgment: `Γ ⊢ t : A`. -/
  hasType : Ctx → Pattern → Pattern → Prop
  /-- One-step reduction: `t ~> t'`. -/
  reduces : Pattern → Pattern → Prop
  /-- Subject reduction: typing is preserved under reduction. -/
  subject_reduction : ∀ {Γ t t' A},
    hasType Γ t A → reduces t t' → hasType Γ t' A

/-- the two-sort experiment as a `TypedLangDef`.

    Uses `twoSortDependent_subject_reduction` from `SubjectReduction.lean`. -/
noncomputable def twoSortDependentTyped : TypedLangDef where
  lang := twoSortDependent
  Ctx := TwoSortCtx
  hasType := TwoSortHasType
  reduces := TwoSortReduces
  subject_reduction := twoSortDependent_subject_reduction

/-! ## Contrast: the two-sort experiment vs MeTTa-Current -/

/-- MeTTa's current `HasType` (annotation-based lookup) provably
    fails subject reduction.

    This uses the counterexample from `Languages/MeTTa/OSLFCore/SubjectReduction.lean`. -/
theorem metta_current_sr_fails :
    ¬ Mettapedia.Languages.MeTTa.OSLFCore.SubjectReduction
      Mettapedia.Languages.MeTTa.OSLFCore.HasType
      Mettapedia.Languages.MeTTa.OSLFCore.AtomReduces :=
  Mettapedia.Languages.MeTTa.OSLFCore.metta_not_subject_reduction

/-! ## Architectural Properties -/

/-- the two-sort experiment has exactly 2 sorts: Tm (terms) and Ctx (contexts). -/
theorem twoSortDependent_two_sorts : twoSortDependent.types.length = 2 := by decide

/-- the two-sort experiment has exactly 3 β-reductions (Π, Σ-fst, Σ-snd). -/
theorem twoSortDependent_three_betas : twoSortDependent.rewrites.length = 3 := by decide

/-- the two-sort experiment is intensional: no equations (no extensional axioms). -/
theorem twoSortDependent_intensional : twoSortDependent.equations = [] := rfl

/-- the two-sort experiment has 13 grammar rules (11 Tm + 2 Ctx constructors). -/
theorem twoSortDependent_thirteen_constructors : twoSortDependent.terms.length = 13 := by decide

/-- Every one-step reduction of a locally closed term is a definitional equality. -/
theorem twoSortDependent_reduction_sound {t t' : Pattern}
    (hlc : lc_at 0 t = true) (htwoSort : TwoSortTermPattern t) (h : TwoSortReduces t t') : TwoSortConv t t' :=
  TwoSortReduces_implies_TwoSortConv h hlc htwoSort

/-- Multi-step reduction of a locally closed term is a definitional equality. -/
theorem twoSortDependent_reduction_star_sound {t t' : Pattern}
    (hlc : lc_at 0 t = true) (htwoSort : TwoSortTermPattern t) (h : TwoSortReducesStar t t') : TwoSortConv t t' :=
  TwoSortReducesStar_implies_TwoSortConv h hlc htwoSort

/-- Typed one-step reduction is a definitional equality. -/
theorem twoSortDependent_typed_reduction_sound {Γ : TwoSortCtx} {t t' A : Pattern}
    (ht : TwoSortHasType Γ t A) (h : TwoSortReduces t t') : TwoSortConv t t' :=
  TwoSortReduces_implies_TwoSortConv h (typing_lc ht) (typing_term_twoSort ht)

/-- Typed multi-step reduction is a definitional equality. -/
theorem twoSortDependent_typed_reduction_star_sound {Γ : TwoSortCtx} {t t' A : Pattern}
    (ht : TwoSortHasType Γ t A) (h : TwoSortReducesStar t t') : TwoSortConv t t' :=
  TwoSortReducesStar_implies_TwoSortConv h (typing_lc ht) (typing_term_twoSort ht)

/-! ## Milestone Status

**Milestone 1** (the two-sort experiment kernel): substitution and subject-reduction
theorems are present in `SubjectReduction.lean`.

Current integration status should be read from project build targets and
framework trackers (rather than this historical milestone note).

**Milestone 2** (Bridge to `langReduces`): future.
**Milestone 3** (MeTTa-Core assembly): future. -/

end Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Assembly
